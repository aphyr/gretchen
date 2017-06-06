(ns gretchen.history
  "Basic operations over transactions and histories."
  (:refer-clojure :exclude [ancestors descendants])
  (:require [gretchen.recurset :as recurset]
            [clojure.set :as set]))

(defn legal-order
  "Given a history, returns true if the given history's ops can be applied
  on top of the initial state, in order, without ever reading the wrong thing"
  [history]
  (let [solution (:solution history)]
    ;; for each txn in the solution perform its ops in order and update/check state on writes/reads. if empty --> legal
    (empty?
      (->> solution
           ;; creates a map of operations
           (map :ops ,,,)
           ;; reduces that map into a single value
           (reduce (fn [(=(f k)v)] "more here"))))))


(defn ext-reads
  "Given a transaction, returns the map of keys to values for its external
  reads."
  [txn]
  (->> (:ops txn)
       (reduce (fn [[ext ignore?] {:keys [f k v]}]
                 [(if (or (= :write f)
                          (ignore? k))
                    ext
                    (assoc ext k v))
                  (conj ignore? k)])
               [{} #{}])
       first))

(defn ext-writes
  "Given a transaction, returns the map of keys to values for its external
  writes."
  [txn]
  (->> (:ops txn)
       (reduce (fn [ext {:keys [f k v]}]
                 (if (= :read f)
                   ext
                   (assoc ext k v)))
               {})))

(defn add-initial-txn
  "Takes a history and prepends a transaction writing its initial state."
  [history]
  (let [t0 (->> (:initial history)
                (map (fn [[k v]] {:f :write, :k k, :v v}))
                (array-map :ops))]
    (assoc history :txns (cons t0 (:txns history)))))

(defn add-txn-ids
  "Takes a history and adds ids :i = 0...n to its transactions."
  [history]
  (->> (:txns history)
       (mapv (fn [i txn] (assoc txn :i i)) (range))
       (assoc history :txns)))

(defn ext-index
  "Takes a history (with initial transaction and indices) and a function
  returning a map of keys to values for a transaction, and computes an index
  which maps keys to values to collections of transaction ids which yielded
  that (k, v) pair. Used to compute the external read and write indices for a
  history."
  [history index-fn]
  (assert (= 0 (:i (first (:txns history)))))
  (reduce (fn [index txn]
            (reduce (fn [index [k v]]
                      (update-in index [k v] conj (:i txn)))
                    index
                    (index-fn txn)))
          {}
          (:txns history)))

(defn add-ext-indices
  "Takes a history and adds :ext-reads and :ext-writes indexes, mapping keys to
  values to collections of transaction IDs."
  [history]
  (assoc history
         :ext-reads  (ext-index history ext-reads)
         :ext-writes (ext-index history ext-writes)))

(defn prepare-history
  "Introduces the initial transaction, assigns ids to transactions, and
  computes indices."
  [history]
  (-> history
      add-initial-txn
      add-txn-ids
      add-ext-indices))

(defn ancestors
  "Builds a partial transaction precedence graph based on each transaction's
  external reads and writes. THIS GRAPH IS NOT TOTAL: if the graph contains
  a->b, then a must execute after b, but the converse is not necessarily true:
  some dependencies may not be present. We only consider happens-before
  precedence, and don't use information about excluded intervals.

  That said, for those transactions we *do* prove lie before another, we
  actually compute the transitive closure."
  [history]
  ; dep graph: a map of txns t to a set of txns t definitely depends on.
  ;
  ; We build up the dep graph by visiting every transaction. Where a
  ; transaction has at most one dependency for every external read, we know
  ; those are its total dependencies. Where a transaction has multiple
  ; dependencies for a given read, we take the intersection of their
  ; dependencies.
  (let [ext-writes (:ext-writes history)
        txns       (:txns history)]
    (loop [stack (list txns) ; A stack of lists of unvisited txns
           graph {}]         ; Our accumulated dependency graph
      (if-not (seq stack)
        ; Stack empty; we're done
        graph

        (let [needed-txns (first stack)]
          (if-not (seq needed-txns)
            ; No more txns at this level; move back up
            (recur (next stack) graph)

            ; OK we have a txn. Is it in the graph yet?
            (let [txn (first needed-txns)]
              (if (get graph txn)
                ; Already computed; move on
                (recur (cons (next needed-txns) (next stack)) graph)

                ; Compute a conjunction of disjunctions of dependency txn ids.
                (let [writes (->> (ext-reads txn)
                                  (keep (fn [[k v]]
                                          (->> (-> ext-writes (get k) (get v))
                                               (keep (fn [i]
                                                       ; Don't depend on self
                                                       (when (not= i (:i txn))
                                                         ; Map ids back to txns
                                                         (nth txns i)))))))
                                  (filter seq))
                      ; Do we still need to visit any of these?
                      needed (remove graph (flatten writes))]
                  (if (seq needed)
                    ; Hang on, we gotta figure out some dependencies first
                    (recur (cons needed stack) graph)

                    ; OK our dependencies are all figured out. Now, we want the
                    ; intersection of the transitive dependency set for any of
                    ; our alternative deps...
                    (let [trans-deps (map (fn [txns]
                                            (->> txns
                                                 (map graph)
                                                 recurset/intersection))
                                          writes)
                          ; ... plus those transactions we definitely directly
                          ; depend on
                          direct-deps (keep #(when (= 1 (count %))
                                               (first %))
                                            writes)
                          deps (recurset/union (cons direct-deps trans-deps))]

                      ; Update graph and move to the next thing in the stack
                      (recur (cons (next needed-txns) (next stack))
                             (assoc graph txn deps)))))))))))))

