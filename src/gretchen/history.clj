(ns gretchen.history
  "Basic operations over transactions and histories."
  (:refer-clojure :exclude [ancestors descendants])
  (:require [clojure.set :as set]))

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
       (map-indexed (fn [i txn] (assoc txn :i i)))
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

(defn precedence-graph
  "Builds a partial transaction precedence graph based on each transaction's
  external reads and writes. THIS GRAPH IS NOT TOTAL: if the graph contains
  a->b, then a must execute after b, but the converse is not necessarily true:
  some dependencies may not be present.

  I can't think of a more efficient way to do this than materializing the
  *entire* dependency tree, so for e.g. 10k transactions each depending on the
  previous, we're looking at, I dunno, a gigabyte of memory. Not great but not
  wholly impractical."
  [history]
  ; dep graph: a map of txn ids i to txn ids i definitely depends on.
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

        (let [txns (first stack)]
          (if-not (seq txns)
            ; No more txns at this level; move back up
            (recur (next stack) graph)

            ; OK we have a txn. Is it in the graph yet?
            (let [txn (first txns)]
              (if (get graph txn)
                ; Already computed; move on
                (recur (cons (next txns) (next stack)) graph)

                ; Compute a conjunction of disjunctions of dependency txn ids.
                (let [writes (->> (ext-reads txn)
                                  (keep (fn [[k v]])
                                        (->> (-> ext-writes (get k) (get v))
                                             (keep (fn [i]
                                                     ; Don't depend on self
                                                     (when (not= i (:i txn))
                                                       ; Map ids back to txns
                                                       (nth txns i)))))))
                      ; Do we still need to visit any of these?
                      needed (remove graph (flatten writes))]
                  (if (seq needed)
                    ; Hang on, we gotta figure out some dependencies first
                    (recur (cons needed stack) graph)

                    ; OK our dependencies are all figured out. Now let's
                    ; combine them.
                    (let [deps (loop [deps #{}
                                      writes writes]
                                 (if-not (seq writes)
                                   ; Done
                                   deps
                                   (let [alts (first writes)]
                                     (condp = (count alts)
                                       ; No deps for this key
                                       0 (recur deps (next writes))

                                       ; Single dep for this key
                                       1 (recur (->> (first alts)
                                                     (get graph)
                                                     (set/union deps))
                                                (next writes))

                                       ; Multiple deps; take their intersection
                                       2 (recur (->> deps
                                                     (map graph)
                                                     (reduce set/intersection)
                                                     (set/union deps))
                                                (next writes))))))]
                      ; Update graph and move to the next thing in the stack
                      (recur (cons (next txns) (next stack))
                             (assoc graph txn deps)))))))))))))
