(ns regina.core
  "In 'A Framework for Transactional Consistency Models with Atomic
  Visibility', Cerone, Bernardi, and Gotsman present a formal model for
  transactions composed of ordered reads and writes on a set of registers.
  They show that serializability can be defined in terms of three properties:

  INT (Internal Consistency): transactions read values consistent with their
  prior reads and writes.

  EXT (External Consistency): Let an 'external read' be the first read of a
  register r without a preceding write in a given transaction. Every external
  read of r in transaction Ti must see the final value written by the most
  recent transaction visible to Ti, where 'most recent' is determined by the
  arbitration order.

  TOTAL-VIS: VIS, the visibility relationship on transactions, must be a total
  order.

  ## Observations

  Note that INT can be verified in linear time: we simply check each
  transaction independently. But without knowing the visiblity order VIS and
  arbitration order AR (which, when TOTAL-VIS holds, are essentially (exactly?)
  the same), we have no efficient way to verify EXT. We must *find* a VIS
  consistent with EXT.

  We could enumerate all possible orders for AR; this is exponential time and
  can trivially overwhelm a SAT solver. Tests with a single register and
  single-op transactions suggests that no more than 30-50 operations can be
  directly checked for serializability in Alloy, at least using MiniSAT, which
  appears to be the fastest solver available.

  However, we can *reduce* the search space dramatically by applying
  heuristics. First, note that the denser the register state space--the more
  reads and writes have the same values--the more valid serializations we are
  likely to have. A test of serializability will likely *limit* degeneracy
  by using many distinct values.

  When degeneracy is small, we can identify prior transactions for EXT in
  constant time for any given transaction, so long as we have a few (linear
  time) indexes identifying which transactions could have written those values.

  ## Approach

  Consider a set of n transactions. For simplicity, we construct an initial
  transaction T_0, which simply writes the initial state.

  Then, for every transaction T_i where 0 < i <= n, take the set of external
  reads R: a map from keys to values. We want to obtain a constraint on the
  arbitrartion order of transactions AR which guarantees that by the time T_i
  executes, R is a subset of the current table state--e.g., T_i's external
  reads are satisfiable.

  For all external reads r = (k, v) in R, let the set of transactions
  externally writing (k, v) be W (Writes), and the set of all transactions
  externally writing (k, not-v) be O (Overwrites). r is satisfied iff:

  1. There exists some T_w in W | w < i (e.g. the write precedes the read)
  2. There exists no T_o in O | w < o < i (the write is not overwritten)

  So for each read, we will generate a series of alterative constraints on the
  indices of writes and overwrites, like so:

  (or (and (< w0 i)                 ; write constraint
           (or (< o0 w0) (< i o0))  ; overwrite constraint
           (or (< o1 w0) (< i o1))) ; another overwrite constraint
      (and (< w1 i)                 ; a different write constraint
           (or (< o0 w1) (< i o0))  ; overwrite constraint
           (or (< o1 w1) (< i o1))) ; another overwrite constraint

  The transaction is satisfied iff all its external reads are satisfied, so:

  (and (or ... r0 constraints ...)
       (or ... r1 constraints ...))

  And the history is satisfied if all its transactions are satisfied, so:

  (and (or ... T0 r0 constraints ...)
       (or ... T0 r1 constraints ...)
       (or ... T1 r0 constraints ...)
       (or ... T1 r1 constraints ...))

  Note that we have eliminated all notion of state variables, reads, writes,
  operations, and even transactional semantics from the constraints. We simply
  require a solution to the integer constraint problem: finding a unique
  assignment of integers to the n indices identifying each transaction's
  position in the order. A solution to this integer constraint problem provides
  us with a legal serialization of the history."
  (:require [clojure.string :as str]
            [clojure.pprint :refer [pprint]]
            [regina.constraint :as c]))

;; Formatting

(defn op-str
  "Formats an op as a string."
  [op]
  (let [f (condp = (:f op) :read "r", :write "w")]
    (str f (name (:k op)) "(" (:v op) ")")))

(defn txn-str
  "Formats a transaction as a string."
  [txn]
  (str "[" (str/join " " (map op-str (:ops txn))) "]"))

(defn pr-history
  "Prints a history"
  [history]
  (doseq [txn history]
    (println (txn-str txn))))

;; Internal consistency

(defn check-int
  "Verifying internal consistency is easy. We need only check that every read
  in a transaction is preceded by an identical read or write. We iterate
  through operations in the transaction, building up a partial model of the
  current state and checking each new op against that state. Augments broken
  transactions with an :error field."
  [txn]
  (if-let [e (->> (:ops txn)
                  (reduce (fn [state, {:keys [f k v] :as op}]
                            (let [state' (assoc state k v)]
                              (if (and (= f :read)
                                       (not= v (get state k v)))
                                (reduced
                                  (assoc state'
                                         ::error {:type :internal
                                                  :op op
                                                  :expected (get state k)}))
                                state')))
                          {})
                  ::error)]
    (assoc txn :error e)
    txn))

(defn check-int-history
  "Checks internal consistency on an entire history. Returns

  {:txns   [t1 t2 ...]
   :errors [t3 ...]}"
  [history]
  (let [txns    (->> history :txns (map check-int))
        errors  (filter :error txns)
        history (assoc history :txns txns)]
    (if (seq errors)
      (assoc history :errors errors)
      history)))

;; External consistency
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

(defn check-spurious-reads
  "Takes a history, and checks for the presence of external reads without
  corresponding external writes."
  [history]
  (let [reads  (:ext-reads history)
        writes (:ext-writes history)
        spurious (->> reads
                      (mapcat
                        (fn [[k reads-of-k]]
                          ; (writes k) is a map of values to txn i's, so
                          ; we can use it to cross off read values.
                          (->> (keys reads-of-k)
                               (remove (writes k))
                               (mapcat (fn [v]
                                         (mapv (fn [i]
                                                 {:txn (nth (:txns history) i)
                                                  :k k
                                                  :v v})
                                               (reads-of-k v))))))))]
    (if (seq spurious)
      (assoc history :error {:type :spurious-read
                              :reads spurious})
      history)))

(defn priors
  "The txn ids which could satisfy the given transaction's external read of k
  with value v, and the txn ids which would invalidate that read."
  [history txn-id [k v]]
  (let [writes-to-k (-> history :ext-writes (get k))
        good        (remove #{txn-id} (get writes-to-k v))
        bad         (->> (dissoc writes-to-k v)
                         vals
                         (apply concat)
                         (remove #{txn-id}))]
    [good bad]))

(defn prior-constraint
  "Given a history, a constraint system, a transaction, and its read of [k v],
  constructs a constraint ensuring that read is satisfiable."
  [history s txn [k v :as r]]
  (let [[W O] (priors history (:i txn) r)
        t (c/v s (:i txn))
        W (map #(c/v s %) W)
        O (map #(c/v s %) O)]
    (assert (seq W) "external read unsatisfied") ; Sanity check
    (c/or* s (for [w W]
               (c/and* s (cons (c/< s w t)
                               (for [o O]
                                 (c/or s (c/< s o w) (c/< s t o)))))))))

(defn txn-constraint
  "Given a history, a constraint system, and transaction, constructs a
  constraint ensuring the transaction's external consistency."
  [history s txn]
  (c/and* s (for [r (ext-reads txn)]
              (prior-constraint history s txn r))))

(defn txn-constraints
  "Given a history and a constraint system, generates a constraint for all
  txns."
  [history s]
  (c/and* s (for [t (:txns history)] (txn-constraint history s t))))

(defn distinct-constraint
  "Given a history and a constraint system, generates a constraint which
  demands all transaction identifiers are unique."
  [history s]
  (->> history
       :txns
       (map (comp (partial c/v s) :i))
       (c/distinct s)))

(defn index-constraints
  "Given a history and a constraint system, generates a constraint declaring
  all transaction index variables to be integers from 0 to n."
  [history s]
  (->> history
       :txns
       (map (fn [txn]
             (c/in s (c/v s (:i txn)) 0 (dec (count (:txns history))))))
       (c/and* s)))

(defn history-constraint
  "Given a history and a constraint system, constructs a constraint ensuring
  the history is serializable."
  [history s]
  (c/tseitin
    (c/simplify
      (c/and* s [(index-constraints history s)
                 (distinct-constraint history s)
                 (txn-constraints history s)]))))

(defn check-ext-history
  "Check history for external consistency."
  [history s]
  (let [constraint (history-constraint history (c/clojure))
        constraint (c/clojure-> s constraint)
        soln       (c/solution s constraint)]
    ; Map solution back to history
    (if soln
      (assoc history :solution
             (let [var-order    (map key (sort-by val soln))
                   txns-by-vars (->> (:txns history)
                                     (map (fn [txn] [(c/v s (:i txn)) txn]))
                                     (into {}))]
               (map txns-by-vars var-order)))
      (assoc history :error {:type :no-ext-solution}))))

(defn check-reduce
  "Transforms a history with a sequence of functions, applied in order. As soon
  as an :error is found, aborts and returns that history."
  [history fs]
  (reduce (fn [h f]
            (if (:error h)
              (reduced h)
              (f h)))
          history
          fs))

(defn check
  "Check history for correctness using the given constraint system."
  [history s]
  (check-reduce history [prepare-history
                         check-int-history
                         check-spurious-reads
                         #(check-ext-history % s)]))
