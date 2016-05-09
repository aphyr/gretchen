(ns regina.core
  "In 'A Framework for Transactional Consistency Models with Atomic
  Visibility', Cerone, Bernardi, and Gotsman present a formal model for
  transactions composed of ordered reads and writes on a set of registers.
  Among other properties, they show that serializability can be defined in
  terms of three properties:

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
  appears to be the fastest option available.

  However, we can *reduce* the search space dramatically by applying
  heuristics. First, note that the denser the register state space--the more
  reads and writes have the same values--the more valid serializations we are
  likely to have. A test of serializability will likely *limit* degeneracy,
  using many distinct values.

  When degeneracy is small, we can identify prior transactions for EXT in
  constant time for any given transaction, so long as we have a few (linear
  time) indexes identifying which transactions could have written those values.

  ## Approach

  Consider a set of n transactions. For simplicity, we construct an initial
  transaction T_0, which simply writes the initial state.

  Then, for every transaction T_i where 0 < i <= n, take the set of external
  reads R: a map from keys to values. We want to obtain a constraint on AR
  which guarantees that by T_i, R is a subset of the current table state.

  For all r = (k, v) in R, let the set of transactions externally writing (k,
  v) be W (Writes), and the set of all transactions externally writing (k,
  not-v) be O (Overwrites). r is satisfied iff:

  1. There exists some T_w in W | w < i (e.g. the write precedes the read)
  2. There exists no T_o in O | w < o < i (the write is not overwritten)

  So for each read, we will generate a series of alteratives, like

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
  position in the order."
  (:require [clojure.string :as str]))

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
                                         ::error {:op op
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
;
; 
