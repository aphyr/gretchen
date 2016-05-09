(ns regina.gen
  "Generates histories for testing.")

(defn rand-key
  [state]
  (rand-nth (keys state)))

(defn read-op
  "Constructs a random read op on state. Returns [state', read-op]"
  [state]
  (let [k (rand-key state)
        v (get state k)]
    [state, {:f :read, :k k, :v v}]))

(defn write-op
  "Constructs a random write op on state. Returns [state', write-op]"
  [state]
  (let [k (rand-key state)
        v (rand-int 128)]
    [(assoc state k v), {:f :write, :k k, :v v}]))

(defn op
  "Constructs a random op on state. Returns [state', op]."
  [state]
  ((rand-nth [read-op write-op]) state))

(defn txn
  "Constructs a random transaction on state. Returns [state', txn]."
  [state]
  (loop [i      (rand-int 5)
         state  state
         ops    []]
    (if (zero? i)
      [state {:ops ops}]
      (let [[state' op] (op state)]
        (recur (dec i) state' (conj ops op))))))

(defn txns
  "A lazy sequence of transactions on state."
  [state]
  (lazy-seq
    (let [[state' txn] (txn state)]
      (cons txn (txns state')))))

(defn history
  "Constructs a history with a lazy sequence of transactions from the given
  state."
  [txn-count state]
  {:initial state
   :txns    (take txn-count (txns state))})
