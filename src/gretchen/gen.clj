(ns gretchen.gen
  "Generates histories for testing.")

(def epoch-key
  "A key used as a monotonic epoch for breaking up large histories."
  :epoch)

(defn rand-key
  [state]
  (rand-nth (remove #{epoch-key} (keys state))))

(defn r
  "Shorthand read constructor."
  [k v]
  {:f :read, :k k, :v v})

(defn w
  "Shorthand write constructor."
  [k v]
  {:f :write, :k k, :v v})

(defn t
  "Generate transaction from seq of ops."
  [& ops]
  {:ops (vec ops)})

(defn read-epoch-op
  "Op that reads the current epoch. Returns [state' op]"
  [state]
  [state {:f :read, :k epoch-key, :v (get state epoch-key)}])

(defn inc-epoch-op
  "Op that advances epoch by 1. Takes state, returns [state' op]"
  [state]
  (let [epoch (inc (get state epoch-key))]
    [(assoc state epoch-key epoch)
     {:f :write, :k epoch-key, :v epoch}]))

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
        v (rand-int 100)]
    [(assoc state k v), {:f :write, :k k, :v v}]))

(defn op
  "Constructs a random op on state. Returns [state', op]."
  [state]
  ((rand-nth [read-op write-op]) state))

(defn txn
  "Constructs a random transaction on state. Returns [state', txn]."
  [state]
  (let [[state epoch-read] (read-epoch-op state)
        [state epoch-write] (if (< (rand) 0.1)
                               (inc-epoch-op state)
                               [state nil])
         ops (if epoch-write
               [epoch-read epoch-write]
               [epoch-read])]
    (loop [i      (inc (rand-int 4))
           state  state
           ops    ops]
      (if (zero? i)
        [state {:ops ops}]
        (let [[state' op] (op state)]
          (recur (dec i) state' (conj ops op)))))))

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
  (assert (not (contains? state epoch-key)))
  (let [state (assoc state epoch-key 0)]
    {:initial state
     :txns    (take txn-count (txns state))}))

(defn shuffle-history
  "A history with shuffled transactions."
  [txn-count state]
  (update (history txn-count state) :txns shuffle))
