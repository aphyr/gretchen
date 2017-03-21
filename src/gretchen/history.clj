(ns gretchen.history
  "Basic operations over transactions and histories.")

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
  "Builds a transaction precedence graph based on each transaction's external
  reads."
