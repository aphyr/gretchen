(ns gretchen.gen-test
  (:require [clojure.test :refer :all]
            [clojure.test.check.generators :as gen]
            [gretchen.history :as history]))

(def key-gen (gen/elements [:x :y :z]))
(def val-gen gen/pos-int)
(def op-gen  (gen/hash-map :f (gen/elements [:read :write])
                           :k key-gen
                           :v val-gen))
(def txn-gen (gen/hash-map
               :ops (gen/vector op-gen)))
(def state-gen (gen/map key-gen val-gen))
(def history-gen (gen/hash-map :initial state-gen
                               :txns    (gen/vector txn-gen)))
(def augmented-history-gen
  (gen/fmap history/prepare-history history-gen))
