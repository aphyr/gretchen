(ns regina.core-test
  (:require [clojure.test :refer :all]
            [clojure.pprint :refer [pprint]]
            [regina.core :refer :all]
            [regina.gen :as gen]))

(deftest history-test
  (->> {:x 0 :y 0}
       (gen/history 10)
       check-int-history
       :txns
       pr-history))
