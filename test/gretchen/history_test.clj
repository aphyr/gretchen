(ns gretchen.history-test
  (:refer-clojure :exclude [ancestors descendants])
  (:require [clojure.test :refer :all]
            [clojure.test.check :as tc]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [clojure.test.check.clojure-test :refer [defspec]]
            [clojure.set :as set]
            [clojure.pprint :refer [pprint]]
            [gretchen [gen :refer [r w t]]
                      [gen-test :refer [augmented-history-gen]]
                      [graph :as graph]
                      [history :refer :all]
                      [recurset :as recurset]
                      [util :refer :all]]))

(def n 1e3) ; test.spec iters

(deftest ancestors-test
  (testing "empty history"
    (is (= {{:i 0 :ops []} #{}}
           (ancestors
             (prepare-history
               {:txns []})))))

  (testing "unrelated txns"
    (let [h (prepare-history {:txns [(t (w :x 0) (w :y 0))
                                     (t (w :x 1) (w :y 1))]})
          [t0 t1 t2] (:txns h)]
      (is (= {t0 #{}
              t1 #{}
              t2 #{}}
             (ancestors h)))))

  (testing "linear chain of txns"
    (let [h (prepare-history {:initial {:x 0}
                              :txns [(t (r :x 0) (w :x 1))
                                     (t (r :x 1) (w :x 2))
                                     (t (r :x 2))]})
          [t0 t1 t2 t3] (:txns h)]
      (is (= {t0 #{}
              t1 #{t0}
              t2 #{t0 t1}
              t3 #{t0 t1 t2}}
             (ancestors h)))))

  (testing "fork-and-join"
    (let [h (prepare-history {:initial {:x 0}
                              :txns [(t (r :x 0) (w :x 1)) ; 0 < 1
                                     (t (r :x 1) (w :y 2)) ; 1 < 2
                                     (t (r :x 1) (w :z 2)) ; 1 < 3
                                     (t (r :y 2) (r :z 2))]}) ; [2 and 3] < 4
          [t0 t1 t2 t3 t4] (:txns h)]
      (is (= {t0 #{}
              t1 #{t0}
              t2 #{t1 t0}
              t3 #{t1 t0}
              t4 #{t3 t2 t1 t0}}
             (ancestors h)))))

  (testing "fork-or-join"
    (let [h (prepare-history {:initial {:x 0}
                              :txns [(t (r :x 0) (w :x 1) (w :y 1)) ; 0 < 1
                                     (t (r :x 1) (w :z 2))  ; 1 < 2
                                     (t (r :y 1) (w :z 2))  ; 1 < 3
                                     (t (r :z 2))]})        ; [2 or 3] < 4
          [t0 t1 t2 t3 t4] (:txns h)]
      (is (= {t0 #{}
              t1 #{t0}
              t2 #{t1 t0}
              t3 #{t1 t0}
              t4 #{t1 t0}}
             (ancestors h))))))
