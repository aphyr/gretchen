(ns gretchen.bottleneck-test
  (:require [clojure.test :refer :all]
            [gretchen [gen :refer [t r w]]
                      [bottleneck :refer :all]
                      [history :as h :refer [prepare-history]]]))

(deftest bottlenecks-test
  (let [b (comp set bottlenecks- h/prepare-history)]
    (testing "empty history"
      (is (= #{{:i 0, :ops []}} ; implict first txn is a bottleneck
             (b {:initial {}
                 :txns []}))))

    (testing "linear chain of txns"
      (let [h (prepare-history {:initial {:x 0}
                                :txns [(t (r :x 0) (w :x 1))
                                       (t (r :x 1) (w :x 2))
                                       (t (r :x 2) (w :x 3))]})
            [t0 t1 t2 t3] (:txns h)]
        (is (= #{t0 t1 t2 t3} (set (bottlenecks- h))))))

    (testing "independent txns"
      (let [h (prepare-history {:initial {:x 0 :y 0}
                                :txns [(t (r :y 0) (w :x 1))
                                       (t (r :y 0) (w :x 2))
                                       (t (r :x 2))]})
            [t0 t1 t2 t3] (:txns h)]
        (is (= #{t0} (set (bottlenecks- h))))))

    (testing "fork-and-join"
      ; t4 is a bottleneck because both t2 and t3 must precede it (and by
      ; extension, t1 and then t0).
      (let [h (prepare-history {:initial {:x 0}
                                :txns [(t (r :x 0) (w :x 1)) ; 0 < 1
                                       (t (r :x 1) (w :y 2)) ; 1 < 2
                                       (t (r :x 1) (w :z 2)) ; 1 < 3
                                       (t (r :y 2) (r :z 2))]}) ; [2 & 3] < 4
            [t0 t1 t2 t3 t4] (:txns h)]
        (is (= #{t0 t1 t4} (set (bottlenecks- h))))))

    (testing "fork-or-join"
      ; Here, t4 is not a bottleneck, because we can't prove that both t2 and t3
      ; had to happen prior.
      (let [h (prepare-history {:initial {:x 0}
                                :txns [(t (r :x 0) (w :x 1) (w :y 1)) ; 0 < 1
                                       (t (r :x 1) (w :z 2))  ; 1 < 2
                                       (t (r :y 1) (w :z 2))  ; 1 < 3
                                       (t (r :z 2))]})        ; [2 or 3] < 4
            [t0 t1 t2 t3 t4] (:txns h)]
        (is (= #{t0 t1} (set (bottlenecks- h))))))))
