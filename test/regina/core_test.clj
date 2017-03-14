(ns regina.core-test
  (:require [clojure.test :refer :all]
            [clojure.pprint :refer [pprint]]
            [regina.core :refer :all]
            [regina.constraint :as c]
            [regina.gen :as gen :refer [t r w]]
            [loco.core :as loco]))

(deftest history-test
  (->> {:x 0 :y 0}
       (gen/history 10)
       check-int-history))
;       pr-history))

(deftest constraint-test
  (is (= '(and
            (in :0 0 2)
            (in :1 0 2)
            (in :2 0 2)
            (distinct :0 :1 :2)
            (< :0 :1)
            (or (< :2 :0) (< :1 :2)))
         (-> {:initial {:x 0}       ; t0
              :txns [(t (r :x 0))   ; t1
                     (t (w :x 1))]} ; t2
             prepare-history
             (history-constraint (c/clojure))))))

(deftest perf-test
  (let [h (gen/history 50 {:x 0 :y 0 :z 0})]
    (pprint (history-constraint (prepare-history h) (c/clojure)))
    (pprint (check h (c/loco)))))

(deftest check-test
  (testing "wx0, rx0, wx1"
    (is (= [{:ops [{:f :write, :k :x, :v 0}], :i 0}  ; t0
            {:ops [{:f :read, :k :x, :v 0}],  :i 1}  ; t1
            {:ops [{:f :write, :k :x, :v 1}], :i 2}] ; t2
           (:solution (check {:initial {:x 0}       ; t0
                              :txns [(t (r :x 0))   ; t1
                                     (t (w :x 1))]} ; t2
                             (c/loco))))))

  (testing "P0 Dirty Write"
    ; A value pops into appearance out of nowhere (e.g. written by an aborted
    ; back txn)
    (is (= {:type :spurious-read
            :reads [{:txn {:ops [(r :x 1)] :i 1}
                     :k :x
                     :v 1}]}
           (:error (check {:initial {:x 0}
                           :txns [(t (r :x 1))]}
                          (c/loco))))))

  (testing "P4 Lost Update"
    ; Two read-modify-write increments
    (is (= {:type :no-ext-solution}
           (:error (check {:initial {:x 0}
                           :txns [(t (r :x 0) (w :x 1))
                                  (t (r :x 0) (w :x 1))]}
                          (c/loco))))))

  ; See Berenson, et al 1995, "A Critique of ANSI SQL Isolation Levels"
  ; https://arxiv.org/pdf/cs/0701157.pdf
  (testing "A5A Read Skew"
    (let [init {:x 0, :y 0}
          t1 (t (r :x 0) (r :y 1))
          t2 (t (w :x 1) (w :y 1))]
      (is (= {:type :no-ext-solution}
             (:error (check {:initial init :txns [t1 t2]} (c/loco)))))))

  (testing "A5B Write Skew"
    (let [init {:x 0, :y 0}
          t1 (t (r :x 0) (r :y 0) (w :x 1))
          t2 (t (r :x 0) (r :y 0) (w :y 2))]
      (is (= {:type :no-ext-solution}
             (:error (check {:initial init :txns [t1 t2]} (c/loco))))))))
