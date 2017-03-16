(ns gretchen.constraint.flatzinc-test
  (:require [clojure.test :refer :all]
            [clojure.test.check :as tc]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [clojure.test.check.clojure-test :refer [defspec]]
            [clojure.walk :refer [postwalk-replace]]
            [clojure.set :as set]
            [clojure.math.numeric-tower :refer [expt]]
            [clojure.pprint :refer [pprint]]
            [gretchen.constraint-test :as ct]
            [gretchen.constraint.flatzinc :refer :all]))

(def n 100) ; test.spec iters

(deftest flatzinc-test
  (is (= (str "\nvar bool: x :: output_var;\n"
              "\n\n"
              "constraint bool_eq(x, true);\n"
              "\n"
              "solve satisfy;\n")
         (flatzinc-str '(and (bool :x)
                             :x))))

  (is (= (str "var 0..2: a :: output_var;\n"
              "var 0..2: b :: output_var;\n"
              "\n\n\n"
              "constraint int_lt(a, b);\n"
              "\n"
              "solve satisfy;\n")
         (flatzinc-str '(and (in :a 0 2)
                             (in :b 0 2)
                             (< :a :b)))))

  (is (= (str "var 0..2: a :: output_var;\n"
              "var 0..2: b :: output_var;\n"
              "\n\n"
              "var bool: _fz0 :: var_is_introduced :: is_defined_var;\n"
              "var bool: _fz1 :: var_is_introduced :: is_defined_var;\n"
              "var bool: _fz2 :: var_is_introduced :: is_defined_var;\n"
              "\n"
              "constraint bool_or(_fz1, _fz2, _fz0) :: defines_var(_fz0);\n"
              "constraint int_lt_reif(a, b, _fz1) :: defines_var(_fz1);\n"
              "constraint int_lt_reif(b, a, _fz2) :: defines_var(_fz2);\n"
              "constraint bool_eq(_fz0, true);\n"
              "\n"
              "solve satisfy;\n")
         (flatzinc-str '(and (in :a 0 2)
                             (in :b 0 2)
                             (or (< :a :b)
                                 (< :b :a))))))

  (is (= #{{:a 0 :b 1}
           {:a 0 :b 2}
           {:a 1 :b 2}
           {:a 1 :b 0}
           {:a 2 :b 0}
           {:a 2 :b 1}}
         (set (solutions '(and (in :a 0 2)
                               (in :b 0 2)
                               (or (< :a :b)
                                   (< :b :a))))))))

(defspec tseitin-spec
  n
  (prop/for-all [e ct/gen-full-expr]
                (let [brute-solutions (ct/solutions e)
                      fz-solutions    (solutions e)]
                  (or (= (set brute-solutions)
                         (set fz-solutions))
                      (println)
                      (println "----------------------------------------------")
                      (println "Expression to solve")
                      (pprint e)
                      (println)
                      (println "Brute-force solutions")
                      (pprint (set brute-solutions))
                      (println)
                      (println "Flatzinc-gecode solutions")
                      (pprint (set fz-solutions))))))
