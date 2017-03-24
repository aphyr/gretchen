(ns gretchen.recurset-test
  (:require [clojure.test :refer :all]
            [clojure.test.check :as tc]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [clojure.test.check.clojure-test :refer [defspec]]
            [clojure.set :as set]
            [clojure.pprint :refer [pprint]]
            [gretchen.recurset :refer :all]
            [gretchen.util :refer :all]))

(def n 1e3) ; test.spec iters

(def gen-set (gen/vector gen/pos-int))
(defn gen-ast-node
  [g]
  (gen/one-of [(gen/fmap (partial cons :union) (gen/vector g))
               (gen/fmap (partial cons :intersection) (gen/vector g))]))
(def gen-ast (gen/recursive-gen gen-ast-node gen-set))

(defn evaluate [[type & args :as ast]]
  (condp = type
    :union        (apply set/union (map evaluate args))
    :intersection (apply set/intersection (map evaluate args))
    (set ast)))

(defn build [[type & args :as ast]]
  (condp = type
    :union        (union        (map build args))
    :intersection (intersection (map build args))
    ast))

(defspec set-spec
  n
  (with-redefs [eager-max-count-limit 4]
    (prop/for-all [ast gen-ast]
                  (let [clj-soln (try (evaluate ast)
                                      (catch clojure.lang.ArityException e
                                        :universe))
                        our-soln (try (to-set (build ast))
                                      (catch IllegalArgumentException e
                                        (if (= (.getMessage e)
                                               "Can't intersect 0 sets")
                                          :universe
                                          (throw e))))]
                    (or (= clj-soln our-soln)
                        (prn)
                        (pprint ast)
                        (prn :clojures clj-soln)
                        (prn :recurset our-soln))))))
