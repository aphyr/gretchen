(ns gretchen.constraint-test
  (:require [clojure.test :refer :all]
            [clojure.test.check :as tc]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [clojure.test.check.clojure-test :refer [defspec]]
            [clojure.walk :refer [postwalk
                                  postwalk-replace]]
            [clojure.set :as set]
            [clojure.math.numeric-tower :refer [expt]]
            [clojure.pprint :refer [pprint]]
            [gretchen.constraint :as c :refer [simplify
                                             tseitin]]))

(def n 100) ; test.spec iters
(def int-vars #{:i :j :k})
(def bool-vars #{:a :b :c})

(defn var-declarations
  "Given a constraint tree, what variable declarations are in it?"
  [tree]
  (->> tree
       (tree-seq sequential? next)
       (filter sequential?)
       (filter (comp #{'in 'bool} first))
       (into #{})))

(defn vars
  "Given a constraint tree, what variables (keywords) are in it?"
  [tree]
  (->> tree
       (tree-seq sequential? next)
       (filter keyword?)
       (into (sorted-set))))

(def gen-bool-var (gen/elements bool-vars))
(def gen-int-var  (gen/elements int-vars))

(def gen-int-relation
  (->> (gen/tuple (gen/elements ['< '<=]) gen-int-var gen-int-var)
       (gen/such-that (fn [t] (= 3 (count t))))
       (gen/fmap (partial apply vector))))

(def gen-bool-terminal (gen/one-of [gen-bool-var
                                    gen-int-relation]))



(defn gen-compound
  [g]
  (gen/one-of [(gen/fmap (partial vector 'not) g)
               (gen/fmap (comp vec (partial cons 'and)) (gen/tuple g g))
               (gen/fmap (comp vec (partial cons 'or)) (gen/tuple g g))]))

(defn add-declarations
  "Add variable declarations to a generated expression."
  [tree]
  (apply list 'and tree
         (->> (vars tree)
              (map (fn [v]
                     (if (bool-vars v)
                       ['bool v]
                       ['in v 0 2]))))))

(def gen-bool-expr
  "Basic boolean expressions"
  (gen/fmap add-declarations
            (gen/recursive-gen gen-compound gen-bool-var)))

(def gen-full-expr
  "Both booleans and integers"
  (gen/fmap add-declarations
            (gen/recursive-gen gen-compound gen-bool-terminal)))

(def gen-simple-expr
  (gen/fmap simplify gen-full-expr))

(defn bool-assignments
  "Given a collection of boolean variables like '(bool v), computes all
  possible maps of variables to boolean values. Only up to 62 vars."
  [vars]
  (if-not (seq vars)
    [{}]
    (let [vars (object-array (map second vars))
          n    (count vars)]
      (assert (< n 63)) ; Math.pow breaks here
      (->> (range (Math/pow 2 n))
           (map (fn [i]
                  (->> (range n)
                       (map (fn [v]
                              [(aget vars v) (pos? (bit-and i (expt 2 v)))]))
                       (into {}))))))))

(defn int-assignments-
  "Helper for int-assignments"
  [vars lowers uppers values]
  (cons (zipmap vars values)
        (lazy-seq
          (loop [i      0
                 values values]
            (if (<= (count vars) i)
              ; Can't go any further
              nil
              (let [var   (nth vars i)
                    lower (nth lowers i)
                    upper (nth uppers i)
                    value (nth values i)]
                (if (< value upper)
                  ; We can increment this value
                  (int-assignments- vars lowers uppers
                                    (assoc values i (inc value)))
                  ; Out of range; zero and carry
                  (recur (inc i) (assoc values i lower)))))))))

(defn int-assignments
  "Given a collection of integer declarations like '(in v 0 2), computes all
  possible maps of variables to integer values."
  [ins]
  (if-not (seq ins)
    [{}]
    (let [vars   (mapv second ins)
          lowers (mapv #(nth % 2) ins)
          uppers (mapv #(nth % 3) ins)]
      (int-assignments- vars lowers uppers lowers))))

(deftest int-assignments-test
  (is (= [{:x 1 :y 0}
          {:x 2 :y 0}
          {:x 1 :y 1}
          {:x 2 :y 1}
          {:x 1 :y 2}
          {:x 2 :y 2}]
         (int-assignments '[(in :x 1 2) (in :y 0 2)]))))

(defn assignments
  "Given a collection of variable declarations, computes all possible
  assignments to those variables."
  [vars]
  (let [vars (group-by first vars)
        ints (int-assignments (get vars 'in))
        bools (bool-assignments (get vars 'bool))]
    (for [i ints, b bools]
      (merge i b))))

(deftest assignments-test
  (is (= [{:a false}
          {:a true}]
         (assignments '#{(bool :a)}))))

(defn solution?
  "Is the given map of variables to boolean values a satisfying assignment for
  the given expression tree?"
  [tree assignment]
  (cond ; Variable lookup
        (keyword? tree)
        (get assignment tree)

        ; Recurse
        (sequential? tree)
        (let [[type & children] tree]
          (condp = type
            'bool (let [v (get assignment (first children))]
                    (or (true? v) (false? v)))
            'in   (let [[var lower upper] children]
                    (<= lower (get assignment var) upper))
            '<    (let [[v1 v2] children]
                    (< (solution? v1 assignment) (solution? v2 assignment)))
            '<=   (let [[v1 v2] children]
                    (<= (solution? v1 assignment) (solution? v2 assignment)))
            'not (not (solution? (first children) assignment))
            'or  (loop [v        nil
                        children children]
                   (if-not (seq children)
                     v
                     (let [x (solution? (first children) assignment)]
                       (if x
                         x
                         (recur x (next children))))))
            'and (loop [children children]
                   (if-not (seq children)
                     true
                     (let [x (solution? (first children) assignment)]
                       (if x
                         (recur (next children))
                         x))))))

        ; Literals fall through
        true
        tree))

(defn clojure-eval-able
  "Turns an expression tree into something you can eval with Clojure."
  [tree ass]
  (postwalk
    (fn [form]
      ; (prn :postwalk form)
      ; Look up variables in assignment map
      (cond (keyword? form)
            (get ass form)

            ; Turn declarations into clojure predicates
            (sequential? form)
            (let [form (seq form)] ; Map back to code
              (condp = (first form)
                'in (list '<=
                          (nth form 2)
                          (second form)
                          (nth form 3))
                'bool (or (true? (second form))
                          (false? (second form)))
                form))

            true
            form))
    tree))


(defspec solution-spec
  n
  (prop/for-all [expr gen-full-expr
                 ass  (gen/hash-map :a gen/boolean
                                    :b gen/boolean
                                    :c gen/boolean
                                    :i gen/int
                                    :j gen/int
                                    :k gen/int)]
                (try
                  (or (= (solution? expr ass)
                         (eval (clojure-eval-able expr ass)))
                      (prn :ass ass)
                      (prn :expr (solution? expr ass) expr)
                      (prn :clj (eval (clojure-eval-able expr ass))
                           (clojure-eval-able expr ass)))
                  (catch Throwable t
                      (prn :ass ass)
                      (prn :expr (solution? expr ass) expr)
                      (prn :clj (clojure-eval-able expr ass))
                      (prn :clj-res (eval (clojure-eval-able expr ass)))
                      (throw t)))))

(defn solutions
  "Given a constraint tree, finds all maps of variables to boolean values which
  satisfy that constraint."
  [tree]
  (->> tree var-declarations assignments (filter (partial solution? tree))))

(defn equivalent?
  "Given two expressions a and b, does every assignment of variables result in
  identical boolean values?"
  [a b]
  (let [vars (set/union (var-declarations a) (var-declarations b))]
;    (prn :a)
;    (pprint a)
;    (prn :b)
;    (pprint b)
    (every? (fn [ass] (= (solution? a ass)
                         (solution? b ass)))
            (assignments vars))))

(defn subsatisfiable?
  "Given two constraint trees a and b, where b's variables are a superset of
  a's, ensures that either:

  - a is not satisfiable, and b is not satisfiable
  - both are satisfiable, and every solution to b is also a solution to a"
  [a b]
  (let [b-solns (solutions b)]
    (or (and (empty? b-solns)
             (empty? (solutions a)))
        (every? (partial solution? a) b-solns))))

(deftest simplify-test
  (is (= false    (simplify '(not true))))
  (is (= true     (simplify '(not false))))
  (is (= 'a       (simplify '(not (not a)))))
  (is (= '(not a) (simplify '(not a)))))

(defspec simplify-spec
  n
  (prop/for-all [e gen-full-expr]
                (or (equivalent? (simplify e) e)
                    (prn :full e)
                    (prn :smpl (simplify e)))))

(deftest cnf-literal?-test
  (is (c/cnf-literal? :a))
  (is (c/cnf-literal? '(not :a)))
  (is (c/cnf-literal? '(not (< :a :b))))
  (is (not (c/cnf-literal? '(not (or :a :b)))))
  (is (not (c/cnf-literal? '(and :a :b)))))

; See http://www.decision-procedures.org/handouts/Tseitin70.pdf
; See http://fmv.jku.at/biere/talks/Biere-VTSA12-talk.pdf
(deftest and-terms-test
  (is (= '[(or (not x) y)
           (or (not x) z)
           (or x (not y) (not z))]
         (c/and-terms 'x '(y z)))))

(deftest or-terms-test
  (is (= '[(or x (not y))
           (or x (not z))
           (or (not x) y z)]
         (c/or-terms 'x '(y z)))))

(deftest not-terms-test
  (is (= '[(or x y)
           (or (not x) (not y))]
         (c/not-terms 'x 'y))))

(deftest ops-to-vars-test
  (testing "single level"
    (is (= {'(and :a :b) :_t1}
           (c/ops-to-vars '(and :a :b) 1))))

  (testing "nested"
  (is (= {'(and :a :b) :_t2
          '(or (and :a :b) :c) :_t1}
          (c/ops-to-vars '(or (and :a :b) :c) 1)))))

(deftest tseitin-test
;  (testing "A constant"
;    (is (= true (tseitin true))))

  (testing "already in cnf"
    (testing "literals"
      (is (= true (tseitin true)))
      (is (= false (tseitin false)))
      (is (= '(< :a :b) (tseitin '(< :a :b))))
      (is (= '(not :a) (tseitin '(not :a)))))

    (testing "empty and"
      (is (= '(and) (tseitin '(and)))))

    (testing "and of literals"
      (is (= '(and :a (not :b) (< :a :b))
             (tseitin '(and :a (not :b) (< :a :b))))))

    (testing "or of literals"
      (is (= '(or :a (not :b))
             (tseitin '(or :a (not :b))))))

    (testing "and of ors of literals"
      (is (= '(and :a (or :b (not :c)))
             (tseitin '(and :a (or :b (not :c))))))))

  (testing "or of and"
    (is (= '(and ; New vars
                 (bool :_t0)
                 (bool :_t1)
                 ; Top level constraint
                 :_t0
                 ; _0: (or :a :v1)
                 (or :_t0 (not :a))
                 (or :_t0 (not :_t1))
                 (or (not :_t0) :a :_t1)
                 ; _1: (and :b :c)
                 (or (not :_t1) :b)
                 (or (not :_t1) :c)
                 (or :_t1 (not :b) (not :c)))
           (tseitin '(or :a (and :b :c))))))

  (let [t '(or :a (and :b :c))]
    (is (subsatisfiable? t (tseitin t)))))

(defspec tseitin-spec
  n
  (prop/for-all [e gen-simple-expr]
                (try
                  (subsatisfiable? e (tseitin e))
                  (catch Throwable t
                    (prn :expr e)
                    (prn :tsei (tseitin e))
                    (throw t)))))
