(ns regina.constraint
  "Polymorphic interface for constraint generation."
  (:require [potemkin :refer [definterface+]]
            [clojure.core :as c]
            [clojure.pprint :refer [pprint]]
            [clojure.walk :as walk]
            [loco.constraints :as loco]
            [loco.core])
  (:refer-clojure :exclude [t and or not < <= distinct type]))

(definterface+ Constraint
  (t                  [s])        ; true
  (f                  [s])        ; false
  (v                  [s i])      ; variable i
  (ands               [s as])     ; and
  (ors                [s as])     ; or
  (not                [s a])      ; not
  (less_than          [s a b])    ; <
  (less_than_equal_to [s a b])    ; <=
  (bool               [s v])      ; v is a boolean var
  (in                 [s v min max]) ; v is an integer between min and max
  (distinct           [s vs]))    ; vs are distinct integers

(definterface+ Solution
  (solution [s c]))

(defn and
  [s & as]
  (ands s as))

(defn or
  [s & as]
  (ors s as))

(defn and*
  [s as]
  (ands s as))

(defn or*
  [s as]
  (ors s as))

(defn <  [s a b] (less_than s a b))
(defn <= [s a b] (less_than_equal_to s a b))

(defn loco
  "Expresses constraints as loco structures."
  []
  (reify Constraint
    (t          [s]     (loco/$true))
    (f          [s]     (loco/$false))
    (v          [s i]   (keyword (str i)))
    (ands       [s as]  (apply loco/$and as))
    (ors        [s as]  (apply loco/$or as))
    (not        [s a]   (loco/$not a))
    (less_than          [s a b] (loco/$< a b))
    (less_than_equal_to [s a b] (loco/$<= a b))
    (bool               [s v]   (loco/$in v [0 1]))
    (in                 [s v min max] (loco/$in v min max))
    (distinct           [s vs] (loco/$distinct vs))

    Solution
    (solution [s c]
      ; Break apart top-level and
      (assert (= :and (:type c))
              (str "Don't know how to solve constraint which is not an :and\n\n"
                   (with-out-str (pprint c))))
      (pprint c)
      (loco.core/solution (vec (:constraints c))))))

(defn clojure
  "Expresses constraints as clojure data structures."
  []
  (reify Constraint
    (t    [s]     true)
    (f    [s]     false)
    (v    [s i]   (keyword (str i)))
    (ands [s as]  (cons 'and as))
    (ors  [s as]  (cons 'or as))
    (not  [s a]   (list 'not a))
    (less_than          [s a b] (list '< a b))
    (less_than_equal_to [s a b] (list '<= a b))
    (bool               [s v]         (list 'bool v))
    (in                 [s v min max] (list 'in v min max))
    (distinct           [s vs]        (apply list 'distinct vs))))

(defn clojure->
  "Convert a clojure constraint c to the given constraint system s."
  [s c]
  (cond
    (= true c)   (t s)
    (= false c)  (f s)
    (keyword? c) (v s (name c))
    (seq? c) (let [[type & children] c
                   [child :as children] (map (partial clojure-> s) children)]
               (condp = type
                 'and  (ands s children)
                 'or   (ors s children)
                 'not  (not s child)
                 '<    (apply < s children)
                 '<=   (apply <= s children)
                 'bool (apply bool s children)
                 'in   (apply in s children)
                 'distinct (distinct s children)))
    :else c))

(defn unfurl-binary-operators
  "Takes a Clojure tree and unfurls n-arity relations to binary form."
  [tree]
  (walk/postwalk (fn [tree]
                   (if (c/and (seq? tree)
                              (c/or (= 'and (first tree))
                                    (= 'or  (first tree))
                                    (= '<   (first tree))
                                    (= '<=  (first tree))))
                     (reduce (partial list (first tree)) (next tree))
                     tree))
                 tree))

(defn simplify-1
  "Simplify a Clojure constraint, in one pass."
  [c]
  ; Terminals
  (if-not (seq? c)
    c ; Can't optimize terminals
    (let [[type & children] c
          children (map simplify-1 children)  ; Recursively simplify
          c (cons type children)]             ; Rebuild expression
      (condp = type
        'and (condp = (count children)
               0 true
               1 (second c)
               (seq (reduce (fn [as a]
                              (cond ; Short-circuit false
                                    (false? a)
                                    false

                                    ; Skip constant true
                                    (true? a)
                                    as

                                    ; Flatten nested and
                                    (c/and (seq? a) (= 'and (first a)))
                                    (into as (next a))

                                    :else
                                    (conj as a)))
                            ['and]
                            (c/distinct children))))
        'or (condp = (count children)
              0 true
              1 (second c)
              (seq (reduce (fn [as a]
                             (cond ; Short-circuit true
                                   (true? a)
                                   true

                                   ; Skip constant false
                                   (false? a)
                                   as

                                   ; Flatten nested and
                                   (c/and (seq? a) (= 'or (first a)))
                                   (into as (next a))

                                   :else
                                   (conj as a)))
                           ['or]
                           (c/distinct children))))
        'not (let [child (first children)]
               (cond ; Constant negation
                     (true? child) false
                     (false? child) true

                     ; Double negation
                     (c/and (seq? child) (= 'not (first child)))
                     (second child)

                     ; Pass through
                     true
                     c))

        ; All other node types are unoptimized
        c))))

(defn fixed-point
  "Applies f repeatedly to x until it converges."
  [f x]
  (let [x' (f x)]
;    (println "simplified\n")
;    (pprint x)
;    (println "\nto\n")
;    (pprint x')
;    (prn)
    (if (= x x')
      x
      (recur f x'))))

(defn simplify
  "Simplify-1 until done."
  [c]
  (fixed-point simplify-1 c))

(defn cnf-literal?
  "Is the given Clojure constraint tree a CNF literal? In our case, we want to
  make sure there's no 'and or 'or nodes in the tree--inequalities are
  considered literals, and of course 'nots are as well."
  [tree]
  (->> tree
       (tree-seq seq? next)
       (filter seq?)
       (map first)
       (not-any? #{'and 'or})))

(defn cnf-or-of-literals?
  "Is the given tree either a literal, or an or of literals?"
  [tree]
  (c/or (cnf-literal? tree)
        (c/and (= 'or (first tree))
               (every? cnf-literal? (next tree)))))

(defn cnf?
  "Is a given tree in CNF? e.g. is it:

  - a literal
  - an or of literals
  - and and of ors of literals"
  [tree]
  (c/or (cnf-literal? tree)
        (cnf-or-of-literals? tree)
        (c/and (= 'and (first tree))
               (every? cnf-or-of-literals? (next tree)))))

(defn ops-to-vars
  "For the Tseitin transformation, takes a tree and returns a map of and/or
  nodes to vars :v1, v2, where numbering begins at n."
  [tree n]
  (->>
    tree
    (tree-seq seq? next)
    (remove cnf-literal?)
    (reduce
      (fn [[i m] [type & children :as tree]]
        (assert (c/or (= 'and type)
                      (= 'or type)
                      (= 'not type))
                (str "Don't know how to tseitin-expand node "
                     (pr-str tree)))
        [(inc i)
         (assoc m tree (keyword (str "_t" (+ n i))))])
      [0 {}])
    second))

(defn and-terms
  "Given a var representing an and axpression, and a sequence of vars in the
  and, returns a seq of disjunctions for the tseitin expansion of that op"
  [v args]
  ; x <-> (and y z)  <=>  (and (or x (not y)) (or x (not z)) (or (not x) y z))
  (cons (apply list 'or v (map (partial list 'not) args))
        (map (partial list 'or (list 'not v)) args)))

(defn or-terms
  "Given a var representing an or expression, and a sequence of vars in the or,
  returns a seq of disjunctions for the tseitin expansion of that op."
  [v args]
  ; x <-> (or y z)  <=>  (and (or x (not y)) (or x (not z)) (or (not x) y z))
  (cons (apply list 'or (list 'not v) args)
        (map (fn invert [a] (list 'or v (list 'not a))) args)))

(defn not-terms
  "Given a var representing a not expression, and the negated var, returns a seq of disjunctions for the tseitin expansion of that op."
  [v a]
  ; x <-> (not y)  <=>  (and (or (not x) (not y)) (or x y))
  [(list 'or v a)
   (list 'or (list 'not v) (list 'not a))])

(defn flatten-ops
  "Takes a map of operations to vars and constructs a sequence of disjunctions
  for those ops."
  [ops-to-vars]
  (mapcat (fn [[op v]]
            (let [[type & args] op
                  ; Replace child terms with their tseitin variables
                  args (if (seq? args)
                         (map (fn [a] (get ops-to-vars a a)) args)
                         args)]
              (condp = type
                'and (and-terms v args)
                'or  (or-terms v args)
                'not (not-terms v (first args)))))
          ops-to-vars))

(defn tseitin+
  "Takes a Clojure constraint tree, and returns

      {:tree      A new constraint tree in conjunctive normal form
       :new-vars  A set of the new logic variables introduced,
                  which may be discarded when computing solutions to this
                  tree}"
  [tree]
  ; TODO: look at optimizations from Plaisted and Greenbaum 86
  ; TODO: eliminate superfluous checks like
  ; (and :_0 (or :_0 :_1) (or (not :_0) (not :_1)) ...)
  (cond
    ; If we're already in CNF, return unchanged
    (cnf? tree)
    {:tree     tree
     :new-vars #{}}

    ; For the special case of a top-level 'and, we can partition our terms into
    ; those which are ors of literals (we'll call them literals for short), and
    ; those which require expansion (call those nonliterals). Pass through
    ; literals unchanged. Compute Tseitin vars for each non-literal term, and
    ; collect their resulting constraints.
    (= 'and (first tree))
    (let [g (group-by cnf-or-of-literals? (next tree))
          literals (get g true)
          nonliterals (get g false)
          ; For each nonliteral, compute a mapping of its nonliteral terms to
          ; tseitin vars, and merge that into a unified tree.
          mappings (->> nonliterals
                        (reduce (fn [[i m] tree]
                             (let [mapping (ops-to-vars tree i)]
                               [(+ i (count mapping))
                                (merge mapping m)]))
                           [0 {}])
                        second)
          ; Compute new constraints based on tseitin mappings
          tseitin-constraints   (flatten-ops mappings)
          ; And global constraints for the top-level terms themselves
          top-level-constraints (map mappings nonliterals)]
      {:tree (simplify (cons 'and (concat (map (partial list 'bool)
                                               (vals mappings))
                                          top-level-constraints
                                          literals
                                          tseitin-constraints)))
       :new-vars (set (vals mappings))})

    ; General case: compute full tseitin vars over the top-level tree
    true
    (let [mappings (ops-to-vars tree 0)]
      {:tree (simplify
               (cons 'and
                     (concat
                       (map (partial list 'bool)  ; New booleans
                            (vals mappings))
                       (list (get mappings tree)) ; Top-level constraint
                       (flatten-ops mappings))))  ; Sub-expression constraints
      :new-vars (set (vals mappings))})))

(defn tseitin
  "Like tseitin+, but just returns the new tree."
  [tree]
  (:tree (tseitin+ tree)))
