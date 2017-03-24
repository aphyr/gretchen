(ns gretchen.constraint
  "Polymorphic interface for constraint generation."
  (:require [potemkin :refer [definterface+]]
            [clojure.core :as c]
            [clojure.pprint :refer [pprint]]
            [clojure.walk :as walk]
            [loco.constraints :as loco]
            [loco.core]
            [gretchen.util :refer [fixed-point]])
  (:refer-clojure :exclude [t and or not < <= distinct type]))

(definterface+ Solver
  (solution [s c]))

(defn t         []            true)
(defn f         []            false)
(defn v         [v]           (keyword (str v)))
(defn and       [& as]        (vec (cons 'and as)))
(defn or        [& as]        (vec (cons 'or as)))
(defn and*      [as]          (vec (cons 'and as)))
(defn or*       [as]          (vec (cons 'or as)))
(defn not       [a]           ['not a])
(defn <         [a b]         ['< a b])
(defn <=        [a b]         ['<= a b])
(defn bool      [v]           ['bool v])
(defn in        [v min max]   ['in v min max])
(defn distinct  [vs]          (vec (cons 'distinct vs)))

(defn unfurl-binary-operators
  "Takes a Clojure tree and unfurls n-arity relations to binary form."
  [tree]
  (walk/postwalk (fn [tree]
                   (if (c/and (sequential? tree)
                              (c/or (= 'and (first tree))
                                    (= 'or  (first tree))
                                    (= '<   (first tree))
                                    (= '<=  (first tree))))
                     (reduce (partial vector (first tree)) (next tree))
                     tree))
                 tree))


(defn simplify-1
  "Simplify a Clojure constraint, in one pass."
  [c]
  ; Terminals
  (if-not (sequential? c)
    c ; Can't optimize terminals
    (let [[type & children] c
          children (map simplify-1 children)  ; Recursively simplify
          c (vec (cons type children))]       ; Rebuild expression
      (condp = type
        'and (condp = (count children)
               0 true
               1 (second c)
               (reduce (fn [as a]
                              (cond ; Short-circuit false
                                    (false? a)
                                    false

                                    ; Skip constant true
                                    (true? a)
                                    as

                                    ; Flatten nested and
                                    (c/and (sequential? a) (= 'and (first a)))
                                    (into as (next a))

                                    :else
                                    (conj as a)))
                            ['and]
                            (c/distinct children)))
        'or (condp = (count children)
              0 true
              1 (second c)
              (reduce (fn [as a]
                             (cond ; Short-circuit true
                                   (true? a)
                                   true

                                   ; Skip constant false
                                   (false? a)
                                   as

                                   ; Flatten nested and
                                   (c/and (sequential? a) (= 'or (first a)))
                                   (into as (next a))

                                   :else
                                   (conj as a)))
                           ['or]
                           (c/distinct children)))
        'not (let [child (first children)]
               (cond ; Constant negation
                     (true? child) false
                     (false? child) true

                     ; Double negation
                     (c/and (sequential? child) (= 'not (first child)))
                     (second child)

                     ; Pass through
                     true
                     c))

        ; All other node types are unoptimized
        c))))

(defn common-subexpressions
  "Identifies subexpressions which must be true in all branches of an
  expression."
  [c]
  (if-not (sequential? c)
    #{c}
    (let [[type & children] c]
      (condp = type
        'and (reduce set/union (map simplify-cse-helper children))
        'or  (if (seq children)
               (reduce set/intersection (map simplify-cse-helper children))
               #{})
        #{c}))))

(defn simplify-cse
  "Simplify a Clojure constraint by eliminating common subexpressions, moving
  them to a top-level 'and."
  [c]
  (let [common (common-subexpressions c)]
    (if-not (seq common)
      c ; Nothing to eliminate
      (vec (into ['and (postwalk-replace
                         (fn rep [c] (or (contains? common c) c)) c)]
                 common)))))

(defn simplify
  "Simplify-1 until done, then perform common subexpression elimination."
  [c]
  (->> c
       (fixed-point simplify-1)
       simplify-cse
       (fixed-point simplify-1)))

(defn cnf-literal?
  "Is the given Clojure constraint tree a CNF literal? In our case, we want to
  make sure there's no 'and or 'or nodes in the tree--inequalities are
  considered literals, and of course 'nots are as well."
  [tree]
  (->> tree
       (tree-seq sequential? next)
       (filter sequential?)
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
    (tree-seq sequential? next)
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
  (conj (mapv (partial vector 'or ['not v]) args)
        (apply vector 'or v (map (partial vector 'not) args))))

(defn or-terms
  "Given a var representing an or expression, and a sequence of vars in the or,
  returns a seq of disjunctions for the tseitin expansion of that op."
  [v args]
  ; x <-> (or y z)  <=>  (and (or x (not y)) (or x (not z)) (or (not x) y z))
  (conj (mapv (fn invert [a] ['or v ['not a]]) args)
        (apply vector 'or ['not v] args)))

(defn not-terms
  "Given a var representing a not expression, and the negated var, returns a seq of disjunctions for the tseitin expansion of that op."
  [v a]
  ; x <-> (not y)  <=>  (and (or (not x) (not y)) (or x y))
  [['or v a]
   ['or ['not v] ['not a]]])

(defn flatten-ops
  "Takes a map of operations to vars and constructs a sequence of disjunctions
  for those ops."
  [ops-to-vars]
  (mapcat (fn [[op v]]
            (let [[type & args] op
                  ; Replace child terms with their tseitin variables
                  args (if (sequential? args)
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
      {:tree (simplify (vec (cons 'and (concat (map (partial vector 'bool)
                                                    (vals mappings))
                                               top-level-constraints
                                               literals
                                               tseitin-constraints))))
       :new-vars (set (vals mappings))})

    ; General case: compute full tseitin vars over the top-level tree
    true
    (let [mappings (ops-to-vars tree 0)]
      {:tree (simplify
               (vec (cons 'and
                          (concat
                            (map (partial vector 'bool)  ; New booleans
                                 (vals mappings))
                            [(get mappings tree)]       ; Top-level constraint
                            (flatten-ops mappings)))))  ; Sub-expressions
      :new-vars (set (vals mappings))})))

(defn tseitin
  "Like tseitin+, but just returns the new tree."
  [tree]
  (:tree (tseitin+ tree)))
