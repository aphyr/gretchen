(ns gretchen.recurset
  "Persistent sorted sets with memory-efficient, constant-time union and
  intersection, and O((n + m) * c) iteration, where n is the number of
  elements, c is the typical size of the set at any given node, and m is the
  number of intersections and unions.

  Note that construction of unions and intersections sorts their arguments by a
  constant-time upper bound on their size, so that the biggest sub-nodes are
  probably first. When we append a node's elements to our backwards stack, we
  wind up working with smaller sets first."
  (:require [potemkin :refer [definterface+ deftype+]]
            [clojure.set :as set])
  (:import (java.util ArrayList)
           (clojure.lang Seqable)))

(def eager-max-count-limit
  "When you call union or intersection, we may perform that set operation
  immediately, rather than creating an indirect node. This is the upper bound
  on a set we'll realize eagerly."
  64)

(declare to-set)

(definterface+ Node
  (xs [node]))

(deftype Union [xs max-count]
  Node
  (xs [_] xs)

  Seqable
  (seq [this] (seq (to-set this)))

  Object
  (toString [this] (str "(∪ " (apply str (interpose " " xs)) ")")))

(deftype Intersection [xs max-count]
  Node
  (xs [_] xs)

  Seqable
  (seq [this] (seq (to-set this)))

  Object
  (toString [this] (str "(∩ " (apply str (interpose " " xs)) ")")))

(defmethod print-method Union
  [x ^java.io.Writer w]
  (.write w (str x)))

(defmethod print-method Intersection
  [x ^java.io.Writer w]
  (.write w (str x)))

(defn max-count
  "Upper bound on the number of elements in a collection."
  [coll]
  (condp identical? (class coll)
    Union         (.max-count ^Union coll)
    Intersection  (.max-count ^Intersection coll)
    (count coll)))

(defn prepare
  "We need to make sure that everything we accept is a literal Set or a
  Union/Intersection type. This function coerces collections to those types."
  [coll]
  (if (or (identical? (class coll) Intersection)
          (identical? (class coll) Union)
          (set? coll))
    coll
    (set coll)))

(defn to-set
  [coll]
  ; We build a stack machine where the stack is of the form
  ; [coll op coll op coll], for instance [a :union b :intersection c], which
  ; means "compute the union of a and b, then intersect that result with c."
  ;
  ; If our stack is a single realized collection, we're done. If it is
  ; unrealized, expand it to [a op b op c ...]. Now,
  ;
  ; Let our stack be [a op1 b op2 c]. If a and b are realized collections, let
  ; res be (op1 a b), and our resulting stack is [res op2 c].
  ;
  ; If a is an unrealized union or intersection o over a1, a2, and a3, then our
  ; resulting stack is [a1 o a2 o a3 op1 b op2 c].
  ;
  ; If a is realized but b is not, our new stack is [b op1 a op2 c], by the
  ; commutativity of intersection and union.
  ;
  ; For performance reasons, our stack is an arraylist and is backwards--so the
  ; first element of the stack has index (dec (count stack)).
  ;
  ; Todo: use bifurcan LinearSet.
  (if-not (or (identical? (class coll) Union)
              (identical? (class coll) Intersection))
    (set coll)
    (let [stack (ArrayList. ^java.util.List (list coll))]
      (loop []
        ; (prn :stack (reverse stack))
        (let [size (.size stack)]
          (if (= 1 size)
            ; Just one element in the stack; we're either starting or finishing
            (let [a (.get stack 0)
                  op (class a)]
              (if (or (identical? op Union)
                      (identical? op Intersection))
                ; Single unrealized node; expand
                (do (.clear stack)
                    (.addAll stack (interpose op (.xs ^Node a)))
                    (recur))
                ; Realized, we're done!
                a))

            ; OK, multiple elements. What's on deck?
            (let [size (.size stack)
                  a    (.get stack (- size 1))
                  op   (.get stack (- size 2))
                  b    (.get stack (- size 3))]
              (cond ; Haven't realized a yet, expand
                    (or (identical? (class a) Union)
                        (identical? (class a) Intersection))
                    (do (.remove stack (int (- size 1)))
                        (.addAll stack (interpose (class a) (.xs ^Node a)))
                        (recur))

                    ; We've got a but not b; swap
                    (or (identical? (class b) Union)
                        (identical? (class b) Intersection))
                    (do (.set stack (- size 3) a)
                        (.set stack (- size 1) b)
                        (recur))

                    ; Both a and b are realized; evaluate
                    true
                    (do (.remove stack (- size 1))
                        (.remove stack (- size 2))
                        (.set stack (- size 3)
                              (if (identical? op Union)
                                (set/union a b)
                                (set/intersection a b)))
                        (recur))))))))))

(defn union
  "Constructs a set representing the union of the given sets."
  [sets]
  (condp = (count sets)
    0 #{}
    1 (prepare (first sets))
    (let [max-count' (reduce + (map max-count sets))]
      (if (<= max-count' eager-max-count-limit)
        ; Realize eagerly
        (apply set/union (map to-set sets))
        ; Create a lazy node
        (Union. (sort-by (comp - max-count) (map prepare sets))
                max-count')))))

(defn intersection
  "Constructs a set representing the intersection of the given sets."
  [sets]
  (condp = (count sets)
    0 (throw (IllegalArgumentException. "Can't intersect 0 sets"))
    1 (prepare (first sets))
    (let [max-count' (reduce min (map max-count sets))]
      (if (<= max-count' eager-max-count-limit)
        (apply set/intersection (map to-set sets))
        (Intersection. (sort-by (comp - max-count) (map prepare sets))
                       max-count')))))
