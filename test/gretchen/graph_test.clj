(ns gretchen.graph-test
  (:require [clojure.test :refer :all]
            [clojure.test.check :as tc]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [clojure.test.check.clojure-test :refer [defspec]]
            [clojure.set :as set]
            [clojure.pprint :refer [pprint]]
            [gretchen.graph :refer :all]
            [gretchen.util :refer :all]))

(def n 1e3) ; test.spec iters

(def gen-vertices (gen/set gen/pos-int))

(defn gen-neighbors
  "Given a collection of vertices, builds a generator which generates a map of
  vertices to collections of vertices."
  [vertices]
  (if (empty? vertices)
    (gen/return {})
    (gen/map (gen/elements vertices)
             (gen/vector-distinct (gen/elements vertices)))))

(def gen-graph
  "Emits directed graphs like

      {:vertices [1 2 3]
       :neighbors    {1 [1 3] 2 [3]}}"
  (gen/bind gen-vertices
            (fn [vertices]
              (gen/hash-map :vertices (gen/return vertices)
                            :neighbors (gen-neighbors vertices)))))

(defn partition?
  "Do the given subgraphs form a total partition of the elements of universe?"
  [universe subgraphs]
  (= (sort (:vertices universe))
     (sort (apply concat (map :vertices subgraphs)))))

(defn weak-connected?
  "Is the given graph weakly connected--e.g. following neighbors in either
  direction, is every node reachable from every other?"
  [g]
  (let [neighbors (:neighbors g)
        bn (persistent!
             (reduce (fn invert [bn src]
                       (reduce (fn [bn dst]
                                 (-> bn
                                     (assoc! src (conj (get bn src []) dst))
                                     (assoc! dst (conj (get bn dst []) src))))
                               bn
                               (neighbors src)))
                     (transient {})
                     (:vertices g)))]
    (= (set (:vertices g))
       (fixed-point (fn expand [nodes]
                      (->> nodes
                           (mapcat bn)
                           (into nodes)))
                    (set (take 1 (:vertices g)))))))

(deftest weak-connected-test
  (is (weak-connected? {:vertices [1 2 3] :neighbors {3 [2] 1 [2]}}))
  (is (weak-connected? {:vertices [] :neighbors {}}))
  (is (not (weak-connected? {:vertices [1 2 3] :neighbors {1 [2]
                                                           2 [1]
                                                           3 [3]}}))))

(deftest disjoint-subgraphs-test
  (is (= #{#{0 1} #{2 3}}
         (set (map :vertices
                   (disjoint-subgraphs
                     {:vertices #{0 1 2 3}
                      :neighbors {1 [0]
                                  2 [2 3]
                                  3 [2]}}))))))

(defspec disjoint-subgraphs-spec
  n
  (prop/for-all [g gen-graph]
                (let [subgraphs (disjoint-subgraphs g)]
                  (or (and (partition? g subgraphs)
                           (every? weak-connected? subgraphs))
                      (prn :----------)
                      (pprint g)
                      (pprint subgraphs)))))
