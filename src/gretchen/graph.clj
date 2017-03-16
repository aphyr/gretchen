(ns gretchen.graph
  "Assists with graph operations."
  (:require [clojure.set :as set]
            [gretchen.util :refer :all]))

(defn disjoint-subgraphs
  "Given a graph composed of :vertices and a function :neighbors, such that
  (neighbors vertex) returns a collection of vertices adjacent to that vertex,
  partitions the vertices graph into a collection of connected subgraphs, each
  a collection of vertices."
  [{:keys [vertices neighbors]}]
  (->> (vals
         ; We build up a map of nodes to the set of all nodes reachable from
         ; that node.
         (reduce (fn red [m vertex]
                   (let [local (set (cons vertex (neighbors vertex)))
                         unified (->> local
                                      (map m)
                                      distinct-identical
                                      (reduce set/union local))]
                     (reduce (fn update-mapping [m vertex]
                               (assoc m vertex unified))
                             m
                             unified)))
                 {}
                 vertices))
       distinct-identical
       (mapv (partial hash-map :neighbors neighbors :vertices))))
