(ns gretchen.graph
  "Assists with graph operations. Our representation of a graph is a map with
  two keys: {:vertices, a collection of objects, and :neighbors, a function of
  vertices to vertices.}

  Graphs may not contain nil vertices."
  (:require [clojure.set :as set]
            [gretchen.util :refer :all]))

(defn reachable
  "Takes a graph and a collection of vertices `start`, and returns a set of all
  vertices reachable from any vertex in `start`."
  [{:keys [vertices neighbors] :as graph} start]
  (loop [visited (set start)
         cambium start]
    (let [cambium' (->> (map neighbors cambium)
                        (remove nil?)
                        (remove visited)
                        distinct)]
      (if (empty? cambium')
        visited
        (recur (into visited cambium')
               cambium')))))

(defn invert
  "Reverses every edge in a graph, such that in the new graph, a->b iff b->a in
  the original graph."
  [{:keys [vertices neighbors]}]
  {:vertices vertices
   :neighbors (persistent!
                (reduce (fn [in src]
                          (reduce (fn [in dst]
                                    (let [x (get in dst [])]
                                      (assoc! in dst (conj x src))))
                                  in
                                  (neighbors src)))
                        (transient {})
                        vertices))})

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
