(ns gretchen.util
  "Kitchen sink")

(defn map-vals
  "Maps values in a map."
  [f m]
  (->> m
       (map (fn [[k v]] [k (f v)]))
       (into {})))

(defn distinct-identical
  "Like distinct, but only skips elements which are identical to those already
  seen."
  ([xs] (distinct-identical xs {}))
  ([xs seen]
   (when (seq xs)
     (lazy-seq
       (let [x       (first xs)
             h       (hash x)
             seen-xs (get seen h)]
         (if (not-any? (partial identical? x) (get seen h))
           (cons x (distinct-identical (next xs)
                                       (assoc seen h (conj seen-xs x))))
           (distinct-identical (next xs) seen)))))))


(defn fixed-point
  "Applies f repeatedly to x until it converges."
  [f x]
  (let [x' (f x)]
    (if (= x x')
      x
      (recur f x'))))
