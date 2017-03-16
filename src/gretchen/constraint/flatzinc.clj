(ns gretchen.constraint.flatzinc
  "Evaluates constraints by compiling them to flatzinc and running that against
  gecode, via the fzn-gecode binary that ships with flatzinc. You'll need
  fzn-gecode on your path for this to work. On Debian, you can apt-get install
  flatzinc for this."
  (:require [gretchen.constraint :as c]
            [clojure.java.shell :refer [sh]]
            [clojure.java.io :as io]
            [clojure.pprint :refer [pprint]])
  (:import (java.io File
                    BufferedReader
                    StringReader)
           (gretchen.constraint Solver)
           (java.util.function BinaryOperator)
           (io.lacuna.bifurcan LinearMap)))

(defn write-bool!
  "Write a boolean var definition like '(bool :x) to a flatzinc outputstream.
  Optionally takes whether this is a real variable or a temporary one we
  introduced."
  [os [_ v] real?]
  (.write os "var bool: ")
  (.write os (name v))
  (if real?
    (.write os " :: output_var;\n")
    ; TODO: use is_defined_var and defines_var
    (.write os " :: var_is_introduced :: is_defined_var;\n")))

(defn write-int!
  "Write an integer var definition like '(in :x 0 5) to a flatzinc
  outputstream."
  [os [_ v lower upper]]
  (.write os "var ")
  (.write os (str lower))
  (.write os "..")
  (.write os (str upper))
  (.write os ": ")
  (.write os (name v))
  (.write os " :: output_var;\n"))

(defn write-constraint!
  "Write a constraint to the given outputstream, calling f with args."
  [os [f args annotations]]
  (assert f (str "No function? " f))
  (assert (coll? args) (str "No args? " f " " args " " annotations))

  (.write os "constraint ")
  (.write os (name f))
  (.write os "(")
  (loop [args args]
    (.write os (let [a (first args)]
                 (if (keyword? a)
                   (name (first args))
                   (pr-str a))))
    (when-let [more (next args)]
      (.write os ", ")
      (recur more)))
  (.write os ")")

  (loop [anns annotations]
    (when-let [ann (first anns)]
      (.write os " :: ")
      (.write os (name (first ann)))
      (when (< 1 (count ann))
        (.write os "(")
        ; Args
        (loop [a (next ann)]
          (when a
            (.write os (name (first a)))
            (when-let [more (next a)]
              (.write os ", ")
              (recur more))))
        (.write os ")"))))

  (.write os ";\n"))

(defn write-constraints!
  "Write a series of constraints to the given outputstream."
  [os constraints]
  (doseq [c constraints]
    (write-constraint! os c)))

(defn mapping
  "Take a tree, and a variable offset n. Compute [a new index n', a map of terms
  to temporary variables.] Mapping is a mutable LinearMap for performance."
  [tree n]
  (->> tree
       (tree-seq sequential? next)
       (filter sequential?)
       (reduce (fn [[i m] [type & children :as tree]]
                 [(inc i)
                  (.put m tree (keyword (str "_fz" (+ n i))))])
               [0 (LinearMap.)])))

(defn direct-constraint
  "Compute a sequence of top-level flatzinc constraints from a given constraint
  expression. Nil if we don't know how to handle this."
  [tree]
  (cond ; Plain old boolean
        (keyword? tree)
        [[:bool_eq [tree true]]]

        ; An expression we know how to handle directly?
        (seq tree)
        (let [[type a b] tree]
          (condp = type
            'distinct (for [a (next tree)
                            b (next tree)
                            :when (not= a b)]
                        [:int_ne [a b]])
            'not (if (keyword? a)
                   [[:bool_eq [a false]]])
            '<   [[:int_lt [a b]]]
            '<=  [[:int_le [a b]]]
            nil))))

(defn mapping-constraints
  "Generates constraints from a mapping."
  [mapping]
  (assert (= (distinct (map #(.value %) mapping))
             (vec (map #(.value %) mapping)))
          (str "Mapping without distinct variable names:\n"
               (with-out-str (pprint mapping))))
  (map (fn [entry]
         (let [tree (.key entry)
               v    (.value entry)
               [type & args] tree
               ; Replace child terms with their variables
               args (map (fn [a] (.get mapping a a)) args)
               [a b] args]
           (condp = type
             '<   [:int_lt_reif [a b v] [[:defines_var v]]]
             '<=  [:int_le_reif [a b v] [[:defines_var v]]]
             'and [:bool_and    [a b v] [[:defines_var v]]]
             'or  [:bool_or     [a b v] [[:defines_var v]]]
             'not [:bool_not    [a v]   [[:defines_var v]]]
             true (throw (IllegalArgumentException.
                           (str "What's a " (pr-str tree) "?"))))))
       mapping))

(defn flat
  "We've got a CNF expression like (and o1 o2 ...) where each o could be (or n1
  n2 ...) and each n could be (not l) and l could be a boolean var or a
  comparison like (< a b). Our job is to flatten this mess by introducing
  temporary vars, into a form that minizinc can understand."
  [ors]
  (let [; First off, we need binary forms
        ors     (map c/unfurl-binary-operators ors)
        ; Compute global mappings
        mapping (->> ors
                     (remove direct-constraint)
                     (reduce (fn merge-mappings
                               [[i m] tree]
                               (let [[n mapping] (mapping tree i)]
                                 [(+ i n) (.merge mapping m
                                                  (reify BinaryOperator
                                                    (apply [_ a b]
                                                      a)))]))
                             [0 (LinearMap.)])
                     second)]
    {:vars (map (fn [entry] ['bool (.value entry)]) mapping)
     :constraints (->> ors
                       (mapcat
                         (fn compute-constraints [o]
                           (or (direct-constraint o)
                               (direct-constraint (.get mapping o nil))
                               (throw (IllegalStateException.
                                        (str "Don't know how to generate constraint for "
                                             (pr-str o) "\ngiven value "
                                             (pr-str (.get mapping o nil))
                                             " from mapping\n"
                                             (with-out-str
                                               (pprint mapping))
                                             "\nover top-level constraints\n"
                                             (pr-str ors)))))))

                       (concat (mapping-constraints mapping)))}))

(defn write-flatzinc!
  "Spits a constraint tree as flatzinc into an OutputStream. Simplifies tree,
  converts it to CNF via tseitin, and reifies logic vars as appropriate."
  [os tree]
  (let [; First, convert the tree to CNF
;        {:keys [tree new-vars]} (c/tseitin+ (c/simplify tree))
;        new-vars (set (map (partial vector 'bool) new-vars))

        tree (c/simplify tree)
        new-vars #{}

        ; Force tree to contain an and
        tree (if (and (sequential? tree)
                      (= 'and (first tree)))
               tree
               ['and tree])

;        _ (prn :tree)
;        _ (pprint tree)
;        _ (prn)

        ; Split up terms of the 'and into integer definitions, boolean
        ; definitions, and other constraints
        {:keys [ints
                bools
                constraints]} (group-by (fn [t]
                                          (if (sequential? t)
                                            (condp = (first t)
                                              'in   :ints
                                              'bool :bools
                                              :constraints)
                                            :constraints))
                                        (next tree))

        ; Flatten the tree and compute constraints
        flattened (flat constraints)]

;    (prn :constraints)
;    (pprint (:constraints flattened))
;    (prn)

    ; Write ints
    (doseq [v ints]
      (write-int! os v))
    (.write os "\n")

    ; Bools
    (doseq [b bools]
      (when-not (new-vars b)
        (write-bool! os b true)))
    (.write os "\n")

    ; Temp vars from Tseitin expansion and our flatzinc flattening
    (doseq [b (concat new-vars (:vars flattened))]
      (write-bool! os b false))
    (.write os "\n")

    ; Constraints
    (write-constraints! os (:constraints flattened))
    (.write os "\n")

    ; Solve!
    (.write os "solve satisfy;\n")))

(defn flatzinc-str
  "Converts constraint tree to a flatzinc string."
  [tree]
  (let [s (java.io.StringWriter.)]
    (write-flatzinc! s tree)
    (str s)))

(defn parse-solution
  "Parse a single solution from a sequence of lines from fzn-gecode."
  [lines]
  (try
    (->> lines
         (map (fn [line]
                (let [[_ var val] (re-find #"\A(.+?) = (.+?);\z" line)
                      parsed-val (condp = val
                                   "true"  true
                                   "false" false
                                   (Long/parseLong val))]

                  [(keyword var) parsed-val])))
         (into {}))
    (catch Throwable t
      (println "Unable to parse solutions from:\n")
      (doall (map println lines))
      (throw t))))

(defn parse-solutions
  "Parses a sequence of lines from fzn-gecode into a sequence of solutions."
  [lines]
  (when (and (seq lines)
             (not= "=====UNSATISFIABLE=====" (first lines)))
    (let [[solution more] (split-with (partial not= "----------") lines)]
      (if (= (first solution) "==========")
        nil ; Done here
        (cons (parse-solution solution)
              (lazy-seq (parse-solutions (next more))))))))

(defn parse-solutions-str
  "Parses a string from fzn-gecode into a sequence of solutions, each a map of
  keywords to values."
  [s]
  (-> s
      (StringReader.)
      (BufferedReader.)
      line-seq
      (parse-solutions)))

(defn solve
  "Solves a constraint with flatzinc by shelling out. Emits up to n solutions."
  [tree n]
  (let [file (java.io.File/createTempFile "gretchen" ".flatzinc")]
    (try
;      (println "flatzinc:")
;      (write-flatzinc! *out* tree)
      (with-open [w (io/writer file)]
        (write-flatzinc! w tree))

      (let [res (sh "fzn-gecode" "-n" (str n) "-p" "0" (.getCanonicalPath file))]
        (assert (zero? (:exit res))
                (str "fzn-gecode returned non-zero exit status " (:exit res)
                     ".\nStderr:\n" (:err res)
                     "\nStdout:\n" (:out res)
                     "\nConstraint tree was\n" (with-out-str (pprint tree))
                     "\nGenerated flatzinc was:\n" (flatzinc-str tree)))
             (parse-solutions-str (:out res)))
      (finally
        (.delete file)))))

(defn solution
  "Solve for one solution."
  [tree]
  (first (solve tree 1)))

(defn solutions
  "Solve for all solutions."
  [tree]
  (solve tree 0))

(defn flatzinc
  "Flatzinc gecode based solver."
  []
  (reify Solver
    (solution [_ c]
      (solution c))))
