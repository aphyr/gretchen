(ns gretchen.bottleneck
  "Imagine a history H of transactions with a partial precedence order < over
  those transactions. In generality, we might have to consider every possible
  permutation of those transactions, which is expensive.

  However, if we are lucky, there might exist a *bottleneck* transaction
  c--perhaps inserted by a magnanimous tester who produced the history in the
  first place--which cleanly cuts the other transactions in the history into
  two sets A and B, such that:

  0. (c ∉ A) ∧ (c ∉ B)  Neither A nor B contains c
  1. A ∩ B = {}         A and B are disjoint
  2. A ∪ B ∪ {c} = H    A, B, and c partition (loosely, A and B might be empty)
                        the history
  3. ∀ a ∈ A, a < c     A precedes c
  4. ∀ b ∈ B, c < b     c precedes B

  Visually:

         A        c       B
   ______|______  |  _____|_____
  |             | | |           |
      /-a1--a3|       /-b0--b2
    a0         ---c---
      |-a2--a4/       |-b1

  To abuse notation, since A < c < B, then A < B. This implies that no
  transactions in B can affect the serializability of A. This gives us two
  advantages:

  1. If A is nonserializable, H must be nonserializable. This lets us identify
     illegal histories more quickly, and *localize* the fault to a particular
     part of the history.

  2. If all keys externally read in B were externally read or written by c,
     then the serializability of B does not depend on the serialization we
     choose for A.  Why? Because c sets out a complete initial state for the
     transactions in B, and no transaction from A could interfere. We call c
     \"total\" in this case, and \"partial\" otherwise.

  For example, consider:

  1. Say our transactions implement a series of counters {x 0, y
     0}, and most transactions get and increment a single counter by one. But
     every so often, a transaction occurs that sets all counters to, say, {x
     1000, y 1000}, then {x 2000, y 2000}--values which would not be reachable
     by regular increments alone. We can infer that these resetting
     transactions are total bottlenecks.

  2. Or alternatively, imagine a special epoch key which is periodically
     incremented, and read by every transaction, segmenting transactions into
     groups. This is effectively a view change algorithm: writes to the epoch
     constitute bottlenecks.

  3. Or consider a history in which all transactions read and write the same
     set of variables, and no state is ever repeated--perhaps a series of
     additions to a set, or increments to a single counter. The dependency graph
     is *linear* in this case, and every transaction is a total bottleneck.

  If c is total, we can verify the serializability of H by checking that A ∪
  {c} is serializable, and that {c} ∪ B is serializable. Any serialization S_A
  for A, and S_B for B, can be stitched together to form a serialization for
  the complete history S_H = S_A + (S_B without the initial c).

  If c is *not* total, then the serializability of B depends on the order we
  choose for A. However, we can exploit degeneracy at the bottleneck: it is
  likely the case that there are only a few possible outcomes for A, though
  there could be many more possible serializations. Wetherefore compute
  *all* serializations of A ∪ {c}, but only retain the set of distinct
  outcome states from those histories: O.

  We can then check B by taking each state o ∈ O, and verifying that B is
  serializable beginning with state O. If we wish to find *any* serialization,
  we can pick any serialization for B, preceded by any serialization of A ∪ {c}
  which produced the bottleneck state O. If we wish to find all possible
  outcome states--for instance, as a part of a recursive solution to a history
  with many bottlenecks, we do not need to retain every serialization of A ∪
  {c}. A single serialization from A ∪ {c} for each bottleneck state o will
  suffice."
  (:require [clojure.set :as set]
            [gretchen [history :as h]
                      [recurset :as recurset]
                      [util :refer :all]]))

(defn bottlenecks-
  "This function takes an augmented history, and returns a collection of
  bottleneck transactions.

  We do this by identifying transactions t which have a casual relationship with
  every other transaction o in the history: either t < o, or o < t."
  [history]
  (let [txns (set (:txns history))
        ; A map of tranactions to recursets of transactions that they depend
        ; on.
        ancestors (h/ancestors history)
        ; A map of transactions to the set of transactions which must depend on
        ; them.
        candidates (persistent!
                     (reduce (fn [candidates [t ancestors-of-t]]
                               (assoc! candidates t
                                       (set/difference
                                         txns
                                         #{t}
                                         (recurset/to-set ancestors-of-t))))
                             (transient {})
                             ancestors))]
    (keys
      (reduce (fn [candidates t]
                ; For every transaction t...
                (let [ancestors-of-t (recurset/to-set (get ancestors t))]
                  (reduce (fn [candidates [candidate required]]
                            ; For every candidate
                            (cond ; candidate already has a relationship with t
                                  (not (required t)) candidates

                                  ; candidate is an ancestor of t
                                  (ancestors-of-t candidate) candidates

                                  ; We can't prove any relationship
                                  true
                                  (dissoc candidates candidate)))
                          candidates
                          candidates)))
              candidates
              txns))))
