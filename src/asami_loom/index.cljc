(ns ^{:doc "Extension of Asami in-memory index to Loom protocols"
      :author "Paula Gearon"}
    asami-loom.index
  (:require [asami.graph :as gr :refer [graph-add graph-delete resolve-triple]]
            [clojure.set :as set]
            [loom.graph :as loom :refer [nodes edges has-node? successors* build-graph
                                         out-degree out-edges
                                         add-edges* add-nodes*
                                         add-nodes add-edges]]
            #?(:clj  [asami.index :as index]
               :cljs [asami.index :as index :refer [GraphIndexed]])
            #?(:clj  [schema.core :as s]
               :cljs [schema.core :as s :include-macros true]))
  #?(:clj (:import [asami.index GraphIndexed])))

(defn node-only?
  "Tests if a graph contains a node without associated edges"
  [{spo :spo} n]
  (contains? (get-in spo [n nil]) nil))

(defn clean
  "Removes a node-only entry from a graph"
  [g n]
  (if (node-only? g n)
    (graph-delete g n nil nil)
    g))

(defn all-triple-edges
  [g n]
  (concat
    (map #(cons n %) (resolve-triple g n '?a '?b))
    (map #(conj % n) (resolve-triple g '?a '?b n))))

(extend-type GraphIndexed
  loom/Graph
  (nodes [{:keys [spo osp] :as graph}]
    (disj (into (set (keys spo)) (keys osp)) nil))

  (edges [{:keys [osp] :as graph}]
    (for [[o sp] osp :when o s (keys sp)] [s o]))

  (has-node? [{:keys [spo osp] :as graph} node]
    (when node (boolean (or (spo node) (osp node)))))

  (has-edge? [{:keys [osp] :as graph} n1 n2]
    (boolean (get-in osp [n2 n1])))

  (successors* [{:keys [spo] :as graph} node]
    (disj (apply set/union (vals (spo node))) nil))

  (out-degree [{:keys [spo] :as graph} node]
    ;; drops duplicates for different predicates!
    (count (disj (apply set/union (vals (spo node))) nil)))

  (out-edges [{:keys [spo] :as graph} node]
    "Returns all the outgoing edges of node"
    (for [o (apply set/union (vals (spo node))) :when o] [node o]))

  loom/EditableGraph
  (add-nodes* [gr nodes]
    (reduce
     (fn [{:keys [spo osp] :as g} n]
       (if (or (spo n) (osp n)) g (graph-add g n nil nil)))
     gr nodes))

  (add-edges* [gr edges]
    (reduce
     (fn [g [s o]]
       (-> g
           (clean s)
           (clean o)
           (graph-add s :to o)))
     gr edges))

  (remove-nodes* [gr nodes]
    (reduce
     (fn [{:keys [spo osp] :as g} node]
       (let [other-ends (into (set (map keys (vals (spo node))))
                              (keys (osp node)))
             all-triples (all-triple-edges g node)
             {:keys [spo osp] :as scrubbed} (reduce #(apply graph-delete %1 %2)
                                                      (graph-delete g node nil nil)  ;; remove if exists
                                                      all-triples)
             ;; find nodes whose edges were removed, and the node is no longer referenced
             reinserts (remove #(or (spo %) (osp %)) other-ends)]
         ;; add back the nodes that are still there but not in edges anymore
         (reduce #(graph-add %1 %2 nil nil) scrubbed reinserts)))
     gr nodes))

  (remove-edges* [gr edges]
    (reduce
     (fn [{:keys [spo osp] :as g} [s o]]
       (let [other-ends (into (set (map keys (vals (spo s))))
                              (keys (osp o)))
             ;; there should only be the :to predicate, but search for any others
             all-triples (for [p (get (osp o) s)] [s p o])
             {:keys [spo osp] :as scrubbed} (reduce #(apply graph-delete %1 %2) g all-triples)
             ;; find nodes whose edges were removed, and the node is no longer referenced
             reinserts (remove #(or (spo %) (osp %)) other-ends)]
         ;; add back the nodes that are still there but not in edges anymore
         (reduce #(graph-add %1 %2 nil nil) scrubbed reinserts)))
     gr edges))

  (remove-all [gr] index/empty-graph)

  loom/Digraph
  (predecessors* [{:keys [osp]} node]
    (keys (osp node)))

  (in-degree [{:keys [osp]} node]
    (count (osp node)))

  (in-edges [{:keys [osp]} node]
    (map (fn [s] [s node]) (keys (osp node))))

  (transpose [{:keys [osp] :as gr}]
    (let [nodes (keys (get osp nil))
          triples (resolve-triple gr '?a '?b '?c)]
      (-> (reduce (fn [g [a b c]] (if c (graph-add g c b a) g)) index/empty-graph triples)
          (add-nodes* nodes)))))

(defn graph
  "Creates an index graph with a set of edges. All edges are unlabelled."
  [& inits]
  (apply build-graph index/empty-graph inits))

