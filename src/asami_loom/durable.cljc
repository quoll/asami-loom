(ns ^{:doc "Extension of Asami block-based durable index to Loom protocols"
      :author "Paula Gearon"}
    asami-loom.durable
  (:require [asami.graph :as gr :refer [graph-add graph-delete resolve-triple]]
            [asami.durable.encoder :as e]
            [clojure.set :as set]
            [loom.graph :as loom :refer [nodes edges has-node? successors* build-graph
                                         out-degree out-edges
                                         add-edges* add-nodes*]]
            #?(:clj  [asami.durable.common :as c]
               :cljs [asami.durable.common :as c :refer [BlockGraph]]))
  #?(:clj (:import [asami.index BlockGraph])))

;; It is unusual to call this directly, but the value is constant,
;; and the usual API needs a pool object to obtain
(def ^:const nil-node (e/encapsulate-id :tg/nil))

(defn node-only?
  "Tests if a graph contains a node without associated edges"
  [g n]
  (seq (resolve-triple g n :tg/nil :tg/nil)))

(defn clean
  "Removes a node-only entry from a graph"
  [g n]
  (if (node-only? g n)
    (graph-delete g n :tg/nil :tg/nil)
    g))

(defn all-triple-edges
  [g n]
  (concat
    (map #(cons n %) (resolve-triple g n '?a '?b))
    (map #(conj % n) (resolve-triple g '?a '?b n))))

(extend-type BlockGraph
  loom/Graph
  (nodes [{:keys [spot ospt pool] :as graph}]
    (let [lineproc (map #(c/find-object pool (first %)))
          subjects (c/find-tuples spot [])
          objects (c/find-tuples ospt [])]
      (disj (into #{} lineproc (concat subjects objects)) :tg/nil)))

  (edges [{:keys [ospt pool] :as graph}]
    (let [tuples (c/find-tuples ospt [])
          tx (comp (map (fn [[o s]] [(c/find-object pool s) (c/find-object pool o)]))
                   (remove #(= :tg/nil (first %)))
                   (dedupe))]
      (sequence tx tuples)))

  (has-node? [{:keys [spot ospt pool] :as graph} node]
    (when (and node (not= :tg/nil node))
      (let [n (c/find-id pool node)]
        (boolean (or (seq (c/find-tuples spot [n]))
                     (seq (c/find-tuples ospt [n])))))))

  (has-edge? [{:keys [ospt pool] :as graph} node1 node2]
    (let [n1 (c/find-id pool node1)
          n2 (c/find-id pool node2)]
      (boolean (and n1 n2 (seq (c/find-tuples ospt [n2 n1]))))))

  (successors* [{:keys [spot pool] :as graph} node]
    (let [n (c/find-id pool node)
          os (comp (map #(nth % 2)) (map #(c/find-object pool %)))
          s (into #{} os (c/find-tuples spot [n]))]
      (disj s :tg/nil)))

  (out-degree [{:keys [spot pool] :as graph} node]
    ;; drops duplicates for different predicates!
    (let [nil-val (c/find-id pool :tg/nil)
          n (c/find-id pool node)
          os (comp (map #(nth % 2)) (remove #(= nil-val %)))
          o (sequence os (c/find-tuples spot [n]))]
      (count o)))

  (out-edges [graph node]
    "Returns all the outgoing edges of node"
    (for [o (successors* graph node)] [node o]))

  loom/EditableGraph
  (add-nodes* [gr nodes]
    (reduce
     (fn [{:keys [spot ospt pool] :as g} node]
       (let [n (c/find-id pool node)] 
         (if (or (nil? n)
                 (and (empty? (c/find-tuples spot [n])) 
                      (empty? (c/find-tuples ospt [n]))))
           (graph-add g node :tg/nil :tg/nil)
           g)))
     gr nodes))

  (add-edges* [gr edges]
    (reduce
     (fn [g [s o]]
       (-> g
           (clean s)
           (clean o)
           (graph-add s :to o)))
     gr edges))

  (remove-nodes* [{:keys [pool] :as gr} nodes]
    (->> nodes
         (map #(find-id pool %))
         (reduce
          (fn [{:keys [spot ospt] :as g} node]
            (let [s-statements (c/find-tuples spot [node]) ;; localnode form
                  o-statements (c/find-tuples ospt [node])
                  other-ends (into (set (map #(nth % 2) s-statements))
                                   (map #(nth % 1) o-statements))
                  all-triples (all-triple-edges g node)
                  scrubbed (reduce #(apply graph-delete %1 %2)
                                   (graph-delete g node nil-node nil-node) ;; remove if exists
                                   all-triples)
                  ;; find nodes whose edges were removed, and the node is no longer referenced
                  reinserts (remove #(or (seq (c/find-tuples spot [%])) (seq (c/find-tuples ospt [%]))) other-ends)]
              ;; add back the nodes that are still there but not in edges anymore
              (reduce #(graph-add %1 %2 nil-node nil-node) scrubbed reinserts)))
          gr)))

  (remove-edges* [gr edges]
    (reduce
     (fn [{:keys [spot ospt] :as g} [s o]]
       (let [s-statements (c/find-tuples spot [node]) ;; localnode form
             o-statements (c/find-tuples ospt [node])
             other-ends (into (set (map #(nth % 2) s-statements))
                              (map #(nth % 1) o-statements))
             ;; there should only be the :to predicate, but search for any others
             all-triples (for [p (c/find-tuples ospt [o-node s-node])] [s p o])
             {:keys [spot ospt] :as scrubbed} (reduce #(apply graph-delete %1 %2) g all-triples)
             ;; find nodes whose edges were removed, and the node is no longer referenced
             reinserts (remove #(or (seq (c/find-tuples spot [%])) (seq (c/find-tuples ospt [%]))) other-ends)]
         ;; add back the nodes that are still there but not in edges anymore
         (reduce #(graph-add %1 %2 nil-node nil-node) scrubbed reinserts)))
     gr edges))

  ;; below here has been copy/pasted from index.cljc. Not yet converted and will fail
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

