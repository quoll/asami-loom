(ns ^{:doc "Extension of Asami block-based durable index to Loom protocols"
      :author "Paula Gearon"}
    asami-loom.durable
  (:require [asami.graph :as gr :refer [graph-add graph-delete resolve-triple]]
            [asami.core :as a]
            [asami.storage :as as]
            [asami.durable.encoder :as e]
            [clojure.set :as set]
            [clojure.string :as s]
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
  (add-nodes*
    [gr nodes]
    ;; add each node in turn
    (reduce
     (fn [{:keys [spot ospt pool] :as g} node]
       ;; find the local value for the node
       (let [n (c/find-id pool node)] 
         ;; insert a node if it was never locallized
         (if (or (nil? n)
                 ;; or if it does not show up in a triple
                 (and (empty? (c/find-tuples spot [n])) 
                      (empty? (c/find-tuples ospt [n]))))
           (graph-add g node :tg/nil :tg/nil)
           g)))
     gr nodes))

  (add-edges*
    [gr edges]
    (reduce
     (fn [g [s o]]
       (-> g
           (clean s)
           (clean o)
           (graph-add s :to o)))
     gr edges))

  (remove-nodes*
    [{:keys [pool] :as gr} nodes]
    (->> nodes
         ;; convert all nodes to localized values
         (map #(find-id pool %))
         ;; reduce the graph over the local nodes
         (reduce
          (fn [{:keys [spot ospt] :as g} node]
            ;; find all statements that use the node in the subject or object position
            (let [s-statements (c/find-tuples spot [node])
                  o-statements (c/find-tuples ospt [node])
                  ;; accumulate nodes connected to the node we're looking for
                  other-ends (into (set (map #(nth % 2) s-statements))
                                   (map #(nth % 1) o-statements))
                  ;; get all the full statements that use this node
                  ;; cutting the tuples to just the subject/predicate/object triple
                  all-triples (map #(subvec % 0 3) (concat s-statements o-statements))
                  scrubbed (reduce #(apply graph-delete %1 %2)
                                   (graph-delete g node nil-node nil-node) ;; remove if exists
                                   all-triples)
                  ;; find nodes whose edges were removed, and the node is no longer referenced
                  reinserts (remove #(or (seq (c/find-tuples spot [%]))  ;; look for statements with this subject
                                         (seq (c/find-tuples ospt [%]))) ;; or statements with this object
                                    other-ends)]
              ;; add back the nodes that should still be there but are not in edges anymore
              (reduce #(graph-add %1 %2 nil-node nil-node) scrubbed reinserts)))
          gr)))

  (remove-edges*
    [gr edges]
    (reduce
     (fn [{:keys [spot ospt] :as g} [s o]]
       ;; convert nodes to localized form
       ;; stylistically this would be better in a prior map step
       ;; but that requires a map pipeline, a destructure, and a repacking
       (let [s-node (find-id pool s)
             o-node (find-id pool o)
             ;; there should only be the :to predicate, but search for any others
             all-triples (for [[_ _ p] (c/find-tuples ospt [o-node s-node])] [s p o])
             {:keys [spot ospt] :as scrubbed} (reduce #(apply graph-delete %1 %2) g all-triples)
             ;; find which of the nodes whose edges were removed and are no longer referenced
             reinserts (remove #(or (seq (c/find-tuples spot [%]))
                                    (seq (c/find-tuples ospt [%])))
                               [s-node o-node])]
         ;; add back the nodes that are still there but not in edges anymore
         (reduce #(graph-add %1 %2 nil-node nil-node) scrubbed reinserts)))
     gr edges))

  (remove-all
    [gr]
    ;; removes statements naively
    ;; Each statement goes via the pool, which may be more expensive than needed
    ;; The alternative is to create a new graph manually
    (let [statements (resolve-triple gr '?s '?p '?o)]
      (reduce (fn [g [s p o]] (graph-delete g s p o)) gr statements)))

  loom/Digraph
  (predecessors*
    [{:keys [ospt pool]} node]
    (let [n (find-id pool node)] ;; convert to a local node
      (->> (c/find-tuples ospt [n])  ;; find all statements with this as the object
           (map #(nth % 1))  ;; extract the "subject" position of the result
           set)))  ;; accumulate and remove duplicates

  (in-degree
    [{:keys [ospt pool]} node]
    (let [n (find-id pool node)]  ;; convert to a local node
      (count (c/find-tuples ospt [n]))))  ;; find and count all statements with this as the object

  (in-edges
    [{:keys [ospt pool]} node]
    (let [n (find-id pool node)]  ;; convert to a local node
      (->> (c/find-tuples ospt [n])  ;; find all statements with the node as the object
           (map (fn [[o s]]  ;; extract the object and subject from the tuples
                  [(find-object pool s) (find-object pool o)])))))  ;; globalize the nodes to form an edge

  (transpose
    [{:keys [ospt] :as gr}]
    (let [statements (resolve-triple gr '?s '?p '?o)] ;; get all statements
      (reduce (fn [g [s p o]]
                ;; Check if this is a statement about a node without an edge
                (if-not (= o :tg/nil)
                  ;; no, it's a normal edge
                  (-> g
                      (graph-delete s p o)  ;; remove the statement
                      (graph-add o p s))    ;; insert the reversed statement
                  gd))
              gr statements))))

(def ^:const uri-leader "asami:local:")

(defn graph
  "Creates a durable graph with a set of edges. All edges are unlabelled.
  An initial graph may be provided as a string, in which case it will be created. "
  [graph & inits]
  ;; a string graph implies connecting to that graph
  (let [[g edges] (if (string? graph) (let [nm (if (s/starts-with? graph uri-leader)
                                                 graph
                                                 (str uri-leader graph))
                                            cn (a/connect graph)]
                                        [(as/graph (as/db cn)) inits])
                      ;; Otherwise, assume standard inits, so create a graph
                      (let [cn (a/connect (str uri-leader (name gensym)))]
                        ;; skip adding the graph as an init if it's nil
                        [(as/graph (as/db cn)) (if graph (cons graph inits) inits)]))]
    (apply build-graph g inits)))

