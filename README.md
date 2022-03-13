# asami-loom

[![Clojars Project](http://clojars.org/org.clojars.quoll/asami-loom/latest-version.svg)](http://clojars.org/org.clojars.quoll/asami-loom)

This library extends Asami in-memory graphs to Loom.

By requiring `asami-loom.index`, then the `asami.index.IndexGraph` graphs are extended to:
- `loom.graph.Graph`
- `loom.graph.EditableGraph`
- `loom.graph.DiGraph`

By requiring `asami-loom.multi-graph`, then the `asami.multi-graph.MultiGraph` graphs are extended to:
- `loom.graph.Graph`
- `loom.graph.EditableGraph`
- `loom.graph.DiGraph`
- `loom.graph.WeightedGraph`

By requiring `asami-loom.label`, then both the `asami.index.IndexGraph` and `asami.multi-graph.MultiGraph`
graphs get extended to:
- `loom.label.LabeledGraph`

## Usage

Requiring one of the above namespaces in any namespace that uses Asami in-memory graphs will automatically
apply the extensions. Loom can use the graphs with the standard APIs.

## Example

Configuring Asami Loom can be done by requiring the appropriate name spaces. Then just load data into Asami as usual.

Note: Some of this API will change soon to simplify. Specifically, the use of the Naga Storage API will be dropped.
This means that `naga.store` won't be needed, as the graph won't need to be extracted from the store object.

```clojure
(require '[asami.core :as d :refer [create-database connect transact db q]])

(create-database "asami:mem://music")
(def conn (connect "asami:mem://music"))

(def data
 [{:db/ident "paul"
   :artist/name "Paul McCartney"}
  {:db/ident "george"
   :artist/name "George Harrison"}
  {:db/ident "john"
   :artist/name "John Lennon"}
  {:release/artists {:db/ident "paul"}
   :release/name "My Sweet Lord"}
  {:release/artists {:db/ident "george"}
   :release/name "Electronic Sound"}
  {:release/artists {:db/ident "george"}
   :release/name "Give Me Love (Give Me Peace on Earth)"}
  {:release/artists {:db/ident "george"}
   :release/name "All Things Must Pass"}
  {:release/artists {:db/ident "john"}
   :release/name "Imagine"}])

(transact conn {:tx-data data})
(def graph (d/graph (db conn)))
```

The entity IDs created with `nn` above are represented as keywords with the namespace "mem".
Also, edges are typically keywords, but can also be strings.
With these assumptions in mind, we can use the following definitions to get labels for edges or nodes.

```clojure
(defn edge-label
  [g s d]
  (str (q '[:find ?edge . :in $ ?a ?b :where (or [?a ?edge ?b] [?b ?edge ?a])] g s d)))

(defn node-label
  [g n]
  (let [id (q [:find '?id '. :where [n :db/ident '?id]] g)]
    (cond id (str id)
          (and (keyword? n) (= (namespace n) "tg")) (str ":" (name n))
          :default (str n))))
```

With this configuration set up, the Loom `display` function can be used to create a graphical view.

```clojure
(require '[asami-loom.index])
(require '[asami-loom.label])
(require '[loom.io :as loom-io])

(loom-io/view graph :fmt :pdf :alg :sfdp :edge-label (partial edge-label graph) :node-label (partial node-label graph))
```

## View Parameters

Valid algorithms are:
- :dot
- :neato
- :fdp
- :sfdp
- :twopi
- :circo

Valid Formats are:
- :png
- :ps
- :pdf
- :svg

Loom launches the system default viewers for these file types.

## License

Copyright © 2019-2020 Cisco Systems

Copyright © 2022 Paula Gearon

This program and the accompanying materials are made available under the
terms of the Eclipse Public License 2.0 which is available at
http://www.eclipse.org/legal/epl-2.0.

This Source Code may also be made available under the following Secondary
Licenses when the conditions for such availability set forth in the Eclipse
Public License, v. 2.0 are satisfied: GNU General Public License as published by
the Free Software Foundation, either version 2 of the License, or (at your
option) any later version, with the GNU Classpath Exception which is available
at https://www.gnu.org/software/classpath/license.html.
