/-
Copyright (c) 2018 Simon Hudon All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

Tactics based on the strongly connected components (SCC) of a graph where
the vertices are propositions and the edges are implications found
in the context.

They are used for finding the sets of equivalent propositions in a set
of implications.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.tauto
import Mathlib.data.sum
import Mathlib.PostPort

namespace Mathlib

/-!
# Strongly Connected Components

This file defines tactics to construct proofs of equivalences between a set of mutually equivalent
propositions. The tactics use implications transitively to find sets of equivalent propositions.

## Implementation notes

The tactics use a strongly connected components algorithm on a graph where propositions are
vertices and edges are proofs that the source implies the target. The strongly connected components
are therefore sets of propositions that are pairwise equivalent to each other.

The resulting strongly connected components are encoded in a disjoint set data structure to
facilitate the construction of equivalence proofs between two arbitrary members of an equivalence
class.

## Possible generalizations

Instead of reasoning about implications and equivalence, we could generalize the machinery to
reason about arbitrary partial orders.

## References

 * Tarjan, R. E. (1972), "Depth-first search and linear graph algorithms",
   SIAM Journal on Computing, 1 (2): 146–160, doi:10.1137/0201010
 * Dijkstra, Edsger (1976), A Discipline of Programming, NJ: Prentice Hall, Ch. 25.
 * <https://en.wikipedia.org/wiki/Disjoint-set_data_structure>

## Tags

graphs, tactic, strongly connected components, disjoint sets
-/

namespace tactic


/--
`closure` implements a disjoint set data structure using path compression
optimization. For the sake of the scc algorithm, it also stores the preorder
numbering of the equivalence graph of the local assumptions.

The `expr_map` encodes a directed forest by storing for every non-root
node, a reference to its parent and a proof of equivalence between
that node's expression and its parent's expression. Given that data
structure, checking that two nodes belong to the same tree is easy and
fast by repeatedly following the parent references until a root is reached.
If both nodes have the same root, they belong to the same tree, i.e. their
expressions are equivalent. The proof of equivalence can be formed by
composing the proofs along the edges of the paths to the root.

More concretely, if we ignore preorder numbering, the set
`{ {e₀,e₁,e₂,e₃}, {e₄,e₅} }` is represented as:

```
e₀ → ⊥      -- no parent, i.e. e₀ is a root
e₁ → e₀, p₁ -- with p₁ : e₁ ↔ e₀
e₂ → e₁, p₂ -- with p₂ : e₂ ↔ e₁
e₃ → e₀, p₃ -- with p₃ : e₃ ↔ e₀
e₄ → ⊥      -- no parent, i.e. e₄ is a root
e₅ → e₄, p₅ -- with p₅ : e₅ ↔ e₄
```

We can check that `e₂` and `e₃` are equivalent by seeking the root of
the tree of each. The parent of `e₂` is `e₁`, the parent of `e₁` is
`e₀` and `e₀` does not have a parent, and thus, this is the root of its tree.
The parent of `e₃` is `e₀` and it's also the root, the same as for `e₂` and
they are therefore equivalent. We can build a proof of that equivalence by using
transitivity on `p₂`, `p₁` and `p₃.symm` in that order.

Similarly, we can discover that `e₂` and `e₅` aren't equivalent.

A description of the path compression optimization can be found at:
<https://en.wikipedia.org/wiki/Disjoint-set_data_structure#Path_compression>

-/
namespace closure


/-- `with_new_closure f` creates an empty `closure` `c`, executes `f` on `c`, and then deletes `c`,
returning the output of `f`. -/
/-- `to_tactic_format cl` pretty-prints the `closure` `cl` as a list. Assuming `cl` was built by
`dfs_at`, each element corresponds to a node `pᵢ : expr` and is one of the folllowing:
- if `pᵢ` is a root: `"pᵢ ⇐ i"`, where `i` is the preorder number of `pᵢ`,
- otherwise: `"(pᵢ, pⱼ) : P"`, where `P` is `pᵢ ↔ pⱼ`.
Useful for debugging. -/
/-- `(n,r,p) ← root cl e` returns `r` the root of the tree that `e` is a part of (which might be
itself) along with `p` a proof of `e ↔ r` and `n`, the preorder numbering of the root. -/
/-- (Implementation of `merge`.) -/
/-- `merge cl p`, with `p` a proof of `e₀ ↔ e₁` for some `e₀` and `e₁`,
merges the trees of `e₀` and `e₁` and keeps the root with the smallest preorder
number as the root. This ensures that, in the depth-first traversal of the graph,
when encountering an edge going into a vertex whose equivalence class includes
a vertex that originated the current search, that vertex will be the root of
the corresponding tree. -/
/-- Sequentially assign numbers to the nodes of the graph as they are being visited. -/
/-- `prove_eqv cl e₀ e₁` constructs a proof of equivalence of `e₀` and `e₁` if
they are equivalent. -/
/-- `prove_impl cl e₀ e₁` constructs a proof of `e₀ -> e₁` if they are equivalent. -/
/-- `is_eqv cl e₀ e₁` checks whether `e₀` and `e₁` are equivalent without building a proof. -/
end closure


/-- mutable graphs between local propositions that imply each other with the proof of implication -/
/-- `with_impl_graph f` creates an empty `impl_graph` `g`, executes `f` on `g`, and then deletes
`g`, returning the output of `f`. -/
namespace impl_graph


/-- `add_edge g p`, with `p` a proof of `v₀ → v₁` or `v₀ ↔ v₁`, adds an edge to the implication
graph `g`. -/
/-- `merge_path path e`, where `path` and `e` forms a cycle with proofs of implication between
consecutive vertices. The proofs are compiled into proofs of equivalences and added to the closure
structure. `e` and the first vertex of `path` do not have to be the same but they have to be
in the same equivalence class. -/
/-- (implementation of `collapse`) -/
/-- `collapse path v`, where `v` is a vertex that originated the current search
(or a vertex in the same equivalence class as the one that originated the current search).
It or its equivalent should be found in `path`. Since the vertices following `v` in the path
form a cycle with `v`, they can all be added to an equivalence class. -/
/--
Strongly connected component algorithm inspired by Tarjan's and
Dijkstra's scc algorithm. Whereas they return strongly connected
components by enumerating them, this algorithm returns a disjoint set
data structure using path compression. This is a compact
representation that allows us, after the fact, to construct a proof of
equivalence between any two members of an equivalence class.

 * Tarjan, R. E. (1972), "Depth-first search and linear graph algorithms",
   SIAM Journal on Computing, 1 (2): 146–160, doi:10.1137/0201010
 * Dijkstra, Edsger (1976), A Discipline of Programming, NJ: Prentice Hall, Ch. 25.
-/
/-- Use the local assumptions to create a set of equivalence classes. -/
end impl_graph


/--
`scc` uses the available equivalences and implications to prove
a goal of the form `p ↔ q`.

```lean
example (p q r : Prop) (hpq : p → q) (hqr : q ↔ r) (hrp : r → p) : p ↔ r :=
by scc
```
-/
/-- Collect all the available equivalences and implications and
add assumptions for every equivalence that can be proven using the
strongly connected components technique. Mostly useful for testing. -/
/--
`scc` uses the available equivalences and implications to prove
end Mathlib