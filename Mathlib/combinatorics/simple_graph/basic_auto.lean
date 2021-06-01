/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Aaron Anderson, Jalex Stark, Kyle Miller, Alena Gusakov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.fintype.basic
import Mathlib.data.sym2
import Mathlib.data.set.finite
import Mathlib.PostPort

universes u l 

namespace Mathlib

/-!
# Simple graphs

This module defines simple graphs on a vertex type `V` as an
irreflexive symmetric relation.

There is a basic API for locally finite graphs and for graphs with
finitely many vertices.

## Main definitions

* `simple_graph` is a structure for symmetric, irreflexive relations

* `neighbor_set` is the `set` of vertices adjacent to a given vertex

* `neighbor_finset` is the `finset` of vertices adjacent to a given vertex,
   if `neighbor_set` is finite

* `incidence_set` is the `set` of edges containing a given vertex

* `incidence_finset` is the `finset` of edges containing a given vertex,
   if `incidence_set` is finite

## Implementation notes

* A locally finite graph is one with instances `∀ v, fintype (G.neighbor_set v)`.

* Given instances `decidable_rel G.adj` and `fintype V`, then the graph
  is locally finite, too.

## Naming Conventions

* If the vertex type of a graph is finite, we refer to its cardinality as `card_verts`.

TODO: This is the simplest notion of an unoriented graph.  This should
eventually fit into a more complete combinatorics hierarchy which
includes multigraphs and directed graphs.  We begin with simple graphs
in order to start learning what the combinatorics hierarchy should
look like.

TODO: Part of this would include defining, for example, subgraphs of a
simple graph.

-/

/--
A simple graph is an irreflexive symmetric relation `adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.
There is exactly one edge for every pair of adjacent edges;
see `simple_graph.edge_set` for the corresponding edge set.
-/
structure simple_graph (V : Type u) where
  adj : V → V → Prop
  sym :
    autoParam (symmetric adj)
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
        (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  loopless :
    autoParam (irreflexive adj)
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
        (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

/--
Construct the simple graph induced by the given relation.  It
symmetrizes the relation and makes it irreflexive.
-/
def simple_graph.from_rel {V : Type u} (r : V → V → Prop) : simple_graph V :=
  simple_graph.mk fun (a b : V) => a ≠ b ∧ (r a b ∨ r b a)

protected instance simple_graph.fintype {V : Type u} [fintype V] : fintype (simple_graph V) :=
  fintype.of_injective simple_graph.adj simple_graph.ext

@[simp] theorem simple_graph.from_rel_adj {V : Type u} (r : V → V → Prop) (v : V) (w : V) :
    simple_graph.adj (simple_graph.from_rel r) v w ↔ v ≠ w ∧ (r v w ∨ r w v) :=
  iff.rfl

/--
The complete graph on a type `V` is the simple graph with all pairs of distinct vertices adjacent.
-/
def complete_graph (V : Type u) : simple_graph V := simple_graph.mk ne

protected instance simple_graph.inhabited (V : Type u) : Inhabited (simple_graph V) :=
  { default := complete_graph V }

protected instance complete_graph_adj_decidable (V : Type u) [DecidableEq V] :
    DecidableRel (simple_graph.adj (complete_graph V)) :=
  fun (v w : V) => not.decidable

namespace simple_graph


/-- `G.neighbor_set v` is the set of vertices adjacent to `v` in `G`. -/
def neighbor_set {V : Type u} (G : simple_graph V) (v : V) : set V := set_of (adj G v)

protected instance neighbor_set.mem_decidable {V : Type u} (G : simple_graph V) (v : V)
    [DecidableRel (adj G)] : decidable_pred fun (_x : V) => _x ∈ neighbor_set G v :=
  eq.mpr sorry fun (a : V) => set.decidable_mem (set_of (adj G v)) a

theorem ne_of_adj {V : Type u} (G : simple_graph V) {a : V} {b : V} (hab : adj G a b) : a ≠ b :=
  id fun (ᾰ : a = b) => Eq._oldrec (fun (hab : adj G a a) => loopless G a hab) ᾰ hab

/--
The edges of G consist of the unordered pairs of vertices related by
`G.adj`.
-/
def edge_set {V : Type u} (G : simple_graph V) : set (sym2 V) := sym2.from_rel (sym G)

/--
The `incidence_set` is the set of edges incident to a given vertex.
-/
def incidence_set {V : Type u} (G : simple_graph V) (v : V) : set (sym2 V) :=
  has_sep.sep (fun (e : sym2 V) => v ∈ e) (edge_set G)

theorem incidence_set_subset {V : Type u} (G : simple_graph V) (v : V) :
    incidence_set G v ⊆ edge_set G :=
  fun (_x : sym2 V) (h : _x ∈ incidence_set G v) => and.left h

@[simp] theorem mem_edge_set {V : Type u} (G : simple_graph V) {v : V} {w : V} :
    quotient.mk (v, w) ∈ edge_set G ↔ adj G v w :=
  iff.refl (quotient.mk (v, w) ∈ edge_set G)

/--
Two vertices are adjacent iff there is an edge between them.  The
condition `v ≠ w` ensures they are different endpoints of the edge,
which is necessary since when `v = w` the existential
`∃ (e ∈ G.edge_set), v ∈ e ∧ w ∈ e` is satisfied by every edge
incident to `v`.
-/
theorem adj_iff_exists_edge {V : Type u} (G : simple_graph V) {v : V} {w : V} :
    adj G v w ↔ v ≠ w ∧ ∃ (e : sym2 V), ∃ (H : e ∈ edge_set G), v ∈ e ∧ w ∈ e :=
  sorry

theorem edge_other_ne {V : Type u} (G : simple_graph V) {e : sym2 V} (he : e ∈ edge_set G) {v : V}
    (h : v ∈ e) : sym2.mem.other h ≠ v :=
  ne_of_adj G
    (eq.mp (Eq._oldrec (Eq.refl (quotient.mk (v, sym2.mem.other h) ∈ edge_set G)) sym2.eq_swap)
      (eq.mp (Eq._oldrec (Eq.refl (e ∈ edge_set G)) (Eq.symm (sym2.mem_other_spec h))) he))

protected instance edge_set_decidable_pred {V : Type u} (G : simple_graph V)
    [DecidableRel (adj G)] : decidable_pred (edge_set G) :=
  sym2.from_rel.decidable_pred (sym G)

protected instance edges_fintype {V : Type u} (G : simple_graph V) [DecidableEq V] [fintype V]
    [DecidableRel (adj G)] : fintype ↥(edge_set G) :=
  subtype.fintype fun (x : sym2 V) => x ∈ edge_set G

protected instance incidence_set_decidable_pred {V : Type u} (G : simple_graph V) [DecidableEq V]
    [DecidableRel (adj G)] (v : V) : decidable_pred (incidence_set G v) :=
  fun (e : sym2 V) => and.decidable

/--
The `edge_set` of the graph as a `finset`.
-/
def edge_finset {V : Type u} (G : simple_graph V) [DecidableEq V] [fintype V]
    [DecidableRel (adj G)] : finset (sym2 V) :=
  set.to_finset (edge_set G)

@[simp] theorem mem_edge_finset {V : Type u} (G : simple_graph V) [DecidableEq V] [fintype V]
    [DecidableRel (adj G)] (e : sym2 V) : e ∈ edge_finset G ↔ e ∈ edge_set G :=
  set.mem_to_finset

@[simp] theorem edge_set_univ_card {V : Type u} (G : simple_graph V) [DecidableEq V] [fintype V]
    [DecidableRel (adj G)] : finset.card finset.univ = finset.card (edge_finset G) :=
  fintype.card_of_subtype (edge_finset G) (mem_edge_finset G)

@[simp] theorem irrefl {V : Type u} (G : simple_graph V) {v : V} : ¬adj G v v := loopless G v

theorem edge_symm {V : Type u} (G : simple_graph V) (u : V) (v : V) : adj G u v ↔ adj G v u :=
  { mp := fun (x : adj G u v) => sym G x, mpr := fun (x : adj G v u) => sym G x }

@[simp] theorem mem_neighbor_set {V : Type u} (G : simple_graph V) (v : V) (w : V) :
    w ∈ neighbor_set G v ↔ adj G v w :=
  iff.rfl

@[simp] theorem mem_incidence_set {V : Type u} (G : simple_graph V) (v : V) (w : V) :
    quotient.mk (v, w) ∈ incidence_set G v ↔ adj G v w :=
  sorry

theorem mem_incidence_iff_neighbor {V : Type u} (G : simple_graph V) {v : V} {w : V} :
    quotient.mk (v, w) ∈ incidence_set G v ↔ w ∈ neighbor_set G v :=
  sorry

theorem adj_incidence_set_inter {V : Type u} (G : simple_graph V) {v : V} {e : sym2 V}
    (he : e ∈ edge_set G) (h : v ∈ e) :
    incidence_set G v ∩ incidence_set G (sym2.mem.other h) = singleton e :=
  sorry

/--
The set of common neighbors between two vertices `v` and `w` in a graph `G` is the
intersection of the neighbor sets of `v` and `w`.
-/
def common_neighbors {V : Type u} (G : simple_graph V) (v : V) (w : V) : set V :=
  neighbor_set G v ∩ neighbor_set G w

theorem common_neighbors_eq {V : Type u} (G : simple_graph V) (v : V) (w : V) :
    common_neighbors G v w = neighbor_set G v ∩ neighbor_set G w :=
  rfl

theorem mem_common_neighbors {V : Type u} (G : simple_graph V) {u : V} {v : V} {w : V} :
    u ∈ common_neighbors G v w ↔ adj G v u ∧ adj G w u :=
  sorry

theorem common_neighbors_symm {V : Type u} (G : simple_graph V) (v : V) (w : V) :
    common_neighbors G v w = common_neighbors G w v :=
  sorry

theorem not_mem_common_neighbors_left {V : Type u} (G : simple_graph V) (v : V) (w : V) :
    ¬v ∈ common_neighbors G v w :=
  sorry

theorem not_mem_common_neighbors_right {V : Type u} (G : simple_graph V) (v : V) (w : V) :
    ¬w ∈ common_neighbors G v w :=
  sorry

theorem common_neighbors_subset_neighbor_set {V : Type u} (G : simple_graph V) (v : V) (w : V) :
    common_neighbors G v w ⊆ neighbor_set G v :=
  sorry

/--
Given an edge incident to a particular vertex, get the other vertex on the edge.
-/
def other_vertex_of_incident {V : Type u} (G : simple_graph V) [DecidableEq V] {v : V} {e : sym2 V}
    (h : e ∈ incidence_set G v) : V :=
  sym2.mem.other' sorry

theorem edge_mem_other_incident_set {V : Type u} (G : simple_graph V) [DecidableEq V] {v : V}
    {e : sym2 V} (h : e ∈ incidence_set G v) : e ∈ incidence_set G (other_vertex_of_incident G h) :=
  sorry

theorem incidence_other_prop {V : Type u} (G : simple_graph V) [DecidableEq V] {v : V} {e : sym2 V}
    (h : e ∈ incidence_set G v) : other_vertex_of_incident G h ∈ neighbor_set G v :=
  sorry

@[simp] theorem incidence_other_neighbor_edge {V : Type u} (G : simple_graph V) [DecidableEq V]
    {v : V} {w : V} (h : w ∈ neighbor_set G v) :
    other_vertex_of_incident G (iff.mpr (mem_incidence_iff_neighbor G) h) = w :=
  iff.mp sym2.congr_right
    (sym2.mem_other_spec' (and.right (iff.mpr (mem_incidence_iff_neighbor G) h)))

/--
There is an equivalence between the set of edges incident to a given
vertex and the set of vertices adjacent to the vertex.
-/
def incidence_set_equiv_neighbor_set {V : Type u} (G : simple_graph V) [DecidableEq V] (v : V) :
    ↥(incidence_set G v) ≃ ↥(neighbor_set G v) :=
  equiv.mk
    (fun (e : ↥(incidence_set G v)) =>
      { val := other_vertex_of_incident G sorry, property := sorry })
    (fun (w : ↥(neighbor_set G v)) => { val := quotient.mk (v, subtype.val w), property := sorry })
    sorry sorry

/-!
## Finiteness at a vertex

This section contains definitions and lemmas concerning vertices that
have finitely many adjacent vertices.  We denote this condition by
`fintype (G.neighbor_set v)`.

We define `G.neighbor_finset v` to be the `finset` version of `G.neighbor_set v`.
Use `neighbor_finset_eq_filter` to rewrite this definition as a `filter`.
-/

/--
`G.neighbors v` is the `finset` version of `G.adj v` in case `G` is
locally finite at `v`.
-/
def neighbor_finset {V : Type u} (G : simple_graph V) (v : V) [fintype ↥(neighbor_set G v)] :
    finset V :=
  set.to_finset (neighbor_set G v)

@[simp] theorem mem_neighbor_finset {V : Type u} (G : simple_graph V) (v : V)
    [fintype ↥(neighbor_set G v)] (w : V) : w ∈ neighbor_finset G v ↔ adj G v w :=
  set.mem_to_finset

/--
`G.degree v` is the number of vertices adjacent to `v`.
-/
def degree {V : Type u} (G : simple_graph V) (v : V) [fintype ↥(neighbor_set G v)] : ℕ :=
  finset.card (neighbor_finset G v)

@[simp] theorem card_neighbor_set_eq_degree {V : Type u} (G : simple_graph V) (v : V)
    [fintype ↥(neighbor_set G v)] : fintype.card ↥(neighbor_set G v) = degree G v :=
  Eq.symm (set.to_finset_card (neighbor_set G v))

theorem degree_pos_iff_exists_adj {V : Type u} (G : simple_graph V) (v : V)
    [fintype ↥(neighbor_set G v)] : 0 < degree G v ↔ ∃ (w : V), adj G v w :=
  sorry

protected instance incidence_set_fintype {V : Type u} (G : simple_graph V) (v : V)
    [fintype ↥(neighbor_set G v)] [DecidableEq V] : fintype ↥(incidence_set G v) :=
  fintype.of_equiv (↥(neighbor_set G v)) (equiv.symm (incidence_set_equiv_neighbor_set G v))

/--
This is the `finset` version of `incidence_set`.
-/
def incidence_finset {V : Type u} (G : simple_graph V) (v : V) [fintype ↥(neighbor_set G v)]
    [DecidableEq V] : finset (sym2 V) :=
  set.to_finset (incidence_set G v)

@[simp] theorem card_incidence_set_eq_degree {V : Type u} (G : simple_graph V) (v : V)
    [fintype ↥(neighbor_set G v)] [DecidableEq V] :
    fintype.card ↥(incidence_set G v) = degree G v :=
  sorry

@[simp] theorem mem_incidence_finset {V : Type u} (G : simple_graph V) (v : V)
    [fintype ↥(neighbor_set G v)] [DecidableEq V] (e : sym2 V) :
    e ∈ incidence_finset G v ↔ e ∈ incidence_set G v :=
  set.mem_to_finset

/--
A graph is locally finite if every vertex has a finite neighbor set.
-/
def locally_finite {V : Type u} (G : simple_graph V) := (v : V) → fintype ↥(neighbor_set G v)

/--
A locally finite simple graph is regular of degree `d` if every vertex has degree `d`.
-/
def is_regular_of_degree {V : Type u} (G : simple_graph V) [locally_finite G] (d : ℕ) :=
  ∀ (v : V), degree G v = d

theorem is_regular_of_degree_eq {V : Type u} (G : simple_graph V) [locally_finite G] {d : ℕ}
    (h : is_regular_of_degree G d) (v : V) : degree G v = d :=
  h v

protected instance neighbor_set_fintype {V : Type u} (G : simple_graph V) [fintype V]
    [DecidableRel (adj G)] (v : V) : fintype ↥(neighbor_set G v) :=
  subtype.fintype fun (x : V) => x ∈ neighbor_set G v

theorem neighbor_finset_eq_filter {V : Type u} (G : simple_graph V) [fintype V] {v : V}
    [DecidableRel (adj G)] : neighbor_finset G v = finset.filter (adj G v) finset.univ :=
  sorry

@[simp] theorem complete_graph_degree {V : Type u} [fintype V] [DecidableEq V] (v : V) :
    degree (complete_graph V) v = fintype.card V - 1 :=
  sorry

theorem complete_graph_is_regular {V : Type u} [fintype V] [DecidableEq V] :
    is_regular_of_degree (complete_graph V) (fintype.card V - 1) :=
  sorry

/--
The minimum degree of all vertices
-/
def min_degree {V : Type u} [fintype V] (G : simple_graph V) [Nonempty V] [DecidableRel (adj G)] :
    ℕ :=
  finset.min' (finset.image (fun (v : V) => degree G v) finset.univ) sorry

/--
The maximum degree of all vertices
-/
def max_degree {V : Type u} [fintype V] (G : simple_graph V) [Nonempty V] [DecidableRel (adj G)] :
    ℕ :=
  finset.max' (finset.image (fun (v : V) => degree G v) finset.univ) sorry

/-! The following lemmas about `fintype.card` use noncomputable decidable instances to get fintype
assumptions. -/

theorem degree_lt_card_verts {V : Type u} [fintype V] (G : simple_graph V) (v : V) :
    degree G v < fintype.card V :=
  sorry

theorem card_common_neighbors_le_degree_left {V : Type u} (G : simple_graph V) [fintype V] (v : V)
    (w : V) : fintype.card ↥(common_neighbors G v w) ≤ degree G v :=
  sorry

theorem card_common_neighbors_le_degree_right {V : Type u} (G : simple_graph V) [fintype V] (v : V)
    (w : V) : fintype.card ↥(common_neighbors G v w) ≤ degree G w :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (fintype.card ↥(common_neighbors G v w) ≤ degree G w))
        (common_neighbors_symm G v w)))
    (card_common_neighbors_le_degree_left G w v)

theorem card_common_neighbors_lt_card_verts {V : Type u} (G : simple_graph V) [fintype V] (v : V)
    (w : V) : fintype.card ↥(common_neighbors G v w) < fintype.card V :=
  nat.lt_of_le_of_lt (card_common_neighbors_le_degree_left G v w) (degree_lt_card_verts G v)

/--
If the condition `G.adj v w` fails, then `card_common_neighbors_le_degree` is
the best we can do in general.
-/
theorem adj.card_common_neighbors_lt_degree {V : Type u} [fintype V] {G : simple_graph V} {v : V}
    {w : V} (h : adj G v w) : fintype.card ↥(common_neighbors G v w) < degree G v :=
  sorry

/-!
## Complement of a simple graph

This section contains definitions and lemmas concerning the complement of a simple graph.
-/

/--
We define `compl G` to be the `simple_graph V` such that no two adjacent vertices in `G`
are adjacent in the complement, and every nonadjacent pair of vertices is adjacent
(still ensuring that vertices are not adjacent to themselves.)
-/
def compl {V : Type u} (G : simple_graph V) : simple_graph V :=
  mk fun (v w : V) => v ≠ w ∧ ¬adj G v w

protected instance has_compl {V : Type u} : has_compl (simple_graph V) := has_compl.mk compl

@[simp] theorem compl_adj {V : Type u} (G : simple_graph V) (v : V) (w : V) :
    adj (Gᶜ) v w ↔ v ≠ w ∧ ¬adj G v w :=
  iff.rfl

@[simp] theorem compl_compl {V : Type u} (G : simple_graph V) : Gᶜᶜ = G := sorry

@[simp] theorem compl_involutive {V : Type u} : function.involutive compl := compl_compl

theorem compl_neighbor_set_disjoint {V : Type u} (G : simple_graph V) (v : V) :
    disjoint (neighbor_set G v) (neighbor_set (Gᶜ) v) :=
  sorry

theorem neighbor_set_union_compl_neighbor_set_eq {V : Type u} (G : simple_graph V) (v : V) :
    neighbor_set G v ∪ neighbor_set (Gᶜ) v = (singleton vᶜ) :=
  sorry

end Mathlib