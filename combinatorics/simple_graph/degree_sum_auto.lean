/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kyle Miller
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.combinatorics.simple_graph.basic
import Mathlib.algebra.big_operators.basic
import Mathlib.data.nat.parity
import Mathlib.data.zmod.parity
import Mathlib.tactic.omega.default
import PostPort

universes u l 

namespace Mathlib

/-!
# Degree-sum formula and handshaking lemma

The degree-sum formula is that the sum of the degrees of the vertices in
a finite graph is equal to twice the number of edges.  The handshaking lemma,
a corollary, is that the number of odd-degree vertices is even.

## Main definitions

- A `dart` is a directed edge, consisting of an ordered pair of adjacent vertices,
  thought of as being a directed edge.
- `simple_graph.sum_degrees_eq_twice_card_edges` is the degree-sum formula.
- `simple_graph.even_card_odd_degree_vertices` is the handshaking lemma.
- `simple_graph.odd_card_odd_degree_vertices_ne` is that the number of odd-degree
  vertices different from a given odd-degree vertex is odd.
- `simple_graph.exists_ne_odd_degree_of_exists_odd_degree` is that the existence of an
  odd-degree vertex implies the existence of another one.

## Implementation notes

We give a combinatorial proof by using the facts that (1) the map from
darts to vertices is such that each fiber has cardinality the degree
of the corresponding vertex and that (2) the map from darts to edges is 2-to-1.

## Tags

simple graphs, sums, degree-sum formula, handshaking lemma
-/

namespace simple_graph


/-- A dart is a directed edge, consisting of an ordered pair of adjacent vertices. -/
structure dart {V : Type u} (G : simple_graph V) 
where
  fst : V
  snd : V
  is_adj : adj G fst snd

protected instance dart.fintype {V : Type u} (G : simple_graph V) [fintype V] [DecidableRel (adj G)] : fintype (dart G) :=
  fintype.of_equiv (sigma fun (v : V) => ↥(neighbor_set G v))
    (equiv.mk (fun (s : sigma fun (v : V) => ↥(neighbor_set G v)) => dart.mk (sigma.fst s) ↑(sigma.snd s) sorry)
      (fun (d : dart G) => sigma.mk (dart.fst d) { val := dart.snd d, property := dart.is_adj d }) sorry sorry)

/-- The edge associated to the dart. -/
def dart.edge {V : Type u} {G : simple_graph V} (d : dart G) : sym2 V :=
  quotient.mk (dart.fst d, dart.snd d)

@[simp] theorem dart.edge_mem {V : Type u} {G : simple_graph V} (d : dart G) : dart.edge d ∈ edge_set G :=
  dart.is_adj d

/-- The dart with reversed orientation from a given dart. -/
def dart.rev {V : Type u} {G : simple_graph V} (d : dart G) : dart G :=
  dart.mk (dart.snd d) (dart.fst d) sorry

@[simp] theorem dart.rev_edge {V : Type u} {G : simple_graph V} (d : dart G) : dart.edge (dart.rev d) = dart.edge d :=
  sym2.eq_swap

@[simp] theorem dart.rev_rev {V : Type u} {G : simple_graph V} (d : dart G) : dart.rev (dart.rev d) = d :=
  dart.ext (dart.rev (dart.rev d)) d rfl rfl

@[simp] theorem dart.rev_involutive {V : Type u} {G : simple_graph V} : function.involutive dart.rev :=
  dart.rev_rev

theorem dart.rev_ne {V : Type u} {G : simple_graph V} (d : dart G) : dart.rev d ≠ d := sorry

theorem dart_edge_eq_iff {V : Type u} {G : simple_graph V} (d₁ : dart G) (d₂ : dart G) : dart.edge d₁ = dart.edge d₂ ↔ d₁ = d₂ ∨ d₁ = dart.rev d₂ := sorry

/-- For a given vertex `v`, this is the bijective map from the neighbor set at `v`
to the darts `d` with `d.fst = v`. --/
def dart_of_neighbor_set {V : Type u} (G : simple_graph V) (v : V) (w : ↥(neighbor_set G v)) : dart G :=
  dart.mk v ↑w sorry

theorem dart_of_neighbor_set_injective {V : Type u} (G : simple_graph V) (v : V) : function.injective (dart_of_neighbor_set G v) :=
  fun (e₁ e₂ : ↥(neighbor_set G v)) (h : dart_of_neighbor_set G v e₁ = dart_of_neighbor_set G v e₂) =>
    dart.mk.inj_arrow h fun (h₁ : v = v) (h₂ : ↑e₁ = ↑e₂) => subtype.ext h₂

protected instance dart.inhabited {V : Type u} (G : simple_graph V) [Inhabited V] [Inhabited ↥(neighbor_set G Inhabited.default)] : Inhabited (dart G) :=
  { default := dart_of_neighbor_set G Inhabited.default Inhabited.default }

theorem dart_fst_fiber {V : Type u} (G : simple_graph V) [fintype V] [DecidableRel (adj G)] [DecidableEq V] (v : V) : finset.filter (fun (d : dart G) => dart.fst d = v) finset.univ = finset.image (dart_of_neighbor_set G v) finset.univ := sorry

theorem dart_fst_fiber_card_eq_degree {V : Type u} (G : simple_graph V) [fintype V] [DecidableRel (adj G)] [DecidableEq V] (v : V) : finset.card (finset.filter (fun (d : dart G) => dart.fst d = v) finset.univ) = degree G v := sorry

theorem dart_card_eq_sum_degrees {V : Type u} (G : simple_graph V) [fintype V] [DecidableRel (adj G)] : fintype.card (dart G) = finset.sum finset.univ fun (v : V) => degree G v := sorry

theorem dart.edge_fiber {V : Type u} {G : simple_graph V} [fintype V] [DecidableRel (adj G)] [DecidableEq V] (d : dart G) : finset.filter (fun (d' : dart G) => dart.edge d' = dart.edge d) finset.univ = insert d (singleton (dart.rev d)) := sorry

theorem dart_edge_fiber_card {V : Type u} (G : simple_graph V) [fintype V] [DecidableRel (adj G)] [DecidableEq V] (e : sym2 V) (h : e ∈ edge_set G) : finset.card (finset.filter (fun (d : dart G) => dart.edge d = e) finset.univ) = bit0 1 := sorry

theorem dart_card_eq_twice_card_edges {V : Type u} (G : simple_graph V) [fintype V] [DecidableRel (adj G)] [DecidableEq V] : fintype.card (dart G) = bit0 1 * finset.card (edge_finset G) := sorry

/-- The degree-sum formula.  This is also known as the handshaking lemma, which might
more specifically refer to `simple_graph.even_card_odd_degree_vertices`. -/
theorem sum_degrees_eq_twice_card_edges {V : Type u} (G : simple_graph V) [fintype V] [DecidableRel (adj G)] [DecidableEq V] : (finset.sum finset.univ fun (v : V) => degree G v) = bit0 1 * finset.card (edge_finset G) :=
  Eq.trans (Eq.symm (dart_card_eq_sum_degrees G)) (dart_card_eq_twice_card_edges G)

/-- The handshaking lemma.  See also `simple_graph.sum_degrees_eq_twice_card_edges`. -/
theorem even_card_odd_degree_vertices {V : Type u} (G : simple_graph V) [fintype V] [DecidableRel (adj G)] : even (finset.card (finset.filter (fun (v : V) => odd (degree G v)) finset.univ)) := sorry

theorem odd_card_odd_degree_vertices_ne {V : Type u} (G : simple_graph V) [fintype V] [DecidableEq V] [DecidableRel (adj G)] (v : V) (h : odd (degree G v)) : odd (finset.card (finset.filter (fun (w : V) => w ≠ v ∧ odd (degree G w)) finset.univ)) := sorry

theorem exists_ne_odd_degree_of_exists_odd_degree {V : Type u} (G : simple_graph V) [fintype V] [DecidableRel (adj G)] (v : V) (h : odd (degree G v)) : ∃ (w : V), w ≠ v ∧ odd (degree G w) := sorry

