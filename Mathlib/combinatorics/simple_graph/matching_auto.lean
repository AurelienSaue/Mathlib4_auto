/-
Copyright (c) 2020 Alena Gusakov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alena Gusakov.
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.fintype.basic
import Mathlib.data.sym2
import Mathlib.combinatorics.simple_graph.basic
import PostPort

universes u l 

namespace Mathlib

/-!
# Matchings


## Main definitions

* a `matching` on a simple graph is a subset of its edge set such that
   no two edges share an endpoint.

* a `perfect_matching` on a simple graph is a matching in which every
   vertex belongs to an edge.

TODO:
  - Lemma stating that the existence of a perfect matching on `G` implies that
    the cardinality of `V` is even (assuming it's finite)
  - Hall's Marriage Theorem
  - Tutte's Theorem
  - consider coercions instead of type definition for `matching`:
    https://github.com/leanprover-community/mathlib/pull/5156#discussion_r532935457
  - consider expressing `matching_verts` as union:
    https://github.com/leanprover-community/mathlib/pull/5156#discussion_r532906131

TODO: Tutte and Hall require a definition of subgraphs.
-/

namespace simple_graph


/--
A matching on `G` is a subset of its edges such that no two edges share a vertex.
-/
structure matching {V : Type u} (G : simple_graph V) 
where
  edges : set (sym2 V)
  sub_edges : edges ⊆ edge_set G
  disjoint : ∀ (x y : sym2 V), x ∈ edges → y ∈ edges → ∀ (v : V), v ∈ x ∧ v ∈ y → x = y

protected instance matching.inhabited {V : Type u} (G : simple_graph V) : Inhabited (matching G) :=
  { default := matching.mk ∅ sorry sorry }

/--
`M.support` is the set of vertices of `G` that are
contained in some edge of matching `M`
-/
def matching.support {V : Type u} {G : simple_graph V} (M : matching G) : set V :=
  set_of fun (v : V) => ∃ (x : sym2 V), ∃ (H : x ∈ matching.edges M), v ∈ x

/--
A perfect matching `M` on graph `G` is a matching such that
  every vertex is contained in an edge of `M`.
-/
def matching.is_perfect {V : Type u} {G : simple_graph V} (M : matching G)  :=
  matching.support M = set.univ

theorem matching.is_perfect_iff {V : Type u} {G : simple_graph V} (M : matching G) : matching.is_perfect M ↔ ∀ (v : V), ∃ (e : sym2 V), ∃ (H : e ∈ matching.edges M), v ∈ e :=
  set.eq_univ_iff_forall

