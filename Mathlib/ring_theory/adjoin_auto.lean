/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.ring_theory.polynomial.basic
import Mathlib.algebra.algebra.subalgebra
import Mathlib.PostPort

universes u v w 

namespace Mathlib

/-!
# Adjoining elements to form subalgebras

This file develops the basic theory of subalgebras of an R-algebra generated
by a set of elements. A basic interface for `adjoin` is set up, and various
results about finitely-generated subalgebras and submodules are proved.

## Definitions

* `fg (S : subalgebra R A)` : A predicate saying that the subalgebra is finitely-generated
as an A-algebra

## Tags

adjoin, algebra, finitely-generated algebra

-/

namespace algebra


theorem subset_adjoin {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    {s : set A} : s ⊆ ↑(adjoin R s) :=
  set.subset.trans (set.subset_union_right (set.range ⇑(algebra_map R A)) s)
    subsemiring.subset_closure

theorem adjoin_le {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A] {s : set A}
    {S : subalgebra R A} (H : s ⊆ ↑S) : adjoin R s ≤ S :=
  iff.mpr subsemiring.closure_le (set.union_subset (subalgebra.range_le S) H)

theorem adjoin_le_iff {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    {s : set A} {S : subalgebra R A} : adjoin R s ≤ S ↔ s ⊆ ↑S :=
  { mp := set.subset.trans subset_adjoin, mpr := adjoin_le }

theorem adjoin_mono {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    {s : set A} {t : set A} (H : s ⊆ t) : adjoin R s ≤ adjoin R t :=
  iff.mpr subsemiring.closure_le
    (set.subset.trans (set.union_subset_union_right (set.range ⇑(algebra_map R A)) H)
      subsemiring.subset_closure)

@[simp] theorem adjoin_empty (R : Type u) (A : Type v) [comm_semiring R] [semiring A]
    [algebra R A] : adjoin R ∅ = ⊥ :=
  iff.mpr eq_bot_iff (adjoin_le (set.empty_subset ↑⊥))

theorem adjoin_eq_span (R : Type u) {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    (s : set A) : ↑(adjoin R s) = submodule.span R (monoid.closure s) :=
  sorry

theorem adjoin_image (R : Type u) {A : Type v} {B : Type w} [comm_semiring R] [semiring A]
    [semiring B] [algebra R A] [algebra R B] (f : alg_hom R A B) (s : set A) :
    adjoin R (⇑f '' s) = subalgebra.map (adjoin R s) f :=
  le_antisymm (adjoin_le (set.image_subset (⇑f) subset_adjoin))
    (iff.mpr subalgebra.map_le (adjoin_le (iff.mp set.image_subset_iff subset_adjoin)))

@[simp] theorem adjoin_insert_adjoin (R : Type u) {A : Type v} [comm_semiring R] [semiring A]
    [algebra R A] (s : set A) (x : A) :
    adjoin R (insert x ↑↑(adjoin R s)) = adjoin R (insert x s) :=
  sorry

theorem adjoin_union (R : Type u) {A : Type v} [comm_semiring R] [comm_semiring A] [algebra R A]
    (s : set A) (t : set A) :
    adjoin R (s ∪ t) = subalgebra.under (adjoin R s) (adjoin (↥(adjoin R s)) t) :=
  sorry

theorem adjoin_eq_range (R : Type u) {A : Type v} [comm_semiring R] [comm_semiring A] [algebra R A]
    (s : set A) : adjoin R s = alg_hom.range (mv_polynomial.aeval coe) :=
  sorry

theorem adjoin_singleton_eq_range (R : Type u) {A : Type v} [comm_semiring R] [comm_semiring A]
    [algebra R A] (x : A) : adjoin R (singleton x) = alg_hom.range (polynomial.aeval x) :=
  sorry

theorem adjoin_singleton_one (R : Type u) {A : Type v} [comm_semiring R] [comm_semiring A]
    [algebra R A] : adjoin R (singleton 1) = ⊥ :=
  iff.mpr eq_bot_iff (adjoin_le (iff.mpr set.singleton_subset_iff (subalgebra.one_mem ⊥)))

theorem adjoin_union_coe_submodule (R : Type u) {A : Type v} [comm_semiring R] [comm_semiring A]
    [algebra R A] (s : set A) (t : set A) : ↑(adjoin R (s ∪ t)) = ↑(adjoin R s) * ↑(adjoin R t) :=
  sorry

theorem adjoin_int {R : Type u} [comm_ring R] (s : set R) :
    adjoin ℤ s = subalgebra_of_is_subring (ring.closure s) :=
  le_antisymm (adjoin_le ring.subset_closure) (ring.closure_subset subset_adjoin)

theorem mem_adjoin_iff {R : Type u} {A : Type v} [comm_ring R] [ring A] [algebra R A] {s : set A}
    {x : A} : x ∈ adjoin R s ↔ x ∈ ring.closure (set.range ⇑(algebra_map R A) ∪ s) :=
  sorry

theorem adjoin_eq_ring_closure {R : Type u} {A : Type v} [comm_ring R] [ring A] [algebra R A]
    (s : set A) : ↑(adjoin R s) = ring.closure (set.range ⇑(algebra_map R A) ∪ s) :=
  set.ext fun (x : A) => mem_adjoin_iff

theorem fg_trans {R : Type u} {A : Type v} [comm_ring R] [comm_ring A] [algebra R A] {s : set A}
    {t : set A} (h1 : submodule.fg ↑(adjoin R s)) (h2 : submodule.fg ↑(adjoin (↥(adjoin R s)) t)) :
    submodule.fg ↑(adjoin R (s ∪ t)) :=
  sorry

end algebra


namespace subalgebra


/-- A subalgebra `S` is finitely generated if there exists `t : finset A` such that
`algebra.adjoin R t = S`. -/
def fg {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    (S : subalgebra R A) :=
  ∃ (t : finset A), algebra.adjoin R ↑t = S

theorem fg_adjoin_finset {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    (s : finset A) : fg (algebra.adjoin R ↑s) :=
  Exists.intro s rfl

theorem fg_def {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    {S : subalgebra R A} : fg S ↔ ∃ (t : set A), set.finite t ∧ algebra.adjoin R t = S :=
  sorry

theorem fg_bot {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A] : fg ⊥ :=
  Exists.intro ∅ (algebra.adjoin_empty R A)

theorem fg_of_fg_to_submodule {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    {S : subalgebra R A} : submodule.fg ↑S → fg S :=
  sorry

theorem fg_of_noetherian {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    [is_noetherian R A] (S : subalgebra R A) : fg S :=
  fg_of_fg_to_submodule (is_noetherian.noetherian ↑S)

theorem fg_of_submodule_fg {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    (h : submodule.fg ⊤) : fg ⊤ :=
  sorry

theorem fg_map {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [algebra R A]
    [semiring B] [algebra R B] (S : subalgebra R A) (f : alg_hom R A B) (hs : fg S) :
    fg (map S f) :=
  sorry

theorem fg_of_fg_map {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A]
    [algebra R A] [semiring B] [algebra R B] (S : subalgebra R A) (f : alg_hom R A B)
    (hf : function.injective ⇑f) (hs : fg (map S f)) : fg S :=
  sorry

theorem fg_top {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    (S : subalgebra R A) : fg ⊤ ↔ fg S :=
  sorry

theorem induction_on_adjoin {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    [is_noetherian R A] (P : subalgebra R A → Prop) (base : P ⊥)
    (ih : ∀ (S : subalgebra R A) (x : A), P S → P (algebra.adjoin R (insert x ↑S)))
    (S : subalgebra R A) : P S :=
  sorry

end subalgebra


/-- The image of a Noetherian R-algebra under an R-algebra map is a Noetherian ring. -/
protected instance alg_hom.is_noetherian_ring_range {R : Type u} {A : Type v} {B : Type w}
    [comm_ring R] [comm_ring A] [comm_ring B] [algebra R A] [algebra R B] (f : alg_hom R A B)
    [is_noetherian_ring A] : is_noetherian_ring ↥(alg_hom.range f) :=
  Mathlib.is_noetherian_ring_range (alg_hom.to_ring_hom f)

theorem is_noetherian_ring_of_fg {R : Type u} {A : Type v} [comm_ring R] [comm_ring A] [algebra R A]
    {S : subalgebra R A} (HS : subalgebra.fg S) [is_noetherian_ring R] : is_noetherian_ring ↥S :=
  sorry

theorem is_noetherian_ring_closure {R : Type u} [comm_ring R] (s : set R) (hs : set.finite s) :
    is_noetherian_ring ↥(ring.closure s) :=
  (fun (this : is_noetherian_ring ↥(subalgebra_of_is_subring (ring.closure s))) => this)
    (algebra.adjoin_int s ▸
      is_noetherian_ring_of_fg
        (iff.mpr subalgebra.fg_def (Exists.intro s { left := hs, right := rfl })))

end Mathlib