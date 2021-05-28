/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.deprecated.subgroup
import Mathlib.deprecated.group
import Mathlib.PostPort

universes u l v u_1 

namespace Mathlib

/-- `S` is a subring: a set containing 1 and closed under multiplication, addition and and additive inverse. -/
class is_subring {R : Type u} [ring R] (S : set R) 
extends is_add_subgroup S, is_submonoid S
where

/-- The ring structure on a subring coerced to a type. -/
def subset.ring {R : Type u} [ring R] {S : set R} [is_subring S] : ring ↥S :=
  ring.mk add_comm_group.add sorry add_comm_group.zero sorry sorry add_comm_group.neg add_comm_group.sub sorry sorry
    monoid.mul sorry monoid.one sorry sorry sorry sorry

/-- The ring structure on a subring coerced to a type. -/
def subtype.ring {R : Type u} [ring R] {S : set R} [is_subring S] : ring (Subtype S) :=
  subset.ring

namespace ring_hom


protected instance is_subring_preimage {R : Type u} {S : Type v} [ring R] [ring S] (f : R →+* S) (s : set S) [is_subring s] : is_subring (⇑f ⁻¹' s) :=
  is_subring.mk

protected instance is_subring_image {R : Type u} {S : Type v} [ring R] [ring S] (f : R →+* S) (s : set R) [is_subring s] : is_subring (⇑f '' s) :=
  is_subring.mk

protected instance is_subring_set_range {R : Type u} {S : Type v} [ring R] [ring S] (f : R →+* S) : is_subring (set.range ⇑f) :=
  is_subring.mk

end ring_hom


/-- Restrict the codomain of a ring homomorphism to a subring that includes the range. -/
def ring_hom.cod_restrict {R : Type u} {S : Type v} [ring R] [ring S] (f : R →+* S) (s : set S) [is_subring s] (h : ∀ (x : R), coe_fn f x ∈ s) : R →+* ↥s :=
  ring_hom.mk (fun (x : R) => { val := coe_fn f x, property := h x }) sorry sorry sorry sorry

/-- Coersion `S → R` as a ring homormorphism-/
def is_subring.subtype {R : Type u} [ring R] (S : set R) [is_subring S] : ↥S →+* R :=
  ring_hom.mk coe sorry sorry sorry sorry

@[simp] theorem is_subring.coe_subtype {R : Type u} [ring R] {S : set R} [is_subring S] : ⇑(is_subring.subtype S) = coe :=
  rfl

/-- The commutative ring structure on a subring coerced to a type. -/
def subset.comm_ring {cR : Type u} [comm_ring cR] {S : set cR} [is_subring S] : comm_ring ↥S :=
  comm_ring.mk ring.add sorry ring.zero sorry sorry ring.neg ring.sub sorry sorry ring.mul sorry ring.one sorry sorry
    sorry sorry sorry

/-- The commutative ring structure on a subring coerced to a type. -/
def subtype.comm_ring {cR : Type u} [comm_ring cR] {S : set cR} [is_subring S] : comm_ring (Subtype S) :=
  subset.comm_ring

/-- The integral domain structure on a subring of an integral domain coerced to a type. -/
def subring.domain {D : Type u_1} [integral_domain D] (S : set D) [is_subring S] : integral_domain ↥S :=
  integral_domain.mk comm_ring.add sorry comm_ring.zero sorry sorry comm_ring.neg comm_ring.sub sorry sorry comm_ring.mul
    sorry comm_ring.one sorry sorry sorry sorry sorry sorry sorry

protected instance is_subring.inter {R : Type u} [ring R] (S₁ : set R) (S₂ : set R) [is_subring S₁] [is_subring S₂] : is_subring (S₁ ∩ S₂) :=
  is_subring.mk

protected instance is_subring.Inter {R : Type u} [ring R] {ι : Sort u_1} (S : ι → set R) [h : ∀ (y : ι), is_subring (S y)] : is_subring (set.Inter S) :=
  is_subring.mk

theorem is_subring_Union_of_directed {R : Type u} [ring R] {ι : Type u_1} [hι : Nonempty ι] (s : ι → set R) [∀ (i : ι), is_subring (s i)] (directed : ∀ (i j : ι), ∃ (k : ι), s i ⊆ s k ∧ s j ⊆ s k) : is_subring (set.Union fun (i : ι) => s i) :=
  is_subring.mk

namespace ring


def closure {R : Type u} [ring R] (s : set R) : set R :=
  add_group.closure (monoid.closure s)

theorem exists_list_of_mem_closure {R : Type u} [ring R] {s : set R} {a : R} (h : a ∈ closure s) : ∃ (L : List (List R)), (∀ (l : List R), l ∈ L → ∀ (x : R), x ∈ l → x ∈ s ∨ x = -1) ∧ list.sum (list.map list.prod L) = a := sorry

protected theorem in_closure.rec_on {R : Type u} [ring R] {s : set R} {C : R → Prop} {x : R} (hx : x ∈ closure s) (h1 : C 1) (hneg1 : C (-1)) (hs : ∀ (z : R), z ∈ s → ∀ (n : R), C n → C (z * n)) (ha : ∀ {x y : R}, C x → C y → C (x + y)) : C x := sorry

protected instance closure.is_subring {R : Type u} [ring R] {s : set R} : is_subring (closure s) :=
  is_subring.mk

theorem mem_closure {R : Type u} [ring R] {s : set R} {a : R} : a ∈ s → a ∈ closure s :=
  add_group.mem_closure ∘ monoid.subset_closure

theorem subset_closure {R : Type u} [ring R] {s : set R} : s ⊆ closure s :=
  fun (_x : R) => mem_closure

theorem closure_subset {R : Type u} [ring R] {s : set R} {t : set R} [is_subring t] : s ⊆ t → closure s ⊆ t :=
  add_group.closure_subset ∘ monoid.closure_subset

theorem closure_subset_iff {R : Type u} [ring R] (s : set R) (t : set R) [is_subring t] : closure s ⊆ t ↔ s ⊆ t :=
  iff.trans (add_group.closure_subset_iff (monoid.closure s) t)
    { mp := set.subset.trans monoid.subset_closure, mpr := monoid.closure_subset }

theorem closure_mono {R : Type u} [ring R] {s : set R} {t : set R} (H : s ⊆ t) : closure s ⊆ closure t :=
  closure_subset (set.subset.trans H subset_closure)

theorem image_closure {R : Type u} [ring R] {S : Type u_1} [ring S] (f : R →+* S) (s : set R) : ⇑f '' closure s = closure (⇑f '' s) := sorry

