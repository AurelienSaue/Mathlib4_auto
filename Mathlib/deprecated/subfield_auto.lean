/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.deprecated.subring
import Mathlib.algebra.group_with_zero.power
import Mathlib.PostPort

universes u_1 l u_2 

namespace Mathlib

class is_subfield {F : Type u_1} [field F] (S : set F) extends is_subring S where
  inv_mem : ∀ {x : F}, x ∈ S → x⁻¹ ∈ S

protected instance is_subfield.field {F : Type u_1} [field F] (S : set F) [is_subfield S] :
    field ↥S :=
  let cr_inst : comm_ring ↥S := subset.comm_ring;
  field.mk comm_ring.add sorry comm_ring.zero sorry sorry comm_ring.neg comm_ring.sub sorry sorry
    comm_ring.mul sorry comm_ring.one sorry sorry sorry sorry sorry
    (fun (x : ↥S) => { val := ↑x⁻¹, property := sorry }) sorry sorry sorry

theorem is_subfield.pow_mem {F : Type u_1} [field F] {a : F} {n : ℤ} {s : set F} [is_subfield s]
    (h : a ∈ s) : a ^ n ∈ s :=
  int.cases_on n (fun (n : ℕ) => is_submonoid.pow_mem h)
    fun (n : ℕ) => is_subfield.inv_mem (is_submonoid.pow_mem h)

protected instance univ.is_subfield {F : Type u_1} [field F] : is_subfield set.univ :=
  is_subfield.mk fun (x : F) (ᾰ : x ∈ set.univ) => trivial

/- note: in the next two declarations, if we let type-class inference figure out the instance
  `ring_hom.is_subring_preimage` then that instance only applies when particular instances of
  `is_add_subgroup _` and `is_submonoid _` are chosen (which are not the default ones).
  If we specify it explicitly, then it doesn't complain. -/

protected instance preimage.is_subfield {F : Type u_1} [field F] {K : Type u_2} [field K]
    (f : F →+* K) (s : set K) [is_subfield s] : is_subfield (⇑f ⁻¹' s) :=
  is_subfield.mk
    fun (a : F) (ha : coe_fn f a ∈ s) =>
      (fun (this : coe_fn f (a⁻¹) ∈ s) => this)
        (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn f (a⁻¹) ∈ s)) (ring_hom.map_inv f a)))
          (is_subfield.inv_mem ha))

protected instance image.is_subfield {F : Type u_1} [field F] {K : Type u_2} [field K] (f : F →+* K)
    (s : set F) [is_subfield s] : is_subfield (⇑f '' s) :=
  is_subfield.mk fun (a : K) (_x : a ∈ ⇑f '' s) => sorry

protected instance range.is_subfield {F : Type u_1} [field F] {K : Type u_2} [field K]
    (f : F →+* K) : is_subfield (set.range ⇑f) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_subfield (set.range ⇑f))) (Eq.symm set.image_univ)))
    (image.is_subfield f set.univ)

namespace field


/-- `field.closure s` is the minimal subfield that includes `s`. -/
def closure {F : Type u_1} [field F] (S : set F) : set F :=
  set_of
    fun (x : F) =>
      ∃ (y : F), ∃ (H : y ∈ ring.closure S), ∃ (z : F), ∃ (H : z ∈ ring.closure S), y / z = x

theorem ring_closure_subset {F : Type u_1} [field F] {S : set F} : ring.closure S ⊆ closure S :=
  fun (x : F) (hx : x ∈ ring.closure S) =>
    Exists.intro x
      (Exists.intro hx (Exists.intro 1 (Exists.intro is_submonoid.one_mem (div_one x))))

protected instance closure.is_submonoid {F : Type u_1} [field F] {S : set F} :
    is_submonoid (closure S) :=
  sorry

protected instance closure.is_subfield {F : Type u_1} [field F] {S : set F} :
    is_subfield (closure S) :=
  sorry

theorem mem_closure {F : Type u_1} [field F] {S : set F} {a : F} (ha : a ∈ S) : a ∈ closure S :=
  ring_closure_subset (ring.mem_closure ha)

theorem subset_closure {F : Type u_1} [field F] {S : set F} : S ⊆ closure S :=
  fun (_x : F) => mem_closure

theorem closure_subset {F : Type u_1} [field F] {S : set F} {T : set F} [is_subfield T]
    (H : S ⊆ T) : closure S ⊆ T :=
  sorry

theorem closure_subset_iff {F : Type u_1} [field F] (s : set F) (t : set F) [is_subfield t] :
    closure s ⊆ t ↔ s ⊆ t :=
  { mp := set.subset.trans subset_closure, mpr := closure_subset }

theorem closure_mono {F : Type u_1} [field F] {s : set F} {t : set F} (H : s ⊆ t) :
    closure s ⊆ closure t :=
  closure_subset (set.subset.trans H subset_closure)

end field


theorem is_subfield_Union_of_directed {F : Type u_1} [field F] {ι : Type u_2} [hι : Nonempty ι]
    (s : ι → set F) [∀ (i : ι), is_subfield (s i)]
    (directed : ∀ (i j : ι), ∃ (k : ι), s i ⊆ s k ∧ s j ⊆ s k) :
    is_subfield (set.Union fun (i : ι) => s i) :=
  sorry

protected instance is_subfield.inter {F : Type u_1} [field F] (S₁ : set F) (S₂ : set F)
    [is_subfield S₁] [is_subfield S₂] : is_subfield (S₁ ∩ S₂) :=
  is_subfield.mk
    fun (x : F) (hx : x ∈ S₁ ∩ S₂) =>
      { left := is_subfield.inv_mem (and.left hx), right := is_subfield.inv_mem (and.right hx) }

protected instance is_subfield.Inter {F : Type u_1} [field F] {ι : Sort u_2} (S : ι → set F)
    [h : ∀ (y : ι), is_subfield (S y)] : is_subfield (set.Inter S) :=
  is_subfield.mk
    fun (x : F) (hx : x ∈ set.Inter S) =>
      iff.mpr set.mem_Inter fun (y : ι) => is_subfield.inv_mem (iff.mp set.mem_Inter hx y)

end Mathlib