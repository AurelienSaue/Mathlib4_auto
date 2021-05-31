/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, E. W. Ayers
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.over
import Mathlib.category_theory.limits.shapes.finite_limits
import Mathlib.category_theory.yoneda
import Mathlib.order.complete_lattice
import Mathlib.data.set.lattice
import Mathlib.PostPort

universes v u l 

namespace Mathlib

/-!
# Theory of sieves

- For an object `X` of a category `C`, a `sieve X` is a set of morphisms to `X`
  which is closed under left-composition.
- The complete lattice structure on sieves is given, as well as the Galois insertion
  given by downward-closing.
- A `sieve X` (functorially) induces a presheaf on `C` together with a monomorphism to
  the yoneda embedding of `X`.

## Tags

sieve, pullback
-/

namespace category_theory


/-- A set of arrows all with codomain `X`. -/
def presieve {C : Type u} [category C] (X : C) :=
  {Y : C} → set (Y ⟶ X)

namespace presieve


protected instance inhabited {C : Type u} [category C] {X : C} : Inhabited (presieve X) :=
  { default := ⊤ }

/--
Given a set of arrows `S` all with codomain `X`, and a set of arrows with codomain `Y` for each
`f : Y ⟶ X` in `S`, produce a set of arrows with codomain `X`:
`{ g ≫ f | (f : Y ⟶ X) ∈ S, (g : Z ⟶ Y) ∈ R f }`.
-/
def bind {C : Type u} [category C] {X : C} (S : presieve X) (R : {Y : C} → {f : Y ⟶ X} → S f → presieve Y) : presieve X :=
  fun (Z : C) (h : Z ⟶ X) => ∃ (Y : C), ∃ (g : Z ⟶ Y), ∃ (f : Y ⟶ X), ∃ (H : S f), R H g ∧ g ≫ f = h

@[simp] theorem bind_comp {C : Type u} [category C] {X : C} {Y : C} {Z : C} (f : Y ⟶ X) {S : presieve X} {R : {Y : C} → {f : Y ⟶ X} → S f → presieve Y} {g : Z ⟶ Y} (h₁ : S f) (h₂ : R h₁ g) : bind S R (g ≫ f) :=
  Exists.intro Y (Exists.intro g (Exists.intro f (Exists.intro h₁ { left := h₂, right := rfl })))

/-- The singleton presieve.  -/
-- Note we can't make this into `has_singleton` because of the out-param.

structure singleton {C : Type u} [category C] {X : C} {Y : C} (f : Y ⟶ X) : presieve X
where

@[simp] theorem singleton_eq_iff_domain {C : Type u} [category C] {X : C} {Y : C} (f : Y ⟶ X) (g : Y ⟶ X) : singleton f g ↔ f = g := sorry

theorem singleton_self {C : Type u} [category C] {X : C} {Y : C} (f : Y ⟶ X) : singleton f f :=
  singleton.mk

end presieve


/--
For an object `X` of a category `C`, a `sieve X` is a set of morphisms to `X` which is closed under
left-composition.
-/
structure sieve {C : Type u} [category C] (X : C) 
where
  arrows : presieve X
  downward_closed' : ∀ {Y Z : C} {f : Y ⟶ X}, arrows f → ∀ (g : Z ⟶ Y), arrows (g ≫ f)

namespace sieve


protected instance has_coe_to_fun {C : Type u} [category C] {X : C} : has_coe_to_fun (sieve X) :=
  has_coe_to_fun.mk (fun (x : sieve X) => presieve X) arrows

@[simp] theorem downward_closed {C : Type u} [category C] {X : C} {Y : C} {Z : C} (S : sieve X) {f : Y ⟶ X} (hf : coe_fn S Y f) (g : Z ⟶ Y) : coe_fn S Z (g ≫ f) :=
  downward_closed' S hf g

theorem arrows_ext {C : Type u} [category C] {X : C} {R : sieve X} {S : sieve X} : arrows R = arrows S → R = S := sorry

protected theorem ext {C : Type u} [category C] {X : C} {R : sieve X} {S : sieve X} (h : ∀ {Y : C} (f : Y ⟶ X), coe_fn R Y f ↔ coe_fn S Y f) : R = S :=
  arrows_ext (funext fun (x : C) => funext fun (f : x ⟶ X) => propext (h f))

protected theorem ext_iff {C : Type u} [category C] {X : C} {R : sieve X} {S : sieve X} : R = S ↔ ∀ {Y : C} (f : Y ⟶ X), coe_fn R Y f ↔ coe_fn S Y f :=
  { mp := fun (h : R = S) (Y : C) (f : Y ⟶ X) => h ▸ iff.rfl, mpr := sieve.ext }

/-- The supremum of a collection of sieves: the union of them all. -/
protected def Sup {C : Type u} [category C] {X : C} (𝒮 : set (sieve X)) : sieve X :=
  mk (fun (Y : C) => set_of fun (f : Y ⟶ X) => ∃ (S : sieve X), ∃ (H : S ∈ 𝒮), arrows S f) sorry

/-- The infimum of a collection of sieves: the intersection of them all. -/
protected def Inf {C : Type u} [category C] {X : C} (𝒮 : set (sieve X)) : sieve X :=
  mk (fun (Y : C) => set_of fun (f : Y ⟶ X) => ∀ (S : sieve X), S ∈ 𝒮 → arrows S f) sorry

/-- The union of two sieves is a sieve. -/
protected def union {C : Type u} [category C] {X : C} (S : sieve X) (R : sieve X) : sieve X :=
  mk (fun (Y : C) (f : Y ⟶ X) => coe_fn S Y f ∨ coe_fn R Y f) sorry

/-- The intersection of two sieves is a sieve. -/
protected def inter {C : Type u} [category C] {X : C} (S : sieve X) (R : sieve X) : sieve X :=
  mk (fun (Y : C) (f : Y ⟶ X) => coe_fn S Y f ∧ coe_fn R Y f) sorry

/--
Sieves on an object `X` form a complete lattice.
We generate this directly rather than using the galois insertion for nicer definitional properties.
-/
protected instance complete_lattice {C : Type u} [category C] {X : C} : complete_lattice (sieve X) :=
  complete_lattice.mk sieve.union (fun (S R : sieve X) => ∀ {Y : C} (f : Y ⟶ X), coe_fn S Y f → coe_fn R Y f)
    (bounded_lattice.lt._default fun (S R : sieve X) => ∀ {Y : C} (f : Y ⟶ X), coe_fn S Y f → coe_fn R Y f) sorry sorry
    sorry sorry sorry sorry sieve.inter sorry sorry sorry (mk (fun (_x : C) => set.univ) sorry) sorry
    (mk (fun (_x : C) => ∅) sorry) sorry sieve.Sup sieve.Inf sorry sorry sorry sorry

/-- The maximal sieve always exists. -/
protected instance sieve_inhabited {C : Type u} [category C] {X : C} : Inhabited (sieve X) :=
  { default := ⊤ }

@[simp] theorem Inf_apply {C : Type u} [category C] {X : C} {Ss : set (sieve X)} {Y : C} (f : Y ⟶ X) : coe_fn (Inf Ss) Y f ↔ ∀ (S : sieve X), S ∈ Ss → coe_fn S Y f :=
  iff.rfl

@[simp] theorem Sup_apply {C : Type u} [category C] {X : C} {Ss : set (sieve X)} {Y : C} (f : Y ⟶ X) : coe_fn (Sup Ss) Y f ↔ ∃ (S : sieve X), ∃ (H : S ∈ Ss), coe_fn S Y f :=
  iff.rfl

@[simp] theorem inter_apply {C : Type u} [category C] {X : C} {R : sieve X} {S : sieve X} {Y : C} (f : Y ⟶ X) : coe_fn (R ⊓ S) Y f ↔ coe_fn R Y f ∧ coe_fn S Y f :=
  iff.rfl

@[simp] theorem union_apply {C : Type u} [category C] {X : C} {R : sieve X} {S : sieve X} {Y : C} (f : Y ⟶ X) : coe_fn (R ⊔ S) Y f ↔ coe_fn R Y f ∨ coe_fn S Y f :=
  iff.rfl

@[simp] theorem top_apply {C : Type u} [category C] {X : C} {Y : C} (f : Y ⟶ X) : coe_fn ⊤ Y f :=
  trivial

/-- Generate the smallest sieve containing the given set of arrows. -/
@[simp] theorem generate_apply {C : Type u} [category C] {X : C} (R : presieve X) (Z : C) (f : Z ⟶ X) : coe_fn (generate R) Z f = ∃ (Y : C), ∃ (h : Z ⟶ Y), ∃ (g : Y ⟶ X), R g ∧ h ≫ g = f :=
  Eq.refl (coe_fn (generate R) Z f)

/--
Given a presieve on `X`, and a sieve on each domain of an arrow in the presieve, we can bind to
produce a sieve on `X`.
-/
@[simp] theorem bind_apply {C : Type u} [category C] {X : C} (S : presieve X) (R : {Y : C} → {f : Y ⟶ X} → S f → sieve Y) : ⇑(bind S R) = presieve.bind S fun (Y : C) (f : Y ⟶ X) (h : S f) => ⇑(R h) :=
  Eq.refl ⇑(bind S R)

theorem sets_iff_generate {C : Type u} [category C] {X : C} (R : presieve X) (S : sieve X) : generate R ≤ S ↔ R ≤ ⇑S := sorry

/-- Show that there is a galois insertion (generate, set_over). -/
def gi_generate {C : Type u} [category C] {X : C} : galois_insertion generate arrows :=
  galois_insertion.mk (fun (𝒢 : presieve X) (_x : arrows (generate 𝒢) ≤ 𝒢) => generate 𝒢) sets_iff_generate sorry sorry

theorem le_generate {C : Type u} [category C] {X : C} (R : presieve X) : R ≤ ⇑(generate R) :=
  galois_connection.le_u_l (galois_insertion.gc gi_generate) R

/-- If the identity arrow is in a sieve, the sieve is maximal. -/
theorem id_mem_iff_eq_top {C : Type u} [category C] {X : C} {S : sieve X} : coe_fn S X 𝟙 ↔ S = ⊤ := sorry

/-- If an arrow set contains a split epi, it generates the maximal sieve. -/
theorem generate_of_contains_split_epi {C : Type u} [category C] {X : C} {Y : C} {R : presieve X} (f : Y ⟶ X) [split_epi f] (hf : R f) : generate R = ⊤ := sorry

@[simp] theorem generate_of_singleton_split_epi {C : Type u} [category C] {X : C} {Y : C} (f : Y ⟶ X) [split_epi f] : generate (presieve.singleton f) = ⊤ :=
  generate_of_contains_split_epi f (presieve.singleton_self f)

@[simp] theorem generate_top {C : Type u} [category C] {X : C} : generate ⊤ = ⊤ :=
  generate_of_contains_split_epi 𝟙 True.intro

/-- Given a morphism `h : Y ⟶ X`, send a sieve S on X to a sieve on Y
    as the inverse image of S with `_ ≫ h`.
    That is, `sieve.pullback S h := (≫ h) '⁻¹ S`. -/
def pullback {C : Type u} [category C] {X : C} {Y : C} (h : Y ⟶ X) (S : sieve X) : sieve Y :=
  mk (fun (Y_1 : C) (sl : Y_1 ⟶ Y) => coe_fn S Y_1 (sl ≫ h)) sorry

@[simp] theorem pullback_id {C : Type u} [category C] {X : C} {S : sieve X} : pullback 𝟙 S = S := sorry

@[simp] theorem pullback_top {C : Type u} [category C] {X : C} {Y : C} {f : Y ⟶ X} : pullback f ⊤ = ⊤ :=
  top_unique fun (_x : C) (g : _x ⟶ Y) => id

theorem pullback_comp {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : Y ⟶ X} {g : Z ⟶ Y} (S : sieve X) : pullback (g ≫ f) S = pullback g (pullback f S) := sorry

@[simp] theorem pullback_inter {C : Type u} [category C] {X : C} {Y : C} {f : Y ⟶ X} (S : sieve X) (R : sieve X) : pullback f (S ⊓ R) = pullback f S ⊓ pullback f R := sorry

theorem pullback_eq_top_iff_mem {C : Type u} [category C] {X : C} {Y : C} {S : sieve X} (f : Y ⟶ X) : coe_fn S Y f ↔ pullback f S = ⊤ := sorry

theorem pullback_eq_top_of_mem {C : Type u} [category C] {X : C} {Y : C} (S : sieve X) {f : Y ⟶ X} : coe_fn S Y f → pullback f S = ⊤ :=
  iff.mp (pullback_eq_top_iff_mem f)

/--
Push a sieve `R` on `Y` forward along an arrow `f : Y ⟶ X`: `gf : Z ⟶ X` is in the sieve if `gf`
factors through some `g : Z ⟶ Y` which is in `R`.
-/
@[simp] theorem pushforward_apply {C : Type u} [category C] {X : C} {Y : C} (f : Y ⟶ X) (R : sieve Y) (Z : C) (gf : Z ⟶ X) : coe_fn (pushforward f R) Z gf = ∃ (g : Z ⟶ Y), g ≫ f = gf ∧ coe_fn R Z g :=
  Eq.refl (coe_fn (pushforward f R) Z gf)

theorem pushforward_apply_comp {C : Type u} [category C] {X : C} {Y : C} {R : sieve Y} {Z : C} {g : Z ⟶ Y} (hg : coe_fn R Z g) (f : Y ⟶ X) : coe_fn (pushforward f R) Z (g ≫ f) :=
  Exists.intro g { left := rfl, right := hg }

theorem pushforward_comp {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : Y ⟶ X} {g : Z ⟶ Y} (R : sieve Z) : pushforward (g ≫ f) R = pushforward f (pushforward g R) := sorry

theorem galois_connection {C : Type u} [category C] {X : C} {Y : C} (f : Y ⟶ X) : galois_connection (pushforward f) (pullback f) := sorry

theorem pullback_monotone {C : Type u} [category C] {X : C} {Y : C} (f : Y ⟶ X) : monotone (pullback f) :=
  galois_connection.monotone_u (galois_connection f)

theorem pushforward_monotone {C : Type u} [category C] {X : C} {Y : C} (f : Y ⟶ X) : monotone (pushforward f) :=
  galois_connection.monotone_l (galois_connection f)

theorem le_pushforward_pullback {C : Type u} [category C] {X : C} {Y : C} (f : Y ⟶ X) (R : sieve Y) : R ≤ pullback f (pushforward f R) :=
  galois_connection.le_u_l (galois_connection f) R

theorem pullback_pushforward_le {C : Type u} [category C] {X : C} {Y : C} (f : Y ⟶ X) (R : sieve X) : pushforward f (pullback f R) ≤ R :=
  galois_connection.l_u_le (galois_connection f) R

theorem pushforward_union {C : Type u} [category C] {X : C} {Y : C} {f : Y ⟶ X} (S : sieve Y) (R : sieve Y) : pushforward f (S ⊔ R) = pushforward f S ⊔ pushforward f R :=
  galois_connection.l_sup (galois_connection f)

theorem pushforward_le_bind_of_mem {C : Type u} [category C] {X : C} {Y : C} (S : presieve X) (R : {Y : C} → {f : Y ⟶ X} → S f → sieve Y) (f : Y ⟶ X) (h : S f) : pushforward f (R h) ≤ bind S R := sorry

theorem le_pullback_bind {C : Type u} [category C] {X : C} {Y : C} (S : presieve X) (R : {Y : C} → {f : Y ⟶ X} → S f → sieve Y) (f : Y ⟶ X) (h : S f) : R h ≤ pullback f (bind S R) :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (R h ≤ pullback f (bind S R))) (Eq.symm (propext (galois_connection f (R h) (bind S R))))))
    (pushforward_le_bind_of_mem (fun {Y : C} (f : Y ⟶ X) => S f) R f h)

/-- If `f` is a monomorphism, the pushforward-pullback adjunction on sieves is coreflective. -/
def galois_coinsertion_of_mono {C : Type u} [category C] {X : C} {Y : C} (f : Y ⟶ X) [mono f] : galois_coinsertion (pushforward f) (pullback f) :=
  galois_connection.to_galois_coinsertion (galois_connection f) sorry

/-- If `f` is a split epi, the pushforward-pullback adjunction on sieves is reflective. -/
def galois_insertion_of_split_epi {C : Type u} [category C] {X : C} {Y : C} (f : Y ⟶ X) [split_epi f] : galois_insertion (pushforward f) (pullback f) :=
  galois_connection.to_galois_insertion (galois_connection f) sorry

/-- A sieve induces a presheaf. -/
@[simp] theorem functor_obj {C : Type u} [category C] {X : C} (S : sieve X) (Y : Cᵒᵖ) : functor.obj (functor S) Y = Subtype fun (g : opposite.unop Y ⟶ X) => coe_fn S (opposite.unop Y) g :=
  Eq.refl (functor.obj (functor S) Y)

/--
If a sieve S is contained in a sieve T, then we have a morphism of presheaves on their induced
presheaves.
-/
def nat_trans_of_le {C : Type u} [category C] {X : C} {S : sieve X} {T : sieve X} (h : S ≤ T) : functor S ⟶ functor T :=
  nat_trans.mk fun (Y : Cᵒᵖ) (f : functor.obj (functor S) Y) => { val := subtype.val f, property := sorry }

/-- The natural inclusion from the functor induced by a sieve to the yoneda embedding. -/
@[simp] theorem functor_inclusion_app {C : Type u} [category C] {X : C} (S : sieve X) (Y : Cᵒᵖ) (f : functor.obj (functor S) Y) : nat_trans.app (functor_inclusion S) Y f = subtype.val f :=
  Eq.refl (nat_trans.app (functor_inclusion S) Y f)

theorem nat_trans_of_le_comm {C : Type u} [category C] {X : C} {S : sieve X} {T : sieve X} (h : S ≤ T) : nat_trans_of_le h ≫ functor_inclusion T = functor_inclusion S :=
  rfl

/-- The presheaf induced by a sieve is a subobject of the yoneda embedding. -/
protected instance functor_inclusion_is_mono {C : Type u} [category C] {X : C} {S : sieve X} : mono (functor_inclusion S) :=
  mono.mk
    fun (Z : Cᵒᵖ ⥤ Type v) (f g : Z ⟶ functor S) (h : f ≫ functor_inclusion S = g ≫ functor_inclusion S) =>
      nat_trans.ext f g
        (funext fun (Y : Cᵒᵖ) => funext fun (y : functor.obj Z Y) => subtype.ext (congr_fun (nat_trans.congr_app h Y) y))

/--
A natural transformation to a representable functor induces a sieve. This is the left inverse of
`functor_inclusion`, shown in `sieve_of_functor_inclusion`.
-/
-- TODO: Show that when `f` is mono, this is right inverse to `functor_inclusion` up to isomorphism.

@[simp] theorem sieve_of_subfunctor_apply {C : Type u} [category C] {X : C} {R : Cᵒᵖ ⥤ Type v} (f : R ⟶ functor.obj yoneda X) (Y : C) (g : Y ⟶ X) : coe_fn (sieve_of_subfunctor f) Y g = ∃ (t : functor.obj R (opposite.op Y)), nat_trans.app f (opposite.op Y) t = g :=
  Eq.refl (coe_fn (sieve_of_subfunctor f) Y g)

theorem sieve_of_subfunctor_functor_inclusion {C : Type u} [category C] {X : C} {S : sieve X} : sieve_of_subfunctor (functor_inclusion S) = S := sorry

protected instance functor_inclusion_top_is_iso {C : Type u} [category C] {X : C} : is_iso (functor_inclusion ⊤) :=
  is_iso.mk
    (nat_trans.mk fun (Y : Cᵒᵖ) (a : functor.obj (functor.obj yoneda X) Y) => { val := a, property := True.intro })

