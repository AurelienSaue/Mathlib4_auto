/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.limits.shapes.terminal
import Mathlib.category_theory.limits.shapes.binary_products
import Mathlib.category_theory.limits.shapes.products
import Mathlib.category_theory.limits.shapes.images
import Mathlib.PostPort

universes v u l u_1 v' u' 

namespace Mathlib

/-!
# Zero morphisms and zero objects

A category "has zero morphisms" if there is a designated "zero morphism" in each morphism space,
and compositions of zero morphisms with anything give the zero morphism. (Notice this is extra
structure, not merely a property.)

A category "has a zero object" if it has an object which is both initial and terminal. Having a
zero object provides zero morphisms, as the unique morphisms factoring through the zero object.

## References

* https://en.wikipedia.org/wiki/Zero_morphism
* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]
-/

namespace category_theory.limits


/-- A category "has zero morphisms" if there is a designated "zero morphism" in each morphism space,
and compositions of zero morphisms with anything give the zero morphism. -/
class has_zero_morphisms (C : Type u) [category C] where
  has_zero : (X Y : C) → HasZero (X ⟶ Y)
  comp_zero' :
    autoParam (∀ {X Y : C} (f : X ⟶ Y), C → f ≫ 0 = 0)
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
        (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  zero_comp' :
    autoParam (C → ∀ {Y Z : C} (f : Y ⟶ Z), 0 ≫ f = 0)
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
        (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

theorem has_zero_morphisms.comp_zero {C : Type u} [category C] [c : has_zero_morphisms C] {X : C}
    {Y : C} (f : X ⟶ Y) (Z : C) : f ≫ 0 = 0 :=
  sorry

theorem has_zero_morphisms.zero_comp {C : Type u} [category C] [c : has_zero_morphisms C] (X : C)
    {Y : C} {Z : C} (f : Y ⟶ Z) : 0 ≫ f = 0 :=
  sorry

@[simp] theorem comp_zero {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C}
    {f : X ⟶ Y} {Z : C} : f ≫ 0 = 0 :=
  has_zero_morphisms.comp_zero f Z

@[simp] theorem zero_comp {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C} {Z : C}
    {f : Y ⟶ Z} : 0 ≫ f = 0 :=
  has_zero_morphisms.zero_comp X f

protected instance has_zero_morphisms_pempty : has_zero_morphisms (discrete pempty) :=
  has_zero_morphisms.mk

protected instance has_zero_morphisms_punit : has_zero_morphisms (discrete PUnit) :=
  has_zero_morphisms.mk

namespace has_zero_morphisms


/-- This lemma will be immediately superseded by `ext`, below. -/
/--
If you're tempted to use this lemma "in the wild", you should probably
carefully consider whether you've made a mistake in allowing two
instances of `has_zero_morphisms` to exist at all.

See, particularly, the note on `zero_morphisms_of_zero_object` below.
-/
theorem ext {C : Type u} [category C] (I : has_zero_morphisms C) (J : has_zero_morphisms C) :
    I = J :=
  sorry

protected instance subsingleton {C : Type u} [category C] : subsingleton (has_zero_morphisms C) :=
  subsingleton.intro ext

end has_zero_morphisms


theorem zero_of_comp_mono {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C} {Z : C}
    {f : X ⟶ Y} (g : Y ⟶ Z) [mono g] (h : f ≫ g = 0) : f = 0 :=
  eq.mp (Eq._oldrec (Eq.refl (f ≫ g = 0 ≫ g)) (propext (cancel_mono g)))
    (eq.mp (Eq._oldrec (Eq.refl (f ≫ g = 0)) (Eq.symm zero_comp)) h)

theorem zero_of_epi_comp {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C} {Z : C}
    (f : X ⟶ Y) {g : Y ⟶ Z} [epi f] (h : f ≫ g = 0) : g = 0 :=
  eq.mp (Eq._oldrec (Eq.refl (f ≫ g = f ≫ 0)) (propext (cancel_epi f)))
    (eq.mp (Eq._oldrec (Eq.refl (f ≫ g = 0)) (Eq.symm comp_zero)) h)

theorem eq_zero_of_image_eq_zero {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C}
    {f : X ⟶ Y} [has_image f] (w : image.ι f = 0) : f = 0 :=
  sorry

theorem nonzero_image_of_nonzero {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C}
    {f : X ⟶ Y} [has_image f] (w : f ≠ 0) : image.ι f ≠ 0 :=
  fun (h : image.ι f = 0) => w (eq_zero_of_image_eq_zero h)

theorem equivalence_preserves_zero_morphisms {C : Type u} [category C] (D : Type u') [category D]
    [has_zero_morphisms C] [has_zero_morphisms D] (F : C ≌ D) (X : C) (Y : C) :
    functor.map (equivalence.functor F) 0 = 0 :=
  sorry

@[simp] theorem is_equivalence_preserves_zero_morphisms {C : Type u} [category C] (D : Type u')
    [category D] [has_zero_morphisms C] [has_zero_morphisms D] (F : C ⥤ D) [is_equivalence F]
    (X : C) (Y : C) : functor.map F 0 = 0 :=
  sorry

/-- A category "has a zero object" if it has an object which is both initial and terminal. -/
class has_zero_object (C : Type u) [category C] where
  zero : C
  unique_to : (X : C) → unique (zero ⟶ X)
  unique_from : (X : C) → unique (X ⟶ zero)

protected instance has_zero_object_punit : has_zero_object (discrete PUnit) :=
  has_zero_object.mk PUnit.unit
    (fun (X : discrete PUnit) => punit.cases_on X (unique.mk sorry sorry))
    fun (X : discrete PUnit) => punit.cases_on X (unique.mk sorry sorry)

namespace has_zero_object


/--
Construct a `has_zero C` for a category with a zero object.
This can not be a global instance as it will trigger for every `has_zero C` typeclass search.
-/
protected def has_zero {C : Type u} [category C] [has_zero_object C] : HasZero C := { zero := zero }

theorem to_zero_ext {C : Type u} [category C] [has_zero_object C] {X : C} (f : X ⟶ 0) (g : X ⟶ 0) :
    f = g :=
  eq.mpr (id (Eq._oldrec (Eq.refl (f = g)) (unique.uniq (unique_from X) f)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (Inhabited.default = g)) (unique.uniq (unique_from X) g)))
      (Eq.refl Inhabited.default))

theorem from_zero_ext {C : Type u} [category C] [has_zero_object C] {X : C} (f : 0 ⟶ X)
    (g : 0 ⟶ X) : f = g :=
  eq.mpr (id (Eq._oldrec (Eq.refl (f = g)) (unique.uniq (unique_to X) f)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (Inhabited.default = g)) (unique.uniq (unique_to X) g)))
      (Eq.refl Inhabited.default))

protected instance category_theory.iso.subsingleton {C : Type u} [category C] [has_zero_object C]
    (X : C) : subsingleton (X ≅ 0) :=
  subsingleton.intro fun (a b : X ≅ 0) => iso.ext (of_as_true trivial)

protected instance category_theory.mono {C : Type u} [category C] [has_zero_object C] {X : C}
    (f : 0 ⟶ X) : mono f :=
  mono.mk fun (Z : C) (g h : Z ⟶ 0) (w : g ≫ f = h ≫ f) => to_zero_ext g h

protected instance category_theory.epi {C : Type u} [category C] [has_zero_object C] {X : C}
    (f : X ⟶ 0) : epi f :=
  epi.mk fun (Z : C) (g h : 0 ⟶ Z) (w : f ≫ g = f ≫ h) => from_zero_ext g h

/-- A category with a zero object has zero morphisms.

    It is rarely a good idea to use this. Many categories that have a zero object have zero
    morphisms for some other reason, for example from additivity. Library code that uses
    `zero_morphisms_of_zero_object` will then be incompatible with these categories because
    the `has_zero_morphisms` instances will not be definitionally equal. For this reason library
    code should generally ask for an instance of `has_zero_morphisms` separately, even if it already
    asks for an instance of `has_zero_objects`. -/
def zero_morphisms_of_zero_object {C : Type u} [category C] [has_zero_object C] :
    has_zero_morphisms C :=
  has_zero_morphisms.mk

/-- A zero object is in particular initial. -/
theorem has_initial {C : Type u} [category C] [has_zero_object C] : has_initial C :=
  has_initial_of_unique 0

/-- A zero object is in particular terminal. -/
theorem has_terminal {C : Type u} [category C] [has_zero_object C] : has_terminal C :=
  has_terminal_of_unique 0

end has_zero_object


@[simp] theorem id_zero {C : Type u} [category C] [has_zero_object C] [has_zero_morphisms C] :
    𝟙 = 0 :=
  has_zero_object.from_zero_ext 𝟙 0

/--  An arrow ending in the zero object is zero -/
-- This can't be a `simp` lemma because the left hand side would be a metavariable.

theorem zero_of_to_zero {C : Type u} [category C] [has_zero_object C] [has_zero_morphisms C] {X : C}
    (f : X ⟶ 0) : f = 0 :=
  has_zero_object.to_zero_ext f 0

theorem zero_of_target_iso_zero {C : Type u} [category C] [has_zero_object C] [has_zero_morphisms C]
    {X : C} {Y : C} (f : X ⟶ Y) (i : Y ≅ 0) : f = 0 :=
  sorry

/-- An arrow starting at the zero object is zero -/
theorem zero_of_from_zero {C : Type u} [category C] [has_zero_object C] [has_zero_morphisms C]
    {X : C} (f : 0 ⟶ X) : f = 0 :=
  has_zero_object.from_zero_ext f 0

theorem zero_of_source_iso_zero {C : Type u} [category C] [has_zero_object C] [has_zero_morphisms C]
    {X : C} {Y : C} (f : X ⟶ Y) (i : X ≅ 0) : f = 0 :=
  sorry

theorem mono_of_source_iso_zero {C : Type u} [category C] [has_zero_object C] [has_zero_morphisms C]
    {X : C} {Y : C} (f : X ⟶ Y) (i : X ≅ 0) : mono f :=
  sorry

theorem epi_of_target_iso_zero {C : Type u} [category C] [has_zero_object C] [has_zero_morphisms C]
    {X : C} {Y : C} (f : X ⟶ Y) (i : Y ≅ 0) : epi f :=
  sorry

/--
An object `X` has `𝟙 X = 0` if and only if it is isomorphic to the zero object.

Because `X ≅ 0` contains data (even if a subsingleton), we express this `↔` as an `≃`.
-/
def id_zero_equiv_iso_zero {C : Type u} [category C] [has_zero_object C] [has_zero_morphisms C]
    (X : C) : 𝟙 = 0 ≃ (X ≅ 0) :=
  equiv.mk (fun (h : 𝟙 = 0) => iso.mk 0 0) sorry sorry sorry

@[simp] theorem id_zero_equiv_iso_zero_apply_hom {C : Type u} [category C] [has_zero_object C]
    [has_zero_morphisms C] (X : C) (h : 𝟙 = 0) :
    iso.hom (coe_fn (id_zero_equiv_iso_zero X) h) = 0 :=
  rfl

@[simp] theorem id_zero_equiv_iso_zero_apply_inv {C : Type u} [category C] [has_zero_object C]
    [has_zero_morphisms C] (X : C) (h : 𝟙 = 0) :
    iso.inv (coe_fn (id_zero_equiv_iso_zero X) h) = 0 :=
  rfl

/--
A zero morphism `0 : X ⟶ Y` is an isomorphism if and only if
the identities on both `X` and `Y` are zero.
-/
def is_iso_zero_equiv {C : Type u} [category C] [has_zero_morphisms C] (X : C) (Y : C) :
    is_iso 0 ≃ 𝟙 = 0 ∧ 𝟙 = 0 :=
  equiv.mk sorry (fun (h : 𝟙 = 0 ∧ 𝟙 = 0) => is_iso.mk 0) sorry sorry

/--
A zero morphism `0 : X ⟶ X` is an isomorphism if and only if
the identity on `X` is zero.
-/
def is_iso_zero_self_equiv {C : Type u} [category C] [has_zero_morphisms C] (X : C) :
    is_iso 0 ≃ 𝟙 = 0 :=
  eq.mpr sorry (eq.mp sorry (is_iso_zero_equiv X X))

/--
A zero morphism `0 : X ⟶ Y` is an isomorphism if and only if
`X` and `Y` are isomorphic to the zero object.
-/
def is_iso_zero_equiv_iso_zero {C : Type u} [category C] [has_zero_morphisms C] [has_zero_object C]
    (X : C) (Y : C) : is_iso 0 ≃ (X ≅ 0) × (Y ≅ 0) :=
  equiv.trans (is_iso_zero_equiv X Y)
    (equiv.symm
      (equiv.mk sorry
        (fun (ᾰ : 𝟙 = 0 ∧ 𝟙 = 0) =>
          and.dcases_on ᾰ
            fun (hX : 𝟙 = 0) (hY : 𝟙 = 0) =>
              (coe_fn (id_zero_equiv_iso_zero X) hX, coe_fn (id_zero_equiv_iso_zero Y) hY))
        sorry sorry))

/--
A zero morphism `0 : X ⟶ X` is an isomorphism if and only if
`X` is isomorphic to the zero object.
-/
def is_iso_zero_self_equiv_iso_zero {C : Type u} [category C] [has_zero_morphisms C]
    [has_zero_object C] (X : C) : is_iso 0 ≃ (X ≅ 0) :=
  equiv.trans (is_iso_zero_equiv_iso_zero X X) subsingleton_prod_self_equiv

/-- If there are zero morphisms, any initial object is a zero object. -/
protected instance has_zero_object_of_has_initial_object {C : Type u} [category C]
    [has_zero_morphisms C] [has_initial C] : has_zero_object C :=
  has_zero_object.mk (⊥_C) (fun (X : C) => unique.mk { default := 0 } sorry)
    fun (X : C) => unique.mk { default := 0 } sorry

/-- If there are zero morphisms, any terminal object is a zero object. -/
protected instance has_zero_object_of_has_terminal_object {C : Type u} [category C]
    [has_zero_morphisms C] [has_terminal C] : has_zero_object C :=
  has_zero_object.mk (⊤_C) (fun (X : C) => unique.mk { default := 0 } sorry)
    fun (X : C) => unique.mk { default := 0 } sorry

theorem image_ι_comp_eq_zero {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C}
    {Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} [has_image f] [epi (factor_thru_image f)] (h : f ≫ g = 0) :
    image.ι f ≫ g = 0 :=
  sorry

/--
The zero morphism has a `mono_factorisation` through the zero object.
-/
@[simp] theorem mono_factorisation_zero_e {C : Type u} [category C] [has_zero_morphisms C]
    [has_zero_object C] (X : C) (Y : C) : mono_factorisation.e (mono_factorisation_zero X Y) = 0 :=
  Eq.refl (mono_factorisation.e (mono_factorisation_zero X Y))

/--
The factorisation through the zero object is an image factorisation.
-/
def image_factorisation_zero {C : Type u} [category C] [has_zero_morphisms C] [has_zero_object C]
    (X : C) (Y : C) : image_factorisation 0 :=
  image_factorisation.mk (mono_factorisation_zero X Y)
    (is_image.mk fun (F' : mono_factorisation 0) => 0)

protected instance has_image_zero {C : Type u} [category C] [has_zero_morphisms C]
    [has_zero_object C] {X : C} {Y : C} : has_image 0 :=
  has_image.mk (image_factorisation_zero X Y)

/-- The image of a zero morphism is the zero object. -/
def image_zero {C : Type u} [category C] [has_zero_morphisms C] [has_zero_object C] {X : C}
    {Y : C} : image 0 ≅ 0 :=
  is_image.iso_ext (image.is_image 0) (image_factorisation.is_image (image_factorisation_zero X Y))

/-- The image of a morphism which is equal to zero is the zero object. -/
def image_zero' {C : Type u} [category C] [has_zero_morphisms C] [has_zero_object C] {X : C} {Y : C}
    {f : X ⟶ Y} (h : f = 0) [has_image f] : image f ≅ 0 :=
  image.eq_to_iso h ≪≫ image_zero

@[simp] theorem image.ι_zero {C : Type u} [category C] [has_zero_morphisms C] [has_zero_object C]
    {X : C} {Y : C} [has_image 0] : image.ι 0 = 0 :=
  sorry

/--
If we know `f = 0`,
it requires a little work to conclude `image.ι f = 0`,
because `f = g` only implies `image f ≅ image g`.
-/
@[simp] theorem image.ι_zero' {C : Type u} [category C] [has_zero_morphisms C] [has_zero_object C]
    [has_equalizers C] {X : C} {Y : C} {f : X ⟶ Y} (h : f = 0) [has_image f] : image.ι f = 0 :=
  sorry

/-- In the presence of zero morphisms, coprojections into a coproduct are (split) monomorphisms. -/
protected instance split_mono_sigma_ι {C : Type u} [category C] {β : Type v} [DecidableEq β]
    [has_zero_morphisms C] (f : β → C) [has_colimit (discrete.functor f)] (b : β) :
    split_mono (sigma.ι f b) :=
  split_mono.mk
    (sigma.desc
      fun (b' : β) =>
        dite (b' = b) (fun (h : b' = b) => eq_to_hom (congr_arg f h)) fun (h : ¬b' = b) => 0)

/-- In the presence of zero morphisms, projections into a product are (split) epimorphisms. -/
protected instance split_epi_pi_π {C : Type u} [category C] {β : Type v} [DecidableEq β]
    [has_zero_morphisms C] (f : β → C) [has_limit (discrete.functor f)] (b : β) :
    split_epi (pi.π f b) :=
  split_epi.mk
    (pi.lift
      fun (b' : β) =>
        dite (b = b') (fun (h : b = b') => eq_to_hom (congr_arg f h)) fun (h : ¬b = b') => 0)

/-- In the presence of zero morphisms, coprojections into a coproduct are (split) monomorphisms. -/
protected instance split_mono_coprod_inl {C : Type u} [category C] [has_zero_morphisms C] {X : C}
    {Y : C} [has_colimit (pair X Y)] : split_mono coprod.inl :=
  split_mono.mk (coprod.desc 𝟙 0)

/-- In the presence of zero morphisms, coprojections into a coproduct are (split) monomorphisms. -/
protected instance split_mono_coprod_inr {C : Type u} [category C] [has_zero_morphisms C] {X : C}
    {Y : C} [has_colimit (pair X Y)] : split_mono coprod.inr :=
  split_mono.mk (coprod.desc 0 𝟙)

/-- In the presence of zero morphisms, projections into a product are (split) epimorphisms. -/
protected instance split_epi_prod_fst {C : Type u} [category C] [has_zero_morphisms C] {X : C}
    {Y : C} [has_limit (pair X Y)] : split_epi prod.fst :=
  split_epi.mk (prod.lift 𝟙 0)

/-- In the presence of zero morphisms, projections into a product are (split) epimorphisms. -/
protected instance split_epi_prod_snd {C : Type u} [category C] [has_zero_morphisms C] {X : C}
    {Y : C} [has_limit (pair X Y)] : split_epi prod.snd :=
  split_epi.mk (prod.lift 0 𝟙)

end Mathlib