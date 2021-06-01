/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Scott Morrison, Floris van Doorn
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.functor
import Mathlib.PostPort

universes v u l u₂ v₂ 

namespace Mathlib

/-!
# Isomorphisms

This file defines isomorphisms between objects of a category.

## Main definitions

- `structure iso` : a bundled isomorphism between two objects of a category;
- `class is_iso` : an unbundled version of `iso`; note that `is_iso f` is usually *not* a `Prop`,
  because it holds the inverse morphism;
- `as_iso` : convert from `is_iso` to `iso`;
- `of_iso` : convert from `iso` to `is_iso`;
- standard operations on isomorphisms (composition, inverse etc)

## Notations

- `X ≅ Y` : same as `iso X Y`;
- `α ≪≫ β` : composition of two isomorphisms; it is called `iso.trans`

## Tags

category, category theory, isomorphism
-/

namespace category_theory


/--
An isomorphism (a.k.a. an invertible morphism) between two objects of a category.
The inverse morphism is bundled.

See also `category_theory.core` for the category with the same objects and isomorphisms playing
the role of morphisms.

See https://stacks.math.columbia.edu/tag/0017.
-/
structure iso {C : Type u} [category C] (X : C) (Y : C) where
  hom : X ⟶ Y
  inv : Y ⟶ X
  hom_inv_id' :
    autoParam (hom ≫ inv = 𝟙)
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
        (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  inv_hom_id' :
    autoParam (inv ≫ hom = 𝟙)
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
        (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

@[simp] theorem iso.hom_inv_id {C : Type u} [category C] {X : C} {Y : C} (c : iso X Y) :
    iso.hom c ≫ iso.inv c = 𝟙 :=
  sorry

@[simp] theorem iso.inv_hom_id {C : Type u} [category C] {X : C} {Y : C} (c : iso X Y) :
    iso.inv c ≫ iso.hom c = 𝟙 :=
  sorry

@[simp] theorem iso.hom_inv_id_assoc {C : Type u} [category C] {X : C} {Y : C} (c : iso X Y)
    {X' : C} (f' : X ⟶ X') : iso.hom c ≫ iso.inv c ≫ f' = f' :=
  sorry

infixr:10 " ≅ " => Mathlib.category_theory.iso

namespace iso


theorem ext {C : Type u} [category C] {X : C} {Y : C} {α : X ≅ Y} {β : X ≅ Y} (w : hom α = hom β) :
    α = β :=
  sorry

/-- Inverse isomorphism. -/
def symm {C : Type u} [category C] {X : C} {Y : C} (I : X ≅ Y) : Y ≅ X := mk (inv I) (hom I)

@[simp] theorem symm_hom {C : Type u} [category C] {X : C} {Y : C} (α : X ≅ Y) :
    hom (symm α) = inv α :=
  rfl

@[simp] theorem symm_inv {C : Type u} [category C] {X : C} {Y : C} (α : X ≅ Y) :
    inv (symm α) = hom α :=
  rfl

@[simp] theorem symm_mk {C : Type u} [category C] {X : C} {Y : C} (hom : X ⟶ Y) (inv : Y ⟶ X)
    (hom_inv_id : hom ≫ inv = 𝟙) (inv_hom_id : inv ≫ hom = 𝟙) : symm (mk hom inv) = mk inv hom :=
  rfl

@[simp] theorem symm_symm_eq {C : Type u} [category C] {X : C} {Y : C} (α : X ≅ Y) :
    symm (symm α) = α :=
  sorry

@[simp] theorem symm_eq_iff {C : Type u} [category C] {X : C} {Y : C} {α : X ≅ Y} {β : X ≅ Y} :
    symm α = symm β ↔ α = β :=
  { mp := fun (h : symm α = symm β) => symm_symm_eq α ▸ symm_symm_eq β ▸ congr_arg symm h,
    mpr := congr_arg symm }

/-- Identity isomorphism. -/
@[simp] theorem refl_inv {C : Type u} [category C] (X : C) : inv (refl X) = 𝟙 :=
  Eq.refl (inv (refl X))

protected instance inhabited {C : Type u} [category C] {X : C} : Inhabited (X ≅ X) :=
  { default := refl X }

@[simp] theorem refl_symm {C : Type u} [category C] (X : C) : symm (refl X) = refl X := rfl

/-- Composition of two isomorphisms -/
def trans {C : Type u} [category C] {X : C} {Y : C} {Z : C} (α : X ≅ Y) (β : Y ≅ Z) : X ≅ Z :=
  mk (hom α ≫ hom β) (inv β ≫ inv α)

infixr:80 " ≪≫ " => Mathlib.category_theory.iso.trans

@[simp] theorem trans_mk {C : Type u} [category C] {X : C} {Y : C} {Z : C} (hom : X ⟶ Y)
    (inv : Y ⟶ X) (hom_inv_id : hom ≫ inv = 𝟙) (inv_hom_id : inv ≫ hom = 𝟙) (hom' : Y ⟶ Z)
    (inv' : Z ⟶ Y) (hom_inv_id' : hom' ≫ inv' = 𝟙) (inv_hom_id' : inv' ≫ hom' = 𝟙)
    (hom_inv_id'' : (hom ≫ hom') ≫ inv' ≫ inv = 𝟙) (inv_hom_id'' : (inv' ≫ inv) ≫ hom ≫ hom' = 𝟙) :
    mk hom inv ≪≫ mk hom' inv' = mk (hom ≫ hom') (inv' ≫ inv) :=
  rfl

@[simp] theorem trans_symm {C : Type u} [category C] {X : C} {Y : C} {Z : C} (α : X ≅ Y)
    (β : Y ≅ Z) : symm (α ≪≫ β) = symm β ≪≫ symm α :=
  rfl

@[simp] theorem trans_assoc {C : Type u} [category C] {X : C} {Y : C} {Z : C} {Z' : C} (α : X ≅ Y)
    (β : Y ≅ Z) (γ : Z ≅ Z') : (α ≪≫ β) ≪≫ γ = α ≪≫ β ≪≫ γ :=
  sorry

@[simp] theorem refl_trans {C : Type u} [category C] {X : C} {Y : C} (α : X ≅ Y) :
    refl X ≪≫ α = α :=
  ext (category.id_comp (hom α))

@[simp] theorem trans_refl {C : Type u} [category C] {X : C} {Y : C} (α : X ≅ Y) :
    α ≪≫ refl Y = α :=
  ext (category.comp_id (hom α))

@[simp] theorem symm_self_id {C : Type u} [category C] {X : C} {Y : C} (α : X ≅ Y) :
    symm α ≪≫ α = refl Y :=
  ext (inv_hom_id α)

@[simp] theorem self_symm_id {C : Type u} [category C] {X : C} {Y : C} (α : X ≅ Y) :
    α ≪≫ symm α = refl X :=
  ext (hom_inv_id α)

@[simp] theorem symm_self_id_assoc {C : Type u} [category C] {X : C} {Y : C} {Z : C} (α : X ≅ Y)
    (β : Y ≅ Z) : symm α ≪≫ α ≪≫ β = β :=
  eq.mpr (id (Eq._oldrec (Eq.refl (symm α ≪≫ α ≪≫ β = β)) (Eq.symm (trans_assoc (symm α) α β))))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((symm α ≪≫ α) ≪≫ β = β)) (symm_self_id α)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (refl Y ≪≫ β = β)) (refl_trans β))) (Eq.refl β)))

@[simp] theorem self_symm_id_assoc {C : Type u} [category C] {X : C} {Y : C} {Z : C} (α : X ≅ Y)
    (β : X ≅ Z) : α ≪≫ symm α ≪≫ β = β :=
  eq.mpr (id (Eq._oldrec (Eq.refl (α ≪≫ symm α ≪≫ β = β)) (Eq.symm (trans_assoc α (symm α) β))))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((α ≪≫ symm α) ≪≫ β = β)) (self_symm_id α)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (refl X ≪≫ β = β)) (refl_trans β))) (Eq.refl β)))

theorem inv_comp_eq {C : Type u} [category C] {X : C} {Y : C} {Z : C} (α : X ≅ Y) {f : X ⟶ Z}
    {g : Y ⟶ Z} : inv α ≫ f = g ↔ f = hom α ≫ g :=
  sorry

theorem eq_inv_comp {C : Type u} [category C] {X : C} {Y : C} {Z : C} (α : X ≅ Y) {f : X ⟶ Z}
    {g : Y ⟶ Z} : g = inv α ≫ f ↔ hom α ≫ g = f :=
  iff.symm (inv_comp_eq (symm α))

theorem comp_inv_eq {C : Type u} [category C] {X : C} {Y : C} {Z : C} (α : X ≅ Y) {f : Z ⟶ Y}
    {g : Z ⟶ X} : f ≫ inv α = g ↔ f = g ≫ hom α :=
  sorry

theorem eq_comp_inv {C : Type u} [category C] {X : C} {Y : C} {Z : C} (α : X ≅ Y) {f : Z ⟶ Y}
    {g : Z ⟶ X} : g = f ≫ inv α ↔ g ≫ hom α = f :=
  iff.symm (comp_inv_eq (symm α))

theorem inv_eq_inv {C : Type u} [category C] {X : C} {Y : C} (f : X ≅ Y) (g : X ≅ Y) :
    inv f = inv g ↔ hom f = hom g :=
  sorry

theorem hom_comp_eq_id {C : Type u} [category C] {X : C} {Y : C} (α : X ≅ Y) {f : Y ⟶ X} :
    hom α ≫ f = 𝟙 ↔ f = inv α :=
  eq.mpr (id (Eq._oldrec (Eq.refl (hom α ≫ f = 𝟙 ↔ f = inv α)) (Eq.symm (propext (eq_inv_comp α)))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (f = inv α ≫ 𝟙 ↔ f = inv α)) (category.comp_id (inv α))))
      (iff.refl (f = inv α)))

theorem comp_hom_eq_id {C : Type u} [category C] {X : C} {Y : C} (α : X ≅ Y) {f : Y ⟶ X} :
    f ≫ hom α = 𝟙 ↔ f = inv α :=
  eq.mpr (id (Eq._oldrec (Eq.refl (f ≫ hom α = 𝟙 ↔ f = inv α)) (Eq.symm (propext (eq_comp_inv α)))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (f = 𝟙 ≫ inv α ↔ f = inv α)) (category.id_comp (inv α))))
      (iff.refl (f = inv α)))

theorem hom_eq_inv {C : Type u} [category C] {X : C} {Y : C} (α : X ≅ Y) (β : Y ≅ X) :
    hom α = inv β ↔ hom β = inv α :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (hom α = inv β ↔ hom β = inv α)) (propext (inv_eq_inv (symm α) β))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (hom (symm α) = hom β ↔ hom β = inv α)) (propext eq_comm)))
      (iff.refl (hom β = hom (symm α))))

end iso


/-- `is_iso` typeclass expressing that a morphism is invertible.
    This contains the data of the inverse, but is a subsingleton type. -/
class is_iso {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) where
  inv : Y ⟶ X
  hom_inv_id' :
    autoParam (f ≫ inv = 𝟙)
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
        (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  inv_hom_id' :
    autoParam (inv ≫ f = 𝟙)
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
        (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

/-- Reinterpret a morphism `f` with an `is_iso f` instance as an `iso`. -/
def as_iso {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) [h : is_iso f] : X ≅ Y :=
  iso.mk f (inv f)

@[simp] theorem as_iso_hom {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) [is_iso f] :
    iso.hom (as_iso f) = f :=
  rfl

@[simp] theorem as_iso_inv {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) [is_iso f] :
    iso.inv (as_iso f) = inv f :=
  rfl

namespace is_iso


@[simp] theorem hom_inv_id {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) [is_iso f] :
    f ≫ inv f = 𝟙 :=
  hom_inv_id'

@[simp] theorem inv_hom_id {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) [is_iso f] :
    inv f ≫ f = 𝟙 :=
  inv_hom_id'

@[simp] theorem hom_inv_id_assoc {C : Type u} [category C] {X : C} {Y : C} {Z : C} (f : X ⟶ Y)
    [is_iso f] (g : X ⟶ Z) : f ≫ inv f ≫ g = g :=
  iso.hom_inv_id_assoc (as_iso f) g

@[simp] theorem inv_hom_id_assoc {C : Type u} [category C] {X : C} {Y : C} {Z : C} (f : X ⟶ Y)
    [is_iso f] (g : Y ⟶ Z) : inv f ≫ f ≫ g = g :=
  iso.inv_hom_id_assoc (as_iso f) g

protected instance id {C : Type u} [category C] (X : C) : is_iso 𝟙 := mk 𝟙

protected instance of_iso {C : Type u} [category C] {X : C} {Y : C} (f : X ≅ Y) :
    is_iso (iso.hom f) :=
  mk (iso.inv f)

protected instance of_iso_inv {C : Type u} [category C] {X : C} {Y : C} (f : X ≅ Y) :
    is_iso (iso.inv f) :=
  is_iso.of_iso (iso.symm f)

protected instance inv_is_iso {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} [is_iso f] :
    is_iso (inv f) :=
  is_iso.of_iso_inv (as_iso f)

protected instance comp_is_iso {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Y}
    {h : Y ⟶ Z} [is_iso f] [is_iso h] : is_iso (f ≫ h) :=
  is_iso.of_iso (as_iso f ≪≫ as_iso h)

@[simp] theorem inv_id {C : Type u} [category C] {X : C} : inv 𝟙 = 𝟙 := rfl

@[simp] theorem inv_comp {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Y} {h : Y ⟶ Z}
    [is_iso f] [is_iso h] : inv (f ≫ h) = inv h ≫ inv f :=
  rfl

@[simp] theorem inv_inv {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} [is_iso f] :
    inv (inv f) = f :=
  rfl

@[simp] theorem iso.inv_inv {C : Type u} [category C] {X : C} {Y : C} (f : X ≅ Y) :
    inv (iso.inv f) = iso.hom f :=
  rfl

@[simp] theorem iso.inv_hom {C : Type u} [category C] {X : C} {Y : C} (f : X ≅ Y) :
    inv (iso.hom f) = iso.inv f :=
  rfl

@[simp] theorem inv_comp_eq {C : Type u} [category C] {X : C} {Y : C} {Z : C} (α : X ⟶ Y) [is_iso α]
    {f : X ⟶ Z} {g : Y ⟶ Z} : inv α ≫ f = g ↔ f = α ≫ g :=
  iso.inv_comp_eq (as_iso α)

@[simp] theorem eq_inv_comp {C : Type u} [category C] {X : C} {Y : C} {Z : C} (α : X ⟶ Y) [is_iso α]
    {f : X ⟶ Z} {g : Y ⟶ Z} : g = inv α ≫ f ↔ α ≫ g = f :=
  iso.eq_inv_comp (as_iso α)

@[simp] theorem comp_inv_eq {C : Type u} [category C] {X : C} {Y : C} {Z : C} (α : X ⟶ Y) [is_iso α]
    {f : Z ⟶ Y} {g : Z ⟶ X} : f ≫ inv α = g ↔ f = g ≫ α :=
  iso.comp_inv_eq (as_iso α)

@[simp] theorem eq_comp_inv {C : Type u} [category C] {X : C} {Y : C} {Z : C} (α : X ⟶ Y) [is_iso α]
    {f : Z ⟶ Y} {g : Z ⟶ X} : g = f ≫ inv α ↔ g ≫ α = f :=
  iso.eq_comp_inv (as_iso α)

protected instance epi_of_iso {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) [is_iso f] :
    epi f :=
  epi.mk
    fun (Z : C) (g h : Y ⟶ Z) (w : f ≫ g = f ≫ h) =>
      eq.mpr (id (Eq._oldrec (Eq.refl (g = h)) (Eq.symm (inv_hom_id_assoc f g))))
        (eq.mpr (id (Eq._oldrec (Eq.refl (inv f ≫ f ≫ g = h)) w))
          (eq.mpr (id (Eq._oldrec (Eq.refl (inv f ≫ f ≫ h = h)) (inv_hom_id_assoc f h)))
            (Eq.refl h)))

protected instance mono_of_iso {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) [is_iso f] :
    mono f :=
  mono.mk
    fun (Z : C) (g h : Z ⟶ X) (w : g ≫ f = h ≫ f) =>
      eq.mpr (id (Eq._oldrec (Eq.refl (g = h)) (Eq.symm (category.comp_id g))))
        (eq.mpr (id (Eq._oldrec (Eq.refl (g ≫ 𝟙 = h)) (Eq.symm (category.comp_id h))))
          (eq.mpr (id (Eq._oldrec (Eq.refl (g ≫ 𝟙 = h ≫ 𝟙)) (Eq.symm (hom_inv_id f))))
            (eq.mpr
              (id
                (Eq._oldrec (Eq.refl (g ≫ f ≫ inv f = h ≫ f ≫ inv f))
                  (Eq.symm (category.assoc g f (inv f)))))
              (eq.mpr (id (Eq._oldrec (Eq.refl ((g ≫ f) ≫ inv f = h ≫ f ≫ inv f)) w))
                (eq.mpr
                  (id
                    (Eq._oldrec (Eq.refl ((h ≫ f) ≫ inv f = h ≫ f ≫ inv f))
                      (Eq.symm (category.assoc h f (inv f)))))
                  (Eq.refl ((h ≫ f) ≫ inv f)))))))

end is_iso


theorem eq_of_inv_eq_inv {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y}
    [is_iso f] [is_iso g] (p : inv f = inv g) : f = g :=
  sorry

protected instance is_iso.subsingleton {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) :
    subsingleton (is_iso f) :=
  sorry

theorem is_iso.inv_eq_inv {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y}
    [is_iso f] [is_iso g] : inv f = inv g ↔ f = g :=
  iso.inv_eq_inv (as_iso f) (as_iso g)

theorem hom_comp_eq_id {C : Type u} [category C] {X : C} {Y : C} (g : X ⟶ Y) [is_iso g]
    {f : Y ⟶ X} : g ≫ f = 𝟙 ↔ f = inv g :=
  iso.hom_comp_eq_id (as_iso g)

theorem comp_hom_eq_id {C : Type u} [category C] {X : C} {Y : C} (g : X ⟶ Y) [is_iso g]
    {f : Y ⟶ X} : f ≫ g = 𝟙 ↔ f = inv g :=
  iso.comp_hom_eq_id (as_iso g)

namespace iso


/-!
All these cancellation lemmas can be solved by `simp [cancel_mono]` (or `simp [cancel_epi]`),
but with the current design `cancel_mono` is not a good `simp` lemma,
because it generates a typeclass search.

When we can see syntactically that a morphism is a `mono` or an `epi`
because it came from an isomorphism, it's fine to do the cancellation via `simp`.

In the longer term, it might be worth exploring making `mono` and `epi` structures,
rather than typeclasses, with coercions back to `X ⟶ Y`.
Presumably we could write `X ↪ Y` and `X ↠ Y`.
-/

@[simp] theorem cancel_iso_hom_left {C : Type u} [category C] {X : C} {Y : C} {Z : C} (f : X ≅ Y)
    (g : Y ⟶ Z) (g' : Y ⟶ Z) : hom f ≫ g = hom f ≫ g' ↔ g = g' :=
  sorry

@[simp] theorem cancel_iso_inv_left {C : Type u} [category C] {X : C} {Y : C} {Z : C} (f : Y ≅ X)
    (g : Y ⟶ Z) (g' : Y ⟶ Z) : inv f ≫ g = inv f ≫ g' ↔ g = g' :=
  sorry

@[simp] theorem cancel_iso_hom_right {C : Type u} [category C] {X : C} {Y : C} {Z : C} (f : X ⟶ Y)
    (f' : X ⟶ Y) (g : Y ≅ Z) : f ≫ hom g = f' ≫ hom g ↔ f = f' :=
  sorry

@[simp] theorem cancel_iso_inv_right {C : Type u} [category C] {X : C} {Y : C} {Z : C} (f : X ⟶ Y)
    (f' : X ⟶ Y) (g : Z ≅ Y) : f ≫ inv g = f' ≫ inv g ↔ f = f' :=
  sorry

/-
Unfortunately cancelling an isomorphism from the right of a chain of compositions is awkward.
We would need separate lemmas for each chain length (worse: for each pair of chain lengths).

We provide two more lemmas, for case of three morphisms, because this actually comes up in practice,
but then stop.
-/

@[simp] theorem cancel_iso_hom_right_assoc {C : Type u} [category C] {W : C} {X : C} {X' : C}
    {Y : C} {Z : C} (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X') (g' : X' ⟶ Y) (h : Y ≅ Z) :
    f ≫ g ≫ hom h = f' ≫ g' ≫ hom h ↔ f ≫ g = f' ≫ g' :=
  sorry

@[simp] theorem cancel_iso_inv_right_assoc {C : Type u} [category C] {W : C} {X : C} {X' : C}
    {Y : C} {Z : C} (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X') (g' : X' ⟶ Y) (h : Z ≅ Y) :
    f ≫ g ≫ inv h = f' ≫ g' ≫ inv h ↔ f ≫ g = f' ≫ g' :=
  sorry

end iso


namespace functor


/-- A functor `F : C ⥤ D` sends isomorphisms `i : X ≅ Y` to isomorphisms `F.obj X ≅ F.obj Y` -/
def map_iso {C : Type u} [category C] {D : Type u₂} [category D] (F : C ⥤ D) {X : C} {Y : C}
    (i : X ≅ Y) : obj F X ≅ obj F Y :=
  iso.mk (map F (iso.hom i)) (map F (iso.inv i))

@[simp] theorem map_iso_hom {C : Type u} [category C] {D : Type u₂} [category D] (F : C ⥤ D) {X : C}
    {Y : C} (i : X ≅ Y) : iso.hom (map_iso F i) = map F (iso.hom i) :=
  rfl

@[simp] theorem map_iso_inv {C : Type u} [category C] {D : Type u₂} [category D] (F : C ⥤ D) {X : C}
    {Y : C} (i : X ≅ Y) : iso.inv (map_iso F i) = map F (iso.inv i) :=
  rfl

@[simp] theorem map_iso_symm {C : Type u} [category C] {D : Type u₂} [category D] (F : C ⥤ D)
    {X : C} {Y : C} (i : X ≅ Y) : map_iso F (iso.symm i) = iso.symm (map_iso F i) :=
  rfl

@[simp] theorem map_iso_trans {C : Type u} [category C] {D : Type u₂} [category D] (F : C ⥤ D)
    {X : C} {Y : C} {Z : C} (i : X ≅ Y) (j : Y ≅ Z) :
    map_iso F (i ≪≫ j) = map_iso F i ≪≫ map_iso F j :=
  iso.ext (map_comp F (iso.hom i) (iso.hom j))

@[simp] theorem map_iso_refl {C : Type u} [category C] {D : Type u₂} [category D] (F : C ⥤ D)
    (X : C) : map_iso F (iso.refl X) = iso.refl (obj F X) :=
  iso.ext (map_id F X)

protected instance map_is_iso {C : Type u} [category C] {X : C} {Y : C} {D : Type u₂} [category D]
    (F : C ⥤ D) (f : X ⟶ Y) [is_iso f] : is_iso (map F f) :=
  is_iso.of_iso (map_iso F (as_iso f))

@[simp] theorem map_inv {C : Type u} [category C] {D : Type u₂} [category D] (F : C ⥤ D) {X : C}
    {Y : C} (f : X ⟶ Y) [is_iso f] : map F (inv f) = inv (map F f) :=
  rfl

theorem map_hom_inv {C : Type u} [category C] {D : Type u₂} [category D] (F : C ⥤ D) {X : C} {Y : C}
    (f : X ⟶ Y) [is_iso f] : map F f ≫ map F (inv f) = 𝟙 :=
  sorry

theorem map_inv_hom {C : Type u} [category C] {D : Type u₂} [category D] (F : C ⥤ D) {X : C} {Y : C}
    (f : X ⟶ Y) [is_iso f] : map F (inv f) ≫ map F f = 𝟙 :=
  sorry

end Mathlib