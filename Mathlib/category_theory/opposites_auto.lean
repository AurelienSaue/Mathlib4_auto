/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.types
import Mathlib.category_theory.equivalence
import Mathlib.data.opposite
import Mathlib.PostPort

universes v₁ u₁ u₂ v₂ v 

namespace Mathlib

namespace category_theory


/-- The hom types of the opposite of a category (or graph).

  As with the objects, we'll make this irreducible below.
  Use `f.op` and `f.unop` to convert between morphisms of C
  and morphisms of Cᵒᵖ.
-/
protected instance has_hom.opposite {C : Type u₁} [has_hom C] : has_hom (Cᵒᵖ) :=
  has_hom.mk fun (X Y : Cᵒᵖ) => opposite.unop Y ⟶ opposite.unop X

/--
The opposite of a morphism in `C`.
-/
/--
def has_hom.hom.op {C : Type u₁} [has_hom C] {X : C} {Y : C} (f : X ⟶ Y) :
    opposite.op Y ⟶ opposite.op X :=
  f

Given a morphism in `Cᵒᵖ`, we can take the "unopposite" back in `C`.
-/
def has_hom.hom.unop {C : Type u₁} [has_hom C] {X : Cᵒᵖ} {Y : Cᵒᵖ} (f : X ⟶ Y) :
    opposite.unop Y ⟶ opposite.unop X :=
  f

theorem has_hom.hom.op_inj {C : Type u₁} [has_hom C] {X : C} {Y : C} :
    function.injective has_hom.hom.op :=
  fun (_x _x_1 : X ⟶ Y) (H : has_hom.hom.op _x = has_hom.hom.op _x_1) =>
    congr_arg has_hom.hom.unop H

theorem has_hom.hom.unop_inj {C : Type u₁} [has_hom C] {X : Cᵒᵖ} {Y : Cᵒᵖ} :
    function.injective has_hom.hom.unop :=
  fun (_x _x_1 : X ⟶ Y) (H : has_hom.hom.unop _x = has_hom.hom.unop _x_1) =>
    congr_arg has_hom.hom.op H

@[simp] theorem has_hom.hom.unop_op {C : Type u₁} [has_hom C] {X : C} {Y : C} {f : X ⟶ Y} :
    has_hom.hom.unop (has_hom.hom.op f) = f :=
  rfl

@[simp] theorem has_hom.hom.op_unop {C : Type u₁} [has_hom C] {X : Cᵒᵖ} {Y : Cᵒᵖ} {f : X ⟶ Y} :
    has_hom.hom.op (has_hom.hom.unop f) = f :=
  rfl

/--
The opposite category.

See https://stacks.math.columbia.edu/tag/001M.
-/
protected instance category.opposite {C : Type u₁} [category C] : category (Cᵒᵖ) := category.mk

@[simp] theorem op_comp {C : Type u₁} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} :
    has_hom.hom.op (f ≫ g) = has_hom.hom.op g ≫ has_hom.hom.op f :=
  rfl

@[simp] theorem op_id {C : Type u₁} [category C] {X : C} : has_hom.hom.op 𝟙 = 𝟙 := rfl

@[simp] theorem unop_comp {C : Type u₁} [category C] {X : Cᵒᵖ} {Y : Cᵒᵖ} {Z : Cᵒᵖ} {f : X ⟶ Y}
    {g : Y ⟶ Z} : has_hom.hom.unop (f ≫ g) = has_hom.hom.unop g ≫ has_hom.hom.unop f :=
  rfl

@[simp] theorem unop_id {C : Type u₁} [category C] {X : Cᵒᵖ} : has_hom.hom.unop 𝟙 = 𝟙 := rfl

@[simp] theorem unop_id_op {C : Type u₁} [category C] {X : C} : has_hom.hom.unop 𝟙 = 𝟙 := rfl

@[simp] theorem op_id_unop {C : Type u₁} [category C] {X : Cᵒᵖ} : has_hom.hom.op 𝟙 = 𝟙 := rfl

/-- The functor from the double-opposite of a category to the underlying category. -/
def op_op (C : Type u₁) [category C] : Cᵒᵖᵒᵖ ⥤ C :=
  functor.mk (fun (X : Cᵒᵖᵒᵖ) => opposite.unop (opposite.unop X))
    fun (X Y : Cᵒᵖᵒᵖ) (f : X ⟶ Y) => has_hom.hom.unop (has_hom.hom.unop f)

/-- The functor from a category to its double-opposite.  -/
def unop_unop (C : Type u₁) [category C] : C ⥤ (Cᵒᵖᵒᵖ) :=
  functor.mk (fun (X : C) => opposite.op (opposite.op X))
    fun (X Y : C) (f : X ⟶ Y) => has_hom.hom.op (has_hom.hom.op f)

/-- The double opposite category is equivalent to the original. -/
@[simp] theorem op_op_equivalence_inverse (C : Type u₁) [category C] :
    equivalence.inverse (op_op_equivalence C) = unop_unop C :=
  Eq.refl (equivalence.inverse (op_op_equivalence C))

/--
If `f.op` is an isomorphism `f` must be too.
(This cannot be an instance as it would immediately loop!)
-/
def is_iso_of_op {C : Type u₁} [category C] {X : C} {Y : C} (f : X ⟶ Y)
    [is_iso (has_hom.hom.op f)] : is_iso f :=
  is_iso.mk (has_hom.hom.unop (inv (has_hom.hom.op f)))

namespace functor


/--
The opposite of a functor, i.e. considering a functor `F : C ⥤ D` as a functor `Cᵒᵖ ⥤ Dᵒᵖ`.
In informal mathematics no distinction is made between these.
-/
@[simp] theorem op_obj {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) (X : Cᵒᵖ) :
    obj (functor.op F) X = opposite.op (obj F (opposite.unop X)) :=
  Eq.refl (obj (functor.op F) X)

/--
Given a functor `F : Cᵒᵖ ⥤ Dᵒᵖ` we can take the "unopposite" functor `F : C ⥤ D`.
In informal mathematics no distinction is made between these.
-/
protected def unop {C : Type u₁} [category C] {D : Type u₂} [category D] (F : Cᵒᵖ ⥤ (Dᵒᵖ)) :
    C ⥤ D :=
  mk (fun (X : C) => opposite.unop (obj F (opposite.op X)))
    fun (X Y : C) (f : X ⟶ Y) => has_hom.hom.unop (map F (has_hom.hom.op f))

/-- The isomorphism between `F.op.unop` and `F`. -/
def op_unop_iso {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) :
    functor.unop (functor.op F) ≅ F :=
  nat_iso.of_components (fun (X : C) => iso.refl (obj (functor.unop (functor.op F)) X)) sorry

/-- The isomorphism between `F.unop.op` and `F`. -/
def unop_op_iso {C : Type u₁} [category C] {D : Type u₂} [category D] (F : Cᵒᵖ ⥤ (Dᵒᵖ)) :
    functor.op (functor.unop F) ≅ F :=
  nat_iso.of_components (fun (X : Cᵒᵖ) => iso.refl (obj (functor.op (functor.unop F)) X)) sorry

/--
Taking the opposite of a functor is functorial.
-/
@[simp] theorem op_hom_obj (C : Type u₁) [category C] (D : Type u₂) [category D] (F : C ⥤ Dᵒᵖ) :
    obj (op_hom C D) F = functor.op (opposite.unop F) :=
  Eq.refl (obj (op_hom C D) F)

/--
Take the "unopposite" of a functor is functorial.
-/
@[simp] theorem op_inv_obj (C : Type u₁) [category C] (D : Type u₂) [category D] (F : Cᵒᵖ ⥤ (Dᵒᵖ)) :
    obj (op_inv C D) F = opposite.op (functor.unop F) :=
  Eq.refl (obj (op_inv C D) F)

-- TODO show these form an equivalence

/--
Another variant of the opposite of functor, turning a functor `C ⥤ Dᵒᵖ` into a functor `Cᵒᵖ ⥤ D`.
In informal mathematics no distinction is made.
-/
@[simp] theorem left_op_map {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ (Dᵒᵖ))
    (X : Cᵒᵖ) (Y : Cᵒᵖ) (f : X ⟶ Y) :
    map (functor.left_op F) f = has_hom.hom.unop (map F (has_hom.hom.unop f)) :=
  Eq.refl (map (functor.left_op F) f)

/--
Another variant of the opposite of functor, turning a functor `Cᵒᵖ ⥤ D` into a functor `C ⥤ Dᵒᵖ`.
In informal mathematics no distinction is made.
-/
@[simp] theorem right_op_obj {C : Type u₁} [category C] {D : Type u₂} [category D] (F : Cᵒᵖ ⥤ D)
    (X : C) : obj (functor.right_op F) X = opposite.op (obj F (opposite.op X)) :=
  Eq.refl (obj (functor.right_op F) X)

-- TODO show these form an equivalence

protected instance op.category_theory.full {C : Type u₁} [category C] {D : Type u₂} [category D]
    {F : C ⥤ D} [full F] : full (functor.op F) :=
  full.mk
    fun (X Y : Cᵒᵖ) (f : obj (functor.op F) X ⟶ obj (functor.op F) Y) =>
      has_hom.hom.op (preimage F (has_hom.hom.unop f))

protected instance op.category_theory.faithful {C : Type u₁} [category C] {D : Type u₂} [category D]
    {F : C ⥤ D} [faithful F] : faithful (functor.op F) :=
  faithful.mk

/-- If F is faithful then the right_op of F is also faithful. -/
protected instance right_op_faithful {C : Type u₁} [category C] {D : Type u₂} [category D]
    {F : Cᵒᵖ ⥤ D} [faithful F] : faithful (functor.right_op F) :=
  faithful.mk

/-- If F is faithful then the left_op of F is also faithful. -/
protected instance left_op_faithful {C : Type u₁} [category C] {D : Type u₂} [category D]
    {F : C ⥤ (Dᵒᵖ)} [faithful F] : faithful (functor.left_op F) :=
  faithful.mk

end functor


namespace nat_trans


/-- The opposite of a natural transformation. -/
@[simp] theorem op_app {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D}
    (α : F ⟶ G) (X : Cᵒᵖ) : app (nat_trans.op α) X = has_hom.hom.op (app α (opposite.unop X)) :=
  Eq.refl (app (nat_trans.op α) X)

@[simp] theorem op_id {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) :
    nat_trans.op 𝟙 = 𝟙 :=
  rfl

/-- The "unopposite" of a natural transformation. -/
@[simp] theorem unop_app {C : Type u₁} [category C] {D : Type u₂} [category D] {F : Cᵒᵖ ⥤ (Dᵒᵖ)}
    {G : Cᵒᵖ ⥤ (Dᵒᵖ)} (α : F ⟶ G) (X : C) :
    app (nat_trans.unop α) X = has_hom.hom.unop (app α (opposite.op X)) :=
  Eq.refl (app (nat_trans.unop α) X)

@[simp] theorem unop_id {C : Type u₁} [category C] {D : Type u₂} [category D] (F : Cᵒᵖ ⥤ (Dᵒᵖ)) :
    nat_trans.unop 𝟙 = 𝟙 :=
  rfl

/--
Given a natural transformation `α : F.op ⟶ G.op`,
we can take the "unopposite" of each component obtaining a natural transformation `G ⟶ F`.
-/
protected def remove_op {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D}
    {G : C ⥤ D} (α : functor.op F ⟶ functor.op G) : G ⟶ F :=
  mk fun (X : C) => has_hom.hom.unop (app α (opposite.op X))

@[simp] theorem remove_op_id {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) :
    nat_trans.remove_op 𝟙 = 𝟙 :=
  rfl

/--
Given a natural transformation `α : F ⟶ G`, for `F G : C ⥤ Dᵒᵖ`,
taking `unop` of each component gives a natural transformation `G.left_op ⟶ F.left_op`.
-/
protected def left_op {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ (Dᵒᵖ)}
    {G : C ⥤ (Dᵒᵖ)} (α : F ⟶ G) : functor.left_op G ⟶ functor.left_op F :=
  mk fun (X : Cᵒᵖ) => has_hom.hom.unop (app α (opposite.unop X))

@[simp] theorem left_op_app {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ (Dᵒᵖ)}
    {G : C ⥤ (Dᵒᵖ)} (α : F ⟶ G) (X : Cᵒᵖ) :
    app (nat_trans.left_op α) X = has_hom.hom.unop (app α (opposite.unop X)) :=
  rfl

/--
Given a natural transformation `α : F.left_op ⟶ G.left_op`, for `F G : C ⥤ Dᵒᵖ`,
taking `op` of each component gives a natural transformation `G ⟶ F`.
-/
protected def remove_left_op {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ (Dᵒᵖ)}
    {G : C ⥤ (Dᵒᵖ)} (α : functor.left_op F ⟶ functor.left_op G) : G ⟶ F :=
  mk fun (X : C) => has_hom.hom.op (app α (opposite.op X))

@[simp] theorem remove_left_op_app {C : Type u₁} [category C] {D : Type u₂} [category D]
    {F : C ⥤ (Dᵒᵖ)} {G : C ⥤ (Dᵒᵖ)} (α : functor.left_op F ⟶ functor.left_op G) (X : C) :
    app (nat_trans.remove_left_op α) X = has_hom.hom.op (app α (opposite.op X)) :=
  rfl

end nat_trans


namespace iso


/--
The opposite isomorphism.
-/
protected def op {C : Type u₁} [category C] {X : C} {Y : C} (α : X ≅ Y) :
    opposite.op Y ≅ opposite.op X :=
  mk (has_hom.hom.op (hom α)) (has_hom.hom.op (inv α))

@[simp] theorem op_hom {C : Type u₁} [category C] {X : C} {Y : C} {α : X ≅ Y} :
    hom (iso.op α) = has_hom.hom.op (hom α) :=
  rfl

@[simp] theorem op_inv {C : Type u₁} [category C] {X : C} {Y : C} {α : X ≅ Y} :
    inv (iso.op α) = has_hom.hom.op (inv α) :=
  rfl

end iso


namespace nat_iso


/-- The natural isomorphism between opposite functors `G.op ≅ F.op` induced by a natural
isomorphism between the original functors `F ≅ G`. -/
protected def op {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D}
    (α : F ≅ G) : functor.op G ≅ functor.op F :=
  iso.mk (nat_trans.op (iso.hom α)) (nat_trans.op (iso.inv α))

@[simp] theorem op_hom {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D}
    (α : F ≅ G) : iso.hom (nat_iso.op α) = nat_trans.op (iso.hom α) :=
  rfl

@[simp] theorem op_inv {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D}
    (α : F ≅ G) : iso.inv (nat_iso.op α) = nat_trans.op (iso.inv α) :=
  rfl

/-- The natural isomorphism between functors `G ≅ F` induced by a natural isomorphism
between the opposite functors `F.op ≅ G.op`. -/
protected def remove_op {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D}
    {G : C ⥤ D} (α : functor.op F ≅ functor.op G) : G ≅ F :=
  iso.mk (nat_trans.remove_op (iso.hom α)) (nat_trans.remove_op (iso.inv α))

@[simp] theorem remove_op_hom {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D}
    {G : C ⥤ D} (α : functor.op F ≅ functor.op G) :
    iso.hom (nat_iso.remove_op α) = nat_trans.remove_op (iso.hom α) :=
  rfl

@[simp] theorem remove_op_inv {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D}
    {G : C ⥤ D} (α : functor.op F ≅ functor.op G) :
    iso.inv (nat_iso.remove_op α) = nat_trans.remove_op (iso.inv α) :=
  rfl

/-- The natural isomorphism between functors `G.unop ≅ F.unop` induced by a natural isomorphism
between the original functors `F ≅ G`. -/
protected def unop {C : Type u₁} [category C] {D : Type u₂} [category D] {F : Cᵒᵖ ⥤ (Dᵒᵖ)}
    {G : Cᵒᵖ ⥤ (Dᵒᵖ)} (α : F ≅ G) : functor.unop G ≅ functor.unop F :=
  iso.mk (nat_trans.unop (iso.hom α)) (nat_trans.unop (iso.inv α))

@[simp] theorem unop_hom {C : Type u₁} [category C] {D : Type u₂} [category D] {F : Cᵒᵖ ⥤ (Dᵒᵖ)}
    {G : Cᵒᵖ ⥤ (Dᵒᵖ)} (α : F ≅ G) : iso.hom (nat_iso.unop α) = nat_trans.unop (iso.hom α) :=
  rfl

@[simp] theorem unop_inv {C : Type u₁} [category C] {D : Type u₂} [category D] {F : Cᵒᵖ ⥤ (Dᵒᵖ)}
    {G : Cᵒᵖ ⥤ (Dᵒᵖ)} (α : F ≅ G) : iso.inv (nat_iso.unop α) = nat_trans.unop (iso.inv α) :=
  rfl

end nat_iso


namespace equivalence


/--
An equivalence between categories gives an equivalence between the opposite categories.
-/
@[simp] theorem op_inverse {C : Type u₁} [category C] {D : Type u₂} [category D] (e : C ≌ D) :
    inverse (op e) = functor.op (inverse e) :=
  Eq.refl (inverse (op e))

/--
An equivalence between opposite categories gives an equivalence between the original categories.
-/
@[simp] theorem unop_unit_iso {C : Type u₁} [category C] {D : Type u₂} [category D]
    (e : Cᵒᵖ ≌ (Dᵒᵖ)) : unit_iso (unop e) = iso.symm (nat_iso.unop (unit_iso e)) :=
  Eq.refl (unit_iso (unop e))

end equivalence


/-- The equivalence between arrows of the form `A ⟶ B` and `B.unop ⟶ A.unop`. Useful for building
adjunctions.
Note that this (definitionally) gives variants
```
def op_equiv' (A : C) (B : Cᵒᵖ) : (opposite.op A ⟶ B) ≃ (B.unop ⟶ A) :=
op_equiv _ _

def op_equiv'' (A : Cᵒᵖ) (B : C) : (A ⟶ opposite.op B) ≃ (B ⟶ A.unop) :=
op_equiv _ _

def op_equiv''' (A B : C) : (opposite.op A ⟶ opposite.op B) ≃ (B ⟶ A) :=
op_equiv _ _
```
-/
def op_equiv {C : Type u₁} [category C] (A : Cᵒᵖ) (B : Cᵒᵖ) :
    (A ⟶ B) ≃ (opposite.unop B ⟶ opposite.unop A) :=
  equiv.mk (fun (f : A ⟶ B) => has_hom.hom.unop f)
    (fun (g : opposite.unop B ⟶ opposite.unop A) => has_hom.hom.op g) sorry sorry

-- These two are made by hand rather than by simps because simps generates

-- `(op_equiv _ _).to_fun f = ...` rather than the coercion version.

@[simp] theorem op_equiv_apply {C : Type u₁} [category C] (A : Cᵒᵖ) (B : Cᵒᵖ) (f : A ⟶ B) :
    coe_fn (op_equiv A B) f = has_hom.hom.unop f :=
  rfl

@[simp] theorem op_equiv_symm_apply {C : Type u₁} [category C] (A : Cᵒᵖ) (B : Cᵒᵖ)
    (f : opposite.unop B ⟶ opposite.unop A) :
    coe_fn (equiv.symm (op_equiv A B)) f = has_hom.hom.op f :=
  rfl

/-- Construct a morphism in the opposite of a preorder category from an inequality. -/
def op_hom_of_le {α : Type v} [preorder α] {U : αᵒᵖ} {V : αᵒᵖ}
    (h : opposite.unop V ≤ opposite.unop U) : U ⟶ V :=
  has_hom.hom.op (hom_of_le h)

theorem le_of_op_hom {α : Type v} [preorder α] {U : αᵒᵖ} {V : αᵒᵖ} (h : U ⟶ V) :
    opposite.unop V ≤ opposite.unop U :=
  le_of_hom (has_hom.hom.unop h)

end Mathlib