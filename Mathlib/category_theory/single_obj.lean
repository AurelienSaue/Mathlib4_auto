/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.endomorphism
import Mathlib.category_theory.category.Cat
import Mathlib.algebra.category.Mon.basic
import Mathlib.PostPort

universes u v w u_1 

namespace Mathlib

/-!
# Single-object category

Single object category with a given monoid of endomorphisms.  It is defined to facilitate transfering
some definitions and lemmas (e.g., conjugacy etc.) from category theory to monoids and groups.

## Main definitions

Given a type `α` with a monoid structure, `single_obj α` is `unit` type with `category` structure
such that `End (single_obj α).star` is the monoid `α`.  This can be extended to a functor `Mon ⥤
Cat`.

If `α` is a group, then `single_obj α` is a groupoid.

An element `x : α` can be reinterpreted as an element of `End (single_obj.star α)` using
`single_obj.to_End`.

## Implementation notes

- `category_struct.comp` on `End (single_obj.star α)` is `flip (*)`, not `(*)`. This way
  multiplication on `End` agrees with the multiplication on `α`.

- By default, Lean puts instances into `category_theory` namespace instead of
  `category_theory.single_obj`, so we give all names explicitly.
-/

namespace category_theory


/-- Type tag on `unit` used to define single-object categories and groupoids. -/
def single_obj (α : Type u)  :=
  Unit

namespace single_obj


/-- One and `flip (*)` become `id` and `comp` for morphisms of the single object category. -/
protected instance category_struct (α : Type u) [HasOne α] [Mul α] : category_struct (single_obj α) :=
  category_struct.mk (fun (_x : single_obj α) => 1)
    fun (_x _x_1 _x_2 : single_obj α) (x : _x ⟶ _x_1) (y : _x_1 ⟶ _x_2) => y * x

/-- Monoid laws become category laws for the single object category. -/
protected instance category (α : Type u) [monoid α] : category (single_obj α) :=
  category.mk

/--
Groupoid structure on `single_obj α`.

See https://stacks.math.columbia.edu/tag/0019.
-/
protected instance groupoid (α : Type u) [group α] : groupoid (single_obj α) :=
  groupoid.mk fun (_x _x_1 : single_obj α) (x : _x ⟶ _x_1) => x⁻¹

/-- The single object in `single_obj α`. -/
protected def star (α : Type u) : single_obj α :=
  Unit.unit

/-- The endomorphisms monoid of the only object in `single_obj α` is equivalent to the original
     monoid α. -/
def to_End (α : Type u) [monoid α] : α ≃* End (single_obj.star α) :=
  mul_equiv.mk (equiv.to_fun (equiv.refl α)) (equiv.inv_fun (equiv.refl α)) sorry sorry sorry

theorem to_End_def (α : Type u) [monoid α] (x : α) : coe_fn (to_End α) x = x :=
  rfl

/-- There is a 1-1 correspondence between monoid homomorphisms `α → β` and functors between the
    corresponding single-object categories. It means that `single_obj` is a fully faithful
    functor.

See https://stacks.math.columbia.edu/tag/001F --
although we do not characterize when the functor is full or faithful.
-/
def map_hom (α : Type u) (β : Type v) [monoid α] [monoid β] : (α →* β) ≃ single_obj α ⥤ single_obj β :=
  equiv.mk (fun (f : α →* β) => functor.mk id fun (_x _x : single_obj α) => ⇑f)
    (fun (f : single_obj α ⥤ single_obj β) => monoid_hom.mk (functor.map f) sorry sorry) sorry sorry

theorem map_hom_id (α : Type u) [monoid α] : coe_fn (map_hom α α) (monoid_hom.id α) = 𝟭 :=
  rfl

theorem map_hom_comp {α : Type u} {β : Type v} [monoid α] [monoid β] (f : α →* β) {γ : Type w} [monoid γ] (g : β →* γ) : coe_fn (map_hom α γ) (monoid_hom.comp g f) = coe_fn (map_hom α β) f ⋙ coe_fn (map_hom β γ) g :=
  rfl

end single_obj


end category_theory


namespace monoid_hom


/-- Reinterpret a monoid homomorphism `f : α → β` as a functor `(single_obj α) ⥤ (single_obj β)`.
See also `category_theory.single_obj.map_hom` for an equivalence between these types. -/
def to_functor {α : Type u} {β : Type v} [monoid α] [monoid β] (f : α →* β) : category_theory.single_obj α ⥤ category_theory.single_obj β :=
  coe_fn (category_theory.single_obj.map_hom α β) f

@[simp] theorem id_to_functor (α : Type u) [monoid α] : to_functor (id α) = 𝟭 :=
  rfl

@[simp] theorem comp_to_functor {α : Type u} {β : Type v} [monoid α] [monoid β] (f : α →* β) {γ : Type w} [monoid γ] (g : β →* γ) : to_functor (comp g f) = to_functor f ⋙ to_functor g :=
  rfl

end monoid_hom


namespace units


/--
The units in a monoid are (multiplicatively) equivalent to
the automorphisms of `star` when we think of the monoid as a single-object category. -/
def to_Aut (α : Type u) [monoid α] : units α ≃* category_theory.Aut (category_theory.single_obj.star α) :=
  mul_equiv.trans (map_equiv (category_theory.single_obj.to_End α))
    (category_theory.Aut.units_End_equiv_Aut (category_theory.single_obj.star α))

@[simp] theorem to_Aut_hom (α : Type u) [monoid α] (x : units α) : category_theory.iso.hom (coe_fn (to_Aut α) x) = coe_fn (category_theory.single_obj.to_End α) ↑x :=
  rfl

@[simp] theorem to_Aut_inv (α : Type u) [monoid α] (x : units α) : category_theory.iso.inv (coe_fn (to_Aut α) x) = coe_fn (category_theory.single_obj.to_End α) ↑(x⁻¹) :=
  rfl

end units


namespace Mon


/-- The fully faithful functor from `Mon` to `Cat`. -/
def to_Cat : Mon ⥤ category_theory.Cat :=
  category_theory.functor.mk (fun (x : Mon) => category_theory.Cat.of (category_theory.single_obj ↥x))
    fun (x y : Mon) (f : x ⟶ y) => coe_fn (category_theory.single_obj.map_hom ↥x ↥y) f

protected instance to_Cat_full : category_theory.full to_Cat :=
  category_theory.full.mk fun (x y : Mon) => equiv.inv_fun (category_theory.single_obj.map_hom ↥x ↥y)

protected instance to_Cat_faithful : category_theory.faithful to_Cat :=
  category_theory.faithful.mk

