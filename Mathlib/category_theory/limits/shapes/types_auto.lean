/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.limits.types
import Mathlib.category_theory.limits.shapes.products
import Mathlib.category_theory.limits.shapes.binary_products
import Mathlib.category_theory.limits.shapes.terminal
import Mathlib.PostPort

universes u 

namespace Mathlib

/-!
# Special shapes for limits in `Type`.

The general shape (co)limits defined in `category_theory.limits.types`
are intended for use through the limits API,
and the actual implementation should mostly be considered "sealed".

In this file, we provide definitions of the "standard" special shapes of limits in `Type`,
giving the expected definitional implementation:
* the terminal object is `punit`
* the binary product of `X` and `Y` is `X × Y`
* the product of a family `f : J → Type` is `Π j, f j`.

Because these are not intended for use with the `has_limit` API,
we instead construct terms of `limit_data`.

As an example, when setting up the monoidal category structure on `Type`
we use the `types_has_terminal` and `types_has_binary_products` instances.
-/

namespace category_theory.limits.types


/-- A restatement of `types.lift_π_apply` that uses `pi.π` and `pi.lift`. -/
@[simp] theorem pi_lift_π_apply {β : Type u} (f : β → Type u) {P : Type u} (s : (b : β) → P ⟶ f b)
    (b : β) (x : P) : pi.π f b (pi.lift s x) = s b x :=
  congr_fun (limit.lift_π (fan.mk P s) b) x

/-- A restatement of `types.map_π_apply` that uses `pi.π` and `pi.map`. -/
@[simp] theorem pi_map_π_apply {β : Type u} {f : β → Type u} {g : β → Type u}
    (α : (j : β) → f j ⟶ g j) (b : β) (x : ∏ fun (j : β) => f j) :
    pi.π g b (pi.map α x) = α b (pi.π f b x) :=
  limit.map_π_apply (discrete.nat_trans α) b x

/-- The category of types has `punit` as a terminal object. -/
def terminal_limit_cone : limit_cone (functor.empty (Type u)) :=
  limit_cone.mk (cone.mk PUnit (nat_trans.mk sorry)) (id (is_limit.mk sorry))

/-- The category of types has `pempty` as an initial object. -/
def initial_limit_cone : colimit_cocone (functor.empty (Type u)) :=
  colimit_cocone.mk (cocone.mk pempty (nat_trans.mk sorry)) (id (is_colimit.mk sorry))

/-- The product type `X × Y` forms a cone for the binary product of `X` and `Y`. -/
-- We manually generate the other projection lemmas since the simp-normal form for the legs is

-- otherwise not created correctly.

@[simp] theorem binary_product_cone_X (X : Type u) (Y : Type u) :
    cone.X (binary_product_cone X Y) = (X × Y) :=
  Eq.refl (X × Y)

@[simp] theorem binary_product_cone_fst (X : Type u) (Y : Type u) :
    binary_fan.fst (binary_product_cone X Y) = prod.fst :=
  rfl

@[simp] theorem binary_product_cone_snd (X : Type u) (Y : Type u) :
    binary_fan.snd (binary_product_cone X Y) = prod.snd :=
  rfl

/-- The product type `X × Y` is a binary product for `X` and `Y`. -/
@[simp] theorem binary_product_limit_lift (X : Type u) (Y : Type u) (s : binary_fan X Y)
    (x : cone.X s) :
    is_limit.lift (binary_product_limit X Y) s x = (binary_fan.fst s x, binary_fan.snd s x) :=
  Eq.refl (is_limit.lift (binary_product_limit X Y) s x)

/--
The category of types has `X × Y`, the usual cartesian product,
as the binary product of `X` and `Y`.
-/
@[simp] theorem binary_product_limit_cone_is_limit (X : Type u) (Y : Type u) :
    limit_cone.is_limit (binary_product_limit_cone X Y) = binary_product_limit X Y :=
  Eq.refl (limit_cone.is_limit (binary_product_limit_cone X Y))

/-- The functor which sends `X, Y` to the product type `X × Y`. -/
-- We add the option `type_md` to tell `@[simps]` to not treat homomorphisms `X ⟶ Y` in `Type*` as

-- a function type

@[simp] theorem binary_product_functor_obj_map (X : Type u) (Y₁ : Type u) (Y₂ : Type u)
    (f : Y₁ ⟶ Y₂) :
    functor.map (functor.obj binary_product_functor X) f =
        is_limit.lift (binary_product_limit X Y₂) (binary_fan.mk prod.fst (prod.snd ≫ f)) :=
  Eq.refl (functor.map (functor.obj binary_product_functor X) f)

/--
The product functor given by the instance `has_binary_products (Type u)` is isomorphic to the
explicit binary product functor given by the product type.
-/
def binary_product_iso_prod : binary_product_functor ≅ prod.functor :=
  nat_iso.of_components
    (fun (X : Type u) =>
      nat_iso.of_components
        (fun (Y : Type u) =>
          iso.symm
            (is_limit.cone_point_unique_up_to_iso (limit.is_limit (pair X Y))
              (binary_product_limit X Y)))
        sorry)
    sorry

/-- The sum type `X ⊕ Y` forms a cocone for the binary coproduct of `X` and `Y`. -/
@[simp] theorem binary_coproduct_cocone_ι_app (X : Type u) (Y : Type u)
    (j : discrete walking_pair) :
    ∀ (ᾰ : functor.obj (pair X Y) j),
        nat_trans.app (cocone.ι (binary_coproduct_cocone X Y)) j ᾰ =
          walking_pair.rec sum.inl sum.inr j ᾰ :=
  fun (ᾰ : functor.obj (pair X Y) j) => Eq.refl (walking_pair.rec sum.inl sum.inr j ᾰ)

/-- The sum type `X ⊕ Y` is a binary coproduct for `X` and `Y`. -/
def binary_coproduct_colimit (X : Type u) (Y : Type u) : is_colimit (binary_coproduct_cocone X Y) :=
  is_colimit.mk fun (s : binary_cofan X Y) => sum.elim (binary_cofan.inl s) (binary_cofan.inr s)

/--
The category of types has `X ⊕ Y`,
as the binary coproduct of `X` and `Y`.
-/
def binary_coproduct_colimit_cocone (X : Type u) (Y : Type u) : colimit_cocone (pair X Y) :=
  colimit_cocone.mk (binary_coproduct_cocone X Y) (binary_coproduct_colimit X Y)

/--
The category of types has `Π j, f j` as the product of a type family `f : J → Type`.
-/
def product_limit_cone {J : Type u} (F : J → Type u) : limit_cone (discrete.functor F) :=
  limit_cone.mk
    (cone.mk ((j : J) → F j)
      (nat_trans.mk
        fun (j : discrete J)
          (f : functor.obj (functor.obj (functor.const (discrete J)) ((j : J) → F j)) j) => f j))
    (is_limit.mk
      fun (s : cone (discrete.functor F)) (x : cone.X s) (j : J) => nat_trans.app (cone.π s) j x)

/--
The category of types has `Σ j, f j` as the coproduct of a type family `f : J → Type`.
-/
def coproduct_colimit_cocone {J : Type u} (F : J → Type u) : colimit_cocone (discrete.functor F) :=
  colimit_cocone.mk
    (cocone.mk (sigma fun (j : J) => F j)
      (nat_trans.mk fun (j : discrete J) (x : functor.obj (discrete.functor F) j) => sigma.mk j x))
    (is_colimit.mk
      fun (s : cocone (discrete.functor F))
        (x :
        cocone.X
          (cocone.mk (sigma fun (j : J) => F j)
            (nat_trans.mk
              fun (j : discrete J) (x : functor.obj (discrete.functor F) j) => sigma.mk j x))) =>
        nat_trans.app (cocone.ι s) (sigma.fst x) (sigma.snd x))

/--
Show the given fork in `Type u` is an equalizer given that any element in the "difference kernel"
comes from `X`.
The converse of `unique_of_type_equalizer`.
-/
def type_equalizer_of_unique {X : Type u} {Y : Type u} {Z : Type u} (f : X ⟶ Y) {g : Y ⟶ Z}
    {h : Y ⟶ Z} (w : f ≫ g = f ≫ h)
    (t : ∀ (y : Y), g y = h y → exists_unique fun (x : X) => f x = y) : is_limit (fork.of_ι f w) :=
  fork.is_limit.mk' (fork.of_ι f w)
    fun (s : fork g h) =>
      { val :=
          fun
            (i :
            functor.obj (functor.obj (functor.const walking_parallel_pair) (cone.X s))
              walking_parallel_pair.zero) =>
            classical.some sorry,
        property := sorry }

/-- The converse of `type_equalizer_of_unique`. -/
theorem unique_of_type_equalizer {X : Type u} {Y : Type u} {Z : Type u} (f : X ⟶ Y) {g : Y ⟶ Z}
    {h : Y ⟶ Z} (w : f ≫ g = f ≫ h) (t : is_limit (fork.of_ι f w)) (y : Y) (hy : g y = h y) :
    exists_unique fun (x : X) => f x = y :=
  sorry

theorem type_equalizer_iff_unique {X : Type u} {Y : Type u} {Z : Type u} (f : X ⟶ Y) {g : Y ⟶ Z}
    {h : Y ⟶ Z} (w : f ≫ g = f ≫ h) :
    Nonempty (is_limit (fork.of_ι f w)) ↔
        ∀ (y : Y), g y = h y → exists_unique fun (x : X) => f x = y :=
  sorry

/-- Show that the subtype `{x : Y // g x = h x}` is an equalizer for the pair `(g,h)`. -/
def equalizer_limit {Y : Type u} {Z : Type u} {g : Y ⟶ Z} {h : Y ⟶ Z} :
    limit_cone (parallel_pair g h) :=
  limit_cone.mk (fork.of_ι subtype.val sorry)
    (fork.is_limit.mk' (fork.of_ι subtype.val sorry)
      fun (s : fork g h) =>
        { val :=
            fun
              (i :
              functor.obj (functor.obj (functor.const walking_parallel_pair) (cone.X s))
                walking_parallel_pair.zero) =>
              { val := fork.ι s i, property := sorry },
          property := sorry })

end Mathlib