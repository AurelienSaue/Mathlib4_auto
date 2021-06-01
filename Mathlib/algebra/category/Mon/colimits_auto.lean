/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.category.Mon.basic
import Mathlib.category_theory.limits.limits
import Mathlib.category_theory.limits.concrete_category
import Mathlib.PostPort

universes v l u_1 

namespace Mathlib

/-!
# The category of monoids has all colimits.

We do this construction knowing nothing about monoids.
In particular, I want to claim that this file could be produced by a python script
that just looks at the output of `#print monoid`:

  -- structure monoid : Type u → Type u
  -- fields:
  -- monoid.mul : Π {α : Type u} [c : monoid α], α → α → α
  -- monoid.mul_assoc : ∀ {α : Type u} [c : monoid α] (a b c_1 : α), a * b * c_1 = a * (b * c_1)
  -- monoid.one : Π (α : Type u) [c : monoid α], α
  -- monoid.one_mul : ∀ {α : Type u} [c : monoid α] (a : α), 1 * a = a
  -- monoid.mul_one : ∀ {α : Type u} [c : monoid α] (a : α), a * 1 = a

and if we'd fed it the output of `#print comm_ring`, this file would instead build
colimits of commutative rings.

A slightly bolder claim is that we could do this with tactics, as well.
-/

namespace Mon.colimits


/-!
We build the colimit of a diagram in `Mon` by constructing the
free monoid on the disjoint union of all the monoids in the diagram,
then taking the quotient by the monoid laws within each monoid,
and the identifications given by the morphisms in the diagram.
-/

/--
An inductive type representing all monoid expressions (without relations)
on a collection of types indexed by the objects of `J`.
-/
-- There's always `of`

inductive prequotient {J : Type v} [category_theory.small_category J] (F : J ⥤ Mon) where
| of : (j : J) → ↥(category_theory.functor.obj F j) → prequotient F
| one : prequotient F
| mul : prequotient F → prequotient F → prequotient F

-- Then one generator for each operation

protected instance prequotient.inhabited {J : Type v} [category_theory.small_category J]
    (F : J ⥤ Mon) : Inhabited (prequotient F) :=
  { default := prequotient.one }

/--
The relation on `prequotient` saying when two expressions are equal
because of the monoid laws, or
because one element is mapped to another by a morphism in the diagram.
-/
-- Make it an equivalence relation:

inductive relation {J : Type v} [category_theory.small_category J] (F : J ⥤ Mon) :
    prequotient F → prequotient F → Prop
    where
| refl : ∀ (x : prequotient F), relation F x x
| symm : ∀ (x y : prequotient F), relation F x y → relation F y x
| trans : ∀ (x y z : prequotient F), relation F x y → relation F y z → relation F x z
| map :
    ∀ (j j' : J) (f : j ⟶ j') (x : ↥(category_theory.functor.obj F j)),
      relation F (prequotient.of j' (coe_fn (category_theory.functor.map F f) x))
        (prequotient.of j x)
| mul :
    ∀ (j : J) (x y : ↥(category_theory.functor.obj F j)),
      relation F (prequotient.of j (x * y))
        (prequotient.mul (prequotient.of j x) (prequotient.of j y))
| one : ∀ (j : J), relation F (prequotient.of j 1) prequotient.one
| mul_1 :
    ∀ (x x' y : prequotient F),
      relation F x x' → relation F (prequotient.mul x y) (prequotient.mul x' y)
| mul_2 :
    ∀ (x y y' : prequotient F),
      relation F y y' → relation F (prequotient.mul x y) (prequotient.mul x y')
| mul_assoc :
    ∀ (x y z : prequotient F),
      relation F (prequotient.mul (prequotient.mul x y) z) (prequotient.mul x (prequotient.mul y z))
| one_mul : ∀ (x : prequotient F), relation F (prequotient.mul prequotient.one x) x
| mul_one : ∀ (x : prequotient F), relation F (prequotient.mul x prequotient.one) x

-- There's always a `map` relation

-- Then one relation per operation, describing the interaction with `of`

-- Then one relation per argument of each operation

-- And one relation per axiom

/--
The setoid corresponding to monoid expressions modulo monoid relations and identifications.
-/
instance colimit_setoid {J : Type v} [category_theory.small_category J] (F : J ⥤ Mon) :
    setoid (prequotient F) :=
  setoid.mk (relation F) sorry

/--
The underlying type of the colimit of a diagram in `Mon`.
-/
def colimit_type {J : Type v} [category_theory.small_category J] (F : J ⥤ Mon) :=
  quotient (colimit_setoid F)

protected instance monoid_colimit_type {J : Type v} [category_theory.small_category J]
    (F : J ⥤ Mon) : monoid (colimit_type F) :=
  monoid.mk
    (Quot.lift
      (fun (x : prequotient F) =>
        Quot.lift (fun (y : prequotient F) => Quot.mk setoid.r (prequotient.mul x y)) sorry)
      sorry)
    sorry (Quot.mk setoid.r prequotient.one) sorry sorry

@[simp] theorem quot_one {J : Type v} [category_theory.small_category J] (F : J ⥤ Mon) :
    Quot.mk setoid.r prequotient.one = 1 :=
  rfl

@[simp] theorem quot_mul {J : Type v} [category_theory.small_category J] (F : J ⥤ Mon)
    (x : prequotient F) (y : prequotient F) :
    Quot.mk setoid.r (prequotient.mul x y) = Quot.mk setoid.r x * Quot.mk setoid.r y :=
  rfl

/-- The bundled monoid giving the colimit of a diagram. -/
def colimit {J : Type v} [category_theory.small_category J] (F : J ⥤ Mon) : Mon :=
  category_theory.bundled.mk (colimit_type F)

/-- The function from a given monoid in the diagram to the colimit monoid. -/
def cocone_fun {J : Type v} [category_theory.small_category J] (F : J ⥤ Mon) (j : J)
    (x : ↥(category_theory.functor.obj F j)) : colimit_type F :=
  Quot.mk setoid.r (prequotient.of j x)

/-- The monoid homomorphism from a given monoid in the diagram to the colimit monoid. -/
def cocone_morphism {J : Type v} [category_theory.small_category J] (F : J ⥤ Mon) (j : J) :
    category_theory.functor.obj F j ⟶ colimit F :=
  monoid_hom.mk (cocone_fun F j) sorry sorry

@[simp] theorem cocone_naturality {J : Type v} [category_theory.small_category J] (F : J ⥤ Mon)
    {j : J} {j' : J} (f : j ⟶ j') :
    category_theory.functor.map F f ≫ cocone_morphism F j' = cocone_morphism F j :=
  monoid_hom.ext fun (x : ↥(category_theory.functor.obj F j)) => quot.sound (relation.map j j' f x)

@[simp] theorem cocone_naturality_components {J : Type v} [category_theory.small_category J]
    (F : J ⥤ Mon) (j : J) (j' : J) (f : j ⟶ j') (x : ↥(category_theory.functor.obj F j)) :
    coe_fn (cocone_morphism F j') (coe_fn (category_theory.functor.map F f) x) =
        coe_fn (cocone_morphism F j) x :=
  sorry

/-- The cocone over the proposed colimit monoid. -/
def colimit_cocone {J : Type v} [category_theory.small_category J] (F : J ⥤ Mon) :
    category_theory.limits.cocone F :=
  category_theory.limits.cocone.mk (colimit F) (category_theory.nat_trans.mk (cocone_morphism F))

/-- The function from the free monoid on the diagram to the cone point of any other cocone. -/
@[simp] def desc_fun_lift {J : Type v} [category_theory.small_category J] (F : J ⥤ Mon)
    (s : category_theory.limits.cocone F) : prequotient F → ↥(category_theory.limits.cocone.X s) :=
  sorry

/-- The function from the colimit monoid to the cone point of any other cocone. -/
def desc_fun {J : Type v} [category_theory.small_category J] (F : J ⥤ Mon)
    (s : category_theory.limits.cocone F) : colimit_type F → ↥(category_theory.limits.cocone.X s) :=
  Quot.lift (desc_fun_lift F s) sorry

/-- The monoid homomorphism from the colimit monoid to the cone point of any other cocone. -/
def desc_morphism {J : Type v} [category_theory.small_category J] (F : J ⥤ Mon)
    (s : category_theory.limits.cocone F) : colimit F ⟶ category_theory.limits.cocone.X s :=
  monoid_hom.mk (desc_fun F s) sorry sorry

/-- Evidence that the proposed colimit is the colimit. -/
def colimit_is_colimit {J : Type v} [category_theory.small_category J] (F : J ⥤ Mon) :
    category_theory.limits.is_colimit (colimit_cocone F) :=
  category_theory.limits.is_colimit.mk
    fun (s : category_theory.limits.cocone F) => desc_morphism F s

protected instance has_colimits_Mon : category_theory.limits.has_colimits Mon :=
  category_theory.limits.has_colimits.mk
    fun (J : Type u_1) (𝒥 : category_theory.small_category J) =>
      category_theory.limits.has_colimits_of_shape.mk
        fun (F : J ⥤ Mon) =>
          category_theory.limits.has_colimit.mk
            (category_theory.limits.colimit_cocone.mk (colimit_cocone F) (colimit_is_colimit F))

end Mathlib