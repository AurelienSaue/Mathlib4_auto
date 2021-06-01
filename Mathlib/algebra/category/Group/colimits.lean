/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.category.Group.preadditive
import Mathlib.group_theory.quotient_group
import Mathlib.category_theory.limits.limits
import Mathlib.category_theory.limits.concrete_category
import Mathlib.category_theory.limits.shapes.kernels
import Mathlib.category_theory.limits.shapes.concrete_category
import Mathlib.PostPort

universes v l u_1 

namespace Mathlib

/-!
# The category of additive commutative groups has all colimits.

This file uses a "pre-automated" approach, just as for `Mon/colimits.lean`.
It is a very uniform approach, that conceivably could be synthesised directly
by a tactic that analyses the shape of `add_comm_group` and `monoid_hom`.

TODO:
In fact, in `AddCommGroup` there is a much nicer model of colimits as quotients
of finitely supported functions, and we really should implement this as well (or instead).
-/

-- [ROBOT VOICE]:

-- You should pretend for now that this file was automatically generated.

-- It follows the same template as colimits in Mon.

namespace AddCommGroup.colimits


/-!
We build the colimit of a diagram in `AddCommGroup` by constructing the
free group on the disjoint union of all the abelian groups in the diagram,
then taking the quotient by the abelian group laws within each abelian group,
and the identifications given by the morphisms in the diagram.
-/

/--
An inductive type representing all group expressions (without relations)
on a collection of types indexed by the objects of `J`.
-/
-- There's always `of`

inductive prequotient {J : Type v} [category_theory.small_category J] (F : J ⥤ AddCommGroup) 
where
| of : (j : J) → ↥(category_theory.functor.obj F j) → prequotient F
| zero : prequotient F
| neg : prequotient F → prequotient F
| add : prequotient F → prequotient F → prequotient F

-- Then one generator for each operation

protected instance prequotient.inhabited {J : Type v} [category_theory.small_category J] (F : J ⥤ AddCommGroup) : Inhabited (prequotient F) :=
  { default := prequotient.zero }

/--
The relation on `prequotient` saying when two expressions are equal
because of the abelian group laws, or
because one element is mapped to another by a morphism in the diagram.
-/
-- Make it an equivalence relation:

inductive relation {J : Type v} [category_theory.small_category J] (F : J ⥤ AddCommGroup) : prequotient F → prequotient F → Prop
where
| refl : ∀ (x : prequotient F), relation F x x
| symm : ∀ (x y : prequotient F), relation F x y → relation F y x
| trans : ∀ (x y z : prequotient F), relation F x y → relation F y z → relation F x z
| map : ∀ (j j' : J) (f : j ⟶ j') (x : ↥(category_theory.functor.obj F j)),
  relation F (prequotient.of j' (coe_fn (category_theory.functor.map F f) x)) (prequotient.of j x)
| zero : ∀ (j : J), relation F (prequotient.of j 0) prequotient.zero
| neg : ∀ (j : J) (x : ↥(category_theory.functor.obj F j)),
  relation F (prequotient.of j (-x)) (prequotient.neg (prequotient.of j x))
| add : ∀ (j : J) (x y : ↥(category_theory.functor.obj F j)),
  relation F (prequotient.of j (x + y)) (prequotient.add (prequotient.of j x) (prequotient.of j y))
| neg_1 : ∀ (x x' : prequotient F), relation F x x' → relation F (prequotient.neg x) (prequotient.neg x')
| add_1 : ∀ (x x' y : prequotient F), relation F x x' → relation F (prequotient.add x y) (prequotient.add x' y)
| add_2 : ∀ (x y y' : prequotient F), relation F y y' → relation F (prequotient.add x y) (prequotient.add x y')
| zero_add : ∀ (x : prequotient F), relation F (prequotient.add prequotient.zero x) x
| add_zero : ∀ (x : prequotient F), relation F (prequotient.add x prequotient.zero) x
| add_left_neg : ∀ (x : prequotient F), relation F (prequotient.add (prequotient.neg x) x) prequotient.zero
| add_comm : ∀ (x y : prequotient F), relation F (prequotient.add x y) (prequotient.add y x)
| add_assoc : ∀ (x y z : prequotient F),
  relation F (prequotient.add (prequotient.add x y) z) (prequotient.add x (prequotient.add y z))

-- There's always a `map` relation

-- Then one relation per operation, describing the interaction with `of`

-- Then one relation per argument of each operation

-- And one relation per axiom

/--
The setoid corresponding to group expressions modulo abelian group relations and identifications.
-/
instance colimit_setoid {J : Type v} [category_theory.small_category J] (F : J ⥤ AddCommGroup) : setoid (prequotient F) :=
  setoid.mk (relation F) sorry

/--
The underlying type of the colimit of a diagram in `AddCommGroup`.
-/
def colimit_type {J : Type v} [category_theory.small_category J] (F : J ⥤ AddCommGroup) :=
  quotient (colimit_setoid F)

protected instance colimit_type.add_comm_group {J : Type v} [category_theory.small_category J] (F : J ⥤ AddCommGroup) : add_comm_group (colimit_type F) :=
  add_comm_group.mk
    (Quot.lift
      (fun (x : prequotient F) => Quot.lift (fun (y : prequotient F) => Quot.mk setoid.r (prequotient.add x y)) sorry)
      sorry)
    sorry (Quot.mk setoid.r prequotient.zero) sorry sorry
    (Quot.lift (fun (x : prequotient F) => Quot.mk setoid.r (prequotient.neg x)) sorry)
    (add_group.sub._default
      (Quot.lift
        (fun (x : prequotient F) => Quot.lift (fun (y : prequotient F) => Quot.mk setoid.r (prequotient.add x y)) sorry)
        sorry)
      sorry (Quot.mk setoid.r prequotient.zero) sorry sorry
      (Quot.lift (fun (x : prequotient F) => Quot.mk setoid.r (prequotient.neg x)) sorry))
    sorry sorry

@[simp] theorem quot_zero {J : Type v} [category_theory.small_category J] (F : J ⥤ AddCommGroup) : Quot.mk setoid.r prequotient.zero = 0 :=
  rfl

@[simp] theorem quot_neg {J : Type v} [category_theory.small_category J] (F : J ⥤ AddCommGroup) (x : prequotient F) : Quot.mk setoid.r (prequotient.neg x) = -Quot.mk setoid.r x :=
  rfl

@[simp] theorem quot_add {J : Type v} [category_theory.small_category J] (F : J ⥤ AddCommGroup) (x : prequotient F) (y : prequotient F) : Quot.mk setoid.r (prequotient.add x y) = Quot.mk setoid.r x + Quot.mk setoid.r y :=
  rfl

/-- The bundled abelian group giving the colimit of a diagram. -/
def colimit {J : Type v} [category_theory.small_category J] (F : J ⥤ AddCommGroup) : AddCommGroup :=
  of (colimit_type F)

/-- The function from a given abelian group in the diagram to the colimit abelian group. -/
def cocone_fun {J : Type v} [category_theory.small_category J] (F : J ⥤ AddCommGroup) (j : J) (x : ↥(category_theory.functor.obj F j)) : colimit_type F :=
  Quot.mk setoid.r (prequotient.of j x)

/-- The group homomorphism from a given abelian group in the diagram to the colimit abelian
group. -/
def cocone_morphism {J : Type v} [category_theory.small_category J] (F : J ⥤ AddCommGroup) (j : J) : category_theory.functor.obj F j ⟶ colimit F :=
  add_monoid_hom.mk (cocone_fun F j) sorry sorry

@[simp] theorem cocone_naturality {J : Type v} [category_theory.small_category J] (F : J ⥤ AddCommGroup) {j : J} {j' : J} (f : j ⟶ j') : category_theory.functor.map F f ≫ cocone_morphism F j' = cocone_morphism F j :=
  ext (category_theory.functor.obj F j) (colimit F) (category_theory.functor.map F f ≫ cocone_morphism F j')
    (cocone_morphism F j) fun (x : ↥(category_theory.functor.obj F j)) => quot.sound (relation.map j j' f x)

@[simp] theorem cocone_naturality_components {J : Type v} [category_theory.small_category J] (F : J ⥤ AddCommGroup) (j : J) (j' : J) (f : j ⟶ j') (x : ↥(category_theory.functor.obj F j)) : coe_fn (cocone_morphism F j') (coe_fn (category_theory.functor.map F f) x) = coe_fn (cocone_morphism F j) x := sorry

/-- The cocone over the proposed colimit abelian group. -/
def colimit_cocone {J : Type v} [category_theory.small_category J] (F : J ⥤ AddCommGroup) : category_theory.limits.cocone F :=
  category_theory.limits.cocone.mk (colimit F) (category_theory.nat_trans.mk (cocone_morphism F))

/-- The function from the free abelian group on the diagram to the cone point of any other
cocone. -/
@[simp] def desc_fun_lift {J : Type v} [category_theory.small_category J] (F : J ⥤ AddCommGroup) (s : category_theory.limits.cocone F) : prequotient F → ↥(category_theory.limits.cocone.X s) :=
  sorry

/-- The function from the colimit abelian group to the cone point of any other cocone. -/
def desc_fun {J : Type v} [category_theory.small_category J] (F : J ⥤ AddCommGroup) (s : category_theory.limits.cocone F) : colimit_type F → ↥(category_theory.limits.cocone.X s) :=
  Quot.lift (desc_fun_lift F s) sorry

/-- The group homomorphism from the colimit abelian group to the cone point of any other cocone. -/
def desc_morphism {J : Type v} [category_theory.small_category J] (F : J ⥤ AddCommGroup) (s : category_theory.limits.cocone F) : colimit F ⟶ category_theory.limits.cocone.X s :=
  add_monoid_hom.mk (desc_fun F s) sorry sorry

/-- Evidence that the proposed colimit is the colimit. -/
def colimit_cocone_is_colimit {J : Type v} [category_theory.small_category J] (F : J ⥤ AddCommGroup) : category_theory.limits.is_colimit (colimit_cocone F) :=
  category_theory.limits.is_colimit.mk fun (s : category_theory.limits.cocone F) => desc_morphism F s

protected instance has_colimits_AddCommGroup : category_theory.limits.has_colimits AddCommGroup :=
  category_theory.limits.has_colimits.mk
    fun (J : Type u_1) (𝒥 : category_theory.small_category J) =>
      category_theory.limits.has_colimits_of_shape.mk
        fun (F : J ⥤ AddCommGroup) =>
          category_theory.limits.has_colimit.mk
            (category_theory.limits.colimit_cocone.mk (colimit_cocone F) (colimit_cocone_is_colimit F))

end AddCommGroup.colimits


namespace AddCommGroup


/--
The categorical cokernel of a morphism in `AddCommGroup`
agrees with the usual group-theoretical quotient.
-/
def cokernel_iso_quotient {G : AddCommGroup} {H : AddCommGroup} (f : G ⟶ H) : category_theory.limits.cokernel f ≅ of (quotient_add_group.quotient (add_monoid_hom.range f)) :=
  category_theory.iso.mk (category_theory.limits.cokernel.desc f (quotient_add_group.mk' (add_monoid_hom.range f)) sorry)
    (add_monoid_hom.of ⇑(quotient_add_group.lift (add_monoid_hom.range f) (category_theory.limits.cokernel.π f) sorry))

