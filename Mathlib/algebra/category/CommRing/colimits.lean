/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.category.CommRing.basic
import Mathlib.category_theory.limits.limits
import Mathlib.category_theory.limits.concrete_category
import Mathlib.PostPort

universes v l u_1 

namespace Mathlib

/-!
# The category of commutative rings has all colimits.

This file uses a "pre-automated" approach, just as for `Mon/colimits.lean`.
It is a very uniform approach, that conceivably could be synthesised directly
by a tactic that analyses the shape of `comm_ring` and `ring_hom`.
-/

-- [ROBOT VOICE]:

-- You should pretend for now that this file was automatically generated.

-- It follows the same template as colimits in Mon.

/-
`#print comm_ring` says:

structure comm_ring : Type u → Type u
fields:
comm_ring.zero : Π (α : Type u) [c : comm_ring α], α
comm_ring.one : Π (α : Type u) [c : comm_ring α], α
comm_ring.neg : Π {α : Type u} [c : comm_ring α], α → α
comm_ring.add : Π {α : Type u} [c : comm_ring α], α → α → α
comm_ring.mul : Π {α : Type u} [c : comm_ring α], α → α → α

comm_ring.zero_add : ∀ {α : Type u} [c : comm_ring α] (a : α), 0 + a = a
comm_ring.add_zero : ∀ {α : Type u} [c : comm_ring α] (a : α), a + 0 = a
comm_ring.one_mul : ∀ {α : Type u} [c : comm_ring α] (a : α), 1 * a = a
comm_ring.mul_one : ∀ {α : Type u} [c : comm_ring α] (a : α), a * 1 = a
comm_ring.add_left_neg : ∀ {α : Type u} [c : comm_ring α] (a : α), -a + a = 0
comm_ring.add_comm : ∀ {α : Type u} [c : comm_ring α] (a b : α), a + b = b + a
comm_ring.mul_comm : ∀ {α : Type u} [c : comm_ring α] (a b : α), a * b = b * a
comm_ring.add_assoc : ∀ {α : Type u} [c : comm_ring α] (a b c_1 : α), a + b + c_1 = a + (b + c_1)
comm_ring.mul_assoc : ∀ {α : Type u} [c : comm_ring α] (a b c_1 : α), a * b * c_1 = a * (b * c_1)
comm_ring.left_distrib : ∀ {α : Type u} [c : comm_ring α] (a b c_1 : α), a * (b + c_1) = a * b + a * c_1
comm_ring.right_distrib : ∀ {α : Type u} [c : comm_ring α] (a b c_1 : α), (a + b) * c_1 = a * c_1 + b * c_1
-/

namespace CommRing.colimits


/-!
We build the colimit of a diagram in `CommRing` by constructing the
free commutative ring on the disjoint union of all the commutative rings in the diagram,
then taking the quotient by the commutative ring laws within each commutative ring,
and the identifications given by the morphisms in the diagram.
-/

/--
An inductive type representing all commutative ring expressions (without relations)
on a collection of types indexed by the objects of `J`.
-/
-- There's always `of`

inductive prequotient {J : Type v} [category_theory.small_category J] (F : J ⥤ CommRing) 
where
| of : (j : J) → ↥(category_theory.functor.obj F j) → prequotient F
| zero : prequotient F
| one : prequotient F
| neg : prequotient F → prequotient F
| add : prequotient F → prequotient F → prequotient F
| mul : prequotient F → prequotient F → prequotient F

-- Then one generator for each operation

protected instance prequotient.inhabited {J : Type v} [category_theory.small_category J] (F : J ⥤ CommRing) : Inhabited (prequotient F) :=
  { default := prequotient.zero }

/--
The relation on `prequotient` saying when two expressions are equal
because of the commutative ring laws, or
because one element is mapped to another by a morphism in the diagram.
-/
-- Make it an equivalence relation:

inductive relation {J : Type v} [category_theory.small_category J] (F : J ⥤ CommRing) : prequotient F → prequotient F → Prop
where
| refl : ∀ (x : prequotient F), relation F x x
| symm : ∀ (x y : prequotient F), relation F x y → relation F y x
| trans : ∀ (x y z : prequotient F), relation F x y → relation F y z → relation F x z
| map : ∀ (j j' : J) (f : j ⟶ j') (x : ↥(category_theory.functor.obj F j)),
  relation F (prequotient.of j' (coe_fn (category_theory.functor.map F f) x)) (prequotient.of j x)
| zero : ∀ (j : J), relation F (prequotient.of j 0) prequotient.zero
| one : ∀ (j : J), relation F (prequotient.of j 1) prequotient.one
| neg : ∀ (j : J) (x : ↥(category_theory.functor.obj F j)),
  relation F (prequotient.of j (-x)) (prequotient.neg (prequotient.of j x))
| add : ∀ (j : J) (x y : ↥(category_theory.functor.obj F j)),
  relation F (prequotient.of j (x + y)) (prequotient.add (prequotient.of j x) (prequotient.of j y))
| mul : ∀ (j : J) (x y : ↥(category_theory.functor.obj F j)),
  relation F (prequotient.of j (x * y)) (prequotient.mul (prequotient.of j x) (prequotient.of j y))
| neg_1 : ∀ (x x' : prequotient F), relation F x x' → relation F (prequotient.neg x) (prequotient.neg x')
| add_1 : ∀ (x x' y : prequotient F), relation F x x' → relation F (prequotient.add x y) (prequotient.add x' y)
| add_2 : ∀ (x y y' : prequotient F), relation F y y' → relation F (prequotient.add x y) (prequotient.add x y')
| mul_1 : ∀ (x x' y : prequotient F), relation F x x' → relation F (prequotient.mul x y) (prequotient.mul x' y)
| mul_2 : ∀ (x y y' : prequotient F), relation F y y' → relation F (prequotient.mul x y) (prequotient.mul x y')
| zero_add : ∀ (x : prequotient F), relation F (prequotient.add prequotient.zero x) x
| add_zero : ∀ (x : prequotient F), relation F (prequotient.add x prequotient.zero) x
| one_mul : ∀ (x : prequotient F), relation F (prequotient.mul prequotient.one x) x
| mul_one : ∀ (x : prequotient F), relation F (prequotient.mul x prequotient.one) x
| add_left_neg : ∀ (x : prequotient F), relation F (prequotient.add (prequotient.neg x) x) prequotient.zero
| add_comm : ∀ (x y : prequotient F), relation F (prequotient.add x y) (prequotient.add y x)
| mul_comm : ∀ (x y : prequotient F), relation F (prequotient.mul x y) (prequotient.mul y x)
| add_assoc : ∀ (x y z : prequotient F),
  relation F (prequotient.add (prequotient.add x y) z) (prequotient.add x (prequotient.add y z))
| mul_assoc : ∀ (x y z : prequotient F),
  relation F (prequotient.mul (prequotient.mul x y) z) (prequotient.mul x (prequotient.mul y z))
| left_distrib : ∀ (x y z : prequotient F),
  relation F (prequotient.mul x (prequotient.add y z)) (prequotient.add (prequotient.mul x y) (prequotient.mul x z))
| right_distrib : ∀ (x y z : prequotient F),
  relation F (prequotient.mul (prequotient.add x y) z) (prequotient.add (prequotient.mul x z) (prequotient.mul y z))

-- There's always a `map` relation

-- Then one relation per operation, describing the interaction with `of`

-- Then one relation per argument of each operation

-- And one relation per axiom

/--
The setoid corresponding to commutative expressions modulo monoid relations and identifications.
-/
instance colimit_setoid {J : Type v} [category_theory.small_category J] (F : J ⥤ CommRing) : setoid (prequotient F) :=
  setoid.mk (relation F) sorry

/--
The underlying type of the colimit of a diagram in `CommRing`.
-/
def colimit_type {J : Type v} [category_theory.small_category J] (F : J ⥤ CommRing)  :=
  quotient (colimit_setoid F)

protected instance colimit_type.comm_ring {J : Type v} [category_theory.small_category J] (F : J ⥤ CommRing) : comm_ring (colimit_type F) :=
  comm_ring.mk
    (Quot.lift
      (fun (x : prequotient F) => Quot.lift (fun (y : prequotient F) => Quot.mk setoid.r (prequotient.add x y)) sorry)
      sorry)
    sorry (Quot.mk setoid.r prequotient.zero) sorry sorry
    (Quot.lift (fun (x : prequotient F) => Quot.mk setoid.r (prequotient.neg x)) sorry)
    (ring.sub._default
      (Quot.lift
        (fun (x : prequotient F) => Quot.lift (fun (y : prequotient F) => Quot.mk setoid.r (prequotient.add x y)) sorry)
        sorry)
      sorry (Quot.mk setoid.r prequotient.zero) sorry sorry
      (Quot.lift (fun (x : prequotient F) => Quot.mk setoid.r (prequotient.neg x)) sorry))
    sorry sorry
    (Quot.lift
      (fun (x : prequotient F) => Quot.lift (fun (y : prequotient F) => Quot.mk setoid.r (prequotient.mul x y)) sorry)
      sorry)
    sorry (Quot.mk setoid.r prequotient.one) sorry sorry sorry sorry sorry

@[simp] theorem quot_zero {J : Type v} [category_theory.small_category J] (F : J ⥤ CommRing) : Quot.mk setoid.r prequotient.zero = 0 :=
  rfl

@[simp] theorem quot_one {J : Type v} [category_theory.small_category J] (F : J ⥤ CommRing) : Quot.mk setoid.r prequotient.one = 1 :=
  rfl

@[simp] theorem quot_neg {J : Type v} [category_theory.small_category J] (F : J ⥤ CommRing) (x : prequotient F) : Quot.mk setoid.r (prequotient.neg x) = -Quot.mk setoid.r x :=
  rfl

@[simp] theorem quot_add {J : Type v} [category_theory.small_category J] (F : J ⥤ CommRing) (x : prequotient F) (y : prequotient F) : Quot.mk setoid.r (prequotient.add x y) = Quot.mk setoid.r x + Quot.mk setoid.r y :=
  rfl

@[simp] theorem quot_mul {J : Type v} [category_theory.small_category J] (F : J ⥤ CommRing) (x : prequotient F) (y : prequotient F) : Quot.mk setoid.r (prequotient.mul x y) = Quot.mk setoid.r x * Quot.mk setoid.r y :=
  rfl

/-- The bundled commutative ring giving the colimit of a diagram. -/
def colimit {J : Type v} [category_theory.small_category J] (F : J ⥤ CommRing) : CommRing :=
  of (colimit_type F)

/-- The function from a given commutative ring in the diagram to the colimit commutative ring. -/
def cocone_fun {J : Type v} [category_theory.small_category J] (F : J ⥤ CommRing) (j : J) (x : ↥(category_theory.functor.obj F j)) : colimit_type F :=
  Quot.mk setoid.r (prequotient.of j x)

/-- The ring homomorphism from a given commutative ring in the diagram to the colimit commutative
ring. -/
def cocone_morphism {J : Type v} [category_theory.small_category J] (F : J ⥤ CommRing) (j : J) : category_theory.functor.obj F j ⟶ colimit F :=
  ring_hom.mk (cocone_fun F j) sorry sorry sorry sorry

@[simp] theorem cocone_naturality {J : Type v} [category_theory.small_category J] (F : J ⥤ CommRing) {j : J} {j' : J} (f : j ⟶ j') : category_theory.functor.map F f ≫ cocone_morphism F j' = cocone_morphism F j :=
  ring_hom.ext fun (x : ↥(category_theory.functor.obj F j)) => quot.sound (relation.map j j' f x)

@[simp] theorem cocone_naturality_components {J : Type v} [category_theory.small_category J] (F : J ⥤ CommRing) (j : J) (j' : J) (f : j ⟶ j') (x : ↥(category_theory.functor.obj F j)) : coe_fn (cocone_morphism F j') (coe_fn (category_theory.functor.map F f) x) = coe_fn (cocone_morphism F j) x := sorry

/-- The cocone over the proposed colimit commutative ring. -/
def colimit_cocone {J : Type v} [category_theory.small_category J] (F : J ⥤ CommRing) : category_theory.limits.cocone F :=
  category_theory.limits.cocone.mk (colimit F) (category_theory.nat_trans.mk (cocone_morphism F))

/-- The function from the free commutative ring on the diagram to the cone point of any other
cocone. -/
@[simp] def desc_fun_lift {J : Type v} [category_theory.small_category J] (F : J ⥤ CommRing) (s : category_theory.limits.cocone F) : prequotient F → ↥(category_theory.limits.cocone.X s) :=
  sorry

/-- The function from the colimit commutative ring to the cone point of any other cocone. -/
def desc_fun {J : Type v} [category_theory.small_category J] (F : J ⥤ CommRing) (s : category_theory.limits.cocone F) : colimit_type F → ↥(category_theory.limits.cocone.X s) :=
  Quot.lift (desc_fun_lift F s) sorry

/-- The ring homomorphism from the colimit commutative ring to the cone point of any other
cocone. -/
def desc_morphism {J : Type v} [category_theory.small_category J] (F : J ⥤ CommRing) (s : category_theory.limits.cocone F) : colimit F ⟶ category_theory.limits.cocone.X s :=
  ring_hom.mk (desc_fun F s) sorry sorry sorry sorry

/-- Evidence that the proposed colimit is the colimit. -/
def colimit_is_colimit {J : Type v} [category_theory.small_category J] (F : J ⥤ CommRing) : category_theory.limits.is_colimit (colimit_cocone F) :=
  category_theory.limits.is_colimit.mk fun (s : category_theory.limits.cocone F) => desc_morphism F s

protected instance has_colimits_CommRing : category_theory.limits.has_colimits CommRing :=
  category_theory.limits.has_colimits.mk
    fun (J : Type u_1) (𝒥 : category_theory.small_category J) =>
      category_theory.limits.has_colimits_of_shape.mk
        fun (F : J ⥤ CommRing) =>
          category_theory.limits.has_colimit.mk
            (category_theory.limits.colimit_cocone.mk (colimit_cocone F) (colimit_is_colimit F))

