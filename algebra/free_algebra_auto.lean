/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Scott Morrison, Adam Topaz.
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.algebra.subalgebra
import Mathlib.algebra.monoid_algebra
import Mathlib.linear_algebra.default
import Mathlib.data.equiv.transfer_instance
import PostPort

universes u_1 u_2 l u_3 

namespace Mathlib

/-!
# Free Algebras

Given a commutative semiring `R`, and a type `X`, we construct the free `R`-algebra on `X`.

## Notation

1. `free_algebra R X` is the free algebra itself. It is endowed with an `R`-algebra structure.
2. `free_algebra.ι R` is the function `X → free_algebra R X`.
3. Given a function `f : X → A` to an R-algebra `A`, `lift R f` is the lift of `f` to an
  `R`-algebra morphism `free_algebra R X → A`.

## Theorems

1. `ι_comp_lift` states that the composition `(lift R f) ∘ (ι R)` is identical to `f`.
2. `lift_unique` states that whenever an R-algebra morphism `g : free_algebra R X → A` is
  given whose composition with `ι R` is `f`, then one has `g = lift R f`.
3. `hom_ext` is a variant of `lift_unique` in the form of an extensionality theorem.
4. `lift_comp_ι` is a combination of `ι_comp_lift` and `lift_unique`. It states that the lift
  of the composition of an algebra morphism with `ι` is the algebra morphism itself.
5. `equiv_monoid_algebra_free_monoid : free_algebra R X ≃ₐ[R] monoid_algebra R (free_monoid X)`
6. An inductive principle `induction`.

## Implementation details

We construct the free algebra on `X` as a quotient of an inductive type `free_algebra.pre` by an
inductively defined relation `free_algebra.rel`. Explicitly, the construction involves three steps:
1. We construct an inductive type `free_algebra.pre R X`, the terms of which should be thought
  of as representatives for the elements of `free_algebra R X`.
  It is the free type with maps from `R` and `X`, and with two binary operations `add` and `mul`.
2. We construct an inductive relation `free_algebra.rel R X` on `free_algebra.pre R X`.
  This is the smallest relation for which the quotient is an `R`-algebra where addition resp.
  multiplication are induced by `add` resp. `mul` from 1., and for which the map from `R` is the
  structure map for the algebra.
3. The free algebra `free_algebra R X` is the quotient of `free_algebra.pre R X` by
  the relation `free_algebra.rel R X`.
-/

namespace free_algebra


/--
This inductive type is used to express representatives of the free algebra.
-/
inductive pre (R : Type u_1) [comm_semiring R] (X : Type u_2) 
where
| of : X → pre R X
| of_scalar : R → pre R X
| add : pre R X → pre R X → pre R X
| mul : pre R X → pre R X → pre R X

namespace pre


protected instance inhabited (R : Type u_1) [comm_semiring R] (X : Type u_2) : Inhabited (pre R X) :=
  { default := of_scalar 0 }

-- Note: These instances are only used to simplify the notation.

/-- Coercion from `X` to `pre R X`. Note: Used for notation only. -/
/-- Coercion from `R` to `pre R X`. Note: Used for notation only. -/
def has_coe_generator (R : Type u_1) [comm_semiring R] (X : Type u_2) : has_coe X (pre R X) :=
  has_coe.mk of

/-- Multiplication in `pre R X` defined as `pre.mul`. Note: Used for notation only. -/
def has_coe_semiring (R : Type u_1) [comm_semiring R] (X : Type u_2) : has_coe R (pre R X) :=
  has_coe.mk of_scalar

/-- Addition in `pre R X` defined as `pre.add`. Note: Used for notation only. -/
def has_mul (R : Type u_1) [comm_semiring R] (X : Type u_2) : Mul (pre R X) :=
  { mul := mul }

/-- Zero in `pre R X` defined as the image of `0` from `R`. Note: Used for notation only. -/
def has_add (R : Type u_1) [comm_semiring R] (X : Type u_2) : Add (pre R X) :=
  { add := add }

/-- One in `pre R X` defined as the image of `1` from `R`. Note: Used for notation only. -/
def has_zero (R : Type u_1) [comm_semiring R] (X : Type u_2) : HasZero (pre R X) :=
  { zero := of_scalar 0 }

/--
def has_one (R : Type u_1) [comm_semiring R] (X : Type u_2) : HasOne (pre R X) :=
  { one := of_scalar 1 }

Scalar multiplication defined as multiplication by the image of elements from `R`.
Note: Used for notation only.
-/
def has_scalar (R : Type u_1) [comm_semiring R] (X : Type u_2) : has_scalar R (pre R X) :=
  has_scalar.mk fun (r : R) (m : pre R X) => mul (of_scalar r) m

end pre


/--
Given a function from `X` to an `R`-algebra `A`, `lift_fun` provides a lift of `f` to a function
from `pre R X` to `A`. This is mainly used in the construction of `free_algebra.lift`.
-/
def lift_fun (R : Type u_1) [comm_semiring R] (X : Type u_2) {A : Type u_3} [semiring A] [algebra R A] (f : X → A) : pre R X → A :=
  fun (t : pre R X) =>
    pre.rec_on t f (⇑(algebra_map R A)) (fun (_x _x : pre R X) => Add.add) fun (_x _x : pre R X) => Mul.mul

/--
An inductively defined relation on `pre R X` used to force the initial algebra structure on
the associated quotient.
-/
-- force `of_scalar` to be a central semiring morphism

inductive rel (R : Type u_1) [comm_semiring R] (X : Type u_2) : pre R X → pre R X → Prop
where
| add_scalar : ∀ {r s : R}, rel R X (↑(r + s)) (↑r + ↑s)
| mul_scalar : ∀ {r s : R}, rel R X (↑(r * s)) (↑r * ↑s)
| central_scalar : ∀ {r : R} {a : pre R X}, rel R X (↑r * a) (a * ↑r)
| add_assoc : ∀ {a b c : pre R X}, rel R X (a + b + c) (a + (b + c))
| add_comm : ∀ {a b : pre R X}, rel R X (a + b) (b + a)
| zero_add : ∀ {a : pre R X}, rel R X (0 + a) a
| mul_assoc : ∀ {a b c : pre R X}, rel R X (a * b * c) (a * (b * c))
| one_mul : ∀ {a : pre R X}, rel R X (1 * a) a
| mul_one : ∀ {a : pre R X}, rel R X (a * 1) a
| left_distrib : ∀ {a b c : pre R X}, rel R X (a * (b + c)) (a * b + a * c)
| right_distrib : ∀ {a b c : pre R X}, rel R X ((a + b) * c) (a * c + b * c)
| zero_mul : ∀ {a : pre R X}, rel R X (0 * a) 0
| mul_zero : ∀ {a : pre R X}, rel R X (a * 0) 0
| add_compat_left : ∀ {a b c : pre R X}, rel R X a b → rel R X (a + c) (b + c)
| add_compat_right : ∀ {a b c : pre R X}, rel R X a b → rel R X (c + a) (c + b)
| mul_compat_left : ∀ {a b c : pre R X}, rel R X a b → rel R X (a * c) (b * c)
| mul_compat_right : ∀ {a b c : pre R X}, rel R X a b → rel R X (c * a) (c * b)

-- commutative additive semigroup

-- multiplicative monoid

-- distributivity

-- other relations needed for semiring

-- compatibility

end free_algebra


/--
The free algebra for the type `X` over the commutative semiring `R`.
-/
def free_algebra (R : Type u_1) [comm_semiring R] (X : Type u_2)  :=
  Quot sorry

namespace free_algebra


protected instance semiring (R : Type u_1) [comm_semiring R] (X : Type u_2) : semiring (free_algebra R X) :=
  semiring.mk (quot.map₂ Add.add sorry sorry) sorry (Quot.mk (rel R X) 0) sorry sorry sorry
    (quot.map₂ Mul.mul sorry sorry) sorry (Quot.mk (rel R X) 1) sorry sorry sorry sorry sorry sorry

protected instance inhabited (R : Type u_1) [comm_semiring R] (X : Type u_2) : Inhabited (free_algebra R X) :=
  { default := 0 }

protected instance has_scalar (R : Type u_1) [comm_semiring R] (X : Type u_2) : has_scalar R (free_algebra R X) :=
  has_scalar.mk
    fun (r : R) (a : free_algebra R X) => quot.lift_on a (fun (x : pre R X) => Quot.mk (rel R X) (↑r * x)) sorry

protected instance algebra (R : Type u_1) [comm_semiring R] (X : Type u_2) : algebra R (free_algebra R X) :=
  algebra.mk (ring_hom.mk (fun (r : R) => Quot.mk (rel R X) ↑r) sorry sorry sorry sorry) sorry sorry

protected instance ring (X : Type u_2) {S : Type u_1} [comm_ring S] : ring (free_algebra S X) :=
  algebra.semiring_to_ring S

/--
The canonical function `X → free_algebra R X`.
-/
def ι (R : Type u_1) [comm_semiring R] {X : Type u_2} : X → free_algebra R X :=
  fun (m : X) => Quot.mk (rel R X) ↑m

@[simp] theorem quot_mk_eq_ι (R : Type u_1) [comm_semiring R] {X : Type u_2} (m : X) : Quot.mk (rel R X) ↑m = ι R m :=
  rfl

/-- Internal definition used to define `lift` -/
/--
Given a function `f : X → A` where `A` is an `R`-algebra, `lift R f` is the unique lift
of `f` to a morphism of `R`-algebras `free_algebra R X → A`.
-/
def lift (R : Type u_1) [comm_semiring R] {X : Type u_2} {A : Type u_3} [semiring A] [algebra R A] : (X → A) ≃ alg_hom R (free_algebra R X) A :=
  equiv.mk (lift_aux R) (fun (F : alg_hom R (free_algebra R X) A) => ⇑F ∘ ι R) sorry sorry

@[simp] theorem lift_aux_eq (R : Type u_1) [comm_semiring R] {X : Type u_2} {A : Type u_3} [semiring A] [algebra R A] (f : X → A) : lift_aux R f = coe_fn (lift R) f :=
  rfl

@[simp] theorem lift_symm_apply (R : Type u_1) [comm_semiring R] {X : Type u_2} {A : Type u_3} [semiring A] [algebra R A] (F : alg_hom R (free_algebra R X) A) : coe_fn (equiv.symm (lift R)) F = ⇑F ∘ ι R :=
  rfl

@[simp] theorem ι_comp_lift {R : Type u_1} [comm_semiring R] {X : Type u_2} {A : Type u_3} [semiring A] [algebra R A] (f : X → A) : ⇑(coe_fn (lift R) f) ∘ ι R = f :=
  funext fun (x : X) => Eq.refl (function.comp (⇑(coe_fn (lift R) f)) (ι R) x)

@[simp] theorem lift_ι_apply {R : Type u_1} [comm_semiring R] {X : Type u_2} {A : Type u_3} [semiring A] [algebra R A] (f : X → A) (x : X) : coe_fn (coe_fn (lift R) f) (ι R x) = f x :=
  rfl

@[simp] theorem lift_unique {R : Type u_1} [comm_semiring R] {X : Type u_2} {A : Type u_3} [semiring A] [algebra R A] (f : X → A) (g : alg_hom R (free_algebra R X) A) : ⇑g ∘ ι R = f ↔ g = coe_fn (lift R) f :=
  equiv.symm_apply_eq (lift R)

/-!
At this stage we set the basic definitions as `@[irreducible]`, so from this point onwards one
should only use the universal properties of the free algebra, and consider the actual implementation
as a quotient of an inductive type as completely hidden.

Of course, one still has the option to locally make these definitions `semireducible` if so desired,
and Lean is still willing in some circumstances to do unification based on the underlying
definition.
-/

-- Marking `free_algebra` irreducible makes `ring` instances inaccessible on quotients.

-- https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/algebra.2Esemiring_to_ring.20breaks.20semimodule.20typeclass.20lookup/near/212580241

-- For now, we avoid this by not marking it irreducible.

@[simp] theorem lift_comp_ι {R : Type u_1} [comm_semiring R] {X : Type u_2} {A : Type u_3} [semiring A] [algebra R A] (g : alg_hom R (free_algebra R X) A) : coe_fn (lift R) (⇑g ∘ ι R) = g :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn (lift R) (⇑g ∘ ι R) = g)) (Eq.symm (lift_symm_apply R g))))
    (equiv.apply_symm_apply (lift R) g)

/-- See note [partially-applied ext lemmas]. -/
theorem hom_ext {R : Type u_1} [comm_semiring R] {X : Type u_2} {A : Type u_3} [semiring A] [algebra R A] {f : alg_hom R (free_algebra R X) A} {g : alg_hom R (free_algebra R X) A} (w : ⇑f ∘ ι R = ⇑g ∘ ι R) : f = g :=
  equiv.injective (equiv.symm (lift R))
    (eq.mp (Eq._oldrec (Eq.refl (coe_fn (equiv.symm (lift R)) f = ⇑g ∘ ι R)) (Eq.symm (lift_symm_apply R g)))
      (eq.mp (Eq._oldrec (Eq.refl (⇑f ∘ ι R = ⇑g ∘ ι R)) (Eq.symm (lift_symm_apply R f))) w))

/--
The free algebra on `X` is "just" the monoid algebra on the free monoid on `X`.

This would be useful when constructing linear maps out of a free algebra,
for example.
-/
def equiv_monoid_algebra_free_monoid {R : Type u_1} [comm_semiring R] {X : Type u_2} : alg_equiv R (free_algebra R X) (monoid_algebra R (free_monoid X)) :=
  alg_equiv.of_alg_hom (coe_fn (lift R) fun (x : X) => coe_fn (monoid_algebra.of R (free_monoid X)) (free_monoid.of x))
    (coe_fn (monoid_algebra.lift R (free_monoid X) (free_algebra R X)) (coe_fn free_monoid.lift (ι R))) sorry sorry

protected instance nontrivial {R : Type u_1} [comm_semiring R] {X : Type u_2} [nontrivial R] : nontrivial (free_algebra R X) :=
  equiv.nontrivial (alg_equiv.to_equiv equiv_monoid_algebra_free_monoid)

/-- The left-inverse of `algebra_map`. -/
def algebra_map_inv {R : Type u_1} [comm_semiring R] {X : Type u_2} : alg_hom R (free_algebra R X) R :=
  coe_fn (lift R) 0

theorem algebra_map_left_inverse {R : Type u_1} [comm_semiring R] {X : Type u_2} : function.left_inverse ⇑algebra_map_inv ⇑(algebra_map R (free_algebra R X)) := sorry

-- this proof is copied from the approach in `free_abelian_group.of_injective`

theorem ι_injective {R : Type u_1} [comm_semiring R] {X : Type u_2} [nontrivial R] : function.injective (ι R) := sorry

end free_algebra


/- There is something weird in the above namespace that breaks the typeclass resolution of
`has_coe_to_sort` below. Closing it and reopening it fixes it... -/

namespace free_algebra


/-- An induction principle for the free algebra.

If `C` holds for the `algebra_map` of `r : R` into `free_algebra R X`, the `ι` of `x : X`, and is
preserved under addition and muliplication, then it holds for all of `free_algebra R X`.
-/
theorem induction (R : Type u_1) [comm_semiring R] (X : Type u_2) {C : free_algebra R X → Prop} (h_grade0 : ∀ (r : R), C (coe_fn (algebra_map R (free_algebra R X)) r)) (h_grade1 : ∀ (x : X), C (ι R x)) (h_mul : ∀ (a b : free_algebra R X), C a → C b → C (a * b)) (h_add : ∀ (a b : free_algebra R X), C a → C b → C (a + b)) (a : free_algebra R X) : C a := sorry

/-- The star ring formed by reversing the elements of products -/
protected instance star_ring (R : Type u_1) [comm_semiring R] (X : Type u_2) : star_ring (free_algebra R X) :=
  star_ring.mk sorry

@[simp] theorem star_ι (R : Type u_1) [comm_semiring R] (X : Type u_2) (x : X) : star (ι R x) = ι R x := sorry

@[simp] theorem star_algebra_map (R : Type u_1) [comm_semiring R] (X : Type u_2) (r : R) : star (coe_fn (algebra_map R (free_algebra R X)) r) = coe_fn (algebra_map R (free_algebra R X)) r := sorry

/-- `star` as an `alg_equiv` -/
def star_hom (R : Type u_1) [comm_semiring R] (X : Type u_2) : alg_equiv R (free_algebra R X) (free_algebra R Xᵒᵖ) :=
  alg_equiv.mk (ring_equiv.to_fun star_ring_equiv) (ring_equiv.inv_fun star_ring_equiv) sorry sorry sorry sorry sorry

