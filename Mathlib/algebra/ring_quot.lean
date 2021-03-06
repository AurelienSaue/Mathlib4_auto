/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.algebra.basic
import Mathlib.ring_theory.ideal.basic
import Mathlib.PostPort

universes u₁ u₂ u₃ u₄ 

namespace Mathlib

/-!
# Quotients of non-commutative rings

Unfortunately, ideals have only been developed in the commutative case as `ideal`,
and it's not immediately clear how one should formalise ideals in the non-commutative case.

In this file, we directly define the quotient of a semiring by any relation,
by building a bigger relation that represents the ideal generated by that relation.

We prove the universal properties of the quotient,
and recommend avoiding relying on the actual definition!

Since everything runs in parallel for quotients of `R`-algebras, we do that case at the same time.
-/

namespace ring_quot


/--
Given an arbitrary relation `r` on a ring, we strengthen it to a relation `rel r`,
such that the equivalence relation generated by `rel r` has `x ~ y` if and only if
`x - y` is in the ideal generated by elements `a - b` such that `r a b`.
-/
inductive rel {R : Type u₁} [semiring R] (r : R → R → Prop) : R → R → Prop
where
| of : ∀ {x y : R}, r x y → rel r x y
| add_left : ∀ {a b c : R}, rel r a b → rel r (a + c) (b + c)
| mul_left : ∀ {a b c : R}, rel r a b → rel r (a * c) (b * c)
| mul_right : ∀ {a b c : R}, rel r b c → rel r (a * b) (a * c)

theorem rel.add_right {R : Type u₁} [semiring R] {r : R → R → Prop} {a : R} {b : R} {c : R} (h : rel r b c) : rel r (a + b) (a + c) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (rel r (a + b) (a + c))) (add_comm a b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (rel r (b + a) (a + c))) (add_comm a c))) (rel.add_left h))

theorem rel.neg {R : Type u₁} [ring R] {r : R → R → Prop} {a : R} {b : R} (h : rel r a b) : rel r (-a) (-b) := sorry

theorem rel.smul {S : Type u₂} [comm_semiring S] {A : Type u₃} [semiring A] [algebra S A] {r : A → A → Prop} (k : S) {a : A} {b : A} (h : rel r a b) : rel r (k • a) (k • b) := sorry

end ring_quot


/-- The quotient of a ring by an arbitrary relation. -/
def ring_quot {R : Type u₁} [semiring R] (r : R → R → Prop) :=
  Quot sorry

namespace ring_quot


protected instance semiring {R : Type u₁} [semiring R] (r : R → R → Prop) : semiring (ring_quot r) :=
  semiring.mk (quot.map₂ Add.add rel.add_right rel.add_left) sorry (Quot.mk (rel r) 0) sorry sorry sorry
    (quot.map₂ Mul.mul rel.mul_right rel.mul_left) sorry (Quot.mk (rel r) 1) sorry sorry sorry sorry sorry sorry

protected instance ring {R : Type u₁} [ring R] (r : R → R → Prop) : ring (ring_quot r) :=
  ring.mk semiring.add sorry semiring.zero sorry sorry (quot.map (fun (a : R) => -a) rel.neg)
    (add_comm_group.sub._default semiring.add sorry semiring.zero sorry sorry (quot.map (fun (a : R) => -a) rel.neg))
    sorry sorry semiring.mul sorry semiring.one sorry sorry sorry sorry

protected instance comm_semiring {R : Type u₁} [comm_semiring R] (r : R → R → Prop) : comm_semiring (ring_quot r) :=
  comm_semiring.mk semiring.add sorry semiring.zero sorry sorry sorry semiring.mul sorry semiring.one sorry sorry sorry
    sorry sorry sorry sorry

protected instance comm_ring {R : Type u₁} [comm_ring R] (r : R → R → Prop) : comm_ring (ring_quot r) :=
  comm_ring.mk comm_semiring.add sorry comm_semiring.zero sorry sorry ring.neg ring.sub sorry sorry comm_semiring.mul
    sorry comm_semiring.one sorry sorry sorry sorry sorry

protected instance algebra {S : Type u₂} [comm_semiring S] {A : Type u₃} [semiring A] [algebra S A] (s : A → A → Prop) : algebra S (ring_quot s) :=
  algebra.mk (ring_hom.mk (fun (r : S) => Quot.mk (rel s) (coe_fn (algebra_map S A) r)) sorry sorry sorry sorry) sorry
    sorry

protected instance inhabited {R : Type u₁} [semiring R] (r : R → R → Prop) : Inhabited (ring_quot r) :=
  { default := 0 }

/--
The quotient map from a ring to its quotient, as a homomorphism of rings.
-/
def mk_ring_hom {R : Type u₁} [semiring R] (r : R → R → Prop) : R →+* ring_quot r :=
  ring_hom.mk (Quot.mk (rel r)) sorry sorry sorry sorry

theorem mk_ring_hom_rel {R : Type u₁} [semiring R] {r : R → R → Prop} {x : R} {y : R} (w : r x y) : coe_fn (mk_ring_hom r) x = coe_fn (mk_ring_hom r) y :=
  quot.sound (rel.of w)

theorem mk_ring_hom_surjective {R : Type u₁} [semiring R] (r : R → R → Prop) : function.surjective ⇑(mk_ring_hom r) := sorry

theorem ring_quot_ext {R : Type u₁} [semiring R] {T : Type u₄} [semiring T] {r : R → R → Prop} (f : ring_quot r →+* T) (g : ring_quot r →+* T) (w : ring_hom.comp f (mk_ring_hom r) = ring_hom.comp g (mk_ring_hom r)) : f = g := sorry

/--
Any ring homomorphism `f : R →+* T` which respects a relation `r : R → R → Prop`
factors uniquely through a morphism `ring_quot r →+* T`.
-/
def lift {R : Type u₁} [semiring R] {T : Type u₄} [semiring T] {r : R → R → Prop} : (Subtype fun (f : R →+* T) => ∀ {x y : R}, r x y → coe_fn f x = coe_fn f y) ≃ (ring_quot r →+* T) :=
  equiv.mk
    (fun (f' : Subtype fun (f : R →+* T) => ∀ {x y : R}, r x y → coe_fn f x = coe_fn f y) =>
      let f : R →+* T := ↑f';
      ring_hom.mk (Quot.lift ⇑f sorry) (ring_hom.map_one f) sorry (ring_hom.map_zero f) sorry)
    (fun (F : ring_quot r →+* T) => { val := ring_hom.comp F (mk_ring_hom r), property := sorry }) sorry sorry

@[simp] theorem lift_mk_ring_hom_apply {R : Type u₁} [semiring R] {T : Type u₄} [semiring T] (f : R →+* T) {r : R → R → Prop} (w : ∀ {x y : R}, r x y → coe_fn f x = coe_fn f y) (x : R) : coe_fn (coe_fn lift { val := f, property := w }) (coe_fn (mk_ring_hom r) x) = coe_fn f x :=
  rfl

-- note this is essentially `lift.symm_apply_eq.mp h`

theorem lift_unique {R : Type u₁} [semiring R] {T : Type u₄} [semiring T] (f : R →+* T) {r : R → R → Prop} (w : ∀ {x y : R}, r x y → coe_fn f x = coe_fn f y) (g : ring_quot r →+* T) (h : ring_hom.comp g (mk_ring_hom r) = f) : g = coe_fn lift { val := f, property := w } := sorry

theorem eq_lift_comp_mk_ring_hom {R : Type u₁} [semiring R] {T : Type u₄} [semiring T] {r : R → R → Prop} (f : ring_quot r →+* T) : f =
  coe_fn lift
    { val := ring_hom.comp f (mk_ring_hom r),
      property :=
        fun (x y : R) (h : r x y) =>
          id
            (eq.mpr
              (id
                (Eq._oldrec (Eq.refl (coe_fn f (coe_fn (mk_ring_hom r) x) = coe_fn f (coe_fn (mk_ring_hom r) y)))
                  (mk_ring_hom_rel h)))
              (Eq.refl (coe_fn f (coe_fn (mk_ring_hom r) y)))) } :=
  Eq.symm (equiv.apply_symm_apply lift f)

/-!
We now verify that in the case of a commutative ring, the `ring_quot` construction
agrees with the quotient by the appropriate ideal.
-/

/-- The universal ring homomorphism from `ring_quot r` to `(ideal.of_rel r).quotient`. -/
def ring_quot_to_ideal_quotient {B : Type u₁} [comm_ring B] (r : B → B → Prop) : ring_quot r →+* ideal.quotient (ideal.of_rel r) :=
  coe_fn lift { val := ideal.quotient.mk (ideal.of_rel r), property := sorry }

@[simp] theorem ring_quot_to_ideal_quotient_apply {B : Type u₁} [comm_ring B] (r : B → B → Prop) (x : B) : coe_fn (ring_quot_to_ideal_quotient r) (coe_fn (mk_ring_hom r) x) = coe_fn (ideal.quotient.mk (ideal.of_rel r)) x :=
  rfl

/-- The universal ring homomorphism from `(ideal.of_rel r).quotient` to `ring_quot r`. -/
def ideal_quotient_to_ring_quot {B : Type u₁} [comm_ring B] (r : B → B → Prop) : ideal.quotient (ideal.of_rel r) →+* ring_quot r :=
  ideal.quotient.lift (ideal.of_rel r) (mk_ring_hom r) sorry

@[simp] theorem ideal_quotient_to_ring_quot_apply {B : Type u₁} [comm_ring B] (r : B → B → Prop) (x : B) : coe_fn (ideal_quotient_to_ring_quot r) (coe_fn (ideal.quotient.mk (ideal.of_rel r)) x) = coe_fn (mk_ring_hom r) x :=
  rfl

/--
The ring equivalence between `ring_quot r` and `(ideal.of_rel r).quotient`
-/
def ring_quot_equiv_ideal_quotient {B : Type u₁} [comm_ring B] (r : B → B → Prop) : ring_quot r ≃+* ideal.quotient (ideal.of_rel r) :=
  ring_equiv.of_hom_inv (ring_quot_to_ideal_quotient r) (ideal_quotient_to_ring_quot r) sorry sorry

/-- Transfer a star_ring instance through a quotient, if the quotient is invariant to `star` -/
def star_ring {R : Type u₁} [semiring R] [star_ring R] (r : R → R → Prop) (hr : ∀ {a b : R}, r a b → r (star a) (star b)) : star_ring (ring_quot r) :=
  star_ring.mk sorry

/--
The quotient map from an `S`-algebra to its quotient, as a homomorphism of `S`-algebras.
-/
def mk_alg_hom (S : Type u₂) [comm_semiring S] {A : Type u₃} [semiring A] [algebra S A] (s : A → A → Prop) : alg_hom S A (ring_quot s) :=
  alg_hom.mk (ring_hom.to_fun (mk_ring_hom s)) sorry sorry sorry sorry sorry

@[simp] theorem mk_alg_hom_coe (S : Type u₂) [comm_semiring S] {A : Type u₃} [semiring A] [algebra S A] (s : A → A → Prop) : ↑(mk_alg_hom S s) = mk_ring_hom s :=
  rfl

theorem mk_alg_hom_rel (S : Type u₂) [comm_semiring S] {A : Type u₃} [semiring A] [algebra S A] {s : A → A → Prop} {x : A} {y : A} (w : s x y) : coe_fn (mk_alg_hom S s) x = coe_fn (mk_alg_hom S s) y :=
  quot.sound (rel.of w)

theorem mk_alg_hom_surjective (S : Type u₂) [comm_semiring S] {A : Type u₃} [semiring A] [algebra S A] (s : A → A → Prop) : function.surjective ⇑(mk_alg_hom S s) := sorry

theorem ring_quot_ext' (S : Type u₂) [comm_semiring S] {A : Type u₃} [semiring A] [algebra S A] {B : Type u₄} [semiring B] [algebra S B] {s : A → A → Prop} (f : alg_hom S (ring_quot s) B) (g : alg_hom S (ring_quot s) B) (w : alg_hom.comp f (mk_alg_hom S s) = alg_hom.comp g (mk_alg_hom S s)) : f = g := sorry

/--
Any `S`-algebra homomorphism `f : A →ₐ[S] B` which respects a relation `s : A → A → Prop`
factors uniquely through a morphism `ring_quot s →ₐ[S]  B`.
-/
def lift_alg_hom (S : Type u₂) [comm_semiring S] {A : Type u₃} [semiring A] [algebra S A] {B : Type u₄} [semiring B] [algebra S B] {s : A → A → Prop} : (Subtype fun (f : alg_hom S A B) => ∀ {x y : A}, s x y → coe_fn f x = coe_fn f y) ≃ alg_hom S (ring_quot s) B :=
  equiv.mk
    (fun (f' : Subtype fun (f : alg_hom S A B) => ∀ {x y : A}, s x y → coe_fn f x = coe_fn f y) =>
      let f : alg_hom S A B := ↑f';
      alg_hom.mk (Quot.lift ⇑f sorry) (alg_hom.map_one f) sorry (alg_hom.map_zero f) sorry sorry)
    (fun (F : alg_hom S (ring_quot s) B) => { val := alg_hom.comp F (mk_alg_hom S s), property := sorry }) sorry sorry

@[simp] theorem lift_alg_hom_mk_alg_hom_apply (S : Type u₂) [comm_semiring S] {A : Type u₃} [semiring A] [algebra S A] {B : Type u₄} [semiring B] [algebra S B] (f : alg_hom S A B) {s : A → A → Prop} (w : ∀ {x y : A}, s x y → coe_fn f x = coe_fn f y) (x : A) : coe_fn (coe_fn (lift_alg_hom S) { val := f, property := w }) (coe_fn (mk_alg_hom S s) x) = coe_fn f x :=
  rfl

-- note this is essentially `(lift_alg_hom S).symm_apply_eq.mp h`

theorem lift_alg_hom_unique (S : Type u₂) [comm_semiring S] {A : Type u₃} [semiring A] [algebra S A] {B : Type u₄} [semiring B] [algebra S B] (f : alg_hom S A B) {s : A → A → Prop} (w : ∀ {x y : A}, s x y → coe_fn f x = coe_fn f y) (g : alg_hom S (ring_quot s) B) (h : alg_hom.comp g (mk_alg_hom S s) = f) : g = coe_fn (lift_alg_hom S) { val := f, property := w } := sorry

theorem eq_lift_alg_hom_comp_mk_alg_hom (S : Type u₂) [comm_semiring S] {A : Type u₃} [semiring A] [algebra S A] {B : Type u₄} [semiring B] [algebra S B] {s : A → A → Prop} (f : alg_hom S (ring_quot s) B) : f =
  coe_fn (lift_alg_hom S)
    { val := alg_hom.comp f (mk_alg_hom S s),
      property :=
        fun (x y : A) (h : s x y) =>
          id
            (eq.mpr
              (id
                (Eq._oldrec (Eq.refl (coe_fn f (coe_fn (mk_alg_hom S s) x) = coe_fn f (coe_fn (mk_alg_hom S s) y)))
                  (mk_alg_hom_rel S h)))
              (Eq.refl (coe_fn f (coe_fn (mk_alg_hom S s) y)))) } :=
  Eq.symm (equiv.apply_symm_apply (lift_alg_hom S) f)

