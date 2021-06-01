/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.group_ring_action
import Mathlib.group_theory.group_action.default
import Mathlib.PostPort

universes u_1 u_2 u_3 l u_4 u_16 u_5 u_6 u_8 u_7 u_9 u_10 u_11 u_13 u_12 u_14 u_15 

namespace Mathlib

/-!
# Equivariant homomorphisms

## Main definitions

* `mul_action_hom M X Y`, the type of equivariant functions from `X` to `Y`, where `M` is a monoid
  that acts on the types `X` and `Y`.
* `distrib_mul_action_hom M A B`, the type of equivariant additive monoid homomorphisms
  from `A` to `B`, where `M` is a monoid that acts on the additive monoids `A` and `B`.
* `mul_semiring_action_hom M R S`, the type of equivariant ring homomorphisms
  from `R` to `S`, where `M` is a monoid that acts on the rings `R` and `S`.

## Notations

* `X →[M] Y` is `mul_action_hom M X Y`.
* `A →+[M] B` is `distrib_mul_action_hom M X Y`.
* `R →+*[M] S` is `mul_semiring_action_hom M X Y`.

-/

/-- Equivariant functions. -/
structure mul_action_hom (M' : Type u_1) (X : Type u_2) [has_scalar M' X] (Y : Type u_3)
    [has_scalar M' Y]
    where
  to_fun : X → Y
  map_smul' : ∀ (m : M') (x : X), to_fun (m • x) = m • to_fun x

namespace mul_action_hom


protected instance has_coe_to_fun (M' : Type u_1) (X : Type u_2) [has_scalar M' X] (Y : Type u_3)
    [has_scalar M' Y] : has_coe_to_fun (mul_action_hom M' X Y) :=
  has_coe_to_fun.mk (fun (c : mul_action_hom M' X Y) => X → Y)
    fun (c : mul_action_hom M' X Y) => to_fun c

@[simp] theorem map_smul {M' : Type u_1} {X : Type u_2} [has_scalar M' X] {Y : Type u_3}
    [has_scalar M' Y] (f : mul_action_hom M' X Y) (m : M') (x : X) :
    coe_fn f (m • x) = m • coe_fn f x :=
  map_smul' f m x

theorem ext {M' : Type u_1} {X : Type u_2} [has_scalar M' X] {Y : Type u_3} [has_scalar M' Y]
    {f : mul_action_hom M' X Y} {g : mul_action_hom M' X Y} :
    (∀ (x : X), coe_fn f x = coe_fn g x) → f = g :=
  sorry

theorem ext_iff {M' : Type u_1} {X : Type u_2} [has_scalar M' X] {Y : Type u_3} [has_scalar M' Y]
    {f : mul_action_hom M' X Y} {g : mul_action_hom M' X Y} :
    f = g ↔ ∀ (x : X), coe_fn f x = coe_fn g x :=
  { mp :=
      fun (H : f = g) (x : X) =>
        eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn f x = coe_fn g x)) H)) (Eq.refl (coe_fn g x)),
    mpr := ext }

/-- The identity map as an equivariant map. -/
protected def id (M' : Type u_1) {X : Type u_2} [has_scalar M' X] : mul_action_hom M' X X :=
  mk id sorry

@[simp] theorem id_apply (M' : Type u_1) {X : Type u_2} [has_scalar M' X] (x : X) :
    coe_fn (mul_action_hom.id M') x = x :=
  rfl

/-- Composition of two equivariant maps. -/
def comp {M' : Type u_1} {X : Type u_2} [has_scalar M' X] {Y : Type u_3} [has_scalar M' Y]
    {Z : Type u_4} [has_scalar M' Z] (g : mul_action_hom M' Y Z) (f : mul_action_hom M' X Y) :
    mul_action_hom M' X Z :=
  mk (⇑g ∘ ⇑f) sorry

@[simp] theorem comp_apply {M' : Type u_1} {X : Type u_2} [has_scalar M' X] {Y : Type u_3}
    [has_scalar M' Y] {Z : Type u_4} [has_scalar M' Z] (g : mul_action_hom M' Y Z)
    (f : mul_action_hom M' X Y) (x : X) : coe_fn (comp g f) x = coe_fn g (coe_fn f x) :=
  rfl

@[simp] theorem id_comp {M' : Type u_1} {X : Type u_2} [has_scalar M' X] {Y : Type u_3}
    [has_scalar M' Y] (f : mul_action_hom M' X Y) : comp (mul_action_hom.id M') f = f :=
  sorry

@[simp] theorem comp_id {M' : Type u_1} {X : Type u_2} [has_scalar M' X] {Y : Type u_3}
    [has_scalar M' Y] (f : mul_action_hom M' X Y) : comp f (mul_action_hom.id M') = f :=
  sorry

/-- The canonical map to the left cosets. -/
def to_quotient {G : Type u_16} [group G] (H : subgroup G) :
    mul_action_hom G G (quotient_group.quotient H) :=
  mk coe sorry

@[simp] theorem to_quotient_apply {G : Type u_16} [group G] (H : subgroup G) (g : G) :
    coe_fn (to_quotient H) g = ↑g :=
  rfl

end mul_action_hom


/-- Equivariant additive monoid homomorphisms. -/
structure distrib_mul_action_hom (M : Type u_5) [monoid M] (A : Type u_6) [add_monoid A]
    [distrib_mul_action M A] (B : Type u_8) [add_monoid B] [distrib_mul_action M B]
    extends A →+ B, mul_action_hom M A B where

/-- Reinterpret an equivariant additive monoid homomorphism as an additive monoid homomorphism. -/
/-- Reinterpret an equivariant additive monoid homomorphism as an equivariant function. -/
namespace distrib_mul_action_hom


protected instance has_coe (M : Type u_5) [monoid M] (A : Type u_6) [add_monoid A]
    [distrib_mul_action M A] (B : Type u_8) [add_monoid B] [distrib_mul_action M B] :
    has_coe (distrib_mul_action_hom M A B) (A →+ B) :=
  has_coe.mk to_add_monoid_hom

protected instance has_coe' (M : Type u_5) [monoid M] (A : Type u_6) [add_monoid A]
    [distrib_mul_action M A] (B : Type u_8) [add_monoid B] [distrib_mul_action M B] :
    has_coe (distrib_mul_action_hom M A B) (mul_action_hom M A B) :=
  has_coe.mk to_mul_action_hom

protected instance has_coe_to_fun (M : Type u_5) [monoid M] (A : Type u_6) [add_monoid A]
    [distrib_mul_action M A] (B : Type u_8) [add_monoid B] [distrib_mul_action M B] :
    has_coe_to_fun (distrib_mul_action_hom M A B) :=
  has_coe_to_fun.mk (fun (c : distrib_mul_action_hom M A B) => A → B)
    fun (c : distrib_mul_action_hom M A B) => to_fun c

theorem coe_fn_coe {M : Type u_5} [monoid M] {A : Type u_6} [add_monoid A] [distrib_mul_action M A]
    {B : Type u_8} [add_monoid B] [distrib_mul_action M B] (f : distrib_mul_action_hom M A B) :
    ⇑↑f = ⇑f :=
  rfl

theorem coe_fn_coe' {M : Type u_5} [monoid M] {A : Type u_6} [add_monoid A] [distrib_mul_action M A]
    {B : Type u_8} [add_monoid B] [distrib_mul_action M B] (f : distrib_mul_action_hom M A B) :
    ⇑↑f = ⇑f :=
  rfl

theorem ext {M : Type u_5} [monoid M] {A : Type u_6} [add_monoid A] [distrib_mul_action M A]
    {B : Type u_8} [add_monoid B] [distrib_mul_action M B] {f : distrib_mul_action_hom M A B}
    {g : distrib_mul_action_hom M A B} : (∀ (x : A), coe_fn f x = coe_fn g x) → f = g :=
  sorry

theorem ext_iff {M : Type u_5} [monoid M] {A : Type u_6} [add_monoid A] [distrib_mul_action M A]
    {B : Type u_8} [add_monoid B] [distrib_mul_action M B] {f : distrib_mul_action_hom M A B}
    {g : distrib_mul_action_hom M A B} : f = g ↔ ∀ (x : A), coe_fn f x = coe_fn g x :=
  { mp :=
      fun (H : f = g) (x : A) =>
        eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn f x = coe_fn g x)) H)) (Eq.refl (coe_fn g x)),
    mpr := ext }

@[simp] theorem map_zero {M : Type u_5} [monoid M] {A : Type u_6} [add_monoid A]
    [distrib_mul_action M A] {B : Type u_8} [add_monoid B] [distrib_mul_action M B]
    (f : distrib_mul_action_hom M A B) : coe_fn f 0 = 0 :=
  map_zero' f

@[simp] theorem map_add {M : Type u_5} [monoid M] {A : Type u_6} [add_monoid A]
    [distrib_mul_action M A] {B : Type u_8} [add_monoid B] [distrib_mul_action M B]
    (f : distrib_mul_action_hom M A B) (x : A) (y : A) :
    coe_fn f (x + y) = coe_fn f x + coe_fn f y :=
  map_add' f x y

@[simp] theorem map_neg {M : Type u_5} [monoid M] (A' : Type u_7) [add_group A']
    [distrib_mul_action M A'] (B' : Type u_9) [add_group B'] [distrib_mul_action M B']
    (f : distrib_mul_action_hom M A' B') (x : A') : coe_fn f (-x) = -coe_fn f x :=
  add_monoid_hom.map_neg (↑f) x

@[simp] theorem map_sub {M : Type u_5} [monoid M] (A' : Type u_7) [add_group A']
    [distrib_mul_action M A'] (B' : Type u_9) [add_group B'] [distrib_mul_action M B']
    (f : distrib_mul_action_hom M A' B') (x : A') (y : A') :
    coe_fn f (x - y) = coe_fn f x - coe_fn f y :=
  add_monoid_hom.map_sub (↑f) x y

@[simp] theorem map_smul {M : Type u_5} [monoid M] {A : Type u_6} [add_monoid A]
    [distrib_mul_action M A] {B : Type u_8} [add_monoid B] [distrib_mul_action M B]
    (f : distrib_mul_action_hom M A B) (m : M) (x : A) : coe_fn f (m • x) = m • coe_fn f x :=
  map_smul' f m x

/-- The identity map as an equivariant additive monoid homomorphism. -/
protected def id (M : Type u_5) [monoid M] {A : Type u_6} [add_monoid A] [distrib_mul_action M A] :
    distrib_mul_action_hom M A A :=
  mk id sorry sorry sorry

@[simp] theorem id_apply (M : Type u_5) [monoid M] {A : Type u_6} [add_monoid A]
    [distrib_mul_action M A] (x : A) : coe_fn (distrib_mul_action_hom.id M) x = x :=
  rfl

/-- Composition of two equivariant additive monoid homomorphisms. -/
def comp {M : Type u_5} [monoid M] {A : Type u_6} [add_monoid A] [distrib_mul_action M A]
    {B : Type u_8} [add_monoid B] [distrib_mul_action M B] {C : Type u_10} [add_monoid C]
    [distrib_mul_action M C] (g : distrib_mul_action_hom M B C) (f : distrib_mul_action_hom M A B) :
    distrib_mul_action_hom M A C :=
  mk (mul_action_hom.to_fun (mul_action_hom.comp ↑g ↑f)) sorry sorry sorry

@[simp] theorem comp_apply {M : Type u_5} [monoid M] {A : Type u_6} [add_monoid A]
    [distrib_mul_action M A] {B : Type u_8} [add_monoid B] [distrib_mul_action M B] {C : Type u_10}
    [add_monoid C] [distrib_mul_action M C] (g : distrib_mul_action_hom M B C)
    (f : distrib_mul_action_hom M A B) (x : A) : coe_fn (comp g f) x = coe_fn g (coe_fn f x) :=
  rfl

@[simp] theorem id_comp {M : Type u_5} [monoid M] {A : Type u_6} [add_monoid A]
    [distrib_mul_action M A] {B : Type u_8} [add_monoid B] [distrib_mul_action M B]
    (f : distrib_mul_action_hom M A B) : comp (distrib_mul_action_hom.id M) f = f :=
  sorry

@[simp] theorem comp_id {M : Type u_5} [monoid M] {A : Type u_6} [add_monoid A]
    [distrib_mul_action M A] {B : Type u_8} [add_monoid B] [distrib_mul_action M B]
    (f : distrib_mul_action_hom M A B) : comp f (distrib_mul_action_hom.id M) = f :=
  sorry

end distrib_mul_action_hom


/-- Equivariant ring homomorphisms. -/
structure mul_semiring_action_hom (M : Type u_5) [monoid M] (R : Type u_11) [semiring R]
    [mul_semiring_action M R] (S : Type u_13) [semiring S] [mul_semiring_action M S]
    extends distrib_mul_action_hom M R S, R →+* S where

/-- Reinterpret an equivariant ring homomorphism as a ring homomorphism. -/
/-- Reinterpret an equivariant ring homomorphism as an equivariant additive monoid homomorphism. -/
namespace mul_semiring_action_hom


protected instance has_coe (M : Type u_5) [monoid M] (R : Type u_11) [semiring R]
    [mul_semiring_action M R] (S : Type u_13) [semiring S] [mul_semiring_action M S] :
    has_coe (mul_semiring_action_hom M R S) (R →+* S) :=
  has_coe.mk to_ring_hom

protected instance has_coe' (M : Type u_5) [monoid M] (R : Type u_11) [semiring R]
    [mul_semiring_action M R] (S : Type u_13) [semiring S] [mul_semiring_action M S] :
    has_coe (mul_semiring_action_hom M R S) (distrib_mul_action_hom M R S) :=
  has_coe.mk to_distrib_mul_action_hom

protected instance has_coe_to_fun (M : Type u_5) [monoid M] (R : Type u_11) [semiring R]
    [mul_semiring_action M R] (S : Type u_13) [semiring S] [mul_semiring_action M S] :
    has_coe_to_fun (mul_semiring_action_hom M R S) :=
  has_coe_to_fun.mk (fun (c : mul_semiring_action_hom M R S) => R → S)
    fun (c : mul_semiring_action_hom M R S) => to_fun c

theorem coe_fn_coe {M : Type u_5} [monoid M] {R : Type u_11} [semiring R] [mul_semiring_action M R]
    {S : Type u_13} [semiring S] [mul_semiring_action M S] (f : mul_semiring_action_hom M R S) :
    ⇑↑f = ⇑f :=
  rfl

theorem coe_fn_coe' {M : Type u_5} [monoid M] {R : Type u_11} [semiring R] [mul_semiring_action M R]
    {S : Type u_13} [semiring S] [mul_semiring_action M S] (f : mul_semiring_action_hom M R S) :
    ⇑↑f = ⇑f :=
  rfl

theorem ext {M : Type u_5} [monoid M] {R : Type u_11} [semiring R] [mul_semiring_action M R]
    {S : Type u_13} [semiring S] [mul_semiring_action M S] {f : mul_semiring_action_hom M R S}
    {g : mul_semiring_action_hom M R S} : (∀ (x : R), coe_fn f x = coe_fn g x) → f = g :=
  sorry

theorem ext_iff {M : Type u_5} [monoid M] {R : Type u_11} [semiring R] [mul_semiring_action M R]
    {S : Type u_13} [semiring S] [mul_semiring_action M S] {f : mul_semiring_action_hom M R S}
    {g : mul_semiring_action_hom M R S} : f = g ↔ ∀ (x : R), coe_fn f x = coe_fn g x :=
  { mp :=
      fun (H : f = g) (x : R) =>
        eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn f x = coe_fn g x)) H)) (Eq.refl (coe_fn g x)),
    mpr := ext }

@[simp] theorem map_zero {M : Type u_5} [monoid M] {R : Type u_11} [semiring R]
    [mul_semiring_action M R] {S : Type u_13} [semiring S] [mul_semiring_action M S]
    (f : mul_semiring_action_hom M R S) : coe_fn f 0 = 0 :=
  map_zero' f

@[simp] theorem map_add {M : Type u_5} [monoid M] {R : Type u_11} [semiring R]
    [mul_semiring_action M R] {S : Type u_13} [semiring S] [mul_semiring_action M S]
    (f : mul_semiring_action_hom M R S) (x : R) (y : R) :
    coe_fn f (x + y) = coe_fn f x + coe_fn f y :=
  map_add' f x y

@[simp] theorem map_neg {M : Type u_5} [monoid M] (R' : Type u_12) [ring R']
    [mul_semiring_action M R'] (S' : Type u_14) [ring S'] [mul_semiring_action M S']
    (f : mul_semiring_action_hom M R' S') (x : R') : coe_fn f (-x) = -coe_fn f x :=
  ring_hom.map_neg (↑f) x

@[simp] theorem map_sub {M : Type u_5} [monoid M] (R' : Type u_12) [ring R']
    [mul_semiring_action M R'] (S' : Type u_14) [ring S'] [mul_semiring_action M S']
    (f : mul_semiring_action_hom M R' S') (x : R') (y : R') :
    coe_fn f (x - y) = coe_fn f x - coe_fn f y :=
  ring_hom.map_sub (↑f) x y

@[simp] theorem map_one {M : Type u_5} [monoid M] {R : Type u_11} [semiring R]
    [mul_semiring_action M R] {S : Type u_13} [semiring S] [mul_semiring_action M S]
    (f : mul_semiring_action_hom M R S) : coe_fn f 1 = 1 :=
  map_one' f

@[simp] theorem map_mul {M : Type u_5} [monoid M] {R : Type u_11} [semiring R]
    [mul_semiring_action M R] {S : Type u_13} [semiring S] [mul_semiring_action M S]
    (f : mul_semiring_action_hom M R S) (x : R) (y : R) :
    coe_fn f (x * y) = coe_fn f x * coe_fn f y :=
  map_mul' f x y

@[simp] theorem map_smul {M : Type u_5} [monoid M] {R : Type u_11} [semiring R]
    [mul_semiring_action M R] {S : Type u_13} [semiring S] [mul_semiring_action M S]
    (f : mul_semiring_action_hom M R S) (m : M) (x : R) : coe_fn f (m • x) = m • coe_fn f x :=
  map_smul' f m x

/-- The identity map as an equivariant ring homomorphism. -/
protected def id (M : Type u_5) [monoid M] {R : Type u_11} [semiring R] [mul_semiring_action M R] :
    mul_semiring_action_hom M R R :=
  mk id sorry sorry sorry sorry sorry

@[simp] theorem id_apply (M : Type u_5) [monoid M] {R : Type u_11} [semiring R]
    [mul_semiring_action M R] (x : R) : coe_fn (mul_semiring_action_hom.id M) x = x :=
  rfl

/-- Composition of two equivariant additive monoid homomorphisms. -/
def comp {M : Type u_5} [monoid M] {R : Type u_11} [semiring R] [mul_semiring_action M R]
    {S : Type u_13} [semiring S] [mul_semiring_action M S] {T : Type u_15} [semiring T]
    [mul_semiring_action M T] (g : mul_semiring_action_hom M S T)
    (f : mul_semiring_action_hom M R S) : mul_semiring_action_hom M R T :=
  mk (distrib_mul_action_hom.to_fun (distrib_mul_action_hom.comp ↑g ↑f)) sorry sorry sorry sorry
    sorry

@[simp] theorem comp_apply {M : Type u_5} [monoid M] {R : Type u_11} [semiring R]
    [mul_semiring_action M R] {S : Type u_13} [semiring S] [mul_semiring_action M S] {T : Type u_15}
    [semiring T] [mul_semiring_action M T] (g : mul_semiring_action_hom M S T)
    (f : mul_semiring_action_hom M R S) (x : R) : coe_fn (comp g f) x = coe_fn g (coe_fn f x) :=
  rfl

@[simp] theorem id_comp {M : Type u_5} [monoid M] {R : Type u_11} [semiring R]
    [mul_semiring_action M R] {S : Type u_13} [semiring S] [mul_semiring_action M S]
    (f : mul_semiring_action_hom M R S) : comp (mul_semiring_action_hom.id M) f = f :=
  sorry

@[simp] theorem comp_id {M : Type u_5} [monoid M] {R : Type u_11} [semiring R]
    [mul_semiring_action M R] {S : Type u_13} [semiring S] [mul_semiring_action M S]
    (f : mul_semiring_action_hom M R S) : comp f (mul_semiring_action_hom.id M) = f :=
  sorry

end mul_semiring_action_hom


/-- The canonical inclusion from an invariant subring. -/
def is_invariant_subring.subtype_hom (M : Type u_5) [monoid M] {R' : Type u_12} [ring R']
    [mul_semiring_action M R'] (U : set R') [is_subring U] [is_invariant_subring M U] :
    mul_semiring_action_hom M (↥U) R' :=
  mul_semiring_action_hom.mk (ring_hom.to_fun (is_subring.subtype U)) sorry sorry sorry sorry sorry

@[simp] theorem is_invariant_subring.coe_subtype_hom (M : Type u_5) [monoid M] {R' : Type u_12}
    [ring R'] [mul_semiring_action M R'] (U : set R') [is_subring U] [is_invariant_subring M U] :
    ⇑(is_invariant_subring.subtype_hom M U) = coe :=
  rfl

@[simp] theorem is_invariant_subring.coe_subtype_hom' (M : Type u_5) [monoid M] {R' : Type u_12}
    [ring R'] [mul_semiring_action M R'] (U : set R') [is_subring U] [is_invariant_subring M U] :
    ↑(is_invariant_subring.subtype_hom M U) = is_subring.subtype U :=
  rfl

end Mathlib