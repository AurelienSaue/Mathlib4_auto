/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.big_operators.basic
import Mathlib.algebra.group.hom
import Mathlib.algebra.ring.basic
import Mathlib.data.rat.cast
import Mathlib.group_theory.group_action.group
import Mathlib.tactic.nth_rewrite.default
import Mathlib.PostPort

universes u v l w x z u_1 u_2 u_3 

namespace Mathlib

/-!
# Modules over a ring

In this file we define

* `semimodule R M` : an additive commutative monoid `M` is a `semimodule` over a
  `semiring` `R` if for `r : R` and `x : M` their "scalar multiplication `r • x : M` is defined, and
  the operation `•` satisfies some natural associativity and distributivity axioms similar to those
  on a ring.

* `module R M` : same as `semimodule R M` but assumes that `R` is a `ring` and `M` is an
  additive commutative group.

* `vector_space k M` : same as `semimodule k M` and `module k M` but assumes that `k` is a `field`
  and `M` is an additive commutative group.

* `linear_map R M M₂`, `M →ₗ[R] M₂` : a linear map between two R-`semimodule`s.

## Implementation notes

* `vector_space` and `module` are abbreviations for `semimodule R M`.

## Tags

semimodule, module, vector space
-/

/-- A semimodule is a generalization of vector spaces to a scalar semiring.
  It consists of a scalar semiring `R` and an additive monoid of "vectors" `M`,
  connected by a "scalar multiplication" operation `r • x : M`
  (where `r : R` and `x : M`) with some natural associativity and
  distributivity axioms similar to those on a ring. -/
class semimodule (R : Type u) (M : Type v) [semiring R] [add_comm_monoid M] 
extends distrib_mul_action R M
where
  add_smul : ∀ (r s : R) (x : M), (r + s) • x = r • x + s • x
  zero_smul : ∀ (x : M), 0 • x = 0

theorem add_smul {R : Type u} {M : Type w} [semiring R] [add_comm_monoid M] [semimodule R M] (r : R) (s : R) (x : M) : (r + s) • x = r • x + s • x :=
  semimodule.add_smul r s x

@[simp] theorem zero_smul (R : Type u) {M : Type w} [semiring R] [add_comm_monoid M] [semimodule R M] (x : M) : 0 • x = 0 :=
  semimodule.zero_smul x

theorem two_smul (R : Type u) {M : Type w} [semiring R] [add_comm_monoid M] [semimodule R M] (x : M) : bit0 1 • x = x + x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (bit0 1 • x = x + x)) (bit0.equations._eqn_1 1)))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((1 + 1) • x = x + x)) (add_smul 1 1 x)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (1 • x + 1 • x = x + x)) (one_smul R x))) (Eq.refl (x + x))))

theorem two_smul' (R : Type u) {M : Type w} [semiring R] [add_comm_monoid M] [semimodule R M] (x : M) : bit0 1 • x = bit0 x :=
  two_smul R x

/-- Pullback a `semimodule` structure along an injective additive monoid homomorphism. -/
protected def function.injective.semimodule (R : Type u) {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M] [semimodule R M] [add_comm_monoid M₂] [has_scalar R M₂] (f : M₂ →+ M) (hf : function.injective ⇑f) (smul : ∀ (c : R) (x : M₂), coe_fn f (c • x) = c • coe_fn f x) : semimodule R M₂ :=
  semimodule.mk sorry sorry

/-- Pushforward a `semimodule` structure along a surjective additive monoid homomorphism. -/
protected def function.surjective.semimodule (R : Type u) {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M] [semimodule R M] [add_comm_monoid M₂] [has_scalar R M₂] (f : M →+ M₂) (hf : function.surjective ⇑f) (smul : ∀ (c : R) (x : M), coe_fn f (c • x) = c • coe_fn f x) : semimodule R M₂ :=
  semimodule.mk sorry sorry

/-- `(•)` as an `add_monoid_hom`. -/
def smul_add_hom (R : Type u) (M : Type w) [semiring R] [add_comm_monoid M] [semimodule R M] : R →+ M →+ M :=
  add_monoid_hom.mk (const_smul_hom M) sorry sorry

@[simp] theorem smul_add_hom_apply {R : Type u} {M : Type w} [semiring R] [add_comm_monoid M] [semimodule R M] (r : R) (x : M) : coe_fn (coe_fn (smul_add_hom R M) r) x = r • x :=
  rfl

theorem semimodule.eq_zero_of_zero_eq_one {R : Type u} {M : Type w} [semiring R] [add_comm_monoid M] [semimodule R M] (x : M) (zero_eq_one : 0 = 1) : x = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (x = 0)) (Eq.symm (one_smul R x))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (1 • x = 0)) (Eq.symm zero_eq_one)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (0 • x = 0)) (zero_smul R x))) (Eq.refl 0)))

theorem list.sum_smul {R : Type u} {M : Type w} [semiring R] [add_comm_monoid M] [semimodule R M] {l : List R} {x : M} : list.sum l • x = list.sum (list.map (fun (r : R) => r • x) l) :=
  add_monoid_hom.map_list_sum (coe_fn (add_monoid_hom.flip (smul_add_hom R M)) x) l

theorem multiset.sum_smul {R : Type u} {M : Type w} [semiring R] [add_comm_monoid M] [semimodule R M] {l : multiset R} {x : M} : multiset.sum l • x = multiset.sum (multiset.map (fun (r : R) => r • x) l) :=
  add_monoid_hom.map_multiset_sum (coe_fn (add_monoid_hom.flip (smul_add_hom R M)) x) l

theorem finset.sum_smul {R : Type u} {M : Type w} {ι : Type z} [semiring R] [add_comm_monoid M] [semimodule R M] {f : ι → R} {s : finset ι} {x : M} : (finset.sum s fun (i : ι) => f i) • x = finset.sum s fun (i : ι) => f i • x :=
  add_monoid_hom.map_sum (coe_fn (add_monoid_hom.flip (smul_add_hom R M)) x) f s

/-- An `add_comm_monoid` that is a `semimodule` over a `ring` carries a natural `add_comm_group`
structure. -/
def semimodule.add_comm_monoid_to_add_comm_group (R : Type u) {M : Type w} [ring R] [add_comm_monoid M] [semimodule R M] : add_comm_group M :=
  add_comm_group.mk add_comm_monoid.add sorry add_comm_monoid.zero sorry sorry (fun (a : M) => -1 • a)
    (add_group.sub._default add_comm_monoid.add sorry add_comm_monoid.zero sorry sorry fun (a : M) => -1 • a) sorry sorry

/-- A structure containing most informations as in a semimodule, except the fields `zero_smul`
and `smul_zero`. As these fields can be deduced from the other ones when `M` is an `add_comm_group`,
this provides a way to construct a semimodule structure by checking less properties, in
`semimodule.of_core`. -/
structure semimodule.core (R : Type u) (M : Type w) [semiring R] [add_comm_group M] 
extends has_scalar R M
where
  smul_add : ∀ (r : R) (x y : M), r • (x + y) = r • x + r • y
  add_smul : ∀ (r s : R) (x : M), (r + s) • x = r • x + s • x
  mul_smul : ∀ (r s : R) (x : M), (r * s) • x = r • s • x
  one_smul : ∀ (x : M), 1 • x = x

/-- Define `semimodule` without proving `zero_smul` and `smul_zero` by using an auxiliary
structure `semimodule.core`, when the underlying space is an `add_comm_group`. -/
def semimodule.of_core {R : Type u} {M : Type w} [semiring R] [add_comm_group M] (H : semimodule.core R M) : semimodule R M :=
  semimodule.mk (semimodule.core.add_smul H) sorry

/--
Modules are defined as an `abbreviation` for semimodules,
if the base semiring is a ring.
(A previous definition made `module` a structure
defined to be `semimodule`.)
This has as advantage that modules are completely transparent
for type class inference, which means that all instances for semimodules
are immediately picked up for modules as well.
A cosmetic disadvantage is that one can not extend modules as such,
in definitions such as `normed_space`.
The solution is to extend `semimodule` instead.
-/
/-- A module is the same as a semimodule, except the scalar semiring is actually
  a ring.
  This is the traditional generalization of spaces like `ℤ^n`, which have a natural
  addition operation and a way to multiply them by elements of a ring, but no multiplication
  operation between vectors. -/
def module (R : Type u) (M : Type v) [ring R] [add_comm_group M]  :=
  semimodule R M

/--
To prove two semimodule structures on a fixed `add_comm_monoid` agree,
it suffices to check the scalar multiplications agree.
-/
-- We'll later use this to show `semimodule ℕ M` and `module ℤ M` are subsingletons.

theorem semimodule_ext {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M] (P : semimodule R M) (Q : semimodule R M) (w : ∀ (r : R) (m : M), r • m = r • m) : P = Q := sorry

@[simp] theorem neg_smul {R : Type u} {M : Type w} [ring R] [add_comm_group M] [module R M] (r : R) (x : M) : -r • x = -(r • x) := sorry

theorem neg_one_smul (R : Type u) {M : Type w} [ring R] [add_comm_group M] [module R M] (x : M) : -1 • x = -x := sorry

theorem sub_smul {R : Type u} {M : Type w} [ring R] [add_comm_group M] [module R M] (r : R) (s : R) (y : M) : (r - s) • y = r • y - s • y := sorry

theorem smul_eq_zero {R : Type u_1} {E : Type u_2} [division_ring R] [add_comm_group E] [module R E] {c : R} {x : E} : c • x = 0 ↔ c = 0 ∨ x = 0 := sorry

/-- A semimodule over a `subsingleton` semiring is a `subsingleton`. We cannot register this
as an instance because Lean has no way to guess `R`. -/
theorem semimodule.subsingleton (R : Type u_1) (M : Type u_2) [semiring R] [subsingleton R] [add_comm_monoid M] [semimodule R M] : subsingleton M := sorry

protected instance semiring.to_semimodule {R : Type u} [semiring R] : semimodule R R :=
  semimodule.mk sorry sorry

@[simp] theorem smul_eq_mul {R : Type u} [semiring R] {a : R} {a' : R} : a • a' = a * a' :=
  rfl

/-- A ring homomorphism `f : R →+* M` defines a module structure by `r • x = f r * x`. -/
def ring_hom.to_semimodule {R : Type u} {S : Type v} [semiring R] [semiring S] (f : R →+* S) : semimodule R S :=
  semimodule.mk sorry sorry

/--
Vector spaces are defined as an `abbreviation` for semimodules,
if the base ring is a field.
(A previous definition made `vector_space` a structure
defined to be `module`.)
This has as advantage that vector spaces are completely transparent
for type class inference, which means that all instances for semimodules
are immediately picked up for vector spaces as well.
A cosmetic disadvantage is that one can not extend vector spaces as such,
in definitions such as `normed_space`.
The solution is to extend `semimodule` instead.
-/
/-- A vector space is the same as a module, except the scalar ring is actually
  a field. (This adds commutativity of the multiplication and existence of inverses.)
  This is the traditional generalization of spaces like `ℝ^n`, which have a natural
  addition operation and a way to multiply them by real numbers, but no multiplication
  operation between vectors. -/
def vector_space (R : Type u) (M : Type v) [field R] [add_comm_group M]  :=
  semimodule R M

/-- The natural ℕ-semimodule structure on any `add_comm_monoid`. -/
-- We don't make this a global instance, as it results in too many instances,

-- and confusing ambiguity in the notation `n • x` when `n : ℕ`.

instance add_comm_monoid.nat_semimodule {M : Type w} [add_comm_monoid M] : semimodule ℕ M :=
  semimodule.mk sorry sorry

/-- `nsmul` is defined as the `smul` action of `add_comm_monoid.nat_semimodule`. -/
theorem nsmul_def {M : Type w} [add_comm_monoid M] (n : ℕ) (x : M) : n •ℕ x = n • x :=
  rfl

/-- `nsmul` is equal to any other semimodule structure via a cast. -/
theorem nsmul_eq_smul_cast (R : Type u) {M : Type w} [semiring R] [add_comm_monoid M] [semimodule R M] (n : ℕ) (b : M) : n •ℕ b = ↑n • b := sorry

/-- `nsmul` is equal to any `ℕ`-semimodule structure. -/
theorem nsmul_eq_smul {M : Type w} [add_comm_monoid M] [semimodule ℕ M] (n : ℕ) (b : M) : n •ℕ b = n • b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (n •ℕ b = n • b)) (nsmul_eq_smul_cast ℕ n b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑n • b = n • b)) (nat.cast_id n))) (Eq.refl (n • b)))

/-- All `ℕ`-semimodule structures are equal. -/
protected instance add_comm_monoid.nat_semimodule.subsingleton {M : Type w} [add_comm_monoid M] : subsingleton (semimodule ℕ M) :=
  subsingleton.intro
    fun (P Q : semimodule ℕ M) =>
      semimodule_ext P Q
        fun (n : ℕ) (m : M) =>
          eq.mpr (id (Eq._oldrec (Eq.refl (n • m = n • m)) (Eq.symm (nsmul_eq_smul n m))))
            (eq.mpr (id (Eq._oldrec (Eq.refl (n •ℕ m = n • m)) (Eq.symm (nsmul_eq_smul n m)))) (Eq.refl (n •ℕ m)))

/-- Note this does not depend on the `nat_semimodule` definition above, to avoid issues when
diamonds occur in finding `semimodule ℕ M` instances. -/
protected instance add_comm_monoid.nat_is_scalar_tower {R : Type u} {M : Type w} [semiring R] [add_comm_monoid M] [semimodule R M] [semimodule ℕ R] [semimodule ℕ M] : is_scalar_tower ℕ R M := sorry

protected instance add_comm_monoid.nat_smul_comm_class {R : Type u} {M : Type w} [semiring R] [add_comm_monoid M] [semimodule R M] [semimodule ℕ M] : smul_comm_class ℕ R M := sorry

-- `smul_comm_class.symm` is not registered as an instance, as it would cause a loop

protected instance add_comm_monoid.nat_smul_comm_class' {R : Type u} {M : Type w} [semiring R] [add_comm_monoid M] [semimodule R M] [semimodule ℕ M] : smul_comm_class R ℕ M :=
  smul_comm_class.symm ℕ R M

/-- The natural ℤ-module structure on any `add_comm_group`. -/
-- We don't immediately make this a global instance, as it results in too many instances,

-- and confusing ambiguity in the notation `n • x` when `n : ℤ`.

-- We do turn it into a global instance, but only at the end of this file,

-- and I remain dubious whether this is a good idea.

instance add_comm_group.int_module {M : Type w} [add_comm_group M] : module ℤ M :=
  semimodule.mk sorry sorry

/-- `gsmul` is defined as the `smul` action of `add_comm_group.int_module`. -/
theorem gsmul_def {M : Type w} [add_comm_group M] (n : ℤ) (x : M) : n •ℤ x = n • x :=
  rfl

/-- `gsmul` is equal to any other module structure via a cast. -/
theorem gsmul_eq_smul_cast (R : Type u) {M : Type w} [ring R] [add_comm_group M] [semimodule R M] (n : ℤ) (b : M) : n •ℤ b = ↑n • b := sorry

/-- `gsmul` is equal to any `ℤ`-module structure. -/
theorem gsmul_eq_smul {M : Type w} [add_comm_group M] [semimodule ℤ M] (n : ℤ) (b : M) : n •ℤ b = n • b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (n •ℤ b = n • b)) (gsmul_eq_smul_cast ℤ n b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑n • b = n • b)) (int.cast_id n))) (Eq.refl (n • b)))

/-- All `ℤ`-module structures are equal. -/
protected instance add_comm_group.int_module.subsingleton {M : Type w} [add_comm_group M] : subsingleton (semimodule ℤ M) :=
  subsingleton.intro
    fun (P Q : semimodule ℤ M) =>
      semimodule_ext P Q
        fun (n : ℤ) (m : M) =>
          eq.mpr (id (Eq._oldrec (Eq.refl (n • m = n • m)) (Eq.symm (gsmul_eq_smul n m))))
            (eq.mpr (id (Eq._oldrec (Eq.refl (n •ℤ m = n • m)) (Eq.symm (gsmul_eq_smul n m)))) (Eq.refl (n •ℤ m)))

protected instance add_comm_group.int_is_scalar_tower {R : Type u} {M : Type w} [ring R] [add_comm_group M] [semimodule R M] [semimodule ℤ R] [semimodule ℤ M] : is_scalar_tower ℤ R M := sorry

protected instance add_comm_group.int_smul_comm_class {S : Type v} {M : Type w} [semiring S] [add_comm_group M] [semimodule S M] [semimodule ℤ M] : smul_comm_class ℤ S M := sorry

-- `smul_comm_class.symm` is not registered as an instance, as it would cause a loop

protected instance add_comm_group.int_smul_comm_class' {S : Type v} {M : Type w} [semiring S] [add_comm_group M] [semimodule S M] [semimodule ℤ M] : smul_comm_class S ℤ M :=
  smul_comm_class.symm ℤ S M

namespace add_monoid_hom


-- We prove this without using the `add_comm_group.int_module` instance, so the `•`s here

-- come from whatever the local `module ℤ` structure actually is.

theorem map_int_module_smul {M : Type w} {M₂ : Type x} [add_comm_group M] [add_comm_group M₂] [module ℤ M] [module ℤ M₂] (f : M →+ M₂) (x : ℤ) (a : M) : coe_fn f (x • a) = x • coe_fn f a := sorry

theorem map_int_cast_smul {R : Type u} {M : Type w} {M₂ : Type x} [ring R] [add_comm_group M] [add_comm_group M₂] [module R M] [module R M₂] (f : M →+ M₂) (x : ℤ) (a : M) : coe_fn f (↑x • a) = ↑x • coe_fn f a := sorry

theorem map_nat_cast_smul {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : M →+ M₂) (x : ℕ) (a : M) : coe_fn f (↑x • a) = ↑x • coe_fn f a := sorry

theorem map_rat_cast_smul {R : Type u_1} [division_ring R] [char_zero R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] (f : E →+ F) (c : ℚ) (x : E) : coe_fn f (↑c • x) = ↑c • coe_fn f x := sorry

theorem map_rat_module_smul {E : Type u_1} [add_comm_group E] [vector_space ℚ E] {F : Type u_2} [add_comm_group F] [module ℚ F] (f : E →+ F) (c : ℚ) (x : E) : coe_fn f (c • x) = c • coe_fn f x :=
  rat.cast_id c ▸ map_rat_cast_smul f c x

@[simp] theorem nat_smul_apply {M : Type w} {M₂ : Type x} [add_monoid M] [add_comm_monoid M₂] [semimodule ℕ (M →+ M₂)] [semimodule ℕ M₂] (n : ℕ) (f : M →+ M₂) (a : M) : coe_fn (n • f) a = n • coe_fn f a := sorry

@[simp] theorem int_smul_apply {M : Type w} {M₂ : Type x} [add_monoid M] [add_comm_group M₂] [module ℤ (M →+ M₂)] [module ℤ M₂] (n : ℤ) (f : M →+ M₂) (a : M) : coe_fn (n • f) a = n • coe_fn f a := sorry

end add_monoid_hom


/-! Some tests for the vanishing of elements in modules over division rings. -/

theorem smul_nat_eq_zero (R : Type u) {M : Type w} [division_ring R] [add_comm_group M] [module R M] [semimodule ℕ M] [char_zero R] {v : M} {n : ℕ} : n • v = 0 ↔ n = 0 ∨ v = 0 := sorry

theorem eq_zero_of_smul_two_eq_zero (R : Type u) {M : Type w} [division_ring R] [add_comm_group M] [module R M] [semimodule ℕ M] [char_zero R] {v : M} (hv : bit0 1 • v = 0) : v = 0 := sorry

theorem eq_zero_of_eq_neg (R : Type u) {M : Type w} [division_ring R] [add_comm_group M] [module R M] [char_zero R] {v : M} (hv : v = -v) : v = 0 := sorry

theorem ne_neg_of_ne_zero (R : Type u) [division_ring R] [char_zero R] {v : R} (hv : v ≠ 0) : v ≠ -v :=
  fun (h : v = -v) => (fun (this : semimodule ℕ R) => hv (eq_zero_of_eq_neg R h)) add_comm_monoid.nat_semimodule

