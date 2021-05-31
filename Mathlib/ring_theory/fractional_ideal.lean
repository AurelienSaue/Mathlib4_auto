/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Filippo A. E. Nuccio
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.ring_theory.localization
import Mathlib.ring_theory.noetherian
import Mathlib.ring_theory.principal_ideal_domain
import Mathlib.tactic.field_simp
import Mathlib.PostPort

universes u_1 u_2 u_3 u_4 u_5 

namespace Mathlib

/-!
# Fractional ideals

This file defines fractional ideals of an integral domain and proves basic facts about them.

## Main definitions
Let `S` be a submonoid of an integral domain `R`, `P` the localization of `R` at `S`, and `f` the
natural ring hom from `R` to `P`.
 * `is_fractional` defines which `R`-submodules of `P` are fractional ideals
 * `fractional_ideal f` is the type of fractional ideals in `P`
 * `has_coe (ideal R) (fractional_ideal f)` instance
 * `comm_semiring (fractional_ideal f)` instance:
   the typical ideal operations generalized to fractional ideals
 * `lattice (fractional_ideal f)` instance
 * `map` is the pushforward of a fractional ideal along an algebra morphism

Let `K` be the localization of `R` at `R \ {0}` and `g` the natural ring hom from `R` to `K`.
 * `has_div (fractional_ideal g)` instance:
   the ideal quotient `I / J` (typically written $I : J$, but a `:` operator cannot be defined)

## Main statements

  * `mul_left_mono` and `mul_right_mono` state that ideal multiplication is monotone
  * `prod_one_self_div_eq` states that `1 / I` is the inverse of `I` if one exists
  * `is_noetherian` states that very fractional ideal of a noetherian integral domain is noetherian

## Implementation notes

Fractional ideals are considered equal when they contain the same elements,
independent of the denominator `a : R` such that `a I ⊆ R`.
Thus, we define `fractional_ideal` to be the subtype of the predicate `is_fractional`,
instead of having `fractional_ideal` be a structure of which `a` is a field.

Most definitions in this file specialize operations from submodules to fractional ideals,
proving that the result of this operation is fractional if the input is fractional.
Exceptions to this rule are defining `(+) := (⊔)` and `⊥ := 0`,
in order to re-use their respective proof terms.
We can still use `simp` to show `I.1 + J.1 = (I + J).1` and `⊥.1 = 0.1`.

In `ring_theory.localization`, we define a copy of the localization map `f`'s codomain `P`
(`f.codomain`) so that the `R`-algebra instance on `P` can 'know' the map needed to induce
the `R`-algebra structure.

We don't assume that the localization is a field until we need it to define ideal quotients.
When this assumption is needed, we replace `S` with `non_zero_divisors R`, making the localization
a field.

## References

  * https://en.wikipedia.org/wiki/Fractional_ideal

## Tags

fractional ideal, fractional ideals, invertible ideal
-/

namespace ring


/-- A submodule `I` is a fractional ideal if `a I ⊆ R` for some `a ≠ 0`. -/
def is_fractional {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] (f : localization_map S P) (I : submodule R (localization_map.codomain f)) :=
  ∃ (a : R), ∃ (H : a ∈ S), ∀ (b : P), b ∈ I → localization_map.is_integer f (coe_fn (localization_map.to_map f) a * b)

/-- The fractional ideals of a domain `R` are ideals of `R` divided by some `a ∈ R`.

  More precisely, let `P` be a localization of `R` at some submonoid `S`,
  then a fractional ideal `I ⊆ P` is an `R`-submodule of `P`,
  such that there is a nonzero `a : R` with `a I ⊆ R`.
-/
def fractional_ideal {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] (f : localization_map S P) :=
  Subtype fun (I : submodule R (localization_map.codomain f)) => is_fractional f I

namespace fractional_ideal


protected instance submodule.has_coe {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} : has_coe (fractional_ideal f) (submodule R (localization_map.codomain f)) :=
  has_coe.mk fun (I : fractional_ideal f) => subtype.val I

@[simp] theorem val_eq_coe {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} (I : fractional_ideal f) : subtype.val I = ↑I :=
  rfl

@[simp] theorem coe_mk {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} (I : submodule R (localization_map.codomain f)) (hI : is_fractional f I) : ↑{ val := I, property := hI } = I :=
  rfl

protected instance has_mem {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} : has_mem P (fractional_ideal f) :=
  has_mem.mk fun (x : P) (I : fractional_ideal f) => x ∈ ↑I

/-- Fractional ideals are equal if their submodules are equal.

  Combined with `submodule.ext` this gives that fractional ideals are equal if
  they have the same elements.
-/
theorem ext {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {I : fractional_ideal f} {J : fractional_ideal f} : ↑I = ↑J → I = J :=
  iff.mpr subtype.ext_iff_val

theorem ext_iff {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {I : fractional_ideal f} {J : fractional_ideal f} : (∀ (x : P), x ∈ I ↔ x ∈ J) ↔ I = J :=
  { mp := fun (h : ∀ (x : P), x ∈ I ↔ x ∈ J) => ext (submodule.ext h), mpr := fun (h : I = J) (x : P) => h ▸ iff.rfl }

theorem fractional_of_subset_one {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} (I : submodule R (localization_map.codomain f)) (h : I ≤ submodule.span R (singleton 1)) : is_fractional f I := sorry

theorem is_fractional_of_le {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {I : submodule R (localization_map.codomain f)} {J : fractional_ideal f} (hIJ : I ≤ ↑J) : is_fractional f I := sorry

protected instance coe_to_fractional_ideal {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} : has_coe (ideal R) (fractional_ideal f) :=
  has_coe.mk fun (I : ideal R) => { val := localization_map.coe_submodule f I, property := sorry }

@[simp] theorem coe_coe_ideal {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} (I : ideal R) : ↑↑I = localization_map.coe_submodule f I :=
  rfl

@[simp] theorem mem_coe_ideal {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {x : localization_map.codomain f} {I : ideal R} : x ∈ ↑I ↔ ∃ (x' : R), ∃ (H : x' ∈ I), coe_fn (localization_map.to_map f) x' = x := sorry

protected instance has_zero {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} : HasZero (fractional_ideal f) :=
  { zero := ↑0 }

@[simp] theorem mem_zero_iff {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {x : P} : x ∈ 0 ↔ x = 0 := sorry

@[simp] theorem coe_zero {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} : ↑0 = ⊥ :=
  submodule.ext fun (_x : localization_map.codomain f) => mem_zero_iff

@[simp] theorem coe_to_fractional_ideal_bot {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} : ↑⊥ = 0 :=
  rfl

@[simp] theorem exists_mem_to_map_eq {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {x : R} {I : ideal R} (h : S ≤ non_zero_divisors R) : (∃ (x' : R), x' ∈ I ∧ coe_fn (localization_map.to_map f) x' = coe_fn (localization_map.to_map f) x) ↔ x ∈ I := sorry

theorem coe_to_fractional_ideal_injective {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} (h : S ≤ non_zero_divisors R) : function.injective coe := sorry

theorem coe_to_fractional_ideal_eq_zero {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {I : ideal R} (hS : S ≤ non_zero_divisors R) : ↑I = 0 ↔ I = ⊥ := sorry

theorem coe_to_fractional_ideal_ne_zero {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {I : ideal R} (hS : S ≤ non_zero_divisors R) : ↑I ≠ 0 ↔ I ≠ ⊥ :=
  iff.mpr not_iff_not (coe_to_fractional_ideal_eq_zero hS)

theorem coe_to_submodule_eq_bot {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {I : fractional_ideal f} : ↑I = ⊥ ↔ I = 0 := sorry

theorem coe_to_submodule_ne_bot {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {I : fractional_ideal f} : ↑I ≠ ⊥ ↔ I ≠ 0 :=
  iff.mpr not_iff_not coe_to_submodule_eq_bot

protected instance inhabited {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} : Inhabited (fractional_ideal f) :=
  { default := 0 }

protected instance has_one {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} : HasOne (fractional_ideal f) :=
  { one := ↑1 }

theorem mem_one_iff {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {x : P} : x ∈ 1 ↔ ∃ (x' : R), coe_fn (localization_map.to_map f) x' = x := sorry

theorem coe_mem_one {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} (x : R) : coe_fn (localization_map.to_map f) x ∈ 1 :=
  iff.mpr mem_one_iff (Exists.intro x rfl)

theorem one_mem_one {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} : 1 ∈ 1 :=
  iff.mpr mem_one_iff (Exists.intro 1 (ring_hom.map_one (localization_map.to_map f)))

/-- `(1 : fractional_ideal f)` is defined as the R-submodule `f(R) ≤ K`.

However, this is not definitionally equal to `1 : submodule R K`,
which is proved in the actual `simp` lemma `coe_one`. -/
theorem coe_one_eq_coe_submodule_one {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} : ↑1 = localization_map.coe_submodule f 1 :=
  rfl

@[simp] theorem coe_one {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} : ↑1 = 1 := sorry

/-!
### `lattice` section

Defines the order on fractional ideals as inclusion of their underlying sets,
and ports the lattice structure on submodules to fractional ideals.
-/

protected instance partial_order {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} : partial_order (fractional_ideal f) :=
  partial_order.mk (fun (I J : fractional_ideal f) => subtype.val I ≤ subtype.val J)
    (preorder.lt._default fun (I J : fractional_ideal f) => subtype.val I ≤ subtype.val J) sorry sorry sorry

theorem le_iff_mem {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {I : fractional_ideal f} {J : fractional_ideal f} : I ≤ J ↔ ∀ (x : P), x ∈ I → x ∈ J :=
  iff.rfl

@[simp] theorem coe_le_coe {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {I : fractional_ideal f} {J : fractional_ideal f} : ↑I ≤ ↑J ↔ I ≤ J :=
  iff.rfl

theorem zero_le {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} (I : fractional_ideal f) : 0 ≤ I := sorry

protected instance order_bot {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} : order_bot (fractional_ideal f) :=
  order_bot.mk 0 partial_order.le partial_order.lt sorry sorry sorry zero_le

@[simp] theorem bot_eq_zero {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} : ⊥ = 0 :=
  rfl

@[simp] theorem le_zero_iff {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {I : fractional_ideal f} : I ≤ 0 ↔ I = 0 :=
  le_bot_iff

theorem eq_zero_iff {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {I : fractional_ideal f} : I = 0 ↔ ∀ (x : P), x ∈ I → x = 0 := sorry

theorem fractional_sup {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} (I : fractional_ideal f) (J : fractional_ideal f) : is_fractional f (subtype.val I ⊔ subtype.val J) := sorry

theorem fractional_inf {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} (I : fractional_ideal f) (J : fractional_ideal f) : is_fractional f (subtype.val I ⊓ subtype.val J) := sorry

protected instance lattice {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} : lattice (fractional_ideal f) :=
  lattice.mk (fun (I J : fractional_ideal f) => { val := subtype.val I ⊔ subtype.val J, property := fractional_sup I J })
    partial_order.le partial_order.lt sorry sorry sorry sorry sorry sorry
    (fun (I J : fractional_ideal f) => { val := subtype.val I ⊓ subtype.val J, property := fractional_inf I J }) sorry
    sorry sorry

protected instance semilattice_sup_bot {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} : semilattice_sup_bot (fractional_ideal f) :=
  semilattice_sup_bot.mk order_bot.bot order_bot.le order_bot.lt sorry sorry sorry sorry lattice.sup sorry sorry sorry

protected instance has_add {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} : Add (fractional_ideal f) :=
  { add := has_sup.sup }

@[simp] theorem sup_eq_add {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} (I : fractional_ideal f) (J : fractional_ideal f) : I ⊔ J = I + J :=
  rfl

@[simp] theorem coe_add {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} (I : fractional_ideal f) (J : fractional_ideal f) : ↑(I + J) = ↑I + ↑J :=
  rfl

theorem fractional_mul {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} (I : fractional_ideal f) (J : fractional_ideal f) : is_fractional f (subtype.val I * subtype.val J) := sorry

/-- `fractional_ideal.mul` is the product of two fractional ideals,
used to define the `has_mul` instance.

This is only an auxiliary definition: the preferred way of writing `I.mul J` is `I * J`.

Elaborated terms involving `fractional_ideal` tend to grow quite large,
so by making definitions irreducible, we hope to avoid deep unfolds.
-/
def mul {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} (I : fractional_ideal f) (J : fractional_ideal f) : fractional_ideal f :=
  { val := subtype.val I * subtype.val J, property := fractional_mul I J }

protected instance has_mul {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} : Mul (fractional_ideal f) :=
  { mul := fun (I J : fractional_ideal f) => mul I J }

@[simp] theorem mul_eq_mul {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} (I : fractional_ideal f) (J : fractional_ideal f) : mul I J = I * J :=
  rfl

@[simp] theorem coe_mul {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} (I : fractional_ideal f) (J : fractional_ideal f) : ↑(I * J) = ↑I * ↑J :=
  rfl

theorem mul_left_mono {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} (I : fractional_ideal f) : monotone (Mul.mul I) := sorry

theorem mul_right_mono {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} (I : fractional_ideal f) : monotone fun (J : fractional_ideal f) => J * I := sorry

theorem mul_mem_mul {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {I : fractional_ideal f} {J : fractional_ideal f} {i : localization_map.codomain f} {j : localization_map.codomain f} (hi : i ∈ I) (hj : j ∈ J) : i * j ∈ I * J :=
  submodule.mul_mem_mul hi hj

theorem mul_le {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {I : fractional_ideal f} {J : fractional_ideal f} {K : fractional_ideal f} : I * J ≤ K ↔ ∀ (i : P), i ∈ I → ∀ (j : P), j ∈ J → i * j ∈ K :=
  submodule.mul_le

protected theorem mul_induction_on {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {I : fractional_ideal f} {J : fractional_ideal f} {C : localization_map.codomain f → Prop} {r : localization_map.codomain f} (hr : r ∈ I * J) (hm : ∀ (i : localization_map.codomain f), i ∈ I → ∀ (j : localization_map.codomain f), j ∈ J → C (i * j)) (h0 : C 0) (ha : ∀ (x y : localization_map.codomain f), C x → C y → C (x + y)) (hs : ∀ (r : R) (x : localization_map.codomain f), C x → C (r • x)) : C r :=
  submodule.mul_induction_on hr hm h0 ha hs

protected instance comm_semiring {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} : comm_semiring (fractional_ideal f) :=
  comm_semiring.mk Add.add sorry 0 sorry sorry sorry Mul.mul sorry 1 sorry sorry sorry sorry sorry sorry sorry

theorem add_le_add_left {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {I : fractional_ideal f} {J : fractional_ideal f} (hIJ : I ≤ J) (J' : fractional_ideal f) : J' + I ≤ J' + J :=
  sup_le_sup_left hIJ J'

theorem mul_le_mul_left {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {I : fractional_ideal f} {J : fractional_ideal f} (hIJ : I ≤ J) (J' : fractional_ideal f) : J' * I ≤ J' * J :=
  iff.mpr mul_le fun (k : P) (hk : k ∈ J') (j : P) (hj : j ∈ I) => mul_mem_mul hk (hIJ hj)

theorem le_self_mul_self {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {I : fractional_ideal f} (hI : 1 ≤ I) : I ≤ I * I := sorry

theorem mul_self_le_self {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {I : fractional_ideal f} (hI : I ≤ 1) : I * I ≤ I := sorry

theorem coe_ideal_le_one {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {I : ideal R} : ↑I ≤ 1 := sorry

theorem le_one_iff_exists_coe_ideal {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {J : fractional_ideal f} : J ≤ 1 ↔ ∃ (I : ideal R), ↑I = J := sorry

theorem fractional_map {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {P' : Type u_3} [comm_ring P'] {f' : localization_map S P'} (g : alg_hom R (localization_map.codomain f) (localization_map.codomain f')) (I : fractional_ideal f) : is_fractional f' (submodule.map (alg_hom.to_linear_map g) (subtype.val I)) := sorry

/-- `I.map g` is the pushforward of the fractional ideal `I` along the algebra morphism `g` -/
def map {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {P' : Type u_3} [comm_ring P'] {f' : localization_map S P'} (g : alg_hom R (localization_map.codomain f) (localization_map.codomain f')) : fractional_ideal f → fractional_ideal f' :=
  fun (I : fractional_ideal f) =>
    { val := submodule.map (alg_hom.to_linear_map g) (subtype.val I), property := fractional_map g I }

@[simp] theorem coe_map {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {P' : Type u_3} [comm_ring P'] {f' : localization_map S P'} (g : alg_hom R (localization_map.codomain f) (localization_map.codomain f')) (I : fractional_ideal f) : ↑(map g I) = submodule.map (alg_hom.to_linear_map g) ↑I :=
  rfl

@[simp] theorem mem_map {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {P' : Type u_3} [comm_ring P'] {f' : localization_map S P'} {I : fractional_ideal f} {g : alg_hom R (localization_map.codomain f) (localization_map.codomain f')} {y : localization_map.codomain f'} : y ∈ map g I ↔ ∃ (x : localization_map.codomain f), x ∈ I ∧ coe_fn g x = y :=
  submodule.mem_map

@[simp] theorem map_id {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} (I : fractional_ideal f) : map (alg_hom.id R (localization_map.codomain f)) I = I :=
  ext (submodule.map_id (subtype.val I))

@[simp] theorem map_comp {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {P' : Type u_3} [comm_ring P'] {f' : localization_map S P'} {P'' : Type u_4} [comm_ring P''] {f'' : localization_map S P''} (I : fractional_ideal f) (g : alg_hom R (localization_map.codomain f) (localization_map.codomain f')) (g' : alg_hom R (localization_map.codomain f') (localization_map.codomain f'')) : map (alg_hom.comp g' g) I = map g' (map g I) :=
  ext (submodule.map_comp (alg_hom.to_linear_map g) (alg_hom.to_linear_map g') (subtype.val I))

@[simp] theorem map_coe_ideal {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {P' : Type u_3} [comm_ring P'] {f' : localization_map S P'} (g : alg_hom R (localization_map.codomain f) (localization_map.codomain f')) (I : ideal R) : map g ↑I = ↑I := sorry

@[simp] theorem map_one {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {P' : Type u_3} [comm_ring P'] {f' : localization_map S P'} (g : alg_hom R (localization_map.codomain f) (localization_map.codomain f')) : map g 1 = 1 :=
  map_coe_ideal g 1

@[simp] theorem map_zero {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {P' : Type u_3} [comm_ring P'] {f' : localization_map S P'} (g : alg_hom R (localization_map.codomain f) (localization_map.codomain f')) : map g 0 = 0 :=
  map_coe_ideal g 0

@[simp] theorem map_add {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {P' : Type u_3} [comm_ring P'] {f' : localization_map S P'} (I : fractional_ideal f) (J : fractional_ideal f) (g : alg_hom R (localization_map.codomain f) (localization_map.codomain f')) : map g (I + J) = map g I + map g J :=
  ext (submodule.map_sup (subtype.val I) (subtype.val J) (alg_hom.to_linear_map g))

@[simp] theorem map_mul {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {P' : Type u_3} [comm_ring P'] {f' : localization_map S P'} (I : fractional_ideal f) (J : fractional_ideal f) (g : alg_hom R (localization_map.codomain f) (localization_map.codomain f')) : map g (I * J) = map g I * map g J :=
  ext (submodule.map_mul (subtype.val I) (subtype.val J) g)

@[simp] theorem map_map_symm {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {P' : Type u_3} [comm_ring P'] {f' : localization_map S P'} (I : fractional_ideal f) (g : alg_equiv R (localization_map.codomain f) (localization_map.codomain f')) : map (↑(alg_equiv.symm g)) (map (↑g) I) = I := sorry

@[simp] theorem map_symm_map {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {P' : Type u_3} [comm_ring P'] {f' : localization_map S P'} (I : fractional_ideal f') (g : alg_equiv R (localization_map.codomain f) (localization_map.codomain f')) : map (↑g) (map (↑(alg_equiv.symm g)) I) = I := sorry

/-- If `g` is an equivalence, `map g` is an isomorphism -/
def map_equiv {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {P' : Type u_3} [comm_ring P'] {f' : localization_map S P'} (g : alg_equiv R (localization_map.codomain f) (localization_map.codomain f')) : fractional_ideal f ≃+* fractional_ideal f' :=
  ring_equiv.mk (map ↑g) (map ↑(alg_equiv.symm g)) sorry sorry sorry sorry

@[simp] theorem coe_fun_map_equiv {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {P' : Type u_3} [comm_ring P'] {f' : localization_map S P'} (g : alg_equiv R (localization_map.codomain f) (localization_map.codomain f')) : ⇑(map_equiv g) = map ↑g :=
  rfl

@[simp] theorem map_equiv_apply {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {P' : Type u_3} [comm_ring P'] {f' : localization_map S P'} (g : alg_equiv R (localization_map.codomain f) (localization_map.codomain f')) (I : fractional_ideal f) : coe_fn (map_equiv g) I = map (↑g) I :=
  rfl

@[simp] theorem map_equiv_symm {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {P' : Type u_3} [comm_ring P'] {f' : localization_map S P'} (g : alg_equiv R (localization_map.codomain f) (localization_map.codomain f')) : ring_equiv.symm (map_equiv g) = map_equiv (alg_equiv.symm g) :=
  rfl

@[simp] theorem map_equiv_refl {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} : map_equiv alg_equiv.refl = ring_equiv.refl (fractional_ideal f) := sorry

theorem is_fractional_span_iff {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {s : set (localization_map.codomain f)} : is_fractional f (submodule.span R s) ↔
  ∃ (a : R), ∃ (H : a ∈ S), ∀ (b : P), b ∈ s → localization_map.is_integer f (coe_fn (localization_map.to_map f) a * b) := sorry

theorem is_fractional_of_fg {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {I : submodule R (localization_map.codomain f)} (hI : submodule.fg I) : is_fractional f I := sorry

/-- `canonical_equiv f f'` is the canonical equivalence between the fractional
ideals in `f.codomain` and in `f'.codomain` -/
def canonical_equiv {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {P' : Type u_3} [comm_ring P'] (f : localization_map S P) (f' : localization_map S P') : fractional_ideal f ≃+* fractional_ideal f' :=
  map_equiv
    (alg_equiv.mk (ring_equiv.to_fun (localization_map.ring_equiv_of_ring_equiv f f' (ring_equiv.refl R) sorry))
      (ring_equiv.inv_fun (localization_map.ring_equiv_of_ring_equiv f f' (ring_equiv.refl R) sorry)) sorry sorry sorry
      sorry sorry)

@[simp] theorem mem_canonical_equiv_apply {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {P' : Type u_3} [comm_ring P'] {f' : localization_map S P'} {I : fractional_ideal f} {x : localization_map.codomain f'} : x ∈ coe_fn (canonical_equiv f f') I ↔
  ∃ (y : P),
    ∃ (H : y ∈ I),
      coe_fn
          (localization_map.map f
            (fun (_x : ↥S) =>
              (fun (_a : ↥S) => subtype.cases_on _a fun (val : R) (property : val ∈ S) => idRhs (val ∈ S) property) _x)
            f')
          y =
        x := sorry

@[simp] theorem canonical_equiv_symm {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {P' : Type u_3} [comm_ring P'] (f : localization_map S P) (f' : localization_map S P') : ring_equiv.symm (canonical_equiv f f') = canonical_equiv f' f := sorry

@[simp] theorem canonical_equiv_flip {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {P' : Type u_3} [comm_ring P'] (f : localization_map S P) (f' : localization_map S P') (I : fractional_ideal f') : coe_fn (canonical_equiv f f') (coe_fn (canonical_equiv f' f) I) = I := sorry

/-!
### `fraction_map` section

This section concerns fractional ideals in the field of fractions,
i.e. the type `fractional_ideal g` when `g` is a `fraction_map R K`.
-/

/-- Nonzero fractional ideals contain a nonzero integer. -/
theorem exists_ne_zero_mem_is_integer {R : Type u_1} [comm_ring R] {K : Type u_3} [field K] {g : fraction_map R K} {I : fractional_ideal g} [nontrivial R] (hI : I ≠ 0) : ∃ (x : R), ∃ (H : x ≠ 0), coe_fn (localization_map.to_map g) x ∈ I := sorry

theorem map_ne_zero {R : Type u_1} [comm_ring R] {K : Type u_3} {K' : Type u_4} [field K] [field K'] {g : fraction_map R K} {g' : fraction_map R K'} {I : fractional_ideal g} (h : alg_hom R (localization_map.codomain g) (localization_map.codomain g')) [nontrivial R] (hI : I ≠ 0) : map h I ≠ 0 := sorry

@[simp] theorem map_eq_zero_iff {R : Type u_1} [comm_ring R] {K : Type u_3} {K' : Type u_4} [field K] [field K'] {g : fraction_map R K} {g' : fraction_map R K'} {I : fractional_ideal g} (h : alg_hom R (localization_map.codomain g) (localization_map.codomain g')) [nontrivial R] : map h I = 0 ↔ I = 0 :=
  { mp := imp_of_not_imp_not (map h I = 0) (I = 0) (map_ne_zero h), mpr := fun (hI : I = 0) => Eq.symm hI ▸ map_zero h }

/-!
### `quotient` section

This section defines the ideal quotient of fractional ideals.

In this section we need that each non-zero `y : R` has an inverse in
the localization, i.e. that the localization is a field. We satisfy this
assumption by taking `S = non_zero_divisors R`, `R`'s localization at which
is a field because `R` is a domain.
-/

protected instance nontrivial {R₁ : Type u_3} [integral_domain R₁] {K : Type u_4} [field K] {g : fraction_map R₁ K} : nontrivial (fractional_ideal g) :=
  nontrivial.mk
    (Exists.intro 0
      (Exists.intro 1
        fun (h : 0 = 1) =>
          (fun (this : 1 ∈ 0) => one_ne_zero (iff.mp mem_zero_iff this))
            (eq.mpr (id (Eq._oldrec (Eq.refl (1 ∈ 0)) (Eq.symm (ring_hom.map_one (localization_map.to_map g)))))
              (eq.mpr
                ((fun (ᾰ ᾰ_1 : K) (e_2 : ᾰ = ᾰ_1) (ᾰ_2 ᾰ_3 : fractional_ideal g) (e_3 : ᾰ_2 = ᾰ_3) =>
                    congr (congr_arg has_mem.mem e_2) e_3)
                  (coe_fn (localization_map.to_map g) 1) (coe_fn (localization_map.to_map g) 1)
                  (Eq.refl (coe_fn (localization_map.to_map g) 1)) 0 1 h)
                (coe_mem_one 1)))))

theorem fractional_div_of_nonzero {R₁ : Type u_3} [integral_domain R₁] {K : Type u_4} [field K] {g : fraction_map R₁ K} {I : fractional_ideal g} {J : fractional_ideal g} (h : J ≠ 0) : is_fractional g (subtype.val I / subtype.val J) := sorry

protected instance fractional_ideal_has_div {R₁ : Type u_3} [integral_domain R₁] {K : Type u_4} [field K] {g : fraction_map R₁ K} : Div (fractional_ideal g) :=
  { div :=
      fun (I J : fractional_ideal g) =>
        dite (J = 0) (fun (h : J = 0) => 0)
          fun (h : ¬J = 0) => { val := subtype.val I / subtype.val J, property := fractional_div_of_nonzero h } }

@[simp] theorem div_zero {R₁ : Type u_3} [integral_domain R₁] {K : Type u_4} [field K] {g : fraction_map R₁ K} {I : fractional_ideal g} : I / 0 = 0 :=
  dif_pos rfl

theorem div_nonzero {R₁ : Type u_3} [integral_domain R₁] {K : Type u_4} [field K] {g : fraction_map R₁ K} {I : fractional_ideal g} {J : fractional_ideal g} (h : J ≠ 0) : I / J = { val := subtype.val I / subtype.val J, property := fractional_div_of_nonzero h } :=
  dif_neg h

@[simp] theorem coe_div {R₁ : Type u_3} [integral_domain R₁] {K : Type u_4} [field K] {g : fraction_map R₁ K} {I : fractional_ideal g} {J : fractional_ideal g} (hJ : J ≠ 0) : ↑(I / J) = ↑I / ↑J := sorry

theorem mem_div_iff_of_nonzero {R₁ : Type u_3} [integral_domain R₁] {K : Type u_4} [field K] {g : fraction_map R₁ K} {I : fractional_ideal g} {J : fractional_ideal g} (h : J ≠ 0) {x : K} : x ∈ I / J ↔ ∀ (y : K), y ∈ J → x * y ∈ I :=
  eq.mpr (id (Eq._oldrec (Eq.refl (x ∈ I / J ↔ ∀ (y : K), y ∈ J → x * y ∈ I)) (div_nonzero h)))
    submodule.mem_div_iff_forall_mul_mem

theorem mul_one_div_le_one {R₁ : Type u_3} [integral_domain R₁] {K : Type u_4} [field K] {g : fraction_map R₁ K} {I : fractional_ideal g} : I * (1 / I) ≤ 1 := sorry

theorem le_self_mul_one_div {R₁ : Type u_3} [integral_domain R₁] {K : Type u_4} [field K] {g : fraction_map R₁ K} {I : fractional_ideal g} (hI : I ≤ 1) : I ≤ I * (1 / I) := sorry

theorem le_div_iff_of_nonzero {R₁ : Type u_3} [integral_domain R₁] {K : Type u_4} [field K] {g : fraction_map R₁ K} {I : fractional_ideal g} {J : fractional_ideal g} {J' : fractional_ideal g} (hJ' : J' ≠ 0) : I ≤ J / J' ↔ ∀ (x : K), x ∈ I → ∀ (y : K), y ∈ J' → x * y ∈ J := sorry

theorem le_div_iff_mul_le {R₁ : Type u_3} [integral_domain R₁] {K : Type u_4} [field K] {g : fraction_map R₁ K} {I : fractional_ideal g} {J : fractional_ideal g} {J' : fractional_ideal g} (hJ' : J' ≠ 0) : I ≤ J / J' ↔ I * J' ≤ J := sorry

@[simp] theorem div_one {R₁ : Type u_3} [integral_domain R₁] {K : Type u_4} [field K] {g : fraction_map R₁ K} {I : fractional_ideal g} : I / 1 = I := sorry

theorem ne_zero_of_mul_eq_one {R₁ : Type u_3} [integral_domain R₁] {K : Type u_4} [field K] {g : fraction_map R₁ K} (I : fractional_ideal g) (J : fractional_ideal g) (h : I * J = 1) : I ≠ 0 := sorry

theorem eq_one_div_of_mul_eq_one {R₁ : Type u_3} [integral_domain R₁] {K : Type u_4} [field K] {g : fraction_map R₁ K} (I : fractional_ideal g) (J : fractional_ideal g) (h : I * J = 1) : J = 1 / I :=
  congr_arg units.inv (units.ext rfl)

theorem mul_div_self_cancel_iff {R₁ : Type u_3} [integral_domain R₁] {K : Type u_4} [field K] {g : fraction_map R₁ K} {I : fractional_ideal g} : I * (1 / I) = 1 ↔ ∃ (J : fractional_ideal g), I * J = 1 := sorry

@[simp] theorem map_div {R₁ : Type u_3} [integral_domain R₁] {K : Type u_4} [field K] {g : fraction_map R₁ K} {K' : Type u_5} [field K'] {g' : fraction_map R₁ K'} (I : fractional_ideal g) (J : fractional_ideal g) (h : alg_equiv R₁ (localization_map.codomain g) (localization_map.codomain g')) : map (↑h) (I / J) = map (↑h) I / map (↑h) J := sorry

@[simp] theorem map_one_div {R₁ : Type u_3} [integral_domain R₁] {K : Type u_4} [field K] {g : fraction_map R₁ K} {K' : Type u_5} [field K'] {g' : fraction_map R₁ K'} (I : fractional_ideal g) (h : alg_equiv R₁ (localization_map.codomain g) (localization_map.codomain g')) : map (↑h) (1 / I) = 1 / map (↑h) I :=
  eq.mpr (id (Eq._oldrec (Eq.refl (map (↑h) (1 / I) = 1 / map (↑h) I)) (map_div 1 I h)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (map (↑h) 1 / map (↑h) I = 1 / map (↑h) I)) (map_one ↑h)))
      (Eq.refl (1 / map (↑h) I)))

theorem is_fractional_span_singleton {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} (x : localization_map.codomain f) : is_fractional f (submodule.span R (singleton x)) := sorry

/-- `span_singleton x` is the fractional ideal generated by `x` if `0 ∉ S` -/
def span_singleton {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} (x : localization_map.codomain f) : fractional_ideal f :=
  { val := submodule.span R (singleton x), property := is_fractional_span_singleton x }

@[simp] theorem coe_span_singleton {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} (x : localization_map.codomain f) : ↑(span_singleton x) = submodule.span R (singleton x) :=
  rfl

@[simp] theorem mem_span_singleton {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {x : localization_map.codomain f} {y : localization_map.codomain f} : x ∈ span_singleton y ↔ ∃ (z : R), z • y = x :=
  submodule.mem_span_singleton

theorem mem_span_singleton_self {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} (x : localization_map.codomain f) : x ∈ span_singleton x :=
  iff.mpr mem_span_singleton (Exists.intro 1 (one_smul R x))

theorem eq_span_singleton_of_principal {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} (I : fractional_ideal f) [submodule.is_principal ↑I] : I = span_singleton (submodule.is_principal.generator ↑I) :=
  ext (Eq.symm (submodule.is_principal.span_singleton_generator (subtype.val I)))

theorem is_principal_iff {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} (I : fractional_ideal f) : submodule.is_principal ↑I ↔ ∃ (x : localization_map.codomain f), I = span_singleton x := sorry

@[simp] theorem span_singleton_zero {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} : span_singleton 0 = 0 := sorry

theorem span_singleton_eq_zero_iff {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {y : localization_map.codomain f} : span_singleton y = 0 ↔ y = 0 := sorry

theorem span_singleton_ne_zero_iff {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {y : localization_map.codomain f} : span_singleton y ≠ 0 ↔ y ≠ 0 :=
  not_congr span_singleton_eq_zero_iff

@[simp] theorem span_singleton_one {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} : span_singleton 1 = 1 := sorry

@[simp] theorem span_singleton_mul_span_singleton {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} (x : localization_map.codomain f) (y : localization_map.codomain f) : span_singleton x * span_singleton y = span_singleton (x * y) := sorry

@[simp] theorem coe_ideal_span_singleton {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} (x : R) : ↑(submodule.span R (singleton x)) = span_singleton (coe_fn (localization_map.to_map f) x) := sorry

@[simp] theorem canonical_equiv_span_singleton {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] (f : localization_map S P) {P' : Type u_3} [comm_ring P'] (f' : localization_map S P') (x : localization_map.codomain f) : coe_fn (canonical_equiv f f') (span_singleton x) =
  span_singleton
    (coe_fn
      (localization_map.map f
        ((fun (this : ∀ (y : ↥S), coe_fn (ring_hom.id R) (subtype.val y) ∈ S) => this)
          fun (y : ↥S) => subtype.property y)
        f')
      x) := sorry

theorem mem_singleton_mul {R : Type u_1} [comm_ring R] {S : submonoid R} {P : Type u_2} [comm_ring P] {f : localization_map S P} {x : localization_map.codomain f} {y : localization_map.codomain f} {I : fractional_ideal f} : y ∈ span_singleton x * I ↔ ∃ (y' : localization_map.codomain f), ∃ (H : y' ∈ I), y = x * y' := sorry

theorem one_div_span_singleton {R₁ : Type u_3} [integral_domain R₁] {K : Type u_4} [field K] {g : fraction_map R₁ K} (x : localization_map.codomain g) : 1 / span_singleton x = span_singleton (x⁻¹) := sorry

@[simp] theorem div_span_singleton {R₁ : Type u_3} [integral_domain R₁] {K : Type u_4} [field K] {g : fraction_map R₁ K} (J : fractional_ideal g) (d : localization_map.codomain g) : J / span_singleton d = span_singleton (d⁻¹) * J := sorry

theorem exists_eq_span_singleton_mul {R₁ : Type u_3} [integral_domain R₁] {K : Type u_4} [field K] {g : fraction_map R₁ K} (I : fractional_ideal g) : ∃ (a : R₁), ∃ (aI : ideal R₁), a ≠ 0 ∧ I = span_singleton (coe_fn (localization_map.to_map g) a⁻¹) * ↑aI := sorry

protected instance is_principal {K : Type u_4} [field K] {R : Type u_1} [integral_domain R] [is_principal_ideal_ring R] {f : fraction_map R K} (I : fractional_ideal f) : submodule.is_principal ↑I := sorry

theorem is_noetherian_zero {R₁ : Type u_3} [integral_domain R₁] {K : Type u_4} [field K] {g : fraction_map R₁ K} : is_noetherian R₁ ↥0 := sorry

theorem is_noetherian_iff {R₁ : Type u_3} [integral_domain R₁] {K : Type u_4} [field K] {g : fraction_map R₁ K} {I : fractional_ideal g} : is_noetherian R₁ ↥I ↔ ∀ (J : fractional_ideal g), J ≤ I → submodule.fg ↑J := sorry

theorem is_noetherian_coe_to_fractional_ideal {R₁ : Type u_3} [integral_domain R₁] {K : Type u_4} [field K] {g : fraction_map R₁ K} [is_noetherian_ring R₁] (I : ideal R₁) : is_noetherian R₁ ↥↑I := sorry

theorem is_noetherian_span_singleton_inv_to_map_mul {R₁ : Type u_3} [integral_domain R₁] {K : Type u_4} [field K] {g : fraction_map R₁ K} (x : R₁) {I : fractional_ideal g} (hI : is_noetherian R₁ ↥I) : is_noetherian R₁ ↥(span_singleton (coe_fn (localization_map.to_map g) x⁻¹) * I) := sorry

/-- Every fractional ideal of a noetherian integral domain is noetherian. -/
theorem is_noetherian {R₁ : Type u_3} [integral_domain R₁] {K : Type u_4} [field K] {g : fraction_map R₁ K} [is_noetherian_ring R₁] (I : fractional_ideal g) : is_noetherian R₁ ↥I := sorry

