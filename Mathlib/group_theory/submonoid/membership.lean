/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.group_theory.submonoid.operations
import Mathlib.algebra.big_operators.basic
import Mathlib.algebra.free_monoid
import Mathlib.PostPort

universes u_1 u_2 u_3 

namespace Mathlib

/-!
# Submonoids: membership criteria

In this file we prove various facts about membership in a submonoid:

* `list_prod_mem`, `multiset_prod_mem`, `prod_mem`: if each element of a collection belongs
  to a multiplicative submonoid, then so does their product;
* `list_sum_mem`, `multiset_sum_mem`, `sum_mem`: if each element of a collection belongs
  to an additive submonoid, then so does their sum;
* `pow_mem`, `nsmul_mem`: if `x ∈ S` where `S` is a multiplicative (resp., additive) submonoid and
  `n` is a natural number, then `x^n` (resp., `n •ℕ x`) belongs to `S`;
* `mem_supr_of_directed`, `coe_supr_of_directed`, `mem_Sup_of_directed_on`,
  `coe_Sup_of_directed_on`: the supremum of a directed collection of submonoid is their union.
* `sup_eq_range`, `mem_sup`: supremum of two submonoids `S`, `T` of a commutative monoid is the set
  of products;
* `closure_singleton_eq`, `mem_closure_singleton`: the multiplicative (resp., additive) closure
  of `{x}` consists of powers (resp., natural multiples) of `x`.

## Tags
submonoid, submonoids
-/

namespace submonoid


/-- Product of a list of elements in a submonoid is in the submonoid. -/
theorem Mathlib.add_submonoid.list_sum_mem {M : Type u_1} [add_monoid M] (S : add_submonoid M) {l : List M} : (∀ (x : M), x ∈ l → x ∈ S) → list.sum l ∈ S := sorry

/-- Product of a multiset of elements in a submonoid of a `comm_monoid` is in the submonoid. -/
theorem Mathlib.add_submonoid.multiset_sum_mem {M : Type u_1} [add_comm_monoid M] (S : add_submonoid M) (m : multiset M) : (∀ (a : M), a ∈ m → a ∈ S) → multiset.sum m ∈ S := sorry

/-- Product of elements of a submonoid of a `comm_monoid` indexed by a `finset` is in the
    submonoid. -/
theorem Mathlib.add_submonoid.sum_mem {M : Type u_1} [add_comm_monoid M] (S : add_submonoid M) {ι : Type u_2} {t : finset ι} {f : ι → M} (h : ∀ (c : ι), c ∈ t → f c ∈ S) : (finset.sum t fun (c : ι) => f c) ∈ S := sorry

theorem pow_mem {M : Type u_1} [monoid M] (S : submonoid M) {x : M} (hx : x ∈ S) (n : ℕ) : x ^ n ∈ S := sorry

theorem mem_supr_of_directed {M : Type u_1} [monoid M] {ι : Sort u_2} [hι : Nonempty ι] {S : ι → submonoid M} (hS : directed LessEq S) {x : M} : (x ∈ supr fun (i : ι) => S i) ↔ ∃ (i : ι), x ∈ S i := sorry

theorem Mathlib.add_submonoid.coe_supr_of_directed {M : Type u_1} [add_monoid M] {ι : Sort u_2} [Nonempty ι] {S : ι → add_submonoid M} (hS : directed LessEq S) : ↑(supr fun (i : ι) => S i) = set.Union fun (i : ι) => ↑(S i) := sorry

theorem Mathlib.add_submonoid.mem_Sup_of_directed_on {M : Type u_1} [add_monoid M] {S : set (add_submonoid M)} (Sne : set.nonempty S) (hS : directed_on LessEq S) {x : M} : x ∈ Sup S ↔ ∃ (s : add_submonoid M), ∃ (H : s ∈ S), x ∈ s := sorry

theorem Mathlib.add_submonoid.coe_Sup_of_directed_on {M : Type u_1} [add_monoid M] {S : set (add_submonoid M)} (Sne : set.nonempty S) (hS : directed_on LessEq S) : ↑(Sup S) = set.Union fun (s : add_submonoid M) => set.Union fun (H : s ∈ S) => ↑s := sorry

theorem mem_sup_left {M : Type u_1} [monoid M] {S : submonoid M} {T : submonoid M} {x : M} : x ∈ S → x ∈ S ⊔ T :=
  (fun (this : S ≤ S ⊔ T) => this) le_sup_left

theorem Mathlib.add_submonoid.mem_sup_right {M : Type u_1} [add_monoid M] {S : add_submonoid M} {T : add_submonoid M} {x : M} : x ∈ T → x ∈ S ⊔ T :=
  (fun (this : T ≤ S ⊔ T) => this) le_sup_right

theorem Mathlib.add_submonoid.mem_supr_of_mem {M : Type u_1} [add_monoid M] {ι : Type u_2} {S : ι → add_submonoid M} (i : ι) {x : M} : x ∈ S i → x ∈ supr S :=
  (fun (this : S i ≤ supr S) => this) (le_supr S i)

theorem mem_Sup_of_mem {M : Type u_1} [monoid M] {S : set (submonoid M)} {s : submonoid M} (hs : s ∈ S) {x : M} : x ∈ s → x ∈ Sup S :=
  (fun (this : s ≤ Sup S) => this) (le_Sup hs)

end submonoid


namespace free_monoid


theorem closure_range_of {α : Type u_3} : submonoid.closure (set.range of) = ⊤ := sorry

end free_monoid


namespace submonoid


theorem closure_singleton_eq {M : Type u_1} [monoid M] (x : M) : closure (singleton x) = monoid_hom.mrange (coe_fn (powers_hom M) x) := sorry

/-- The submonoid generated by an element of a monoid equals the set of natural number powers of
    the element. -/
theorem mem_closure_singleton {M : Type u_1} [monoid M] {x : M} {y : M} : y ∈ closure (singleton x) ↔ ∃ (n : ℕ), x ^ n = y := sorry

theorem mem_closure_singleton_self {M : Type u_1} [monoid M] {y : M} : y ∈ closure (singleton y) :=
  iff.mpr mem_closure_singleton (Exists.intro 1 (pow_one y))

theorem closure_singleton_one {M : Type u_1} [monoid M] : closure (singleton 1) = ⊥ := sorry

theorem Mathlib.add_submonoid.closure_eq_mrange {M : Type u_1} [add_monoid M] (s : set M) : add_submonoid.closure s = add_monoid_hom.mrange (coe_fn free_add_monoid.lift coe) := sorry

theorem Mathlib.add_submonoid.exists_list_of_mem_closure {M : Type u_1} [add_monoid M] {s : set M} {x : M} (hx : x ∈ add_submonoid.closure s) : ∃ (l : List M), ∃ (hl : ∀ (y : M), y ∈ l → y ∈ s), list.sum l = x := sorry

/-- The submonoid generated by an element. -/
def powers {N : Type u_3} [monoid N] (n : N) : submonoid N :=
  copy (monoid_hom.mrange (coe_fn (powers_hom N) n)) (set.range (pow n)) sorry

@[simp] theorem mem_powers {N : Type u_3} [monoid N] (n : N) : n ∈ powers n :=
  Exists.intro 1 (pow_one n)

theorem powers_eq_closure {N : Type u_3} [monoid N] (n : N) : powers n = closure (singleton n) :=
  ext fun (x : N) => iff.symm mem_closure_singleton

theorem powers_subset {N : Type u_3} [monoid N] {n : N} {P : submonoid N} (h : n ∈ P) : powers n ≤ P := sorry

end submonoid


namespace submonoid


theorem sup_eq_range {N : Type u_3} [comm_monoid N] (s : submonoid N) (t : submonoid N) : s ⊔ t = monoid_hom.mrange (monoid_hom.coprod (subtype s) (subtype t)) := sorry

theorem Mathlib.add_submonoid.mem_sup {N : Type u_3} [add_comm_monoid N] {s : add_submonoid N} {t : add_submonoid N} {x : N} : x ∈ s ⊔ t ↔ ∃ (y : N), ∃ (H : y ∈ s), ∃ (z : N), ∃ (H : z ∈ t), y + z = x := sorry

end submonoid


namespace add_submonoid


theorem nsmul_mem {A : Type u_2} [add_monoid A] (S : add_submonoid A) {x : A} (hx : x ∈ S) (n : ℕ) : n •ℕ x ∈ S := sorry

theorem closure_singleton_eq {A : Type u_2} [add_monoid A] (x : A) : closure (singleton x) = add_monoid_hom.mrange (coe_fn (multiples_hom A) x) := sorry

/-- The `add_submonoid` generated by an element of an `add_monoid` equals the set of
natural number multiples of the element. -/
theorem mem_closure_singleton {A : Type u_2} [add_monoid A] {x : A} {y : A} : y ∈ closure (singleton x) ↔ ∃ (n : ℕ), n •ℕ x = y := sorry

theorem closure_singleton_zero {A : Type u_2} [add_monoid A] : closure (singleton 0) = ⊥ := sorry

/-- The additive submonoid generated by an element. -/
def multiples {A : Type u_2} [add_monoid A] (x : A) : add_submonoid A :=
  copy (add_monoid_hom.mrange (coe_fn (multiples_hom A) x)) (set.range fun (i : ℕ) => i •ℕ x) sorry

@[simp] theorem mem_multiples {A : Type u_2} [add_monoid A] (x : A) : x ∈ multiples x :=
  Exists.intro 1 (one_nsmul x)

theorem multiples_eq_closure {A : Type u_2} [add_monoid A] (x : A) : multiples x = closure (singleton x) :=
  ext fun (x_1 : A) => iff.symm mem_closure_singleton

theorem multiples_subset {A : Type u_2} [add_monoid A] {x : A} {P : add_submonoid A} (h : x ∈ P) : multiples x ≤ P := sorry

