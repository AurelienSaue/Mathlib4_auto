/-
Copyright (c) 2020 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.order.basic
import Mathlib.data.equiv.encodable.basic
import PostPort

universes u_2 l u_1 

namespace Mathlib

/-!
# Order ideals, cofinal sets, and the Rasiowa–Sikorski lemma

## Main definitions

Throughout this file, `P` is at least a preorder, but some sections require more
structure, such as a bottom element, a top element, or a join-semilattice structure.

- `ideal P`: the type of upward directed, downward closed subsets of `P`.
             Dual to the notion of a filter on a preorder.
- `cofinal P`: the type of subsets of `P` containing arbitrarily large elements.
               Dual to the notion of 'dense set' used in forcing.
- `ideal_of_cofinals p 𝒟`, where `p : P`, and `𝒟` is a countable family of cofinal
  subsets of P: an ideal in `P` which contains `p` and intersects every set in `𝒟`.

## References

- https://en.wikipedia.org/wiki/Ideal_(order_theory)
- https://en.wikipedia.org/wiki/Cofinal_(mathematics)
- https://en.wikipedia.org/wiki/Rasiowa–Sikorski_lemma

Note that for the Rasiowa–Sikorski lemma, Wikipedia uses the opposite ordering on `P`,
in line with most presentations of forcing.

## Tags

ideal, cofinal, dense, countable, generic

-/

namespace order


/-- An ideal on a preorder `P` is a subset of `P` that is
  - nonempty
  - upward directed
  - downward closed. -/
structure ideal (P : Type u_2) [preorder P] 
where
  carrier : set P
  nonempty : set.nonempty carrier
  directed : directed_on LessEq carrier
  mem_of_le : ∀ {x y : P}, x ≤ y → y ∈ carrier → x ∈ carrier

namespace ideal


/-- The smallest ideal containing a given element. -/
def principal {P : Type u_1} [preorder P] (p : P) : ideal P :=
  mk (set_of fun (x : P) => x ≤ p) sorry sorry sorry

protected instance inhabited {P : Type u_1} [preorder P] [Inhabited P] : Inhabited (ideal P) :=
  { default := principal Inhabited.default }

/-- An ideal of `P` can be viewed as a subset of `P`. -/
protected instance set.has_coe {P : Type u_1} [preorder P] : has_coe (ideal P) (set P) :=
  has_coe.mk carrier

/-- For the notation `x ∈ I`. -/
protected instance has_mem {P : Type u_1} [preorder P] : has_mem P (ideal P) :=
  has_mem.mk fun (x : P) (I : ideal P) => x ∈ ↑I

/-- Two ideals are equal when their underlying sets are equal. -/
theorem ext {P : Type u_1} [preorder P] (I : ideal P) (J : ideal P) : ↑I = ↑J → I = J := sorry

/-- The partial ordering by subset inclusion, inherited from `set P`. -/
protected instance partial_order {P : Type u_1} [preorder P] : partial_order (ideal P) :=
  partial_order.lift coe ext

theorem mem_of_mem_of_le {P : Type u_1} [preorder P] {x : P} {I : ideal P} {J : ideal P} : x ∈ I → I ≤ J → x ∈ J :=
  set.mem_of_mem_of_subset

@[simp] theorem principal_le_iff {P : Type u_1} [preorder P] {x : P} {I : ideal P} : principal x ≤ I ↔ x ∈ I :=
  { mp := fun (h : ∀ {y : P}, y ≤ x → y ∈ I) => h (le_refl x),
    mpr := fun (h_mem : x ∈ I) (y : P) (h_le : y ≤ x) => mem_of_le I h_le h_mem }

/-- A specific witness of `I.nonempty` when `P` has a bottom element. -/
@[simp] theorem bot_mem {P : Type u_1} [order_bot P] {I : ideal P} : ⊥ ∈ I :=
  mem_of_le I bot_le (set.nonempty.some_mem (nonempty I))

/-- There is a bottom ideal when `P` has a bottom element. -/
protected instance order_bot {P : Type u_1} [order_bot P] : order_bot (ideal P) :=
  order_bot.mk (principal ⊥) partial_order.le partial_order.lt sorry sorry sorry sorry

/-- There is a top ideal when `P` has a top element. -/
protected instance order_top {P : Type u_1} [order_top P] : order_top (ideal P) :=
  order_top.mk (principal ⊤) partial_order.le partial_order.lt sorry sorry sorry sorry

/-- A specific witness of `I.directed` when `P` has joins. -/
theorem sup_mem {P : Type u_1} [semilattice_sup P] {I : ideal P} (x : P) (y : P) (H : x ∈ I) : y ∈ I → x ⊔ y ∈ I := sorry

@[simp] theorem sup_mem_iff {P : Type u_1} [semilattice_sup P] {x : P} {y : P} {I : ideal P} : x ⊔ y ∈ I ↔ x ∈ I ∧ y ∈ I :=
  { mp := fun (h : x ⊔ y ∈ I) => { left := mem_of_le I le_sup_left h, right := mem_of_le I le_sup_right h },
    mpr := fun (h : x ∈ I ∧ y ∈ I) => sup_mem x y (and.left h) (and.right h) }

end ideal


/-- For a preorder `P`, `cofinal P` is the type of subsets of `P`
  containing arbitrarily large elements. They are the dense sets in
  the topology whose open sets are terminal segments. -/
structure cofinal (P : Type u_2) [preorder P] 
where
  carrier : set P
  mem_gt : ∀ (x : P), ∃ (y : P), ∃ (H : y ∈ carrier), x ≤ y

namespace cofinal


protected instance inhabited {P : Type u_1} [preorder P] : Inhabited (cofinal P) :=
  { default := mk set.univ sorry }

protected instance has_mem {P : Type u_1} [preorder P] : has_mem P (cofinal P) :=
  has_mem.mk fun (x : P) (D : cofinal P) => x ∈ carrier D

/-- A (noncomputable) element of a cofinal set lying above a given element. -/
def above {P : Type u_1} [preorder P] (D : cofinal P) (x : P) : P :=
  classical.some (mem_gt D x)

theorem above_mem {P : Type u_1} [preorder P] (D : cofinal P) (x : P) : above D x ∈ D :=
  exists.elim (classical.some_spec (mem_gt D x))
    fun (a : classical.some (mem_gt D x) ∈ carrier D) (_x : x ≤ classical.some (mem_gt D x)) => a

theorem le_above {P : Type u_1} [preorder P] (D : cofinal P) (x : P) : x ≤ above D x :=
  exists.elim (classical.some_spec (mem_gt D x))
    fun (_x : classical.some (mem_gt D x) ∈ carrier D) (b : x ≤ classical.some (mem_gt D x)) => b

end cofinal


/-- Given a starting point, and a countable family of cofinal sets,
  this is an increasing sequence that intersects each cofinal set. -/
def sequence_of_cofinals {P : Type u_1} [preorder P] (p : P) {ι : Type u_2} [encodable ι] (𝒟 : ι → cofinal P) : ℕ → P :=
  sorry

theorem sequence_of_cofinals.monotone {P : Type u_1} [preorder P] (p : P) {ι : Type u_2} [encodable ι] (𝒟 : ι → cofinal P) : monotone (sequence_of_cofinals p 𝒟) := sorry

theorem sequence_of_cofinals.encode_mem {P : Type u_1} [preorder P] (p : P) {ι : Type u_2} [encodable ι] (𝒟 : ι → cofinal P) (i : ι) : sequence_of_cofinals p 𝒟 (encodable.encode i + 1) ∈ 𝒟 i := sorry

/-- Given an element `p : P` and a family `𝒟` of cofinal subsets of a preorder `P`,
  indexed by a countable type, `ideal_of_cofinals p 𝒟` is an ideal in `P` which
  - contains `p`, according to `mem_ideal_of_cofinals p 𝒟`, and
  - intersects every set in `𝒟`, according to `cofinal_meets_ideal_of_cofinals p 𝒟`.

  This proves the Rasiowa–Sikorski lemma. -/
def ideal_of_cofinals {P : Type u_1} [preorder P] (p : P) {ι : Type u_2} [encodable ι] (𝒟 : ι → cofinal P) : ideal P :=
  ideal.mk (set_of fun (x : P) => ∃ (n : ℕ), x ≤ sequence_of_cofinals p 𝒟 n) sorry sorry sorry

theorem mem_ideal_of_cofinals {P : Type u_1} [preorder P] (p : P) {ι : Type u_2} [encodable ι] (𝒟 : ι → cofinal P) : p ∈ ideal_of_cofinals p 𝒟 :=
  Exists.intro 0 (le_refl p)

/-- `ideal_of_cofinals p 𝒟` is `𝒟`-generic. -/
theorem cofinal_meets_ideal_of_cofinals {P : Type u_1} [preorder P] (p : P) {ι : Type u_2} [encodable ι] (𝒟 : ι → cofinal P) (i : ι) : ∃ (x : P), x ∈ 𝒟 i ∧ x ∈ ideal_of_cofinals p 𝒟 :=
  Exists.intro (sequence_of_cofinals p 𝒟 (encodable.encode i + 1))
    { left := sequence_of_cofinals.encode_mem p 𝒟 i,
      right := Exists.intro (encodable.encode i + 1) (le_refl (sequence_of_cofinals p 𝒟 (encodable.encode i + 1))) }

