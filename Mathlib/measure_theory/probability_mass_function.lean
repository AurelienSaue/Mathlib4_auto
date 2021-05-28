/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.instances.ennreal
import Mathlib.PostPort

universes u u_1 u_2 u_3 

namespace Mathlib

/-!
# Probability mass functions

This file is about probability mass functions or discrete probability measures:
a function `α → ℝ≥0` such that the values have (infinite) sum `1`.

This file features the monadic structure of `pmf` and the Bernoulli distribution

## Implementation Notes

This file is not yet connected to the `measure_theory` library in any way.
At some point we need to define a `measure` from a `pmf` and prove the appropriate lemmas about
that.

## Tags

probability mass function, discrete probability measure, bernoulli distribution
-/

/-- A probability mass function, or discrete probability measures is a function `α → ℝ≥0` such that
  the values have (infinite) sum `1`. -/
def pmf (α : Type u)  :=
  Subtype fun (f : α → nnreal) => has_sum f 1

namespace pmf


protected instance has_coe_to_fun {α : Type u_1} : has_coe_to_fun (pmf α) :=
  has_coe_to_fun.mk (fun (p : pmf α) => α → nnreal) fun (p : pmf α) (a : α) => subtype.val p a

protected theorem ext {α : Type u_1} {p : pmf α} {q : pmf α} : (∀ (a : α), coe_fn p a = coe_fn q a) → p = q := sorry

theorem has_sum_coe_one {α : Type u_1} (p : pmf α) : has_sum (⇑p) 1 :=
  subtype.property p

theorem summable_coe {α : Type u_1} (p : pmf α) : summable ⇑p :=
  has_sum.summable (has_sum_coe_one p)

@[simp] theorem tsum_coe {α : Type u_1} (p : pmf α) : (tsum fun (a : α) => coe_fn p a) = 1 :=
  has_sum.tsum_eq (has_sum_coe_one p)

/-- The support of a `pmf` is the set where it is nonzero. -/
def support {α : Type u_1} (p : pmf α) : set α :=
  set_of fun (a : α) => subtype.val p a ≠ 0

/-- The pure `pmf` is the `pmf` where all the mass lies in one point.
  The value of `pure a` is `1` at `a` and `0` elsewhere. -/
def pure {α : Type u_1} (a : α) : pmf α :=
  { val := fun (a' : α) => ite (a' = a) 1 0, property := sorry }

@[simp] theorem pure_apply {α : Type u_1} (a : α) (a' : α) : coe_fn (pure a) a' = ite (a' = a) 1 0 :=
  rfl

protected instance inhabited {α : Type u_1} [Inhabited α] : Inhabited (pmf α) :=
  { default := pure Inhabited.default }

theorem coe_le_one {α : Type u_1} (p : pmf α) (a : α) : coe_fn p a ≤ 1 := sorry

protected theorem bind.summable {α : Type u_1} {β : Type u_2} (p : pmf α) (f : α → pmf β) (b : β) : summable fun (a : α) => coe_fn p a * coe_fn (f a) b := sorry

/-- The monadic bind operation for `pmf`. -/
def bind {α : Type u_1} {β : Type u_2} (p : pmf α) (f : α → pmf β) : pmf β :=
  { val := fun (b : β) => tsum fun (a : α) => coe_fn p a * coe_fn (f a) b, property := sorry }

@[simp] theorem bind_apply {α : Type u_1} {β : Type u_2} (p : pmf α) (f : α → pmf β) (b : β) : coe_fn (bind p f) b = tsum fun (a : α) => coe_fn p a * coe_fn (f a) b :=
  rfl

theorem coe_bind_apply {α : Type u_1} {β : Type u_2} (p : pmf α) (f : α → pmf β) (b : β) : ↑(coe_fn (bind p f) b) = tsum fun (a : α) => ↑(coe_fn p a) * ↑(coe_fn (f a) b) := sorry

@[simp] theorem pure_bind {α : Type u_1} {β : Type u_2} (a : α) (f : α → pmf β) : bind (pure a) f = f a := sorry

@[simp] theorem bind_pure {α : Type u_1} (p : pmf α) : bind p pure = p := sorry

@[simp] theorem bind_bind {α : Type u_1} {β : Type u_2} {γ : Type u_3} (p : pmf α) (f : α → pmf β) (g : β → pmf γ) : bind (bind p f) g = bind p fun (a : α) => bind (f a) g := sorry

theorem bind_comm {α : Type u_1} {β : Type u_2} {γ : Type u_3} (p : pmf α) (q : pmf β) (f : α → β → pmf γ) : (bind p fun (a : α) => bind q (f a)) = bind q fun (b : β) => bind p fun (a : α) => f a b := sorry

/-- The functorial action of a function on a `pmf`. -/
def map {α : Type u_1} {β : Type u_2} (f : α → β) (p : pmf α) : pmf β :=
  bind p (pure ∘ f)

theorem bind_pure_comp {α : Type u_1} {β : Type u_2} (f : α → β) (p : pmf α) : bind p (pure ∘ f) = map f p :=
  rfl

theorem map_id {α : Type u_1} (p : pmf α) : map id p = p := sorry

theorem map_comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} (p : pmf α) (f : α → β) (g : β → γ) : map g (map f p) = map (g ∘ f) p := sorry

theorem pure_map {α : Type u_1} {β : Type u_2} (a : α) (f : α → β) : map f (pure a) = pure (f a) := sorry

/-- The monadic sequencing operation for `pmf`. -/
def seq {α : Type u_1} {β : Type u_2} (f : pmf (α → β)) (p : pmf α) : pmf β :=
  bind f fun (m : α → β) => bind p fun (a : α) => pure (m a)

/-- Given a non-empty multiset `s` we construct the `pmf` which sends `a` to the fraction of
  elements in `s` that are `a`. -/
def of_multiset {α : Type u_1} (s : multiset α) (hs : s ≠ 0) : pmf α :=
  { val := fun (a : α) => ↑(multiset.count a s) / ↑(coe_fn multiset.card s), property := sorry }

/-- Given a finite type `α` and a function `f : α → ℝ≥0` with sum 1, we get a `pmf`. -/
def of_fintype {α : Type u_1} [fintype α] (f : α → nnreal) (h : (finset.sum finset.univ fun (x : α) => f x) = 1) : pmf α :=
  { val := f, property := sorry }

/-- A `pmf` which assigns probability `p` to `tt` and `1 - p` to `ff`. -/
def bernoulli (p : nnreal) (h : p ≤ 1) : pmf Bool :=
  of_fintype (fun (b : Bool) => cond b p (1 - p)) sorry

