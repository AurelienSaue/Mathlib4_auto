/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.big_operators.basic
import Mathlib.data.finset.pi
import Mathlib.data.finset.powerset
import Mathlib.PostPort

universes u v u_1 u_2 

namespace Mathlib

/-!
# Results about big operators with values in a (semi)ring

We prove results about big operators that involve some interaction between
multiplicative and additive structures on the values being combined.
-/

namespace finset


theorem sum_mul {α : Type u} {β : Type v} {s : finset α} {b : β} {f : α → β} [semiring β] :
    (finset.sum s fun (x : α) => f x) * b = finset.sum s fun (x : α) => f x * b :=
  Eq.symm (sum_hom s fun (x : β) => x * b)

theorem mul_sum {α : Type u} {β : Type v} {s : finset α} {b : β} {f : α → β} [semiring β] :
    (b * finset.sum s fun (x : α) => f x) = finset.sum s fun (x : α) => b * f x :=
  Eq.symm (sum_hom s (Mul.mul b))

theorem sum_mul_boole {α : Type u} {β : Type v} [semiring β] [DecidableEq α] (s : finset α)
    (f : α → β) (a : α) :
    (finset.sum s fun (x : α) => f x * ite (a = x) 1 0) = ite (a ∈ s) (f a) 0 :=
  sorry

theorem sum_boole_mul {α : Type u} {β : Type v} [semiring β] [DecidableEq α] (s : finset α)
    (f : α → β) (a : α) :
    (finset.sum s fun (x : α) => ite (a = x) 1 0 * f x) = ite (a ∈ s) (f a) 0 :=
  sorry

theorem sum_div {α : Type u} {β : Type v} [division_ring β] {s : finset α} {f : α → β} {b : β} :
    (finset.sum s fun (x : α) => f x) / b = finset.sum s fun (x : α) => f x / b :=
  sorry

/-- The product over a sum can be written as a sum over the product of sets, `finset.pi`.
  `finset.prod_univ_sum` is an alternative statement when the product is over `univ`. -/
theorem prod_sum {α : Type u} {β : Type v} [comm_semiring β] {δ : α → Type u_1} [DecidableEq α]
    [(a : α) → DecidableEq (δ a)] {s : finset α} {t : (a : α) → finset (δ a)}
    {f : (a : α) → δ a → β} :
    (finset.prod s fun (a : α) => finset.sum (t a) fun (b : δ a) => f a b) =
        finset.sum (pi s t)
          fun (p : (a : α) → a ∈ s → δ a) =>
            finset.prod (attach s)
              fun (x : Subtype fun (x : α) => x ∈ s) =>
                f (subtype.val x) (p (subtype.val x) (subtype.property x)) :=
  sorry

theorem sum_mul_sum {β : Type v} [comm_semiring β] {ι₁ : Type u_1} {ι₂ : Type u_2} (s₁ : finset ι₁)
    (s₂ : finset ι₂) (f₁ : ι₁ → β) (f₂ : ι₂ → β) :
    ((finset.sum s₁ fun (x₁ : ι₁) => f₁ x₁) * finset.sum s₂ fun (x₂ : ι₂) => f₂ x₂) =
        finset.sum (finset.product s₁ s₂) fun (p : ι₁ × ι₂) => f₁ (prod.fst p) * f₂ (prod.snd p) :=
  sorry

/-- The product of `f a + g a` over all of `s` is the sum
  over the powerset of `s` of the product of `f` over a subset `t` times
  the product of `g` over the complement of `t`  -/
theorem prod_add {α : Type u} {β : Type v} [comm_semiring β] (f : α → β) (g : α → β)
    (s : finset α) :
    (finset.prod s fun (a : α) => f a + g a) =
        finset.sum (powerset s)
          fun (t : finset α) =>
            (finset.prod t fun (a : α) => f a) * finset.prod (s \ t) fun (a : α) => g a :=
  sorry

/--  Summing `a^s.card * b^(n-s.card)` over all finite subsets `s` of a `finset`
gives `(a + b)^s.card`.-/
theorem sum_pow_mul_eq_add_pow {α : Type u_1} {R : Type u_2} [comm_semiring R] (a : R) (b : R)
    (s : finset α) :
    (finset.sum (powerset s) fun (t : finset α) => a ^ card t * b ^ (card s - card t)) =
        (a + b) ^ card s :=
  sorry

theorem prod_pow_eq_pow_sum {α : Type u} {β : Type v} [comm_semiring β] {x : β} {f : α → ℕ}
    {s : finset α} : (finset.prod s fun (i : α) => x ^ f i) = x ^ finset.sum s fun (x : α) => f x :=
  sorry

theorem dvd_sum {α : Type u} {β : Type v} [comm_semiring β] {b : β} {s : finset α} {f : α → β}
    (h : ∀ (x : α), x ∈ s → b ∣ f x) : b ∣ finset.sum s fun (x : α) => f x :=
  sorry

theorem prod_nat_cast {α : Type u} {β : Type v} [comm_semiring β] (s : finset α) (f : α → ℕ) :
    ↑(finset.prod s fun (x : α) => f x) = finset.prod s fun (x : α) => ↑(f x) :=
  ring_hom.map_prod (nat.cast_ring_hom β) f s

/-- A product over all subsets of `s ∪ {x}` is obtained by multiplying the product over all subsets
of `s`, and over all subsets of `s` to which one adds `x`. -/
theorem prod_powerset_insert {α : Type u} {β : Type v} [DecidableEq α] [comm_monoid β]
    {s : finset α} {x : α} (h : ¬x ∈ s) (f : finset α → β) :
    (finset.prod (powerset (insert x s)) fun (a : finset α) => f a) =
        (finset.prod (powerset s) fun (a : finset α) => f a) *
          finset.prod (powerset s) fun (t : finset α) => f (insert x t) :=
  sorry

end Mathlib