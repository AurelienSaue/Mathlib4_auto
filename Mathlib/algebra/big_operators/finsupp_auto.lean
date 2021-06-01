/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.big_operators.pi
import Mathlib.data.finsupp.default
import Mathlib.PostPort

universes u_1 u_2 u_4 u_3 u_5 u_6 

namespace Mathlib

/-!
# Big operators for finsupps

This file contains theorems relevant to big operators in finitely supported functions.
-/

theorem finset.sum_apply' {α : Type u_1} {ι : Type u_2} {A : Type u_4} [add_comm_monoid A]
    {s : finset α} {f : α → ι →₀ A} (i : ι) :
    coe_fn (finset.sum s fun (k : α) => f k) i = finset.sum s fun (k : α) => coe_fn (f k) i :=
  Eq.symm (finset.sum_hom s ⇑(finsupp.apply_add_hom i))

theorem finsupp.sum_apply' {ι : Type u_2} {γ : Type u_3} {A : Type u_4} {B : Type u_5}
    [add_comm_monoid A] [add_comm_monoid B] (g : ι →₀ A) (k : ι → A → γ → B) (x : γ) :
    finsupp.sum g k x = finsupp.sum g fun (i : ι) (b : A) => k i b x :=
  finset.sum_apply x (finsupp.support g) fun (a : ι) => k a (coe_fn g a)

theorem finsupp.sum_sum_index' {α : Type u_1} {ι : Type u_2} {A : Type u_4} {C : Type u_6}
    [add_comm_monoid A] [add_comm_monoid C] {t : ι → A → C} (h0 : ∀ (i : ι), t i 0 = 0)
    (h1 : ∀ (i : ι) (x y : A), t i (x + y) = t i x + t i y) {s : finset α} {f : α → ι →₀ A} :
    finsupp.sum (finset.sum s fun (x : α) => f x) t =
        finset.sum s fun (x : α) => finsupp.sum (f x) t :=
  sorry

end Mathlib