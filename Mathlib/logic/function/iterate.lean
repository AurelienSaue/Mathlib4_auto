/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.logic.function.conjugate
import Mathlib.PostPort

universes u v 

namespace Mathlib

/-!
# Iterations of a function

In this file we prove simple properties of `nat.iterate f n` a.k.a. `f^[n]`:

* `iterate_zero`, `iterate_succ`, `iterate_succ'`, `iterate_add`, `iterate_mul`:
  formulas for `f^[0]`, `f^[n+1]` (two versions), `f^[n+m]`, and `f^[n*m]`;

* `iterate_id` : `id^[n]=id`;

* `injective.iterate`, `surjective.iterate`, `bijective.iterate` :
  iterates of an injective/surjective/bijective function belong to the same class;

* `left_inverse.iterate`, `right_inverse.iterate`, `commute.iterate_left`, `comute.iterate_right`,
  `commute.iterate_iterate`:
  some properties of pairs of functions survive under iterations

* `iterate_fixed`, `semiconj.iterate_*`, `semiconj₂.iterate`:
  if `f` fixes a point (resp., semiconjugates unary/binary operarations), then so does `f^[n]`.

-/

namespace function


@[simp] theorem iterate_zero {α : Type u} (f : α → α) : nat.iterate f 0 = id :=
  rfl

theorem iterate_zero_apply {α : Type u} (f : α → α) (x : α) : nat.iterate f 0 x = x :=
  rfl

@[simp] theorem iterate_succ {α : Type u} (f : α → α) (n : ℕ) : nat.iterate f (Nat.succ n) = nat.iterate f n ∘ f :=
  rfl

theorem iterate_succ_apply {α : Type u} (f : α → α) (n : ℕ) (x : α) : nat.iterate f (Nat.succ n) x = nat.iterate f n (f x) :=
  rfl

@[simp] theorem iterate_id {α : Type u} (n : ℕ) : nat.iterate id n = id := sorry

theorem iterate_add {α : Type u} (f : α → α) (m : ℕ) (n : ℕ) : nat.iterate f (m + n) = nat.iterate f m ∘ nat.iterate f n := sorry

theorem iterate_add_apply {α : Type u} (f : α → α) (m : ℕ) (n : ℕ) (x : α) : nat.iterate f (m + n) x = nat.iterate f m (nat.iterate f n x) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (nat.iterate f (m + n) x = nat.iterate f m (nat.iterate f n x))) (iterate_add f m n)))
    (Eq.refl (comp (nat.iterate f m) (nat.iterate f n) x))

@[simp] theorem iterate_one {α : Type u} (f : α → α) : nat.iterate f 1 = f :=
  funext fun (a : α) => rfl

theorem iterate_mul {α : Type u} (f : α → α) (m : ℕ) (n : ℕ) : nat.iterate f (m * n) = nat.iterate (nat.iterate f m) n := sorry

theorem iterate_fixed {α : Type u} {f : α → α} {x : α} (h : f x = x) (n : ℕ) : nat.iterate f n x = x := sorry

theorem injective.iterate {α : Type u} {f : α → α} (Hinj : injective f) (n : ℕ) : injective (nat.iterate f n) :=
  nat.rec_on n injective_id fun (n : ℕ) (ihn : injective (nat.iterate f n)) => injective.comp ihn Hinj

theorem surjective.iterate {α : Type u} {f : α → α} (Hsurj : surjective f) (n : ℕ) : surjective (nat.iterate f n) :=
  nat.rec_on n surjective_id fun (n : ℕ) (ihn : surjective (nat.iterate f n)) => surjective.comp ihn Hsurj

theorem bijective.iterate {α : Type u} {f : α → α} (Hbij : bijective f) (n : ℕ) : bijective (nat.iterate f n) :=
  { left := injective.iterate (and.left Hbij) n, right := surjective.iterate (and.right Hbij) n }

namespace semiconj


theorem iterate_right {α : Type u} {β : Type v} {f : α → β} {ga : α → α} {gb : β → β} (h : semiconj f ga gb) (n : ℕ) : semiconj f (nat.iterate ga n) (nat.iterate gb n) :=
  nat.rec_on n id_right fun (n : ℕ) (ihn : semiconj f (nat.iterate ga n) (nat.iterate gb n)) => comp_right ihn h

theorem iterate_left {α : Type u} {f : α → α} {g : ℕ → α → α} (H : ∀ (n : ℕ), semiconj f (g n) (g (n + 1))) (n : ℕ) (k : ℕ) : semiconj (nat.iterate f n) (g k) (g (n + k)) := sorry

end semiconj


namespace commute


theorem iterate_right {α : Type u} {f : α → α} {g : α → α} (h : commute f g) (n : ℕ) : commute f (nat.iterate g n) :=
  semiconj.iterate_right h n

theorem iterate_left {α : Type u} {f : α → α} {g : α → α} (h : commute f g) (n : ℕ) : commute (nat.iterate f n) g :=
  symm (iterate_right (symm h) n)

theorem iterate_iterate {α : Type u} {f : α → α} {g : α → α} (h : commute f g) (m : ℕ) (n : ℕ) : commute (nat.iterate f m) (nat.iterate g n) :=
  iterate_right (iterate_left h m) n

theorem iterate_eq_of_map_eq {α : Type u} {f : α → α} {g : α → α} (h : commute f g) (n : ℕ) {x : α} (hx : f x = g x) : nat.iterate f n x = nat.iterate g n x := sorry

theorem comp_iterate {α : Type u} {f : α → α} {g : α → α} (h : commute f g) (n : ℕ) : nat.iterate (f ∘ g) n = nat.iterate f n ∘ nat.iterate g n := sorry

theorem iterate_self {α : Type u} (f : α → α) (n : ℕ) : commute (nat.iterate f n) f :=
  iterate_left (refl f) n

theorem self_iterate {α : Type u} (f : α → α) (n : ℕ) : commute f (nat.iterate f n) :=
  iterate_right (refl f) n

theorem iterate_iterate_self {α : Type u} (f : α → α) (m : ℕ) (n : ℕ) : commute (nat.iterate f m) (nat.iterate f n) :=
  iterate_iterate (refl f) m n

end commute


theorem semiconj₂.iterate {α : Type u} {f : α → α} {op : α → α → α} (hf : semiconj₂ f op op) (n : ℕ) : semiconj₂ (nat.iterate f n) op op :=
  nat.rec_on n (semiconj₂.id_left op) fun (n : ℕ) (ihn : semiconj₂ (nat.iterate f n) op op) => semiconj₂.comp ihn hf

theorem iterate_succ' {α : Type u} (f : α → α) (n : ℕ) : nat.iterate f (Nat.succ n) = f ∘ nat.iterate f n := sorry

theorem iterate_succ_apply' {α : Type u} (f : α → α) (n : ℕ) (x : α) : nat.iterate f (Nat.succ n) x = f (nat.iterate f n x) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (nat.iterate f (Nat.succ n) x = f (nat.iterate f n x))) (iterate_succ' f n)))
    (Eq.refl (comp f (nat.iterate f n) x))

theorem iterate_pred_comp_of_pos {α : Type u} (f : α → α) {n : ℕ} (hn : 0 < n) : nat.iterate f (Nat.pred n) ∘ f = nat.iterate f n := sorry

theorem comp_iterate_pred_of_pos {α : Type u} (f : α → α) {n : ℕ} (hn : 0 < n) : f ∘ nat.iterate f (Nat.pred n) = nat.iterate f n := sorry

theorem left_inverse.iterate {α : Type u} {f : α → α} {g : α → α} (hg : left_inverse g f) (n : ℕ) : left_inverse (nat.iterate g n) (nat.iterate f n) := sorry

theorem right_inverse.iterate {α : Type u} {f : α → α} {g : α → α} (hg : right_inverse g f) (n : ℕ) : right_inverse (nat.iterate g n) (nat.iterate f n) :=
  left_inverse.iterate hg n

