/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.list.basic
import PostPort

universes u 

namespace Mathlib

namespace list


theorem rotate_mod {α : Type u} (l : List α) (n : ℕ) : rotate l (n % length l) = rotate l n := sorry

@[simp] theorem rotate_nil {α : Type u} (n : ℕ) : rotate [] n = [] :=
  nat.cases_on n (Eq.refl (rotate [] 0)) fun (n : ℕ) => Eq.refl (rotate [] (Nat.succ n))

@[simp] theorem rotate_zero {α : Type u} (l : List α) : rotate l 0 = l := sorry

@[simp] theorem rotate'_nil {α : Type u} (n : ℕ) : rotate' [] n = [] :=
  nat.cases_on n (Eq.refl (rotate' [] 0)) fun (n : ℕ) => Eq.refl (rotate' [] (Nat.succ n))

@[simp] theorem rotate'_zero {α : Type u} (l : List α) : rotate' l 0 = l :=
  list.cases_on l (Eq.refl (rotate' [] 0)) fun (l_hd : α) (l_tl : List α) => Eq.refl (rotate' (l_hd :: l_tl) 0)

theorem rotate'_cons_succ {α : Type u} (l : List α) (a : α) (n : ℕ) : rotate' (a :: l) (Nat.succ n) = rotate' (l ++ [a]) n := sorry

@[simp] theorem length_rotate' {α : Type u} (l : List α) (n : ℕ) : length (rotate' l n) = length l := sorry

theorem rotate'_eq_take_append_drop {α : Type u} {l : List α} {n : ℕ} : n ≤ length l → rotate' l n = drop n l ++ take n l := sorry

theorem rotate'_rotate' {α : Type u} (l : List α) (n : ℕ) (m : ℕ) : rotate' (rotate' l n) m = rotate' l (n + m) := sorry

@[simp] theorem rotate'_length {α : Type u} (l : List α) : rotate' l (length l) = l := sorry

@[simp] theorem rotate'_length_mul {α : Type u} (l : List α) (n : ℕ) : rotate' l (length l * n) = l := sorry

theorem rotate'_mod {α : Type u} (l : List α) (n : ℕ) : rotate' l (n % length l) = rotate' l n := sorry

theorem rotate_eq_rotate' {α : Type u} (l : List α) (n : ℕ) : rotate l n = rotate' l n := sorry

theorem rotate_cons_succ {α : Type u} (l : List α) (a : α) (n : ℕ) : rotate (a :: l) (Nat.succ n) = rotate (l ++ [a]) n := sorry

@[simp] theorem mem_rotate {α : Type u} {l : List α} {a : α} {n : ℕ} : a ∈ rotate l n ↔ a ∈ l := sorry

@[simp] theorem length_rotate {α : Type u} (l : List α) (n : ℕ) : length (rotate l n) = length l :=
  eq.mpr (id (Eq._oldrec (Eq.refl (length (rotate l n) = length l)) (rotate_eq_rotate' l n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (length (rotate' l n) = length l)) (length_rotate' l n))) (Eq.refl (length l)))

theorem rotate_eq_take_append_drop {α : Type u} {l : List α} {n : ℕ} : n ≤ length l → rotate l n = drop n l ++ take n l :=
  eq.mpr (id (Eq._oldrec (Eq.refl (n ≤ length l → rotate l n = drop n l ++ take n l)) (rotate_eq_rotate' l n)))
    rotate'_eq_take_append_drop

theorem rotate_rotate {α : Type u} (l : List α) (n : ℕ) (m : ℕ) : rotate (rotate l n) m = rotate l (n + m) := sorry

@[simp] theorem rotate_length {α : Type u} (l : List α) : rotate l (length l) = l :=
  eq.mpr (id (Eq._oldrec (Eq.refl (rotate l (length l) = l)) (rotate_eq_rotate' l (length l))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (rotate' l (length l) = l)) (rotate'_length l))) (Eq.refl l))

@[simp] theorem rotate_length_mul {α : Type u} (l : List α) (n : ℕ) : rotate l (length l * n) = l :=
  eq.mpr (id (Eq._oldrec (Eq.refl (rotate l (length l * n) = l)) (rotate_eq_rotate' l (length l * n))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (rotate' l (length l * n) = l)) (rotate'_length_mul l n))) (Eq.refl l))

theorem prod_rotate_eq_one_of_prod_eq_one {α : Type u} [group α] {l : List α} (hl : prod l = 1) (n : ℕ) : prod (rotate l n) = 1 := sorry

