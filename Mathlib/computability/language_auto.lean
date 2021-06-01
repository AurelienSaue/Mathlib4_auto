/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.finset.basic
import Mathlib.PostPort

universes u_1 u v 

namespace Mathlib

/-!
# Languages
This file contains the definition and operations on formal languages over an alphabet. Note strings
are implemented as lists over the alphabet.
The operations in this file define a [Kleene algebra](https://en.wikipedia.org/wiki/Kleene_algebra)
over the languages.
-/

/-- A language is a set of strings over an alphabet. -/
def language (α : Type u_1) := set (List α)

namespace language


protected instance has_zero {α : Type u} : HasZero (language α) := { zero := ∅ }

protected instance has_one {α : Type u} : HasOne (language α) := { one := singleton [] }

protected instance inhabited {α : Type u} : Inhabited (language α) := { default := 0 }

protected instance has_add {α : Type u} : Add (language α) := { add := set.union }

protected instance has_mul {α : Type u} : Mul (language α) :=
  { mul :=
      fun (l m : language α) =>
        (fun (p : List α × List α) => prod.fst p ++ prod.snd p) '' set.prod l m }

theorem zero_def {α : Type u} : 0 = ∅ := rfl

theorem one_def {α : Type u} : 1 = singleton [] := rfl

theorem add_def {α : Type u} (l : language α) (m : language α) : l + m = l ∪ m := rfl

theorem mul_def {α : Type u} (l : language α) (m : language α) :
    l * m = (fun (p : List α × List α) => prod.fst p ++ prod.snd p) '' set.prod l m :=
  rfl

/-- The star of a language `L` is the set of all strings which can be written by concatenating
  strings from `L`. -/
def star {α : Type u} (l : language α) : language α :=
  set_of fun (x : List α) => ∃ (S : List (List α)), x = list.join S ∧ ∀ (y : List α), y ∈ S → y ∈ l

theorem star_def {α : Type u} (l : language α) :
    star l =
        set_of
          fun (x : List α) =>
            ∃ (S : List (List α)), x = list.join S ∧ ∀ (y : List α), y ∈ S → y ∈ l :=
  rfl

@[simp] theorem mem_one {α : Type u} (x : List α) : x ∈ 1 ↔ x = [] := iff.refl (x ∈ 1)

@[simp] theorem mem_add {α : Type u} (l : language α) (m : language α) (x : List α) :
    x ∈ l + m ↔ x ∈ l ∨ x ∈ m :=
  sorry

theorem mem_mul {α : Type u} (l : language α) (m : language α) (x : List α) :
    x ∈ l * m ↔ ∃ (a : List α), ∃ (b : List α), a ∈ l ∧ b ∈ m ∧ a ++ b = x :=
  sorry

theorem mem_star {α : Type u} (l : language α) (x : List α) :
    x ∈ star l ↔ ∃ (S : List (List α)), x = list.join S ∧ ∀ (y : List α), y ∈ S → y ∈ l :=
  iff.refl (x ∈ star l)

protected instance semiring {α : Type u} : semiring (language α) :=
  semiring.mk Add.add sorry 0 sorry sorry sorry Mul.mul mul_assoc_lang 1 one_mul_lang mul_one_lang
    sorry sorry left_distrib_lang right_distrib_lang

@[simp] theorem add_self {α : Type u} (l : language α) : l + l = l := sup_idem

theorem star_def_nonempty {α : Type u} (l : language α) :
    star l =
        set_of
          fun (x : List α) =>
            ∃ (S : List (List α)), x = list.join S ∧ ∀ (y : List α), y ∈ S → y ∈ l ∧ y ≠ [] :=
  sorry

theorem le_iff {α : Type u} (l : language α) (m : language α) : l ≤ m ↔ l + m = m :=
  iff.symm sup_eq_right

theorem le_mul_congr {α : Type u} {l₁ : language α} {l₂ : language α} {m₁ : language α}
    {m₂ : language α} : l₁ ≤ m₁ → l₂ ≤ m₂ → l₁ * l₂ ≤ m₁ * m₂ :=
  sorry

theorem le_add_congr {α : Type u} {l₁ : language α} {l₂ : language α} {m₁ : language α}
    {m₂ : language α} : l₁ ≤ m₁ → l₂ ≤ m₂ → l₁ + l₂ ≤ m₁ + m₂ :=
  sup_le_sup

theorem supr_mul {α : Type u} {ι : Sort v} (l : ι → language α) (m : language α) :
    (supr fun (i : ι) => l i) * m = supr fun (i : ι) => l i * m :=
  sorry

theorem mul_supr {α : Type u} {ι : Sort v} (l : ι → language α) (m : language α) :
    (m * supr fun (i : ι) => l i) = supr fun (i : ι) => m * l i :=
  sorry

theorem supr_add {α : Type u} {ι : Sort v} [Nonempty ι] (l : ι → language α) (m : language α) :
    (supr fun (i : ι) => l i) + m = supr fun (i : ι) => l i + m :=
  supr_sup

theorem add_supr {α : Type u} {ι : Sort v} [Nonempty ι] (l : ι → language α) (m : language α) :
    (m + supr fun (i : ι) => l i) = supr fun (i : ι) => m + l i :=
  sup_supr

theorem star_eq_supr_pow {α : Type u} (l : language α) : star l = supr fun (i : ℕ) => l ^ i := sorry

theorem mul_self_star_comm {α : Type u} (l : language α) : star l * l = l * star l := sorry

@[simp] theorem one_add_self_mul_star_eq_star {α : Type u} (l : language α) :
    1 + l * star l = star l :=
  sorry

@[simp] theorem one_add_star_mul_self_eq_star {α : Type u} (l : language α) :
    1 + star l * l = star l :=
  eq.mpr (id (Eq._oldrec (Eq.refl (1 + star l * l = star l)) (mul_self_star_comm l)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (1 + l * star l = star l)) (one_add_self_mul_star_eq_star l)))
      (Eq.refl (star l)))

theorem star_mul_le_right_of_mul_le_right {α : Type u} (l : language α) (m : language α) :
    l * m ≤ m → star l * m ≤ m :=
  sorry

theorem star_mul_le_left_of_mul_le_left {α : Type u} (l : language α) (m : language α) :
    m * l ≤ m → m * star l ≤ m :=
  sorry

end Mathlib