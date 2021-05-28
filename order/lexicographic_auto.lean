/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Scott Morrison, Minchao Wu

Lexicographic preorder / partial_order / linear_order / linear_order,
for pairs and dependent pairs.
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.tactic.basic
import PostPort

universes u v 

namespace Mathlib

/-- The cartesian product, equipped with the lexicographic order. -/
def lex (α : Type u) (β : Type v)  :=
  α × β

protected instance lex.decidable_eq {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β] : DecidableEq (lex α β) :=
  prod.decidable_eq

protected instance lex.inhabited {α : Type u} {β : Type v} [Inhabited α] [Inhabited β] : Inhabited (lex α β) :=
  prod.inhabited

/-- Dictionary / lexicographic ordering on pairs.  -/
protected instance lex_has_le {α : Type u} {β : Type v} [preorder α] [preorder β] : HasLessEq (lex α β) :=
  { LessEq := prod.lex Less LessEq }

protected instance lex_has_lt {α : Type u} {β : Type v} [preorder α] [preorder β] : HasLess (lex α β) :=
  { Less := prod.lex Less Less }

/-- Dictionary / lexicographic preorder for pairs. -/
protected instance lex_preorder {α : Type u} {β : Type v} [preorder α] [preorder β] : preorder (lex α β) :=
  preorder.mk LessEq Less sorry sorry

/-- Dictionary / lexicographic partial_order for pairs. -/
protected instance lex_partial_order {α : Type u} {β : Type v} [partial_order α] [partial_order β] : partial_order (lex α β) :=
  partial_order.mk preorder.le preorder.lt sorry sorry sorry

/-- Dictionary / lexicographic linear_order for pairs. -/
protected instance lex_linear_order {α : Type u} {β : Type v} [linear_order α] [linear_order β] : linear_order (lex α β) :=
  linear_order.mk partial_order.le partial_order.lt sorry sorry sorry sorry
    (id
      fun (a b : lex α β) =>
        prod.cases_on a
          fun (a₁ : α) (b₁ : β) =>
            prod.cases_on b
              fun (a₂ : α) (b₂ : β) =>
                decidable.cases_on (linear_order.decidable_le a₁ a₂) (fun (a_lt : ¬a₁ ≤ a₂) => isFalse sorry)
                  fun (a_le : a₁ ≤ a₂) =>
                    dite (a₁ = a₂)
                      (fun (h : a₁ = a₂) =>
                        eq.mpr sorry
                          (decidable.cases_on (linear_order.decidable_le b₁ b₂) (fun (b_lt : ¬b₁ ≤ b₂) => isFalse sorry)
                            fun (b_le : b₁ ≤ b₂) => is_true sorry))
                      fun (h : ¬a₁ = a₂) => is_true sorry)
    Mathlib.decidable_eq_of_decidable_le Mathlib.decidable_lt_of_decidable_le

/--
Dictionary / lexicographic ordering on dependent pairs.

The 'pointwise' partial order `prod.has_le` doesn't make
sense for dependent pairs, so it's safe to mark these as
instances here.
-/
protected instance dlex_has_le {α : Type u} {Z : α → Type v} [preorder α] [(a : α) → preorder (Z a)] : HasLessEq (psigma fun (a : α) => Z a) :=
  { LessEq := psigma.lex Less fun (a : α) => LessEq }

protected instance dlex_has_lt {α : Type u} {Z : α → Type v} [preorder α] [(a : α) → preorder (Z a)] : HasLess (psigma fun (a : α) => Z a) :=
  { Less := psigma.lex Less fun (a : α) => Less }

/-- Dictionary / lexicographic preorder on dependent pairs. -/
protected instance dlex_preorder {α : Type u} {Z : α → Type v} [preorder α] [(a : α) → preorder (Z a)] : preorder (psigma fun (a : α) => Z a) :=
  preorder.mk LessEq Less sorry sorry

/-- Dictionary / lexicographic partial_order for dependent pairs. -/
protected instance dlex_partial_order {α : Type u} {Z : α → Type v} [partial_order α] [(a : α) → partial_order (Z a)] : partial_order (psigma fun (a : α) => Z a) :=
  partial_order.mk preorder.le preorder.lt sorry sorry sorry

/-- Dictionary / lexicographic linear_order for pairs. -/
protected instance dlex_linear_order {α : Type u} {Z : α → Type v} [linear_order α] [(a : α) → linear_order (Z a)] : linear_order (psigma fun (a : α) => Z a) :=
  linear_order.mk partial_order.le partial_order.lt sorry sorry sorry sorry
    (id
      fun (a b : psigma fun (a : α) => Z a) =>
        psigma.cases_on a
          fun (a₁ : α) (b₁ : Z a₁) =>
            psigma.cases_on b
              fun (a₂ : α) (b₂ : Z a₂) =>
                decidable.cases_on (linear_order.decidable_le a₁ a₂) (fun (a_lt : ¬a₁ ≤ a₂) => isFalse sorry)
                  fun (a_le : a₁ ≤ a₂) =>
                    dite (a₁ = a₂)
                      (fun (h : a₁ = a₂) =>
                        Eq._oldrec
                          (fun (b₂ : Z a₁) (a_le : a₁ ≤ a₁) =>
                            decidable.cases_on (linear_order.decidable_le b₁ b₂) (fun (b_lt : ¬b₁ ≤ b₂) => isFalse sorry)
                              fun (b_le : b₁ ≤ b₂) => is_true sorry)
                          h b₂ a_le)
                      fun (h : ¬a₁ = a₂) => is_true sorry)
    Mathlib.decidable_eq_of_decidable_le Mathlib.decidable_lt_of_decidable_le

