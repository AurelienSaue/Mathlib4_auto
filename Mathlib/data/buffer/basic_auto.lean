/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

General utility functions for buffers.
-/
import PrePort
import Lean3Lib.init.default
import Lean3Lib.data.buffer
import Mathlib.data.array.lemmas
import Mathlib.control.traversable.instances
import PostPort

universes u_1 

namespace Mathlib

namespace buffer


protected instance inhabited {α : Type u_1} : Inhabited (buffer α) :=
  { default := nil }

theorem ext {α : Type u_1} {b₁ : buffer α} {b₂ : buffer α} : to_list b₁ = to_list b₂ → b₁ = b₂ := sorry

protected instance decidable_eq (α : Type u_1) [DecidableEq α] : DecidableEq (buffer α) :=
  id
    fun (_v : buffer α) =>
      sigma.cases_on _v
        fun (fst : ℕ) (snd : array fst α) (w : buffer α) =>
          sigma.cases_on w
            fun (w_fst : ℕ) (w_snd : array w_fst α) =>
              decidable.by_cases
                (fun (ᾰ : fst = w_fst) =>
                  Eq._oldrec
                    (fun (w_snd : array fst α) =>
                      decidable.by_cases (fun (ᾰ : snd = w_snd) => Eq._oldrec (is_true sorry) ᾰ)
                        fun (ᾰ : ¬snd = w_snd) => isFalse sorry)
                    ᾰ w_snd)
                fun (ᾰ : ¬fst = w_fst) => isFalse sorry

@[simp] theorem to_list_append_list {α : Type u_1} {xs : List α} {b : buffer α} : to_list (append_list b xs) = to_list b ++ xs := sorry

@[simp] theorem append_list_mk_buffer {α : Type u_1} {xs : List α} : append_list mk_buffer xs = array.to_buffer (list.to_array xs) := sorry

/-- The natural equivalence between lists and buffers, using
`list.to_buffer` and `buffer.to_list`. -/
def list_equiv_buffer (α : Type u_1) : List α ≃ buffer α :=
  equiv.mk list.to_buffer to_list sorry sorry

protected instance traversable : traversable buffer :=
  equiv.traversable list_equiv_buffer

protected instance is_lawful_traversable : is_lawful_traversable buffer :=
  equiv.is_lawful_traversable list_equiv_buffer

