/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import PrePort
import Lean3Lib.init.meta.tactic
import Lean3Lib.init.meta.format
import Lean3Lib.init.function
import PostPort

universes l 

namespace Mathlib

/-- This is a kind attached to an argument of a congruence lemma that tells the simplifier how to fill it in.
- `fixed`: It is a parameter for the congruence lemma, the parameter occurs in the left and right hand sides.
  For example the α in the congruence generated from `f: Π {α : Type} α → α`.
- `fixed_no_param`: It is not a parameter for the congruence lemma, the lemma was specialized for this parameter.
  This only happens if the parameter is a subsingleton/proposition, and other parameters depend on it.
- `eq`: The lemma contains three parameters for this kind of argument `a_i`, `b_i` and `(eq_i : a_i = b_i)`.
  `a_i` and `b_i` represent the left and right hand sides, and `eq_i` is a proof for their equality.
  For example the second argument in `f: Π {α : Type}, α → α`.
- `cast`: corresponds to arguments that are subsingletons/propositions.
  For example the `p` in the congruence generated from `f : Π (x y : ℕ) (p: x < y), ℕ`.
- `heq` The lemma contains three parameters for this kind of argument `a_i`, `b_i` and `(eq_i : a_i == b_i)`.
   `a_i` and `b_i` represent the left and right hand sides, and eq_i is a proof for their heterogeneous equality.
-/
inductive congr_arg_kind 
where
| fixed : congr_arg_kind
| fixed_no_param : congr_arg_kind
| eq : congr_arg_kind
| cast : congr_arg_kind
| heq : congr_arg_kind

namespace congr_arg_kind


def to_string : congr_arg_kind → string :=
  sorry

protected instance has_repr : has_repr congr_arg_kind :=
  has_repr.mk to_string

