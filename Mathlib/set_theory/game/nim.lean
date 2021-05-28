/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Markus Himmel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.nat.bitwise
import Mathlib.set_theory.game.impartial
import Mathlib.set_theory.ordinal_arithmetic
import Mathlib.PostPort

universes u_1 u 

namespace Mathlib

/-!
# Nim and the Sprague-Grundy theorem

This file contains the definition for nim for any ordinal `O`. In the game of `nim O₁` both players
may move to `nim O₂` for any `O₂ < O₁`.
We also define a Grundy value for an impartial game `G` and prove the Sprague-Grundy theorem, that
`G` is equivalent to `nim (grundy_value G)`.
Finally, we compute the sum of finite Grundy numbers: if `G` and `H` have Grundy values `n` and `m`,
where `n` and `m` are natural numbers, then `G + H` has the Grundy value `n xor m`.

## Implementation details

The pen-and-paper definition of nim defines the possible moves of `nim O` to be `{O' | O' < O}`.
However, this definition does not work for us because it would make the type of nim
`ordinal.{u} → pgame.{u + 1}`, which would make it impossible for us to state the Sprague-Grundy
theorem, since that requires the type of `nim` to be `ordinal.{u} → pgame.{u}`. For this reason, we
instead use `O.out.α` for the possible moves, which makes proofs significantly more messy and
tedious, but avoids the universe bump.

The lemma `nim_def` is somewhat prone to produce "motive is not type correct" errors. If you run
into this problem, you may find the lemmas `exists_ordinal_move_left_eq` and `exists_move_left_eq`
useful.

-/

/-- `ordinal.out` and `ordinal.type_out'` are required to make the definition of nim computable.
 `ordinal.out` performs the same job as `quotient.out` but is specific to ordinals. -/
def ordinal.out (o : ordinal) : Well_order :=
  Well_order.mk (Well_order.α (quotient.out o))
    (fun (x y : Well_order.α (quotient.out o)) => Well_order.r (quotient.out o) x y) sorry

/-- This is the same as `ordinal.type_out` but defined to use `ordinal.out`. -/
theorem ordinal.type_out' (o : ordinal) : ordinal.type (Well_order.r (ordinal.out o)) = o :=
  ordinal.type_out

/-- The definition of single-heap nim, which can be viewed as a pile of stones where each player can
 take a positive number of stones from it on their turn. -/
def nim : ordinal → pgame :=
  sorry

namespace pgame


namespace nim


theorem nim_def (O : ordinal) : nim O =
  mk (Well_order.α (ordinal.out O)) (Well_order.α (ordinal.out O))
    (fun (O₂ : Well_order.α (ordinal.out O)) => nim (ordinal.typein (Well_order.r (ordinal.out O)) O₂))
    fun (O₂ : Well_order.α (ordinal.out O)) => nim (ordinal.typein (Well_order.r (ordinal.out O)) O₂) := sorry

theorem nim_wf_lemma {O₁ : ordinal} (O₂ : Well_order.α (ordinal.out O₁)) : ordinal.typein (Well_order.r (ordinal.out O₁)) O₂ < O₁ := sorry

protected instance nim_impartial (O : ordinal) : impartial (nim O) :=
  sorry

theorem exists_ordinal_move_left_eq (O : ordinal) (i : left_moves (nim O)) : ∃ (O' : ordinal), ∃ (H : O' < O), move_left (nim O) i = nim O' := sorry

theorem exists_move_left_eq (O : ordinal) (O' : ordinal) (H : O' < O) : ∃ (i : left_moves (nim O)), move_left (nim O) i = nim O' := sorry

theorem zero_first_loses : first_loses (nim 0) := sorry

theorem non_zero_first_wins (O : ordinal) (hO : O ≠ 0) : first_wins (nim O) := sorry

theorem sum_first_loses_iff_eq (O₁ : ordinal) (O₂ : ordinal) : first_loses (nim O₁ + nim O₂) ↔ O₁ = O₂ := sorry

theorem sum_first_wins_iff_neq (O₁ : ordinal) (O₂ : ordinal) : first_wins (nim O₁ + nim O₂) ↔ O₁ ≠ O₂ := sorry

theorem equiv_iff_eq (O₁ : ordinal) (O₂ : ordinal) : equiv (nim O₁) (nim O₂) ↔ O₁ = O₂ := sorry

end nim


/-- This definition will be used in the proof of the Sprague-Grundy theorem. It takes a function
  from some type to ordinals and returns a nonempty set of ordinals with empty intersection with
  the image of the function. It is guaranteed that the smallest ordinal not in the image will be
  in the set, i.e. we can use this to find the mex. -/
def nonmoves {α : Type u} (M : α → ordinal) : set ordinal :=
  set_of fun (O : ordinal) => ¬∃ (a : α), M a = O

theorem nonmoves_nonempty {α : Type u} (M : α → ordinal) : ∃ (O : ordinal), O ∈ nonmoves M := sorry

/-- The Grundy value of an impartial game, the ordinal which corresponds to the game of nim that the
 game is equivalent to -/
def grundy_value (G : pgame) [impartial G] : ordinal :=
  sorry

theorem grundy_value_def (G : pgame) [impartial G] : grundy_value G =
  ordinal.omin (nonmoves fun (i : left_moves G) => grundy_value (move_left G i))
    (nonmoves_nonempty fun (i : left_moves G) => grundy_value (move_left G i)) := sorry

/-- The Sprague-Grundy theorem which states that every impartial game is equivalent to a game of
 nim, namely the game of nim corresponding to the games Grundy value -/
theorem equiv_nim_grundy_value (G : pgame) [impartial G] : equiv G (nim (grundy_value G)) := sorry

theorem equiv_nim_iff_grundy_value_eq (G : pgame) [impartial G] (O : ordinal) : equiv G (nim O) ↔ grundy_value G = O := sorry

theorem nim.grundy_value (O : ordinal) : grundy_value (nim O) = O :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (grundy_value (nim O) = O)) (Eq.symm (propext (equiv_nim_iff_grundy_value_eq (nim O) O)))))
    (equiv_refl (nim O))

theorem equiv_iff_grundy_value_eq (G : pgame) (H : pgame) [impartial G] [impartial H] : equiv G H ↔ grundy_value G = grundy_value H :=
  iff.trans (iff.mp equiv_congr_left (equiv_nim_grundy_value H) G) (equiv_nim_iff_grundy_value_eq G (grundy_value H))

theorem grundy_value_zero : grundy_value 0 = 0 := sorry

theorem equiv_zero_iff_grundy_value (G : pgame) [impartial G] : equiv G 0 ↔ grundy_value G = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (equiv G 0 ↔ grundy_value G = 0)) (propext (equiv_iff_grundy_value_eq G 0))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (grundy_value G = grundy_value 0 ↔ grundy_value G = 0)) grundy_value_zero))
      (iff.refl (grundy_value G = 0)))

theorem grundy_value_nim_add_nim (n : ℕ) (m : ℕ) : grundy_value (nim ↑n + nim ↑m) = ↑(nat.lxor n m) := sorry

theorem nim_add_nim_equiv {n : ℕ} {m : ℕ} : equiv (nim ↑n + nim ↑m) (nim ↑(nat.lxor n m)) := sorry

theorem grundy_value_add (G : pgame) (H : pgame) [impartial G] [impartial H] {n : ℕ} {m : ℕ} (hG : grundy_value G = ↑n) (hH : grundy_value H = ↑m) : grundy_value (G + H) = ↑(nat.lxor n m) := sorry

