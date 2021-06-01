/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.set_theory.game.winner
import Mathlib.tactic.nth_rewrite.default
import Mathlib.tactic.equiv_rw
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Basic definitions about impartial (pre-)games

We will define an impartial game, one in which left and right can make exactly the same moves.
Our definition differs slightly by saying that the game is always equivalent to its negative,
no matter what moves are played. This allows for games such as poker-nim to be classifed as
impartial.
-/

namespace pgame


/-- The definition for a impartial game, defined using Conway induction -/
def impartial : pgame → Prop := sorry

theorem impartial_def {G : pgame} :
    impartial G ↔
        equiv G (-G) ∧
          (∀ (i : left_moves G), impartial (move_left G i)) ∧
            ∀ (j : right_moves G), impartial (move_right G j) :=
  sorry

namespace impartial


protected instance impartial_zero : impartial 0 := sorry

theorem neg_equiv_self (G : pgame) [h : impartial G] : equiv G (-G) :=
  and.left (iff.mp impartial_def h)

protected instance move_left_impartial {G : pgame} [h : impartial G] (i : left_moves G) :
    impartial (move_left G i) :=
  and.left (and.right (iff.mp impartial_def h)) i

protected instance move_right_impartial {G : pgame} [h : impartial G] (j : right_moves G) :
    impartial (move_right G j) :=
  and.right (and.right (iff.mp impartial_def h)) j

protected instance impartial_add (G : pgame) (H : pgame) [impartial G] [impartial H] :
    impartial (G + H) :=
  sorry

protected instance impartial_neg (G : pgame) [impartial G] : impartial (-G) := sorry

theorem winner_cases (G : pgame) [impartial G] : first_loses G ∨ first_wins G := sorry

theorem not_first_wins (G : pgame) [impartial G] : ¬first_wins G ↔ first_loses G := sorry

theorem not_first_loses (G : pgame) [impartial G] : ¬first_loses G ↔ first_wins G :=
  iff.symm (iff.mp iff_not_comm (iff.symm (not_first_wins G)))

theorem add_self (G : pgame) [impartial G] : first_loses (G + G) :=
  iff.mpr first_loses_is_zero
    (equiv_trans (add_congr (neg_equiv_self G) (equiv_refl G)) add_left_neg_equiv)

theorem equiv_iff_sum_first_loses (G : pgame) (H : pgame) [impartial G] [impartial H] :
    equiv G H ↔ first_loses (G + H) :=
  sorry

theorem le_zero_iff {G : pgame} [impartial G] : G ≤ 0 ↔ 0 ≤ G :=
  eq.mpr (id (Eq._oldrec (Eq.refl (G ≤ 0 ↔ 0 ≤ G)) (propext le_zero_iff_zero_le_neg)))
    (eq.mpr
      (id
        (Eq._oldrec (Eq.refl (0 ≤ -G ↔ 0 ≤ G))
          (propext (le_congr (equiv_refl 0) (neg_equiv_self G)))))
      (iff.refl (0 ≤ -G)))

theorem lt_zero_iff {G : pgame} [impartial G] : G < 0 ↔ 0 < G := sorry

theorem first_loses_symm (G : pgame) [impartial G] : first_loses G ↔ G ≤ 0 :=
  { mp := and.left, mpr := fun (h : G ≤ 0) => { left := h, right := iff.mp le_zero_iff h } }

theorem first_wins_symm (G : pgame) [impartial G] : first_wins G ↔ G < 0 :=
  { mp := and.right, mpr := fun (h : G < 0) => { left := iff.mp lt_zero_iff h, right := h } }

theorem first_loses_symm' (G : pgame) [impartial G] : first_loses G ↔ 0 ≤ G :=
  { mp := and.right, mpr := fun (h : 0 ≤ G) => { left := iff.mpr le_zero_iff h, right := h } }

theorem first_wins_symm' (G : pgame) [impartial G] : first_wins G ↔ 0 < G :=
  { mp := and.left, mpr := fun (h : 0 < G) => { left := h, right := iff.mpr lt_zero_iff h } }

theorem no_good_left_moves_iff_first_loses (G : pgame) [impartial G] :
    (∀ (i : left_moves G), first_wins (move_left G i)) ↔ first_loses G :=
  sorry

theorem no_good_right_moves_iff_first_loses (G : pgame) [impartial G] :
    (∀ (j : right_moves G), first_wins (move_right G j)) ↔ first_loses G :=
  sorry

theorem good_left_move_iff_first_wins (G : pgame) [impartial G] :
    (∃ (i : left_moves G), first_loses (move_left G i)) ↔ first_wins G :=
  sorry

theorem good_right_move_iff_first_wins (G : pgame) [impartial G] :
    (∃ (j : right_moves G), first_loses (move_right G j)) ↔ first_wins G :=
  sorry

end Mathlib