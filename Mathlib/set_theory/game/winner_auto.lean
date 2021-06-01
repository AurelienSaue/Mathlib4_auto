/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.set_theory.pgame
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Basic definitions about who has a winning stratergy

We define `G.first_loses`, `G.first_wins`, `G.left_wins` and `G.right_wins` for a pgame `G`, which
means the second, first, left and right players have a winning strategy respectively.
These are defined by inequalities which can be unfolded with `pgame.lt_def` and `pgame.le_def`.
-/

namespace pgame


/-- The player who goes first loses -/
def first_loses (G : pgame) := G ≤ 0 ∧ 0 ≤ G

/-- The player who goes first wins -/
def first_wins (G : pgame) := 0 < G ∧ G < 0

/-- The left player can always win -/
def left_wins (G : pgame) := 0 < G ∧ 0 ≤ G

/-- The right player can always win -/
def right_wins (G : pgame) := G ≤ 0 ∧ G < 0

theorem zero_first_loses : first_loses 0 := { left := le_refl 0, right := le_refl 0 }

theorem one_left_wins : left_wins 1 := sorry

theorem star_first_wins : first_wins star := { left := zero_lt_star, right := star_lt_zero }

theorem omega_left_wins : left_wins omega := sorry

theorem winner_cases (G : pgame) : left_wins G ∨ right_wins G ∨ first_loses G ∨ first_wins G :=
  sorry

theorem first_loses_is_zero {G : pgame} : first_loses G ↔ equiv G 0 := iff.refl (first_loses G)

theorem first_loses_of_equiv {G : pgame} {H : pgame} (h : equiv G H) :
    first_loses G → first_loses H :=
  fun (hGp : first_loses G) =>
    { left := le_of_equiv_of_le (and.symm h) (and.left hGp),
      right := le_of_le_of_equiv (and.right hGp) h }

theorem first_wins_of_equiv {G : pgame} {H : pgame} (h : equiv G H) : first_wins G → first_wins H :=
  fun (hGn : first_wins G) =>
    { left := lt_of_lt_of_equiv (and.left hGn) h,
      right := lt_of_equiv_of_lt (and.symm h) (and.right hGn) }

theorem left_wins_of_equiv {G : pgame} {H : pgame} (h : equiv G H) : left_wins G → left_wins H :=
  fun (hGl : left_wins G) =>
    { left := lt_of_lt_of_equiv (and.left hGl) h, right := le_of_le_of_equiv (and.right hGl) h }

theorem right_wins_of_equiv {G : pgame} {H : pgame} (h : equiv G H) : right_wins G → right_wins H :=
  fun (hGr : right_wins G) =>
    { left := le_of_equiv_of_le (and.symm h) (and.left hGr),
      right := lt_of_equiv_of_lt (and.symm h) (and.right hGr) }

theorem first_loses_of_equiv_iff {G : pgame} {H : pgame} (h : equiv G H) :
    first_loses G ↔ first_loses H :=
  { mp := first_loses_of_equiv h, mpr := first_loses_of_equiv (and.symm h) }

theorem first_wins_of_equiv_iff {G : pgame} {H : pgame} (h : equiv G H) :
    first_wins G ↔ first_wins H :=
  { mp := first_wins_of_equiv h, mpr := first_wins_of_equiv (and.symm h) }

theorem left_wins_of_equiv_iff {G : pgame} {H : pgame} (h : equiv G H) :
    left_wins G ↔ left_wins H :=
  { mp := left_wins_of_equiv h, mpr := left_wins_of_equiv (and.symm h) }

theorem right_wins_of_equiv_iff {G : pgame} {H : pgame} (h : equiv G H) :
    right_wins G ↔ right_wins H :=
  { mp := right_wins_of_equiv h, mpr := right_wins_of_equiv (and.symm h) }

theorem not_first_wins_of_first_loses {G : pgame} : first_loses G → ¬first_wins G := sorry

theorem not_first_loses_of_first_wins {G : pgame} : first_wins G → ¬first_loses G :=
  iff.mp imp_not_comm not_first_wins_of_first_loses

end Mathlib