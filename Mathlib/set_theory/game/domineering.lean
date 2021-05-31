/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.set_theory.game.state
import Mathlib.PostPort

namespace Mathlib

/-!
# Domineering as a combinatorial game.

We define the game of Domineering, played on a chessboard of arbitrary shape
(possibly even disconnected).
Left moves by placing a domino vertically, while Right moves by placing a domino horizontally.

This is only a fragment of a full development;
in order to successfully analyse positions we would need some more theorems.
Most importantly, we need a general statement that allows us to discard irrelevant moves.
Specifically to domineering, we need the fact that
disjoint parts of the chessboard give sums of games.
-/

namespace pgame


namespace domineering


/-- The embedding `(x, y) ↦ (x, y+1)`. -/
def shift_up : ℤ × ℤ ↪ ℤ × ℤ :=
  function.embedding.prod_map (function.embedding.refl ℤ) (function.embedding.mk (fun (n : ℤ) => n + 1) sorry)

/-- The embedding `(x, y) ↦ (x+1, y)`. -/
def shift_right : ℤ × ℤ ↪ ℤ × ℤ :=
  function.embedding.prod_map (function.embedding.mk (fun (n : ℤ) => n + 1) sorry) (function.embedding.refl ℤ)

/-- A Domineering board is an arbitrary finite subset of `ℤ × ℤ`. -/
def board :=
  finset (ℤ × ℤ)

/-- Left can play anywhere that a square and the square below it are open. -/
/-- Right can play anywhere that a square and the square to the left are open. -/
def left (b : board) : finset (ℤ × ℤ) :=
  b ∩ finset.map shift_up b

def right (b : board) : finset (ℤ × ℤ) :=
  b ∩ finset.map shift_right b

/-- After Left moves, two vertically adjacent squares are removed from the board. -/
def move_left (b : board) (m : ℤ × ℤ) : board :=
  finset.erase (finset.erase b m) (prod.fst m, prod.snd m - 1)

/-- After Left moves, two horizontally adjacent squares are removed from the board. -/
def move_right (b : board) (m : ℤ × ℤ) : board :=
  finset.erase (finset.erase b m) (prod.fst m - 1, prod.snd m)

theorem card_of_mem_left {b : board} {m : ℤ × ℤ} (h : m ∈ left b) : bit0 1 ≤ finset.card b := sorry

theorem card_of_mem_right {b : board} {m : ℤ × ℤ} (h : m ∈ right b) : bit0 1 ≤ finset.card b := sorry

theorem move_left_card {b : board} {m : ℤ × ℤ} (h : m ∈ left b) : finset.card (move_left b m) + bit0 1 = finset.card b := sorry

theorem move_right_card {b : board} {m : ℤ × ℤ} (h : m ∈ right b) : finset.card (move_right b m) + bit0 1 = finset.card b := sorry

theorem move_left_smaller {b : board} {m : ℤ × ℤ} (h : m ∈ left b) : finset.card (move_left b m) / bit0 1 < finset.card b / bit0 1 := sorry

theorem move_right_smaller {b : board} {m : ℤ × ℤ} (h : m ∈ right b) : finset.card (move_right b m) / bit0 1 < finset.card b / bit0 1 := sorry

/-- The instance describing allowed moves on a Domineering board. -/
protected instance state : state board :=
  state.mk (fun (s : board) => finset.card s / bit0 1) (fun (s : board) => finset.image (move_left s) (left s))
    (fun (s : board) => finset.image (move_right s) (right s)) sorry sorry

end domineering


/-- Construct a pre-game from a Domineering board. -/
def domineering (b : domineering.board) : pgame :=
  of b

/-- All games of Domineering are short, because each move removes two squares. -/
protected instance short_domineering (b : domineering.board) : short (domineering b) :=
  id (pgame.short_of b)

/-- The Domineering board with two squares arranged vertically, in which Left has the only move. -/
def domineering.one : pgame :=
  domineering (list.to_finset [(0, 0), (0, 1)])

/-- The `L` shaped Domineering board, in which Left is exactly half a move ahead. -/
def domineering.L : pgame :=
  domineering (list.to_finset [(0, bit0 1), (0, 1), (0, 0), (1, 0)])

protected instance short_one : short domineering.one :=
  id (pgame.short_domineering (list.to_finset [(0, 0), (0, 1)]))

protected instance short_L : short domineering.L :=
  id (pgame.short_domineering (list.to_finset [(0, bit0 1), (0, 1), (0, 0), (1, 0)]))

