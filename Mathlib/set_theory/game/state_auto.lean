/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.set_theory.game.short
import Mathlib.PostPort

universes u l 

namespace Mathlib

/-!
# Games described via "the state of the board".

We provide a simple mechanism for constructing combinatorial (pre-)games, by describing
"the state of the board", and providing an upper bound on the number of turns remaining.


## Implementation notes

We're very careful to produce a computable definition, so small games can be evaluated
using `dec_trivial`. To achieve this, I've had to rely solely on induction on natural numbers:
relying on general well-foundedness seems to be poisonous to computation?

See `set_theory/game/domineering` for an example using this construction.
-/

namespace pgame


/--
`pgame_state S` describes how to interpret `s : S` as a state of a combinatorial game.
Use `pgame.of s` or `game.of s` to construct the game.

`pgame_state.L : S → finset S` and `pgame_state.R : S → finset S` describe the states reachable
by a move by Left or Right. `pgame_state.turn_bound : S → ℕ` gives an upper bound on the number of
possible turns remaining from this state.
-/
class state (S : Type u) where
  turn_bound : S → ℕ
  L : S → finset S
  R : S → finset S
  left_bound : ∀ {s t : S}, t ∈ L s → turn_bound t < turn_bound s
  right_bound : ∀ {s t : S}, t ∈ R s → turn_bound t < turn_bound s

theorem turn_bound_ne_zero_of_left_move {S : Type u} [state S] {s : S} {t : S} (m : t ∈ state.L s) :
    state.turn_bound s ≠ 0 :=
  sorry

theorem turn_bound_ne_zero_of_right_move {S : Type u} [state S] {s : S} {t : S}
    (m : t ∈ state.R s) : state.turn_bound s ≠ 0 :=
  sorry

theorem turn_bound_of_left {S : Type u} [state S] {s : S} {t : S} (m : t ∈ state.L s) (n : ℕ)
    (h : state.turn_bound s ≤ n + 1) : state.turn_bound t ≤ n :=
  nat.le_of_lt_succ (nat.lt_of_lt_of_le (state.left_bound m) h)

theorem turn_bound_of_right {S : Type u} [state S] {s : S} {t : S} (m : t ∈ state.R s) (n : ℕ)
    (h : state.turn_bound s ≤ n + 1) : state.turn_bound t ≤ n :=
  nat.le_of_lt_succ (nat.lt_of_lt_of_le (state.right_bound m) h)

/--
Construct a `pgame` from a state and a (not necessarily optimal) bound on the number of
turns remaining.
-/
def of_aux {S : Type u} [state S] (n : ℕ) (s : S) (h : state.turn_bound s ≤ n) : pgame := sorry

/-- Two different (valid) turn bounds give equivalent games. -/
def of_aux_relabelling {S : Type u} [state S] (s : S) (n : ℕ) (m : ℕ) (hn : state.turn_bound s ≤ n)
    (hm : state.turn_bound s ≤ m) : relabelling (of_aux n s hn) (of_aux m s hm) :=
  sorry

/-- Construct a combinatorial `pgame` from a state. -/
def of {S : Type u} [state S] (s : S) : pgame := of_aux (state.turn_bound s) s sorry

/--
The equivalence between `left_moves` for a `pgame` constructed using `of_aux _ s _`, and `L s`.
-/
def left_moves_of_aux {S : Type u} [state S] (n : ℕ) {s : S} (h : state.turn_bound s ≤ n) :
    left_moves (of_aux n s h) ≃ Subtype fun (t : S) => t ∈ state.L s :=
  Nat.rec (fun (h : state.turn_bound s ≤ 0) => equiv.refl (left_moves (of_aux 0 s h)))
    (fun (n_n : ℕ)
      (n_ih :
      (h : state.turn_bound s ≤ n_n) →
        left_moves (of_aux n_n s h) ≃ Subtype fun (t : S) => t ∈ state.L s)
      (h : state.turn_bound s ≤ Nat.succ n_n) =>
      equiv.refl (left_moves (of_aux (Nat.succ n_n) s h)))
    n h

/--
The equivalence between `left_moves` for a `pgame` constructed using `of s`, and `L s`.
-/
def left_moves_of {S : Type u} [state S] (s : S) :
    left_moves (of s) ≃ Subtype fun (t : S) => t ∈ state.L s :=
  left_moves_of_aux (state.turn_bound s) (of._proof_1 s)

/--
The equivalence between `right_moves` for a `pgame` constructed using `of_aux _ s _`, and `R s`.
-/
def right_moves_of_aux {S : Type u} [state S] (n : ℕ) {s : S} (h : state.turn_bound s ≤ n) :
    right_moves (of_aux n s h) ≃ Subtype fun (t : S) => t ∈ state.R s :=
  Nat.rec (fun (h : state.turn_bound s ≤ 0) => equiv.refl (right_moves (of_aux 0 s h)))
    (fun (n_n : ℕ)
      (n_ih :
      (h : state.turn_bound s ≤ n_n) →
        right_moves (of_aux n_n s h) ≃ Subtype fun (t : S) => t ∈ state.R s)
      (h : state.turn_bound s ≤ Nat.succ n_n) =>
      equiv.refl (right_moves (of_aux (Nat.succ n_n) s h)))
    n h

/-- The equivalence between `right_moves` for a `pgame` constructed using `of s`, and `R s`. -/
def right_moves_of {S : Type u} [state S] (s : S) :
    right_moves (of s) ≃ Subtype fun (t : S) => t ∈ state.R s :=
  right_moves_of_aux (state.turn_bound s) (of._proof_1 s)

/--
The relabelling showing `move_left` applied to a game constructed using `of_aux`
has itself been constructed using `of_aux`.
-/
def relabelling_move_left_aux {S : Type u} [state S] (n : ℕ) {s : S} (h : state.turn_bound s ≤ n)
    (t : left_moves (of_aux n s h)) :
    relabelling (move_left (of_aux n s h) t)
        (of_aux (n - 1) (↑(coe_fn (left_moves_of_aux n h) t))
          (relabelling_move_left_aux._proof_1 n h t)) :=
  Nat.rec (fun (h : state.turn_bound s ≤ 0) (t : left_moves (of_aux 0 s h)) => False._oldrec sorry)
    (fun (n_n : ℕ)
      (n_ih :
      (h : state.turn_bound s ≤ n_n) →
        (t : left_moves (of_aux n_n s h)) →
          relabelling (move_left (of_aux n_n s h) t)
            (of_aux (n_n - 1) ↑(coe_fn (left_moves_of_aux n_n h) t) sorry))
      (h : state.turn_bound s ≤ Nat.succ n_n) (t : left_moves (of_aux (Nat.succ n_n) s h)) =>
      relabelling.refl (move_left (of_aux (Nat.succ n_n) s h) t))
    n h t

/--
The relabelling showing `move_left` applied to a game constructed using `of`
has itself been constructed using `of`.
-/
def relabelling_move_left {S : Type u} [state S] (s : S) (t : left_moves (of s)) :
    relabelling (move_left (of s) t) (of ↑(equiv.to_fun (left_moves_of s) t)) :=
  relabelling.trans (relabelling_move_left_aux (state.turn_bound s) (of._proof_1 s) t)
    (of_aux_relabelling (↑(coe_fn (left_moves_of_aux (state.turn_bound s) (of._proof_1 s)) t))
      (state.turn_bound s - 1) (state.turn_bound ↑(equiv.to_fun (left_moves_of s) t)) sorry sorry)

/--
The relabelling showing `move_right` applied to a game constructed using `of_aux`
has itself been constructed using `of_aux`.
-/
def relabelling_move_right_aux {S : Type u} [state S] (n : ℕ) {s : S} (h : state.turn_bound s ≤ n)
    (t : right_moves (of_aux n s h)) :
    relabelling (move_right (of_aux n s h) t)
        (of_aux (n - 1) (↑(coe_fn (right_moves_of_aux n h) t))
          (relabelling_move_right_aux._proof_1 n h t)) :=
  Nat.rec (fun (h : state.turn_bound s ≤ 0) (t : right_moves (of_aux 0 s h)) => False._oldrec sorry)
    (fun (n_n : ℕ)
      (n_ih :
      (h : state.turn_bound s ≤ n_n) →
        (t : right_moves (of_aux n_n s h)) →
          relabelling (move_right (of_aux n_n s h) t)
            (of_aux (n_n - 1) ↑(coe_fn (right_moves_of_aux n_n h) t) sorry))
      (h : state.turn_bound s ≤ Nat.succ n_n) (t : right_moves (of_aux (Nat.succ n_n) s h)) =>
      relabelling.refl (move_right (of_aux (Nat.succ n_n) s h) t))
    n h t

/--
The relabelling showing `move_right` applied to a game constructed using `of`
has itself been constructed using `of`.
-/
def relabelling_move_right {S : Type u} [state S] (s : S) (t : right_moves (of s)) :
    relabelling (move_right (of s) t) (of ↑(equiv.to_fun (right_moves_of s) t)) :=
  relabelling.trans (relabelling_move_right_aux (state.turn_bound s) (of._proof_1 s) t)
    (of_aux_relabelling (↑(coe_fn (right_moves_of_aux (state.turn_bound s) (of._proof_1 s)) t))
      (state.turn_bound s - 1) (state.turn_bound ↑(equiv.to_fun (right_moves_of s) t)) sorry sorry)

protected instance fintype_left_moves_of_aux {S : Type u} [state S] (n : ℕ) (s : S)
    (h : state.turn_bound s ≤ n) : fintype (left_moves (of_aux n s h)) :=
  fintype.of_equiv (Subtype fun (t : S) => t ∈ state.L s) (equiv.symm (left_moves_of_aux n h))

protected instance fintype_right_moves_of_aux {S : Type u} [state S] (n : ℕ) (s : S)
    (h : state.turn_bound s ≤ n) : fintype (right_moves (of_aux n s h)) :=
  fintype.of_equiv (Subtype fun (t : S) => t ∈ state.R s) (equiv.symm (right_moves_of_aux n h))

protected instance short_of_aux {S : Type u} [state S] (n : ℕ) {s : S}
    (h : state.turn_bound s ≤ n) : short (of_aux n s h) :=
  sorry

protected instance short_of {S : Type u} [state S] (s : S) : short (of s) :=
  id (pgame.short_of_aux (state.turn_bound s) (of._proof_1 s))

end pgame


namespace game


/-- Construct a combinatorial `game` from a state. -/
def of {S : Type u} [pgame.state S] (s : S) : game := quotient.mk (pgame.of s)

end Mathlib