/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.set_theory.game
import Mathlib.data.fintype.basic
import PostPort

universes u l u_1 

namespace Mathlib

/-!
# Short games

A combinatorial game is `short` [Conway, ch.9][conway2001] if it has only finitely many positions.
In particular, this means there is a finite set of moves at every point.

We prove that the order relations `≤` and `<`, and the equivalence relation `≈`, are decidable on
short games, although unfortunately in practice `dec_trivial` doesn't seem to be able to
prove anything using these instances.
-/

namespace pgame


/-- A short game is a game with a finite set of moves at every turn. -/
class inductive short : pgame → Type (u + 1)
where
| mk : {α β : Type u} →
  {L : α → pgame} →
    {R : β → pgame} →
      ((i : α) → short (L i)) →
        ((j : β) → short (R j)) → [_inst_1 : fintype α] → [_inst_2 : fintype β] → short (mk α β L R)

protected instance subsingleton_short (x : pgame) : subsingleton (short x) :=
  sorry

/-- A synonym for `short.mk` that specifies the pgame in an implicit argument. -/
def short.mk' {x : pgame} [fintype (left_moves x)] [fintype (right_moves x)] (sL : (i : left_moves x) → short (move_left x i)) (sR : (j : right_moves x) → short (move_right x j)) : short x :=
  pgame.cases_on x
    (fun (x_α x_β : Type u_1) (x_ᾰ : x_α → pgame) (x_ᾰ_1 : x_β → pgame)
      [_inst_1 : fintype (left_moves (mk x_α x_β x_ᾰ x_ᾰ_1))] [_inst_2 : fintype (right_moves (mk x_α x_β x_ᾰ x_ᾰ_1))]
      (sL : (i : left_moves (mk x_α x_β x_ᾰ x_ᾰ_1)) → short (move_left (mk x_α x_β x_ᾰ x_ᾰ_1) i))
      (sR : (j : right_moves (mk x_α x_β x_ᾰ x_ᾰ_1)) → short (move_right (mk x_α x_β x_ᾰ x_ᾰ_1) j)) =>
      id
        (fun (x_α x_β : Type u_1) (x_ᾰ : x_α → pgame) (x_ᾰ_1 : x_β → pgame) (sL : (i : x_α) → short (x_ᾰ i))
          (sR : (j : x_β) → short (x_ᾰ_1 j)) => short.mk sL sR)
        x_α x_β x_ᾰ x_ᾰ_1 _inst_1 _inst_2 sL sR)
    _inst_1 _inst_2 sL sR

/--
Extracting the `fintype` instance for the indexing type for Left's moves in a short game.
This is an unindexed typeclass, so it can't be made a global instance.
-/
def fintype_left {α : Type u} {β : Type u} {L : α → pgame} {R : β → pgame} [S : short (mk α β L R)] : fintype α :=
  short.cases_on S
    (fun {S_α S_β : Type u} {S_L : S_α → pgame} {S_R : S_β → pgame} (S_sL : (i : S_α) → short (S_L i))
      (S_sR : (j : S_β) → short (S_R j)) [F : fintype S_α] [S__inst_2 : fintype S_β]
      (H_1 : mk α β L R = mk S_α S_β S_L S_R) =>
      pgame.no_confusion H_1
        fun (α_eq : α = S_α) =>
          Eq._oldrec
            (fun {S_L : α → pgame} (S_sL : (i : α) → short (S_L i)) [F : fintype α] (β_eq : β = S_β) =>
              Eq._oldrec
                (fun {S_R : β → pgame} (S_sR : (j : β) → short (S_R j)) (ᾰ_eq : L == S_L) =>
                  Eq._oldrec
                    (fun (S_sL : (i : α) → short (L i)) (ᾰ_eq : R == S_R) =>
                      Eq._oldrec
                        (fun (S_sR : (j : β) → short (R j)) (H_2 : S == short.mk S_sL S_sR) => Eq._oldrec F sorry) sorry
                        S_sR)
                    sorry S_sL)
                β_eq S_R S_sR S__inst_2)
            α_eq S_L S_sL F)
    sorry sorry

protected instance fintype_left_moves (x : pgame) [S : short x] : fintype (left_moves x) :=
  pgame.cases_on x (fun (x_α x_β : Type u_1) (x_ᾰ : x_α → pgame) (x_ᾰ_1 : x_β → pgame) => id fintype_left) S

/--
Extracting the `fintype` instance for the indexing type for Right's moves in a short game.
This is an unindexed typeclass, so it can't be made a global instance.
-/
def fintype_right {α : Type u} {β : Type u} {L : α → pgame} {R : β → pgame} [S : short (mk α β L R)] : fintype β :=
  short.cases_on S
    (fun {S_α S_β : Type u} {S_L : S_α → pgame} {S_R : S_β → pgame} (S_sL : (i : S_α) → short (S_L i))
      (S_sR : (j : S_β) → short (S_R j)) [S__inst_1 : fintype S_α] [F : fintype S_β]
      (H_1 : mk α β L R = mk S_α S_β S_L S_R) =>
      pgame.no_confusion H_1
        fun (α_eq : α = S_α) =>
          Eq._oldrec
            (fun {S_L : α → pgame} (S_sL : (i : α) → short (S_L i)) (β_eq : β = S_β) =>
              Eq._oldrec
                (fun {S_R : β → pgame} (S_sR : (j : β) → short (S_R j)) [F : fintype β] (ᾰ_eq : L == S_L) =>
                  Eq._oldrec
                    (fun (S_sL : (i : α) → short (L i)) (ᾰ_eq : R == S_R) =>
                      Eq._oldrec
                        (fun (S_sR : (j : β) → short (R j)) (H_2 : S == short.mk S_sL S_sR) => Eq._oldrec F sorry) sorry
                        S_sR)
                    sorry S_sL)
                β_eq S_R S_sR F)
            α_eq S_L S_sL S__inst_1)
    sorry sorry

protected instance fintype_right_moves (x : pgame) [S : short x] : fintype (right_moves x) :=
  pgame.cases_on x (fun (x_α x_β : Type u_1) (x_ᾰ : x_α → pgame) (x_ᾰ_1 : x_β → pgame) => id fintype_right) S

protected instance move_left_short (x : pgame) [S : short x] (i : left_moves x) : short (move_left x i) :=
  short.cases_on S
    (fun {S_α S_β : Type u_1} {S_L : S_α → pgame} {S_R : S_β → pgame} (L : (i : S_α) → short (S_L i))
      (S_sR : (j : S_β) → short (S_R j)) (H_1 : x = mk S_α S_β S_L S_R) =>
      Eq._oldrec
        (fun [S : short (mk S_α S_β S_L S_R)] (i : left_moves (mk S_α S_β S_L S_R)) (H_2 : S == short.mk L S_sR) =>
          Eq._oldrec (L i) sorry)
        sorry S i)
    (Eq.refl x) sorry

/--
Extracting the `short` instance for a move by Left.
This would be a dangerous instance potentially introducing new metavariables
in typeclass search, so we only make it an instance locally.
-/
def move_left_short' {xl : Type u_1} {xr : Type u_1} (xL : xl → pgame) (xR : xr → pgame) [S : short (mk xl xr xL xR)] (i : xl) : short (xL i) :=
  short.cases_on S
    (fun {S_α S_β : Type u_1} {S_L : S_α → pgame} {S_R : S_β → pgame} (L : (i : S_α) → short (S_L i))
      (S_sR : (j : S_β) → short (S_R j)) [S__inst_1 : fintype S_α] [S__inst_2 : fintype S_β]
      (H_1 : mk xl xr xL xR = mk S_α S_β S_L S_R) =>
      pgame.no_confusion H_1
        fun (α_eq : xl = S_α) =>
          Eq._oldrec
            (fun {S_L : xl → pgame} (L : (i : xl) → short (S_L i)) (β_eq : xr = S_β) =>
              Eq._oldrec
                (fun {S_R : xr → pgame} (S_sR : (j : xr) → short (S_R j)) (ᾰ_eq : xL == S_L) =>
                  Eq._oldrec
                    (fun (L : (i : xl) → short (xL i)) (ᾰ_eq : xR == S_R) =>
                      Eq._oldrec
                        (fun (S_sR : (j : xr) → short (xR j)) (H_2 : S == short.mk L S_sR) => Eq._oldrec (L i) sorry)
                        sorry S_sR)
                    sorry L)
                β_eq S_R S_sR S__inst_2)
            α_eq S_L L S__inst_1)
    sorry sorry

protected instance move_right_short (x : pgame) [S : short x] (j : right_moves x) : short (move_right x j) :=
  short.cases_on S
    (fun {S_α S_β : Type u_1} {S_L : S_α → pgame} {S_R : S_β → pgame} (S_sL : (i : S_α) → short (S_L i))
      (R : (j : S_β) → short (S_R j)) (H_1 : x = mk S_α S_β S_L S_R) =>
      Eq._oldrec
        (fun [S : short (mk S_α S_β S_L S_R)] (j : right_moves (mk S_α S_β S_L S_R)) (H_2 : S == short.mk S_sL R) =>
          Eq._oldrec (R j) sorry)
        sorry S j)
    (Eq.refl x) sorry

/--
Extracting the `short` instance for a move by Right.
This would be a dangerous instance potentially introducing new metavariables
in typeclass search, so we only make it an instance locally.
-/
def move_right_short' {xl : Type u_1} {xr : Type u_1} (xL : xl → pgame) (xR : xr → pgame) [S : short (mk xl xr xL xR)] (j : xr) : short (xR j) :=
  short.cases_on S
    (fun {S_α S_β : Type u_1} {S_L : S_α → pgame} {S_R : S_β → pgame} (S_sL : (i : S_α) → short (S_L i))
      (R : (j : S_β) → short (S_R j)) [S__inst_1 : fintype S_α] [S__inst_2 : fintype S_β]
      (H_1 : mk xl xr xL xR = mk S_α S_β S_L S_R) =>
      pgame.no_confusion H_1
        fun (α_eq : xl = S_α) =>
          Eq._oldrec
            (fun {S_L : xl → pgame} (S_sL : (i : xl) → short (S_L i)) (β_eq : xr = S_β) =>
              Eq._oldrec
                (fun {S_R : xr → pgame} (R : (j : xr) → short (S_R j)) (ᾰ_eq : xL == S_L) =>
                  Eq._oldrec
                    (fun (S_sL : (i : xl) → short (xL i)) (ᾰ_eq : xR == S_R) =>
                      Eq._oldrec
                        (fun (R : (j : xr) → short (xR j)) (H_2 : S == short.mk S_sL R) => Eq._oldrec (R j) sorry) sorry
                        R)
                    sorry S_sL)
                β_eq S_R R S__inst_2)
            α_eq S_L S_sL S__inst_1)
    sorry sorry

protected instance short.of_pempty {xL : pempty → pgame} {xR : pempty → pgame} : short (mk pempty pempty xL xR) :=
  short.mk (fun (i : pempty) => pempty.elim i) fun (j : pempty) => pempty.elim j

protected instance short_0 : short 0 :=
  short.mk (fun (i : pempty) => pempty.cases_on (fun (i : pempty) => short (pempty.elim i)) i)
    fun (i : pempty) => pempty.cases_on (fun (i : pempty) => short (pempty.elim i)) i

protected instance short_1 : short 1 :=
  short.mk (fun (i : PUnit) => punit.cases_on i pgame.short_0)
    fun (j : pempty) => pempty.cases_on (fun (j : pempty) => short (pempty.elim j)) j

/-- Evidence that every `pgame` in a list is `short`. -/
class inductive list_short : List pgame → Type (u + 1)
where
| nil : list_short []
| cons : (hd : pgame) → [_inst_1 : short hd] → (tl : List pgame) → [_inst_2 : list_short tl] → list_short (hd :: tl)

protected instance list_short_nth_le (L : List pgame) [list_short L] (i : fin (list.length L)) : short (list.nth_le L (↑i) (list_short_nth_le._proof_1 L i)) :=
  sorry

protected instance short_of_lists (L : List pgame) (R : List pgame) [list_short L] [list_short R] : short (of_lists L R) :=
  sorry

/-- If `x` is a short game, and `y` is a relabelling of `x`, then `y` is also short. -/
def short_of_relabelling {x : pgame} {y : pgame} (R : relabelling x y) (S : short x) : short y :=
  sorry

/-- If `x` has no left move or right moves, it is (very!) short. -/
def short_of_equiv_empty {x : pgame} (el : left_moves x ≃ pempty) (er : right_moves x ≃ pempty) : short x :=
  short_of_relabelling (relabelling.symm (relabel_relabelling el er)) short.of_pempty

protected instance short_neg (x : pgame) [short x] : short (-x) :=
  sorry

protected instance short_add (x : pgame) (y : pgame) [short x] [short y] : short (x + y) :=
  sorry

protected instance short_nat (n : ℕ) : short ↑n :=
  sorry

protected instance short_bit0 (x : pgame) [short x] : short (bit0 x) :=
  id (pgame.short_add x x)

protected instance short_bit1 (x : pgame) [short x] : short (bit1 x) :=
  id (pgame.short_add (bit0 x) 1)

/--
Auxiliary construction of decidability instances.
We build `decidable (x ≤ y)` and `decidable (x < y)` in a simultaneous induction.
Instances for the two projections separately are provided below.
-/
def le_lt_decidable (x : pgame) (y : pgame) [short x] [short y] : Decidable (x ≤ y) × Decidable (x < y) :=
  sorry

protected instance le_decidable (x : pgame) (y : pgame) [short x] [short y] : Decidable (x ≤ y) :=
  prod.fst (le_lt_decidable x y _inst_1 _inst_2)

protected instance lt_decidable (x : pgame) (y : pgame) [short x] [short y] : Decidable (x < y) :=
  prod.snd (le_lt_decidable x y _inst_1 _inst_2)

protected instance equiv_decidable (x : pgame) (y : pgame) [short x] [short y] : Decidable (x ≈ y) :=
  and.decidable

