/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Mario Carneiro, Isabel Longbottom, Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.logic.embedding
import Mathlib.data.nat.cast
import Mathlib.data.fin
import Mathlib.PostPort

universes u l u_1 u_2 

namespace Mathlib

/-!
# Combinatorial (pre-)games.

The basic theory of combinatorial games, following Conway's book `On Numbers and Games`. We
construct "pregames", define an ordering and arithmetic operations on them, then show that the
operations descend to "games", defined via the equivalence relation `p ≈ q ↔ p ≤ q ∧ q ≤ p`.

The surreal numbers will be built as a quotient of a subtype of pregames.

A pregame (`pgame` below) is axiomatised via an inductive type, whose sole constructor takes two
types (thought of as indexing the the possible moves for the players Left and Right), and a pair of
functions out of these types to `pgame` (thought of as describing the resulting game after making a
move).

Combinatorial games themselves, as a quotient of pregames, are constructed in `game.lean`.

## Conway induction

By construction, the induction principle for pregames is exactly "Conway induction". That is, to
prove some predicate `pgame → Prop` holds for all pregames, it suffices to prove that for every
pregame `g`, if the predicate holds for every game resulting from making a move, then it also holds
for `g`.

While it is often convenient to work "by induction" on pregames, in some situations this becomes
awkward, so we also define accessor functions `left_moves`, `right_moves`, `move_left` and
`move_right`. There is a relation `subsequent p q`, saying that `p` can be reached by playing some
non-empty sequence of moves starting from `q`, an instance `well_founded subsequent`, and a local
tactic `pgame_wf_tac` which is helpful for discharging proof obligations in inductive proofs relying
on this relation.

## Order properties

Pregames have both a `≤` and a `<` relation, which are related in quite a subtle way. In particular,
it is worth noting that in Lean's (perhaps unfortunate?) definition of a `preorder`, we have
`lt_iff_le_not_le : ∀ a b : α, a < b ↔ (a ≤ b ∧ ¬ b ≤ a)`, but this is _not_ satisfied by the usual
`≤` and `<` relations on pregames. (It is satisfied once we restrict to the surreal numbers.) In
particular, `<` is not transitive; there is an example below showing `0 < star ∧ star < 0`.

We do have
```
theorem not_le {x y : pgame} : ¬ x ≤ y ↔ y < x := ...
theorem not_lt {x y : pgame} : ¬ x < y ↔ y ≤ x := ...
```

The statement `0 ≤ x` means that Left has a good response to any move by Right; in particular, the
theorem `zero_le` below states
```
0 ≤ x ↔ ∀ j : x.right_moves, ∃ i : (x.move_right j).left_moves, 0 ≤ (x.move_right j).move_left i
```
On the other hand the statement `0 < x` means that Left has a good move right now; in particular the
theorem `zero_lt` below states
```
0 < x ↔ ∃ i : left_moves x, ∀ j : right_moves (x.move_left i), 0 < (x.move_left i).move_right j
```

The theorems `le_def`, `lt_def`, give a recursive characterisation of each relation, in terms of
themselves two moves later. The theorems `le_def_lt` and `lt_def_lt` give recursive
characterisations of each relation in terms of the other relation one move later.

We define an equivalence relation `equiv p q ↔ p ≤ q ∧ q ≤ p`. Later, games will be defined as the
quotient by this relation.

## Algebraic structures

We next turn to defining the operations necessary to make games into a commutative additive group.
Addition is defined for $x = \{xL | xR\}$ and $y = \{yL | yR\}$ by $x + y = \{xL + y, x + yL | xR +
y, x + yR\}$. Negation is defined by $\{xL | xR\} = \{-xR | -xL\}$.

The order structures interact in the expected way with addition, so we have
```
theorem le_iff_sub_nonneg {x y : pgame} : x ≤ y ↔ 0 ≤ y - x := sorry
theorem lt_iff_sub_pos {x y : pgame} : x < y ↔ 0 < y - x := sorry
```

We show that these operations respect the equivalence relation, and hence descend to games. At the
level of games, these operations satisfy all the laws of a commutative group. To prove the necessary
equivalence relations at the level of pregames, we introduce the notion of a `relabelling` of a
game, and show, for example, that there is a relabelling between `x + (y + z)` and `(x + y) + z`.

## Future work
* The theory of dominated and reversible positions, and unique normal form for short games.
* Analysis of basic domineering positions.
* Hex.
* Temperature.
* The development of surreal numbers, based on this development of combinatorial games, is still
  quite incomplete.

## References

The material here is all drawn from
* [Conway, *On numbers and games*][conway2001]

An interested reader may like to formalise some of the material from
* [Andreas Blass, *A game semantics for linear logic*][MR1167694]
* [André Joyal, *Remarques sur la théorie des jeux à deux personnes*][joyal1997]
-/

/-- The type of pre-games, before we have quotiented
  by extensionality. In ZFC, a combinatorial game is constructed from
  two sets of combinatorial games that have been constructed at an earlier
  stage. To do this in type theory, we say that a pre-game is built
  inductively from two families of pre-games indexed over any type
  in Type u. The resulting type `pgame.{u}` lives in `Type (u+1)`,
  reflecting that it is a proper class in ZFC. -/
inductive pgame 
where
| mk : (α β : Type u) → (α → pgame) → (β → pgame) → pgame

namespace pgame


/--
Construct a pre-game from list of pre-games describing the available moves for Left and Right.
-/
-- TODO provide some API describing the interaction with

-- `left_moves`, `right_moves`, `move_left` and `move_right` below.

-- TODO define this at the level of games, as well, and perhaps also for finsets of games.

def of_lists (L : List pgame) (R : List pgame) : pgame :=
  mk (fin (list.length L)) (fin (list.length R)) (fun (i : fin (list.length L)) => list.nth_le L ↑i sorry)
    fun (j : fin (list.length R)) => list.nth_le R (subtype.val j) sorry

/-- The indexing type for allowable moves by Left. -/
def left_moves : pgame → Type u :=
  sorry

/-- The indexing type for allowable moves by Right. -/
def right_moves : pgame → Type u :=
  sorry

/-- The new game after Left makes an allowed move. -/
def move_left (g : pgame) : left_moves g → pgame :=
  sorry

/-- The new game after Right makes an allowed move. -/
def move_right (g : pgame) : right_moves g → pgame :=
  sorry

@[simp] theorem left_moves_mk {xl : Type u_1} {xr : Type u_1} {xL : xl → pgame} {xR : xr → pgame} : left_moves (mk xl xr xL xR) = xl :=
  rfl

@[simp] theorem move_left_mk {xl : Type u_1} {xr : Type u_1} {xL : xl → pgame} {xR : xr → pgame} {i : left_moves (mk xl xr xL xR)} : move_left (mk xl xr xL xR) i = xL i :=
  rfl

@[simp] theorem right_moves_mk {xl : Type u_1} {xr : Type u_1} {xL : xl → pgame} {xR : xr → pgame} : right_moves (mk xl xr xL xR) = xr :=
  rfl

@[simp] theorem move_right_mk {xl : Type u_1} {xr : Type u_1} {xL : xl → pgame} {xR : xr → pgame} {j : right_moves (mk xl xr xL xR)} : move_right (mk xl xr xL xR) j = xR j :=
  rfl

/-- `subsequent p q` says that `p` can be obtained by playing
  some nonempty sequence of moves from `q`. -/
inductive subsequent : pgame → pgame → Prop
where
| left : ∀ (x : pgame) (i : left_moves x), subsequent (move_left x i) x
| right : ∀ (x : pgame) (j : right_moves x), subsequent (move_right x j) x
| trans : ∀ (x y z : pgame), subsequent x y → subsequent y z → subsequent x z

theorem wf_subsequent : well_founded subsequent := sorry

protected instance has_well_founded : has_well_founded pgame :=
  has_well_founded.mk subsequent wf_subsequent

/-- A move by Left produces a subsequent game. (For use in pgame_wf_tac.) -/
theorem subsequent.left_move {xl : Type u_1} {xr : Type u_1} {xL : xl → pgame} {xR : xr → pgame} {i : xl} : subsequent (xL i) (mk xl xr xL xR) :=
  subsequent.left (mk xl xr xL xR) i

/-- A move by Right produces a subsequent game. (For use in pgame_wf_tac.) -/
theorem subsequent.right_move {xl : Type u_1} {xr : Type u_1} {xL : xl → pgame} {xR : xr → pgame} {j : xr} : subsequent (xR j) (mk xl xr xL xR) :=
  subsequent.right (mk xl xr xL xR) j

/-- A local tactic for proving well-foundedness of recursive definitions involving pregames. -/
/-- The pre-game `zero` is defined by `0 = { | }`. -/
protected instance has_zero : HasZero pgame :=
  { zero := mk pempty pempty pempty.elim pempty.elim }

@[simp] theorem zero_left_moves : left_moves 0 = pempty :=
  rfl

@[simp] theorem zero_right_moves : right_moves 0 = pempty :=
  rfl

protected instance inhabited : Inhabited pgame :=
  { default := 0 }

/-- The pre-game `one` is defined by `1 = { 0 | }`. -/
protected instance has_one : HasOne pgame :=
  { one := mk PUnit pempty (fun (_x : PUnit) => 0) pempty.elim }

@[simp] theorem one_left_moves : left_moves 1 = PUnit :=
  rfl

@[simp] theorem one_move_left : move_left 1 PUnit.unit = 0 :=
  rfl

@[simp] theorem one_right_moves : right_moves 1 = pempty :=
  rfl

/-- Define simultaneously by mutual induction the `<=` and `<`
  relation on pre-games. The ZFC definition says that `x = {xL | xR}`
  is less or equal to `y = {yL | yR}` if `∀ x₁ ∈ xL, x₁ < y`
  and `∀ y₂ ∈ yR, x < y₂`, where `x < y` is the same as `¬ y <= x`.
  This is a tricky induction because it only decreases one side at
  a time, and it also swaps the arguments in the definition of `<`.
  The solution is to define `x < y` and `x <= y` simultaneously. -/
def le_lt (x : pgame) (y : pgame) : Prop × Prop :=
  sorry

protected instance has_le : HasLessEq pgame :=
  { LessEq := fun (x y : pgame) => prod.fst (le_lt x y) }

protected instance has_lt : HasLess pgame :=
  { Less := fun (x y : pgame) => prod.snd (le_lt x y) }

/-- Definition of `x ≤ y` on pre-games built using the constructor. -/
@[simp] theorem mk_le_mk {xl : Type u_1} {xr : Type u_1} {xL : xl → pgame} {xR : xr → pgame} {yl : Type u_1} {yr : Type u_1} {yL : yl → pgame} {yR : yr → pgame} : mk xl xr xL xR ≤ mk yl yr yL yR ↔ (∀ (i : xl), xL i < mk yl yr yL yR) ∧ ∀ (j : yr), mk xl xr xL xR < yR j :=
  iff.rfl

/-- Definition of `x ≤ y` on pre-games, in terms of `<` -/
theorem le_def_lt {x : pgame} {y : pgame} : x ≤ y ↔ (∀ (i : left_moves x), move_left x i < y) ∧ ∀ (j : right_moves y), x < move_right y j := sorry

/-- Definition of `x < y` on pre-games built using the constructor. -/
@[simp] theorem mk_lt_mk {xl : Type u_1} {xr : Type u_1} {xL : xl → pgame} {xR : xr → pgame} {yl : Type u_1} {yr : Type u_1} {yL : yl → pgame} {yR : yr → pgame} : mk xl xr xL xR < mk yl yr yL yR ↔ (∃ (i : yl), mk xl xr xL xR ≤ yL i) ∨ ∃ (j : xr), xR j ≤ mk yl yr yL yR :=
  iff.rfl

/-- Definition of `x < y` on pre-games, in terms of `≤` -/
theorem lt_def_le {x : pgame} {y : pgame} : x < y ↔ (∃ (i : left_moves y), x ≤ move_left y i) ∨ ∃ (j : right_moves x), move_right x j ≤ y := sorry

/-- The definition of `x ≤ y` on pre-games, in terms of `≤` two moves later. -/
theorem le_def {x : pgame} {y : pgame} : x ≤ y ↔
  (∀ (i : left_moves x),
      (∃ (i' : left_moves y), move_left x i ≤ move_left y i') ∨
        ∃ (j : right_moves (move_left x i)), move_right (move_left x i) j ≤ y) ∧
    ∀ (j : right_moves y),
      (∃ (i : left_moves (move_right y j)), x ≤ move_left (move_right y j) i) ∨
        ∃ (j' : right_moves x), move_right x j' ≤ move_right y j := sorry

/-- The definition of `x < y` on pre-games, in terms of `<` two moves later. -/
theorem lt_def {x : pgame} {y : pgame} : x < y ↔
  (∃ (i : left_moves y),
      (∀ (i' : left_moves x), move_left x i' < move_left y i) ∧
        ∀ (j : right_moves (move_left y i)), x < move_right (move_left y i) j) ∨
    ∃ (j : right_moves x),
      (∀ (i : left_moves (move_right x j)), move_left (move_right x j) i < y) ∧
        ∀ (j' : right_moves y), move_right x j < move_right y j' := sorry

/-- The definition of `x ≤ 0` on pre-games, in terms of `≤ 0` two moves later. -/
theorem le_zero {x : pgame} : x ≤ 0 ↔ ∀ (i : left_moves x), ∃ (j : right_moves (move_left x i)), move_right (move_left x i) j ≤ 0 := sorry

/-- The definition of `0 ≤ x` on pre-games, in terms of `0 ≤` two moves later. -/
theorem zero_le {x : pgame} : 0 ≤ x ↔ ∀ (j : right_moves x), ∃ (i : left_moves (move_right x j)), 0 ≤ move_left (move_right x j) i := sorry

/-- The definition of `x < 0` on pre-games, in terms of `< 0` two moves later. -/
theorem lt_zero {x : pgame} : x < 0 ↔ ∃ (j : right_moves x), ∀ (i : left_moves (move_right x j)), move_left (move_right x j) i < 0 := sorry

/-- The definition of `0 < x` on pre-games, in terms of `< x` two moves later. -/
theorem zero_lt {x : pgame} : 0 < x ↔ ∃ (i : left_moves x), ∀ (j : right_moves (move_left x i)), 0 < move_right (move_left x i) j := sorry

/-- Given a right-player-wins game, provide a response to any move by left. -/
def right_response {x : pgame} (h : x ≤ 0) (i : left_moves x) : right_moves (move_left x i) :=
  classical.some sorry

/-- Show that the response for right provided by `right_response`
    preserves the right-player-wins condition. -/
theorem right_response_spec {x : pgame} (h : x ≤ 0) (i : left_moves x) : move_right (move_left x i) (right_response h i) ≤ 0 :=
  classical.some_spec (iff.mp le_zero h i)

/-- Given a left-player-wins game, provide a response to any move by right. -/
def left_response {x : pgame} (h : 0 ≤ x) (j : right_moves x) : left_moves (move_right x j) :=
  classical.some sorry

/-- Show that the response for left provided by `left_response`
    preserves the left-player-wins condition. -/
theorem left_response_spec {x : pgame} (h : 0 ≤ x) (j : right_moves x) : 0 ≤ move_left (move_right x j) (left_response h j) :=
  classical.some_spec (iff.mp zero_le h j)

theorem lt_of_le_mk {xl : Type u_1} {xr : Type u_1} {xL : xl → pgame} {xR : xr → pgame} {y : pgame} {i : xl} : mk xl xr xL xR ≤ y → xL i < y :=
  pgame.cases_on y
    fun (y_α y_β : Type u_1) (y_ᾰ : y_α → pgame) (y_ᾰ_1 : y_β → pgame) (h : mk xl xr xL xR ≤ mk y_α y_β y_ᾰ y_ᾰ_1) =>
      and.left h i

theorem lt_of_mk_le {x : pgame} {yl : Type u_1} {yr : Type u_1} {yL : yl → pgame} {yR : yr → pgame} {i : yr} : x ≤ mk yl yr yL yR → x < yR i :=
  pgame.cases_on x
    fun (x_α x_β : Type u_1) (x_ᾰ : x_α → pgame) (x_ᾰ_1 : x_β → pgame) (h : mk x_α x_β x_ᾰ x_ᾰ_1 ≤ mk yl yr yL yR) =>
      and.right h i

theorem mk_lt_of_le {xl : Type u_1} {xr : Type u_1} {xL : xl → pgame} {xR : xr → pgame} {y : pgame} {i : xr} : xR i ≤ y → mk xl xr xL xR < y :=
  pgame.cases_on y
    fun (y_α y_β : Type u_1) (y_ᾰ : y_α → pgame) (y_ᾰ_1 : y_β → pgame) (h : xR i ≤ mk y_α y_β y_ᾰ y_ᾰ_1) =>
      Or.inr (Exists.intro i h)

theorem lt_mk_of_le {x : pgame} {yl : Type u_1} {yr : Type u_1} {yL : yl → pgame} {yR : yr → pgame} {i : yl} : x ≤ yL i → x < mk yl yr yL yR :=
  pgame.cases_on x
    fun (x_α x_β : Type u_1) (x_ᾰ : x_α → pgame) (x_ᾰ_1 : x_β → pgame) (h : mk x_α x_β x_ᾰ x_ᾰ_1 ≤ yL i) =>
      Or.inl (Exists.intro i h)

theorem not_le_lt {x : pgame} {y : pgame} : (¬x ≤ y ↔ y < x) ∧ (¬x < y ↔ y ≤ x) := sorry

theorem not_le {x : pgame} {y : pgame} : ¬x ≤ y ↔ y < x :=
  and.left not_le_lt

theorem not_lt {x : pgame} {y : pgame} : ¬x < y ↔ y ≤ x :=
  and.right not_le_lt

theorem le_refl (x : pgame) : x ≤ x := sorry

theorem lt_irrefl (x : pgame) : ¬x < x :=
  iff.mpr not_lt (le_refl x)

theorem ne_of_lt {x : pgame} {y : pgame} : x < y → x ≠ y := sorry

theorem le_trans_aux {xl : Type u_1} {xr : Type u_1} {xL : xl → pgame} {xR : xr → pgame} {yl : Type u_1} {yr : Type u_1} {yL : yl → pgame} {yR : yr → pgame} {zl : Type u_1} {zr : Type u_1} {zL : zl → pgame} {zR : zr → pgame} (h₁ : ∀ (i : xl), mk yl yr yL yR ≤ mk zl zr zL zR → mk zl zr zL zR ≤ xL i → mk yl yr yL yR ≤ xL i) (h₂ : ∀ (i : zr), zR i ≤ mk xl xr xL xR → mk xl xr xL xR ≤ mk yl yr yL yR → zR i ≤ mk yl yr yL yR) : mk xl xr xL xR ≤ mk yl yr yL yR → mk yl yr yL yR ≤ mk zl zr zL zR → mk xl xr xL xR ≤ mk zl zr zL zR := sorry

theorem le_trans {x : pgame} {y : pgame} {z : pgame} : x ≤ y → y ≤ z → x ≤ z := sorry

theorem lt_of_le_of_lt {x : pgame} {y : pgame} {z : pgame} (hxy : x ≤ y) (hyz : y < z) : x < z :=
  eq.mpr (id (Eq._oldrec (Eq.refl (x < z)) (Eq.symm (propext not_le))))
    (mt (fun (H : z ≤ x) => le_trans H hxy) (eq.mp (Eq._oldrec (Eq.refl (y < z)) (Eq.symm (propext not_le))) hyz))

theorem lt_of_lt_of_le {x : pgame} {y : pgame} {z : pgame} (hxy : x < y) (hyz : y ≤ z) : x < z :=
  eq.mpr (id (Eq._oldrec (Eq.refl (x < z)) (Eq.symm (propext not_le))))
    (mt (fun (H : z ≤ x) => le_trans hyz H) (eq.mp (Eq._oldrec (Eq.refl (x < y)) (Eq.symm (propext not_le))) hxy))

/-- Define the equivalence relation on pre-games. Two pre-games
  `x`, `y` are equivalent if `x ≤ y` and `y ≤ x`. -/
def equiv (x : pgame) (y : pgame) :=
  x ≤ y ∧ y ≤ x

theorem equiv_refl (x : pgame) : equiv x x :=
  { left := le_refl x, right := le_refl x }

theorem equiv_symm {x : pgame} {y : pgame} : equiv x y → equiv y x :=
  fun (ᾰ : equiv x y) =>
    and.dcases_on ᾰ fun (ᾰ_left : x ≤ y) (ᾰ_right : y ≤ x) => idRhs (y ≤ x ∧ x ≤ y) { left := ᾰ_right, right := ᾰ_left }

theorem equiv_trans {x : pgame} {y : pgame} {z : pgame} : equiv x y → equiv y z → equiv x z := sorry

theorem lt_of_lt_of_equiv {x : pgame} {y : pgame} {z : pgame} (h₁ : x < y) (h₂ : equiv y z) : x < z :=
  lt_of_lt_of_le h₁ (and.left h₂)

theorem le_of_le_of_equiv {x : pgame} {y : pgame} {z : pgame} (h₁ : x ≤ y) (h₂ : equiv y z) : x ≤ z :=
  le_trans h₁ (and.left h₂)

theorem lt_of_equiv_of_lt {x : pgame} {y : pgame} {z : pgame} (h₁ : equiv x y) (h₂ : y < z) : x < z :=
  lt_of_le_of_lt (and.left h₁) h₂

theorem le_of_equiv_of_le {x : pgame} {y : pgame} {z : pgame} (h₁ : equiv x y) (h₂ : y ≤ z) : x ≤ z :=
  le_trans (and.left h₁) h₂

theorem le_congr {x₁ : pgame} {y₁ : pgame} {x₂ : pgame} {y₂ : pgame} : equiv x₁ x₂ → equiv y₁ y₂ → (x₁ ≤ y₁ ↔ x₂ ≤ y₂) := sorry

theorem lt_congr {x₁ : pgame} {y₁ : pgame} {x₂ : pgame} {y₂ : pgame} (hx : equiv x₁ x₂) (hy : equiv y₁ y₂) : x₁ < y₁ ↔ x₂ < y₂ :=
  iff.trans (iff.symm not_le) (iff.trans (not_congr (le_congr hy hx)) not_le)

theorem equiv_congr_left {y₁ : pgame} {y₂ : pgame} : equiv y₁ y₂ ↔ ∀ (x₁ : pgame), equiv x₁ y₁ ↔ equiv x₁ y₂ := sorry

theorem equiv_congr_right {x₁ : pgame} {x₂ : pgame} : equiv x₁ x₂ ↔ ∀ (y₁ : pgame), equiv x₁ y₁ ↔ equiv x₂ y₁ := sorry

/-- `restricted x y` says that Left always has no more moves in `x` than in `y`,
     and Right always has no more moves in `y` than in `x` -/
inductive restricted : pgame → pgame → Type (u + 1)
where
| mk : {x y : pgame} →
  (L : left_moves x → left_moves y) →
    (R : right_moves y → right_moves x) →
      ((i : left_moves x) → restricted (move_left x i) (move_left y (L i))) →
        ((j : right_moves y) → restricted (move_right x (R j)) (move_right y j)) → restricted x y

/-- The identity restriction. -/
def restricted.refl (x : pgame) : restricted x x :=
  sorry

-- TODO trans for restricted

theorem le_of_restricted {x : pgame} {y : pgame} (r : restricted x y) : x ≤ y := sorry

/--
`relabelling x y` says that `x` and `y` are really the same game, just dressed up differently.
Specifically, there is a bijection between the moves for Left in `x` and in `y`, and similarly
for Right, and under these bijections we inductively have `relabelling`s for the consequent games.
-/
inductive relabelling : pgame → pgame → Type (u + 1)
where
| mk : {x y : pgame} →
  (L : left_moves x ≃ left_moves y) →
    (R : right_moves x ≃ right_moves y) →
      ((i : left_moves x) → relabelling (move_left x i) (move_left y (coe_fn L i))) →
        ((j : right_moves y) → relabelling (move_right x (coe_fn (equiv.symm R) j)) (move_right y j)) → relabelling x y

/-- If `x` is a relabelling of `y`, then Left and Right have the same moves in either game,
    so `x` is a restriction of `y`. -/
def restricted_of_relabelling {x : pgame} {y : pgame} (r : relabelling x y) : restricted x y :=
  sorry

-- It's not the case that `restricted x y → restricted y x → relabelling x y`,

-- but if we insisted that the maps in a restriction were injective, then one

-- could use Schröder-Bernstein for do this.

/-- The identity relabelling. -/
def relabelling.refl (x : pgame) : relabelling x x :=
  sorry

/-- Reverse a relabelling. -/
def relabelling.symm {x : pgame} {y : pgame} : relabelling x y → relabelling y x :=
  sorry

/-- Transitivity of relabelling -/
def relabelling.trans {x : pgame} {y : pgame} {z : pgame} : relabelling x y → relabelling y z → relabelling x z :=
  sorry

theorem le_of_relabelling {x : pgame} {y : pgame} (r : relabelling x y) : x ≤ y :=
  le_of_restricted (restricted_of_relabelling r)

/-- A relabelling lets us prove equivalence of games. -/
theorem equiv_of_relabelling {x : pgame} {y : pgame} (r : relabelling x y) : equiv x y :=
  { left := le_of_relabelling r, right := le_of_relabelling (relabelling.symm r) }

protected instance equiv.has_coe {x : pgame} {y : pgame} : has_coe (relabelling x y) (equiv x y) :=
  has_coe.mk equiv_of_relabelling

/-- Replace the types indexing the next moves for Left and Right by equivalent types. -/
def relabel {x : pgame} {xl' : Type u_1} {xr' : Type u_1} (el : left_moves x ≃ xl') (er : right_moves x ≃ xr') : pgame :=
  mk xl' xr' (fun (i : xl') => move_left x (coe_fn (equiv.symm el) i))
    fun (j : xr') => move_right x (coe_fn (equiv.symm er) j)

@[simp] theorem relabel_move_left' {x : pgame} {xl' : Type u_1} {xr' : Type u_1} (el : left_moves x ≃ xl') (er : right_moves x ≃ xr') (i : xl') : move_left (relabel el er) i = move_left x (coe_fn (equiv.symm el) i) :=
  rfl

@[simp] theorem relabel_move_left {x : pgame} {xl' : Type u_1} {xr' : Type u_1} (el : left_moves x ≃ xl') (er : right_moves x ≃ xr') (i : left_moves x) : move_left (relabel el er) (coe_fn el i) = move_left x i := sorry

@[simp] theorem relabel_move_right' {x : pgame} {xl' : Type u_1} {xr' : Type u_1} (el : left_moves x ≃ xl') (er : right_moves x ≃ xr') (j : xr') : move_right (relabel el er) j = move_right x (coe_fn (equiv.symm er) j) :=
  rfl

@[simp] theorem relabel_move_right {x : pgame} {xl' : Type u_1} {xr' : Type u_1} (el : left_moves x ≃ xl') (er : right_moves x ≃ xr') (j : right_moves x) : move_right (relabel el er) (coe_fn er j) = move_right x j := sorry

/-- The game obtained by relabelling the next moves is a relabelling of the original game. -/
def relabel_relabelling {x : pgame} {xl' : Type u_1} {xr' : Type u_1} (el : left_moves x ≃ xl') (er : right_moves x ≃ xr') : relabelling x (relabel el er) :=
  relabelling.mk el er (fun (i : left_moves x) => eq.mpr sorry (relabelling.refl (move_left x i)))
    fun (j : right_moves (relabel el er)) => eq.mpr sorry (relabelling.refl (move_right x (coe_fn (equiv.symm er) j)))

/-- The negation of `{L | R}` is `{-R | -L}`. -/
def neg : pgame → pgame :=
  sorry

protected instance has_neg : Neg pgame :=
  { neg := neg }

@[simp] theorem neg_def {xl : Type u_1} {xr : Type u_1} {xL : xl → pgame} {xR : xr → pgame} : -mk xl xr xL xR = mk xr xl (fun (j : xr) => -xR j) fun (i : xl) => -xL i :=
  rfl

@[simp] theorem neg_neg {x : pgame} : --x = x := sorry

@[simp] theorem neg_zero : -0 = 0 := sorry

/-- An explicit equivalence between the moves for Left in `-x` and the moves for Right in `x`. -/
-- This equivalence is useful to avoid having to use `cases` unnecessarily.

def left_moves_neg (x : pgame) : left_moves (-x) ≃ right_moves x :=
  pgame.cases_on x
    fun (x_α x_β : Type u_1) (x_ᾰ : x_α → pgame) (x_ᾰ_1 : x_β → pgame) => equiv.refl (left_moves (-mk x_α x_β x_ᾰ x_ᾰ_1))

/-- An explicit equivalence between the moves for Right in `-x` and the moves for Left in `x`. -/
def right_moves_neg (x : pgame) : right_moves (-x) ≃ left_moves x :=
  pgame.cases_on x
    fun (x_α x_β : Type u_1) (x_ᾰ : x_α → pgame) (x_ᾰ_1 : x_β → pgame) => equiv.refl (right_moves (-mk x_α x_β x_ᾰ x_ᾰ_1))

@[simp] theorem move_right_left_moves_neg {x : pgame} (i : left_moves (-x)) : move_right x (coe_fn (left_moves_neg x) i) = -move_left (-x) i := sorry

@[simp] theorem move_left_left_moves_neg_symm {x : pgame} (i : right_moves x) : move_left (-x) (coe_fn (equiv.symm (left_moves_neg x)) i) = -move_right x i := sorry

@[simp] theorem move_left_right_moves_neg {x : pgame} (i : right_moves (-x)) : move_left x (coe_fn (right_moves_neg x) i) = -move_right (-x) i := sorry

@[simp] theorem move_right_right_moves_neg_symm {x : pgame} (i : left_moves x) : move_right (-x) (coe_fn (equiv.symm (right_moves_neg x)) i) = -move_left x i := sorry

theorem le_iff_neg_ge {x : pgame} {y : pgame} : x ≤ y ↔ -y ≤ -x := sorry

theorem neg_congr {x : pgame} {y : pgame} (h : equiv x y) : equiv (-x) (-y) :=
  { left := iff.mp le_iff_neg_ge (and.right h), right := iff.mp le_iff_neg_ge (and.left h) }

theorem lt_iff_neg_gt {x : pgame} {y : pgame} : x < y ↔ -y < -x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (x < y ↔ -y < -x)) (Eq.symm (propext not_le))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (¬y ≤ x ↔ -y < -x)) (Eq.symm (propext not_le))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (¬y ≤ x ↔ ¬-x ≤ -y)) (propext not_iff_not))) le_iff_neg_ge))

theorem zero_le_iff_neg_le_zero {x : pgame} : 0 ≤ x ↔ -x ≤ 0 := sorry

theorem le_zero_iff_zero_le_neg {x : pgame} : x ≤ 0 ↔ 0 ≤ -x := sorry

/-- The sum of `x = {xL | xR}` and `y = {yL | yR}` is `{xL + y, x + yL | xR + y, x + yR}`. -/
def add (x : pgame) (y : pgame) : pgame :=
  pgame.rec
    (fun (xl xr : Type u_1) (xL : xl → pgame) (xR : xr → pgame)
      (IHxl : (ᾰ : xl) → (fun (x : pgame) => pgame → pgame) (xL ᾰ))
      (IHxr : (ᾰ : xr) → (fun (x : pgame) => pgame → pgame) (xR ᾰ)) (y : pgame) =>
      pgame.rec
        (fun (yl yr : Type u_2) (yL : yl → pgame) (yR : yr → pgame) (IHyl : (ᾰ : yl) → (fun (y : pgame) => pgame) (yL ᾰ))
          (IHyr : (ᾰ : yr) → (fun (y : pgame) => pgame) (yR ᾰ)) =>
          mk (xl ⊕ yl) (xr ⊕ yr) (sum.rec (fun (i : xl) => IHxl i (mk yl yr yL yR)) fun (i : yl) => IHyl i)
            (sum.rec (fun (i : xr) => IHxr i (mk yl yr yL yR)) fun (i : yr) => IHyr i))
        y)
    x y

protected instance has_add : Add pgame :=
  { add := add }

/-- `x + 0` has exactly the same moves as `x`. -/
def add_zero_relabelling (x : pgame) : relabelling (x + 0) x :=
  sorry

/-- `x + 0` is equivalent to `x`. -/
theorem add_zero_equiv (x : pgame) : equiv (x + 0) x :=
  equiv_of_relabelling (add_zero_relabelling x)

/-- `0 + x` has exactly the same moves as `x`. -/
def zero_add_relabelling (x : pgame) : relabelling (0 + x) x :=
  sorry

/-- `0 + x` is equivalent to `x`. -/
theorem zero_add_equiv (x : pgame) : equiv (0 + x) x :=
  equiv_of_relabelling (zero_add_relabelling x)

/-- An explicit equivalence between the moves for Left in `x + y` and the type-theory sum
    of the moves for Left in `x` and in `y`. -/
def left_moves_add (x : pgame) (y : pgame) : left_moves (x + y) ≃ left_moves x ⊕ left_moves y :=
  pgame.cases_on x
    fun (x_α x_β : Type u_1) (x_ᾰ : x_α → pgame) (x_ᾰ_1 : x_β → pgame) =>
      pgame.cases_on y
        fun (y_α y_β : Type u_1) (y_ᾰ : y_α → pgame) (y_ᾰ_1 : y_β → pgame) =>
          equiv.refl (left_moves (mk x_α x_β x_ᾰ x_ᾰ_1 + mk y_α y_β y_ᾰ y_ᾰ_1))

/-- An explicit equivalence between the moves for Right in `x + y` and the type-theory sum
    of the moves for Right in `x` and in `y`. -/
def right_moves_add (x : pgame) (y : pgame) : right_moves (x + y) ≃ right_moves x ⊕ right_moves y :=
  pgame.cases_on x
    fun (x_α x_β : Type u_1) (x_ᾰ : x_α → pgame) (x_ᾰ_1 : x_β → pgame) =>
      pgame.cases_on y
        fun (y_α y_β : Type u_1) (y_ᾰ : y_α → pgame) (y_ᾰ_1 : y_β → pgame) =>
          equiv.refl (right_moves (mk x_α x_β x_ᾰ x_ᾰ_1 + mk y_α y_β y_ᾰ y_ᾰ_1))

@[simp] theorem mk_add_move_left_inl {xl : Type u_1} {xr : Type u_1} {yl : Type u_1} {yr : Type u_1} {xL : xl → pgame} {xR : xr → pgame} {yL : yl → pgame} {yR : yr → pgame} {i : xl} : move_left (mk xl xr xL xR + mk yl yr yL yR) (sum.inl i) = move_left (mk xl xr xL xR) i + mk yl yr yL yR :=
  rfl

@[simp] theorem add_move_left_inl {x : pgame} {y : pgame} {i : left_moves x} : move_left (x + y) (coe_fn (equiv.symm (left_moves_add x y)) (sum.inl i)) = move_left x i + y := sorry

@[simp] theorem mk_add_move_right_inl {xl : Type u_1} {xr : Type u_1} {yl : Type u_1} {yr : Type u_1} {xL : xl → pgame} {xR : xr → pgame} {yL : yl → pgame} {yR : yr → pgame} {i : xr} : move_right (mk xl xr xL xR + mk yl yr yL yR) (sum.inl i) = move_right (mk xl xr xL xR) i + mk yl yr yL yR :=
  rfl

@[simp] theorem add_move_right_inl {x : pgame} {y : pgame} {i : right_moves x} : move_right (x + y) (coe_fn (equiv.symm (right_moves_add x y)) (sum.inl i)) = move_right x i + y := sorry

@[simp] theorem mk_add_move_left_inr {xl : Type u_1} {xr : Type u_1} {yl : Type u_1} {yr : Type u_1} {xL : xl → pgame} {xR : xr → pgame} {yL : yl → pgame} {yR : yr → pgame} {i : yl} : move_left (mk xl xr xL xR + mk yl yr yL yR) (sum.inr i) = mk xl xr xL xR + move_left (mk yl yr yL yR) i :=
  rfl

@[simp] theorem add_move_left_inr {x : pgame} {y : pgame} {i : left_moves y} : move_left (x + y) (coe_fn (equiv.symm (left_moves_add x y)) (sum.inr i)) = x + move_left y i := sorry

@[simp] theorem mk_add_move_right_inr {xl : Type u_1} {xr : Type u_1} {yl : Type u_1} {yr : Type u_1} {xL : xl → pgame} {xR : xr → pgame} {yL : yl → pgame} {yR : yr → pgame} {i : yr} : move_right (mk xl xr xL xR + mk yl yr yL yR) (sum.inr i) = mk xl xr xL xR + move_right (mk yl yr yL yR) i :=
  rfl

@[simp] theorem add_move_right_inr {x : pgame} {y : pgame} {i : right_moves y} : move_right (x + y) (coe_fn (equiv.symm (right_moves_add x y)) (sum.inr i)) = x + move_right y i := sorry

protected instance has_sub : Sub pgame :=
  { sub := fun (x y : pgame) => x + -y }

/-- `-(x+y)` has exactly the same moves as `-x + -y`. -/
def neg_add_relabelling (x : pgame) (y : pgame) : relabelling (-(x + y)) (-x + -y) :=
  sorry

theorem neg_add_le {x : pgame} {y : pgame} : -(x + y) ≤ -x + -y :=
  le_of_relabelling (neg_add_relabelling x y)

/-- `x+y` has exactly the same moves as `y+x`. -/
def add_comm_relabelling (x : pgame) (y : pgame) : relabelling (x + y) (y + x) :=
  sorry

theorem add_comm_le {x : pgame} {y : pgame} : x + y ≤ y + x :=
  le_of_relabelling (add_comm_relabelling x y)

theorem add_comm_equiv {x : pgame} {y : pgame} : equiv (x + y) (y + x) :=
  equiv_of_relabelling (add_comm_relabelling x y)

/-- `(x + y) + z` has exactly the same moves as `x + (y + z)`. -/
def add_assoc_relabelling (x : pgame) (y : pgame) (z : pgame) : relabelling (x + y + z) (x + (y + z)) :=
  sorry

theorem add_assoc_equiv {x : pgame} {y : pgame} {z : pgame} : equiv (x + y + z) (x + (y + z)) :=
  equiv_of_relabelling (add_assoc_relabelling x y z)

theorem add_le_add_right {x : pgame} {y : pgame} {z : pgame} (h : x ≤ y) : x + z ≤ y + z := sorry

theorem add_le_add_left {x : pgame} {y : pgame} {z : pgame} (h : y ≤ z) : x + y ≤ x + z :=
  le_trans (le_trans add_comm_le (add_le_add_right h)) add_comm_le

theorem add_congr {w : pgame} {x : pgame} {y : pgame} {z : pgame} (h₁ : equiv w x) (h₂ : equiv y z) : equiv (w + y) (x + z) :=
  { left := le_trans (add_le_add_left (and.left h₂)) (add_le_add_right (and.left h₁)),
    right := le_trans (add_le_add_left (and.right h₂)) (add_le_add_right (and.right h₁)) }

theorem add_left_neg_le_zero {x : pgame} : -x + x ≤ 0 := sorry

theorem zero_le_add_left_neg {x : pgame} : 0 ≤ -x + x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (0 ≤ -x + x)) (propext le_iff_neg_ge)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (-(-x + x) ≤ -0)) neg_zero)) (le_trans neg_add_le add_left_neg_le_zero))

theorem add_left_neg_equiv {x : pgame} : equiv (-x + x) 0 :=
  { left := add_left_neg_le_zero, right := zero_le_add_left_neg }

theorem add_right_neg_le_zero {x : pgame} : x + -x ≤ 0 :=
  le_trans add_comm_le add_left_neg_le_zero

theorem zero_le_add_right_neg {x : pgame} : 0 ≤ x + -x :=
  le_trans zero_le_add_left_neg add_comm_le

theorem add_lt_add_right {x : pgame} {y : pgame} {z : pgame} (h : x < y) : x + z < y + z := sorry

theorem add_lt_add_left {x : pgame} {y : pgame} {z : pgame} (h : y < z) : x + y < x + z :=
  lt_of_lt_of_le (lt_of_le_of_lt add_comm_le (add_lt_add_right h)) add_comm_le

theorem le_iff_sub_nonneg {x : pgame} {y : pgame} : x ≤ y ↔ 0 ≤ y - x := sorry

theorem lt_iff_sub_pos {x : pgame} {y : pgame} : x < y ↔ 0 < y - x := sorry

/-- The pre-game `star`, which is fuzzy/confused with zero. -/
def star : pgame :=
  of_lists [0] [0]

theorem star_lt_zero : star < 0 := sorry

theorem zero_lt_star : 0 < star := sorry

/-- The pre-game `ω`. (In fact all ordinals have game and surreal representatives.) -/
def omega : pgame :=
  mk (ulift ℕ) pempty (fun (n : ulift ℕ) => ↑(ulift.down n)) pempty.elim

