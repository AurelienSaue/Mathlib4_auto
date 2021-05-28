/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.set_theory.pgame
import Mathlib.PostPort

universes u_1 u_2 u l u_3 

namespace Mathlib

/-!
# Surreal numbers

The basic theory of surreal numbers, built on top of the theory of combinatorial (pre-)games.

A pregame is `numeric` if all the Left options are strictly smaller than all the Right options, and
all those options are themselves numeric. In terms of combinatorial games, the numeric games have
"frozen"; you can only make your position worse by playing, and Left is some definite "number" of
moves ahead (or behind) Right.

A surreal number is an equivalence class of numeric pregames.

In fact, the surreals form a complete ordered field, containing a copy of the reals (and much else
besides!) but we do not yet have a complete development.

## Order properties
Surreal numbers inherit the relations `≤` and `<` from games, and these relations satisfy the axioms
of a partial order (recall that `x < y ↔ x ≤ y ∧ ¬ y ≤ x` did not hold for games).

## Algebraic operations
At this point, we have defined addition and negation (from pregames), and shown that surreals form
an additive semigroup. It would be very little work to finish showing that the surreals form an
ordered commutative group.

We define the operations of multiplication and inverse on surreals, but do not yet establish any of
the necessary properties to show the surreals form an ordered field.

## Embeddings
It would be nice projects to define the group homomorphism `surreal → game`, and also `ℤ → surreal`,
and then the homomorphic inclusion of the dyadic rationals into surreals, and finally
via dyadic Dedekind cuts the homomorphic inclusion of the reals into the surreals.

One can also map all the ordinals into the surreals!

## References
* [Conway, *On numbers and games*][conway2001]
-/

namespace pgame


/-! Multiplicative operations can be defined at the level of pre-games, but as
they are only useful on surreal numbers, we define them here. -/

/-- The product of `x = {xL | xR}` and `y = {yL | yR}` is
`{xL*y + x*yL - xL*yL, xR*y + x*yR - xR*yR | xL*y + x*yR - xL*yR, x*yL + xR*y - xR*yL }`. -/
def mul (x : pgame) (y : pgame) : pgame := sorry

protected instance has_mul : Mul pgame :=
  { mul := mul }

/-- Because the two halves of the definition of `inv` produce more elements
of each side, we have to define the two families inductively.
This is the indexing set for the function, and `inv_val` is the function part. -/
inductive inv_ty (l : Type u) (r : Type u) : Bool → Type u
where
| zero : inv_ty l r false
| left₁ : r → inv_ty l r false → inv_ty l r false
| left₂ : l → inv_ty l r tt → inv_ty l r false
| right₁ : l → inv_ty l r false → inv_ty l r tt
| right₂ : r → inv_ty l r tt → inv_ty l r tt

/-- Because the two halves of the definition of `inv` produce more elements
of each side, we have to define the two families inductively.
This is the function part, defined by recursion on `inv_ty`. -/
def inv_val {l : Type u_1} {r : Type u_1} (L : l → pgame) (R : r → pgame) (IHl : l → pgame) (IHr : r → pgame) {b : Bool} : inv_ty l r b → pgame :=
  sorry

/-- The inverse of a positive surreal number `x = {L | R}` is
given by `x⁻¹ = {0,
  (1 + (R - x) * x⁻¹L) * R, (1 + (L - x) * x⁻¹R) * L |
  (1 + (L - x) * x⁻¹L) * L, (1 + (R - x) * x⁻¹R) * R}`.
Because the two halves `x⁻¹L, x⁻¹R` of `x⁻¹` are used in their own
definition, the sets and elements are inductively generated. -/
def inv' : pgame → pgame :=
  sorry

/-- The inverse of a surreal number in terms of the inverse on positive surreals. -/
def inv (x : pgame) : pgame :=
  ite (x = 0) 0 (ite (0 < x) (inv' x) (inv' (-x)))

protected instance has_inv : has_inv pgame :=
  has_inv.mk inv

protected instance has_div : Div pgame :=
  { div := fun (x y : pgame) => x * (y⁻¹) }

/-- A pre-game is numeric if everything in the L set is less than everything in the R set,
and all the elements of L and R are also numeric. -/
def numeric : pgame → Prop :=
  sorry

theorem numeric.move_left {x : pgame} (o : numeric x) (i : left_moves x) : numeric (move_left x i) := sorry

theorem numeric.move_right {x : pgame} (o : numeric x) (j : right_moves x) : numeric (move_right x j) := sorry

theorem numeric_rec {C : pgame → Prop} (H : ∀ (l r : Type u_1) (L : l → pgame) (R : r → pgame),
  (∀ (i : l) (j : r), L i < R j) →
    (∀ (i : l), numeric (L i)) →
      (∀ (i : r), numeric (R i)) → (∀ (i : l), C (L i)) → (∀ (i : r), C (R i)) → C (mk l r L R)) (x : pgame) : numeric x → C x := sorry

theorem lt_asymm {x : pgame} {y : pgame} (ox : numeric x) (oy : numeric y) : x < y → ¬y < x := sorry

theorem le_of_lt {x : pgame} {y : pgame} (ox : numeric x) (oy : numeric y) (h : x < y) : x ≤ y :=
  iff.mp not_lt (lt_asymm ox oy h)

/-- On numeric pre-games, `<` and `≤` satisfy the axioms of a partial order (even though they
don't on all pre-games). -/
theorem lt_iff_le_not_le {x : pgame} {y : pgame} (ox : numeric x) (oy : numeric y) : x < y ↔ x ≤ y ∧ ¬y ≤ x :=
  { mp := fun (h : x < y) => { left := le_of_lt ox oy h, right := iff.mpr not_le h },
    mpr := fun (h : x ≤ y ∧ ¬y ≤ x) => iff.mp not_le (and.right h) }

theorem numeric_zero : numeric 0 := sorry

theorem numeric_one : numeric 1 := sorry

theorem numeric_neg {x : pgame} (o : numeric x) : numeric (-x) := sorry

theorem numeric.move_left_lt {x : pgame} (o : numeric x) (i : left_moves x) : move_left x i < x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (move_left x i < x)) (propext lt_def_le)))
    (Or.inl (Exists.intro i (id (le_refl (move_left x i)))))

theorem numeric.move_left_le {x : pgame} (o : numeric x) (i : left_moves x) : move_left x i ≤ x :=
  le_of_lt (numeric.move_left o i) o (numeric.move_left_lt o i)

theorem numeric.lt_move_right {x : pgame} (o : numeric x) (j : right_moves x) : x < move_right x j :=
  eq.mpr (id (Eq._oldrec (Eq.refl (x < move_right x j)) (propext lt_def_le)))
    (Or.inr (Exists.intro j (id (le_refl (move_right x j)))))

theorem numeric.le_move_right {x : pgame} (o : numeric x) (j : right_moves x) : x ≤ move_right x j :=
  le_of_lt o (numeric.move_right o j) (numeric.lt_move_right o j)

theorem add_lt_add {w : pgame} {x : pgame} {y : pgame} {z : pgame} (ow : numeric w) (ox : numeric x) (oy : numeric y) (oz : numeric z) (hwx : w < x) (hyz : y < z) : w + y < x + z := sorry

theorem numeric_add {x : pgame} {y : pgame} (ox : numeric x) (oy : numeric y) : numeric (x + y) := sorry

-- TODO prove

-- theorem numeric_nat (n : ℕ) : numeric n := sorry

-- theorem numeric_omega : numeric omega := sorry

end pgame


/-- The equivalence on numeric pre-games. -/
def surreal.equiv (x : Subtype fun (x : pgame) => pgame.numeric x) (y : Subtype fun (x : pgame) => pgame.numeric x)  :=
  pgame.equiv (subtype.val x) (subtype.val y)

protected instance surreal.setoid : setoid (Subtype fun (x : pgame) => pgame.numeric x) :=
  setoid.mk (fun (x y : Subtype fun (x : pgame) => pgame.numeric x) => pgame.equiv (subtype.val x) (subtype.val y)) sorry

/-- The type of surreal numbers. These are the numeric pre-games quotiented
by the equivalence relation `x ≈ y ↔ x ≤ y ∧ y ≤ x`. In the quotient,
the order becomes a total order. -/
def surreal  :=
  quotient sorry

namespace surreal


/-- Construct a surreal number from a numeric pre-game. -/
def mk (x : pgame) (h : pgame.numeric x) : surreal :=
  quotient.mk { val := x, property := h }

protected instance has_zero : HasZero surreal :=
  { zero := quotient.mk { val := 0, property := pgame.numeric_zero } }

protected instance has_one : HasOne surreal :=
  { one := quotient.mk { val := 1, property := pgame.numeric_one } }

protected instance inhabited : Inhabited surreal :=
  { default := 0 }

/-- Lift an equivalence-respecting function on pre-games to surreals. -/
def lift {α : Sort u_1} (f : (x : pgame) → pgame.numeric x → α) (H : ∀ {x y : pgame} (hx : pgame.numeric x) (hy : pgame.numeric y), pgame.equiv x y → f x hx = f y hy) : surreal → α :=
  quotient.lift (fun (x : Subtype fun (x : pgame) => pgame.numeric x) => f (subtype.val x) sorry) sorry

/-- Lift a binary equivalence-respecting function on pre-games to surreals. -/
def lift₂ {α : Sort u_1} (f : (x : pgame) → (y : pgame) → pgame.numeric x → pgame.numeric y → α) (H : ∀ {x₁ : pgame} {y₁ : pgame} {x₂ : pgame} {y₂ : pgame} (ox₁ : pgame.numeric x₁) (oy₁ : pgame.numeric y₁)
  (ox₂ : pgame.numeric x₂) (oy₂ : pgame.numeric y₂),
  pgame.equiv x₁ x₂ → pgame.equiv y₁ y₂ → f x₁ y₁ ox₁ oy₁ = f x₂ y₂ ox₂ oy₂) : surreal → surreal → α :=
  lift (fun (x : pgame) (ox : pgame.numeric x) => lift (fun (y : pgame) (oy : pgame.numeric y) => f x y ox oy) sorry)
    sorry

/-- The relation `x ≤ y` on surreals. -/
def le : surreal → surreal → Prop :=
  lift₂ (fun (x y : pgame) (_x : pgame.numeric x) (_x : pgame.numeric y) => x ≤ y) sorry

/-- The relation `x < y` on surreals. -/
def lt : surreal → surreal → Prop :=
  lift₂ (fun (x y : pgame) (_x : pgame.numeric x) (_x : pgame.numeric y) => x < y) sorry

theorem not_le {x : surreal} {y : surreal} : ¬le x y ↔ lt y x := sorry

protected instance preorder : preorder surreal :=
  preorder.mk le lt sorry sorry

protected instance partial_order : partial_order surreal :=
  partial_order.mk preorder.le preorder.lt preorder.le_refl preorder.le_trans sorry

protected instance linear_order : linear_order surreal :=
  linear_order.mk partial_order.le partial_order.lt partial_order.le_refl partial_order.le_trans partial_order.le_antisymm
    sorry (classical.dec_rel LessEq) Mathlib.decidable_eq_of_decidable_le Mathlib.decidable_lt_of_decidable_le

/-- Addition on surreals is inherited from pre-game addition:
the sum of `x = {xL | xR}` and `y = {yL | yR}` is `{xL + y, x + yL | xR + y, x + yR}`. -/
def add : surreal → surreal → surreal :=
  lift₂
    (fun (x y : pgame) (ox : pgame.numeric x) (oy : pgame.numeric y) =>
      quotient.mk { val := x + y, property := pgame.numeric_add ox oy })
    sorry

protected instance has_add : Add surreal :=
  { add := add }

theorem add_assoc (x : surreal) (y : surreal) (z : surreal) : x + y + z = x + (y + z) := sorry

protected instance add_semigroup : add_semigroup surreal :=
  add_semigroup.mk Add.add add_assoc

