/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.linear_ordered_comm_group_with_zero
import Mathlib.algebra.big_operators.ring
import Mathlib.data.real.basic
import Mathlib.data.indicator_function
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Nonnegative real numbers

In this file we define `nnreal` (notation: `ℝ≥0`) to be the type of non-negative real numbers,
a.k.a. the interval `[0, ∞)`. We also define the following operations and structures on `ℝ≥0`:

* the order on `ℝ≥0` is the restriction of the order on `ℝ`; these relations define a conditionally
  complete linear order with a bottom element, `conditionally_complete_linear_order_bot`;

* `a + b` and `a * b` are the restrictions of addition and multiplication of real numbers to `ℝ≥0`;
  these operations together with `0 = ⟨0, _⟩` and `1 = ⟨1, _⟩` turn `ℝ≥0` into a linear ordered
  archimedean commutative semifield; we have no typeclass for this in `mathlib` yet, so we define
  the following instances instead:

  - `linear_ordered_semiring ℝ≥0`;
  - `comm_semiring ℝ≥0`;
  - `canonically_ordered_comm_semiring ℝ≥0`;
  - `linear_ordered_comm_group_with_zero ℝ≥0`;
  - `archimedean ℝ≥0`.

* `nnreal.of_real x` is defined as `⟨max x 0, _⟩`, i.e. `↑(nnreal.of_real x) = x` when `0 ≤ x` and
  `↑(nnreal.of_real x) = 0` otherwise.

We also define an instance `can_lift ℝ ℝ≥0`. This instance can be used by the `lift` tactic to
replace `x : ℝ` and `hx : 0 ≤ x` in the proof context with `x : ℝ≥0` while replacing all occurences
of `x` with `↑x`. This tactic also works for a function `f : α → ℝ` with a hypothesis
`hf : ∀ x, 0 ≤ f x`.

## Notations

This file defines `ℝ≥0` as a localized notation for `nnreal`.
-/

/-- Nonnegative real numbers. -/
def nnreal := Subtype fun (r : ℝ) => 0 ≤ r

namespace nnreal


protected instance real.has_coe : has_coe nnreal ℝ := has_coe.mk subtype.val

/- Simp lemma to put back `n.val` into the normal form given by the coercion. -/

@[simp] theorem val_eq_coe (n : nnreal) : subtype.val n = ↑n := rfl

protected instance can_lift : can_lift ℝ nnreal := can_lift.mk coe (fun (r : ℝ) => 0 ≤ r) sorry

protected theorem eq {n : nnreal} {m : nnreal} : ↑n = ↑m → n = m := subtype.eq

protected theorem eq_iff {n : nnreal} {m : nnreal} : ↑n = ↑m ↔ n = m :=
  { mp := nnreal.eq, mpr := congr_arg coe }

theorem ne_iff {x : nnreal} {y : nnreal} : ↑x ≠ ↑y ↔ x ≠ y := not_iff_not_of_iff nnreal.eq_iff

/-- Reinterpret a real number `r` as a non-negative real number. Returns `0` if `r < 0`. -/
protected def of_real (r : ℝ) : nnreal := { val := max r 0, property := sorry }

theorem coe_of_real (r : ℝ) (hr : 0 ≤ r) : ↑(nnreal.of_real r) = r := max_eq_left hr

theorem le_coe_of_real (r : ℝ) : r ≤ ↑(nnreal.of_real r) := le_max_left r 0

theorem coe_nonneg (r : nnreal) : 0 ≤ ↑r := subtype.property r

theorem coe_mk (a : ℝ) (ha : 0 ≤ a) : ↑{ val := a, property := ha } = a := rfl

protected instance has_zero : HasZero nnreal := { zero := { val := 0, property := sorry } }

protected instance has_one : HasOne nnreal := { one := { val := 1, property := zero_le_one } }

protected instance has_add : Add nnreal :=
  { add := fun (a b : nnreal) => { val := ↑a + ↑b, property := sorry } }

protected instance has_sub : Sub nnreal := { sub := fun (a b : nnreal) => nnreal.of_real (↑a - ↑b) }

protected instance has_mul : Mul nnreal :=
  { mul := fun (a b : nnreal) => { val := ↑a * ↑b, property := sorry } }

protected instance has_inv : has_inv nnreal :=
  has_inv.mk fun (a : nnreal) => { val := subtype.val a⁻¹, property := sorry }

protected instance has_le : HasLessEq nnreal := { LessEq := fun (r s : nnreal) => ↑r ≤ ↑s }

protected instance has_bot : has_bot nnreal := has_bot.mk 0

protected instance inhabited : Inhabited nnreal := { default := 0 }

protected theorem injective_coe : function.injective coe := subtype.coe_injective

@[simp] protected theorem coe_eq {r₁ : nnreal} {r₂ : nnreal} : ↑r₁ = ↑r₂ ↔ r₁ = r₂ :=
  function.injective.eq_iff nnreal.injective_coe

@[simp] protected theorem coe_zero : ↑0 = 0 := rfl

@[simp] protected theorem coe_one : ↑1 = 1 := rfl

@[simp] protected theorem coe_add (r₁ : nnreal) (r₂ : nnreal) : ↑(r₁ + r₂) = ↑r₁ + ↑r₂ := rfl

@[simp] protected theorem coe_mul (r₁ : nnreal) (r₂ : nnreal) : ↑(r₁ * r₂) = ↑r₁ * ↑r₂ := rfl

@[simp] protected theorem coe_inv (r : nnreal) : ↑(r⁻¹) = (↑r⁻¹) := rfl

@[simp] protected theorem coe_bit0 (r : nnreal) : ↑(bit0 r) = bit0 ↑r := rfl

@[simp] protected theorem coe_bit1 (r : nnreal) : ↑(bit1 r) = bit1 ↑r := rfl

@[simp] protected theorem coe_sub {r₁ : nnreal} {r₂ : nnreal} (h : r₂ ≤ r₁) :
    ↑(r₁ - r₂) = ↑r₁ - ↑r₂ :=
  sorry

-- TODO: setup semifield!

@[simp] protected theorem coe_eq_zero (r : nnreal) : ↑r = 0 ↔ r = 0 := sorry

theorem coe_ne_zero {r : nnreal} : ↑r ≠ 0 ↔ r ≠ 0 := sorry

protected instance comm_semiring : comm_semiring nnreal :=
  comm_semiring.mk Add.add sorry 0 sorry sorry sorry Mul.mul sorry 1 sorry sorry sorry sorry sorry
    sorry sorry

/-- Coercion `ℝ≥0 → ℝ` as a `ring_hom`. -/
def to_real_hom : nnreal →+* ℝ :=
  ring_hom.mk coe nnreal.coe_one nnreal.coe_mul nnreal.coe_zero nnreal.coe_add

@[simp] theorem coe_to_real_hom : ⇑to_real_hom = coe := rfl

protected instance comm_group_with_zero : comm_group_with_zero nnreal :=
  comm_group_with_zero.mk comm_semiring.mul comm_semiring.mul_assoc comm_semiring.one
    comm_semiring.one_mul comm_semiring.mul_one comm_semiring.mul_comm comm_semiring.zero
    comm_semiring.zero_mul comm_semiring.mul_zero has_inv.inv
    (group_with_zero.div._default comm_semiring.mul comm_semiring.mul_assoc comm_semiring.one
      comm_semiring.one_mul comm_semiring.mul_one has_inv.inv)
    sorry sorry sorry

@[simp] theorem coe_indicator {α : Type u_1} (s : set α) (f : α → nnreal) (a : α) :
    ↑(set.indicator s f a) = set.indicator s (fun (x : α) => ↑(f x)) a :=
  add_monoid_hom.map_indicator (↑to_real_hom) s f a

@[simp] protected theorem coe_div (r₁ : nnreal) (r₂ : nnreal) : ↑(r₁ / r₂) = ↑r₁ / ↑r₂ := rfl

@[simp] theorem coe_pow (r : nnreal) (n : ℕ) : ↑(r ^ n) = ↑r ^ n := ring_hom.map_pow to_real_hom r n

theorem coe_list_sum (l : List nnreal) : ↑(list.sum l) = list.sum (list.map coe l) :=
  ring_hom.map_list_sum to_real_hom l

theorem coe_list_prod (l : List nnreal) : ↑(list.prod l) = list.prod (list.map coe l) :=
  ring_hom.map_list_prod to_real_hom l

theorem coe_multiset_sum (s : multiset nnreal) :
    ↑(multiset.sum s) = multiset.sum (multiset.map coe s) :=
  ring_hom.map_multiset_sum to_real_hom s

theorem coe_multiset_prod (s : multiset nnreal) :
    ↑(multiset.prod s) = multiset.prod (multiset.map coe s) :=
  ring_hom.map_multiset_prod to_real_hom s

theorem coe_sum {α : Type u_1} {s : finset α} {f : α → nnreal} :
    ↑(finset.sum s fun (a : α) => f a) = finset.sum s fun (a : α) => ↑(f a) :=
  ring_hom.map_sum to_real_hom (fun (a : α) => f a) s

theorem of_real_sum_of_nonneg {α : Type u_1} {s : finset α} {f : α → ℝ}
    (hf : ∀ (a : α), a ∈ s → 0 ≤ f a) :
    nnreal.of_real (finset.sum s fun (a : α) => f a) =
        finset.sum s fun (a : α) => nnreal.of_real (f a) :=
  sorry

theorem coe_prod {α : Type u_1} {s : finset α} {f : α → nnreal} :
    ↑(finset.prod s fun (a : α) => f a) = finset.prod s fun (a : α) => ↑(f a) :=
  ring_hom.map_prod to_real_hom (fun (a : α) => f a) s

theorem of_real_prod_of_nonneg {α : Type u_1} {s : finset α} {f : α → ℝ}
    (hf : ∀ (a : α), a ∈ s → 0 ≤ f a) :
    nnreal.of_real (finset.prod s fun (a : α) => f a) =
        finset.prod s fun (a : α) => nnreal.of_real (f a) :=
  sorry

theorem nsmul_coe (r : nnreal) (n : ℕ) : ↑(n •ℕ r) = n •ℕ ↑r :=
  add_monoid_hom.map_nsmul (ring_hom.to_add_monoid_hom to_real_hom) r n

@[simp] protected theorem coe_nat_cast (n : ℕ) : ↑↑n = ↑n := ring_hom.map_nat_cast to_real_hom n

protected instance linear_order : linear_order nnreal := linear_order.lift coe nnreal.injective_coe

@[simp] protected theorem coe_le_coe {r₁ : nnreal} {r₂ : nnreal} : ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂ := iff.rfl

@[simp] protected theorem coe_lt_coe {r₁ : nnreal} {r₂ : nnreal} : ↑r₁ < ↑r₂ ↔ r₁ < r₂ := iff.rfl

@[simp] protected theorem coe_pos {r : nnreal} : 0 < ↑r ↔ 0 < r := iff.rfl

protected theorem coe_mono : monotone coe := fun (_x _x_1 : nnreal) => iff.mpr nnreal.coe_le_coe

protected theorem of_real_mono : monotone nnreal.of_real :=
  fun (x y : ℝ) (h : x ≤ y) => max_le_max h (le_refl 0)

@[simp] theorem of_real_coe {r : nnreal} : nnreal.of_real ↑r = r :=
  nnreal.eq (max_eq_left (subtype.property r))

@[simp] theorem mk_coe_nat (n : ℕ) : { val := ↑n, property := nat.cast_nonneg n } = ↑n :=
  nnreal.eq (Eq.symm (nnreal.coe_nat_cast n))

@[simp] theorem of_real_coe_nat (n : ℕ) : nnreal.of_real ↑n = ↑n := sorry

/-- `nnreal.of_real` and `coe : ℝ≥0 → ℝ` form a Galois insertion. -/
protected def gi : galois_insertion nnreal.of_real coe :=
  galois_insertion.monotone_intro nnreal.coe_mono nnreal.of_real_mono le_coe_of_real sorry

protected instance order_bot : order_bot nnreal :=
  order_bot.mk ⊥ linear_order.le linear_order.lt linear_order.le_refl linear_order.le_trans
    linear_order.le_antisymm sorry

protected instance canonically_ordered_add_monoid : canonically_ordered_add_monoid nnreal :=
  canonically_ordered_add_monoid.mk comm_semiring.add comm_semiring.add_assoc comm_semiring.zero
    comm_semiring.zero_add comm_semiring.add_zero comm_semiring.add_comm order_bot.le order_bot.lt
    order_bot.le_refl order_bot.le_trans order_bot.le_antisymm sorry sorry order_bot.bot
    order_bot.bot_le sorry

protected instance distrib_lattice : distrib_lattice nnreal :=
  Mathlib.distrib_lattice_of_linear_order

protected instance semilattice_inf_bot : semilattice_inf_bot nnreal :=
  semilattice_inf_bot.mk order_bot.bot order_bot.le order_bot.lt order_bot.le_refl
    order_bot.le_trans order_bot.le_antisymm order_bot.bot_le distrib_lattice.inf
    distrib_lattice.inf_le_left distrib_lattice.inf_le_right distrib_lattice.le_inf

protected instance semilattice_sup_bot : semilattice_sup_bot nnreal :=
  semilattice_sup_bot.mk order_bot.bot order_bot.le order_bot.lt order_bot.le_refl
    order_bot.le_trans order_bot.le_antisymm order_bot.bot_le distrib_lattice.sup
    distrib_lattice.le_sup_left distrib_lattice.le_sup_right distrib_lattice.sup_le

protected instance linear_ordered_semiring : linear_ordered_semiring nnreal :=
  linear_ordered_semiring.mk canonically_ordered_add_monoid.add
    canonically_ordered_add_monoid.add_assoc canonically_ordered_add_monoid.zero
    canonically_ordered_add_monoid.zero_add canonically_ordered_add_monoid.add_zero
    canonically_ordered_add_monoid.add_comm comm_semiring.mul comm_semiring.mul_assoc
    comm_semiring.one comm_semiring.one_mul comm_semiring.mul_one comm_semiring.zero_mul
    comm_semiring.mul_zero comm_semiring.left_distrib comm_semiring.right_distrib sorry sorry
    linear_order.le linear_order.lt linear_order.le_refl linear_order.le_trans
    linear_order.le_antisymm canonically_ordered_add_monoid.add_le_add_left sorry zero_le_one sorry
    sorry linear_order.le_total linear_order.decidable_le linear_order.decidable_eq
    linear_order.decidable_lt sorry

protected instance linear_ordered_comm_group_with_zero :
    linear_ordered_comm_group_with_zero nnreal :=
  linear_ordered_comm_group_with_zero.mk linear_ordered_semiring.le linear_ordered_semiring.lt
    linear_ordered_semiring.le_refl linear_ordered_semiring.le_trans
    linear_ordered_semiring.le_antisymm linear_ordered_semiring.le_total
    linear_ordered_semiring.decidable_le linear_ordered_semiring.decidable_eq
    linear_ordered_semiring.decidable_lt linear_ordered_semiring.mul
    linear_ordered_semiring.mul_assoc linear_ordered_semiring.one linear_ordered_semiring.one_mul
    linear_ordered_semiring.mul_one comm_group_with_zero.mul_comm linear_ordered_semiring.zero
    linear_ordered_semiring.zero_mul linear_ordered_semiring.mul_zero sorry sorry sorry
    comm_group_with_zero.inv comm_group_with_zero.div linear_ordered_semiring.exists_pair_ne
    comm_group_with_zero.inv_zero comm_group_with_zero.mul_inv_cancel

protected instance canonically_ordered_comm_semiring : canonically_ordered_comm_semiring nnreal :=
  canonically_ordered_comm_semiring.mk canonically_ordered_add_monoid.add
    canonically_ordered_add_monoid.add_assoc canonically_ordered_add_monoid.zero
    canonically_ordered_add_monoid.zero_add canonically_ordered_add_monoid.add_zero
    canonically_ordered_add_monoid.add_comm canonically_ordered_add_monoid.le
    canonically_ordered_add_monoid.lt canonically_ordered_add_monoid.le_refl
    canonically_ordered_add_monoid.le_trans canonically_ordered_add_monoid.le_antisymm
    canonically_ordered_add_monoid.add_le_add_left
    canonically_ordered_add_monoid.lt_of_add_lt_add_left canonically_ordered_add_monoid.bot
    canonically_ordered_add_monoid.bot_le canonically_ordered_add_monoid.le_iff_exists_add
    comm_semiring.mul comm_semiring.mul_assoc comm_semiring.one comm_semiring.one_mul
    comm_semiring.mul_one comm_semiring.zero_mul comm_semiring.mul_zero comm_semiring.left_distrib
    comm_semiring.right_distrib comm_semiring.mul_comm sorry

protected instance densely_ordered : densely_ordered nnreal :=
  densely_ordered.mk fun (a b : nnreal) (h : ↑a < ↑b) => sorry

protected instance no_top_order : no_top_order nnreal := no_top_order.mk fun (a : nnreal) => sorry

theorem bdd_above_coe {s : set nnreal} : bdd_above (coe '' s) ↔ bdd_above s := sorry

theorem bdd_below_coe (s : set nnreal) : bdd_below (coe '' s) := sorry

protected instance has_Sup : has_Sup nnreal :=
  has_Sup.mk fun (s : set nnreal) => { val := Sup (coe '' s), property := sorry }

protected instance has_Inf : has_Inf nnreal :=
  has_Inf.mk fun (s : set nnreal) => { val := Inf (coe '' s), property := sorry }

theorem coe_Sup (s : set nnreal) : ↑(Sup s) = Sup (coe '' s) := rfl

theorem coe_Inf (s : set nnreal) : ↑(Inf s) = Inf (coe '' s) := rfl

protected instance conditionally_complete_linear_order_bot :
    conditionally_complete_linear_order_bot nnreal :=
  conditionally_complete_linear_order_bot.mk lattice.sup linear_ordered_semiring.le
    linear_ordered_semiring.lt linear_ordered_semiring.le_refl linear_ordered_semiring.le_trans
    linear_ordered_semiring.le_antisymm sorry sorry sorry lattice.inf sorry sorry sorry Sup Inf
    sorry sorry sorry sorry linear_ordered_semiring.le_total
    (id fun (x y : nnreal) => classical.dec (x ≤ y)) linear_ordered_semiring.decidable_eq
    linear_ordered_semiring.decidable_lt order_bot.bot order_bot.bot_le sorry

protected instance archimedean : archimedean nnreal :=
  archimedean.mk fun (x y : nnreal) (pos_y : 0 < y) => sorry

theorem le_of_forall_pos_le_add {a : nnreal} {b : nnreal} (h : ∀ (ε : nnreal), 0 < ε → a ≤ b + ε) :
    a ≤ b :=
  sorry

theorem lt_iff_exists_rat_btwn (a : nnreal) (b : nnreal) :
    a < b ↔ ∃ (q : ℚ), 0 ≤ q ∧ a < nnreal.of_real ↑q ∧ nnreal.of_real ↑q < b :=
  sorry

theorem bot_eq_zero : ⊥ = 0 := rfl

theorem mul_sup (a : nnreal) (b : nnreal) (c : nnreal) : a * (b ⊔ c) = a * b ⊔ a * c := sorry

theorem mul_finset_sup {α : Type u_1} {f : α → nnreal} {s : finset α} (r : nnreal) :
    r * finset.sup s f = finset.sup s fun (a : α) => r * f a :=
  sorry

@[simp] theorem coe_max (x : nnreal) (y : nnreal) : ↑(max x y) = max ↑x ↑y := sorry

@[simp] theorem coe_min (x : nnreal) (y : nnreal) : ↑(min x y) = min ↑x ↑y := sorry

@[simp] theorem zero_le_coe {q : nnreal} : 0 ≤ ↑q := subtype.property q

@[simp] theorem of_real_zero : nnreal.of_real 0 = 0 := sorry

@[simp] theorem of_real_one : nnreal.of_real 1 = 1 := sorry

@[simp] theorem of_real_pos {r : ℝ} : 0 < nnreal.of_real r ↔ 0 < r := sorry

@[simp] theorem of_real_eq_zero {r : ℝ} : nnreal.of_real r = 0 ↔ r ≤ 0 := sorry

theorem of_real_of_nonpos {r : ℝ} : r ≤ 0 → nnreal.of_real r = 0 := iff.mpr of_real_eq_zero

@[simp] theorem of_real_le_of_real_iff {r : ℝ} {p : ℝ} (hp : 0 ≤ p) :
    nnreal.of_real r ≤ nnreal.of_real p ↔ r ≤ p :=
  sorry

@[simp] theorem of_real_lt_of_real_iff' {r : ℝ} {p : ℝ} :
    nnreal.of_real r < nnreal.of_real p ↔ r < p ∧ 0 < p :=
  sorry

theorem of_real_lt_of_real_iff {r : ℝ} {p : ℝ} (h : 0 < p) :
    nnreal.of_real r < nnreal.of_real p ↔ r < p :=
  iff.trans of_real_lt_of_real_iff' (and_iff_left h)

theorem of_real_lt_of_real_iff_of_nonneg {r : ℝ} {p : ℝ} (hr : 0 ≤ r) :
    nnreal.of_real r < nnreal.of_real p ↔ r < p :=
  iff.trans of_real_lt_of_real_iff'
    { mp := and.left, mpr := fun (h : r < p) => { left := h, right := lt_of_le_of_lt hr h } }

@[simp] theorem of_real_add {r : ℝ} {p : ℝ} (hr : 0 ≤ r) (hp : 0 ≤ p) :
    nnreal.of_real (r + p) = nnreal.of_real r + nnreal.of_real p :=
  sorry

theorem of_real_add_of_real {r : ℝ} {p : ℝ} (hr : 0 ≤ r) (hp : 0 ≤ p) :
    nnreal.of_real r + nnreal.of_real p = nnreal.of_real (r + p) :=
  Eq.symm (of_real_add hr hp)

theorem of_real_le_of_real {r : ℝ} {p : ℝ} (h : r ≤ p) : nnreal.of_real r ≤ nnreal.of_real p :=
  nnreal.of_real_mono h

theorem of_real_add_le {r : ℝ} {p : ℝ} :
    nnreal.of_real (r + p) ≤ nnreal.of_real r + nnreal.of_real p :=
  iff.mp nnreal.coe_le_coe (max_le (add_le_add (le_max_left r 0) (le_max_left p 0)) zero_le_coe)

theorem of_real_le_iff_le_coe {r : ℝ} {p : nnreal} : nnreal.of_real r ≤ p ↔ r ≤ ↑p :=
  galois_insertion.gc nnreal.gi r p

theorem le_of_real_iff_coe_le {r : nnreal} {p : ℝ} (hp : 0 ≤ p) : r ≤ nnreal.of_real p ↔ ↑r ≤ p :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (r ≤ nnreal.of_real p ↔ ↑r ≤ p)) (Eq.symm (propext nnreal.coe_le_coe))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑r ≤ ↑(nnreal.of_real p) ↔ ↑r ≤ p)) (coe_of_real p hp)))
      (iff.refl (↑r ≤ p)))

theorem le_of_real_iff_coe_le' {r : nnreal} {p : ℝ} (hr : 0 < r) : r ≤ nnreal.of_real p ↔ ↑r ≤ p :=
  sorry

theorem of_real_lt_iff_lt_coe {r : ℝ} {p : nnreal} (ha : 0 ≤ r) : nnreal.of_real r < p ↔ r < ↑p :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (nnreal.of_real r < p ↔ r < ↑p)) (Eq.symm (propext nnreal.coe_lt_coe))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑(nnreal.of_real r) < ↑p ↔ r < ↑p)) (coe_of_real r ha)))
      (iff.refl (r < ↑p)))

theorem lt_of_real_iff_coe_lt {r : nnreal} {p : ℝ} : r < nnreal.of_real p ↔ ↑r < p := sorry

theorem mul_eq_mul_left {a : nnreal} {b : nnreal} {c : nnreal} (h : a ≠ 0) :
    a * b = a * c ↔ b = c :=
  sorry

theorem of_real_mul {p : ℝ} {q : ℝ} (hp : 0 ≤ p) :
    nnreal.of_real (p * q) = nnreal.of_real p * nnreal.of_real q :=
  sorry

theorem sub_def {r : nnreal} {p : nnreal} : r - p = nnreal.of_real (↑r - ↑p) := rfl

theorem sub_eq_zero {r : nnreal} {p : nnreal} (h : r ≤ p) : r - p = 0 := sorry

@[simp] theorem sub_self {r : nnreal} : r - r = 0 := sub_eq_zero (le_refl r)

@[simp] theorem sub_zero {r : nnreal} : r - 0 = r := sorry

theorem sub_pos {r : nnreal} {p : nnreal} : 0 < r - p ↔ p < r :=
  iff.trans of_real_pos (iff.trans sub_pos nnreal.coe_lt_coe)

protected theorem sub_lt_self {r : nnreal} {p : nnreal} : 0 < r → 0 < p → r - p < r := sorry

@[simp] theorem sub_le_iff_le_add {r : nnreal} {p : nnreal} {q : nnreal} : r - p ≤ q ↔ r ≤ q + p :=
  sorry

@[simp] theorem sub_le_self {r : nnreal} {p : nnreal} : r - p ≤ r :=
  iff.mpr sub_le_iff_le_add (le_add_right (le_refl r))

theorem add_sub_cancel {r : nnreal} {p : nnreal} : p + r - r = p := sorry

theorem add_sub_cancel' {r : nnreal} {p : nnreal} : r + p - r = p :=
  eq.mpr (id (Eq._oldrec (Eq.refl (r + p - r = p)) (add_comm r p)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (p + r - r = p)) add_sub_cancel)) (Eq.refl p))

theorem sub_add_eq_max {r : nnreal} {p : nnreal} : r - p + p = max r p := sorry

theorem add_sub_eq_max {r : nnreal} {p : nnreal} : p + (r - p) = max p r :=
  eq.mpr (id (Eq._oldrec (Eq.refl (p + (r - p) = max p r)) (add_comm p (r - p))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (r - p + p = max p r)) sub_add_eq_max))
      (eq.mpr (id (Eq._oldrec (Eq.refl (max r p = max p r)) (max_comm r p))) (Eq.refl (max p r))))

@[simp] theorem sub_add_cancel_of_le {a : nnreal} {b : nnreal} (h : b ≤ a) : a - b + b = a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a - b + b = a)) sub_add_eq_max))
    (eq.mpr (id (Eq._oldrec (Eq.refl (max a b = a)) (max_eq_left h))) (Eq.refl a))

theorem sub_sub_cancel_of_le {r : nnreal} {p : nnreal} (h : r ≤ p) : p - (p - r) = r := sorry

theorem lt_sub_iff_add_lt {p : nnreal} {q : nnreal} {r : nnreal} : p < q - r ↔ p + r < q := sorry

theorem sub_lt_iff_lt_add {a : nnreal} {b : nnreal} {c : nnreal} (h : b ≤ a) :
    a - b < c ↔ a < b + c :=
  sorry

theorem sub_eq_iff_eq_add {a : nnreal} {b : nnreal} {c : nnreal} (h : b ≤ a) :
    a - b = c ↔ a = c + b :=
  sorry

theorem sum_div {ι : Type u_1} (s : finset ι) (f : ι → nnreal) (b : nnreal) :
    (finset.sum s fun (i : ι) => f i) / b = finset.sum s fun (i : ι) => f i / b :=
  sorry

@[simp] theorem inv_pos {r : nnreal} : 0 < (r⁻¹) ↔ 0 < r := sorry

theorem div_pos {r : nnreal} {p : nnreal} (hr : 0 < r) (hp : 0 < p) : 0 < r / p := sorry

protected theorem mul_inv {r : nnreal} {p : nnreal} : r * p⁻¹ = p⁻¹ * (r⁻¹) :=
  nnreal.eq (mul_inv_rev' ↑r ↑p)

theorem div_self_le (r : nnreal) : r / r ≤ 1 := sorry

@[simp] theorem inv_le {r : nnreal} {p : nnreal} (h : r ≠ 0) : r⁻¹ ≤ p ↔ 1 ≤ r * p :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (r⁻¹ ≤ p ↔ 1 ≤ r * p))
        (Eq.symm (propext (mul_le_mul_left (iff.mpr pos_iff_ne_zero h))))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (r * (r⁻¹) ≤ r * p ↔ 1 ≤ r * p)) (mul_inv_cancel h)))
      (iff.refl (1 ≤ r * p)))

theorem inv_le_of_le_mul {r : nnreal} {p : nnreal} (h : 1 ≤ r * p) : r⁻¹ ≤ p := sorry

@[simp] theorem le_inv_iff_mul_le {r : nnreal} {p : nnreal} (h : p ≠ 0) : r ≤ (p⁻¹) ↔ r * p ≤ 1 :=
  sorry

@[simp] theorem lt_inv_iff_mul_lt {r : nnreal} {p : nnreal} (h : p ≠ 0) : r < (p⁻¹) ↔ r * p < 1 :=
  sorry

theorem mul_le_iff_le_inv {a : nnreal} {b : nnreal} {r : nnreal} (hr : r ≠ 0) :
    r * a ≤ b ↔ a ≤ r⁻¹ * b :=
  sorry

theorem le_div_iff_mul_le {a : nnreal} {b : nnreal} {r : nnreal} (hr : r ≠ 0) :
    a ≤ b / r ↔ a * r ≤ b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ≤ b / r ↔ a * r ≤ b)) div_eq_inv_mul))
    (eq.mpr
      (id
        (Eq._oldrec (Eq.refl (a ≤ r⁻¹ * b ↔ a * r ≤ b)) (Eq.symm (propext (mul_le_iff_le_inv hr)))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (r * a ≤ b ↔ a * r ≤ b)) (mul_comm r a)))
        (iff.refl (a * r ≤ b))))

theorem div_le_iff {a : nnreal} {b : nnreal} {r : nnreal} (hr : r ≠ 0) : a / r ≤ b ↔ a ≤ b * r :=
  div_le_iff (iff.mpr pos_iff_ne_zero hr)

theorem lt_div_iff {a : nnreal} {b : nnreal} {r : nnreal} (hr : r ≠ 0) : a < b / r ↔ a * r < b :=
  lt_iff_lt_of_le_iff_le (div_le_iff hr)

theorem mul_lt_of_lt_div {a : nnreal} {b : nnreal} {r : nnreal} (h : a < b / r) : a * r < b := sorry

theorem le_of_forall_lt_one_mul_le {x : nnreal} {y : nnreal}
    (h : ∀ (a : nnreal), a < 1 → a * x ≤ y) : x ≤ y :=
  sorry

theorem div_add_div_same (a : nnreal) (b : nnreal) (c : nnreal) : a / c + b / c = (a + b) / c :=
  Eq.symm (right_distrib a b (c⁻¹))

theorem half_pos {a : nnreal} (h : 0 < a) : 0 < a / bit0 1 := div_pos h zero_lt_two

theorem add_halves (a : nnreal) : a / bit0 1 + a / bit0 1 = a := nnreal.eq (add_halves ↑a)

theorem half_lt_self {a : nnreal} (h : a ≠ 0) : a / bit0 1 < a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a / bit0 1 < a)) (Eq.symm (propext nnreal.coe_lt_coe))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑(a / bit0 1) < ↑a)) (nnreal.coe_div a (bit0 1))))
      (half_lt_self (iff.mpr bot_lt_iff_ne_bot h)))

theorem two_inv_lt_one : bit0 1⁻¹ < 1 := sorry

theorem div_lt_iff {a : nnreal} {b : nnreal} {c : nnreal} (hc : c ≠ 0) : b / c < a ↔ b < a * c :=
  lt_iff_lt_of_le_iff_le (le_div_iff_mul_le hc)

theorem div_lt_one_of_lt {a : nnreal} {b : nnreal} (h : a < b) : a / b < 1 :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (a / b < 1))
        (propext (div_lt_iff (ne_of_gt (lt_of_le_of_lt (zero_le a) h))))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a < 1 * b)) (one_mul b))) h)

theorem div_add_div (a : nnreal) {b : nnreal} (c : nnreal) {d : nnreal} (hb : b ≠ 0) (hd : d ≠ 0) :
    a / b + c / d = (a * d + b * c) / (b * d) :=
  sorry

theorem add_div' (a : nnreal) (b : nnreal) (c : nnreal) (hc : c ≠ 0) :
    b + a / c = (b * c + a) / c :=
  sorry

theorem div_add' (a : nnreal) (b : nnreal) (c : nnreal) (hc : c ≠ 0) :
    a / c + b = (a + b * c) / c :=
  sorry

theorem of_real_inv {x : ℝ} : nnreal.of_real (x⁻¹) = (nnreal.of_real x⁻¹) := sorry

theorem of_real_div {x : ℝ} {y : ℝ} (hx : 0 ≤ x) :
    nnreal.of_real (x / y) = nnreal.of_real x / nnreal.of_real y :=
  sorry

theorem of_real_div' {x : ℝ} {y : ℝ} (hy : 0 ≤ y) :
    nnreal.of_real (x / y) = nnreal.of_real x / nnreal.of_real y :=
  sorry

@[simp] theorem abs_eq (x : nnreal) : abs ↑x = ↑x := abs_of_nonneg (subtype.property x)

end nnreal


/-- The absolute value on `ℝ` as a map to `ℝ≥0`. -/
def real.nnabs (x : ℝ) : nnreal := { val := abs x, property := abs_nonneg x }

@[simp] theorem nnreal.coe_nnabs (x : ℝ) : ↑(real.nnabs x) = abs x := sorry

end Mathlib