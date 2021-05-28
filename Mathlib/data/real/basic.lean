/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn

The (classical) real numbers ℝ. This is a direct construction
from Cauchy sequences.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.order.conditionally_complete_lattice
import Mathlib.data.real.cau_seq_completion
import Mathlib.algebra.archimedean
import Mathlib.algebra.star.basic
import Mathlib.PostPort

namespace Mathlib

/-- The type `ℝ` of real numbers constructed as equivalence classes of Cauchy sequences of rational
numbers. -/
def real  :=
  cau_seq.completion.Cauchy

notation:1024 "ℝ" => Mathlib.real

namespace real


def comm_ring_aux : comm_ring ℝ :=
  cau_seq.completion.Cauchy.comm_ring

protected instance comm_ring : comm_ring ℝ :=
  comm_ring.mk comm_ring.add comm_ring.add_assoc comm_ring.zero comm_ring.zero_add comm_ring.add_zero comm_ring.neg
    comm_ring.sub comm_ring.add_left_neg comm_ring.add_comm comm_ring.mul comm_ring.mul_assoc comm_ring.one
    comm_ring.one_mul comm_ring.mul_one comm_ring.left_distrib comm_ring.right_distrib comm_ring.mul_comm

/- Extra instances to short-circuit type class resolution -/

protected instance ring : ring ℝ :=
  comm_ring.to_ring ℝ

protected instance comm_semiring : comm_semiring ℝ :=
  comm_ring.to_comm_semiring

protected instance semiring : semiring ℝ :=
  ring.to_semiring

protected instance add_comm_group : add_comm_group ℝ :=
  ring.to_add_comm_group ℝ

protected instance add_group : add_group ℝ :=
  add_comm_group.to_add_group ℝ

protected instance add_comm_monoid : add_comm_monoid ℝ :=
  add_comm_group.to_add_comm_monoid ℝ

protected instance add_monoid : add_monoid ℝ :=
  sub_neg_monoid.to_add_monoid ℝ

protected instance add_left_cancel_semigroup : add_left_cancel_semigroup ℝ :=
  add_left_cancel_monoid.to_add_left_cancel_semigroup ℝ

protected instance add_right_cancel_semigroup : add_right_cancel_semigroup ℝ :=
  add_right_cancel_monoid.to_add_right_cancel_semigroup ℝ

protected instance add_comm_semigroup : add_comm_semigroup ℝ :=
  add_comm_monoid.to_add_comm_semigroup ℝ

protected instance add_semigroup : add_semigroup ℝ :=
  add_monoid.to_add_semigroup ℝ

protected instance comm_monoid : comm_monoid ℝ :=
  comm_semiring.to_comm_monoid ℝ

protected instance monoid : monoid ℝ :=
  ring.to_monoid ℝ

protected instance comm_semigroup : comm_semigroup ℝ :=
  comm_ring.to_comm_semigroup ℝ

protected instance semigroup : semigroup ℝ :=
  monoid.to_semigroup ℝ

protected instance inhabited : Inhabited ℝ :=
  { default := 0 }

/-- The real numbers are a *-ring, with the trivial *-structure. -/
protected instance star_ring : star_ring ℝ :=
  star_ring_of_comm

/-- Coercion `ℚ` → `ℝ` as a `ring_hom`. Note that this
is `cau_seq.completion.of_rat`, not `rat.cast`. -/
def of_rat : ℚ →+* ℝ :=
  ring_hom.mk cau_seq.completion.of_rat sorry sorry sorry sorry

/-- Make a real number from a Cauchy sequence of rationals (by taking the equivalence class). -/
def mk (x : cau_seq ℚ abs) : ℝ :=
  cau_seq.completion.mk x

theorem of_rat_sub (x : ℚ) (y : ℚ) : coe_fn of_rat (x - y) = coe_fn of_rat x - coe_fn of_rat y :=
  congr_arg mk (cau_seq.const_sub x y)

protected instance has_lt : HasLess ℝ :=
  { Less := fun (x y : ℝ) => quotient.lift_on₂ x y Less sorry }

@[simp] theorem mk_lt {f : cau_seq ℚ abs} {g : cau_seq ℚ abs} : mk f < mk g ↔ f < g :=
  iff.rfl

theorem mk_eq {f : cau_seq ℚ abs} {g : cau_seq ℚ abs} : mk f = mk g ↔ f ≈ g :=
  cau_seq.completion.mk_eq

theorem quotient_mk_eq_mk (f : cau_seq ℚ abs) : quotient.mk f = mk f :=
  rfl

theorem mk_eq_mk {f : cau_seq ℚ abs} : cau_seq.completion.mk f = mk f :=
  rfl

@[simp] theorem mk_pos {f : cau_seq ℚ abs} : 0 < mk f ↔ cau_seq.pos f :=
  iff_of_eq (congr_arg cau_seq.pos (sub_zero f))

protected def le (x : ℝ) (y : ℝ)  :=
  x < y ∨ x = y

protected instance has_le : HasLessEq ℝ :=
  { LessEq := real.le }

@[simp] theorem mk_le {f : cau_seq ℚ abs} {g : cau_seq ℚ abs} : mk f ≤ mk g ↔ f ≤ g :=
  or_congr iff.rfl quotient.eq

theorem add_lt_add_iff_left {a : ℝ} {b : ℝ} (c : ℝ) : c + a < c + b ↔ a < b := sorry

protected instance partial_order : partial_order ℝ :=
  partial_order.mk LessEq Less sorry sorry sorry

protected instance preorder : preorder ℝ :=
  partial_order.to_preorder ℝ

theorem of_rat_lt {x : ℚ} {y : ℚ} : coe_fn of_rat x < coe_fn of_rat y ↔ x < y :=
  cau_seq.const_lt

protected theorem zero_lt_one : 0 < 1 :=
  iff.mpr of_rat_lt zero_lt_one

protected theorem mul_pos {a : ℝ} {b : ℝ} : 0 < a → 0 < b → 0 < a * b := sorry

protected instance ordered_ring : ordered_ring ℝ :=
  ordered_ring.mk comm_ring.add comm_ring.add_assoc comm_ring.zero comm_ring.zero_add comm_ring.add_zero comm_ring.neg
    comm_ring.sub comm_ring.add_left_neg comm_ring.add_comm comm_ring.mul comm_ring.mul_assoc comm_ring.one
    comm_ring.one_mul comm_ring.mul_one comm_ring.left_distrib comm_ring.right_distrib partial_order.le partial_order.lt
    partial_order.le_refl partial_order.le_trans partial_order.le_antisymm sorry sorry real.mul_pos

protected instance ordered_semiring : ordered_semiring ℝ :=
  ordered_ring.to_ordered_semiring

protected instance ordered_add_comm_group : ordered_add_comm_group ℝ :=
  ordered_ring.to_ordered_add_comm_group ℝ

protected instance ordered_cancel_add_comm_monoid : ordered_cancel_add_comm_monoid ℝ :=
  ordered_semiring.to_ordered_cancel_add_comm_monoid ℝ

protected instance ordered_add_comm_monoid : ordered_add_comm_monoid ℝ :=
  ordered_cancel_add_comm_monoid.to_ordered_add_comm_monoid

protected instance has_one : HasOne ℝ :=
  monoid.to_has_one ℝ

protected instance has_zero : HasZero ℝ :=
  mul_zero_class.to_has_zero ℝ

protected instance has_mul : Mul ℝ :=
  distrib.to_has_mul ℝ

protected instance has_add : Add ℝ :=
  distrib.to_has_add ℝ

protected instance has_sub : Sub ℝ :=
  sub_neg_monoid.to_has_sub ℝ

protected instance nontrivial : nontrivial ℝ :=
  nontrivial.mk (Exists.intro 0 (Exists.intro 1 (ne_of_lt real.zero_lt_one)))

protected instance linear_order : linear_order ℝ :=
  linear_order.mk partial_order.le partial_order.lt partial_order.le_refl partial_order.le_trans partial_order.le_antisymm
    sorry (fun (a b : ℝ) => classical.prop_decidable (a ≤ b)) Mathlib.decidable_eq_of_decidable_le
    Mathlib.decidable_lt_of_decidable_le

protected instance linear_ordered_comm_ring : linear_ordered_comm_ring ℝ :=
  linear_ordered_comm_ring.mk ordered_ring.add ordered_ring.add_assoc ordered_ring.zero ordered_ring.zero_add
    ordered_ring.add_zero ordered_ring.neg ordered_ring.sub ordered_ring.add_left_neg ordered_ring.add_comm
    ordered_ring.mul ordered_ring.mul_assoc ordered_ring.one ordered_ring.one_mul ordered_ring.mul_one
    ordered_ring.left_distrib ordered_ring.right_distrib ordered_ring.le ordered_ring.lt ordered_ring.le_refl
    ordered_ring.le_trans ordered_ring.le_antisymm ordered_ring.add_le_add_left ordered_ring.zero_le_one
    ordered_ring.mul_pos linear_order.le_total linear_order.decidable_le linear_order.decidable_eq
    linear_order.decidable_lt nontrivial.exists_pair_ne comm_ring.mul_comm

/- Extra instances to short-circuit type class resolution -/

protected instance linear_ordered_ring : linear_ordered_ring ℝ :=
  linear_ordered_comm_ring.to_linear_ordered_ring ℝ

protected instance linear_ordered_semiring : linear_ordered_semiring ℝ :=
  linear_ordered_comm_ring.to_linear_ordered_semiring

protected instance domain : domain ℝ :=
  domain.mk comm_ring.add comm_ring.add_assoc comm_ring.zero comm_ring.zero_add comm_ring.add_zero comm_ring.neg
    comm_ring.sub comm_ring.add_left_neg comm_ring.add_comm comm_ring.mul comm_ring.mul_assoc comm_ring.one
    comm_ring.one_mul comm_ring.mul_one comm_ring.left_distrib comm_ring.right_distrib nontrivial.exists_pair_ne sorry

protected instance linear_ordered_field : linear_ordered_field ℝ := sorry

/- Extra instances to short-circuit type class resolution -/

protected instance linear_ordered_add_comm_group : linear_ordered_add_comm_group ℝ :=
  linear_ordered_ring.to_linear_ordered_add_comm_group

protected instance field : field ℝ :=
  linear_ordered_field.to_field ℝ

protected instance division_ring : division_ring ℝ :=
  field.to_division_ring

protected instance integral_domain : integral_domain ℝ :=
  field.to_integral_domain

protected instance distrib_lattice : distrib_lattice ℝ :=
  Mathlib.distrib_lattice_of_linear_order

protected instance lattice : lattice ℝ :=
  Mathlib.lattice_of_linear_order

protected instance semilattice_inf : semilattice_inf ℝ :=
  lattice.to_semilattice_inf ℝ

protected instance semilattice_sup : semilattice_sup ℝ :=
  lattice.to_semilattice_sup ℝ

protected instance has_inf : has_inf ℝ :=
  semilattice_inf.to_has_inf ℝ

protected instance has_sup : has_sup ℝ :=
  semilattice_sup.to_has_sup ℝ

protected instance decidable_lt (a : ℝ) (b : ℝ) : Decidable (a < b) :=
  has_lt.lt.decidable a b

protected instance decidable_le (a : ℝ) (b : ℝ) : Decidable (a ≤ b) :=
  has_le.le.decidable a b

protected instance decidable_eq (a : ℝ) (b : ℝ) : Decidable (a = b) :=
  quotient.decidable_eq a b

@[simp] theorem of_rat_eq_cast (x : ℚ) : coe_fn of_rat x = ↑x :=
  ring_hom.eq_rat_cast of_rat

theorem le_mk_of_forall_le {x : ℝ} {f : cau_seq ℚ abs} : (∃ (i : ℕ), ∀ (j : ℕ), j ≥ i → x ≤ ↑(coe_fn f j)) → x ≤ mk f := sorry

theorem mk_le_of_forall_le {f : cau_seq ℚ abs} {x : ℝ} : (∃ (i : ℕ), ∀ (j : ℕ), j ≥ i → ↑(coe_fn f j) ≤ x) → mk f ≤ x := sorry

theorem mk_near_of_forall_near {f : cau_seq ℚ abs} {x : ℝ} {ε : ℝ} (H : ∃ (i : ℕ), ∀ (j : ℕ), j ≥ i → abs (↑(coe_fn f j) - x) ≤ ε) : abs (mk f - x) ≤ ε := sorry

protected instance archimedean : archimedean ℝ :=
  iff.mpr archimedean_iff_rat_le fun (x : ℝ) => quotient.induction_on x fun (f : cau_seq ℚ abs) => sorry

/- mark `real` irreducible in order to prevent `auto_cases` unfolding reals,
since users rarely want to consider real numbers as Cauchy sequences.
Marking `comm_ring_aux` `irreducible` is done to ensure that there are no problems
with non definitionally equal instances, caused by making `real` irreducible-/

protected instance floor_ring : floor_ring ℝ :=
  archimedean.floor_ring ℝ

theorem is_cau_seq_iff_lift {f : ℕ → ℚ} : is_cau_seq abs f ↔ is_cau_seq abs fun (i : ℕ) => ↑(f i) := sorry

theorem of_near (f : ℕ → ℚ) (x : ℝ) (h : ∀ (ε : ℝ), ε > 0 → ∃ (i : ℕ), ∀ (j : ℕ), j ≥ i → abs (↑(f j) - x) < ε) : ∃ (h' : is_cau_seq abs f), mk { val := f, property := h' } = x := sorry

theorem exists_floor (x : ℝ) : ∃ (ub : ℤ), ↑ub ≤ x ∧ ∀ (z : ℤ), ↑z ≤ x → z ≤ ub := sorry

theorem exists_sup (S : set ℝ) : (∃ (x : ℝ), x ∈ S) → (∃ (x : ℝ), ∀ (y : ℝ), y ∈ S → y ≤ x) → ∃ (x : ℝ), ∀ (y : ℝ), x ≤ y ↔ ∀ (z : ℝ), z ∈ S → z ≤ y := sorry

protected instance has_Sup : has_Sup ℝ :=
  has_Sup.mk
    fun (S : set ℝ) =>
      dite ((∃ (x : ℝ), x ∈ S) ∧ ∃ (x : ℝ), ∀ (y : ℝ), y ∈ S → y ≤ x)
        (fun (h : (∃ (x : ℝ), x ∈ S) ∧ ∃ (x : ℝ), ∀ (y : ℝ), y ∈ S → y ≤ x) => classical.some sorry)
        fun (h : ¬((∃ (x : ℝ), x ∈ S) ∧ ∃ (x : ℝ), ∀ (y : ℝ), y ∈ S → y ≤ x)) => 0

theorem Sup_def (S : set ℝ) : Sup S =
  dite ((∃ (x : ℝ), x ∈ S) ∧ ∃ (x : ℝ), ∀ (y : ℝ), y ∈ S → y ≤ x)
    (fun (h : (∃ (x : ℝ), x ∈ S) ∧ ∃ (x : ℝ), ∀ (y : ℝ), y ∈ S → y ≤ x) =>
      classical.some (exists_sup S (and.left h) (and.right h)))
    fun (h : ¬((∃ (x : ℝ), x ∈ S) ∧ ∃ (x : ℝ), ∀ (y : ℝ), y ∈ S → y ≤ x)) => 0 :=
  rfl

theorem Sup_le (S : set ℝ) (h₁ : ∃ (x : ℝ), x ∈ S) (h₂ : ∃ (x : ℝ), ∀ (y : ℝ), y ∈ S → y ≤ x) {y : ℝ} : Sup S ≤ y ↔ ∀ (z : ℝ), z ∈ S → z ≤ y := sorry

-- this proof times out without this

theorem lt_Sup (S : set ℝ) (h₁ : ∃ (x : ℝ), x ∈ S) (h₂ : ∃ (x : ℝ), ∀ (y : ℝ), y ∈ S → y ≤ x) {y : ℝ} : y < Sup S ↔ ∃ (z : ℝ), ∃ (H : z ∈ S), y < z := sorry

theorem le_Sup (S : set ℝ) (h₂ : ∃ (x : ℝ), ∀ (y : ℝ), y ∈ S → y ≤ x) {x : ℝ} (xS : x ∈ S) : x ≤ Sup S :=
  iff.mp (Sup_le S (Exists.intro x xS) h₂) (le_refl (Sup S)) x xS

theorem Sup_le_ub (S : set ℝ) (h₁ : ∃ (x : ℝ), x ∈ S) {ub : ℝ} (h₂ : ∀ (y : ℝ), y ∈ S → y ≤ ub) : Sup S ≤ ub :=
  iff.mpr (Sup_le S h₁ (Exists.intro ub h₂)) h₂

protected theorem is_lub_Sup {s : set ℝ} {a : ℝ} {b : ℝ} (ha : a ∈ s) (hb : b ∈ upper_bounds s) : is_lub s (Sup s) :=
  { left := fun (x : ℝ) (xs : x ∈ s) => le_Sup s (Exists.intro b hb) xs,
    right := fun (u : ℝ) (h : u ∈ upper_bounds s) => Sup_le_ub s (Exists.intro a ha) h }

protected instance has_Inf : has_Inf ℝ :=
  has_Inf.mk fun (S : set ℝ) => -Sup (set_of fun (x : ℝ) => -x ∈ S)

theorem Inf_def (S : set ℝ) : Inf S = -Sup (set_of fun (x : ℝ) => -x ∈ S) :=
  rfl

theorem le_Inf (S : set ℝ) (h₁ : ∃ (x : ℝ), x ∈ S) (h₂ : ∃ (x : ℝ), ∀ (y : ℝ), y ∈ S → x ≤ y) {y : ℝ} : y ≤ Inf S ↔ ∀ (z : ℝ), z ∈ S → y ≤ z := sorry

-- this proof times out without this

theorem Inf_lt (S : set ℝ) (h₁ : ∃ (x : ℝ), x ∈ S) (h₂ : ∃ (x : ℝ), ∀ (y : ℝ), y ∈ S → x ≤ y) {y : ℝ} : Inf S < y ↔ ∃ (z : ℝ), ∃ (H : z ∈ S), z < y := sorry

theorem Inf_le (S : set ℝ) (h₂ : ∃ (x : ℝ), ∀ (y : ℝ), y ∈ S → x ≤ y) {x : ℝ} (xS : x ∈ S) : Inf S ≤ x :=
  iff.mp (le_Inf S (Exists.intro x xS) h₂) (le_refl (Inf S)) x xS

theorem lb_le_Inf (S : set ℝ) (h₁ : ∃ (x : ℝ), x ∈ S) {lb : ℝ} (h₂ : ∀ (y : ℝ), y ∈ S → lb ≤ y) : lb ≤ Inf S :=
  iff.mpr (le_Inf S h₁ (Exists.intro lb h₂)) h₂

protected instance conditionally_complete_linear_order : conditionally_complete_linear_order ℝ :=
  conditionally_complete_linear_order.mk lattice.sup linear_order.le linear_order.lt linear_order.le_refl
    linear_order.le_trans linear_order.le_antisymm lattice.le_sup_left lattice.le_sup_right lattice.sup_le lattice.inf
    lattice.inf_le_left lattice.inf_le_right lattice.le_inf Sup Inf sorry sorry sorry sorry linear_order.le_total
    (classical.dec_rel LessEq) linear_order.decidable_eq linear_order.decidable_lt

theorem Sup_empty : Sup ∅ = 0 := sorry

theorem Sup_of_not_bdd_above {s : set ℝ} (hs : ¬bdd_above s) : Sup s = 0 :=
  dif_neg fun (h : (∃ (x : ℝ), x ∈ s) ∧ ∃ (x : ℝ), ∀ (y : ℝ), y ∈ s → y ≤ x) => hs (and.right h)

theorem Sup_univ : Sup set.univ = 0 := sorry

theorem Inf_empty : Inf ∅ = 0 := sorry

theorem Inf_of_not_bdd_below {s : set ℝ} (hs : ¬bdd_below s) : Inf s = 0 := sorry

theorem cau_seq_converges (f : cau_seq ℝ abs) : ∃ (x : ℝ), f ≈ cau_seq.const abs x := sorry

protected instance abs.cau_seq.is_complete : cau_seq.is_complete ℝ abs :=
  cau_seq.is_complete.mk cau_seq_converges

