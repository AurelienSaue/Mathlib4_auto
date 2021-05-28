/-
Copyright (c) 2019 Minchao Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Minchao Wu, Mario Carneiro
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.computability.halting
import PostPort

universes u_1 u_2 u_3 u v 

namespace Mathlib

/-!
# Strong reducibility and degrees.

This file defines the notions of computable many-one reduction and one-one
reduction between sets, and shows that the corresponding degrees form a
semilattice.

## Notations

This file uses the local notation `⊕'` for `sum.elim` to denote the disjoint union of two degrees.

## References

* [Robert Soare, *Recursively enumerable sets and degrees*][soare1987]

## Tags

computability, reducibility, reduction
-/

/--
`p` is many-one reducible to `q` if there is a computable function translating questions about `p`
to questions about `q`.
-/
def many_one_reducible {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] (p : α → Prop) (q : β → Prop)  :=
  ∃ (f : α → β), computable f ∧ ∀ (a : α), p a ↔ q (f a)

infixl:1000 " ≤₀ " => Mathlib.many_one_reducible

theorem many_one_reducible.mk {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] {f : α → β} (q : β → Prop) (h : computable f) : (fun (a : α) => q (f a)) ≤₀ q :=
  Exists.intro f { left := h, right := fun (a : α) => iff.rfl }

theorem many_one_reducible_refl {α : Type u_1} [primcodable α] (p : α → Prop) : p ≤₀ p := sorry

theorem many_one_reducible.trans {α : Type u_1} {β : Type u_2} {γ : Type u_3} [primcodable α] [primcodable β] [primcodable γ] {p : α → Prop} {q : β → Prop} {r : γ → Prop} : p ≤₀ q → q ≤₀ r → p ≤₀ r := sorry

theorem reflexive_many_one_reducible {α : Type u_1} [primcodable α] : reflexive many_one_reducible :=
  many_one_reducible_refl

theorem transitive_many_one_reducible {α : Type u_1} [primcodable α] : transitive many_one_reducible :=
  fun (p q r : α → Prop) => many_one_reducible.trans

/--
`p` is one-one reducible to `q` if there is an injective computable function translating questions
about `p` to questions about `q`.
-/
def one_one_reducible {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] (p : α → Prop) (q : β → Prop)  :=
  ∃ (f : α → β), computable f ∧ function.injective f ∧ ∀ (a : α), p a ↔ q (f a)

infixl:1000 " ≤₁ " => Mathlib.one_one_reducible

theorem one_one_reducible.mk {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] {f : α → β} (q : β → Prop) (h : computable f) (i : function.injective f) : (fun (a : α) => q (f a)) ≤₁ q :=
  Exists.intro f { left := h, right := { left := i, right := fun (a : α) => iff.rfl } }

theorem one_one_reducible_refl {α : Type u_1} [primcodable α] (p : α → Prop) : p ≤₁ p := sorry

theorem one_one_reducible.trans {α : Type u_1} {β : Type u_2} {γ : Type u_3} [primcodable α] [primcodable β] [primcodable γ] {p : α → Prop} {q : β → Prop} {r : γ → Prop} : p ≤₁ q → q ≤₁ r → p ≤₁ r := sorry

theorem one_one_reducible.to_many_one {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] {p : α → Prop} {q : β → Prop} : p ≤₁ q → p ≤₀ q := sorry

theorem one_one_reducible.of_equiv {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] {e : α ≃ β} (q : β → Prop) (h : computable ⇑e) : (q ∘ ⇑e) ≤₁ q :=
  one_one_reducible.mk q h (equiv.injective e)

theorem one_one_reducible.of_equiv_symm {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] {e : α ≃ β} (q : β → Prop) (h : computable ⇑(equiv.symm e)) : q ≤₁ (q ∘ ⇑e) := sorry

theorem reflexive_one_one_reducible {α : Type u_1} [primcodable α] : reflexive one_one_reducible :=
  one_one_reducible_refl

theorem transitive_one_one_reducible {α : Type u_1} [primcodable α] : transitive one_one_reducible :=
  fun (p q r : α → Prop) => one_one_reducible.trans

namespace computable_pred


theorem computable_of_many_one_reducible {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] {p : α → Prop} {q : β → Prop} (h₁ : p ≤₀ q) (h₂ : computable_pred q) : computable_pred p := sorry

theorem computable_of_one_one_reducible {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] {p : α → Prop} {q : β → Prop} (h : p ≤₁ q) : computable_pred q → computable_pred p :=
  computable_of_many_one_reducible (one_one_reducible.to_many_one h)

end computable_pred


/-- `p` and `q` are many-one equivalent if each one is many-one reducible to the other. -/
def many_one_equiv {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] (p : α → Prop) (q : β → Prop)  :=
  p ≤₀ q ∧ q ≤₀ p

/-- `p` and `q` are one-one equivalent if each one is one-one reducible to the other. -/
def one_one_equiv {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] (p : α → Prop) (q : β → Prop)  :=
  p ≤₁ q ∧ q ≤₁ p

theorem many_one_equiv_refl {α : Type u_1} [primcodable α] (p : α → Prop) : many_one_equiv p p :=
  { left := many_one_reducible_refl p, right := many_one_reducible_refl p }

theorem many_one_equiv.symm {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] {p : α → Prop} {q : β → Prop} : many_one_equiv p q → many_one_equiv q p :=
  and.swap

theorem many_one_equiv.trans {α : Type u_1} {β : Type u_2} {γ : Type u_3} [primcodable α] [primcodable β] [primcodable γ] {p : α → Prop} {q : β → Prop} {r : γ → Prop} : many_one_equiv p q → many_one_equiv q r → many_one_equiv p r := sorry

theorem equivalence_of_many_one_equiv {α : Type u_1} [primcodable α] : equivalence many_one_equiv :=
  { left := many_one_equiv_refl,
    right :=
      { left := fun (x y : α → Prop) => many_one_equiv.symm, right := fun (x y z : α → Prop) => many_one_equiv.trans } }

theorem one_one_equiv_refl {α : Type u_1} [primcodable α] (p : α → Prop) : one_one_equiv p p :=
  { left := one_one_reducible_refl p, right := one_one_reducible_refl p }

theorem one_one_equiv.symm {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] {p : α → Prop} {q : β → Prop} : one_one_equiv p q → one_one_equiv q p :=
  and.swap

theorem one_one_equiv.trans {α : Type u_1} {β : Type u_2} {γ : Type u_3} [primcodable α] [primcodable β] [primcodable γ] {p : α → Prop} {q : β → Prop} {r : γ → Prop} : one_one_equiv p q → one_one_equiv q r → one_one_equiv p r := sorry

theorem equivalence_of_one_one_equiv {α : Type u_1} [primcodable α] : equivalence one_one_equiv :=
  { left := one_one_equiv_refl,
    right :=
      { left := fun (x y : α → Prop) => one_one_equiv.symm, right := fun (x y z : α → Prop) => one_one_equiv.trans } }

theorem one_one_equiv.to_many_one {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] {p : α → Prop} {q : β → Prop} : one_one_equiv p q → many_one_equiv p q := sorry

/-- a computable bijection -/
def equiv.computable {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] (e : α ≃ β)  :=
  computable ⇑e ∧ computable ⇑(equiv.symm e)

theorem equiv.computable.symm {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] {e : α ≃ β} : equiv.computable e → equiv.computable (equiv.symm e) :=
  and.swap

theorem equiv.computable.trans {α : Type u_1} {β : Type u_2} {γ : Type u_3} [primcodable α] [primcodable β] [primcodable γ] {e₁ : α ≃ β} {e₂ : β ≃ γ} : equiv.computable e₁ → equiv.computable e₂ → equiv.computable (equiv.trans e₁ e₂) := sorry

theorem computable.eqv (α : Type u_1) [denumerable α] : equiv.computable (denumerable.eqv α) :=
  { left := computable.encode, right := computable.of_nat α }

theorem computable.equiv₂ (α : Type u_1) (β : Type u_2) [denumerable α] [denumerable β] : equiv.computable (denumerable.equiv₂ α β) :=
  equiv.computable.trans (computable.eqv α) (equiv.computable.symm (computable.eqv β))

theorem one_one_equiv.of_equiv {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] {e : α ≃ β} (h : equiv.computable e) {p : β → Prop} : one_one_equiv (p ∘ ⇑e) p :=
  { left := one_one_reducible.of_equiv p (and.left h), right := one_one_reducible.of_equiv_symm p (and.right h) }

theorem many_one_equiv.of_equiv {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] {e : α ≃ β} (h : equiv.computable e) {p : β → Prop} : many_one_equiv (p ∘ ⇑e) p :=
  one_one_equiv.to_many_one (one_one_equiv.of_equiv h)

theorem many_one_equiv.le_congr_left {α : Type u_1} {β : Type u_2} {γ : Type u_3} [primcodable α] [primcodable β] [primcodable γ] {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : many_one_equiv p q) : p ≤₀ r ↔ q ≤₀ r :=
  { mp := many_one_reducible.trans (and.right h), mpr := many_one_reducible.trans (and.left h) }

theorem many_one_equiv.le_congr_right {α : Type u_1} {β : Type u_2} {γ : Type u_3} [primcodable α] [primcodable β] [primcodable γ] {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : many_one_equiv q r) : p ≤₀ q ↔ p ≤₀ r :=
  { mp := fun (h' : p ≤₀ q) => many_one_reducible.trans h' (and.left h),
    mpr := fun (h' : p ≤₀ r) => many_one_reducible.trans h' (and.right h) }

theorem one_one_equiv.le_congr_left {α : Type u_1} {β : Type u_2} {γ : Type u_3} [primcodable α] [primcodable β] [primcodable γ] {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : one_one_equiv p q) : p ≤₁ r ↔ q ≤₁ r :=
  { mp := one_one_reducible.trans (and.right h), mpr := one_one_reducible.trans (and.left h) }

theorem one_one_equiv.le_congr_right {α : Type u_1} {β : Type u_2} {γ : Type u_3} [primcodable α] [primcodable β] [primcodable γ] {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : one_one_equiv q r) : p ≤₁ q ↔ p ≤₁ r :=
  { mp := fun (h' : p ≤₁ q) => one_one_reducible.trans h' (and.left h),
    mpr := fun (h' : p ≤₁ r) => one_one_reducible.trans h' (and.right h) }

theorem many_one_equiv.congr_left {α : Type u_1} {β : Type u_2} {γ : Type u_3} [primcodable α] [primcodable β] [primcodable γ] {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : many_one_equiv p q) : many_one_equiv p r ↔ many_one_equiv q r :=
  and_congr (many_one_equiv.le_congr_left h) (many_one_equiv.le_congr_right h)

theorem many_one_equiv.congr_right {α : Type u_1} {β : Type u_2} {γ : Type u_3} [primcodable α] [primcodable β] [primcodable γ] {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : many_one_equiv q r) : many_one_equiv p q ↔ many_one_equiv p r :=
  and_congr (many_one_equiv.le_congr_right h) (many_one_equiv.le_congr_left h)

theorem one_one_equiv.congr_left {α : Type u_1} {β : Type u_2} {γ : Type u_3} [primcodable α] [primcodable β] [primcodable γ] {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : one_one_equiv p q) : one_one_equiv p r ↔ one_one_equiv q r :=
  and_congr (one_one_equiv.le_congr_left h) (one_one_equiv.le_congr_right h)

theorem one_one_equiv.congr_right {α : Type u_1} {β : Type u_2} {γ : Type u_3} [primcodable α] [primcodable β] [primcodable γ] {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : one_one_equiv q r) : one_one_equiv p q ↔ one_one_equiv p r :=
  and_congr (one_one_equiv.le_congr_right h) (one_one_equiv.le_congr_left h)

@[simp] theorem ulower.down_computable {α : Type u_1} [primcodable α] : equiv.computable (ulower.equiv α) :=
  { left := primrec.to_comp primrec.ulower_down, right := primrec.to_comp primrec.ulower_up }

theorem many_one_equiv_up {α : Type u_1} [primcodable α] {p : α → Prop} : many_one_equiv (p ∘ ulower.up) p :=
  many_one_equiv.of_equiv (equiv.computable.symm ulower.down_computable)

theorem one_one_reducible.disjoin_left {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] {p : α → Prop} {q : β → Prop} : p ≤₁ sum.elim p q :=
  Exists.intro sum.inl
    { left := computable.sum_inl,
      right := { left := fun (x y : α) => iff.mp sum.inl.inj_iff, right := fun (a : α) => iff.rfl } }

theorem one_one_reducible.disjoin_right {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] {p : α → Prop} {q : β → Prop} : q ≤₁ sum.elim p q :=
  Exists.intro sum.inr
    { left := computable.sum_inr,
      right := { left := fun (x y : β) => iff.mp sum.inr.inj_iff, right := fun (a : β) => iff.rfl } }

theorem disjoin_many_one_reducible {α : Type u_1} {β : Type u_2} {γ : Type u_3} [primcodable α] [primcodable β] [primcodable γ] {p : α → Prop} {q : β → Prop} {r : γ → Prop} : p ≤₀ r → q ≤₀ r → sum.elim p q ≤₀ r := sorry

theorem disjoin_le {α : Type u_1} {β : Type u_2} {γ : Type u_3} [primcodable α] [primcodable β] [primcodable γ] {p : α → Prop} {q : β → Prop} {r : γ → Prop} : sum.elim p q ≤₀ r ↔ p ≤₀ r ∧ q ≤₀ r := sorry

/--
Computable and injective mapping of predicates to sets of natural numbers.
-/
def to_nat {α : Type u} [primcodable α] [Inhabited α] (p : set α) : set ℕ :=
  set_of fun (n : ℕ) => p (option.get_or_else (encodable.decode α n) Inhabited.default)

@[simp] theorem to_nat_many_one_reducible {α : Type u} [primcodable α] [Inhabited α] {p : set α} : to_nat p ≤₀ p :=
  Exists.intro (fun (n : ℕ) => option.get_or_else (encodable.decode α n) Inhabited.default)
    { left := computable.option_get_or_else computable.decode (computable.const Inhabited.default),
      right := fun (_x : ℕ) => iff.rfl }

@[simp] theorem many_one_reducible_to_nat {α : Type u} [primcodable α] [Inhabited α] {p : set α} : p ≤₀ to_nat p := sorry

@[simp] theorem many_one_reducible_to_nat_to_nat {α : Type u} [primcodable α] [Inhabited α] {β : Type v} [primcodable β] [Inhabited β] {p : set α} {q : set β} : to_nat p ≤₀ to_nat q ↔ p ≤₀ q := sorry

@[simp] theorem to_nat_many_one_equiv {α : Type u} [primcodable α] [Inhabited α] {p : set α} : many_one_equiv (to_nat p) p := sorry

@[simp] theorem many_one_equiv_to_nat {α : Type u} [primcodable α] [Inhabited α] {β : Type v} [primcodable β] [Inhabited β] (p : set α) (q : set β) : many_one_equiv (to_nat p) (to_nat q) ↔ many_one_equiv p q := sorry

/-- A many-one degree is an equivalence class of sets up to many-one equivalence. -/
def many_one_degree  :=
  quotient (setoid.mk many_one_equiv sorry)

namespace many_one_degree


/-- The many-one degree of a set on a primcodable type. -/
def of {α : Type u} [primcodable α] [Inhabited α] (p : α → Prop) : many_one_degree :=
  quotient.mk' (to_nat p)

protected theorem ind_on {C : many_one_degree → Prop} (d : many_one_degree) (h : ∀ (p : set ℕ), C (of p)) : C d :=
  quotient.induction_on' d h

/--
Lifts a function on sets of natural numbers to many-one degrees.
-/
protected def lift_on {φ : Sort u_1} (d : many_one_degree) (f : set ℕ → φ) (h : ∀ (p q : ℕ → Prop), many_one_equiv p q → f p = f q) : φ :=
  quotient.lift_on' d f h

@[simp] protected theorem lift_on_eq {φ : Sort u_1} (p : set ℕ) (f : set ℕ → φ) (h : ∀ (p q : ℕ → Prop), many_one_equiv p q → f p = f q) : many_one_degree.lift_on (of p) f h = f p :=
  rfl

/--
Lifts a binary function on sets of natural numbers to many-one degrees.
-/
@[simp] protected def lift_on₂ {φ : Sort u_1} (d₁ : many_one_degree) (d₂ : many_one_degree) (f : set ℕ → set ℕ → φ) (h : ∀ (p₁ p₂ q₁ q₂ : ℕ → Prop), many_one_equiv p₁ p₂ → many_one_equiv q₁ q₂ → f p₁ q₁ = f p₂ q₂) : φ :=
  many_one_degree.lift_on d₁ (fun (p : set ℕ) => many_one_degree.lift_on d₂ (f p) sorry) sorry

@[simp] protected theorem lift_on₂_eq {φ : Sort u_1} (p : set ℕ) (q : set ℕ) (f : set ℕ → set ℕ → φ) (h : ∀ (p₁ p₂ q₁ q₂ : ℕ → Prop), many_one_equiv p₁ p₂ → many_one_equiv q₁ q₂ → f p₁ q₁ = f p₂ q₂) : many_one_degree.lift_on₂ (of p) (of q) f h = f p q :=
  rfl

@[simp] theorem of_eq_of {α : Type u} [primcodable α] [Inhabited α] {β : Type v} [primcodable β] [Inhabited β] {p : α → Prop} {q : β → Prop} : of p = of q ↔ many_one_equiv p q := sorry

protected instance inhabited : Inhabited many_one_degree :=
  { default := of ∅ }

/--
For many-one degrees `d₁` and `d₂`, `d₁ ≤ d₂` if the sets in `d₁` are many-one reducible to the
sets in `d₂`.
-/
protected instance has_le : HasLessEq many_one_degree :=
  { LessEq := fun (d₁ d₂ : many_one_degree) => many_one_degree.lift_on₂ d₁ d₂ many_one_reducible sorry }

@[simp] theorem of_le_of {α : Type u} [primcodable α] [Inhabited α] {β : Type v} [primcodable β] [Inhabited β] {p : α → Prop} {q : β → Prop} : of p ≤ of q ↔ p ≤₀ q :=
  many_one_reducible_to_nat_to_nat

protected instance partial_order : partial_order many_one_degree :=
  partial_order.mk LessEq (preorder.lt._default LessEq) le_refl sorry sorry

/-- The join of two degrees, induced by the disjoint union of two underlying sets. -/
protected instance has_add : Add many_one_degree :=
  { add :=
      fun (d₁ d₂ : many_one_degree) => many_one_degree.lift_on₂ d₁ d₂ (fun (a b : set ℕ) => of (sum.elim a b)) sorry }

@[simp] theorem add_of {α : Type u} [primcodable α] [Inhabited α] {β : Type v} [primcodable β] [Inhabited β] (p : set α) (q : set β) : of (sum.elim p q) = of p + of q := sorry

@[simp] protected theorem add_le {d₁ : many_one_degree} {d₂ : many_one_degree} {d₃ : many_one_degree} : d₁ + d₂ ≤ d₃ ↔ d₁ ≤ d₃ ∧ d₂ ≤ d₃ := sorry

@[simp] protected theorem le_add_left (d₁ : many_one_degree) (d₂ : many_one_degree) : d₁ ≤ d₁ + d₂ :=
  and.left (iff.mp many_one_degree.add_le (le_refl (d₁ + d₂)))

@[simp] protected theorem le_add_right (d₁ : many_one_degree) (d₂ : many_one_degree) : d₂ ≤ d₁ + d₂ :=
  and.right (iff.mp many_one_degree.add_le (le_refl (d₁ + d₂)))

protected instance semilattice_sup : semilattice_sup many_one_degree :=
  semilattice_sup.mk Add.add partial_order.le partial_order.lt partial_order.le_refl partial_order.le_trans
    partial_order.le_antisymm many_one_degree.le_add_left many_one_degree.le_add_right sorry

