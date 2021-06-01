/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.logic.nontrivial
import Mathlib.algebra.group.units_hom
import Mathlib.algebra.group.inj_surj
import Mathlib.algebra.group_with_zero.defs
import Mathlib.PostPort

universes u_1 u_3 u u_2 u_4 u_5 

namespace Mathlib

/-!
# Groups with an adjoined zero element

This file describes structures that are not usually studied on their own right in mathematics,
namely a special sort of monoid: apart from a distinguished “zero element” they form a group,
or in other words, they are groups with an adjoined zero element.

Examples are:

* division rings;
* the value monoid of a multiplicative valuation;
* in particular, the non-negative real numbers.

## Main definitions

Various lemmas about `group_with_zero` and `comm_group_with_zero`.
To reduce import dependencies, the type-classes themselves are in
`algebra.group_with_zero.defs`.

## Implementation details

As is usual in mathlib, we extend the inverse function to the zero element,
and require `0⁻¹ = 0`.

-/

/-- Pullback a `mul_zero_class` instance along an injective function. -/
protected def function.injective.mul_zero_class {M₀ : Type u_1} {M₀' : Type u_3} [mul_zero_class M₀]
    [Mul M₀'] [HasZero M₀'] (f : M₀' → M₀) (hf : function.injective f) (zero : f 0 = 0)
    (mul : ∀ (a b : M₀'), f (a * b) = f a * f b) : mul_zero_class M₀' :=
  mul_zero_class.mk Mul.mul 0 sorry sorry

/-- Pushforward a `mul_zero_class` instance along an surjective function. -/
protected def function.surjective.mul_zero_class {M₀ : Type u_1} {M₀' : Type u_3}
    [mul_zero_class M₀] [Mul M₀'] [HasZero M₀'] (f : M₀ → M₀') (hf : function.surjective f)
    (zero : f 0 = 0) (mul : ∀ (a b : M₀), f (a * b) = f a * f b) : mul_zero_class M₀' :=
  mul_zero_class.mk Mul.mul 0 sorry sorry

theorem mul_eq_zero_of_left {M₀ : Type u_1} [mul_zero_class M₀] {a : M₀} (h : a = 0) (b : M₀) :
    a * b = 0 :=
  Eq.symm h ▸ zero_mul b

theorem mul_eq_zero_of_right {M₀ : Type u_1} [mul_zero_class M₀] {b : M₀} (a : M₀) (h : b = 0) :
    a * b = 0 :=
  Eq.symm h ▸ mul_zero a

theorem left_ne_zero_of_mul {M₀ : Type u_1} [mul_zero_class M₀] {a : M₀} {b : M₀} :
    a * b ≠ 0 → a ≠ 0 :=
  mt fun (h : a = 0) => mul_eq_zero_of_left h b

theorem right_ne_zero_of_mul {M₀ : Type u_1} [mul_zero_class M₀] {a : M₀} {b : M₀} :
    a * b ≠ 0 → b ≠ 0 :=
  mt (mul_eq_zero_of_right a)

theorem ne_zero_and_ne_zero_of_mul {M₀ : Type u_1} [mul_zero_class M₀] {a : M₀} {b : M₀}
    (h : a * b ≠ 0) : a ≠ 0 ∧ b ≠ 0 :=
  { left := left_ne_zero_of_mul h, right := right_ne_zero_of_mul h }

theorem mul_eq_zero_of_ne_zero_imp_eq_zero {M₀ : Type u_1} [mul_zero_class M₀] {a : M₀} {b : M₀}
    (h : a ≠ 0 → b = 0) : a * b = 0 :=
  sorry

/-- Pushforward a `no_zero_divisors` instance along an injective function. -/
protected theorem function.injective.no_zero_divisors {M₀ : Type u_1} {M₀' : Type u_3} [Mul M₀]
    [HasZero M₀] [Mul M₀'] [HasZero M₀'] [no_zero_divisors M₀'] (f : M₀ → M₀')
    (hf : function.injective f) (zero : f 0 = 0) (mul : ∀ (x y : M₀), f (x * y) = f x * f y) :
    no_zero_divisors M₀ :=
  sorry

theorem eq_zero_of_mul_self_eq_zero {M₀ : Type u_1} [Mul M₀] [HasZero M₀] [no_zero_divisors M₀]
    {a : M₀} (h : a * a = 0) : a = 0 :=
  or.elim (eq_zero_or_eq_zero_of_mul_eq_zero h) id id

/-- If `α` has no zero divisors, then the product of two elements equals zero iff one of them
equals zero. -/
@[simp] theorem mul_eq_zero {M₀ : Type u_1} [mul_zero_class M₀] [no_zero_divisors M₀] {a : M₀}
    {b : M₀} : a * b = 0 ↔ a = 0 ∨ b = 0 :=
  { mp := eq_zero_or_eq_zero_of_mul_eq_zero,
    mpr :=
      fun (o : a = 0 ∨ b = 0) =>
        or.elim o (fun (h : a = 0) => mul_eq_zero_of_left h b) (mul_eq_zero_of_right a) }

/-- If `α` has no zero divisors, then the product of two elements equals zero iff one of them
equals zero. -/
@[simp] theorem zero_eq_mul {M₀ : Type u_1} [mul_zero_class M₀] [no_zero_divisors M₀] {a : M₀}
    {b : M₀} : 0 = a * b ↔ a = 0 ∨ b = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (0 = a * b ↔ a = 0 ∨ b = 0)) (propext eq_comm)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * b = 0 ↔ a = 0 ∨ b = 0)) (propext mul_eq_zero)))
      (iff.refl (a = 0 ∨ b = 0)))

/-- If `α` has no zero divisors, then the product of two elements is nonzero iff both of them
are nonzero. -/
theorem mul_ne_zero_iff {M₀ : Type u_1} [mul_zero_class M₀] [no_zero_divisors M₀] {a : M₀}
    {b : M₀} : a * b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 :=
  iff.trans (not_congr mul_eq_zero) not_or_distrib

theorem mul_ne_zero {M₀ : Type u_1} [mul_zero_class M₀] [no_zero_divisors M₀] {a : M₀} {b : M₀}
    (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 :=
  iff.mpr mul_ne_zero_iff { left := ha, right := hb }

/-- If `α` has no zero divisors, then for elements `a, b : α`, `a * b` equals zero iff so is
`b * a`. -/
theorem mul_eq_zero_comm {M₀ : Type u_1} [mul_zero_class M₀] [no_zero_divisors M₀] {a : M₀}
    {b : M₀} : a * b = 0 ↔ b * a = 0 :=
  iff.trans mul_eq_zero (iff.trans (or_comm (a = 0) (b = 0)) (iff.symm mul_eq_zero))

/-- If `α` has no zero divisors, then for elements `a, b : α`, `a * b` is nonzero iff so is
`b * a`. -/
theorem mul_ne_zero_comm {M₀ : Type u_1} [mul_zero_class M₀] [no_zero_divisors M₀] {a : M₀}
    {b : M₀} : a * b ≠ 0 ↔ b * a ≠ 0 :=
  not_congr mul_eq_zero_comm

theorem mul_self_eq_zero {M₀ : Type u_1} [mul_zero_class M₀] [no_zero_divisors M₀] {a : M₀} :
    a * a = 0 ↔ a = 0 :=
  sorry

theorem zero_eq_mul_self {M₀ : Type u_1} [mul_zero_class M₀] [no_zero_divisors M₀] {a : M₀} :
    0 = a * a ↔ a = 0 :=
  sorry

/-- In a nontrivial monoid with zero, zero and one are different. -/
@[simp] theorem zero_ne_one {M₀ : Type u_1} [monoid_with_zero M₀] [nontrivial M₀] : 0 ≠ 1 := sorry

@[simp] theorem one_ne_zero {M₀ : Type u_1} [monoid_with_zero M₀] [nontrivial M₀] : 1 ≠ 0 :=
  ne.symm zero_ne_one

theorem ne_zero_of_eq_one {M₀ : Type u_1} [monoid_with_zero M₀] [nontrivial M₀] {a : M₀}
    (h : a = 1) : a ≠ 0 :=
  trans_rel_right ne h one_ne_zero

theorem left_ne_zero_of_mul_eq_one {M₀ : Type u_1} [monoid_with_zero M₀] [nontrivial M₀] {a : M₀}
    {b : M₀} (h : a * b = 1) : a ≠ 0 :=
  left_ne_zero_of_mul (ne_zero_of_eq_one h)

theorem right_ne_zero_of_mul_eq_one {M₀ : Type u_1} [monoid_with_zero M₀] [nontrivial M₀] {a : M₀}
    {b : M₀} (h : a * b = 1) : b ≠ 0 :=
  right_ne_zero_of_mul (ne_zero_of_eq_one h)

/-- Pullback a `nontrivial` instance along a function sending `0` to `0` and `1` to `1`. -/
protected theorem pullback_nonzero {M₀ : Type u_1} {M₀' : Type u_3} [monoid_with_zero M₀]
    [nontrivial M₀] [HasZero M₀'] [HasOne M₀'] (f : M₀' → M₀) (zero : f 0 = 0) (one : f 1 = 1) :
    nontrivial M₀' :=
  sorry

/-- Pullback a `monoid_with_zero` class along an injective function. -/
protected def function.injective.monoid_with_zero {M₀ : Type u_1} {M₀' : Type u_3} [HasZero M₀']
    [Mul M₀'] [HasOne M₀'] [monoid_with_zero M₀] (f : M₀' → M₀) (hf : function.injective f)
    (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ (x y : M₀'), f (x * y) = f x * f y) :
    monoid_with_zero M₀' :=
  monoid_with_zero.mk monoid.mul sorry monoid.one sorry sorry mul_zero_class.zero sorry sorry

/-- Pushforward a `monoid_with_zero` class along a surjective function. -/
protected def function.surjective.monoid_with_zero {M₀ : Type u_1} {M₀' : Type u_3} [HasZero M₀']
    [Mul M₀'] [HasOne M₀'] [monoid_with_zero M₀] (f : M₀ → M₀') (hf : function.surjective f)
    (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ (x y : M₀), f (x * y) = f x * f y) :
    monoid_with_zero M₀' :=
  monoid_with_zero.mk monoid.mul sorry monoid.one sorry sorry mul_zero_class.zero sorry sorry

/-- Pullback a `monoid_with_zero` class along an injective function. -/
protected def function.injective.comm_monoid_with_zero {M₀ : Type u_1} {M₀' : Type u_3}
    [HasZero M₀'] [Mul M₀'] [HasOne M₀'] [comm_monoid_with_zero M₀] (f : M₀' → M₀)
    (hf : function.injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ (x y : M₀'), f (x * y) = f x * f y) : comm_monoid_with_zero M₀' :=
  comm_monoid_with_zero.mk comm_monoid.mul sorry comm_monoid.one sorry sorry sorry
    mul_zero_class.zero sorry sorry

/-- Pushforward a `monoid_with_zero` class along a surjective function. -/
protected def function.surjective.comm_monoid_with_zero {M₀ : Type u_1} {M₀' : Type u_3}
    [HasZero M₀'] [Mul M₀'] [HasOne M₀'] [comm_monoid_with_zero M₀] (f : M₀ → M₀')
    (hf : function.surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ (x y : M₀), f (x * y) = f x * f y) : comm_monoid_with_zero M₀' :=
  comm_monoid_with_zero.mk comm_monoid.mul sorry comm_monoid.one sorry sorry sorry
    mul_zero_class.zero sorry sorry

namespace units


/-- An element of the unit group of a nonzero monoid with zero represented as an element
    of the monoid is nonzero. -/
@[simp] theorem ne_zero {M₀ : Type u_1} [monoid_with_zero M₀] [nontrivial M₀] (u : units M₀) :
    ↑u ≠ 0 :=
  left_ne_zero_of_mul_eq_one (mul_inv u)

-- We can't use `mul_eq_zero` + `units.ne_zero` in the next two lemmas because we don't assume

-- `nonzero M₀`.

@[simp] theorem mul_left_eq_zero {M₀ : Type u_1} [monoid_with_zero M₀] (u : units M₀) {a : M₀} :
    a * ↑u = 0 ↔ a = 0 :=
  sorry

@[simp] theorem mul_right_eq_zero {M₀ : Type u_1} [monoid_with_zero M₀] (u : units M₀) {a : M₀} :
    ↑u * a = 0 ↔ a = 0 :=
  sorry

end units


namespace is_unit


theorem ne_zero {M₀ : Type u_1} [monoid_with_zero M₀] [nontrivial M₀] {a : M₀} (ha : is_unit a) :
    a ≠ 0 :=
  (fun (_a : is_unit a) =>
      Exists.dcases_on _a
        fun (w : units M₀) (h : ↑w = a) =>
          idRhs ((fun (_x : M₀) => _x ≠ 0) a) (h ▸ units.ne_zero w))
    ha

theorem mul_right_eq_zero {M₀ : Type u_1} [monoid_with_zero M₀] {a : M₀} {b : M₀} (ha : is_unit a) :
    a * b = 0 ↔ b = 0 :=
  sorry

theorem mul_left_eq_zero {M₀ : Type u_1} [monoid_with_zero M₀] {a : M₀} {b : M₀} (hb : is_unit b) :
    a * b = 0 ↔ a = 0 :=
  sorry

end is_unit


/-- In a monoid with zero, if zero equals one, then zero is the only element. -/
theorem eq_zero_of_zero_eq_one {M₀ : Type u_1} [monoid_with_zero M₀] (h : 0 = 1) (a : M₀) : a = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a = 0)) (Eq.symm (mul_one a))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * 1 = 0)) (Eq.symm h)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a * 0 = 0)) (mul_zero a))) (Eq.refl 0)))

/-- In a monoid with zero, if zero equals one, then zero is the unique element.

Somewhat arbitrarily, we define the default element to be `0`.
All other elements will be provably equal to it, but not necessarily definitionally equal. -/
def unique_of_zero_eq_one {M₀ : Type u_1} [monoid_with_zero M₀] (h : 0 = 1) : unique M₀ :=
  unique.mk { default := 0 } (eq_zero_of_zero_eq_one h)

/-- In a monoid with zero, zero equals one if and only if all elements of that semiring
are equal. -/
theorem subsingleton_iff_zero_eq_one {M₀ : Type u_1} [monoid_with_zero M₀] :
    0 = 1 ↔ subsingleton M₀ :=
  { mp := fun (h : 0 = 1) => unique.subsingleton,
    mpr := fun (h : subsingleton M₀) => subsingleton.elim 0 1 }

theorem subsingleton_of_zero_eq_one {M₀ : Type u_1} [monoid_with_zero M₀] :
    0 = 1 → subsingleton M₀ :=
  iff.mp subsingleton_iff_zero_eq_one

theorem eq_of_zero_eq_one {M₀ : Type u_1} [monoid_with_zero M₀] (h : 0 = 1) (a : M₀) (b : M₀) :
    a = b :=
  subsingleton.elim a b

@[simp] theorem is_unit_zero_iff {M₀ : Type u_1} [monoid_with_zero M₀] : is_unit 0 ↔ 0 = 1 := sorry

@[simp] theorem not_is_unit_zero {M₀ : Type u_1} [monoid_with_zero M₀] [nontrivial M₀] :
    ¬is_unit 0 :=
  mt (iff.mp is_unit_zero_iff) zero_ne_one

/-- In a monoid with zero, either zero and one are nonequal, or zero is the only element. -/
theorem zero_ne_one_or_forall_eq_0 (M₀ : Type u_1) [monoid_with_zero M₀] :
    0 ≠ 1 ∨ ∀ (a : M₀), a = 0 :=
  not_or_of_imp eq_zero_of_zero_eq_one

protected instance cancel_monoid_with_zero.to_no_zero_divisors {M₀ : Type u_1}
    [cancel_monoid_with_zero M₀] : no_zero_divisors M₀ :=
  no_zero_divisors.mk
    fun (a b : M₀) (ab0 : a * b = 0) =>
      dite (a = 0) (fun (h : a = 0) => Or.inl h)
        fun (h : ¬a = 0) =>
          Or.inr
            (cancel_monoid_with_zero.mul_left_cancel_of_ne_zero h
              (eq.mpr (id (Eq._oldrec (Eq.refl (a * b = a * 0)) ab0))
                (eq.mpr (id (Eq._oldrec (Eq.refl (0 = a * 0)) (mul_zero a))) (Eq.refl 0))))

theorem mul_left_inj' {M₀ : Type u_1} [cancel_monoid_with_zero M₀] {a : M₀} {b : M₀} {c : M₀}
    (hc : c ≠ 0) : a * c = b * c ↔ a = b :=
  { mp := mul_right_cancel' hc, mpr := fun (h : a = b) => h ▸ rfl }

theorem mul_right_inj' {M₀ : Type u_1} [cancel_monoid_with_zero M₀] {a : M₀} {b : M₀} {c : M₀}
    (ha : a ≠ 0) : a * b = a * c ↔ b = c :=
  { mp := mul_left_cancel' ha, mpr := fun (h : b = c) => h ▸ rfl }

@[simp] theorem mul_eq_mul_right_iff {M₀ : Type u_1} [cancel_monoid_with_zero M₀] {a : M₀} {b : M₀}
    {c : M₀} : a * c = b * c ↔ a = b ∨ c = 0 :=
  sorry

@[simp] theorem mul_eq_mul_left_iff {M₀ : Type u_1} [cancel_monoid_with_zero M₀] {a : M₀} {b : M₀}
    {c : M₀} : a * b = a * c ↔ b = c ∨ a = 0 :=
  sorry

/-- Pullback a `monoid_with_zero` class along an injective function. -/
protected def function.injective.cancel_monoid_with_zero {M₀ : Type u_1} {M₀' : Type u_3}
    [cancel_monoid_with_zero M₀] [HasZero M₀'] [Mul M₀'] [HasOne M₀'] (f : M₀' → M₀)
    (hf : function.injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ (x y : M₀'), f (x * y) = f x * f y) : cancel_monoid_with_zero M₀' :=
  cancel_monoid_with_zero.mk monoid.mul sorry monoid.one sorry sorry mul_zero_class.zero sorry sorry
    sorry sorry

/-- An element of a `cancel_monoid_with_zero` fixed by right multiplication by an element other
than one must be zero. -/
theorem eq_zero_of_mul_eq_self_right {M₀ : Type u_1} [cancel_monoid_with_zero M₀] {a : M₀} {b : M₀}
    (h₁ : b ≠ 1) (h₂ : a * b = a) : a = 0 :=
  classical.by_contradiction
    fun (ha : ¬a = 0) => h₁ (mul_left_cancel' ha (Eq.symm h₂ ▸ Eq.symm (mul_one a)))

/-- An element of a `cancel_monoid_with_zero` fixed by left multiplication by an element other
than one must be zero. -/
theorem eq_zero_of_mul_eq_self_left {M₀ : Type u_1} [cancel_monoid_with_zero M₀] {a : M₀} {b : M₀}
    (h₁ : b ≠ 1) (h₂ : b * a = a) : a = 0 :=
  classical.by_contradiction
    fun (ha : ¬a = 0) => h₁ (mul_right_cancel' ha (Eq.symm h₂ ▸ Eq.symm (one_mul a)))

theorem division_def {G : Type u} [div_inv_monoid G] (a : G) (b : G) : a / b = a * (b⁻¹) :=
  div_eq_mul_inv

/-- Pullback a `group_with_zero` class along an injective function. -/
protected def function.injective.group_with_zero {G₀ : Type u_2} {G₀' : Type u_4}
    [group_with_zero G₀] [HasZero G₀'] [Mul G₀'] [HasOne G₀'] [has_inv G₀'] (f : G₀' → G₀)
    (hf : function.injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ (x y : G₀'), f (x * y) = f x * f y) (inv : ∀ (x : G₀'), f (x⁻¹) = (f x⁻¹)) :
    group_with_zero G₀' :=
  group_with_zero.mk monoid_with_zero.mul sorry monoid_with_zero.one sorry sorry
    monoid_with_zero.zero sorry sorry has_inv.inv
    (div_inv_monoid.div._default monoid_with_zero.mul sorry monoid_with_zero.one sorry sorry
      has_inv.inv)
    sorry sorry sorry

/-- Pullback a `group_with_zero` class along an injective function. This is a version of
`function.injective.group_with_zero` that uses a specified `/` instead of the default
`a / b = a * b⁻¹`. -/
protected def function.injective.group_with_zero_div {G₀ : Type u_2} {G₀' : Type u_4}
    [group_with_zero G₀] [HasZero G₀'] [Mul G₀'] [HasOne G₀'] [has_inv G₀'] [Div G₀'] (f : G₀' → G₀)
    (hf : function.injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ (x y : G₀'), f (x * y) = f x * f y) (inv : ∀ (x : G₀'), f (x⁻¹) = (f x⁻¹))
    (div : ∀ (x y : G₀'), f (x / y) = f x / f y) : group_with_zero G₀' :=
  group_with_zero.mk monoid_with_zero.mul sorry monoid_with_zero.one sorry sorry
    monoid_with_zero.zero sorry sorry div_inv_monoid.inv div_inv_monoid.div sorry sorry sorry

/-- Pushforward a `group_with_zero` class along an surjective function. -/
protected def function.surjective.group_with_zero {G₀ : Type u_2} {G₀' : Type u_4}
    [group_with_zero G₀] [HasZero G₀'] [Mul G₀'] [HasOne G₀'] [has_inv G₀'] (h01 : 0 ≠ 1)
    (f : G₀ → G₀') (hf : function.surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ (x y : G₀), f (x * y) = f x * f y) (inv : ∀ (x : G₀), f (x⁻¹) = (f x⁻¹)) :
    group_with_zero G₀' :=
  group_with_zero.mk monoid_with_zero.mul sorry monoid_with_zero.one sorry sorry
    monoid_with_zero.zero sorry sorry has_inv.inv
    (div_inv_monoid.div._default monoid_with_zero.mul sorry monoid_with_zero.one sorry sorry
      has_inv.inv)
    sorry sorry sorry

/-- Pushforward a `group_with_zero` class along a surjective function. This is a version of
`function.surjective.group_with_zero` that uses a specified `/` instead of the default
`a / b = a * b⁻¹`. -/
protected def function.surjective.group_with_zero_div {G₀ : Type u_2} {G₀' : Type u_4}
    [group_with_zero G₀] [HasZero G₀'] [Mul G₀'] [HasOne G₀'] [has_inv G₀'] [Div G₀'] (h01 : 0 ≠ 1)
    (f : G₀ → G₀') (hf : function.surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ (x y : G₀), f (x * y) = f x * f y) (inv : ∀ (x : G₀), f (x⁻¹) = (f x⁻¹))
    (div : ∀ (x y : G₀), f (x / y) = f x / f y) : group_with_zero G₀' :=
  group_with_zero.mk div_inv_monoid.mul sorry div_inv_monoid.one sorry sorry group_with_zero.zero
    sorry sorry div_inv_monoid.inv div_inv_monoid.div sorry sorry sorry

@[simp] theorem mul_inv_cancel_right' {G₀ : Type u_2} [group_with_zero G₀] {b : G₀} (h : b ≠ 0)
    (a : G₀) : a * b * (b⁻¹) = a :=
  sorry

@[simp] theorem mul_inv_cancel_left' {G₀ : Type u_2} [group_with_zero G₀] {a : G₀} (h : a ≠ 0)
    (b : G₀) : a * (a⁻¹ * b) = b :=
  sorry

theorem inv_ne_zero {G₀ : Type u_2} [group_with_zero G₀] {a : G₀} (h : a ≠ 0) : a⁻¹ ≠ 0 := sorry

@[simp] theorem inv_mul_cancel {G₀ : Type u_2} [group_with_zero G₀] {a : G₀} (h : a ≠ 0) :
    a⁻¹ * a = 1 :=
  sorry

@[simp] theorem inv_mul_cancel_right' {G₀ : Type u_2} [group_with_zero G₀] {b : G₀} (h : b ≠ 0)
    (a : G₀) : a * (b⁻¹) * b = a :=
  sorry

@[simp] theorem inv_mul_cancel_left' {G₀ : Type u_2} [group_with_zero G₀] {a : G₀} (h : a ≠ 0)
    (b : G₀) : a⁻¹ * (a * b) = b :=
  sorry

@[simp] theorem inv_one {G₀ : Type u_2} [group_with_zero G₀] : 1⁻¹ = 1 := sorry

@[simp] theorem inv_inv' {G₀ : Type u_2} [group_with_zero G₀] (a : G₀) : a⁻¹⁻¹ = a := sorry

/-- Multiplying `a` by itself and then by its inverse results in `a`
(whether or not `a` is zero). -/
@[simp] theorem mul_self_mul_inv {G₀ : Type u_2} [group_with_zero G₀] (a : G₀) :
    a * a * (a⁻¹) = a :=
  sorry

/-- Multiplying `a` by its inverse and then by itself results in `a`
(whether or not `a` is zero). -/
@[simp] theorem mul_inv_mul_self {G₀ : Type u_2} [group_with_zero G₀] (a : G₀) :
    a * (a⁻¹) * a = a :=
  sorry

/-- Multiplying `a⁻¹` by `a` twice results in `a` (whether or not `a`
is zero). -/
@[simp] theorem inv_mul_mul_self {G₀ : Type u_2} [group_with_zero G₀] (a : G₀) : a⁻¹ * a * a = a :=
  sorry

/-- Multiplying `a` by itself and then dividing by itself results in
`a` (whether or not `a` is zero). -/
@[simp] theorem mul_self_div_self {G₀ : Type u_2} [group_with_zero G₀] (a : G₀) : a * a / a = a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a * a / a = a)) (div_eq_mul_inv (a * a) a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * a * (a⁻¹) = a)) (mul_self_mul_inv a))) (Eq.refl a))

/-- Dividing `a` by itself and then multiplying by itself results in
`a` (whether or not `a` is zero). -/
@[simp] theorem div_self_mul_self {G₀ : Type u_2} [group_with_zero G₀] (a : G₀) : a / a * a = a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a / a * a = a)) (div_eq_mul_inv a a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * (a⁻¹) * a = a)) (mul_inv_mul_self a))) (Eq.refl a))

theorem inv_involutive' {G₀ : Type u_2} [group_with_zero G₀] : function.involutive has_inv.inv :=
  inv_inv'

theorem eq_inv_of_mul_right_eq_one {G₀ : Type u_2} [group_with_zero G₀] {a : G₀} {b : G₀}
    (h : a * b = 1) : b = (a⁻¹) :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (b = (a⁻¹)))
        (Eq.symm (inv_mul_cancel_left' (left_ne_zero_of_mul_eq_one h) b))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a⁻¹ * (a * b) = (a⁻¹))) h))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a⁻¹ * 1 = (a⁻¹))) (mul_one (a⁻¹)))) (Eq.refl (a⁻¹))))

theorem eq_inv_of_mul_left_eq_one {G₀ : Type u_2} [group_with_zero G₀] {a : G₀} {b : G₀}
    (h : a * b = 1) : a = (b⁻¹) :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (a = (b⁻¹)))
        (Eq.symm (mul_inv_cancel_right' (right_ne_zero_of_mul_eq_one h) a))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * b * (b⁻¹) = (b⁻¹))) h))
      (eq.mpr (id (Eq._oldrec (Eq.refl (1 * (b⁻¹) = (b⁻¹))) (one_mul (b⁻¹)))) (Eq.refl (b⁻¹))))

theorem inv_injective' {G₀ : Type u_2} [group_with_zero G₀] : function.injective has_inv.inv :=
  function.involutive.injective inv_involutive'

@[simp] theorem inv_inj' {G₀ : Type u_2} [group_with_zero G₀] {g : G₀} {h : G₀} :
    g⁻¹ = (h⁻¹) ↔ g = h :=
  function.injective.eq_iff inv_injective'

theorem inv_eq_iff {G₀ : Type u_2} [group_with_zero G₀] {g : G₀} {h : G₀} : g⁻¹ = h ↔ h⁻¹ = g :=
  eq.mpr (id (Eq._oldrec (Eq.refl (g⁻¹ = h ↔ h⁻¹ = g)) (Eq.symm (propext inv_inj'))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (g⁻¹⁻¹ = (h⁻¹) ↔ h⁻¹ = g)) (propext eq_comm)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (h⁻¹ = (g⁻¹⁻¹) ↔ h⁻¹ = g)) (inv_inv' g)))
        (iff.refl (h⁻¹ = g))))

@[simp] theorem inv_eq_one' {G₀ : Type u_2} [group_with_zero G₀] {g : G₀} : g⁻¹ = 1 ↔ g = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (g⁻¹ = 1 ↔ g = 1)) (propext inv_eq_iff)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (1⁻¹ = g ↔ g = 1)) inv_one))
      (eq.mpr (id (Eq._oldrec (Eq.refl (1 = g ↔ g = 1)) (propext eq_comm))) (iff.refl (g = 1))))

namespace units


/-- Embed a non-zero element of a `group_with_zero` into the unit group.
  By combining this function with the operations on units,
  or the `/ₚ` operation, it is possible to write a division
  as a partial function with three arguments. -/
def mk0 {G₀ : Type u_2} [group_with_zero G₀] (a : G₀) (ha : a ≠ 0) : units G₀ :=
  mk a (a⁻¹) (mul_inv_cancel ha) (inv_mul_cancel ha)

@[simp] theorem coe_mk0 {G₀ : Type u_2} [group_with_zero G₀] {a : G₀} (h : a ≠ 0) :
    ↑(mk0 a h) = a :=
  rfl

@[simp] theorem mk0_coe {G₀ : Type u_2} [group_with_zero G₀] (u : units G₀) (h : ↑u ≠ 0) :
    mk0 (↑u) h = u :=
  ext rfl

@[simp] theorem coe_inv' {G₀ : Type u_2} [group_with_zero G₀] (u : units G₀) : ↑(u⁻¹) = (↑u⁻¹) :=
  eq_inv_of_mul_left_eq_one (inv_mul u)

@[simp] theorem mul_inv' {G₀ : Type u_2} [group_with_zero G₀] (u : units G₀) : ↑u * (↑u⁻¹) = 1 :=
  mul_inv_cancel (ne_zero u)

@[simp] theorem inv_mul' {G₀ : Type u_2} [group_with_zero G₀] (u : units G₀) : ↑u⁻¹ * ↑u = 1 :=
  inv_mul_cancel (ne_zero u)

@[simp] theorem mk0_inj {G₀ : Type u_2} [group_with_zero G₀] {a : G₀} {b : G₀} (ha : a ≠ 0)
    (hb : b ≠ 0) : mk0 a ha = mk0 b hb ↔ a = b :=
  { mp :=
      fun (h : mk0 a ha = mk0 b hb) => mk.inj_arrow h fun (h_1 : a = b) (h_2 : a⁻¹ = (b⁻¹)) => h_1,
    mpr := fun (h : a = b) => ext h }

@[simp] theorem exists_iff_ne_zero {G₀ : Type u_2} [group_with_zero G₀] {x : G₀} :
    (∃ (u : units G₀), ↑u = x) ↔ x ≠ 0 :=
  sorry

end units


theorem is_unit.mk0 {G₀ : Type u_2} [group_with_zero G₀] (x : G₀) (hx : x ≠ 0) : is_unit x :=
  is_unit_unit (units.mk0 x hx)

theorem is_unit_iff_ne_zero {G₀ : Type u_2} [group_with_zero G₀] {x : G₀} : is_unit x ↔ x ≠ 0 :=
  units.exists_iff_ne_zero

protected instance group_with_zero.no_zero_divisors {G₀ : Type u_2} [group_with_zero G₀] :
    no_zero_divisors G₀ :=
  no_zero_divisors.mk
    fun (a b : G₀) (h : a * b = 0) =>
      imp_of_not_imp_not (a * b = 0) (a = 0 ∨ b = 0)
        (eq.mpr (id (imp_congr_eq (push_neg.not_or_eq (a = 0) (b = 0)) (Eq.refl (¬a * b = 0))))
          (eq.mpr
            (id
              (imp_congr_eq
                ((fun (a a_1 : Prop) (e_1 : a = a_1) (b b_1 : Prop) (e_2 : b = b_1) =>
                    congr (congr_arg And e_1) e_2)
                  (¬a = 0) (a ≠ 0) (propext (push_neg.not_eq a 0)) (¬b = 0) (b ≠ 0)
                  (propext (push_neg.not_eq b 0)))
                (propext (push_neg.not_eq (a * b) 0))))
            fun (h : a ≠ 0 ∧ b ≠ 0) =>
              units.ne_zero (units.mk0 a (and.left h) * units.mk0 b (and.right h))))
        h

protected instance group_with_zero.cancel_monoid_with_zero {G₀ : Type u_2} [group_with_zero G₀] :
    cancel_monoid_with_zero G₀ :=
  cancel_monoid_with_zero.mk group_with_zero.mul group_with_zero.mul_assoc group_with_zero.one
    group_with_zero.one_mul group_with_zero.mul_one group_with_zero.zero group_with_zero.zero_mul
    group_with_zero.mul_zero sorry sorry

theorem mul_inv_rev' {G₀ : Type u_2} [group_with_zero G₀] (x : G₀) (y : G₀) :
    x * y⁻¹ = y⁻¹ * (x⁻¹) :=
  sorry

@[simp] theorem div_self {G₀ : Type u_2} [group_with_zero G₀] {a : G₀} (h : a ≠ 0) : a / a = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a / a = 1)) (div_eq_mul_inv a a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * (a⁻¹) = 1)) (mul_inv_cancel h))) (Eq.refl 1))

@[simp] theorem div_one {G₀ : Type u_2} [group_with_zero G₀] (a : G₀) : a / 1 = a := sorry

@[simp] theorem zero_div {G₀ : Type u_2} [group_with_zero G₀] (a : G₀) : 0 / a = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (0 / a = 0)) (div_eq_mul_inv 0 a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (0 * (a⁻¹) = 0)) (zero_mul (a⁻¹)))) (Eq.refl 0))

@[simp] theorem div_zero {G₀ : Type u_2} [group_with_zero G₀] (a : G₀) : a / 0 = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a / 0 = 0)) (div_eq_mul_inv a 0)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * (0⁻¹) = 0)) inv_zero))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a * 0 = 0)) (mul_zero a))) (Eq.refl 0)))

@[simp] theorem div_mul_cancel {G₀ : Type u_2} [group_with_zero G₀] (a : G₀) {b : G₀} (h : b ≠ 0) :
    a / b * b = a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a / b * b = a)) (div_eq_mul_inv a b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * (b⁻¹) * b = a)) (inv_mul_cancel_right' h a))) (Eq.refl a))

theorem div_mul_cancel_of_imp {G₀ : Type u_2} [group_with_zero G₀] {a : G₀} {b : G₀}
    (h : b = 0 → a = 0) : a / b * b = a :=
  sorry

@[simp] theorem mul_div_cancel {G₀ : Type u_2} [group_with_zero G₀] (a : G₀) {b : G₀} (h : b ≠ 0) :
    a * b / b = a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a * b / b = a)) (div_eq_mul_inv (a * b) b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * b * (b⁻¹) = a)) (mul_inv_cancel_right' h a))) (Eq.refl a))

theorem mul_div_cancel_of_imp {G₀ : Type u_2} [group_with_zero G₀] {a : G₀} {b : G₀}
    (h : b = 0 → a = 0) : a * b / b = a :=
  sorry

@[simp] theorem div_self_mul_self' {G₀ : Type u_2} [group_with_zero G₀] (a : G₀) :
    a / (a * a) = (a⁻¹) :=
  sorry

theorem div_eq_mul_one_div {G₀ : Type u_2} [group_with_zero G₀] (a : G₀) (b : G₀) :
    a / b = a * (1 / b) :=
  sorry

theorem mul_one_div_cancel {G₀ : Type u_2} [group_with_zero G₀] {a : G₀} (h : a ≠ 0) :
    a * (1 / a) = 1 :=
  sorry

theorem one_div_mul_cancel {G₀ : Type u_2} [group_with_zero G₀] {a : G₀} (h : a ≠ 0) :
    1 / a * a = 1 :=
  sorry

theorem one_div_one {G₀ : Type u_2} [group_with_zero G₀] : 1 / 1 = 1 :=
  div_self (ne.symm zero_ne_one)

theorem one_div_ne_zero {G₀ : Type u_2} [group_with_zero G₀] {a : G₀} (h : a ≠ 0) : 1 / a ≠ 0 :=
  sorry

theorem eq_one_div_of_mul_eq_one {G₀ : Type u_2} [group_with_zero G₀] {a : G₀} {b : G₀}
    (h : a * b = 1) : b = 1 / a :=
  sorry

theorem eq_one_div_of_mul_eq_one_left {G₀ : Type u_2} [group_with_zero G₀] {a : G₀} {b : G₀}
    (h : b * a = 1) : b = 1 / a :=
  sorry

@[simp] theorem one_div_div {G₀ : Type u_2} [group_with_zero G₀] (a : G₀) (b : G₀) :
    1 / (a / b) = b / a :=
  sorry

theorem one_div_one_div {G₀ : Type u_2} [group_with_zero G₀] (a : G₀) : 1 / (1 / a) = a := sorry

theorem eq_of_one_div_eq_one_div {G₀ : Type u_2} [group_with_zero G₀] {a : G₀} {b : G₀}
    (h : 1 / a = 1 / b) : a = b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a = b)) (Eq.symm (one_div_one_div a))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (1 / (1 / a) = b)) h))
      (eq.mpr (id (Eq._oldrec (Eq.refl (1 / (1 / b) = b)) (one_div_one_div b))) (Eq.refl b)))

@[simp] theorem inv_eq_zero {G₀ : Type u_2} [group_with_zero G₀] {a : G₀} : a⁻¹ = 0 ↔ a = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a⁻¹ = 0 ↔ a = 0)) (propext inv_eq_iff)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (0⁻¹ = a ↔ a = 0)) inv_zero))
      (eq.mpr (id (Eq._oldrec (Eq.refl (0 = a ↔ a = 0)) (propext eq_comm))) (iff.refl (a = 0))))

@[simp] theorem zero_eq_inv {G₀ : Type u_2} [group_with_zero G₀] {a : G₀} : 0 = (a⁻¹) ↔ 0 = a :=
  iff.trans eq_comm (iff.trans inv_eq_zero eq_comm)

theorem one_div_mul_one_div_rev {G₀ : Type u_2} [group_with_zero G₀] (a : G₀) (b : G₀) :
    1 / a * (1 / b) = 1 / (b * a) :=
  sorry

theorem divp_eq_div {G₀ : Type u_2} [group_with_zero G₀] (a : G₀) (u : units G₀) :
    a /ₚ u = a / ↑u :=
  sorry

@[simp] theorem divp_mk0 {G₀ : Type u_2} [group_with_zero G₀] (a : G₀) {b : G₀} (hb : b ≠ 0) :
    a /ₚ units.mk0 b hb = a / b :=
  divp_eq_div a (units.mk0 b hb)

theorem inv_div {G₀ : Type u_2} [group_with_zero G₀] {a : G₀} {b : G₀} : a / b⁻¹ = b / a := sorry

theorem inv_div_left {G₀ : Type u_2} [group_with_zero G₀] {a : G₀} {b : G₀} : a⁻¹ / b = (b * a⁻¹) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a⁻¹ / b = (b * a⁻¹))) (mul_inv_rev' b a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a⁻¹ / b = a⁻¹ * (b⁻¹))) (div_eq_mul_inv (a⁻¹) b)))
      (Eq.refl (a⁻¹ * (b⁻¹))))

theorem div_ne_zero {G₀ : Type u_2} [group_with_zero G₀] {a : G₀} {b : G₀} (ha : a ≠ 0)
    (hb : b ≠ 0) : a / b ≠ 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a / b ≠ 0)) (div_eq_mul_inv a b)))
    (mul_ne_zero ha (inv_ne_zero hb))

@[simp] theorem div_eq_zero_iff {G₀ : Type u_2} [group_with_zero G₀] {a : G₀} {b : G₀} :
    a / b = 0 ↔ a = 0 ∨ b = 0 :=
  sorry

theorem div_ne_zero_iff {G₀ : Type u_2} [group_with_zero G₀] {a : G₀} {b : G₀} :
    a / b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 :=
  iff.trans (not_congr div_eq_zero_iff) not_or_distrib

theorem div_left_inj' {G₀ : Type u_2} [group_with_zero G₀] {a : G₀} {b : G₀} {c : G₀} (hc : c ≠ 0) :
    a / c = b / c ↔ a = b :=
  sorry

theorem div_eq_iff_mul_eq {G₀ : Type u_2} [group_with_zero G₀] {a : G₀} {b : G₀} {c : G₀}
    (hb : b ≠ 0) : a / b = c ↔ c * b = a :=
  sorry

theorem eq_div_iff_mul_eq {G₀ : Type u_2} [group_with_zero G₀] {a : G₀} {b : G₀} {c : G₀}
    (hc : c ≠ 0) : a = b / c ↔ a * c = b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a = b / c ↔ a * c = b)) (propext eq_comm)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b / c = a ↔ a * c = b)) (propext (div_eq_iff_mul_eq hc))))
      (iff.refl (a * c = b)))

theorem div_eq_of_eq_mul {G₀ : Type u_2} [group_with_zero G₀] {x : G₀} (hx : x ≠ 0) {y : G₀}
    {z : G₀} (h : y = z * x) : y / x = z :=
  iff.mpr (div_eq_iff_mul_eq hx) (Eq.symm h)

theorem eq_div_of_mul_eq {G₀ : Type u_2} [group_with_zero G₀] {x : G₀} (hx : x ≠ 0) {y : G₀}
    {z : G₀} (h : z * x = y) : z = y / x :=
  Eq.symm (div_eq_of_eq_mul hx (Eq.symm h))

theorem eq_of_div_eq_one {G₀ : Type u_2} [group_with_zero G₀] {a : G₀} {b : G₀} (h : a / b = 1) :
    a = b :=
  sorry

theorem div_eq_one_iff_eq {G₀ : Type u_2} [group_with_zero G₀] {a : G₀} {b : G₀} (hb : b ≠ 0) :
    a / b = 1 ↔ a = b :=
  { mp := eq_of_div_eq_one, mpr := fun (h : a = b) => Eq.symm h ▸ div_self hb }

theorem div_mul_left {G₀ : Type u_2} [group_with_zero G₀] {a : G₀} {b : G₀} (hb : b ≠ 0) :
    b / (a * b) = 1 / a :=
  sorry

theorem mul_div_mul_right {G₀ : Type u_2} [group_with_zero G₀] (a : G₀) (b : G₀) {c : G₀}
    (hc : c ≠ 0) : a * c / (b * c) = a / b :=
  sorry

theorem mul_mul_div {G₀ : Type u_2} [group_with_zero G₀] (a : G₀) {b : G₀} (hb : b ≠ 0) :
    a = a * b * (1 / b) :=
  sorry

protected instance comm_group_with_zero.comm_cancel_monoid_with_zero {G₀ : Type u_2}
    [comm_group_with_zero G₀] : comm_cancel_monoid_with_zero G₀ :=
  comm_cancel_monoid_with_zero.mk cancel_monoid_with_zero.mul sorry cancel_monoid_with_zero.one
    sorry sorry sorry cancel_monoid_with_zero.zero sorry sorry sorry sorry

/-- Pullback a `comm_group_with_zero` class along an injective function. -/
protected def function.injective.comm_group_with_zero {G₀ : Type u_2} {G₀' : Type u_4}
    [comm_group_with_zero G₀] [HasZero G₀'] [Mul G₀'] [HasOne G₀'] [has_inv G₀'] (f : G₀' → G₀)
    (hf : function.injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ (x y : G₀'), f (x * y) = f x * f y) (inv : ∀ (x : G₀'), f (x⁻¹) = (f x⁻¹)) :
    comm_group_with_zero G₀' :=
  comm_group_with_zero.mk group_with_zero.mul sorry group_with_zero.one sorry sorry sorry
    group_with_zero.zero sorry sorry group_with_zero.inv group_with_zero.div sorry sorry sorry

/-- Pullback a `comm_group_with_zero` class along an injective function. -/
protected def function.injective.comm_group_with_zero_div {G₀ : Type u_2} {G₀' : Type u_4}
    [comm_group_with_zero G₀] [HasZero G₀'] [Mul G₀'] [HasOne G₀'] [has_inv G₀'] [Div G₀']
    (f : G₀' → G₀) (hf : function.injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ (x y : G₀'), f (x * y) = f x * f y) (inv : ∀ (x : G₀'), f (x⁻¹) = (f x⁻¹))
    (div : ∀ (x y : G₀'), f (x / y) = f x / f y) : comm_group_with_zero G₀' :=
  comm_group_with_zero.mk group_with_zero.mul sorry group_with_zero.one sorry sorry sorry
    group_with_zero.zero sorry sorry group_with_zero.inv group_with_zero.div sorry sorry sorry

/-- Pushforward a `comm_group_with_zero` class along an surjective function. -/
protected def function.surjective.comm_group_with_zero {G₀ : Type u_2} {G₀' : Type u_4}
    [comm_group_with_zero G₀] [HasZero G₀'] [Mul G₀'] [HasOne G₀'] [has_inv G₀'] (h01 : 0 ≠ 1)
    (f : G₀ → G₀') (hf : function.surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ (x y : G₀), f (x * y) = f x * f y) (inv : ∀ (x : G₀), f (x⁻¹) = (f x⁻¹)) :
    comm_group_with_zero G₀' :=
  comm_group_with_zero.mk group_with_zero.mul sorry group_with_zero.one sorry sorry sorry
    group_with_zero.zero sorry sorry group_with_zero.inv group_with_zero.div sorry sorry sorry

/-- Pushforward a `comm_group_with_zero` class along a surjective function. -/
protected def function.surjective.comm_group_with_zero_div {G₀ : Type u_2} {G₀' : Type u_4}
    [comm_group_with_zero G₀] [HasZero G₀'] [Mul G₀'] [HasOne G₀'] [has_inv G₀'] [Div G₀']
    (h01 : 0 ≠ 1) (f : G₀ → G₀') (hf : function.surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ (x y : G₀), f (x * y) = f x * f y) (inv : ∀ (x : G₀), f (x⁻¹) = (f x⁻¹))
    (div : ∀ (x y : G₀), f (x / y) = f x / f y) : comm_group_with_zero G₀' :=
  comm_group_with_zero.mk group_with_zero.mul sorry group_with_zero.one sorry sorry sorry
    group_with_zero.zero sorry sorry group_with_zero.inv group_with_zero.div sorry sorry sorry

theorem mul_inv' {G₀ : Type u_2} [comm_group_with_zero G₀] {a : G₀} {b : G₀} :
    a * b⁻¹ = a⁻¹ * (b⁻¹) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a * b⁻¹ = a⁻¹ * (b⁻¹))) (mul_inv_rev' a b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b⁻¹ * (a⁻¹) = a⁻¹ * (b⁻¹))) (mul_comm (b⁻¹) (a⁻¹))))
      (Eq.refl (a⁻¹ * (b⁻¹))))

theorem one_div_mul_one_div {G₀ : Type u_2} [comm_group_with_zero G₀] (a : G₀) (b : G₀) :
    1 / a * (1 / b) = 1 / (a * b) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (1 / a * (1 / b) = 1 / (a * b))) (one_div_mul_one_div_rev a b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (1 / (b * a) = 1 / (a * b))) (mul_comm b a)))
      (Eq.refl (1 / (a * b))))

theorem div_mul_right {G₀ : Type u_2} [comm_group_with_zero G₀] {a : G₀} (b : G₀) (ha : a ≠ 0) :
    a / (a * b) = 1 / b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a / (a * b) = 1 / b)) (mul_comm a b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a / (b * a) = 1 / b)) (div_mul_left ha))) (Eq.refl (1 / b)))

theorem mul_div_cancel_left_of_imp {G₀ : Type u_2} [comm_group_with_zero G₀] {a : G₀} {b : G₀}
    (h : a = 0 → b = 0) : a * b / a = b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a * b / a = b)) (mul_comm a b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b * a / a = b)) (mul_div_cancel_of_imp h))) (Eq.refl b))

theorem mul_div_cancel_left {G₀ : Type u_2} [comm_group_with_zero G₀] {a : G₀} (b : G₀)
    (ha : a ≠ 0) : a * b / a = b :=
  mul_div_cancel_left_of_imp fun (h : a = 0) => false.elim (ha h)

theorem mul_div_cancel_of_imp' {G₀ : Type u_2} [comm_group_with_zero G₀] {a : G₀} {b : G₀}
    (h : b = 0 → a = 0) : b * (a / b) = a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (b * (a / b) = a)) (mul_comm b (a / b))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a / b * b = a)) (div_mul_cancel_of_imp h))) (Eq.refl a))

theorem mul_div_cancel' {G₀ : Type u_2} [comm_group_with_zero G₀] (a : G₀) {b : G₀} (hb : b ≠ 0) :
    b * (a / b) = a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (b * (a / b) = a)) (mul_comm b (a / b))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a / b * b = a)) (div_mul_cancel a hb))) (Eq.refl a))

theorem div_mul_div {G₀ : Type u_2} [comm_group_with_zero G₀] (a : G₀) (b : G₀) (c : G₀) (d : G₀) :
    a / b * (c / d) = a * c / (b * d) :=
  sorry

theorem mul_div_mul_left {G₀ : Type u_2} [comm_group_with_zero G₀] (a : G₀) (b : G₀) {c : G₀}
    (hc : c ≠ 0) : c * a / (c * b) = a / b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (c * a / (c * b) = a / b)) (mul_comm c a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * c / (c * b) = a / b)) (mul_comm c b)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a * c / (b * c) = a / b)) (mul_div_mul_right a b hc)))
        (Eq.refl (a / b))))

theorem div_mul_eq_mul_div {G₀ : Type u_2} [comm_group_with_zero G₀] (a : G₀) (b : G₀) (c : G₀) :
    b / c * a = b * a / c :=
  sorry

theorem div_mul_eq_mul_div_comm {G₀ : Type u_2} [comm_group_with_zero G₀] (a : G₀) (b : G₀)
    (c : G₀) : b / c * a = b * (a / c) :=
  sorry

theorem mul_eq_mul_of_div_eq_div {G₀ : Type u_2} [comm_group_with_zero G₀] (a : G₀) {b : G₀}
    (c : G₀) {d : G₀} (hb : b ≠ 0) (hd : d ≠ 0) (h : a / b = c / d) : a * d = c * b :=
  sorry

theorem div_div_eq_mul_div {G₀ : Type u_2} [comm_group_with_zero G₀] (a : G₀) (b : G₀) (c : G₀) :
    a / (b / c) = a * c / b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a / (b / c) = a * c / b)) (div_eq_mul_one_div a (b / c))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * (1 / (b / c)) = a * c / b)) (one_div_div b c)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a * (c / b) = a * c / b)) (Eq.symm mul_div_assoc)))
        (Eq.refl (a * c / b))))

theorem div_div_eq_div_mul {G₀ : Type u_2} [comm_group_with_zero G₀] (a : G₀) (b : G₀) (c : G₀) :
    a / b / c = a / (b * c) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a / b / c = a / (b * c))) (div_eq_mul_one_div (a / b) c)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a / b * (1 / c) = a / (b * c))) (div_mul_div a b 1 c)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a * 1 / (b * c) = a / (b * c))) (mul_one a)))
        (Eq.refl (a / (b * c)))))

theorem div_div_div_div_eq {G₀ : Type u_2} [comm_group_with_zero G₀] (a : G₀) {b : G₀} {c : G₀}
    {d : G₀} : a / b / (c / d) = a * d / (b * c) :=
  sorry

theorem div_mul_eq_div_mul_one_div {G₀ : Type u_2} [comm_group_with_zero G₀] (a : G₀) (b : G₀)
    (c : G₀) : a / (b * c) = a / b * (1 / c) :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (a / (b * c) = a / b * (1 / c))) (Eq.symm (div_div_eq_div_mul a b c))))
    (eq.mpr
      (id
        (Eq._oldrec (Eq.refl (a / b / c = a / b * (1 / c)))
          (Eq.symm (div_eq_mul_one_div (a / b) c))))
      (Eq.refl (a / b / c)))

/-- Dividing `a` by the result of dividing `a` by itself results in
`a` (whether or not `a` is zero). -/
@[simp] theorem div_div_self {G₀ : Type u_2} [comm_group_with_zero G₀] (a : G₀) : a / (a / a) = a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a / (a / a) = a)) (div_div_eq_mul_div a a a)))
    (mul_self_div_self a)

theorem ne_zero_of_one_div_ne_zero {G₀ : Type u_2} [comm_group_with_zero G₀] {a : G₀}
    (h : 1 / a ≠ 0) : a ≠ 0 :=
  fun (ha : a = 0) =>
    absurd (Eq.refl 0)
      (eq.mp (Eq._oldrec (Eq.refl (1 / 0 ≠ 0)) (div_zero 1))
        (eq.mp (Eq._oldrec (Eq.refl (1 / a ≠ 0)) ha) h))

theorem eq_zero_of_one_div_eq_zero {G₀ : Type u_2} [comm_group_with_zero G₀] {a : G₀}
    (h : 1 / a = 0) : a = 0 :=
  classical.by_cases (fun (ha : a = 0) => ha) fun (ha : ¬a = 0) => false.elim (one_div_ne_zero ha h)

theorem div_helper {G₀ : Type u_2} [comm_group_with_zero G₀] {a : G₀} (b : G₀) (h : a ≠ 0) :
    1 / (a * b) * a = 1 / b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (1 / (a * b) * a = 1 / b)) (div_mul_eq_mul_div a 1 (a * b))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (1 * a / (a * b) = 1 / b)) (one_mul a)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a / (a * b) = 1 / b)) (div_mul_right b h)))
        (Eq.refl (1 / b))))

theorem div_eq_inv_mul {G₀ : Type u_2} [comm_group_with_zero G₀] {a : G₀} {b : G₀} :
    a / b = b⁻¹ * a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a / b = b⁻¹ * a)) (div_eq_mul_inv a b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * (b⁻¹) = b⁻¹ * a)) (mul_comm a (b⁻¹))))
      (Eq.refl (b⁻¹ * a)))

theorem mul_div_right_comm {G₀ : Type u_2} [comm_group_with_zero G₀] (a : G₀) (b : G₀) (c : G₀) :
    a * b / c = a / c * b :=
  sorry

theorem mul_comm_div' {G₀ : Type u_2} [comm_group_with_zero G₀] (a : G₀) (b : G₀) (c : G₀) :
    a / b * c = a * (c / b) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a / b * c = a * (c / b))) (Eq.symm mul_div_assoc)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a / b * c = a * c / b)) (mul_div_right_comm a c b)))
      (Eq.refl (a / b * c)))

theorem div_mul_comm' {G₀ : Type u_2} [comm_group_with_zero G₀] (a : G₀) (b : G₀) (c : G₀) :
    a / b * c = c / b * a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a / b * c = c / b * a)) (div_mul_eq_mul_div c a b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * c / b = c / b * a)) (mul_comm a c)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (c * a / b = c / b * a)) (mul_div_right_comm c a b)))
        (Eq.refl (c / b * a))))

theorem mul_div_comm {G₀ : Type u_2} [comm_group_with_zero G₀] (a : G₀) (b : G₀) (c : G₀) :
    a * (b / c) = b * (a / c) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a * (b / c) = b * (a / c))) (Eq.symm mul_div_assoc)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * b / c = b * (a / c))) (mul_comm a b)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (b * a / c = b * (a / c))) mul_div_assoc))
        (Eq.refl (b * (a / c)))))

theorem div_right_comm {G₀ : Type u_2} [comm_group_with_zero G₀] {b : G₀} {c : G₀} (a : G₀) :
    a / b / c = a / c / b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a / b / c = a / c / b)) (div_div_eq_div_mul a b c)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a / (b * c) = a / c / b)) (div_div_eq_div_mul a c b)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a / (b * c) = a / (c * b))) (mul_comm b c)))
        (Eq.refl (a / (c * b)))))

theorem div_div_div_cancel_right {G₀ : Type u_2} [comm_group_with_zero G₀] {b : G₀} {c : G₀}
    (a : G₀) (hc : c ≠ 0) : a / c / (b / c) = a / b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a / c / (b / c) = a / b)) (div_div_eq_mul_div (a / c) b c)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a / c * c / b = a / b)) (div_mul_cancel a hc)))
      (Eq.refl (a / b)))

theorem div_mul_div_cancel {G₀ : Type u_2} [comm_group_with_zero G₀] {b : G₀} {c : G₀} (a : G₀)
    (hc : c ≠ 0) : a / c * (c / b) = a / b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a / c * (c / b) = a / b)) (Eq.symm mul_div_assoc)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a / c * c / b = a / b)) (div_mul_cancel a hc)))
      (Eq.refl (a / b)))

theorem div_eq_div_iff {G₀ : Type u_2} [comm_group_with_zero G₀] {a : G₀} {b : G₀} {c : G₀} {d : G₀}
    (hb : b ≠ 0) (hd : d ≠ 0) : a / b = c / d ↔ a * d = c * b :=
  sorry

theorem div_eq_iff {G₀ : Type u_2} [comm_group_with_zero G₀] {a : G₀} {b : G₀} {c : G₀}
    (hb : b ≠ 0) : a / b = c ↔ a = c * b :=
  iff.trans (div_eq_iff_mul_eq hb) eq_comm

theorem eq_div_iff {G₀ : Type u_2} [comm_group_with_zero G₀] {a : G₀} {b : G₀} {c : G₀}
    (hb : b ≠ 0) : c = a / b ↔ c * b = a :=
  eq_div_iff_mul_eq hb

theorem div_div_cancel' {G₀ : Type u_2} [comm_group_with_zero G₀] {a : G₀} {b : G₀} (ha : a ≠ 0) :
    a / (a / b) = b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a / (a / b) = b)) (div_eq_mul_inv a (a / b))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * (a / b⁻¹) = b)) inv_div))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a * (b / a) = b)) (mul_div_cancel' b ha))) (Eq.refl b)))

namespace semiconj_by


@[simp] theorem zero_right {G₀ : Type u_2} [mul_zero_class G₀] (a : G₀) : semiconj_by a 0 0 := sorry

@[simp] theorem zero_left {G₀ : Type u_2} [mul_zero_class G₀] (x : G₀) (y : G₀) :
    semiconj_by 0 x y :=
  sorry

@[simp] theorem inv_symm_left_iff' {G₀ : Type u_2} [group_with_zero G₀] {a : G₀} {x : G₀} {y : G₀} :
    semiconj_by (a⁻¹) x y ↔ semiconj_by a y x :=
  sorry

theorem inv_symm_left' {G₀ : Type u_2} [group_with_zero G₀] {a : G₀} {x : G₀} {y : G₀}
    (h : semiconj_by a x y) : semiconj_by (a⁻¹) y x :=
  iff.mpr inv_symm_left_iff' h

theorem inv_right' {G₀ : Type u_2} [group_with_zero G₀] {a : G₀} {x : G₀} {y : G₀}
    (h : semiconj_by a x y) : semiconj_by a (x⁻¹) (y⁻¹) :=
  sorry

@[simp] theorem inv_right_iff' {G₀ : Type u_2} [group_with_zero G₀] {a : G₀} {x : G₀} {y : G₀} :
    semiconj_by a (x⁻¹) (y⁻¹) ↔ semiconj_by a x y :=
  { mp := fun (h : semiconj_by a (x⁻¹) (y⁻¹)) => inv_inv' x ▸ inv_inv' y ▸ inv_right' h,
    mpr := inv_right' }

theorem div_right {G₀ : Type u_2} [group_with_zero G₀] {a : G₀} {x : G₀} {y : G₀} {x' : G₀}
    {y' : G₀} (h : semiconj_by a x y) (h' : semiconj_by a x' y') :
    semiconj_by a (x / x') (y / y') :=
  eq.mpr (id (Eq._oldrec (Eq.refl (semiconj_by a (x / x') (y / y'))) (div_eq_mul_inv x x')))
    (eq.mpr (id (Eq._oldrec (Eq.refl (semiconj_by a (x * (x'⁻¹)) (y / y'))) (div_eq_mul_inv y y')))
      (mul_right h (inv_right' h')))

end semiconj_by


namespace commute


@[simp] theorem zero_right {G₀ : Type u_2} [mul_zero_class G₀] (a : G₀) : commute a 0 :=
  semiconj_by.zero_right a

@[simp] theorem zero_left {G₀ : Type u_2} [mul_zero_class G₀] (a : G₀) : commute 0 a :=
  semiconj_by.zero_left a a

@[simp] theorem inv_left_iff' {G₀ : Type u_2} [group_with_zero G₀] {a : G₀} {b : G₀} :
    commute (a⁻¹) b ↔ commute a b :=
  semiconj_by.inv_symm_left_iff'

theorem inv_left' {G₀ : Type u_2} [group_with_zero G₀] {a : G₀} {b : G₀} (h : commute a b) :
    commute (a⁻¹) b :=
  iff.mpr inv_left_iff' h

@[simp] theorem inv_right_iff' {G₀ : Type u_2} [group_with_zero G₀] {a : G₀} {b : G₀} :
    commute a (b⁻¹) ↔ commute a b :=
  semiconj_by.inv_right_iff'

theorem inv_right' {G₀ : Type u_2} [group_with_zero G₀] {a : G₀} {b : G₀} (h : commute a b) :
    commute a (b⁻¹) :=
  iff.mpr inv_right_iff' h

theorem inv_inv' {G₀ : Type u_2} [group_with_zero G₀] {a : G₀} {b : G₀} (h : commute a b) :
    commute (a⁻¹) (b⁻¹) :=
  inv_right' (inv_left' h)

@[simp] theorem div_right {G₀ : Type u_2} [group_with_zero G₀] {a : G₀} {b : G₀} {c : G₀}
    (hab : commute a b) (hac : commute a c) : commute a (b / c) :=
  semiconj_by.div_right hab hac

@[simp] theorem div_left {G₀ : Type u_2} [group_with_zero G₀] {a : G₀} {b : G₀} {c : G₀}
    (hac : commute a c) (hbc : commute b c) : commute (a / b) c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (commute (a / b) c)) (div_eq_mul_inv a b)))
    (mul_left hac (inv_left' hbc))

end commute


namespace monoid_with_zero_hom


theorem map_ne_zero {M₀ : Type u_1} {G₀ : Type u_2} [group_with_zero G₀] [monoid_with_zero M₀]
    [nontrivial M₀] (f : monoid_with_zero_hom G₀ M₀) {a : G₀} : coe_fn f a ≠ 0 ↔ a ≠ 0 :=
  { mp := fun (hfa : coe_fn f a ≠ 0) (ha : a = 0) => hfa (Eq.symm ha ▸ map_zero f),
    mpr := fun (ha : a ≠ 0) => is_unit.ne_zero (is_unit.map (to_monoid_hom f) (is_unit.mk0 a ha)) }

@[simp] theorem map_eq_zero {M₀ : Type u_1} {G₀ : Type u_2} [group_with_zero G₀]
    [monoid_with_zero M₀] [nontrivial M₀] (f : monoid_with_zero_hom G₀ M₀) {a : G₀} :
    coe_fn f a = 0 ↔ a = 0 :=
  iff.mp not_iff_not (map_ne_zero f)

/-- A monoid homomorphism between groups with zeros sending `0` to `0` sends `a⁻¹` to `(f a)⁻¹`. -/
@[simp] theorem map_inv' {G₀ : Type u_2} {G₀' : Type u_4} [group_with_zero G₀] [group_with_zero G₀']
    (f : monoid_with_zero_hom G₀ G₀') (a : G₀) : coe_fn f (a⁻¹) = (coe_fn f a⁻¹) :=
  sorry

@[simp] theorem map_div {G₀ : Type u_2} {G₀' : Type u_4} [group_with_zero G₀] [group_with_zero G₀']
    (f : monoid_with_zero_hom G₀ G₀') (a : G₀) (b : G₀) :
    coe_fn f (a / b) = coe_fn f a / coe_fn f b :=
  sorry

end monoid_with_zero_hom


@[simp] theorem monoid_hom.map_units_inv {M : Type u_1} {G₀ : Type u_2} [monoid M]
    [group_with_zero G₀] (f : M →* G₀) (u : units M) : coe_fn f ↑(u⁻¹) = (coe_fn f ↑u⁻¹) :=
  sorry

/-- Constructs a `group_with_zero` structure on a `monoid_with_zero`
  consisting only of units and 0. -/
def group_with_zero_of_is_unit_or_eq_zero {M : Type u_5} [nontrivial M] [hM : monoid_with_zero M]
    (h : ∀ (a : M), is_unit a ∨ a = 0) : group_with_zero M :=
  group_with_zero.mk monoid_with_zero.mul monoid_with_zero.mul_assoc monoid_with_zero.one
    monoid_with_zero.one_mul monoid_with_zero.mul_one monoid_with_zero.zero
    monoid_with_zero.zero_mul monoid_with_zero.mul_zero
    (fun (a : M) =>
      dite (a = 0) (fun (h0 : a = 0) => 0) fun (h0 : ¬a = 0) => ↑(is_unit.unit sorry⁻¹))
    (div_inv_monoid.div._default monoid_with_zero.mul monoid_with_zero.mul_assoc
      monoid_with_zero.one monoid_with_zero.one_mul monoid_with_zero.mul_one
      fun (a : M) =>
        dite (a = 0) (fun (h0 : a = 0) => 0) fun (h0 : ¬a = 0) => ↑(is_unit.unit sorry⁻¹))
    nontrivial.exists_pair_ne sorry sorry

/-- Constructs a `comm_group_with_zero` structure on a `comm_monoid_with_zero`
  consisting only of units and 0. -/
def comm_group_with_zero_of_is_unit_or_eq_zero {M : Type u_5} [nontrivial M]
    [hM : comm_monoid_with_zero M] (h : ∀ (a : M), is_unit a ∨ a = 0) : comm_group_with_zero M :=
  comm_group_with_zero.mk group_with_zero.mul sorry group_with_zero.one sorry sorry
    comm_monoid_with_zero.mul_comm group_with_zero.zero sorry sorry group_with_zero.inv
    group_with_zero.div sorry sorry sorry

end Mathlib