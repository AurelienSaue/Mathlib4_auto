/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.big_operators.order
import PostPort

universes u_1 u_2 l 

namespace Mathlib

/-!
# Cauchy sequences

A basic theory of Cauchy sequences, used in the construction of the reals and p-adic numbers. Where
applicable, lemmas that will be reused in other contexts have been stated in extra generality.

There are other "versions" of Cauchyness in the library, in particular Cauchy filters in topology.
This is a concrete implementation that is useful for simplicity and computability reasons.

## Important definitions

* `is_absolute_value`: a type class stating that `f : β → α` satisfies the axioms of an abs val
* `is_cau_seq`: a predicate that says `f : ℕ → β` is Cauchy.
* `cau_seq`: the type of Cauchy sequences valued in type `β` with respect to an absolute value
  function `abv`.

## Tags

sequence, cauchy, abs val, absolute value
-/

/-- A function `f` is an absolute value if it is nonnegative, zero only at 0, additive, and
multiplicative. -/
class is_absolute_value {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] (f : β → α) 
where
  abv_nonneg : ∀ (x : β), 0 ≤ f x
  abv_eq_zero : ∀ {x : β}, f x = 0 ↔ x = 0
  abv_add : ∀ (x y : β), f (x + y) ≤ f x + f y
  abv_mul : ∀ (x y : β), f (x * y) = f x * f y

namespace is_absolute_value


theorem abv_zero {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] (abv : β → α) [is_absolute_value abv] : abv 0 = 0 :=
  iff.mpr (abv_eq_zero abv) rfl

theorem abv_one {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] (abv : β → α) [is_absolute_value abv] [nontrivial β] : abv 1 = 1 := sorry

theorem abv_pos {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] (abv : β → α) [is_absolute_value abv] {a : β} : 0 < abv a ↔ a ≠ 0 := sorry

theorem abv_neg {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] (abv : β → α) [is_absolute_value abv] (a : β) : abv (-a) = abv a := sorry

theorem abv_sub {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] (abv : β → α) [is_absolute_value abv] (a : β) (b : β) : abv (a - b) = abv (b - a) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (abv (a - b) = abv (b - a))) (Eq.symm (neg_sub b a))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (abv (-(b - a)) = abv (b - a))) (abv_neg abv (b - a)))) (Eq.refl (abv (b - a))))

/-- `abv` as a `monoid_with_zero_hom`. -/
def abv_hom {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] (abv : β → α) [is_absolute_value abv] [nontrivial β] : monoid_with_zero_hom β α :=
  monoid_with_zero_hom.mk abv (abv_zero abv) (abv_one abv) (abv_mul abv)

theorem abv_inv {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [field β] (abv : β → α) [is_absolute_value abv] (a : β) : abv (a⁻¹) = (abv a⁻¹) :=
  monoid_with_zero_hom.map_inv' (abv_hom abv) a

theorem abv_div {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [field β] (abv : β → α) [is_absolute_value abv] (a : β) (b : β) : abv (a / b) = abv a / abv b :=
  monoid_with_zero_hom.map_div (abv_hom abv) a b

theorem abv_sub_le {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] (abv : β → α) [is_absolute_value abv] (a : β) (b : β) (c : β) : abv (a - c) ≤ abv (a - b) + abv (b - c) := sorry

theorem sub_abv_le_abv_sub {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] (abv : β → α) [is_absolute_value abv] (a : β) (b : β) : abv a - abv b ≤ abv (a - b) := sorry

theorem abs_abv_sub_le_abv_sub {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] (abv : β → α) [is_absolute_value abv] (a : β) (b : β) : abs (abv a - abv b) ≤ abv (a - b) := sorry

theorem abv_pow {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] [nontrivial β] (abv : β → α) [is_absolute_value abv] (a : β) (n : ℕ) : abv (a ^ n) = abv a ^ n :=
  monoid_hom.map_pow (monoid_with_zero_hom.to_monoid_hom (abv_hom abv)) a n

end is_absolute_value


protected instance abs_is_absolute_value {α : Type u_1} [linear_ordered_field α] : is_absolute_value abs :=
  is_absolute_value.mk abs_nonneg (fun (_x : α) => abs_eq_zero) abs_add abs_mul

theorem exists_forall_ge_and {α : Type u_1} [linear_order α] {P : α → Prop} {Q : α → Prop} : (∃ (i : α), ∀ (j : α), j ≥ i → P j) → (∃ (i : α), ∀ (j : α), j ≥ i → Q j) → ∃ (i : α), ∀ (j : α), j ≥ i → P j ∧ Q j := sorry

theorem rat_add_continuous_lemma {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] (abv : β → α) [is_absolute_value abv] {ε : α} (ε0 : 0 < ε) : ∃ (δ : α), ∃ (H : δ > 0), ∀ {a₁ a₂ b₁ b₂ : β}, abv (a₁ - b₁) < δ → abv (a₂ - b₂) < δ → abv (a₁ + a₂ - (b₁ + b₂)) < ε := sorry

theorem rat_mul_continuous_lemma {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] (abv : β → α) [is_absolute_value abv] {ε : α} {K₁ : α} {K₂ : α} (ε0 : 0 < ε) : ∃ (δ : α),
  ∃ (H : δ > 0),
    ∀ {a₁ a₂ b₁ b₂ : β}, abv a₁ < K₁ → abv b₂ < K₂ → abv (a₁ - b₁) < δ → abv (a₂ - b₂) < δ → abv (a₁ * a₂ - b₁ * b₂) < ε := sorry

theorem rat_inv_continuous_lemma {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [field β] (abv : β → α) [is_absolute_value abv] {ε : α} {K : α} (ε0 : 0 < ε) (K0 : 0 < K) : ∃ (δ : α), ∃ (H : δ > 0), ∀ {a b : β}, K ≤ abv a → K ≤ abv b → abv (a - b) < δ → abv (a⁻¹ - (b⁻¹)) < ε := sorry

/-- A sequence is Cauchy if the distance between its entries tends to zero. -/
def is_cau_seq {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] (abv : β → α) (f : ℕ → β)  :=
  ∀ (ε : α), ε > 0 → ∃ (i : ℕ), ∀ (j : ℕ), j ≥ i → abv (f j - f i) < ε

namespace is_cau_seq


theorem cauchy₂ {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] {f : ℕ → β} (hf : is_cau_seq abv f) {ε : α} (ε0 : 0 < ε) : ∃ (i : ℕ), ∀ (j k : ℕ), j ≥ i → k ≥ i → abv (f j - f k) < ε := sorry

theorem cauchy₃ {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] {f : ℕ → β} (hf : is_cau_seq abv f) {ε : α} (ε0 : 0 < ε) : ∃ (i : ℕ), ∀ (j : ℕ), j ≥ i → ∀ (k : ℕ), k ≥ j → abv (f k - f j) < ε := sorry

end is_cau_seq


/-- `cau_seq β abv` is the type of `β`-valued Cauchy sequences, with respect to the absolute value
function `abv`. -/
def cau_seq {α : Type u_1} [linear_ordered_field α] (β : Type u_2) [ring β] (abv : β → α)  :=
  Subtype fun (f : ℕ → β) => is_cau_seq abv f

namespace cau_seq


protected instance has_coe_to_fun {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} : has_coe_to_fun (cau_seq β abv) :=
  has_coe_to_fun.mk (fun (x : cau_seq β abv) => ℕ → β) subtype.val

@[simp] theorem mk_to_fun {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} (f : ℕ → β) (hf : is_cau_seq abv f) : ⇑{ val := f, property := hf } = f :=
  rfl

theorem ext {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} {f : cau_seq β abv} {g : cau_seq β abv} (h : ∀ (i : ℕ), coe_fn f i = coe_fn g i) : f = g :=
  subtype.eq (funext h)

theorem is_cau {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} (f : cau_seq β abv) : is_cau_seq abv ⇑f :=
  subtype.property f

theorem cauchy {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} (f : cau_seq β abv) {ε : α} : 0 < ε → ∃ (i : ℕ), ∀ (j : ℕ), j ≥ i → abv (coe_fn f j - coe_fn f i) < ε :=
  subtype.property f

/-- Given a Cauchy sequence `f`, create a Cauchy sequence from a sequence `g` with
the same values as `f`. -/
def of_eq {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} (f : cau_seq β abv) (g : ℕ → β) (e : ∀ (i : ℕ), coe_fn f i = g i) : cau_seq β abv :=
  { val := g, property := sorry }

theorem cauchy₂ {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] (f : cau_seq β abv) {ε : α} : 0 < ε → ∃ (i : ℕ), ∀ (j k : ℕ), j ≥ i → k ≥ i → abv (coe_fn f j - coe_fn f k) < ε :=
  is_cau_seq.cauchy₂ (subtype.property f)

theorem cauchy₃ {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] (f : cau_seq β abv) {ε : α} : 0 < ε → ∃ (i : ℕ), ∀ (j : ℕ), j ≥ i → ∀ (k : ℕ), k ≥ j → abv (coe_fn f k - coe_fn f j) < ε :=
  is_cau_seq.cauchy₃ (subtype.property f)

theorem bounded {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] (f : cau_seq β abv) : ∃ (r : α), ∀ (i : ℕ), abv (coe_fn f i) < r := sorry

theorem bounded' {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] (f : cau_seq β abv) (x : α) : ∃ (r : α), ∃ (H : r > x), ∀ (i : ℕ), abv (coe_fn f i) < r := sorry

protected instance has_add {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] : Add (cau_seq β abv) :=
  { add := fun (f g : cau_seq β abv) => { val := fun (i : ℕ) => coe_fn f i + coe_fn g i, property := sorry } }

@[simp] theorem add_apply {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] (f : cau_seq β abv) (g : cau_seq β abv) (i : ℕ) : coe_fn (f + g) i = coe_fn f i + coe_fn g i :=
  rfl

/-- The constant Cauchy sequence. -/
def const {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] (abv : β → α) [is_absolute_value abv] (x : β) : cau_seq β abv :=
  { val := fun (i : ℕ) => x, property := sorry }

@[simp] theorem const_apply {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] (x : β) (i : ℕ) : coe_fn (const abv x) i = x :=
  rfl

theorem const_inj {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] {x : β} {y : β} : const abv x = const abv y ↔ x = y :=
  { mp := fun (h : const abv x = const abv y) => congr_arg (fun (f : cau_seq β abv) => coe_fn f 0) h,
    mpr := congr_arg fun {x : β} => const abv x }

protected instance has_zero {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] : HasZero (cau_seq β abv) :=
  { zero := const abv 0 }

protected instance has_one {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] : HasOne (cau_seq β abv) :=
  { one := const abv 1 }

protected instance inhabited {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] : Inhabited (cau_seq β abv) :=
  { default := 0 }

@[simp] theorem zero_apply {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] (i : ℕ) : coe_fn 0 i = 0 :=
  rfl

@[simp] theorem one_apply {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] (i : ℕ) : coe_fn 1 i = 1 :=
  rfl

theorem const_add {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] (x : β) (y : β) : const abv (x + y) = const abv x + const abv y :=
  ext fun (i : ℕ) => rfl

protected instance has_mul {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] : Mul (cau_seq β abv) :=
  { mul := fun (f g : cau_seq β abv) => { val := fun (i : ℕ) => coe_fn f i * coe_fn g i, property := sorry } }

@[simp] theorem mul_apply {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] (f : cau_seq β abv) (g : cau_seq β abv) (i : ℕ) : coe_fn (f * g) i = coe_fn f i * coe_fn g i :=
  rfl

theorem const_mul {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] (x : β) (y : β) : const abv (x * y) = const abv x * const abv y :=
  ext fun (i : ℕ) => rfl

protected instance has_neg {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] : Neg (cau_seq β abv) :=
  { neg := fun (f : cau_seq β abv) => of_eq (const abv (-1) * f) (fun (x : ℕ) => -coe_fn f x) sorry }

@[simp] theorem neg_apply {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] (f : cau_seq β abv) (i : ℕ) : coe_fn (-f) i = -coe_fn f i :=
  rfl

theorem const_neg {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] (x : β) : const abv (-x) = -const abv x :=
  ext fun (i : ℕ) => rfl

protected instance has_sub {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] : Sub (cau_seq β abv) :=
  { sub := fun (f g : cau_seq β abv) => of_eq (f + -g) (fun (x : ℕ) => coe_fn f x - coe_fn g x) sorry }

@[simp] theorem sub_apply {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] (f : cau_seq β abv) (g : cau_seq β abv) (i : ℕ) : coe_fn (f - g) i = coe_fn f i - coe_fn g i :=
  rfl

theorem const_sub {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] (x : β) (y : β) : const abv (x - y) = const abv x - const abv y :=
  ext fun (i : ℕ) => rfl

protected instance ring {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] : ring (cau_seq β abv) :=
  ring.mk Add.add sorry 0 sorry sorry Neg.neg Sub.sub sorry sorry Mul.mul sorry 1 sorry sorry sorry sorry

protected instance comm_ring {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [comm_ring β] {abv : β → α} [is_absolute_value abv] : comm_ring (cau_seq β abv) :=
  comm_ring.mk ring.add sorry ring.zero sorry sorry ring.neg ring.sub sorry sorry ring.mul sorry ring.one sorry sorry
    sorry sorry sorry

/-- `lim_zero f` holds when `f` approaches 0. -/
def lim_zero {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} (f : cau_seq β abv)  :=
  ∀ (ε : α), ε > 0 → ∃ (i : ℕ), ∀ (j : ℕ), j ≥ i → abv (coe_fn f j) < ε

theorem add_lim_zero {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] {f : cau_seq β abv} {g : cau_seq β abv} (hf : lim_zero f) (hg : lim_zero g) : lim_zero (f + g) := sorry

theorem mul_lim_zero_right {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] (f : cau_seq β abv) {g : cau_seq β abv} (hg : lim_zero g) : lim_zero (f * g) := sorry

theorem mul_lim_zero_left {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] {f : cau_seq β abv} (g : cau_seq β abv) (hg : lim_zero f) : lim_zero (f * g) := sorry

theorem neg_lim_zero {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] {f : cau_seq β abv} (hf : lim_zero f) : lim_zero (-f) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (lim_zero (-f))) (Eq.symm (neg_one_mul f)))) (mul_lim_zero_right (-1) hf)

theorem sub_lim_zero {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] {f : cau_seq β abv} {g : cau_seq β abv} (hf : lim_zero f) (hg : lim_zero g) : lim_zero (f - g) :=
  eq.mpr
    (id ((fun (f f_1 : cau_seq β abv) (e_1 : f = f_1) => congr_arg lim_zero e_1) (f - g) (f + -g) (sub_eq_add_neg f g)))
    (eq.mp (Eq.refl (lim_zero (f + -g))) (add_lim_zero hf (neg_lim_zero hg)))

theorem lim_zero_sub_rev {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] {f : cau_seq β abv} {g : cau_seq β abv} (hfg : lim_zero (f - g)) : lim_zero (g - f) :=
  eq.mpr (id (Eq.refl (lim_zero (g - f))))
    (eq.mp ((fun (f f_1 : cau_seq β abv) (e_1 : f = f_1) => congr_arg lim_zero e_1) (-(f - g)) (g - f) (neg_sub f g))
      (neg_lim_zero hfg))

theorem zero_lim_zero {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] : lim_zero 0 := sorry

theorem const_lim_zero {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] {x : β} : lim_zero (const abv x) ↔ x = 0 := sorry

protected instance equiv {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] : setoid (cau_seq β abv) :=
  setoid.mk (fun (f g : cau_seq β abv) => lim_zero (f - g)) sorry

theorem add_equiv_add {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] {f1 : cau_seq β abv} {f2 : cau_seq β abv} {g1 : cau_seq β abv} {g2 : cau_seq β abv} (hf : f1 ≈ f2) (hg : g1 ≈ g2) : f1 + g1 ≈ f2 + g2 := sorry

theorem neg_equiv_neg {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] {f : cau_seq β abv} {g : cau_seq β abv} (hf : f ≈ g) : -f ≈ -g := sorry

theorem equiv_def₃ {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] {f : cau_seq β abv} {g : cau_seq β abv} (h : f ≈ g) {ε : α} (ε0 : 0 < ε) : ∃ (i : ℕ), ∀ (j : ℕ), j ≥ i → ∀ (k : ℕ), k ≥ j → abv (coe_fn f k - coe_fn g j) < ε := sorry

theorem lim_zero_congr {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] {f : cau_seq β abv} {g : cau_seq β abv} (h : f ≈ g) : lim_zero f ↔ lim_zero g := sorry

theorem abv_pos_of_not_lim_zero {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] {f : cau_seq β abv} (hf : ¬lim_zero f) : ∃ (K : α), ∃ (H : K > 0), ∃ (i : ℕ), ∀ (j : ℕ), j ≥ i → K ≤ abv (coe_fn f j) := sorry

theorem of_near {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] (f : ℕ → β) (g : cau_seq β abv) (h : ∀ (ε : α), ε > 0 → ∃ (i : ℕ), ∀ (j : ℕ), j ≥ i → abv (f j - coe_fn g j) < ε) : is_cau_seq abv f := sorry

theorem not_lim_zero_of_not_congr_zero {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] {f : cau_seq β abv} (hf : ¬f ≈ 0) : ¬lim_zero f := sorry

theorem mul_equiv_zero {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] (g : cau_seq β abv) {f : cau_seq β abv} (hf : f ≈ 0) : g * f ≈ 0 := sorry

theorem mul_not_equiv_zero {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] {f : cau_seq β abv} {g : cau_seq β abv} (hf : ¬f ≈ 0) (hg : ¬g ≈ 0) : ¬f * g ≈ 0 := sorry

theorem const_equiv {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] {x : β} {y : β} : const abv x ≈ const abv y ↔ x = y := sorry

theorem mul_equiv_zero' {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [comm_ring β] {abv : β → α} [is_absolute_value abv] (g : cau_seq β abv) {f : cau_seq β abv} (hf : f ≈ 0) : f * g ≈ 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (f * g ≈ 0)) (mul_comm f g))) (mul_equiv_zero g hf)

theorem one_not_equiv_zero {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [integral_domain β] (abv : β → α) [is_absolute_value abv] : ¬const abv 1 ≈ const abv 0 := sorry

theorem inv_aux {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [field β] {abv : β → α} [is_absolute_value abv] {f : cau_seq β abv} (hf : ¬lim_zero f) (ε : α) (H : ε > 0) : ∃ (i : ℕ), ∀ (j : ℕ), j ≥ i → abv (coe_fn f j⁻¹ - (coe_fn f i⁻¹)) < ε := sorry

/-- Given a Cauchy sequence `f` with nonzero limit, create a Cauchy sequence with values equal to
the inverses of the values of `f`. -/
def inv {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [field β] {abv : β → α} [is_absolute_value abv] (f : cau_seq β abv) (hf : ¬lim_zero f) : cau_seq β abv :=
  { val := fun (j : ℕ) => coe_fn f j⁻¹, property := inv_aux hf }

@[simp] theorem inv_apply {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [field β] {abv : β → α} [is_absolute_value abv] {f : cau_seq β abv} (hf : ¬lim_zero f) (i : ℕ) : coe_fn (inv f hf) i = (coe_fn f i⁻¹) :=
  rfl

theorem inv_mul_cancel {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [field β] {abv : β → α} [is_absolute_value abv] {f : cau_seq β abv} (hf : ¬lim_zero f) : inv f hf * f ≈ 1 := sorry

theorem const_inv {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [field β] {abv : β → α} [is_absolute_value abv] {x : β} (hx : x ≠ 0) : const abv (x⁻¹) =
  inv (const abv x) (eq.mpr (id (Eq._oldrec (Eq.refl (¬lim_zero (const abv x))) (propext const_lim_zero))) hx) := sorry

/-- The entries of a positive Cauchy sequence eventually have a positive lower bound. -/
def pos {α : Type u_1} [linear_ordered_field α] (f : cau_seq α abs)  :=
  ∃ (K : α), ∃ (H : K > 0), ∃ (i : ℕ), ∀ (j : ℕ), j ≥ i → K ≤ coe_fn f j

theorem not_lim_zero_of_pos {α : Type u_1} [linear_ordered_field α] {f : cau_seq α abs} : pos f → ¬lim_zero f := sorry

theorem const_pos {α : Type u_1} [linear_ordered_field α] {x : α} : pos (const abs x) ↔ 0 < x := sorry

theorem add_pos {α : Type u_1} [linear_ordered_field α] {f : cau_seq α abs} {g : cau_seq α abs} : pos f → pos g → pos (f + g) := sorry

theorem pos_add_lim_zero {α : Type u_1} [linear_ordered_field α] {f : cau_seq α abs} {g : cau_seq α abs} : pos f → lim_zero g → pos (f + g) := sorry

protected theorem mul_pos {α : Type u_1} [linear_ordered_field α] {f : cau_seq α abs} {g : cau_seq α abs} : pos f → pos g → pos (f * g) := sorry

theorem trichotomy {α : Type u_1} [linear_ordered_field α] (f : cau_seq α abs) : pos f ∨ lim_zero f ∨ pos (-f) := sorry

protected instance has_lt {α : Type u_1} [linear_ordered_field α] : HasLess (cau_seq α abs) :=
  { Less := fun (f g : cau_seq α abs) => pos (g - f) }

protected instance has_le {α : Type u_1} [linear_ordered_field α] : HasLessEq (cau_seq α abs) :=
  { LessEq := fun (f g : cau_seq α abs) => f < g ∨ f ≈ g }

theorem lt_of_lt_of_eq {α : Type u_1} [linear_ordered_field α] {f : cau_seq α abs} {g : cau_seq α abs} {h : cau_seq α abs} (fg : f < g) (gh : g ≈ h) : f < h := sorry

theorem lt_of_eq_of_lt {α : Type u_1} [linear_ordered_field α] {f : cau_seq α abs} {g : cau_seq α abs} {h : cau_seq α abs} (fg : f ≈ g) (gh : g < h) : f < h :=
  eq.mp (Eq._oldrec (Eq.refl (pos (h - g - (f - g)))) (sub_sub_sub_cancel_right h f g))
    (eq.mp (Eq._oldrec (Eq.refl (pos (h - g + -(f - g)))) (Eq.symm (sub_eq_add_neg (h - g) (f - g))))
      (pos_add_lim_zero gh (neg_lim_zero fg)))

theorem lt_trans {α : Type u_1} [linear_ordered_field α] {f : cau_seq α abs} {g : cau_seq α abs} {h : cau_seq α abs} (fg : f < g) (gh : g < h) : f < h := sorry

theorem lt_irrefl {α : Type u_1} [linear_ordered_field α] {f : cau_seq α abs} : ¬f < f := sorry

theorem le_of_eq_of_le {α : Type u_1} [linear_ordered_field α] {f : cau_seq α abs} {g : cau_seq α abs} {h : cau_seq α abs} (hfg : f ≈ g) (hgh : g ≤ h) : f ≤ h :=
  or.elim hgh (Or.inl ∘ lt_of_eq_of_lt hfg) (Or.inr ∘ setoid.trans hfg)

theorem le_of_le_of_eq {α : Type u_1} [linear_ordered_field α] {f : cau_seq α abs} {g : cau_seq α abs} {h : cau_seq α abs} (hfg : f ≤ g) (hgh : g ≈ h) : f ≤ h :=
  or.elim hfg (fun (h_1 : f < g) => Or.inl (lt_of_lt_of_eq h_1 hgh)) fun (h_1 : f ≈ g) => Or.inr (setoid.trans h_1 hgh)

protected instance preorder {α : Type u_1} [linear_ordered_field α] : preorder (cau_seq α abs) :=
  preorder.mk (fun (f g : cau_seq α abs) => f < g ∨ f ≈ g) Less sorry sorry

theorem le_antisymm {α : Type u_1} [linear_ordered_field α] {f : cau_seq α abs} {g : cau_seq α abs} (fg : f ≤ g) (gf : g ≤ f) : f ≈ g :=
  or.resolve_left fg (not_lt_of_le gf)

theorem lt_total {α : Type u_1} [linear_ordered_field α] (f : cau_seq α abs) (g : cau_seq α abs) : f < g ∨ f ≈ g ∨ g < f := sorry

theorem le_total {α : Type u_1} [linear_ordered_field α] (f : cau_seq α abs) (g : cau_seq α abs) : f ≤ g ∨ g ≤ f :=
  or.imp_right Or.inl (iff.mpr or.assoc (lt_total f g))

theorem const_lt {α : Type u_1} [linear_ordered_field α] {x : α} {y : α} : const abs x < const abs y ↔ x < y := sorry

theorem const_le {α : Type u_1} [linear_ordered_field α] {x : α} {y : α} : const abs x ≤ const abs y ↔ x ≤ y :=
  eq.mpr (id (Eq._oldrec (Eq.refl (const abs x ≤ const abs y ↔ x ≤ y)) (propext le_iff_lt_or_eq)))
    (or_congr const_lt const_equiv)

theorem le_of_exists {α : Type u_1} [linear_ordered_field α] {f : cau_seq α abs} {g : cau_seq α abs} (h : ∃ (i : ℕ), ∀ (j : ℕ), j ≥ i → coe_fn f j ≤ coe_fn g j) : f ≤ g := sorry

theorem exists_gt {α : Type u_1} [linear_ordered_field α] (f : cau_seq α abs) : ∃ (a : α), f < const abs a := sorry

theorem exists_lt {α : Type u_1} [linear_ordered_field α] (f : cau_seq α abs) : ∃ (a : α), const abs a < f := sorry

