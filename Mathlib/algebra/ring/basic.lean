/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Amelia Livingston, Yury Kudryashov,
Neil Strickland
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.divisibility
import Mathlib.data.set.basic
import Mathlib.PostPort

universes u_1 l x u v u_2 w 

namespace Mathlib

/-!
# Properties and homomorphisms of semirings and rings

This file proves simple properties of semirings, rings and domains and their unit groups. It also
defines bundled homomorphisms of semirings and rings. As with monoid and groups, we use the same
structure `ring_hom a β`, a.k.a. `α →+* β`, for both homomorphism types.

The unbundled homomorphisms are defined in `deprecated/ring`. They are deprecated and the plan is to
slowly remove them from mathlib.

## Main definitions

ring_hom, nonzero, domain, integral_domain

## Notations

→+* for bundled ring homs (also use for semiring homs)

## Implementation notes

There's a coercion from bundled homs to fun, and the canonical
notation is to use the bundled hom as a function via this coercion.

There is no `semiring_hom` -- the idea is that `ring_hom` is used.
The constructor for a `ring_hom` between semirings needs a proof of `map_zero`, `map_one` and
`map_add` as well as `map_mul`; a separate constructor `ring_hom.mk'` will construct ring homs
between rings from monoid homs given only a proof that addition is preserved.

## Tags

`ring_hom`, `semiring_hom`, `semiring`, `comm_semiring`, `ring`, `comm_ring`, `domain`,
`integral_domain`, `nonzero`, `units`
-/

/-!
### `distrib` class
-/

/-- A typeclass stating that multiplication is left and right distributive
over addition. -/
class distrib (R : Type u_1) 
extends Mul R, Add R
where
  left_distrib : ∀ (a b c : R), a * (b + c) = a * b + a * c
  right_distrib : ∀ (a b c : R), (a + b) * c = a * c + b * c

theorem left_distrib {R : Type x} [distrib R] (a : R) (b : R) (c : R) : a * (b + c) = a * b + a * c :=
  distrib.left_distrib a b c

theorem mul_add {R : Type x} [distrib R] (a : R) (b : R) (c : R) : a * (b + c) = a * b + a * c :=
  left_distrib

theorem right_distrib {R : Type x} [distrib R] (a : R) (b : R) (c : R) : (a + b) * c = a * c + b * c :=
  distrib.right_distrib a b c

theorem add_mul {R : Type x} [distrib R] (a : R) (b : R) (c : R) : (a + b) * c = a * c + b * c :=
  right_distrib

/-- Pullback a `distrib` instance along an injective function. -/
protected def function.injective.distrib {R : Type x} {S : Type u_1} [Mul R] [Add R] [distrib S] (f : R → S) (hf : function.injective f) (add : ∀ (x y : R), f (x + y) = f x + f y) (mul : ∀ (x y : R), f (x * y) = f x * f y) : distrib R :=
  distrib.mk Mul.mul Add.add sorry sorry

/-- Pushforward a `distrib` instance along a surjective function. -/
protected def function.surjective.distrib {R : Type x} {S : Type u_1} [distrib R] [Add S] [Mul S] (f : R → S) (hf : function.surjective f) (add : ∀ (x y : R), f (x + y) = f x + f y) (mul : ∀ (x y : R), f (x * y) = f x * f y) : distrib S :=
  distrib.mk Mul.mul Add.add sorry sorry

/-!
### Semirings
-/

/-- A semiring is a type with the following structures: additive commutative monoid
(`add_comm_monoid`), multiplicative monoid (`monoid`), distributive laws (`distrib`), and
multiplication by zero law (`mul_zero_class`). The actual definition extends `monoid_with_zero`
instead of `monoid` and `mul_zero_class`. -/
class semiring (α : Type u) 
extends monoid_with_zero α, distrib α, add_comm_monoid α
where

/-- Pullback a `semiring` instance along an injective function. -/
protected def function.injective.semiring {α : Type u} {β : Type v} [semiring α] [HasZero β] [HasOne β] [Add β] [Mul β] (f : β → α) (hf : function.injective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ (x y : β), f (x + y) = f x + f y) (mul : ∀ (x y : β), f (x * y) = f x * f y) : semiring β :=
  semiring.mk add_comm_monoid.add sorry monoid_with_zero.zero sorry sorry sorry monoid_with_zero.mul sorry
    monoid_with_zero.one sorry sorry sorry sorry sorry sorry

/-- Pullback a `semiring` instance along an injective function. -/
protected def function.surjective.semiring {α : Type u} {β : Type v} [semiring α] [HasZero β] [HasOne β] [Add β] [Mul β] (f : α → β) (hf : function.surjective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ (x y : α), f (x + y) = f x + f y) (mul : ∀ (x y : α), f (x * y) = f x * f y) : semiring β :=
  semiring.mk add_comm_monoid.add sorry monoid_with_zero.zero sorry sorry sorry monoid_with_zero.mul sorry
    monoid_with_zero.one sorry sorry sorry sorry sorry sorry

theorem one_add_one_eq_two {α : Type u} [semiring α] : 1 + 1 = bit0 1 := sorry

theorem two_mul {α : Type u} [semiring α] (n : α) : bit0 1 * n = n + n := sorry

theorem distrib_three_right {α : Type u} [semiring α] (a : α) (b : α) (c : α) (d : α) : (a + b + c) * d = a * d + b * d + c * d := sorry

theorem mul_two {α : Type u} [semiring α] (n : α) : n * bit0 1 = n + n := sorry

theorem bit0_eq_two_mul {α : Type u} [semiring α] (n : α) : bit0 n = bit0 1 * n :=
  Eq.symm (two_mul n)

theorem add_ite {α : Type u_1} [Add α] (P : Prop) [Decidable P] (a : α) (b : α) (c : α) : a + ite P b c = ite P (a + b) (a + c) := sorry

@[simp] theorem ite_mul {α : Type u_1} [Mul α] (P : Prop) [Decidable P] (a : α) (b : α) (c : α) : ite P a b * c = ite P (a * c) (b * c) := sorry

-- We make `mul_ite` and `ite_mul` simp lemmas,

-- but not `add_ite` or `ite_add`.

-- The problem we're trying to avoid is dealing with

-- summations of the form `∑ x in s, (f x + ite P 1 0)`,

-- in which `add_ite` followed by `sum_ite` would needlessly slice up

-- the `f x` terms according to whether `P` holds at `x`.

-- There doesn't appear to be a corresponding difficulty so far with

-- `mul_ite` and `ite_mul`.

@[simp] theorem mul_boole {α : Type u_1} [semiring α] (P : Prop) [Decidable P] (a : α) : a * ite P 1 0 = ite P a 0 := sorry

@[simp] theorem boole_mul {α : Type u_1} [semiring α] (P : Prop) [Decidable P] (a : α) : ite P 1 0 * a = ite P a 0 := sorry

theorem ite_mul_zero_left {α : Type u_1} [mul_zero_class α] (P : Prop) [Decidable P] (a : α) (b : α) : ite P (a * b) 0 = ite P a 0 * b := sorry

theorem ite_mul_zero_right {α : Type u_1} [mul_zero_class α] (P : Prop) [Decidable P] (a : α) (b : α) : ite P (a * b) 0 = a * ite P b 0 := sorry

/-- An element `a` of a semiring is even if there exists `k` such `a = 2*k`. -/
def even {α : Type u} [semiring α] (a : α)  :=
  ∃ (k : α), a = bit0 1 * k

theorem even_iff_two_dvd {α : Type u} [semiring α] {a : α} : even a ↔ bit0 1 ∣ a :=
  iff.rfl

/-- An element `a` of a semiring is odd if there exists `k` such `a = 2*k + 1`. -/
def odd {α : Type u} [semiring α] (a : α)  :=
  ∃ (k : α), a = bit0 1 * k + 1

theorem dvd_add {α : Type u} [semiring α] {a : α} {b : α} {c : α} (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b + c := sorry

namespace add_monoid_hom


/-- Left multiplication by an element of a (semi)ring is an `add_monoid_hom` -/
def mul_left {R : Type u_1} [semiring R] (r : R) : R →+ R :=
  mk (Mul.mul r) sorry sorry

@[simp] theorem coe_mul_left {R : Type u_1} [semiring R] (r : R) : ⇑(mul_left r) = Mul.mul r :=
  rfl

/-- Right multiplication by an element of a (semi)ring is an `add_monoid_hom` -/
def mul_right {R : Type u_1} [semiring R] (r : R) : R →+ R :=
  mk (fun (a : R) => a * r) sorry sorry

@[simp] theorem coe_mul_right {R : Type u_1} [semiring R] (r : R) : ⇑(mul_right r) = fun (_x : R) => _x * r :=
  rfl

theorem mul_right_apply {R : Type u_1} [semiring R] (a : R) (r : R) : coe_fn (mul_right r) a = a * r :=
  rfl

end add_monoid_hom


/-- Bundled semiring homomorphisms; use this for bundled ring homomorphisms too.

This extends from both `monoid_hom` and `monoid_with_zero_hom` in order to put the fields in a
sensible order, even though `monoid_with_zero_hom` already extends `monoid_hom`. -/
structure ring_hom (α : Type u_1) (β : Type u_2) [semiring α] [semiring β] 
extends monoid_with_zero_hom α β, α →* β, α →+ β
where

infixr:25 " →+* " => Mathlib.ring_hom

/-- Reinterpret a ring homomorphism `f : R →+* S` as a `monoid_with_zero_hom R S`.
The `simp`-normal form is `(f : monoid_with_zero_hom R S)`. -/
/-- Reinterpret a ring homomorphism `f : R →+* S` as a monoid homomorphism `R →* S`.
The `simp`-normal form is `(f : R →* S)`. -/
/-- Reinterpret a ring homomorphism `f : R →+* S` as an additive monoid homomorphism `R →+ S`.
The `simp`-normal form is `(f : R →+ S)`. -/
namespace ring_hom


/-!
Throughout this section, some `semiring` arguments are specified with `{}` instead of `[]`.
See note [implicit instance arguments].
-/

protected instance has_coe_to_fun {α : Type u} {β : Type v} {rα : semiring α} {rβ : semiring β} : has_coe_to_fun (α →+* β) :=
  has_coe_to_fun.mk (fun (x : α →+* β) => α → β) to_fun

@[simp] theorem to_fun_eq_coe {α : Type u} {β : Type v} {rα : semiring α} {rβ : semiring β} (f : α →+* β) : to_fun f = ⇑f :=
  rfl

@[simp] theorem coe_mk {α : Type u} {β : Type v} {rα : semiring α} {rβ : semiring β} (f : α → β) (h₁ : f 1 = 1) (h₂ : ∀ (x y : α), f (x * y) = f x * f y) (h₃ : f 0 = 0) (h₄ : ∀ (x y : α), f (x + y) = f x + f y) : ⇑(mk f h₁ h₂ h₃ h₄) = f :=
  rfl

protected instance has_coe_monoid_hom {α : Type u} {β : Type v} {rα : semiring α} {rβ : semiring β} : has_coe (α →+* β) (α →* β) :=
  has_coe.mk to_monoid_hom

@[simp] theorem coe_monoid_hom {α : Type u} {β : Type v} {rα : semiring α} {rβ : semiring β} (f : α →+* β) : ⇑↑f = ⇑f :=
  rfl

@[simp] theorem to_monoid_hom_eq_coe {α : Type u} {β : Type v} {rα : semiring α} {rβ : semiring β} (f : α →+* β) : to_monoid_hom f = ↑f :=
  rfl

@[simp] theorem coe_monoid_hom_mk {α : Type u} {β : Type v} {rα : semiring α} {rβ : semiring β} (f : α → β) (h₁ : f 1 = 1) (h₂ : ∀ (x y : α), f (x * y) = f x * f y) (h₃ : f 0 = 0) (h₄ : ∀ (x y : α), f (x + y) = f x + f y) : ↑(mk f h₁ h₂ h₃ h₄) = monoid_hom.mk f h₁ h₂ :=
  rfl

protected instance has_coe_add_monoid_hom {α : Type u} {β : Type v} {rα : semiring α} {rβ : semiring β} : has_coe (α →+* β) (α →+ β) :=
  has_coe.mk to_add_monoid_hom

@[simp] theorem coe_add_monoid_hom {α : Type u} {β : Type v} {rα : semiring α} {rβ : semiring β} (f : α →+* β) : ⇑↑f = ⇑f :=
  rfl

@[simp] theorem to_add_monoid_hom_eq_coe {α : Type u} {β : Type v} {rα : semiring α} {rβ : semiring β} (f : α →+* β) : to_add_monoid_hom f = ↑f :=
  rfl

@[simp] theorem coe_add_monoid_hom_mk {α : Type u} {β : Type v} {rα : semiring α} {rβ : semiring β} (f : α → β) (h₁ : f 1 = 1) (h₂ : ∀ (x y : α), f (x * y) = f x * f y) (h₃ : f 0 = 0) (h₄ : ∀ (x y : α), f (x + y) = f x + f y) : ↑(mk f h₁ h₂ h₃ h₄) = add_monoid_hom.mk f h₃ h₄ :=
  rfl

theorem congr_fun {α : Type u} {β : Type v} {rα : semiring α} {rβ : semiring β} {f : α →+* β} {g : α →+* β} (h : f = g) (x : α) : coe_fn f x = coe_fn g x :=
  congr_arg (fun (h : α →+* β) => coe_fn h x) h

theorem congr_arg {α : Type u} {β : Type v} {rα : semiring α} {rβ : semiring β} (f : α →+* β) {x : α} {y : α} (h : x = y) : coe_fn f x = coe_fn f y :=
  congr_arg (fun (x : α) => coe_fn f x) h

theorem coe_inj {α : Type u} {β : Type v} {rα : semiring α} {rβ : semiring β} {f : α →+* β} {g : α →+* β} (h : ⇑f = ⇑g) : f = g := sorry

theorem ext {α : Type u} {β : Type v} {rα : semiring α} {rβ : semiring β} {f : α →+* β} {g : α →+* β} (h : ∀ (x : α), coe_fn f x = coe_fn g x) : f = g :=
  coe_inj (funext h)

theorem ext_iff {α : Type u} {β : Type v} {rα : semiring α} {rβ : semiring β} {f : α →+* β} {g : α →+* β} : f = g ↔ ∀ (x : α), coe_fn f x = coe_fn g x :=
  { mp := fun (h : f = g) (x : α) => h ▸ rfl, mpr := fun (h : ∀ (x : α), coe_fn f x = coe_fn g x) => ext h }

@[simp] theorem mk_coe {α : Type u} {β : Type v} {rα : semiring α} {rβ : semiring β} (f : α →+* β) (h₁ : coe_fn f 1 = 1) (h₂ : ∀ (x y : α), coe_fn f (x * y) = coe_fn f x * coe_fn f y) (h₃ : coe_fn f 0 = 0) (h₄ : ∀ (x y : α), coe_fn f (x + y) = coe_fn f x + coe_fn f y) : mk (⇑f) h₁ h₂ h₃ h₄ = f :=
  ext fun (_x : α) => rfl

theorem coe_add_monoid_hom_injective {α : Type u} {β : Type v} {rα : semiring α} {rβ : semiring β} : function.injective coe :=
  fun (f g : α →+* β) (h : ↑f = ↑g) => ext fun (x : α) => add_monoid_hom.congr_fun h x

theorem coe_monoid_hom_injective {α : Type u} {β : Type v} {rα : semiring α} {rβ : semiring β} : function.injective coe :=
  fun (f g : α →+* β) (h : ↑f = ↑g) => ext fun (x : α) => monoid_hom.congr_fun h x

/-- Ring homomorphisms map zero to zero. -/
@[simp] theorem map_zero {α : Type u} {β : Type v} {rα : semiring α} {rβ : semiring β} (f : α →+* β) : coe_fn f 0 = 0 :=
  map_zero' f

/-- Ring homomorphisms map one to one. -/
@[simp] theorem map_one {α : Type u} {β : Type v} {rα : semiring α} {rβ : semiring β} (f : α →+* β) : coe_fn f 1 = 1 :=
  map_one' f

/-- Ring homomorphisms preserve addition. -/
@[simp] theorem map_add {α : Type u} {β : Type v} {rα : semiring α} {rβ : semiring β} (f : α →+* β) (a : α) (b : α) : coe_fn f (a + b) = coe_fn f a + coe_fn f b :=
  map_add' f a b

/-- Ring homomorphisms preserve multiplication. -/
@[simp] theorem map_mul {α : Type u} {β : Type v} {rα : semiring α} {rβ : semiring β} (f : α →+* β) (a : α) (b : α) : coe_fn f (a * b) = coe_fn f a * coe_fn f b :=
  map_mul' f a b

/-- Ring homomorphisms preserve `bit0`. -/
@[simp] theorem map_bit0 {α : Type u} {β : Type v} {rα : semiring α} {rβ : semiring β} (f : α →+* β) (a : α) : coe_fn f (bit0 a) = bit0 (coe_fn f a) :=
  map_add f a a

/-- Ring homomorphisms preserve `bit1`. -/
@[simp] theorem map_bit1 {α : Type u} {β : Type v} {rα : semiring α} {rβ : semiring β} (f : α →+* β) (a : α) : coe_fn f (bit1 a) = bit1 (coe_fn f a) := sorry

/-- `f : R →+* S` has a trivial codomain iff `f 1 = 0`. -/
theorem codomain_trivial_iff_map_one_eq_zero {α : Type u} {β : Type v} {rα : semiring α} {rβ : semiring β} (f : α →+* β) : 0 = 1 ↔ coe_fn f 1 = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (0 = 1 ↔ coe_fn f 1 = 0)) (map_one f)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (0 = 1 ↔ 1 = 0)) (propext eq_comm))) (iff.refl (1 = 0)))

/-- `f : R →+* S` has a trivial codomain iff it has a trivial range. -/
theorem codomain_trivial_iff_range_trivial {α : Type u} {β : Type v} {rα : semiring α} {rβ : semiring β} (f : α →+* β) : 0 = 1 ↔ ∀ (x : α), coe_fn f x = 0 := sorry

/-- `f : R →+* S` has a trivial codomain iff its range is `{0}`. -/
theorem codomain_trivial_iff_range_eq_singleton_zero {α : Type u} {β : Type v} {rα : semiring α} {rβ : semiring β} (f : α →+* β) : 0 = 1 ↔ set.range ⇑f = singleton 0 := sorry

/-- `f : R →+* S` doesn't map `1` to `0` if `S` is nontrivial -/
theorem map_one_ne_zero {α : Type u} {β : Type v} {rα : semiring α} {rβ : semiring β} (f : α →+* β) [nontrivial β] : coe_fn f 1 ≠ 0 :=
  mt (iff.mpr (codomain_trivial_iff_map_one_eq_zero f)) zero_ne_one

/-- If there is a homomorphism `f : R →+* S` and `S` is nontrivial, then `R` is nontrivial. -/
theorem domain_nontrivial {α : Type u} {β : Type v} {rα : semiring α} {rβ : semiring β} (f : α →+* β) [nontrivial β] : nontrivial α := sorry

theorem is_unit_map {α : Type u} {β : Type v} {rα : semiring α} {rβ : semiring β} (f : α →+* β) {a : α} (h : is_unit a) : is_unit (coe_fn f a) :=
  is_unit.map (to_monoid_hom f) h

/-- The identity ring homomorphism from a semiring to itself. -/
def id (α : Type u_1) [semiring α] : α →+* α :=
  mk id sorry sorry sorry sorry

protected instance inhabited {α : Type u} [rα : semiring α] : Inhabited (α →+* α) :=
  { default := id α }

@[simp] theorem id_apply {α : Type u} [rα : semiring α] (x : α) : coe_fn (id α) x = x :=
  rfl

/-- Composition of ring homomorphisms is a ring homomorphism. -/
def comp {α : Type u} {β : Type v} {γ : Type w} [rα : semiring α] [rβ : semiring β] {rγ : semiring γ} (hnp : β →+* γ) (hmn : α →+* β) : α →+* γ :=
  mk (⇑hnp ∘ ⇑hmn) sorry sorry sorry sorry

/-- Composition of semiring homomorphisms is associative. -/
theorem comp_assoc {α : Type u} {β : Type v} {γ : Type w} [rα : semiring α] [rβ : semiring β] {rγ : semiring γ} {δ : Type u_1} {rδ : semiring δ} (f : α →+* β) (g : β →+* γ) (h : γ →+* δ) : comp (comp h g) f = comp h (comp g f) :=
  rfl

@[simp] theorem coe_comp {α : Type u} {β : Type v} {γ : Type w} [rα : semiring α] [rβ : semiring β] {rγ : semiring γ} (hnp : β →+* γ) (hmn : α →+* β) : ⇑(comp hnp hmn) = ⇑hnp ∘ ⇑hmn :=
  rfl

theorem comp_apply {α : Type u} {β : Type v} {γ : Type w} [rα : semiring α] [rβ : semiring β] {rγ : semiring γ} (hnp : β →+* γ) (hmn : α →+* β) (x : α) : coe_fn (comp hnp hmn) x = coe_fn hnp (coe_fn hmn x) :=
  rfl

@[simp] theorem comp_id {α : Type u} {β : Type v} [rα : semiring α] [rβ : semiring β] (f : α →+* β) : comp f (id α) = f :=
  ext fun (x : α) => rfl

@[simp] theorem id_comp {α : Type u} {β : Type v} [rα : semiring α] [rβ : semiring β] (f : α →+* β) : comp (id β) f = f :=
  ext fun (x : α) => rfl

protected instance monoid {α : Type u} [rα : semiring α] : monoid (α →+* α) :=
  monoid.mk comp sorry (id α) id_comp comp_id

theorem one_def {α : Type u} [rα : semiring α] : 1 = id α :=
  rfl

@[simp] theorem coe_one {α : Type u} [rα : semiring α] : ⇑1 = id :=
  rfl

theorem mul_def {α : Type u} [rα : semiring α] (f : α →+* α) (g : α →+* α) : f * g = comp f g :=
  rfl

@[simp] theorem coe_mul {α : Type u} [rα : semiring α] (f : α →+* α) (g : α →+* α) : ⇑(f * g) = ⇑f ∘ ⇑g :=
  rfl

theorem cancel_right {α : Type u} {β : Type v} {γ : Type w} [rα : semiring α] [rβ : semiring β] {rγ : semiring γ} {g₁ : β →+* γ} {g₂ : β →+* γ} {f : α →+* β} (hf : function.surjective ⇑f) : comp g₁ f = comp g₂ f ↔ g₁ = g₂ :=
  { mp := fun (h : comp g₁ f = comp g₂ f) => ext (iff.mp (forall_iff_forall_surj hf) (iff.mp ext_iff h)),
    mpr := fun (h : g₁ = g₂) => h ▸ rfl }

theorem cancel_left {α : Type u} {β : Type v} {γ : Type w} [rα : semiring α] [rβ : semiring β] {rγ : semiring γ} {g : β →+* γ} {f₁ : α →+* β} {f₂ : α →+* β} (hg : function.injective ⇑g) : comp g f₁ = comp g f₂ ↔ f₁ = f₂ := sorry

end ring_hom


/-- A commutative semiring is a `semiring` with commutative multiplication. In other words, it is a
type with the following structures: additive commutative monoid (`add_comm_monoid`), multiplicative
commutative monoid (`comm_monoid`), distributive laws (`distrib`), and multiplication by zero law
(`mul_zero_class`). -/
class comm_semiring (α : Type u) 
extends semiring α, comm_monoid α
where

protected instance comm_semiring.to_comm_monoid_with_zero {α : Type u} [comm_semiring α] : comm_monoid_with_zero α :=
  comm_monoid_with_zero.mk comm_monoid.mul sorry comm_monoid.one sorry sorry sorry semiring.zero sorry sorry

/-- Pullback a `semiring` instance along an injective function. -/
protected def function.injective.comm_semiring {α : Type u} {γ : Type w} [comm_semiring α] [HasZero γ] [HasOne γ] [Add γ] [Mul γ] (f : γ → α) (hf : function.injective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ (x y : γ), f (x + y) = f x + f y) (mul : ∀ (x y : γ), f (x * y) = f x * f y) : comm_semiring γ :=
  comm_semiring.mk semiring.add sorry semiring.zero sorry sorry sorry semiring.mul sorry semiring.one sorry sorry sorry
    sorry sorry sorry sorry

/-- Pullback a `semiring` instance along an injective function. -/
protected def function.surjective.comm_semiring {α : Type u} {γ : Type w} [comm_semiring α] [HasZero γ] [HasOne γ] [Add γ] [Mul γ] (f : α → γ) (hf : function.surjective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ (x y : α), f (x + y) = f x + f y) (mul : ∀ (x y : α), f (x * y) = f x * f y) : comm_semiring γ :=
  comm_semiring.mk semiring.add sorry semiring.zero sorry sorry sorry semiring.mul sorry semiring.one sorry sorry sorry
    sorry sorry sorry sorry

theorem add_mul_self_eq {α : Type u} [comm_semiring α] (a : α) (b : α) : (a + b) * (a + b) = a * a + bit0 1 * a * b + b * b := sorry

@[simp] theorem two_dvd_bit0 {α : Type u} [comm_semiring α] {a : α} : bit0 1 ∣ bit0 a :=
  Exists.intro a (bit0_eq_two_mul a)

theorem ring_hom.map_dvd {α : Type u} {β : Type v} [comm_semiring α] [comm_semiring β] (f : α →+* β) {a : α} {b : α} : a ∣ b → coe_fn f a ∣ coe_fn f b := sorry

/-!
### Rings
-/

/-- A ring is a type with the following structures: additive commutative group (`add_comm_group`),
multiplicative monoid (`monoid`), and distributive laws (`distrib`).  Equivalently, a ring is a
`semiring` with a negation operation making it an additive group.  -/
class ring (α : Type u) 
extends monoid α, distrib α, add_comm_group α
where

/- The instance from `ring` to `semiring` happens often in linear algebra, for which all the basic
definitions are given in terms of semirings, but many applications use rings or fields. We increase
a little bit its priority above 100 to try it quickly, but remaining below the default 1000 so that
more specific instances are tried first. -/

protected instance ring.to_semiring {α : Type u} [ring α] : semiring α :=
  semiring.mk ring.add ring.add_assoc ring.zero ring.zero_add ring.add_zero ring.add_comm ring.mul ring.mul_assoc ring.one
    ring.one_mul ring.mul_one sorry sorry ring.left_distrib ring.right_distrib

/-- Pullback a `ring` instance along an injective function. -/
protected def function.injective.ring {α : Type u} {β : Type v} [ring α] [HasZero β] [HasOne β] [Add β] [Mul β] [Neg β] (f : β → α) (hf : function.injective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ (x y : β), f (x + y) = f x + f y) (mul : ∀ (x y : β), f (x * y) = f x * f y) (neg : ∀ (x : β), f (-x) = -f x) : ring β :=
  ring.mk add_comm_group.add sorry add_comm_group.zero sorry sorry add_comm_group.neg add_comm_group.sub sorry sorry
    monoid.mul sorry monoid.one sorry sorry sorry sorry

/-- Pullback a `ring` instance along an injective function,
with a subtraction (`-`) that is not necessarily defeq to `a + -b`. -/
protected def function.injective.ring_sub {α : Type u} {β : Type v} [ring α] [HasZero β] [HasOne β] [Add β] [Mul β] [Neg β] [Sub β] (f : β → α) (hf : function.injective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ (x y : β), f (x + y) = f x + f y) (mul : ∀ (x y : β), f (x * y) = f x * f y) (neg : ∀ (x : β), f (-x) = -f x) (sub : ∀ (x y : β), f (x - y) = f x - f y) : ring β :=
  ring.mk add_comm_group.add sorry add_comm_group.zero sorry sorry add_comm_group.neg add_comm_group.sub sorry sorry
    monoid.mul sorry monoid.one sorry sorry sorry sorry

/-- Pullback a `ring` instance along an injective function. -/
protected def function.surjective.ring {α : Type u} {β : Type v} [ring α] [HasZero β] [HasOne β] [Add β] [Mul β] [Neg β] (f : α → β) (hf : function.surjective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ (x y : α), f (x + y) = f x + f y) (mul : ∀ (x y : α), f (x * y) = f x * f y) (neg : ∀ (x : α), f (-x) = -f x) : ring β :=
  ring.mk add_comm_group.add sorry add_comm_group.zero sorry sorry add_comm_group.neg add_comm_group.sub sorry sorry
    monoid.mul sorry monoid.one sorry sorry sorry sorry

/-- Pullback a `ring` instance along an injective function,
with a subtraction (`-`) that is not necessarily defeq to `a + -b`. -/
protected def function.surjective.ring_sub {α : Type u} {β : Type v} [ring α] [HasZero β] [HasOne β] [Add β] [Mul β] [Neg β] [Sub β] (f : α → β) (hf : function.surjective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ (x y : α), f (x + y) = f x + f y) (mul : ∀ (x y : α), f (x * y) = f x * f y) (neg : ∀ (x : α), f (-x) = -f x) (sub : ∀ (x y : α), f (x - y) = f x - f y) : ring β :=
  ring.mk add_comm_group.add sorry add_comm_group.zero sorry sorry add_comm_group.neg add_comm_group.sub sorry sorry
    monoid.mul sorry monoid.one sorry sorry sorry sorry

theorem neg_mul_eq_neg_mul {α : Type u} [ring α] (a : α) (b : α) : -(a * b) = -a * b := sorry

theorem neg_mul_eq_mul_neg {α : Type u} [ring α] (a : α) (b : α) : -(a * b) = a * -b := sorry

@[simp] theorem neg_mul_eq_neg_mul_symm {α : Type u} [ring α] (a : α) (b : α) : -a * b = -(a * b) :=
  Eq.symm (neg_mul_eq_neg_mul a b)

@[simp] theorem mul_neg_eq_neg_mul_symm {α : Type u} [ring α] (a : α) (b : α) : a * -b = -(a * b) :=
  Eq.symm (neg_mul_eq_mul_neg a b)

theorem neg_mul_neg {α : Type u} [ring α] (a : α) (b : α) : -a * -b = a * b := sorry

theorem neg_mul_comm {α : Type u} [ring α] (a : α) (b : α) : -a * b = a * -b := sorry

theorem neg_eq_neg_one_mul {α : Type u} [ring α] (a : α) : -a = -1 * a := sorry

theorem mul_sub_left_distrib {α : Type u} [ring α] (a : α) (b : α) (c : α) : a * (b - c) = a * b - a * c := sorry

theorem mul_sub {α : Type u} [ring α] (a : α) (b : α) (c : α) : a * (b - c) = a * b - a * c :=
  mul_sub_left_distrib

theorem mul_sub_right_distrib {α : Type u} [ring α] (a : α) (b : α) (c : α) : (a - b) * c = a * c - b * c := sorry

theorem sub_mul {α : Type u} [ring α] (a : α) (b : α) (c : α) : (a - b) * c = a * c - b * c :=
  mul_sub_right_distrib

/-- An element of a ring multiplied by the additive inverse of one is the element's additive
  inverse. -/
theorem mul_neg_one {α : Type u} [ring α] (a : α) : a * -1 = -a := sorry

/-- The additive inverse of one multiplied by an element of a ring is the element's additive
  inverse. -/
theorem neg_one_mul {α : Type u} [ring α] (a : α) : -1 * a = -a := sorry

/-- An iff statement following from right distributivity in rings and the definition
  of subtraction. -/
theorem mul_add_eq_mul_add_iff_sub_mul_add_eq {α : Type u} [ring α] {a : α} {b : α} {c : α} {d : α} {e : α} : a * e + c = b * e + d ↔ (a - b) * e + c = d := sorry

/-- A simplification of one side of an equation exploiting right distributivity in rings
  and the definition of subtraction. -/
theorem sub_mul_add_eq_of_mul_add_eq_mul_add {α : Type u} [ring α] {a : α} {b : α} {c : α} {d : α} {e : α} : a * e + c = b * e + d → (a - b) * e + c = d := sorry

namespace units


/-- Each element of the group of units of a ring has an additive inverse. -/
protected instance has_neg {α : Type u} [ring α] : Neg (units α) :=
  { neg := fun (u : units α) => mk (-↑u) (-↑(u⁻¹)) sorry sorry }

/-- Representing an element of a ring's unit group as an element of the ring commutes with
    mapping this element to its additive inverse. -/
@[simp] protected theorem coe_neg {α : Type u} [ring α] (u : units α) : ↑(-u) = -↑u :=
  rfl

@[simp] protected theorem coe_neg_one {α : Type u} [ring α] : ↑(-1) = -1 :=
  rfl

/-- Mapping an element of a ring's unit group to its inverse commutes with mapping this element
    to its additive inverse. -/
@[simp] protected theorem neg_inv {α : Type u} [ring α] (u : units α) : -u⁻¹ = -(u⁻¹) :=
  rfl

/-- An element of a ring's unit group equals the additive inverse of its additive inverse. -/
@[simp] protected theorem neg_neg {α : Type u} [ring α] (u : units α) : --u = u :=
  ext (neg_neg ↑u)

/-- Multiplication of elements of a ring's unit group commutes with mapping the first
    argument to its additive inverse. -/
@[simp] protected theorem neg_mul {α : Type u} [ring α] (u₁ : units α) (u₂ : units α) : -u₁ * u₂ = -(u₁ * u₂) :=
  ext (neg_mul_eq_neg_mul_symm (↑u₁) (val u₂))

/-- Multiplication of elements of a ring's unit group commutes with mapping the second argument
    to its additive inverse. -/
@[simp] protected theorem mul_neg {α : Type u} [ring α] (u₁ : units α) (u₂ : units α) : u₁ * -u₂ = -(u₁ * u₂) :=
  ext (Eq.symm (neg_mul_eq_mul_neg (val u₁) ↑u₂))

/-- Multiplication of the additive inverses of two elements of a ring's unit group equals
    multiplication of the two original elements. -/
@[simp] protected theorem neg_mul_neg {α : Type u} [ring α] (u₁ : units α) (u₂ : units α) : -u₁ * -u₂ = u₁ * u₂ := sorry

/-- The additive inverse of an element of a ring's unit group equals the additive inverse of
    one times the original element. -/
protected theorem neg_eq_neg_one_mul {α : Type u} [ring α] (u : units α) : -u = -1 * u := sorry

end units


namespace ring_hom


/-- Ring homomorphisms preserve additive inverse. -/
@[simp] theorem map_neg {α : Type u_1} {β : Type u_2} [ring α] [ring β] (f : α →+* β) (x : α) : coe_fn f (-x) = -coe_fn f x :=
  add_monoid_hom.map_neg (↑f) x

/-- Ring homomorphisms preserve subtraction. -/
@[simp] theorem map_sub {α : Type u_1} {β : Type u_2} [ring α] [ring β] (f : α →+* β) (x : α) (y : α) : coe_fn f (x - y) = coe_fn f x - coe_fn f y :=
  add_monoid_hom.map_sub (↑f) x y

/-- A ring homomorphism is injective iff its kernel is trivial. -/
theorem injective_iff {α : Type u_1} {β : Type u_2} [ring α] [semiring β] (f : α →+* β) : function.injective ⇑f ↔ ∀ (a : α), coe_fn f a = 0 → a = 0 :=
  add_monoid_hom.injective_iff ↑f

/-- Makes a ring homomorphism from a monoid homomorphism of rings which preserves addition. -/
def mk' {α : Type u} {γ : Type u_1} [semiring α] [ring γ] (f : α →* γ) (map_add : ∀ (a b : α), coe_fn f (a + b) = coe_fn f a + coe_fn f b) : α →+* γ :=
  mk ⇑f sorry sorry sorry sorry

end ring_hom


/-- A commutative ring is a `ring` with commutative multiplication. -/
class comm_ring (α : Type u) 
extends ring α, comm_semigroup α
where

protected instance comm_ring.to_comm_semiring {α : Type u} [s : comm_ring α] : comm_semiring α :=
  comm_semiring.mk comm_ring.add comm_ring.add_assoc comm_ring.zero comm_ring.zero_add comm_ring.add_zero
    comm_ring.add_comm comm_ring.mul comm_ring.mul_assoc comm_ring.one comm_ring.one_mul comm_ring.mul_one sorry sorry
    comm_ring.left_distrib comm_ring.right_distrib comm_ring.mul_comm

/-- Pullback a `comm_ring` instance along an injective function. -/
protected def function.injective.comm_ring {α : Type u} {β : Type v} [comm_ring α] [HasZero β] [HasOne β] [Add β] [Mul β] [Neg β] (f : β → α) (hf : function.injective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ (x y : β), f (x + y) = f x + f y) (mul : ∀ (x y : β), f (x * y) = f x * f y) (neg : ∀ (x : β), f (-x) = -f x) : comm_ring β :=
  comm_ring.mk ring.add sorry ring.zero sorry sorry ring.neg ring.sub sorry sorry ring.mul sorry ring.one sorry sorry
    sorry sorry sorry

/-- Pullback a `comm_ring` instance along an injective function,
with a subtraction (`-`) that is not necessarily defeq to `a + -b`. -/
protected def function.injective.comm_ring_sub {α : Type u} {β : Type v} [comm_ring α] [HasZero β] [HasOne β] [Add β] [Mul β] [Neg β] [Sub β] (f : β → α) (hf : function.injective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ (x y : β), f (x + y) = f x + f y) (mul : ∀ (x y : β), f (x * y) = f x * f y) (neg : ∀ (x : β), f (-x) = -f x) (sub : ∀ (x y : β), f (x - y) = f x - f y) : comm_ring β :=
  comm_ring.mk ring.add sorry ring.zero sorry sorry ring.neg ring.sub sorry sorry ring.mul sorry ring.one sorry sorry
    sorry sorry sorry

/-- Pullback a `comm_ring` instance along an injective function. -/
protected def function.surjective.comm_ring {α : Type u} {β : Type v} [comm_ring α] [HasZero β] [HasOne β] [Add β] [Mul β] [Neg β] (f : α → β) (hf : function.surjective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ (x y : α), f (x + y) = f x + f y) (mul : ∀ (x y : α), f (x * y) = f x * f y) (neg : ∀ (x : α), f (-x) = -f x) : comm_ring β :=
  comm_ring.mk ring.add sorry ring.zero sorry sorry ring.neg ring.sub sorry sorry ring.mul sorry ring.one sorry sorry
    sorry sorry sorry

/-- Pullback a `comm_ring` instance along an injective function,
with a subtraction (`-`) that is not necessarily defeq to `a + -b`. -/
protected def function.surjective.comm_ring_sub {α : Type u} {β : Type v} [comm_ring α] [HasZero β] [HasOne β] [Add β] [Mul β] [Neg β] [Sub β] (f : α → β) (hf : function.surjective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ (x y : α), f (x + y) = f x + f y) (mul : ∀ (x y : α), f (x * y) = f x * f y) (neg : ∀ (x : α), f (-x) = -f x) (sub : ∀ (x y : α), f (x - y) = f x - f y) : comm_ring β :=
  comm_ring.mk ring.add sorry ring.zero sorry sorry ring.neg ring.sub sorry sorry ring.mul sorry ring.one sorry sorry
    sorry sorry sorry

theorem dvd_neg_of_dvd {α : Type u} [comm_ring α] {a : α} {b : α} (h : a ∣ b) : a ∣ -b := sorry

theorem dvd_of_dvd_neg {α : Type u} [comm_ring α] {a : α} {b : α} (h : a ∣ -b) : a ∣ b :=
  let t : a ∣ --b := dvd_neg_of_dvd h;
  eq.mp (Eq._oldrec (Eq.refl (a ∣ --b)) (neg_neg b)) t

theorem dvd_neg_iff_dvd {α : Type u} [comm_ring α] (a : α) (b : α) : a ∣ -b ↔ a ∣ b :=
  { mp := dvd_of_dvd_neg, mpr := dvd_neg_of_dvd }

theorem neg_dvd_of_dvd {α : Type u} [comm_ring α] {a : α} {b : α} (h : a ∣ b) : -a ∣ b := sorry

theorem dvd_of_neg_dvd {α : Type u} [comm_ring α] {a : α} {b : α} (h : -a ∣ b) : a ∣ b :=
  let t : --a ∣ b := neg_dvd_of_dvd h;
  eq.mp (Eq._oldrec (Eq.refl ( --a ∣ b)) (neg_neg a)) t

theorem neg_dvd_iff_dvd {α : Type u} [comm_ring α] (a : α) (b : α) : -a ∣ b ↔ a ∣ b :=
  { mp := dvd_of_neg_dvd, mpr := neg_dvd_of_dvd }

theorem dvd_sub {α : Type u} [comm_ring α] {a : α} {b : α} {c : α} (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b - c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ∣ b - c)) (sub_eq_add_neg b c))) (dvd_add h₁ (dvd_neg_of_dvd h₂))

theorem dvd_add_iff_left {α : Type u} [comm_ring α] {a : α} {b : α} {c : α} (h : a ∣ c) : a ∣ b ↔ a ∣ b + c :=
  { mp := fun (h₂ : a ∣ b) => dvd_add h₂ h,
    mpr := fun (H : a ∣ b + c) => eq.mp (Eq._oldrec (Eq.refl (a ∣ b + c - c)) (add_sub_cancel b c)) (dvd_sub H h) }

theorem dvd_add_iff_right {α : Type u} [comm_ring α] {a : α} {b : α} {c : α} (h : a ∣ b) : a ∣ c ↔ a ∣ b + c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ∣ c ↔ a ∣ b + c)) (add_comm b c))) (dvd_add_iff_left h)

theorem two_dvd_bit1 {α : Type u} [comm_ring α] {a : α} : bit0 1 ∣ bit1 a ↔ bit0 1 ∣ 1 :=
  iff.symm (dvd_add_iff_right two_dvd_bit0)

/-- Representation of a difference of two squares in a commutative ring as a product. -/
theorem mul_self_sub_mul_self {α : Type u} [comm_ring α] (a : α) (b : α) : a * a - b * b = (a + b) * (a - b) := sorry

theorem mul_self_sub_one {α : Type u} [comm_ring α] (a : α) : a * a - 1 = (a + 1) * (a - 1) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a * a - 1 = (a + 1) * (a - 1))) (Eq.symm (mul_self_sub_mul_self a 1))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * a - 1 = a * a - 1 * 1)) (mul_one 1))) (Eq.refl (a * a - 1)))

/-- An element a of a commutative ring divides the additive inverse of an element b iff a
  divides b. -/
@[simp] theorem dvd_neg {α : Type u} [comm_ring α] (a : α) (b : α) : a ∣ -b ↔ a ∣ b :=
  { mp := dvd_of_dvd_neg, mpr := dvd_neg_of_dvd }

/-- The additive inverse of an element a of a commutative ring divides another element b iff a
  divides b. -/
@[simp] theorem neg_dvd {α : Type u} [comm_ring α] (a : α) (b : α) : -a ∣ b ↔ a ∣ b :=
  { mp := dvd_of_neg_dvd, mpr := neg_dvd_of_dvd }

/-- If an element a divides another element c in a commutative ring, a divides the sum of another
  element b with c iff a divides b. -/
theorem dvd_add_left {α : Type u} [comm_ring α] {a : α} {b : α} {c : α} (h : a ∣ c) : a ∣ b + c ↔ a ∣ b :=
  iff.symm (dvd_add_iff_left h)

/-- If an element a divides another element b in a commutative ring, a divides the sum of b and
  another element c iff a divides c. -/
theorem dvd_add_right {α : Type u} [comm_ring α] {a : α} {b : α} {c : α} (h : a ∣ b) : a ∣ b + c ↔ a ∣ c :=
  iff.symm (dvd_add_iff_right h)

/-- An element a divides the sum a + b if and only if a divides b.-/
@[simp] theorem dvd_add_self_left {α : Type u} [comm_ring α] {a : α} {b : α} : a ∣ a + b ↔ a ∣ b :=
  dvd_add_right (dvd_refl a)

/-- An element a divides the sum b + a if and only if a divides b.-/
@[simp] theorem dvd_add_self_right {α : Type u} [comm_ring α] {a : α} {b : α} : a ∣ b + a ↔ a ∣ b :=
  dvd_add_left (dvd_refl a)

/-- Vieta's formula for a quadratic equation, relating the coefficients of the polynomial with
  its roots. This particular version states that if we have a root `x` of a monic quadratic
  polynomial, then there is another root `y` such that `x + y` is negative the `a_1` coefficient
  and `x * y` is the `a_0` coefficient. -/
theorem Vieta_formula_quadratic {α : Type u} [comm_ring α] {b : α} {c : α} {x : α} (h : x * x - b * x + c = 0) : ∃ (y : α), y * y - b * y + c = 0 ∧ x + y = b ∧ x * y = c := sorry

theorem dvd_mul_sub_mul {α : Type u} [comm_ring α] {k : α} {a : α} {b : α} {x : α} {y : α} (hab : k ∣ a - b) (hxy : k ∣ x - y) : k ∣ a * x - b * y := sorry

theorem dvd_iff_dvd_of_dvd_sub {α : Type u} [comm_ring α] {a : α} {b : α} {c : α} (h : a ∣ b - c) : a ∣ b ↔ a ∣ c := sorry

theorem succ_ne_self {α : Type u} [ring α] [nontrivial α] (a : α) : a + 1 ≠ a := sorry

theorem pred_ne_self {α : Type u} [ring α] [nontrivial α] (a : α) : a - 1 ≠ a := sorry

/-- A domain is a ring with no zero divisors, i.e. satisfying
  the condition `a * b = 0 ↔ a = 0 ∨ b = 0`. Alternatively, a domain
  is an integral domain without assuming commutativity of multiplication. -/
class domain (α : Type u) 
extends ring α, nontrivial α
where
  eq_zero_or_eq_zero_of_mul_eq_zero : ∀ (a b : α), a * b = 0 → a = 0 ∨ b = 0

protected instance domain.to_no_zero_divisors {α : Type u} [domain α] : no_zero_divisors α :=
  no_zero_divisors.mk domain.eq_zero_or_eq_zero_of_mul_eq_zero

protected instance domain.to_cancel_monoid_with_zero {α : Type u} [domain α] : cancel_monoid_with_zero α :=
  cancel_monoid_with_zero.mk semiring.mul sorry semiring.one sorry sorry semiring.zero sorry sorry sorry sorry

/-- Pullback a `domain` instance along an injective function. -/
protected def function.injective.domain {α : Type u} {β : Type v} [domain α] [HasZero β] [HasOne β] [Add β] [Mul β] [Neg β] (f : β → α) (hf : function.injective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ (x y : β), f (x + y) = f x + f y) (mul : ∀ (x y : β), f (x * y) = f x * f y) (neg : ∀ (x : β), f (-x) = -f x) : domain β :=
  domain.mk ring.add sorry ring.zero sorry sorry ring.neg ring.sub sorry sorry ring.mul sorry ring.one sorry sorry sorry
    sorry sorry sorry

/-!
### Integral domains
-/

/-- An integral domain is a commutative ring with no zero divisors, i.e. satisfying the condition
`a * b = 0 ↔ a = 0 ∨ b = 0`. Alternatively, an integral domain is a domain with commutative
multiplication. -/
class integral_domain (α : Type u) 
extends comm_ring α, domain α
where

protected instance integral_domain.to_comm_cancel_monoid_with_zero {α : Type u} [integral_domain α] : comm_cancel_monoid_with_zero α :=
  comm_cancel_monoid_with_zero.mk comm_monoid_with_zero.mul sorry comm_monoid_with_zero.one sorry sorry sorry
    comm_monoid_with_zero.zero sorry sorry sorry sorry

/-- Pullback an `integral_domain` instance along an injective function. -/
protected def function.injective.integral_domain {α : Type u} {β : Type v} [integral_domain α] [HasZero β] [HasOne β] [Add β] [Mul β] [Neg β] (f : β → α) (hf : function.injective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ (x y : β), f (x + y) = f x + f y) (mul : ∀ (x y : β), f (x * y) = f x * f y) (neg : ∀ (x : β), f (-x) = -f x) : integral_domain β :=
  integral_domain.mk comm_ring.add sorry comm_ring.zero sorry sorry comm_ring.neg comm_ring.sub sorry sorry comm_ring.mul
    sorry comm_ring.one sorry sorry sorry sorry sorry sorry sorry

theorem mul_self_eq_mul_self_iff {α : Type u} [integral_domain α] {a : α} {b : α} : a * a = b * b ↔ a = b ∨ a = -b := sorry

theorem mul_self_eq_one_iff {α : Type u} [integral_domain α] {a : α} : a * a = 1 ↔ a = 1 ∨ a = -1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a * a = 1 ↔ a = 1 ∨ a = -1)) (Eq.symm (propext mul_self_eq_mul_self_iff))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * a = 1 ↔ a * a = 1 * 1)) (one_mul 1))) (iff.refl (a * a = 1)))

/-- In the unit group of an integral domain, a unit is its own inverse iff the unit is one or
  one's additive inverse. -/
theorem units.inv_eq_self_iff {α : Type u} [integral_domain α] (u : units α) : u⁻¹ = u ↔ u = 1 ∨ u = -1 := sorry

namespace ring


/-- Introduce a function `inverse` on a ring `R`, which sends `x` to `x⁻¹` if `x` is invertible and
to `0` otherwise.  This definition is somewhat ad hoc, but one needs a fully (rather than partially)
defined inverse function for some purposes, including for calculus. -/
def inverse {R : Type x} [ring R] : R → R :=
  fun (x : R) => dite (is_unit x) (fun (h : is_unit x) => ↑(classical.some h⁻¹)) fun (h : ¬is_unit x) => 0

/-- By definition, if `x` is invertible then `inverse x = x⁻¹`. -/
@[simp] theorem inverse_unit {R : Type x} [ring R] (a : units R) : inverse ↑a = ↑(a⁻¹) := sorry

/-- By definition, if `x` is not invertible then `inverse x = 0`. -/
@[simp] theorem inverse_non_unit {R : Type x} [ring R] (x : R) (h : ¬is_unit x) : inverse x = 0 :=
  dif_neg h

end ring


/-- A predicate to express that a ring is an integral domain.

This is mainly useful because such a predicate does not contain data,
and can therefore be easily transported along ring isomorphisms. -/
structure is_integral_domain (R : Type u) [ring R] 
extends nontrivial R
where
  mul_comm : ∀ (x y : R), x * y = y * x
  eq_zero_or_eq_zero_of_mul_eq_zero : ∀ (x y : R), x * y = 0 → x = 0 ∨ y = 0

-- The linter does not recognize that is_integral_domain.to_nontrivial is a structure

-- projection, disable it

/-- Every integral domain satisfies the predicate for integral domains. -/
theorem integral_domain.to_is_integral_domain (R : Type u) [integral_domain R] : is_integral_domain R :=
  is_integral_domain.mk integral_domain.exists_pair_ne integral_domain.mul_comm
    integral_domain.eq_zero_or_eq_zero_of_mul_eq_zero

/-- If a ring satisfies the predicate for integral domains,
then it can be endowed with an `integral_domain` instance
whose data is definitionally equal to the existing data. -/
def is_integral_domain.to_integral_domain (R : Type u) [ring R] (h : is_integral_domain R) : integral_domain R :=
  integral_domain.mk ring.add ring.add_assoc ring.zero ring.zero_add ring.add_zero ring.neg ring.sub ring.add_left_neg
    ring.add_comm ring.mul ring.mul_assoc ring.one ring.one_mul ring.mul_one ring.left_distrib ring.right_distrib
    (is_integral_domain.mul_comm h) (is_integral_domain.exists_pair_ne h)
    (is_integral_domain.eq_zero_or_eq_zero_of_mul_eq_zero h)

namespace semiconj_by


@[simp] theorem add_right {R : Type x} [distrib R] {a : R} {x : R} {y : R} {x' : R} {y' : R} (h : semiconj_by a x y) (h' : semiconj_by a x' y') : semiconj_by a (x + x') (y + y') := sorry

@[simp] theorem add_left {R : Type x} [distrib R] {a : R} {b : R} {x : R} {y : R} (ha : semiconj_by a x y) (hb : semiconj_by b x y) : semiconj_by (a + b) x y := sorry

theorem neg_right {R : Type x} [ring R] {a : R} {x : R} {y : R} (h : semiconj_by a x y) : semiconj_by a (-x) (-y) := sorry

@[simp] theorem neg_right_iff {R : Type x} [ring R] {a : R} {x : R} {y : R} : semiconj_by a (-x) (-y) ↔ semiconj_by a x y :=
  { mp := fun (h : semiconj_by a (-x) (-y)) => neg_neg x ▸ neg_neg y ▸ neg_right h, mpr := neg_right }

theorem neg_left {R : Type x} [ring R] {a : R} {x : R} {y : R} (h : semiconj_by a x y) : semiconj_by (-a) x y := sorry

@[simp] theorem neg_left_iff {R : Type x} [ring R] {a : R} {x : R} {y : R} : semiconj_by (-a) x y ↔ semiconj_by a x y :=
  { mp := fun (h : semiconj_by (-a) x y) => neg_neg a ▸ neg_left h, mpr := neg_left }

@[simp] theorem neg_one_right {R : Type x} [ring R] (a : R) : semiconj_by a (-1) (-1) :=
  neg_right (one_right a)

@[simp] theorem neg_one_left {R : Type x} [ring R] (x : R) : semiconj_by (-1) x x :=
  neg_left (one_left x)

@[simp] theorem sub_right {R : Type x} [ring R] {a : R} {x : R} {y : R} {x' : R} {y' : R} (h : semiconj_by a x y) (h' : semiconj_by a x' y') : semiconj_by a (x - x') (y - y') := sorry

@[simp] theorem sub_left {R : Type x} [ring R] {a : R} {b : R} {x : R} {y : R} (ha : semiconj_by a x y) (hb : semiconj_by b x y) : semiconj_by (a - b) x y := sorry

end semiconj_by


namespace commute


@[simp] theorem add_right {R : Type x} [distrib R] {a : R} {b : R} {c : R} : commute a b → commute a c → commute a (b + c) :=
  semiconj_by.add_right

@[simp] theorem add_left {R : Type x} [distrib R] {a : R} {b : R} {c : R} : commute a c → commute b c → commute (a + b) c :=
  semiconj_by.add_left

theorem neg_right {R : Type x} [ring R] {a : R} {b : R} : commute a b → commute a (-b) :=
  semiconj_by.neg_right

@[simp] theorem neg_right_iff {R : Type x} [ring R] {a : R} {b : R} : commute a (-b) ↔ commute a b :=
  semiconj_by.neg_right_iff

theorem neg_left {R : Type x} [ring R] {a : R} {b : R} : commute a b → commute (-a) b :=
  semiconj_by.neg_left

@[simp] theorem neg_left_iff {R : Type x} [ring R] {a : R} {b : R} : commute (-a) b ↔ commute a b :=
  semiconj_by.neg_left_iff

@[simp] theorem neg_one_right {R : Type x} [ring R] (a : R) : commute a (-1) :=
  semiconj_by.neg_one_right a

@[simp] theorem neg_one_left {R : Type x} [ring R] (a : R) : commute (-1) a :=
  semiconj_by.neg_one_left a

@[simp] theorem sub_right {R : Type x} [ring R] {a : R} {b : R} {c : R} : commute a b → commute a c → commute a (b - c) :=
  semiconj_by.sub_right

@[simp] theorem sub_left {R : Type x} [ring R] {a : R} {b : R} {c : R} : commute a c → commute b c → commute (a - b) c :=
  semiconj_by.sub_left

