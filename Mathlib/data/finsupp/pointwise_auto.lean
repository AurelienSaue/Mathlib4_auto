/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.finsupp.basic
import Mathlib.PostPort

universes u₂ u₁ 

namespace Mathlib

/-!
# The pointwise product on `finsupp`.

TODO per issue #1864:
We intend to remove the convolution product on finsupp, and define
it only on a type synonym `add_monoid_algebra`. After we've done this,
it would be good to make this the default product on `finsupp`.
-/

namespace finsupp


/-! ### Declarations about the pointwise product on `finsupp`s -/

/-- The product of `f g : α →₀ β` is the finitely supported function
  whose value at `a` is `f a * g a`. -/
protected instance has_mul {α : Type u₁} {β : Type u₂} [mul_zero_class β] : Mul (α →₀ β) :=
  { mul := zip_with Mul.mul sorry }

@[simp] theorem mul_apply {α : Type u₁} {β : Type u₂} [mul_zero_class β] {g₁ : α →₀ β} {g₂ : α →₀ β}
    {a : α} : coe_fn (g₁ * g₂) a = coe_fn g₁ a * coe_fn g₂ a :=
  rfl

theorem support_mul {α : Type u₁} {β : Type u₂} [mul_zero_class β] {g₁ : α →₀ β} {g₂ : α →₀ β} :
    support (g₁ * g₂) ⊆ support g₁ ∩ support g₂ :=
  sorry

protected instance semigroup {α : Type u₁} {β : Type u₂} [semiring β] : semigroup (α →₀ β) :=
  semigroup.mk Mul.mul sorry

protected instance distrib {α : Type u₁} {β : Type u₂} [semiring β] : distrib (α →₀ β) :=
  distrib.mk semigroup.mul add_comm_monoid.add sorry sorry

end Mathlib