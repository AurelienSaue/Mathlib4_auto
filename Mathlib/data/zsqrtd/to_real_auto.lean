/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.real.sqrt
import Mathlib.data.zsqrtd.basic
import PostPort

namespace Mathlib

/-!
# Image of `zsqrtd` in `ℝ`

This file defines `zsqrtd.to_real` and related lemmas.
It is in a separate file to avoid pulling in all of `data.real` into `data.zsqrtd`.
-/

namespace zsqrtd


/-- The image of `zsqrtd` in `ℝ`, using `real.sqrt` which takes the positive root of `d`.

If the negative root is desired, use `to_real h a.conj`. -/
@[simp] theorem to_real_apply {d : ℤ} (h : 0 ≤ d) (a : ℤ√d) : coe_fn (to_real h) a = ↑(re a) + ↑(im a) * real.sqrt ↑d :=
  Eq.refl (↑(re a) + ↑(im a) * real.sqrt ↑d)

theorem to_real_injective {d : ℤ} (h0d : 0 ≤ d) (hd : ∀ (n : ℤ), d ≠ n * n) : function.injective ⇑(to_real h0d) :=
  lift_injective { val := real.sqrt ↑d, property := to_real._proof_1 h0d } hd

