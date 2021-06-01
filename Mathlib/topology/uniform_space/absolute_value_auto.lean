/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.real.cau_seq
import Mathlib.topology.uniform_space.basic
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Uniform structure induced by an absolute value

We build a uniform space structure on a commutative ring `R` equipped with an absolute value into
a linear ordered field `𝕜`. Of course in the case `R` is `ℚ`, `ℝ` or `ℂ` and
`𝕜 = ℝ`, we get the same thing as the metric space construction, and the general construction
follows exactly the same path.

## Implementation details

Note that we import `data.real.cau_seq` because this is where absolute values are defined, but
the current file does not depend on real numbers. TODO: extract absolute values from that
`data.real` folder.

## References

* [N. Bourbaki, *Topologie générale*][bourbaki1966]

## Tags

absolute value, uniform spaces
-/

namespace is_absolute_value


/-- The uniformity coming from an absolute value. -/
def uniform_space_core {𝕜 : Type u_1} [linear_ordered_field 𝕜] {R : Type u_2} [comm_ring R]
    (abv : R → 𝕜) [is_absolute_value abv] : uniform_space.core R :=
  uniform_space.core.mk
    (infi
      fun (ε : 𝕜) =>
        infi
          fun (H : ε > 0) =>
            filter.principal (set_of fun (p : R × R) => abv (prod.snd p - prod.fst p) < ε))
    sorry sorry sorry

/-- The uniform structure coming from an absolute value. -/
def uniform_space {𝕜 : Type u_1} [linear_ordered_field 𝕜] {R : Type u_2} [comm_ring R] (abv : R → 𝕜)
    [is_absolute_value abv] : uniform_space R :=
  uniform_space.of_core (uniform_space_core abv)

theorem mem_uniformity {𝕜 : Type u_1} [linear_ordered_field 𝕜] {R : Type u_2} [comm_ring R]
    (abv : R → 𝕜) [is_absolute_value abv] {s : set (R × R)} :
    s ∈ uniform_space.core.uniformity (uniform_space_core abv) ↔
        ∃ (ε : 𝕜), ∃ (H : ε > 0), ∀ {a b : R}, abv (b - a) < ε → (a, b) ∈ s :=
  sorry

end Mathlib