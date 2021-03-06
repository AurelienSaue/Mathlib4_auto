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
a linear ordered field `π`. Of course in the case `R` is `β`, `β` or `β` and
`π = β`, we get the same thing as the metric space construction, and the general construction
follows exactly the same path.

## Implementation details

Note that we import `data.real.cau_seq` because this is where absolute values are defined, but
the current file does not depend on real numbers. TODO: extract absolute values from that
`data.real` folder.

## References

* [N. Bourbaki, *Topologie gΓ©nΓ©rale*][bourbaki1966]

## Tags

absolute value, uniform spaces
-/

namespace is_absolute_value


/-- The uniformity coming from an absolute value. -/
def uniform_space_core {π : Type u_1} [linear_ordered_field π] {R : Type u_2} [comm_ring R] (abv : R β π) [is_absolute_value abv] : uniform_space.core R :=
  uniform_space.core.mk
    (infi
      fun (Ξ΅ : π) =>
        infi fun (H : Ξ΅ > 0) => filter.principal (set_of fun (p : R Γ R) => abv (prod.snd p - prod.fst p) < Ξ΅))
    sorry sorry sorry

/-- The uniform structure coming from an absolute value. -/
def uniform_space {π : Type u_1} [linear_ordered_field π] {R : Type u_2} [comm_ring R] (abv : R β π) [is_absolute_value abv] : uniform_space R :=
  uniform_space.of_core (uniform_space_core abv)

theorem mem_uniformity {π : Type u_1} [linear_ordered_field π] {R : Type u_2} [comm_ring R] (abv : R β π) [is_absolute_value abv] {s : set (R Γ R)} : s β uniform_space.core.uniformity (uniform_space_core abv) β
  β (Ξ΅ : π), β (H : Ξ΅ > 0), β {a b : R}, abv (b - a) < Ξ΅ β (a, b) β s := sorry

