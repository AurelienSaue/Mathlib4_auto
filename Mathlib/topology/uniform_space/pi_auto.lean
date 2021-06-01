/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.uniform_space.cauchy
import Mathlib.topology.uniform_space.separation
import Mathlib.PostPort

universes u u_1 

namespace Mathlib

/-!
# Indexed product of uniform spaces
-/

protected instance Pi.uniform_space {ι : Type u_1} (α : ι → Type u)
    [U : (i : ι) → uniform_space (α i)] : uniform_space ((i : ι) → α i) :=
  uniform_space.of_core_eq uniform_space.to_core Pi.topological_space sorry

theorem Pi.uniformity {ι : Type u_1} (α : ι → Type u) [U : (i : ι) → uniform_space (α i)] :
    uniformity ((i : ι) → α i) =
        infi
          fun (i : ι) =>
            filter.comap
              (fun (a : ((i : ι) → α i) × ((i : ι) → α i)) => (prod.fst a i, prod.snd a i))
              (uniformity (α i)) :=
  infi_uniformity

theorem Pi.uniform_continuous_proj {ι : Type u_1} (α : ι → Type u)
    [U : (i : ι) → uniform_space (α i)] (i : ι) :
    uniform_continuous fun (a : (i : ι) → α i) => a i :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (uniform_continuous fun (a : (i : ι) → α i) => a i))
        (propext uniform_continuous_iff)))
    (infi_le (fun (j : ι) => uniform_space.comap (fun (a : (i : ι) → α i) => a j) (U j)) i)

protected instance Pi.complete {ι : Type u_1} (α : ι → Type u) [U : (i : ι) → uniform_space (α i)]
    [∀ (i : ι), complete_space (α i)] : complete_space ((i : ι) → α i) :=
  sorry

protected instance Pi.separated {ι : Type u_1} (α : ι → Type u) [U : (i : ι) → uniform_space (α i)]
    [∀ (i : ι), separated_space (α i)] : separated_space ((i : ι) → α i) :=
  iff.mpr separated_def
    fun (x y : (i : ι) → α i)
      (H :
      ∀ (r : set (((i : ι) → α i) × ((i : ι) → α i))),
        r ∈ uniformity ((i : ι) → α i) → (x, y) ∈ r) =>
      funext
        fun (i : ι) =>
          uniform_space.eq_of_separated_of_uniform_continuous (Pi.uniform_continuous_proj α i) H

end Mathlib