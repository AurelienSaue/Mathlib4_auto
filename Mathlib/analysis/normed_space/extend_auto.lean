/-
Copyright (c) 2020 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.analysis.complex.basic
import Mathlib.analysis.normed_space.operator_norm
import Mathlib.data.complex.is_R_or_C
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Extending a continuous `â`-linear map to a continuous `ð`-linear map

In this file we provide a way to extend a continuous `â`-linear map to a continuous `ð`-linear map
in a way that bounds the norm by the norm of the original map, when `ð` is either `â` (the
extension is trivial) or `â`. We formulate the extension uniformly, by assuming `is_R_or_C ð`.

We motivate the form of the extension as follows. Note that `fc : F ââ[ð] ð` is determined fully by
`Re fc`: for all `x : F`, `fc (I â¢ x) = I * fc x`, so `Im (fc x) = -Re (fc (I â¢ x))`. Therefore,
given an `fr : F ââ[â] â`, we define `fc x = fr x - fr (I â¢ x) * I`.
-/

/-- Extend `fr : F ââ[â] â` to `F ââ[ð] ð` in a way that will also be continuous and have its norm
bounded by `â¥frâ¥` if `fr` is continuous. -/
def linear_map.extend_to_ð {ð : Type u_1} [is_R_or_C ð] {F : Type u_2} [normed_group F]
    [normed_space ð F] (fr : linear_map â (restrict_scalars â ð F) â) : linear_map ð F ð :=
  let fc : F â ð := fun (x : F) => â(coe_fn fr x) - is_R_or_C.I * â(coe_fn fr (is_R_or_C.I â¢ x));
  linear_map.mk fc sorry sorry

/-- The norm of the extension is bounded by `â¥frâ¥`. -/
theorem norm_bound {ð : Type u_1} [is_R_or_C ð] {F : Type u_2} [normed_group F] [normed_space ð F]
    (fr : continuous_linear_map â (restrict_scalars â ð F) â) (x : F) :
    norm (coe_fn (linear_map.extend_to_ð (continuous_linear_map.to_linear_map fr)) x) â¤
        norm fr * norm x :=
  sorry

/-- Extend `fr : F âL[â] â` to `F âL[ð] ð`. -/
def continuous_linear_map.extend_to_ð {ð : Type u_1} [is_R_or_C ð] {F : Type u_2} [normed_group F]
    [normed_space ð F] (fr : continuous_linear_map â (restrict_scalars â ð F) â) :
    continuous_linear_map ð F ð :=
  linear_map.mk_continuous (linear_map.extend_to_ð (continuous_linear_map.to_linear_map fr))
    (norm fr) (norm_bound fr)

end Mathlib