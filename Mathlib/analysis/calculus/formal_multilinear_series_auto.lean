/-
Copyright (c) 2019 SΓ©bastien GouΓ«zel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: SΓ©bastien GouΓ«zel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.analysis.normed_space.multilinear
import Mathlib.ring_theory.power_series.basic
import Mathlib.PostPort

universes u_1 u_2 u_3 u_4 u_5 

namespace Mathlib

/-!
# Formal multilinear series

In this file we define `formal_multilinear_series π E F` to be a family of `n`-multilinear maps for
all `n`, designed to model the sequence of derivatives of a function. In other files we use this
notion to define `C^n` functions (called `times_cont_diff` in `mathlib`) and analytic functions.

## Notations

We use the notation `E [Γn]βL[π] F` for the space of continuous multilinear maps on `E^n` with
values in `F`. This is the space in which the `n`-th derivative of a function from `E` to `F` lives.

## Tags

multilinear, formal series
-/

/-- A formal multilinear series over a field `π`, from `E` to `F`, is given by a family of
multilinear maps from `E^n` to `F` for all `n`. -/
def formal_multilinear_series (π : Type u_1) [nondiscrete_normed_field π] (E : Type u_2)
    [normed_group E] [normed_space π E] (F : Type u_3) [normed_group F] [normed_space π F] :=
  (n : β) β continuous_multilinear_map π (fun (i : fin n) => E) F

protected instance formal_multilinear_series.inhabited {π : Type u_1} [nondiscrete_normed_field π]
    {E : Type u_2} [normed_group E] [normed_space π E] {F : Type u_3} [normed_group F]
    [normed_space π F] : Inhabited (formal_multilinear_series π E F) :=
  { default := 0 }

/- `derive` is not able to find the module structure, probably because Lean is confused by the
dependent types. We register it explicitly. -/

protected instance formal_multilinear_series.module {π : Type u_1} [nondiscrete_normed_field π]
    {E : Type u_2} [normed_group E] [normed_space π E] {F : Type u_3} [normed_group F]
    [normed_space π F] : module π (formal_multilinear_series π E F) :=
  let _inst : (n : β) β module π (continuous_multilinear_map π (fun (i : fin n) => E) F) :=
    fun (n : β) => continuous_multilinear_map.semimodule;
  pi.semimodule β (fun (n : β) => continuous_multilinear_map π (fun (i : fin n) => E) F) π

namespace formal_multilinear_series


/-- Forgetting the zeroth term in a formal multilinear series, and interpreting the following terms
as multilinear maps into `E βL[π] F`. If `p` corresponds to the Taylor series of a function, then
`p.shift` is the Taylor series of the derivative of the function. -/
def shift {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E]
    [normed_space π E] {F : Type u_3} [normed_group F] [normed_space π F]
    (p : formal_multilinear_series π E F) :
    formal_multilinear_series π E (continuous_linear_map π E F) :=
  fun (n : β) => continuous_multilinear_map.curry_right (p (Nat.succ n))

/-- Adding a zeroth term to a formal multilinear series taking values in `E βL[π] F`. This
corresponds to starting from a Taylor series for the derivative of a function, and building a Taylor
series for the function itself. -/
def unshift {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E]
    [normed_space π E] {F : Type u_3} [normed_group F] [normed_space π F]
    (q : formal_multilinear_series π E (continuous_linear_map π E F)) (z : F) :
    formal_multilinear_series π E F :=
  sorry

/-- Killing the zeroth coefficient in a formal multilinear series -/
def remove_zero {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E]
    [normed_space π E] {F : Type u_3} [normed_group F] [normed_space π F]
    (p : formal_multilinear_series π E F) : formal_multilinear_series π E F :=
  sorry

@[simp] theorem remove_zero_coeff_zero {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2}
    [normed_group E] [normed_space π E] {F : Type u_3} [normed_group F] [normed_space π F]
    (p : formal_multilinear_series π E F) : remove_zero p 0 = 0 :=
  rfl

@[simp] theorem remove_zero_coeff_succ {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2}
    [normed_group E] [normed_space π E] {F : Type u_3} [normed_group F] [normed_space π F]
    (p : formal_multilinear_series π E F) (n : β) : remove_zero p (n + 1) = p (n + 1) :=
  rfl

theorem remove_zero_of_pos {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2}
    [normed_group E] [normed_space π E] {F : Type u_3} [normed_group F] [normed_space π F]
    (p : formal_multilinear_series π E F) {n : β} (h : 0 < n) : remove_zero p n = p n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (remove_zero p n = p n)) (Eq.symm (nat.succ_pred_eq_of_pos h))))
    (Eq.refl (remove_zero p (Nat.succ (Nat.pred n))))

/-- Convenience congruence lemma stating in a dependent setting that, if the arguments to a formal
multilinear series are equal, then the values are also equal. -/
theorem congr {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E]
    [normed_space π E] {F : Type u_3} [normed_group F] [normed_space π F]
    (p : formal_multilinear_series π E F) {m : β} {n : β} {v : fin m β E} {w : fin n β E}
    (h1 : m = n)
    (h2 :
      β (i : β) (him : i < m) (hin : i < n),
        v { val := i, property := him } = w { val := i, property := hin }) :
    coe_fn (p m) v = coe_fn (p n) w :=
  sorry

/-- Composing each term `pβ` in a formal multilinear series with `(u, ..., u)` where `u` is a fixed
continuous linear map, gives a new formal multilinear series `p.comp_continuous_linear_map u`. -/
def comp_continuous_linear_map {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2}
    [normed_group E] [normed_space π E] {F : Type u_3} [normed_group F] [normed_space π F]
    {G : Type u_4} [normed_group G] [normed_space π G] (p : formal_multilinear_series π F G)
    (u : continuous_linear_map π E F) : formal_multilinear_series π E G :=
  fun (n : β) => continuous_multilinear_map.comp_continuous_linear_map (p n) fun (i : fin n) => u

@[simp] theorem comp_continuous_linear_map_apply {π : Type u_1} [nondiscrete_normed_field π]
    {E : Type u_2} [normed_group E] [normed_space π E] {F : Type u_3} [normed_group F]
    [normed_space π F] {G : Type u_4} [normed_group G] [normed_space π G]
    (p : formal_multilinear_series π F G) (u : continuous_linear_map π E F) (n : β)
    (v : fin n β E) : coe_fn (comp_continuous_linear_map p u n) v = coe_fn (p n) (βu β v) :=
  rfl

/-- Reinterpret a formal `π'`-multilinear series as a formal `π`-multilinear series, where `π'` is a
normed algebra over `π`. -/
@[simp] protected def restrict_scalars (π : Type u_1) [nondiscrete_normed_field π] {E : Type u_2}
    [normed_group E] [normed_space π E] {F : Type u_3} [normed_group F] [normed_space π F]
    {π' : Type u_5} [nondiscrete_normed_field π'] [normed_algebra π π'] [normed_space π' E]
    [is_scalar_tower π π' E] [normed_space π' F] [is_scalar_tower π π' F]
    (p : formal_multilinear_series π' E F) : formal_multilinear_series π E F :=
  fun (n : β) => continuous_multilinear_map.restrict_scalars π (p n)

end Mathlib