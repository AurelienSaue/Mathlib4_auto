/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.measure_theory.simple_func_dense
import Mathlib.analysis.normed_space.bounded_linear_maps
import Mathlib.topology.sequences
import Mathlib.PostPort

universes u_1 u_2 u_3 u_4 

namespace Mathlib

/-!
# Bochner integral

The Bochner integral extends the definition of the Lebesgue integral to functions that map from a
measure space into a Banach space (complete normed vector space). It is constructed here by
extending the integral on simple functions.

## Main definitions

The Bochner integral is defined following these steps:

1. Define the integral on simple functions of the type `simple_func α E` (notation : `α →ₛ E`)
  where `E` is a real normed space.

  (See `simple_func.bintegral` and section `bintegral` for details. Also see `simple_func.integral`
  for the integral on simple functions of the type `simple_func α ennreal`.)

2. Use `α →ₛ E` to cut out the simple functions from L1 functions, and define integral
  on these. The type of simple functions in L1 space is written as `α →₁ₛ[μ] E`.

3. Show that the embedding of `α →₁ₛ[μ] E` into L1 is a dense and uniform one.

4. Show that the integral defined on `α →₁ₛ[μ] E` is a continuous linear map.

5. Define the Bochner integral on L1 functions by extending the integral on integrable simple
  functions `α →₁ₛ[μ] E` using `continuous_linear_map.extend`. Define the Bochner integral on
  functions as the Bochner integral of its equivalence class in L1 space.

## Main statements

1. Basic properties of the Bochner integral on functions of type `α → E`, where `α` is a measure
   space and `E` is a real normed space.

  * `integral_zero`                  : `∫ 0 ∂μ = 0`
  * `integral_add`                   : `∫ x, f x + g x ∂μ = ∫ x, f ∂μ + ∫ x, g x ∂μ`
  * `integral_neg`                   : `∫ x, - f x ∂μ = - ∫ x, f x ∂μ`
  * `integral_sub`                   : `∫ x, f x - g x ∂μ = ∫ x, f x ∂μ - ∫ x, g x ∂μ`
  * `integral_smul`                  : `∫ x, r • f x ∂μ = r • ∫ x, f x ∂μ`
  * `integral_congr_ae`              : `f =ᵐ[μ] g → ∫ x, f x ∂μ = ∫ x, g x ∂μ`
  * `norm_integral_le_integral_norm` : `∥∫ x, f x ∂μ∥ ≤ ∫ x, ∥f x∥ ∂μ`

2. Basic properties of the Bochner integral on functions of type `α → ℝ`, where `α` is a measure
  space.

  * `integral_nonneg_of_ae` : `0 ≤ᵐ[μ] f → 0 ≤ ∫ x, f x ∂μ`
  * `integral_nonpos_of_ae` : `f ≤ᵐ[μ] 0 → ∫ x, f x ∂μ ≤ 0`
  * `integral_mono_ae`      : `f ≤ᵐ[μ] g → ∫ x, f x ∂μ ≤ ∫ x, g x ∂μ`
  * `integral_nonneg`       : `0 ≤ f → 0 ≤ ∫ x, f x ∂μ`
  * `integral_nonpos`       : `f ≤ 0 → ∫ x, f x ∂μ ≤ 0`
  * `integral_mono`         : `f ≤ᵐ[μ] g → ∫ x, f x ∂μ ≤ ∫ x, g x ∂μ`

3. Propositions connecting the Bochner integral with the integral on `ennreal`-valued functions,
   which is called `lintegral` and has the notation `∫⁻`.

  * `integral_eq_lintegral_max_sub_lintegral_min` : `∫ x, f x ∂μ = ∫⁻ x, f⁺ x ∂μ - ∫⁻ x, f⁻ x ∂μ`,
    where `f⁺` is the positive part of `f` and `f⁻` is the negative part of `f`.
  * `integral_eq_lintegral_of_nonneg_ae`          : `0 ≤ᵐ[μ] f → ∫ x, f x ∂μ = ∫⁻ x, f x ∂μ`

4. `tendsto_integral_of_dominated_convergence` : the Lebesgue dominated convergence theorem

## Notes

Some tips on how to prove a proposition if the API for the Bochner integral is not enough so that
you need to unfold the definition of the Bochner integral and go back to simple functions.

One method is to use the theorem `integrable.induction` in the file `set_integral`, which allows
you to prove something for an arbitrary measurable + integrable function.

Another method is using the following steps.
See `integral_eq_lintegral_max_sub_lintegral_min` for a complicated example, which proves that
`∫ f = ∫⁻ f⁺ - ∫⁻ f⁻`, with the first integral sign being the Bochner integral of a real-valued
function `f : α → ℝ`, and second and third integral sign being the integral on ennreal-valued
functions (called `lintegral`). The proof of `integral_eq_lintegral_max_sub_lintegral_min` is
scattered in sections with the name `pos_part`.

Here are the usual steps of proving that a property `p`, say `∫ f = ∫⁻ f⁺ - ∫⁻ f⁻`, holds for all
functions :

1. First go to the `L¹` space.

   For example, if you see `ennreal.to_real (∫⁻ a, ennreal.of_real $ ∥f a∥)`, that is the norm of
   `f` in `L¹` space. Rewrite using `l1.norm_of_fun_eq_lintegral_norm`.

2. Show that the set `{f ∈ L¹ | ∫ f = ∫⁻ f⁺ - ∫⁻ f⁻}` is closed in `L¹` using `is_closed_eq`.

3. Show that the property holds for all simple functions `s` in `L¹` space.

   Typically, you need to convert various notions to their `simple_func` counterpart, using lemmas
   like `l1.integral_coe_eq_integral`.

4. Since simple functions are dense in `L¹`,
```
univ = closure {s simple}
     = closure {s simple | ∫ s = ∫⁻ s⁺ - ∫⁻ s⁻} : the property holds for all simple functions
     ⊆ closure {f | ∫ f = ∫⁻ f⁺ - ∫⁻ f⁻}
     = {f | ∫ f = ∫⁻ f⁺ - ∫⁻ f⁻} : closure of a closed set is itself
```
Use `is_closed_property` or `dense_range.induction_on` for this argument.

## Notations

* `α →ₛ E`  : simple functions (defined in `measure_theory/integration`)
* `α →₁[μ] E` : functions in L1 space, i.e., equivalence classes of integrable functions (defined in
                `measure_theory/l1_space`)
* `α →₁ₛ[μ] E` : simple functions in L1 space, i.e., equivalence classes of integrable simple
                 functions

Note : `ₛ` is typed using `\_s`. Sometimes it shows as a box if font is missing.

## Tags

Bochner integral, simple function, function space, Lebesgue dominated convergence theorem

-/

namespace measure_theory


namespace simple_func


/-- Positive part of a simple function. -/
def pos_part {α : Type u_1} {E : Type u_2} [measurable_space α] [linear_order E] [HasZero E]
    (f : simple_func α E) : simple_func α E :=
  map (fun (b : E) => max b 0) f

/-- Negative part of a simple function. -/
def neg_part {α : Type u_1} {E : Type u_2} [measurable_space α] [linear_order E] [HasZero E] [Neg E]
    (f : simple_func α E) : simple_func α E :=
  pos_part (-f)

theorem pos_part_map_norm {α : Type u_1} [measurable_space α] (f : simple_func α ℝ) :
    map norm (pos_part f) = pos_part f :=
  sorry

theorem neg_part_map_norm {α : Type u_1} [measurable_space α] (f : simple_func α ℝ) :
    map norm (neg_part f) = neg_part f :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (map norm (neg_part f) = neg_part f)) (neg_part.equations._eqn_1 f)))
    (pos_part_map_norm (-f))

theorem pos_part_sub_neg_part {α : Type u_1} [measurable_space α] (f : simple_func α ℝ) :
    pos_part f - neg_part f = f :=
  sorry

end simple_func


end measure_theory


namespace measure_theory


namespace simple_func


/-!
### The Bochner integral of simple functions

Define the Bochner integral of simple functions of the type `α →ₛ β` where `β` is a normed group,
and prove basic property of this integral.
-/

/-- For simple functions with a `normed_group` as codomain, being integrable is the same as having
    finite volume support. -/
theorem integrable_iff_fin_meas_supp {α : Type u_1} {E : Type u_2} [measurable_space α]
    [normed_group E] [measurable_space E] {f : simple_func α E} {μ : measure α} :
    integrable ⇑f ↔ simple_func.fin_meas_supp f μ :=
  sorry

theorem fin_meas_supp.integrable {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [measurable_space E] {μ : measure α} {f : simple_func α E} (h : simple_func.fin_meas_supp f μ) :
    integrable ⇑f :=
  iff.mpr integrable_iff_fin_meas_supp h

theorem integrable_pair {α : Type u_1} {E : Type u_2} {F : Type u_3} [measurable_space α]
    [normed_group E] [measurable_space E] [normed_group F] {μ : measure α} [measurable_space F]
    {f : simple_func α E} {g : simple_func α F} :
    integrable ⇑f → integrable ⇑g → integrable ⇑(pair f g) :=
  sorry

/-- Bochner integral of simple functions whose codomain is a real `normed_space`. -/
def integral {α : Type u_1} {F : Type u_3} [measurable_space α] [normed_group F] [normed_space ℝ F]
    (μ : measure α) (f : simple_func α F) : F :=
  finset.sum (simple_func.range f)
    fun (x : F) => ennreal.to_real (coe_fn μ (⇑f ⁻¹' singleton x)) • x

theorem integral_eq_sum_filter {α : Type u_1} {F : Type u_3} [measurable_space α] [normed_group F]
    [normed_space ℝ F] (f : simple_func α F) (μ : measure α) :
    integral μ f =
        finset.sum (finset.filter (fun (x : F) => x ≠ 0) (simple_func.range f))
          fun (x : F) => ennreal.to_real (coe_fn μ (⇑f ⁻¹' singleton x)) • x :=
  sorry

/-- The Bochner integral is equal to a sum over any set that includes `f.range` (except `0`). -/
theorem integral_eq_sum_of_subset {α : Type u_1} {F : Type u_3} [measurable_space α]
    [normed_group F] [normed_space ℝ F] {f : simple_func α F} {μ : measure α} {s : finset F}
    (hs : finset.filter (fun (x : F) => x ≠ 0) (simple_func.range f) ⊆ s) :
    integral μ f =
        finset.sum s fun (x : F) => ennreal.to_real (coe_fn μ (⇑f ⁻¹' singleton x)) • x :=
  sorry

/-- Calculate the integral of `g ∘ f : α →ₛ F`, where `f` is an integrable function from `α` to `E`
    and `g` is a function from `E` to `F`. We require `g 0 = 0` so that `g ∘ f` is integrable. -/
theorem map_integral {α : Type u_1} {E : Type u_2} {F : Type u_3} [measurable_space α]
    [normed_group E] [measurable_space E] [normed_group F] {μ : measure α} [normed_space ℝ F]
    (f : simple_func α E) (g : E → F) (hf : integrable ⇑f) (hg : g 0 = 0) :
    integral μ (map g f) =
        finset.sum (simple_func.range f)
          fun (x : E) => ennreal.to_real (coe_fn μ (⇑f ⁻¹' singleton x)) • g x :=
  sorry

/-- `simple_func.integral` and `simple_func.lintegral` agree when the integrand has type
    `α →ₛ ennreal`. But since `ennreal` is not a `normed_space`, we need some form of coercion.
    See `integral_eq_lintegral` for a simpler version. -/
theorem integral_eq_lintegral' {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [measurable_space E] {μ : measure α} {f : simple_func α E} {g : E → ennreal}
    (hf : integrable ⇑f) (hg0 : g 0 = 0) (hgt : ∀ (b : E), g b < ⊤) :
    integral μ (map (ennreal.to_real ∘ g) f) =
        ennreal.to_real (lintegral μ fun (a : α) => g (coe_fn f a)) :=
  sorry

theorem integral_congr {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [measurable_space E] {μ : measure α} [normed_space ℝ E] {f : simple_func α E}
    {g : simple_func α E} (hf : integrable ⇑f) (h : filter.eventually_eq (measure.ae μ) ⇑f ⇑g) :
    integral μ f = integral μ g :=
  sorry

/-- `simple_func.bintegral` and `simple_func.integral` agree when the integrand has type
    `α →ₛ ennreal`. But since `ennreal` is not a `normed_space`, we need some form of coercion. -/
theorem integral_eq_lintegral {α : Type u_1} [measurable_space α] {μ : measure α}
    {f : simple_func α ℝ} (hf : integrable ⇑f) (h_pos : filter.eventually_le (measure.ae μ) 0 ⇑f) :
    integral μ f = ennreal.to_real (lintegral μ fun (a : α) => ennreal.of_real (coe_fn f a)) :=
  sorry

theorem integral_add {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [measurable_space E] {μ : measure α} [normed_space ℝ E] {f : simple_func α E}
    {g : simple_func α E} (hf : integrable ⇑f) (hg : integrable ⇑g) :
    integral μ (f + g) = integral μ f + integral μ g :=
  sorry

theorem integral_neg {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [measurable_space E] {μ : measure α} [normed_space ℝ E] {f : simple_func α E}
    (hf : integrable ⇑f) : integral μ (-f) = -integral μ f :=
  sorry

theorem integral_sub {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [measurable_space E] {μ : measure α} [normed_space ℝ E] [borel_space E] {f : simple_func α E}
    {g : simple_func α E} (hf : integrable ⇑f) (hg : integrable ⇑g) :
    integral μ (f - g) = integral μ f - integral μ g :=
  sorry

theorem integral_smul {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [measurable_space E] {μ : measure α} [normed_space ℝ E] (r : ℝ) {f : simple_func α E}
    (hf : integrable ⇑f) : integral μ (r • f) = r • integral μ f :=
  sorry

theorem norm_integral_le_integral_norm {α : Type u_1} {E : Type u_2} [measurable_space α]
    [normed_group E] [measurable_space E] {μ : measure α} [normed_space ℝ E] (f : simple_func α E)
    (hf : integrable ⇑f) : norm (integral μ f) ≤ integral μ (map norm f) :=
  sorry

theorem integral_add_measure {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [measurable_space E] {μ : measure α} [normed_space ℝ E]
    {ν :
      autoParam (measure α)
        (Lean.Syntax.ident Lean.SourceInfo.none
          (String.toSubstring "Mathlib.measure_theory.volume_tac")
          (Lean.Name.mkStr
            (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "measure_theory")
            "volume_tac")
          [])}
    (f : simple_func α E) (hf : integrable ⇑f) : integral (μ + ν) f = integral μ f + integral ν f :=
  sorry

end simple_func


namespace l1


-- We use `Type*` instead of `add_subgroup` because otherwise we loose dot notation.

/-- `l1.simple_func` is a subspace of L1 consisting of equivalence classes of an integrable simple
    function. -/
def simple_func (α : Type u_1) (E : Type u_2) [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    (μ : measure α) :=
  ↥(add_subgroup.mk
      (set_of
        fun (f : l1 α E μ) =>
          ∃ (s : simple_func α E), ae_eq_fun.mk (⇑s) (simple_func.ae_measurable s) = ↑f)
      sorry sorry sorry)

namespace simple_func


/-! Simple functions in L1 space form a `normed_space`. -/

protected instance measure_theory.l1.has_coe {α : Type u_1} {E : Type u_2} [measurable_space α]
    [normed_group E] [topological_space.second_countable_topology E] [measurable_space E]
    [borel_space E] {μ : measure α} : has_coe (simple_func α E μ) (l1 α E μ) :=
  Mathlib.coe_subtype

protected instance has_coe_to_fun {α : Type u_1} {E : Type u_2} [measurable_space α]
    [normed_group E] [topological_space.second_countable_topology E] [measurable_space E]
    [borel_space E] {μ : measure α} : has_coe_to_fun (simple_func α E μ) :=
  has_coe_to_fun.mk (fun (f : simple_func α E μ) => α → E) fun (f : simple_func α E μ) => ⇑↑f

@[simp] theorem coe_coe {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} (f : simple_func α E μ) : ⇑↑f = ⇑f :=
  rfl

protected theorem eq {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} {f : simple_func α E μ} {g : simple_func α E μ} : ↑f = ↑g → f = g :=
  subtype.eq

protected theorem eq' {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} {f : simple_func α E μ} {g : simple_func α E μ} : ↑f = ↑g → f = g :=
  subtype.eq ∘ subtype.eq

protected theorem eq_iff {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} {f : simple_func α E μ} {g : simple_func α E μ} : ↑f = ↑g ↔ f = g :=
  iff.symm subtype.ext_iff

protected theorem eq_iff' {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} {f : simple_func α E μ} {g : simple_func α E μ} : ↑f = ↑g ↔ f = g :=
  { mp := simple_func.eq', mpr := congr_arg fun {f : simple_func α E μ} => ↑f }

/-- L1 simple functions forms a `emetric_space`, with the emetric being inherited from L1 space,
  i.e., `edist f g = ∫⁻ a, edist (f a) (g a)`.
  Not declared as an instance as `α →₁ₛ[μ] β` will only be useful in the construction of the Bochner
  integral. -/
protected def emetric_space {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} : emetric_space (simple_func α E μ) :=
  subtype.emetric_space

/-- L1 simple functions forms a `metric_space`, with the metric being inherited from L1 space,
  i.e., `dist f g = ennreal.to_real (∫⁻ a, edist (f a) (g a)`).
  Not declared as an instance as `α →₁ₛ[μ] β` will only be useful in the construction of the Bochner
  integral. -/
protected def metric_space {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} : metric_space (simple_func α E μ) :=
  subtype.metric_space

/-- Functions `α →₁ₛ[μ] E` form an additive commutative group. -/
protected def add_comm_group {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} : add_comm_group (simple_func α E μ) :=
  add_subgroup.to_add_comm_group
    (add_subgroup.mk
      (set_of
        fun (f : l1 α E μ) =>
          ∃ (s : simple_func α E), ae_eq_fun.mk (⇑s) (simple_func.ae_measurable s) = ↑f)
      (_proof_3 α E μ) (_proof_4 α E μ) (_proof_5 α E μ))

protected instance inhabited {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} : Inhabited (simple_func α E μ) :=
  { default := 0 }

@[simp] theorem coe_zero {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} : ↑0 = 0 :=
  rfl

@[simp] theorem coe_add {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} (f : simple_func α E μ) (g : simple_func α E μ) : ↑(f + g) = ↑f + ↑g :=
  rfl

@[simp] theorem coe_neg {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} (f : simple_func α E μ) : ↑(-f) = -↑f :=
  rfl

@[simp] theorem coe_sub {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} (f : simple_func α E μ) (g : simple_func α E μ) : ↑(f - g) = ↑f - ↑g :=
  rfl

@[simp] theorem edist_eq {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} (f : simple_func α E μ) (g : simple_func α E μ) : edist f g = edist ↑f ↑g :=
  rfl

@[simp] theorem dist_eq {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} (f : simple_func α E μ) (g : simple_func α E μ) : dist f g = dist ↑f ↑g :=
  rfl

/-- The norm on `α →₁ₛ[μ] E` is inherited from L1 space. That is, `∥f∥ = ∫⁻ a, edist (f a) 0`.
  Not declared as an instance as `α →₁ₛ[μ] E` will only be useful in the construction of the Bochner
  integral. -/
protected def has_norm {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} : has_norm (simple_func α E μ) :=
  has_norm.mk fun (f : simple_func α E μ) => norm ↑f

theorem norm_eq {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} (f : simple_func α E μ) : norm f = norm ↑f :=
  rfl

theorem norm_eq' {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} (f : simple_func α E μ) : norm f = ennreal.to_real (edist (↑f) 0) :=
  rfl

/-- Not declared as an instance as `α →₁ₛ[μ] E` will only be useful in the construction of the
Bochner integral. -/
protected def normed_group {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} : normed_group (simple_func α E μ) :=
  normed_group.of_add_dist sorry sorry

/-- Not declared as an instance as `α →₁ₛ[μ] E` will only be useful in the construction of the
Bochner integral. -/
protected def has_scalar {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} {𝕜 : Type u_4} [normed_field 𝕜] [normed_space 𝕜 E] :
    has_scalar 𝕜 (simple_func α E μ) :=
  has_scalar.mk fun (k : 𝕜) (f : simple_func α E μ) => { val := k • ↑f, property := sorry }

@[simp] theorem coe_smul {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} {𝕜 : Type u_4} [normed_field 𝕜] [normed_space 𝕜 E] (c : 𝕜)
    (f : simple_func α E μ) : ↑(c • f) = c • ↑f :=
  rfl

/-- Not declared as an instance as `α →₁ₛ[μ] E` will only be useful in the construction of the
  Bochner integral. -/
protected def semimodule {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} {𝕜 : Type u_4} [normed_field 𝕜] [normed_space 𝕜 E] :
    semimodule 𝕜 (simple_func α E μ) :=
  semimodule.mk sorry sorry

/-- Not declared as an instance as `α →₁ₛ[μ] E` will only be useful in the construction of the
Bochner integral. -/
protected def normed_space {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} {𝕜 : Type u_4} [normed_field 𝕜] [normed_space 𝕜 E] :
    normed_space 𝕜 (simple_func α E μ) :=
  normed_space.mk sorry

/-- Construct the equivalence class `[f]` of an integrable simple function `f`. -/
def of_simple_func {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} (f : simple_func α E) (hf : integrable ⇑f) : simple_func α E μ :=
  { val := of_fun (⇑f) hf, property := sorry }

theorem of_simple_func_eq_of_fun {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} (f : simple_func α E) (hf : integrable ⇑f) :
    ↑(of_simple_func f hf) = of_fun (⇑f) hf :=
  rfl

theorem of_simple_func_eq_mk {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} (f : simple_func α E) (hf : integrable ⇑f) :
    ↑(of_simple_func f hf) = ae_eq_fun.mk (⇑f) (simple_func.ae_measurable f) :=
  rfl

theorem of_simple_func_zero {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} : of_simple_func 0 (integrable_zero α E μ) = 0 :=
  rfl

theorem of_simple_func_add {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} (f : simple_func α E) (g : simple_func α E) (hf : integrable ⇑f)
    (hg : integrable ⇑g) :
    of_simple_func (f + g) (integrable.add hf hg) = of_simple_func f hf + of_simple_func g hg :=
  rfl

theorem of_simple_func_neg {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} (f : simple_func α E) (hf : integrable ⇑f) :
    of_simple_func (-f) (integrable.neg hf) = -of_simple_func f hf :=
  rfl

theorem of_simple_func_sub {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} (f : simple_func α E) (g : simple_func α E) (hf : integrable ⇑f)
    (hg : integrable ⇑g) :
    of_simple_func (f - g) (integrable.sub hf hg) = of_simple_func f hf - of_simple_func g hg :=
  sorry

theorem of_simple_func_smul {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} {𝕜 : Type u_4} [normed_field 𝕜] [normed_space 𝕜 E] (f : simple_func α E)
    (hf : integrable ⇑f) (c : 𝕜) :
    of_simple_func (c • f) (integrable.smul c hf) = c • of_simple_func f hf :=
  rfl

theorem norm_of_simple_func {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} (f : simple_func α E) (hf : integrable ⇑f) :
    norm (of_simple_func f hf) =
        ennreal.to_real (lintegral μ fun (a : α) => edist (coe_fn f a) 0) :=
  rfl

/-- Find a representative of a `l1.simple_func`. -/
def to_simple_func {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} (f : simple_func α E μ) : simple_func α E :=
  classical.some sorry

/-- `f.to_simple_func` is measurable. -/
protected theorem measurable {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} (f : simple_func α E μ) : measurable ⇑(to_simple_func f) :=
  simple_func.measurable (to_simple_func f)

protected theorem ae_measurable {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} (f : simple_func α E μ) : ae_measurable ⇑(to_simple_func f) :=
  measurable.ae_measurable (simple_func.measurable f)

/-- `f.to_simple_func` is integrable. -/
protected theorem integrable {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} (f : simple_func α E μ) : integrable ⇑(to_simple_func f) :=
  sorry

theorem of_simple_func_to_simple_func {α : Type u_1} {E : Type u_2} [measurable_space α]
    [normed_group E] [topological_space.second_countable_topology E] [measurable_space E]
    [borel_space E] {μ : measure α} (f : simple_func α E μ) :
    of_simple_func (to_simple_func f) (simple_func.integrable f) = f :=
  sorry

theorem to_simple_func_of_simple_func {α : Type u_1} {E : Type u_2} [measurable_space α]
    [normed_group E] [topological_space.second_countable_topology E] [measurable_space E]
    [borel_space E] {μ : measure α} (f : simple_func α E) (hfi : integrable ⇑f) :
    filter.eventually_eq (measure.ae μ) ⇑(to_simple_func (of_simple_func f hfi)) ⇑f :=
  sorry

theorem to_simple_func_eq_to_fun {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} (f : simple_func α E μ) :
    filter.eventually_eq (measure.ae μ) ⇑(to_simple_func f) ⇑f :=
  sorry

theorem zero_to_simple_func (α : Type u_1) (E : Type u_2) [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} : filter.eventually_eq (measure.ae μ) (⇑(to_simple_func 0)) 0 :=
  sorry

theorem add_to_simple_func {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} (f : simple_func α E μ) (g : simple_func α E μ) :
    filter.eventually_eq (measure.ae μ) (⇑(to_simple_func (f + g)))
        (⇑(to_simple_func f) + ⇑(to_simple_func g)) :=
  sorry

theorem neg_to_simple_func {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} (f : simple_func α E μ) :
    filter.eventually_eq (measure.ae μ) (⇑(to_simple_func (-f))) (-⇑(to_simple_func f)) :=
  sorry

theorem sub_to_simple_func {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} (f : simple_func α E μ) (g : simple_func α E μ) :
    filter.eventually_eq (measure.ae μ) (⇑(to_simple_func (f - g)))
        (⇑(to_simple_func f) - ⇑(to_simple_func g)) :=
  sorry

theorem smul_to_simple_func {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} {𝕜 : Type u_4} [normed_field 𝕜] [normed_space 𝕜 E] (k : 𝕜)
    (f : simple_func α E μ) :
    filter.eventually_eq (measure.ae μ) (⇑(to_simple_func (k • f))) (k • ⇑(to_simple_func f)) :=
  sorry

theorem lintegral_edist_to_simple_func_lt_top {α : Type u_1} {E : Type u_2} [measurable_space α]
    [normed_group E] [topological_space.second_countable_topology E] [measurable_space E]
    [borel_space E] {μ : measure α} (f : simple_func α E μ) (g : simple_func α E μ) :
    (lintegral μ fun (x : α) => edist (coe_fn (to_simple_func f) x) (coe_fn (to_simple_func g) x)) <
        ⊤ :=
  sorry

theorem dist_to_simple_func {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} (f : simple_func α E μ) (g : simple_func α E μ) :
    dist f g =
        ennreal.to_real
          (lintegral μ
            fun (x : α) => edist (coe_fn (to_simple_func f) x) (coe_fn (to_simple_func g) x)) :=
  sorry

theorem norm_to_simple_func {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} (f : simple_func α E μ) :
    norm f = ennreal.to_real (lintegral μ fun (a : α) => ↑(nnnorm (coe_fn (to_simple_func f) a))) :=
  sorry

-- calc ∥f∥ = ennreal.to_real (∫⁻ (x : α), (coe ∘ nnnorm) (f.to_simple_func x) ∂μ) :

theorem norm_eq_integral {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} (f : simple_func α E μ) :
    norm f = simple_func.integral μ (simple_func.map norm (to_simple_func f)) :=
  sorry

--   by { rw norm_to_simple_func }

-- ... = (f.to_simple_func.map norm).integral μ :

protected theorem uniform_continuous {α : Type u_1} {E : Type u_2} [measurable_space α]
    [normed_group E] [topological_space.second_countable_topology E] [measurable_space E]
    [borel_space E] {μ : measure α} : uniform_continuous coe :=
  uniform_continuous_comap

protected theorem uniform_embedding {α : Type u_1} {E : Type u_2} [measurable_space α]
    [normed_group E] [topological_space.second_countable_topology E] [measurable_space E]
    [borel_space E] {μ : measure α} : uniform_embedding coe :=
  uniform_embedding_comap subtype.val_injective

protected theorem uniform_inducing {α : Type u_1} {E : Type u_2} [measurable_space α]
    [normed_group E] [topological_space.second_countable_topology E] [measurable_space E]
    [borel_space E] {μ : measure α} : uniform_inducing coe :=
  uniform_embedding.to_uniform_inducing simple_func.uniform_embedding

protected theorem dense_embedding {α : Type u_1} {E : Type u_2} [measurable_space α]
    [normed_group E] [topological_space.second_countable_topology E] [measurable_space E]
    [borel_space E] {μ : measure α} : dense_embedding coe :=
  sorry

protected theorem dense_inducing {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} : dense_inducing coe :=
  dense_embedding.to_dense_inducing simple_func.dense_embedding

protected theorem dense_range {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} : dense_range coe :=
  dense_inducing.dense simple_func.dense_inducing

/-- The uniform and dense embedding of L1 simple functions into L1 functions. -/
def coe_to_l1 (α : Type u_1) (E : Type u_2) [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} (𝕜 : Type u_4) [normed_field 𝕜] [normed_space 𝕜 E] :
    continuous_linear_map 𝕜 (simple_func α E μ) (l1 α E μ) :=
  continuous_linear_map.mk (linear_map.mk coe sorry sorry)

/-- Positive part of a simple function in L1 space.  -/
def pos_part {α : Type u_1} [measurable_space α] {μ : measure α} (f : simple_func α ℝ μ) :
    simple_func α ℝ μ :=
  { val := pos_part ↑f, property := sorry }

/-- Negative part of a simple function in L1 space. -/
def neg_part {α : Type u_1} [measurable_space α] {μ : measure α} (f : simple_func α ℝ μ) :
    simple_func α ℝ μ :=
  pos_part (-f)

theorem coe_pos_part {α : Type u_1} [measurable_space α] {μ : measure α} (f : simple_func α ℝ μ) :
    ↑(pos_part f) = pos_part ↑f :=
  rfl

theorem coe_neg_part {α : Type u_1} [measurable_space α] {μ : measure α} (f : simple_func α ℝ μ) :
    ↑(neg_part f) = neg_part ↑f :=
  rfl

/-! Define the Bochner integral on `α →₁ₛ[μ] E` and prove basic properties of this integral. -/

/-- The Bochner integral over simple functions in l1 space. -/
def integral {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} [normed_space ℝ E] (f : simple_func α E μ) : E :=
  simple_func.integral μ (to_simple_func f)

theorem integral_eq_integral {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} [normed_space ℝ E] (f : simple_func α E μ) :
    integral f = simple_func.integral μ (to_simple_func f) :=
  rfl

theorem integral_eq_lintegral {α : Type u_1} [measurable_space α] {μ : measure α}
    {f : simple_func α ℝ μ} (h_pos : filter.eventually_le (measure.ae μ) 0 ⇑(to_simple_func f)) :
    integral f =
        ennreal.to_real
          (lintegral μ fun (a : α) => ennreal.of_real (coe_fn (to_simple_func f) a)) :=
  sorry

theorem integral_congr {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} [normed_space ℝ E] {f : simple_func α E μ} {g : simple_func α E μ}
    (h : filter.eventually_eq (measure.ae μ) ⇑(to_simple_func f) ⇑(to_simple_func g)) :
    integral f = integral g :=
  simple_func.integral_congr (simple_func.integrable f) h

theorem integral_add {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} [normed_space ℝ E] (f : simple_func α E μ) (g : simple_func α E μ) :
    integral (f + g) = integral f + integral g :=
  sorry

theorem integral_smul {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} [normed_space ℝ E] (r : ℝ) (f : simple_func α E μ) :
    integral (r • f) = r • integral f :=
  sorry

theorem norm_integral_le_norm {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} [normed_space ℝ E] (f : simple_func α E μ) : norm (integral f) ≤ norm f :=
  eq.mpr (id (Eq._oldrec (Eq.refl (norm (integral f) ≤ norm f)) (integral.equations._eqn_1 f)))
    (eq.mpr
      (id
        (Eq._oldrec (Eq.refl (norm (simple_func.integral μ (to_simple_func f)) ≤ norm f))
          (norm_eq_integral f)))
      (simple_func.norm_integral_le_integral_norm (to_simple_func f) (simple_func.integrable f)))

/-- The Bochner integral over simple functions in l1 space as a continuous linear map. -/
def integral_clm {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} [normed_space ℝ E] : continuous_linear_map ℝ (simple_func α E μ) E :=
  linear_map.mk_continuous (linear_map.mk integral integral_add integral_smul) 1 sorry

theorem norm_Integral_le_one {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} [normed_space ℝ E] : norm integral_clm ≤ 1 :=
  linear_map.mk_continuous_norm_le (linear_map.mk integral integral_add integral_smul) zero_le_one
    integral_clm._proof_1

theorem pos_part_to_simple_func {α : Type u_1} [measurable_space α] {μ : measure α}
    (f : simple_func α ℝ μ) :
    filter.eventually_eq (measure.ae μ) ⇑(to_simple_func (pos_part f))
        ⇑(simple_func.pos_part (to_simple_func f)) :=
  sorry

theorem neg_part_to_simple_func {α : Type u_1} [measurable_space α] {μ : measure α}
    (f : simple_func α ℝ μ) :
    filter.eventually_eq (measure.ae μ) ⇑(to_simple_func (neg_part f))
        ⇑(simple_func.neg_part (to_simple_func f)) :=
  sorry

theorem integral_eq_norm_pos_part_sub {α : Type u_1} [measurable_space α] {μ : measure α}
    (f : simple_func α ℝ μ) : integral f = norm (pos_part f) - norm (neg_part f) :=
  sorry

end simple_func


/-- The Bochner integral in l1 space as a continuous linear map. -/
def integral_clm {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} [normed_space ℝ E] [complete_space E] : continuous_linear_map ℝ (l1 α E μ) E :=
  continuous_linear_map.extend simple_func.integral_clm (simple_func.coe_to_l1 α E ℝ)
    simple_func.dense_range simple_func.uniform_inducing

/-- The Bochner integral in l1 space -/
def integral {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} [normed_space ℝ E] [complete_space E] (f : l1 α E μ) : E :=
  coe_fn integral_clm f

theorem integral_eq {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} [normed_space ℝ E] [complete_space E] (f : l1 α E μ) :
    integral f = coe_fn integral_clm f :=
  rfl

theorem simple_func.integral_l1_eq_integral {α : Type u_1} {E : Type u_2} [measurable_space α]
    [normed_group E] [topological_space.second_countable_topology E] [measurable_space E]
    [borel_space E] {μ : measure α} [normed_space ℝ E] [complete_space E] (f : simple_func α E μ) :
    integral ↑f = simple_func.integral f :=
  uniformly_extend_of_ind simple_func.uniform_inducing simple_func.dense_range
    (continuous_linear_map.uniform_continuous simple_func.integral_clm) f

@[simp] theorem integral_zero (α : Type u_1) (E : Type u_2) [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} [normed_space ℝ E] [complete_space E] : integral 0 = 0 :=
  continuous_linear_map.map_zero integral_clm

theorem integral_add {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} [normed_space ℝ E] [complete_space E] (f : l1 α E μ) (g : l1 α E μ) :
    integral (f + g) = integral f + integral g :=
  continuous_linear_map.map_add integral_clm f g

theorem integral_neg {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} [normed_space ℝ E] [complete_space E] (f : l1 α E μ) :
    integral (-f) = -integral f :=
  continuous_linear_map.map_neg integral_clm f

theorem integral_sub {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} [normed_space ℝ E] [complete_space E] (f : l1 α E μ) (g : l1 α E μ) :
    integral (f - g) = integral f - integral g :=
  continuous_linear_map.map_sub integral_clm f g

theorem integral_smul {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} [normed_space ℝ E] [complete_space E] (r : ℝ) (f : l1 α E μ) :
    integral (r • f) = r • integral f :=
  continuous_linear_map.map_smul r integral_clm f

theorem norm_Integral_le_one {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} [normed_space ℝ E] [complete_space E] : norm integral_clm ≤ 1 :=
  sorry

theorem norm_integral_le {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} [normed_space ℝ E] [complete_space E] (f : l1 α E μ) :
    norm (integral f) ≤ norm f :=
  sorry

theorem continuous_integral {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
    {μ : measure α} [normed_space ℝ E] [complete_space E] :
    continuous fun (f : l1 α E μ) => integral f :=
  sorry

theorem integral_eq_norm_pos_part_sub {α : Type u_1} [measurable_space α] {μ : measure α}
    (f : l1 α ℝ μ) : integral f = norm (pos_part f) - norm (neg_part f) :=
  sorry

end l1


/-- The Bochner integral -/
def integral {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [normed_space ℝ E] [complete_space E]
    [measurable_space E] [borel_space E] (μ : measure α) (f : α → E) : E :=
  dite (integrable f) (fun (hf : integrable f) => l1.integral (l1.of_fun f hf))
    fun (hf : ¬integrable f) => 0

/-! In the notation for integrals, an expression like `∫ x, g ∥x∥ ∂μ` will not be parsed correctly,
  and needs parentheses. We do not set the binding power of `r` to `0`, because then
  `∫ x, f x = 0` will be parsed incorrectly. -/

theorem integral_eq {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [normed_space ℝ E] [complete_space E]
    [measurable_space E] [borel_space E] {μ : measure α} (f : α → E) (hf : integrable f) :
    (integral μ fun (a : α) => f a) = l1.integral (l1.of_fun f hf) :=
  dif_pos hf

theorem l1.integral_eq_integral {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [normed_space ℝ E] [complete_space E]
    [measurable_space E] [borel_space E] {μ : measure α} (f : l1 α E μ) :
    l1.integral f = integral μ fun (a : α) => coe_fn f a :=
  sorry

theorem integral_undef {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [normed_space ℝ E] [complete_space E]
    [measurable_space E] [borel_space E] {f : α → E} {μ : measure α} (h : ¬integrable f) :
    (integral μ fun (a : α) => f a) = 0 :=
  dif_neg h

theorem integral_non_ae_measurable {α : Type u_1} {E : Type u_2} [measurable_space α]
    [normed_group E] [topological_space.second_countable_topology E] [normed_space ℝ E]
    [complete_space E] [measurable_space E] [borel_space E] {f : α → E} {μ : measure α}
    (h : ¬ae_measurable f) : (integral μ fun (a : α) => f a) = 0 :=
  integral_undef (not_and_of_not_left (has_finite_integral fun (a : α) => f a) h)

theorem integral_zero (α : Type u_1) (E : Type u_2) [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [normed_space ℝ E] [complete_space E]
    [measurable_space E] [borel_space E] {μ : measure α} : (integral μ fun (a : α) => 0) = 0 :=
  sorry

@[simp] theorem integral_zero' (α : Type u_1) (E : Type u_2) [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [normed_space ℝ E] [complete_space E]
    [measurable_space E] [borel_space E] {μ : measure α} : integral μ 0 = 0 :=
  integral_zero α E

theorem integral_add {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [normed_space ℝ E] [complete_space E]
    [measurable_space E] [borel_space E] {f : α → E} {g : α → E} {μ : measure α} (hf : integrable f)
    (hg : integrable g) :
    (integral μ fun (a : α) => f a + g a) =
        (integral μ fun (a : α) => f a) + integral μ fun (a : α) => g a :=
  sorry

theorem integral_add' {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [normed_space ℝ E] [complete_space E]
    [measurable_space E] [borel_space E] {f : α → E} {g : α → E} {μ : measure α} (hf : integrable f)
    (hg : integrable g) :
    (integral μ fun (a : α) => Add.add f g a) =
        (integral μ fun (a : α) => f a) + integral μ fun (a : α) => g a :=
  integral_add hf hg

theorem integral_neg {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [normed_space ℝ E] [complete_space E]
    [measurable_space E] [borel_space E] {μ : measure α} (f : α → E) :
    (integral μ fun (a : α) => -f a) = -integral μ fun (a : α) => f a :=
  sorry

theorem integral_neg' {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [normed_space ℝ E] [complete_space E]
    [measurable_space E] [borel_space E] {μ : measure α} (f : α → E) :
    (integral μ fun (a : α) => Neg.neg f a) = -integral μ fun (a : α) => f a :=
  integral_neg f

theorem integral_sub {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [normed_space ℝ E] [complete_space E]
    [measurable_space E] [borel_space E] {f : α → E} {g : α → E} {μ : measure α} (hf : integrable f)
    (hg : integrable g) :
    (integral μ fun (a : α) => f a - g a) =
        (integral μ fun (a : α) => f a) - integral μ fun (a : α) => g a :=
  sorry

theorem integral_sub' {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [normed_space ℝ E] [complete_space E]
    [measurable_space E] [borel_space E] {f : α → E} {g : α → E} {μ : measure α} (hf : integrable f)
    (hg : integrable g) :
    (integral μ fun (a : α) => Sub.sub f g a) =
        (integral μ fun (a : α) => f a) - integral μ fun (a : α) => g a :=
  integral_sub hf hg

theorem integral_smul {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [normed_space ℝ E] [complete_space E]
    [measurable_space E] [borel_space E] {μ : measure α} (r : ℝ) (f : α → E) :
    (integral μ fun (a : α) => r • f a) = r • integral μ fun (a : α) => f a :=
  sorry

theorem integral_mul_left {α : Type u_1} [measurable_space α] {μ : measure α} (r : ℝ) (f : α → ℝ) :
    (integral μ fun (a : α) => r * f a) = r * integral μ fun (a : α) => f a :=
  integral_smul r f

theorem integral_mul_right {α : Type u_1} [measurable_space α] {μ : measure α} (r : ℝ) (f : α → ℝ) :
    (integral μ fun (a : α) => f a * r) = (integral μ fun (a : α) => f a) * r :=
  sorry

theorem integral_div {α : Type u_1} [measurable_space α] {μ : measure α} (r : ℝ) (f : α → ℝ) :
    (integral μ fun (a : α) => f a / r) = (integral μ fun (a : α) => f a) / r :=
  integral_mul_right (r⁻¹) f

theorem integral_congr_ae {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [normed_space ℝ E] [complete_space E]
    [measurable_space E] [borel_space E] {f : α → E} {g : α → E} {μ : measure α}
    (h : filter.eventually_eq (measure.ae μ) f g) :
    (integral μ fun (a : α) => f a) = integral μ fun (a : α) => g a :=
  sorry

@[simp] theorem l1.integral_of_fun_eq_integral {α : Type u_1} {E : Type u_2} [measurable_space α]
    [normed_group E] [topological_space.second_countable_topology E] [normed_space ℝ E]
    [complete_space E] [measurable_space E] [borel_space E] {μ : measure α} {f : α → E}
    (hf : integrable f) :
    (integral μ fun (a : α) => coe_fn (l1.of_fun f hf) a) = integral μ fun (a : α) => f a :=
  integral_congr_ae (l1.to_fun_of_fun f hf)

theorem continuous_integral {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [normed_space ℝ E] [complete_space E]
    [measurable_space E] [borel_space E] {μ : measure α} :
    continuous fun (f : l1 α E μ) => integral μ fun (a : α) => coe_fn f a :=
  sorry

theorem norm_integral_le_lintegral_norm {α : Type u_1} {E : Type u_2} [measurable_space α]
    [normed_group E] [topological_space.second_countable_topology E] [normed_space ℝ E]
    [complete_space E] [measurable_space E] [borel_space E] {μ : measure α} (f : α → E) :
    norm (integral μ fun (a : α) => f a) ≤
        ennreal.to_real (lintegral μ fun (a : α) => ennreal.of_real (norm (f a))) :=
  sorry

theorem ennnorm_integral_le_lintegral_ennnorm {α : Type u_1} {E : Type u_2} [measurable_space α]
    [normed_group E] [topological_space.second_countable_topology E] [normed_space ℝ E]
    [complete_space E] [measurable_space E] [borel_space E] {μ : measure α} (f : α → E) :
    ↑(nnnorm (integral μ fun (a : α) => f a)) ≤ lintegral μ fun (a : α) => ↑(nnnorm (f a)) :=
  sorry

theorem integral_eq_zero_of_ae {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [normed_space ℝ E] [complete_space E]
    [measurable_space E] [borel_space E] {μ : measure α} {f : α → E}
    (hf : filter.eventually_eq (measure.ae μ) f 0) : (integral μ fun (a : α) => f a) = 0 :=
  sorry

/-- If `f` has finite integral, then `∫ x in s, f x ∂μ` is absolutely continuous in `s`: it tends
to zero as `μ s` tends to zero. -/
theorem has_finite_integral.tendsto_set_integral_nhds_zero {α : Type u_1} {E : Type u_2}
    [measurable_space α] [normed_group E] [topological_space.second_countable_topology E]
    [normed_space ℝ E] [complete_space E] [measurable_space E] [borel_space E] {μ : measure α}
    {ι : Type u_3} {f : α → E} (hf : has_finite_integral f) {l : filter ι} {s : ι → set α}
    (hs : filter.tendsto (⇑μ ∘ s) l (nhds 0)) :
    filter.tendsto (fun (i : ι) => integral (measure.restrict μ (s i)) fun (x : α) => f x) l
        (nhds 0) :=
  sorry

/-- If `f` is integrable, then `∫ x in s, f x ∂μ` is absolutely continuous in `s`: it tends
to zero as `μ s` tends to zero. -/
theorem integrable.tendsto_set_integral_nhds_zero {α : Type u_1} {E : Type u_2} [measurable_space α]
    [normed_group E] [topological_space.second_countable_topology E] [normed_space ℝ E]
    [complete_space E] [measurable_space E] [borel_space E] {μ : measure α} {ι : Type u_3}
    {f : α → E} (hf : integrable f) {l : filter ι} {s : ι → set α}
    (hs : filter.tendsto (⇑μ ∘ s) l (nhds 0)) :
    filter.tendsto (fun (i : ι) => integral (measure.restrict μ (s i)) fun (x : α) => f x) l
        (nhds 0) :=
  has_finite_integral.tendsto_set_integral_nhds_zero (and.right hf) hs

/-- If `F i → f` in `L1`, then `∫ x, F i x ∂μ → ∫ x, f x∂μ`. -/
theorem tendsto_integral_of_l1 {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [normed_space ℝ E] [complete_space E]
    [measurable_space E] [borel_space E] {μ : measure α} {ι : Type u_3} (f : α → E)
    (hfi : integrable f) {F : ι → α → E} {l : filter ι}
    (hFi : filter.eventually (fun (i : ι) => integrable (F i)) l)
    (hF :
      filter.tendsto (fun (i : ι) => lintegral μ fun (x : α) => edist (F i x) (f x)) l (nhds 0)) :
    filter.tendsto (fun (i : ι) => integral μ fun (x : α) => F i x) l
        (nhds (integral μ fun (x : α) => f x)) :=
  sorry

/-- Lebesgue dominated convergence theorem provides sufficient conditions under which almost
  everywhere convergence of a sequence of functions implies the convergence of their integrals. -/
theorem tendsto_integral_of_dominated_convergence {α : Type u_1} {E : Type u_2} [measurable_space α]
    [normed_group E] [topological_space.second_countable_topology E] [normed_space ℝ E]
    [complete_space E] [measurable_space E] [borel_space E] {μ : measure α} {F : ℕ → α → E}
    {f : α → E} (bound : α → ℝ) (F_measurable : ∀ (n : ℕ), ae_measurable (F n))
    (f_measurable : ae_measurable f) (bound_integrable : integrable bound)
    (h_bound : ∀ (n : ℕ), filter.eventually (fun (a : α) => norm (F n a) ≤ bound a) (measure.ae μ))
    (h_lim :
      filter.eventually
        (fun (a : α) => filter.tendsto (fun (n : ℕ) => F n a) filter.at_top (nhds (f a)))
        (measure.ae μ)) :
    filter.tendsto (fun (n : ℕ) => integral μ fun (a : α) => F n a) filter.at_top
        (nhds (integral μ fun (a : α) => f a)) :=
  sorry

/-- Lebesgue dominated convergence theorem for filters with a countable basis -/
theorem tendsto_integral_filter_of_dominated_convergence {α : Type u_1} {E : Type u_2}
    [measurable_space α] [normed_group E] [topological_space.second_countable_topology E]
    [normed_space ℝ E] [complete_space E] [measurable_space E] [borel_space E] {μ : measure α}
    {ι : Type u_3} {l : filter ι} {F : ι → α → E} {f : α → E} (bound : α → ℝ)
    (hl_cb : filter.is_countably_generated l)
    (hF_meas : filter.eventually (fun (n : ι) => ae_measurable (F n)) l)
    (f_measurable : ae_measurable f)
    (h_bound :
      filter.eventually
        (fun (n : ι) => filter.eventually (fun (a : α) => norm (F n a) ≤ bound a) (measure.ae μ)) l)
    (bound_integrable : integrable bound)
    (h_lim :
      filter.eventually (fun (a : α) => filter.tendsto (fun (n : ι) => F n a) l (nhds (f a)))
        (measure.ae μ)) :
    filter.tendsto (fun (n : ι) => integral μ fun (a : α) => F n a) l
        (nhds (integral μ fun (a : α) => f a)) :=
  sorry

/-- The Bochner integral of a real-valued function `f : α → ℝ` is the difference between the
  integral of the positive part of `f` and the integral of the negative part of `f`.  -/
theorem integral_eq_lintegral_max_sub_lintegral_min {α : Type u_1} [measurable_space α]
    {μ : measure α} {f : α → ℝ} (hf : integrable f) :
    (integral μ fun (a : α) => f a) =
        ennreal.to_real (lintegral μ fun (a : α) => ennreal.of_real (max (f a) 0)) -
          ennreal.to_real (lintegral μ fun (a : α) => ennreal.of_real (-min (f a) 0)) :=
  sorry

-- Go to the `L¹` space

-- Go to the `L¹` space

theorem integral_eq_lintegral_of_nonneg_ae {α : Type u_1} [measurable_space α] {μ : measure α}
    {f : α → ℝ} (hf : filter.eventually_le (measure.ae μ) 0 f) (hfm : ae_measurable f) :
    (integral μ fun (a : α) => f a) =
        ennreal.to_real (lintegral μ fun (a : α) => ennreal.of_real (f a)) :=
  sorry

theorem integral_nonneg_of_ae {α : Type u_1} [measurable_space α] {μ : measure α} {f : α → ℝ}
    (hf : filter.eventually_le (measure.ae μ) 0 f) : 0 ≤ integral μ fun (a : α) => f a :=
  sorry

theorem lintegral_coe_eq_integral {α : Type u_1} [measurable_space α] {μ : measure α}
    (f : α → nnreal) (hfi : integrable fun (x : α) => ↑(f x)) :
    (lintegral μ fun (a : α) => ↑(f a)) = ennreal.of_real (integral μ fun (x : α) => ↑(f x)) :=
  sorry

theorem integral_to_real {α : Type u_1} [measurable_space α] {μ : measure α} {f : α → ennreal}
    (hfm : ae_measurable f) (hf : filter.eventually (fun (x : α) => f x < ⊤) (measure.ae μ)) :
    (integral μ fun (a : α) => ennreal.to_real (f a)) =
        ennreal.to_real (lintegral μ fun (a : α) => f a) :=
  sorry

theorem integral_nonneg {α : Type u_1} [measurable_space α] {μ : measure α} {f : α → ℝ}
    (hf : 0 ≤ f) : 0 ≤ integral μ fun (a : α) => f a :=
  integral_nonneg_of_ae (filter.eventually_of_forall hf)

theorem integral_nonpos_of_ae {α : Type u_1} [measurable_space α] {μ : measure α} {f : α → ℝ}
    (hf : filter.eventually_le (measure.ae μ) f 0) : (integral μ fun (a : α) => f a) ≤ 0 :=
  sorry

theorem integral_nonpos {α : Type u_1} [measurable_space α] {μ : measure α} {f : α → ℝ}
    (hf : f ≤ 0) : (integral μ fun (a : α) => f a) ≤ 0 :=
  integral_nonpos_of_ae (filter.eventually_of_forall hf)

theorem integral_eq_zero_iff_of_nonneg_ae {α : Type u_1} [measurable_space α] {μ : measure α}
    {f : α → ℝ} (hf : filter.eventually_le (measure.ae μ) 0 f) (hfi : integrable f) :
    (integral μ fun (x : α) => f x) = 0 ↔ filter.eventually_eq (measure.ae μ) f 0 :=
  sorry

theorem integral_eq_zero_iff_of_nonneg {α : Type u_1} [measurable_space α] {μ : measure α}
    {f : α → ℝ} (hf : 0 ≤ f) (hfi : integrable f) :
    (integral μ fun (x : α) => f x) = 0 ↔ filter.eventually_eq (measure.ae μ) f 0 :=
  integral_eq_zero_iff_of_nonneg_ae (filter.eventually_of_forall hf) hfi

theorem integral_pos_iff_support_of_nonneg_ae {α : Type u_1} [measurable_space α] {μ : measure α}
    {f : α → ℝ} (hf : filter.eventually_le (measure.ae μ) 0 f) (hfi : integrable f) :
    (0 < integral μ fun (x : α) => f x) ↔ 0 < coe_fn μ (function.support f) :=
  sorry

theorem integral_pos_iff_support_of_nonneg {α : Type u_1} [measurable_space α] {μ : measure α}
    {f : α → ℝ} (hf : 0 ≤ f) (hfi : integrable f) :
    (0 < integral μ fun (x : α) => f x) ↔ 0 < coe_fn μ (function.support f) :=
  integral_pos_iff_support_of_nonneg_ae (filter.eventually_of_forall hf) hfi

theorem l1.norm_eq_integral_norm {α : Type u_1} [measurable_space α] {μ : measure α} {H : Type u_4}
    [normed_group H] [topological_space.second_countable_topology H] [measurable_space H]
    [borel_space H] (f : l1 α H μ) : norm f = integral μ fun (a : α) => norm (coe_fn f a) :=
  sorry

theorem l1.norm_of_fun_eq_integral_norm {α : Type u_1} [measurable_space α] {μ : measure α}
    {H : Type u_4} [normed_group H] [topological_space.second_countable_topology H]
    [measurable_space H] [borel_space H] {f : α → H} (hf : integrable f) :
    norm (l1.of_fun f hf) = integral μ fun (a : α) => norm (f a) :=
  sorry

theorem integral_mono_ae {α : Type u_1} [measurable_space α] {μ : measure α} {f : α → ℝ} {g : α → ℝ}
    (hf : integrable f) (hg : integrable g) (h : filter.eventually_le (measure.ae μ) f g) :
    (integral μ fun (a : α) => f a) ≤ integral μ fun (a : α) => g a :=
  le_of_sub_nonneg
    (Eq.subst (integral_sub hg hf) integral_nonneg_of_ae
      (filter.eventually.mono h fun (a : α) => sub_nonneg_of_le))

theorem integral_mono {α : Type u_1} [measurable_space α] {μ : measure α} {f : α → ℝ} {g : α → ℝ}
    (hf : integrable f) (hg : integrable g) (h : f ≤ g) :
    (integral μ fun (a : α) => f a) ≤ integral μ fun (a : α) => g a :=
  integral_mono_ae hf hg (filter.eventually_of_forall h)

theorem integral_mono_of_nonneg {α : Type u_1} [measurable_space α] {μ : measure α} {f : α → ℝ}
    {g : α → ℝ} (hf : filter.eventually_le (measure.ae μ) 0 f) (hgi : integrable g)
    (h : filter.eventually_le (measure.ae μ) f g) :
    (integral μ fun (a : α) => f a) ≤ integral μ fun (a : α) => g a :=
  sorry

theorem norm_integral_le_integral_norm {α : Type u_1} {E : Type u_2} [measurable_space α]
    [normed_group E] [topological_space.second_countable_topology E] [normed_space ℝ E]
    [complete_space E] [measurable_space E] [borel_space E] {μ : measure α} (f : α → E) :
    norm (integral μ fun (a : α) => f a) ≤ integral μ fun (a : α) => norm (f a) :=
  sorry

theorem norm_integral_le_of_norm_le {α : Type u_1} {E : Type u_2} [measurable_space α]
    [normed_group E] [topological_space.second_countable_topology E] [normed_space ℝ E]
    [complete_space E] [measurable_space E] [borel_space E] {μ : measure α} {f : α → E} {g : α → ℝ}
    (hg : integrable g) (h : filter.eventually (fun (x : α) => norm (f x) ≤ g x) (measure.ae μ)) :
    norm (integral μ fun (x : α) => f x) ≤ integral μ fun (x : α) => g x :=
  le_trans (norm_integral_le_integral_norm f)
    (integral_mono_of_nonneg (filter.eventually_of_forall fun (x : α) => norm_nonneg (f x)) hg h)

theorem integral_finset_sum {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [normed_space ℝ E] [complete_space E]
    [measurable_space E] [borel_space E] {μ : measure α} {ι : Type u_3} (s : finset ι)
    {f : ι → α → E} (hf : ∀ (i : ι), integrable (f i)) :
    (integral μ fun (a : α) => finset.sum s fun (i : ι) => f i a) =
        finset.sum s fun (i : ι) => integral μ fun (a : α) => f i a :=
  sorry

theorem simple_func.integral_eq_integral {α : Type u_1} {E : Type u_2} [measurable_space α]
    [normed_group E] [topological_space.second_countable_topology E] [normed_space ℝ E]
    [complete_space E] [measurable_space E] [borel_space E] {μ : measure α} (f : simple_func α E)
    (hfi : integrable ⇑f) : simple_func.integral μ f = integral μ fun (x : α) => coe_fn f x :=
  sorry

@[simp] theorem integral_const {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [normed_space ℝ E] [complete_space E]
    [measurable_space E] [borel_space E] {μ : measure α} (c : E) :
    (integral μ fun (x : α) => c) = ennreal.to_real (coe_fn μ set.univ) • c :=
  sorry

theorem norm_integral_le_of_norm_le_const {α : Type u_1} {E : Type u_2} [measurable_space α]
    [normed_group E] [topological_space.second_countable_topology E] [normed_space ℝ E]
    [complete_space E] [measurable_space E] [borel_space E] {μ : measure α} [finite_measure μ]
    {f : α → E} {C : ℝ} (h : filter.eventually (fun (x : α) => norm (f x) ≤ C) (measure.ae μ)) :
    norm (integral μ fun (x : α) => f x) ≤ C * ennreal.to_real (coe_fn μ set.univ) :=
  sorry

theorem tendsto_integral_approx_on_univ_of_measurable {α : Type u_1} {E : Type u_2}
    [measurable_space α] [normed_group E] [topological_space.second_countable_topology E]
    [normed_space ℝ E] [complete_space E] [measurable_space E] [borel_space E] {μ : measure α}
    {f : α → E} (fmeas : measurable f) (hf : integrable f) :
    filter.tendsto
        (fun (n : ℕ) => simple_func.integral μ (simple_func.approx_on f fmeas set.univ 0 trivial n))
        filter.at_top (nhds (integral μ fun (x : α) => f x)) :=
  sorry

theorem integral_add_measure {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [normed_space ℝ E] [complete_space E]
    [measurable_space E] [borel_space E] {μ : measure α} {ν : measure α} {f : α → E}
    (hμ : integrable f) (hν : integrable f) :
    (integral (μ + ν) fun (x : α) => f x) =
        (integral μ fun (x : α) => f x) + integral ν fun (x : α) => f x :=
  sorry

@[simp] theorem integral_zero_measure {α : Type u_1} {E : Type u_2} [measurable_space α]
    [normed_group E] [topological_space.second_countable_topology E] [normed_space ℝ E]
    [complete_space E] [measurable_space E] [borel_space E] (f : α → E) :
    (integral 0 fun (x : α) => f x) = 0 :=
  sorry

@[simp] theorem integral_smul_measure {α : Type u_1} {E : Type u_2} [measurable_space α]
    [normed_group E] [topological_space.second_countable_topology E] [normed_space ℝ E]
    [complete_space E] [measurable_space E] [borel_space E] {μ : measure α} (f : α → E)
    (c : ennreal) :
    (integral (c • μ) fun (x : α) => f x) = ennreal.to_real c • integral μ fun (x : α) => f x :=
  sorry

theorem integral_map_of_measurable {α : Type u_1} {E : Type u_2} [measurable_space α]
    [normed_group E] [topological_space.second_countable_topology E] [normed_space ℝ E]
    [complete_space E] [measurable_space E] [borel_space E] {μ : measure α} {β : Type u_3}
    [measurable_space β] {φ : α → β} (hφ : measurable φ) {f : β → E} (hfm : measurable f) :
    (integral (coe_fn (measure.map φ) μ) fun (y : β) => f y) = integral μ fun (x : α) => f (φ x) :=
  sorry

theorem integral_map {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [normed_space ℝ E] [complete_space E]
    [measurable_space E] [borel_space E] {μ : measure α} {β : Type u_3} [measurable_space β]
    {φ : α → β} (hφ : measurable φ) {f : β → E} (hfm : ae_measurable f) :
    (integral (coe_fn (measure.map φ) μ) fun (y : β) => f y) = integral μ fun (x : α) => f (φ x) :=
  sorry

theorem integral_dirac' {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [normed_space ℝ E] [complete_space E]
    [measurable_space E] [borel_space E] (f : α → E) (a : α) (hfm : measurable f) :
    (integral (measure.dirac a) fun (x : α) => f x) = f a :=
  sorry

theorem integral_dirac {α : Type u_1} {E : Type u_2} [measurable_space α] [normed_group E]
    [topological_space.second_countable_topology E] [normed_space ℝ E] [complete_space E]
    [measurable_space E] [borel_space E] [measurable_singleton_class α] (f : α → E) (a : α) :
    (integral (measure.dirac a) fun (x : α) => f x) = f a :=
  sorry

end Mathlib