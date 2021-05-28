/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo, Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.algebra.ring
import Mathlib.topology.uniform_space.uniform_embedding
import Mathlib.algebra.algebra.basic
import Mathlib.linear_algebra.projection
import Mathlib.PostPort

universes u v l u_1 u_2 u_3 u_4 u_5 

namespace Mathlib

/-!
# Theory of topological modules and continuous linear maps.

We define classes `topological_semimodule`, `topological_module` and `topological_vector_spaces`,
as extensions of the corresponding algebraic classes where the algebraic operations are continuous.

We also define continuous linear maps, as linear maps between topological modules which are
continuous. The set of continuous linear maps between the topological `R`-modules `M` and `M₂` is
denoted by `M →L[R] M₂`.

Continuous linear equivalences are denoted by `M ≃L[R] M₂`.

## Implementation notes

Topological vector spaces are defined as an `abbreviation` for topological modules,
if the base ring is a field. This has as advantage that topological vector spaces are completely
transparent for type class inference, which means that all instances for topological modules
are immediately picked up for vector spaces as well.
A cosmetic disadvantage is that one can not extend topological vector spaces.
The solution is to extend `topological_module` instead.
-/

/-- A topological semimodule, over a semiring which is also a topological space, is a
semimodule in which scalar multiplication is continuous. In applications, R will be a topological
semiring and M a topological additive semigroup, but this is not needed for the definition -/
class topological_semimodule (R : Type u) (M : Type v) [semiring R] [topological_space R] [topological_space M] [add_comm_monoid M] [semimodule R M] 
where
  continuous_smul : continuous fun (p : R × M) => prod.fst p • prod.snd p

theorem continuous_smul {R : Type u} {M : Type v} [semiring R] [topological_space R] [topological_space M] [add_comm_monoid M] [semimodule R M] [topological_semimodule R M] : continuous fun (p : R × M) => prod.fst p • prod.snd p :=
  topological_semimodule.continuous_smul

theorem continuous.smul {R : Type u} {M : Type v} [semiring R] [topological_space R] [topological_space M] [add_comm_monoid M] [semimodule R M] [topological_semimodule R M] {α : Type u_1} [topological_space α] {f : α → R} {g : α → M} (hf : continuous f) (hg : continuous g) : continuous fun (p : α) => f p • g p :=
  continuous.comp continuous_smul (continuous.prod_mk hf hg)

theorem tendsto_smul {R : Type u} {M : Type v} [semiring R] [topological_space R] [topological_space M] [add_comm_monoid M] [semimodule R M] [topological_semimodule R M] {c : R} {x : M} : filter.tendsto (fun (p : R × M) => prod.fst p • prod.snd p) (nhds (c, x)) (nhds (c • x)) :=
  continuous.tendsto continuous_smul (c, x)

theorem filter.tendsto.smul {R : Type u} {M : Type v} [semiring R] [topological_space R] [topological_space M] [add_comm_monoid M] [semimodule R M] [topological_semimodule R M] {α : Type u_1} {l : filter α} {f : α → R} {g : α → M} {c : R} {x : M} (hf : filter.tendsto f l (nhds c)) (hg : filter.tendsto g l (nhds x)) : filter.tendsto (fun (a : α) => f a • g a) l (nhds (c • x)) :=
  filter.tendsto.comp tendsto_smul (filter.tendsto.prod_mk_nhds hf hg)

protected instance topological_semiring.to_semimodule {R : Type u_1} [topological_space R] [semiring R] [topological_semiring R] : topological_semimodule R R :=
  topological_semimodule.mk continuous_mul

/-- A topological module, over a ring which is also a topological space, is a module in which
scalar multiplication is continuous. In applications, `R` will be a topological ring and `M` a
topological additive group, but this is not needed for the definition -/
def topological_module (R : Type u) (M : Type v) [ring R] [topological_space R] [topological_space M] [add_comm_group M] [module R M]  :=
  topological_semimodule R M

/-- A topological vector space is a topological module over a field. -/
def topological_vector_space (R : Type u) (M : Type v) [field R] [topological_space R] [topological_space M] [add_comm_group M] [module R M]  :=
  topological_module R M

/-- Scalar multiplication by a unit is a homeomorphism from a
topological module onto itself. -/
protected def homeomorph.smul_of_unit {R : Type u_1} {M : Type u_2} [ring R] [topological_space R] [topological_space M] [add_comm_group M] [module R M] [topological_module R M] (a : units R) : M ≃ₜ M :=
  homeomorph.mk (equiv.mk (fun (x : M) => ↑a • x) (fun (x : M) => ↑(a⁻¹) • x) sorry sorry)

theorem is_open_map_smul_of_unit {R : Type u_1} {M : Type u_2} [ring R] [topological_space R] [topological_space M] [add_comm_group M] [module R M] [topological_module R M] (a : units R) : is_open_map fun (x : M) => ↑a • x :=
  homeomorph.is_open_map (homeomorph.smul_of_unit a)

theorem is_closed_map_smul_of_unit {R : Type u_1} {M : Type u_2} [ring R] [topological_space R] [topological_space M] [add_comm_group M] [module R M] [topological_module R M] (a : units R) : is_closed_map fun (x : M) => ↑a • x :=
  homeomorph.is_closed_map (homeomorph.smul_of_unit a)

/-- If `M` is a topological module over `R` and `0` is a limit of invertible elements of `R`, then
`⊤` is the only submodule of `M` with a nonempty interior.
This is the case, e.g., if `R` is a nondiscrete normed field. -/
theorem submodule.eq_top_of_nonempty_interior' {R : Type u_1} {M : Type u_2} [ring R] [topological_space R] [topological_space M] [add_comm_group M] [module R M] [topological_module R M] [has_continuous_add M] [filter.ne_bot (nhds_within 0 (set_of fun (x : R) => is_unit x))] (s : submodule R M) (hs : set.nonempty (interior ↑s)) : s = ⊤ := sorry

theorem submodule.closure_smul_self_subset {R : Type u} {M : Type v} [semiring R] [topological_space R] [topological_space M] [add_comm_monoid M] [semimodule R M] [topological_semimodule R M] (s : submodule R M) : (fun (p : R × M) => prod.fst p • prod.snd p) '' set.prod set.univ (closure ↑s) ⊆ closure ↑s := sorry

theorem submodule.closure_smul_self_eq {R : Type u} {M : Type v} [semiring R] [topological_space R] [topological_space M] [add_comm_monoid M] [semimodule R M] [topological_semimodule R M] (s : submodule R M) : (fun (p : R × M) => prod.fst p • prod.snd p) '' set.prod set.univ (closure ↑s) = closure ↑s := sorry

/-- The (topological-space) closure of a submodle of a topological `R`-semimodule `M` is itself
a submodule. -/
def submodule.topological_closure {R : Type u} {M : Type v} [semiring R] [topological_space R] [topological_space M] [add_comm_monoid M] [semimodule R M] [topological_semimodule R M] [has_continuous_add M] (s : submodule R M) : submodule R M :=
  submodule.mk (closure ↑s) sorry sorry sorry

theorem submodule.submodule_topological_closure {R : Type u} {M : Type v} [semiring R] [topological_space R] [topological_space M] [add_comm_monoid M] [semimodule R M] [topological_semimodule R M] [has_continuous_add M] (s : submodule R M) : s ≤ submodule.topological_closure s :=
  subset_closure

theorem submodule.is_closed_topological_closure {R : Type u} {M : Type v} [semiring R] [topological_space R] [topological_space M] [add_comm_monoid M] [semimodule R M] [topological_semimodule R M] [has_continuous_add M] (s : submodule R M) : is_closed ↑(submodule.topological_closure s) := sorry

theorem submodule.topological_closure_minimal {R : Type u} {M : Type v} [semiring R] [topological_space R] [topological_space M] [add_comm_monoid M] [semimodule R M] [topological_semimodule R M] [has_continuous_add M] (s : submodule R M) {t : submodule R M} (h : s ≤ t) (ht : is_closed ↑t) : submodule.topological_closure s ≤ t :=
  closure_minimal h ht

/-- Scalar multiplication by a non-zero field element is a
homeomorphism from a topological vector space onto itself. -/
protected def homeomorph.smul_of_ne_zero {R : Type u_1} {M : Type u_2} {a : R} [field R] [topological_space R] [topological_space M] [add_comm_group M] [vector_space R M] [topological_vector_space R M] (ha : a ≠ 0) : M ≃ₜ M :=
  homeomorph.mk (homeomorph.to_equiv (homeomorph.smul_of_unit (units.mk0 a ha)))

theorem is_open_map_smul_of_ne_zero {R : Type u_1} {M : Type u_2} {a : R} [field R] [topological_space R] [topological_space M] [add_comm_group M] [vector_space R M] [topological_vector_space R M] (ha : a ≠ 0) : is_open_map fun (x : M) => a • x :=
  homeomorph.is_open_map (homeomorph.smul_of_ne_zero ha)

/-- `smul` is a closed map in the second argument.

The lemma that `smul` is a closed map in the first argument (for a normed space over a complete
normed field) is `is_closed_map_smul_left` in `analysis.normed_space.finite_dimension`. -/
theorem is_closed_map_smul_of_ne_zero {R : Type u_1} {M : Type u_2} {a : R} [field R] [topological_space R] [topological_space M] [add_comm_group M] [vector_space R M] [topological_vector_space R M] (ha : a ≠ 0) : is_closed_map fun (x : M) => a • x :=
  homeomorph.is_closed_map (homeomorph.smul_of_ne_zero ha)

/-- Continuous linear maps between modules. We only put the type classes that are necessary for the
definition, although in applications `M` and `M₂` will be topological modules over the topological
ring `R`. -/
structure continuous_linear_map (R : Type u_1) [semiring R] (M : Type u_2) [topological_space M] [add_comm_monoid M] (M₂ : Type u_3) [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] 
extends linear_map R M M₂
where
  cont : autoParam (continuous (linear_map.to_fun _to_linear_map))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.tactic.interactive.continuity'")
    (Lean.Name.mkStr
      (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "tactic") "interactive")
      "continuity'")
    [])

/-- Continuous linear equivalences between modules. We only put the type classes that are necessary
for the definition, although in applications `M` and `M₂` will be topological modules over the
topological ring `R`. -/
structure continuous_linear_equiv (R : Type u_1) [semiring R] (M : Type u_2) [topological_space M] [add_comm_monoid M] (M₂ : Type u_3) [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] 
extends linear_equiv R M M₂
where
  continuous_to_fun : autoParam (continuous (linear_equiv.to_fun _to_linear_equiv))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.tactic.interactive.continuity'")
    (Lean.Name.mkStr
      (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "tactic") "interactive")
      "continuity'")
    [])
  continuous_inv_fun : autoParam (continuous (linear_equiv.inv_fun _to_linear_equiv))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.tactic.interactive.continuity'")
    (Lean.Name.mkStr
      (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "tactic") "interactive")
      "continuity'")
    [])

namespace continuous_linear_map


/-!
### Properties that hold for non-necessarily commutative semirings.
-/

/-- Coerce continuous linear maps to linear maps. -/
protected instance linear_map.has_coe {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : has_coe (continuous_linear_map R M M₂) (linear_map R M M₂) :=
  has_coe.mk to_linear_map

/-- Coerce continuous linear maps to functions. -/
-- see Note [function coercion]

protected instance to_fun {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : has_coe_to_fun (continuous_linear_map R M M₂) :=
  has_coe_to_fun.mk (fun (_x : continuous_linear_map R M M₂) => M → M₂) fun (f : continuous_linear_map R M M₂) => ⇑f

@[simp] theorem coe_mk {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M M₂) (h : autoParam (continuous (linear_map.to_fun f))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.tactic.interactive.continuity'")
    (Lean.Name.mkStr
      (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "tactic") "interactive")
      "continuity'")
    [])) : ↑(mk f) = f :=
  rfl

@[simp] theorem coe_mk' {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M M₂) (h : autoParam (continuous (linear_map.to_fun f))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.tactic.interactive.continuity'")
    (Lean.Name.mkStr
      (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "tactic") "interactive")
      "continuity'")
    [])) : ⇑(mk f) = ⇑f :=
  rfl

protected theorem continuous {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : continuous_linear_map R M M₂) : continuous ⇑f :=
  cont f

theorem coe_injective {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : function.injective coe := sorry

theorem injective_coe_fn {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : function.injective fun (f : continuous_linear_map R M M₂) => (fun (this : M → M₂) => this) ⇑f :=
  function.injective.comp linear_map.coe_injective coe_injective

theorem ext {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {f : continuous_linear_map R M M₂} {g : continuous_linear_map R M M₂} (h : ∀ (x : M), coe_fn f x = coe_fn g x) : f = g :=
  injective_coe_fn (funext h)

theorem ext_iff {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {f : continuous_linear_map R M M₂} {g : continuous_linear_map R M M₂} : f = g ↔ ∀ (x : M), coe_fn f x = coe_fn g x :=
  { mp :=
      fun (h : f = g) (x : M) => eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn f x = coe_fn g x)) h)) (Eq.refl (coe_fn g x)),
    mpr := ext }

-- make some straightforward lemmas available to `simp`.

@[simp] theorem map_zero {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : continuous_linear_map R M M₂) : coe_fn f 0 = 0 :=
  linear_map.map_zero (to_linear_map f)

@[simp] theorem map_add {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : continuous_linear_map R M M₂) (x : M) (y : M) : coe_fn f (x + y) = coe_fn f x + coe_fn f y :=
  linear_map.map_add (to_linear_map f) x y

@[simp] theorem map_smul {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (c : R) (f : continuous_linear_map R M M₂) (x : M) : coe_fn f (c • x) = c • coe_fn f x :=
  linear_map.map_smul (to_linear_map f) c x

theorem map_sum {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : continuous_linear_map R M M₂) {ι : Type u_4} (s : finset ι) (g : ι → M) : coe_fn f (finset.sum s fun (i : ι) => g i) = finset.sum s fun (i : ι) => coe_fn f (g i) :=
  linear_map.map_sum (to_linear_map f)

@[simp] theorem coe_coe {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : continuous_linear_map R M M₂) : ⇑↑f = ⇑f :=
  rfl

/-- If two continuous linear maps are equal on a set `s`, then they are equal on the closure
of the `submodule.span` of this set. -/
theorem eq_on_closure_span {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] [t2_space M₂] {s : set M} {f : continuous_linear_map R M M₂} {g : continuous_linear_map R M M₂} (h : set.eq_on (⇑f) (⇑g) s) : set.eq_on (⇑f) (⇑g) (closure ↑(submodule.span R s)) :=
  set.eq_on.closure (linear_map.eq_on_span' h) (continuous_linear_map.continuous f) (continuous_linear_map.continuous g)

/-- If the submodule generated by a set `s` is dense in the ambient semimodule, then two continuous
linear maps equal on `s` are equal. -/
theorem ext_on {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] [t2_space M₂] {s : set M} (hs : dense ↑(submodule.span R s)) {f : continuous_linear_map R M M₂} {g : continuous_linear_map R M M₂} (h : set.eq_on (⇑f) (⇑g) s) : f = g :=
  ext fun (x : M) => eq_on_closure_span h (hs x)

/-- The continuous map that is constantly zero. -/
protected instance has_zero {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : HasZero (continuous_linear_map R M M₂) :=
  { zero := mk 0 }

protected instance inhabited {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : Inhabited (continuous_linear_map R M M₂) :=
  { default := 0 }

@[simp] theorem default_def {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : Inhabited.default = 0 :=
  rfl

@[simp] theorem zero_apply {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (x : M) : coe_fn 0 x = 0 :=
  rfl

/- no simp attribute on the next line as simp does not always simplify `0 x` to `0`
@[simp] theorem coe_zero {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : ↑0 = 0 :=
  rfl

when `0` is the zero function, while it does for the zero continuous linear map,
and this is the most important property we care about. -/

theorem coe_zero' {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : ⇑0 = 0 :=
  rfl

protected instance unique_of_left {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] [subsingleton M] : unique (continuous_linear_map R M M₂) :=
  function.injective.unique coe_injective

protected instance unique_of_right {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] [subsingleton M₂] : unique (continuous_linear_map R M M₂) :=
  function.injective.unique coe_injective

/-- the identity map as a continuous linear map. -/
def id (R : Type u_1) [semiring R] (M : Type u_2) [topological_space M] [add_comm_monoid M] [semimodule R M] : continuous_linear_map R M M :=
  mk linear_map.id

protected instance has_one {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] [semimodule R M] : HasOne (continuous_linear_map R M M) :=
  { one := id R M }

theorem one_def {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] [semimodule R M] : 1 = id R M :=
  rfl

theorem id_apply {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] [semimodule R M] (x : M) : coe_fn (id R M) x = x :=
  rfl

@[simp] theorem coe_id {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] [semimodule R M] : ↑(id R M) = linear_map.id :=
  rfl

@[simp] theorem coe_id' {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] [semimodule R M] : ⇑(id R M) = id :=
  rfl

@[simp] theorem one_apply {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] [semimodule R M] (x : M) : coe_fn 1 x = x :=
  rfl

protected instance has_add {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] [has_continuous_add M₂] : Add (continuous_linear_map R M M₂) :=
  { add := fun (f g : continuous_linear_map R M M₂) => mk (↑f + ↑g) }

@[simp] theorem add_apply {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : continuous_linear_map R M M₂) (g : continuous_linear_map R M M₂) (x : M) [has_continuous_add M₂] : coe_fn (f + g) x = coe_fn f x + coe_fn g x :=
  rfl

@[simp] theorem coe_add {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : continuous_linear_map R M M₂) (g : continuous_linear_map R M M₂) [has_continuous_add M₂] : ↑(f + g) = ↑f + ↑g :=
  rfl

theorem coe_add' {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : continuous_linear_map R M M₂) (g : continuous_linear_map R M M₂) [has_continuous_add M₂] : ⇑(f + g) = ⇑f + ⇑g :=
  rfl

protected instance add_comm_monoid {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] [has_continuous_add M₂] : add_comm_monoid (continuous_linear_map R M M₂) :=
  add_comm_monoid.mk Add.add sorry 0 sorry sorry sorry

theorem sum_apply {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] [has_continuous_add M₂] {ι : Type u_4} (t : finset ι) (f : ι → continuous_linear_map R M M₂) (b : M) : coe_fn (finset.sum t fun (d : ι) => f d) b = finset.sum t fun (d : ι) => coe_fn (f d) b :=
  Eq.symm (finset.sum_hom t fun (g : continuous_linear_map R M M₂) => coe_fn g b)

/-- Composition of bounded linear maps. -/
def comp {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] {M₃ : Type u_4} [topological_space M₃] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (g : continuous_linear_map R M₂ M₃) (f : continuous_linear_map R M M₂) : continuous_linear_map R M M₃ :=
  mk (linear_map.comp (to_linear_map g) (to_linear_map f))

@[simp] theorem coe_comp {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] {M₃ : Type u_4} [topological_space M₃] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (f : continuous_linear_map R M M₂) (h : continuous_linear_map R M₂ M₃) : ↑(comp h f) = linear_map.comp ↑h ↑f :=
  rfl

@[simp] theorem coe_comp' {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] {M₃ : Type u_4} [topological_space M₃] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (f : continuous_linear_map R M M₂) (h : continuous_linear_map R M₂ M₃) : ⇑(comp h f) = ⇑h ∘ ⇑f :=
  rfl

@[simp] theorem comp_id {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : continuous_linear_map R M M₂) : comp f (id R M) = f :=
  ext fun (x : M) => rfl

@[simp] theorem id_comp {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : continuous_linear_map R M M₂) : comp (id R M₂) f = f :=
  ext fun (x : M) => rfl

@[simp] theorem comp_zero {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] {M₃ : Type u_4} [topological_space M₃] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (f : continuous_linear_map R M M₂) : comp f 0 = 0 := sorry

@[simp] theorem zero_comp {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] {M₃ : Type u_4} [topological_space M₃] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (f : continuous_linear_map R M M₂) : comp 0 f = 0 := sorry

@[simp] theorem comp_add {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] {M₃ : Type u_4} [topological_space M₃] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] [has_continuous_add M₂] [has_continuous_add M₃] (g : continuous_linear_map R M₂ M₃) (f₁ : continuous_linear_map R M M₂) (f₂ : continuous_linear_map R M M₂) : comp g (f₁ + f₂) = comp g f₁ + comp g f₂ := sorry

@[simp] theorem add_comp {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] {M₃ : Type u_4} [topological_space M₃] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] [has_continuous_add M₃] (g₁ : continuous_linear_map R M₂ M₃) (g₂ : continuous_linear_map R M₂ M₃) (f : continuous_linear_map R M M₂) : comp (g₁ + g₂) f = comp g₁ f + comp g₂ f := sorry

theorem comp_assoc {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] {M₃ : Type u_4} [topological_space M₃] [add_comm_monoid M₃] {M₄ : Type u_5} [topological_space M₄] [add_comm_monoid M₄] [semimodule R M] [semimodule R M₂] [semimodule R M₃] [semimodule R M₄] (h : continuous_linear_map R M₃ M₄) (g : continuous_linear_map R M₂ M₃) (f : continuous_linear_map R M M₂) : comp (comp h g) f = comp h (comp g f) :=
  rfl

protected instance has_mul {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] [semimodule R M] : Mul (continuous_linear_map R M M) :=
  { mul := comp }

theorem mul_def {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] [semimodule R M] (f : continuous_linear_map R M M) (g : continuous_linear_map R M M) : f * g = comp f g :=
  rfl

@[simp] theorem coe_mul {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] [semimodule R M] (f : continuous_linear_map R M M) (g : continuous_linear_map R M M) : ⇑(f * g) = ⇑f ∘ ⇑g :=
  rfl

theorem mul_apply {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] [semimodule R M] (f : continuous_linear_map R M M) (g : continuous_linear_map R M M) (x : M) : coe_fn (f * g) x = coe_fn f (coe_fn g x) :=
  rfl

/-- The cartesian product of two bounded linear maps, as a bounded linear map. -/
protected def prod {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] {M₃ : Type u_4} [topological_space M₃] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (f₁ : continuous_linear_map R M M₂) (f₂ : continuous_linear_map R M M₃) : continuous_linear_map R M (M₂ × M₃) :=
  mk (linear_map.mk (linear_map.to_fun (linear_map.prod (to_linear_map f₁) (to_linear_map f₂))) sorry sorry)

@[simp] theorem coe_prod {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] {M₃ : Type u_4} [topological_space M₃] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (f₁ : continuous_linear_map R M M₂) (f₂ : continuous_linear_map R M M₃) : ↑(continuous_linear_map.prod f₁ f₂) = linear_map.prod ↑f₁ ↑f₂ :=
  rfl

@[simp] theorem prod_apply {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] {M₃ : Type u_4} [topological_space M₃] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (f₁ : continuous_linear_map R M M₂) (f₂ : continuous_linear_map R M M₃) (x : M) : coe_fn (continuous_linear_map.prod f₁ f₂) x = (coe_fn f₁ x, coe_fn f₂ x) :=
  rfl

/-- Kernel of a continuous linear map. -/
def ker {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : continuous_linear_map R M M₂) : submodule R M :=
  linear_map.ker ↑f

theorem ker_coe {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : continuous_linear_map R M M₂) : linear_map.ker ↑f = ker f :=
  rfl

@[simp] theorem mem_ker {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {f : continuous_linear_map R M M₂} {x : M} : x ∈ ker f ↔ coe_fn f x = 0 :=
  linear_map.mem_ker

theorem is_closed_ker {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : continuous_linear_map R M M₂) [t1_space M₂] : is_closed ↑(ker f) :=
  iff.mp continuous_iff_is_closed (cont f) (↑⊥) is_closed_singleton

@[simp] theorem apply_ker {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : continuous_linear_map R M M₂) (x : ↥(ker f)) : coe_fn f ↑x = 0 :=
  iff.mp mem_ker (subtype.property x)

theorem is_complete_ker {R : Type u_1} [semiring R] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M₂] {M' : Type u_2} [uniform_space M'] [complete_space M'] [add_comm_monoid M'] [semimodule R M'] [t1_space M₂] (f : continuous_linear_map R M' M₂) : is_complete ↑(ker f) :=
  is_closed.is_complete (is_closed_ker f)

protected instance complete_space_ker {R : Type u_1} [semiring R] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M₂] {M' : Type u_2} [uniform_space M'] [complete_space M'] [add_comm_monoid M'] [semimodule R M'] [t1_space M₂] (f : continuous_linear_map R M' M₂) : complete_space ↥(ker f) :=
  is_closed.complete_space_coe (is_closed_ker f)

@[simp] theorem ker_prod {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] {M₃ : Type u_4} [topological_space M₃] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (f : continuous_linear_map R M M₂) (g : continuous_linear_map R M M₃) : ker (continuous_linear_map.prod f g) = ker f ⊓ ker g :=
  linear_map.ker_prod ↑f ↑g

/-- Range of a continuous linear map. -/
def range {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : continuous_linear_map R M M₂) : submodule R M₂ :=
  linear_map.range ↑f

theorem range_coe {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : continuous_linear_map R M M₂) : ↑(range f) = set.range ⇑f :=
  linear_map.range_coe ↑f

theorem mem_range {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {f : continuous_linear_map R M M₂} {y : M₂} : y ∈ range f ↔ ∃ (x : M), coe_fn f x = y :=
  linear_map.mem_range

theorem range_prod_le {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] {M₃ : Type u_4} [topological_space M₃] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (f : continuous_linear_map R M M₂) (g : continuous_linear_map R M M₃) : range (continuous_linear_map.prod f g) ≤ submodule.prod (range f) (range g) :=
  linear_map.range_prod_le ↑f ↑g

/-- Restrict codomain of a continuous linear map. -/
def cod_restrict {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : continuous_linear_map R M M₂) (p : submodule R M₂) (h : ∀ (x : M), coe_fn f x ∈ p) : continuous_linear_map R M ↥p :=
  mk (linear_map.cod_restrict p (↑f) h)

theorem coe_cod_restrict {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : continuous_linear_map R M M₂) (p : submodule R M₂) (h : ∀ (x : M), coe_fn f x ∈ p) : ↑(cod_restrict f p h) = linear_map.cod_restrict p (↑f) h :=
  rfl

@[simp] theorem coe_cod_restrict_apply {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : continuous_linear_map R M M₂) (p : submodule R M₂) (h : ∀ (x : M), coe_fn f x ∈ p) (x : M) : ↑(coe_fn (cod_restrict f p h) x) = coe_fn f x :=
  rfl

@[simp] theorem ker_cod_restrict {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : continuous_linear_map R M M₂) (p : submodule R M₂) (h : ∀ (x : M), coe_fn f x ∈ p) : ker (cod_restrict f p h) = ker f :=
  linear_map.ker_cod_restrict p (↑f) h

/-- Embedding of a submodule into the ambient space as a continuous linear map. -/
def subtype_val {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] [semimodule R M] (p : submodule R M) : continuous_linear_map R (↥p) M :=
  mk (submodule.subtype p)

@[simp] theorem coe_subtype_val {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] [semimodule R M] (p : submodule R M) : ↑(subtype_val p) = submodule.subtype p :=
  rfl

@[simp] theorem subtype_val_apply {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] [semimodule R M] (p : submodule R M) (x : ↥p) : coe_fn (subtype_val p) x = ↑x :=
  rfl

/-- `prod.fst` as a `continuous_linear_map`. -/
def fst (R : Type u_1) [semiring R] (M : Type u_2) [topological_space M] [add_comm_monoid M] (M₂ : Type u_3) [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : continuous_linear_map R (M × M₂) M :=
  mk (linear_map.fst R M M₂)

/-- `prod.snd` as a `continuous_linear_map`. -/
def snd (R : Type u_1) [semiring R] (M : Type u_2) [topological_space M] [add_comm_monoid M] (M₂ : Type u_3) [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : continuous_linear_map R (M × M₂) M₂ :=
  mk (linear_map.snd R M M₂)

@[simp] theorem coe_fst {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : ↑(fst R M M₂) = linear_map.fst R M M₂ :=
  rfl

@[simp] theorem coe_fst' {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : ⇑(fst R M M₂) = prod.fst :=
  rfl

@[simp] theorem coe_snd {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : ↑(snd R M M₂) = linear_map.snd R M M₂ :=
  rfl

@[simp] theorem coe_snd' {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : ⇑(snd R M M₂) = prod.snd :=
  rfl

@[simp] theorem fst_prod_snd {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : continuous_linear_map.prod (fst R M M₂) (snd R M M₂) = id R (M × M₂) := sorry

/-- `prod.map` of two continuous linear maps. -/
def prod_map {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] {M₃ : Type u_4} [topological_space M₃] [add_comm_monoid M₃] {M₄ : Type u_5} [topological_space M₄] [add_comm_monoid M₄] [semimodule R M] [semimodule R M₂] [semimodule R M₃] [semimodule R M₄] (f₁ : continuous_linear_map R M M₂) (f₂ : continuous_linear_map R M₃ M₄) : continuous_linear_map R (M × M₃) (M₂ × M₄) :=
  continuous_linear_map.prod (comp f₁ (fst R M M₃)) (comp f₂ (snd R M M₃))

@[simp] theorem coe_prod_map {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] {M₃ : Type u_4} [topological_space M₃] [add_comm_monoid M₃] {M₄ : Type u_5} [topological_space M₄] [add_comm_monoid M₄] [semimodule R M] [semimodule R M₂] [semimodule R M₃] [semimodule R M₄] (f₁ : continuous_linear_map R M M₂) (f₂ : continuous_linear_map R M₃ M₄) : ↑(prod_map f₁ f₂) = linear_map.prod_map ↑f₁ ↑f₂ :=
  rfl

@[simp] theorem coe_prod_map' {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] {M₃ : Type u_4} [topological_space M₃] [add_comm_monoid M₃] {M₄ : Type u_5} [topological_space M₄] [add_comm_monoid M₄] [semimodule R M] [semimodule R M₂] [semimodule R M₃] [semimodule R M₄] (f₁ : continuous_linear_map R M M₂) (f₂ : continuous_linear_map R M₃ M₄) : ⇑(prod_map f₁ f₂) = prod.map ⇑f₁ ⇑f₂ :=
  rfl

/-- The continuous linear map given by `(x, y) ↦ f₁ x + f₂ y`. -/
def coprod {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] {M₃ : Type u_4} [topological_space M₃] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] [has_continuous_add M₃] (f₁ : continuous_linear_map R M M₃) (f₂ : continuous_linear_map R M₂ M₃) : continuous_linear_map R (M × M₂) M₃ :=
  mk (linear_map.coprod ↑f₁ ↑f₂)

@[simp] theorem coe_coprod {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] {M₃ : Type u_4} [topological_space M₃] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] [has_continuous_add M₃] (f₁ : continuous_linear_map R M M₃) (f₂ : continuous_linear_map R M₂ M₃) : ↑(coprod f₁ f₂) = linear_map.coprod ↑f₁ ↑f₂ :=
  rfl

@[simp] theorem coprod_apply {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] {M₃ : Type u_4} [topological_space M₃] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] [has_continuous_add M₃] (f₁ : continuous_linear_map R M M₃) (f₂ : continuous_linear_map R M₂ M₃) (x : M × M₂) : coe_fn (coprod f₁ f₂) x = coe_fn f₁ (prod.fst x) + coe_fn f₂ (prod.snd x) :=
  rfl

/-- The linear map `λ x, c x • f`.  Associates to a scalar-valued linear map and an element of
`M₂` the `M₂`-valued linear map obtained by multiplying the two (a.k.a. tensoring by `M₂`).
See also `continuous_linear_map.smul_rightₗ` and `continuous_linear_map.smul_rightL`. -/
def smul_right {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] [topological_space R] [topological_semimodule R M₂] (c : continuous_linear_map R M R) (f : M₂) : continuous_linear_map R M M₂ :=
  mk (linear_map.mk (linear_map.to_fun (linear_map.smul_right (to_linear_map c) f)) sorry sorry)

@[simp] theorem smul_right_apply {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] [topological_space R] [topological_semimodule R M₂] {c : continuous_linear_map R M R} {f : M₂} {x : M} : coe_fn (smul_right c f) x = coe_fn c x • f :=
  rfl

@[simp] theorem smul_right_one_one {R : Type u_1} [semiring R] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M₂] [topological_space R] [topological_semimodule R M₂] (c : continuous_linear_map R R M₂) : smul_right 1 (coe_fn c 1) = c := sorry

@[simp] theorem smul_right_one_eq_iff {R : Type u_1} [semiring R] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M₂] [topological_space R] [topological_semimodule R M₂] {f : M₂} {f' : M₂} : smul_right 1 f = smul_right 1 f' ↔ f = f' := sorry

theorem smul_right_comp {R : Type u_1} [semiring R] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M₂] [topological_space R] [topological_semimodule R M₂] [topological_semimodule R R] {x : M₂} {c : R} : comp (smul_right 1 x) (smul_right 1 c) = smul_right 1 (c • x) := sorry

/-- `pi` construction for continuous linear functions. From a family of continuous linear functions
it produces a continuous linear function into a family of topological modules. -/
def pi {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] [semimodule R M] {ι : Type u_4} {φ : ι → Type u_5} [(i : ι) → topological_space (φ i)] [(i : ι) → add_comm_monoid (φ i)] [(i : ι) → semimodule R (φ i)] (f : (i : ι) → continuous_linear_map R M (φ i)) : continuous_linear_map R M ((i : ι) → φ i) :=
  mk (linear_map.pi fun (i : ι) => ↑(f i))

@[simp] theorem pi_apply {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] [semimodule R M] {ι : Type u_4} {φ : ι → Type u_5} [(i : ι) → topological_space (φ i)] [(i : ι) → add_comm_monoid (φ i)] [(i : ι) → semimodule R (φ i)] (f : (i : ι) → continuous_linear_map R M (φ i)) (c : M) (i : ι) : coe_fn (pi f) c i = coe_fn (f i) c :=
  rfl

theorem pi_eq_zero {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] [semimodule R M] {ι : Type u_4} {φ : ι → Type u_5} [(i : ι) → topological_space (φ i)] [(i : ι) → add_comm_monoid (φ i)] [(i : ι) → semimodule R (φ i)] (f : (i : ι) → continuous_linear_map R M (φ i)) : pi f = 0 ↔ ∀ (i : ι), f i = 0 := sorry

theorem pi_zero {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] [semimodule R M] {ι : Type u_4} {φ : ι → Type u_5} [(i : ι) → topological_space (φ i)] [(i : ι) → add_comm_monoid (φ i)] [(i : ι) → semimodule R (φ i)] : (pi fun (i : ι) => 0) = 0 :=
  ext fun (x : M) => funext fun (x_1 : ι) => Eq.refl (coe_fn (pi fun (i : ι) => 0) x x_1)

theorem pi_comp {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] [semimodule R M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M₂] {ι : Type u_4} {φ : ι → Type u_5} [(i : ι) → topological_space (φ i)] [(i : ι) → add_comm_monoid (φ i)] [(i : ι) → semimodule R (φ i)] (f : (i : ι) → continuous_linear_map R M (φ i)) (g : continuous_linear_map R M₂ M) : comp (pi f) g = pi fun (i : ι) => comp (f i) g :=
  rfl

/-- The projections from a family of topological modules are continuous linear maps. -/
def proj {R : Type u_1} [semiring R] {ι : Type u_4} {φ : ι → Type u_5} [(i : ι) → topological_space (φ i)] [(i : ι) → add_comm_monoid (φ i)] [(i : ι) → semimodule R (φ i)] (i : ι) : continuous_linear_map R ((i : ι) → φ i) (φ i) :=
  mk (linear_map.proj i)

@[simp] theorem proj_apply {R : Type u_1} [semiring R] {ι : Type u_4} {φ : ι → Type u_5} [(i : ι) → topological_space (φ i)] [(i : ι) → add_comm_monoid (φ i)] [(i : ι) → semimodule R (φ i)] (i : ι) (b : (i : ι) → φ i) : coe_fn (proj i) b = b i :=
  rfl

theorem proj_pi {R : Type u_1} [semiring R] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M₂] {ι : Type u_4} {φ : ι → Type u_5} [(i : ι) → topological_space (φ i)] [(i : ι) → add_comm_monoid (φ i)] [(i : ι) → semimodule R (φ i)] (f : (i : ι) → continuous_linear_map R M₂ (φ i)) (i : ι) : comp (proj i) (pi f) = f i :=
  ext fun (c : M₂) => rfl

theorem infi_ker_proj {R : Type u_1} [semiring R] {ι : Type u_4} {φ : ι → Type u_5} [(i : ι) → topological_space (φ i)] [(i : ι) → add_comm_monoid (φ i)] [(i : ι) → semimodule R (φ i)] : (infi fun (i : ι) => ker (proj i)) = ⊥ :=
  linear_map.infi_ker_proj

/-- If `I` and `J` are complementary index sets, the product of the kernels of the `J`th projections of
`φ` is linearly equivalent to the product over `I`. -/
def infi_ker_proj_equiv (R : Type u_1) [semiring R] {ι : Type u_4} (φ : ι → Type u_5) [(i : ι) → topological_space (φ i)] [(i : ι) → add_comm_monoid (φ i)] [(i : ι) → semimodule R (φ i)] {I : set ι} {J : set ι} [decidable_pred fun (i : ι) => i ∈ I] (hd : disjoint I J) (hu : set.univ ⊆ I ∪ J) : continuous_linear_equiv R (↥(infi fun (i : ι) => infi fun (H : i ∈ J) => ker (proj i))) ((i : ↥I) → φ ↑i) :=
  continuous_linear_equiv.mk (linear_map.infi_ker_proj_equiv R φ hd hu)

@[simp] theorem map_neg {R : Type u_1} [ring R] {M : Type u_2} [topological_space M] [add_comm_group M] {M₂ : Type u_3} [topological_space M₂] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] (f : continuous_linear_map R M M₂) (x : M) : coe_fn f (-x) = -coe_fn f x :=
  linear_map.map_neg (to_linear_map f) x

@[simp] theorem map_sub {R : Type u_1} [ring R] {M : Type u_2} [topological_space M] [add_comm_group M] {M₂ : Type u_3} [topological_space M₂] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] (f : continuous_linear_map R M M₂) (x : M) (y : M) : coe_fn f (x - y) = coe_fn f x - coe_fn f y :=
  linear_map.map_sub (to_linear_map f) x y

@[simp] theorem sub_apply' {R : Type u_1} [ring R] {M : Type u_2} [topological_space M] [add_comm_group M] {M₂ : Type u_3} [topological_space M₂] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] (f : continuous_linear_map R M M₂) (g : continuous_linear_map R M M₂) (x : M) : coe_fn (↑f - ↑g) x = coe_fn f x - coe_fn g x :=
  rfl

theorem range_prod_eq {R : Type u_1} [ring R] {M : Type u_2} [topological_space M] [add_comm_group M] {M₂ : Type u_3} [topological_space M₂] [add_comm_group M₂] {M₃ : Type u_4} [topological_space M₃] [add_comm_group M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] {f : continuous_linear_map R M M₂} {g : continuous_linear_map R M M₃} (h : ker f ⊔ ker g = ⊤) : range (continuous_linear_map.prod f g) = submodule.prod (range f) (range g) :=
  linear_map.range_prod_eq h

protected instance has_neg {R : Type u_1} [ring R] {M : Type u_2} [topological_space M] [add_comm_group M] {M₂ : Type u_3} [topological_space M₂] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] [topological_add_group M₂] : Neg (continuous_linear_map R M M₂) :=
  { neg := fun (f : continuous_linear_map R M M₂) => mk (-↑f) }

@[simp] theorem neg_apply {R : Type u_1} [ring R] {M : Type u_2} [topological_space M] [add_comm_group M] {M₂ : Type u_3} [topological_space M₂] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] (f : continuous_linear_map R M M₂) (x : M) [topological_add_group M₂] : coe_fn (-f) x = -coe_fn f x :=
  rfl

@[simp] theorem coe_neg {R : Type u_1} [ring R] {M : Type u_2} [topological_space M] [add_comm_group M] {M₂ : Type u_3} [topological_space M₂] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] (f : continuous_linear_map R M M₂) [topological_add_group M₂] : ↑(-f) = -↑f :=
  rfl

theorem coe_neg' {R : Type u_1} [ring R] {M : Type u_2} [topological_space M] [add_comm_group M] {M₂ : Type u_3} [topological_space M₂] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] (f : continuous_linear_map R M M₂) [topological_add_group M₂] : ⇑(-f) = -⇑f :=
  rfl

protected instance has_sub {R : Type u_1} [ring R] {M : Type u_2} [topological_space M] [add_comm_group M] {M₂ : Type u_3} [topological_space M₂] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] [topological_add_group M₂] : Sub (continuous_linear_map R M M₂) :=
  { sub := fun (f g : continuous_linear_map R M M₂) => mk (↑f - ↑g) }

protected instance add_comm_group {R : Type u_1} [ring R] {M : Type u_2} [topological_space M] [add_comm_group M] {M₂ : Type u_3} [topological_space M₂] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] [topological_add_group M₂] : add_comm_group (continuous_linear_map R M M₂) :=
  add_comm_group.mk Add.add sorry 0 sorry sorry Neg.neg Sub.sub sorry sorry

theorem sub_apply {R : Type u_1} [ring R] {M : Type u_2} [topological_space M] [add_comm_group M] {M₂ : Type u_3} [topological_space M₂] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] (f : continuous_linear_map R M M₂) (g : continuous_linear_map R M M₂) [topological_add_group M₂] (x : M) : coe_fn (f - g) x = coe_fn f x - coe_fn g x :=
  rfl

@[simp] theorem coe_sub {R : Type u_1} [ring R] {M : Type u_2} [topological_space M] [add_comm_group M] {M₂ : Type u_3} [topological_space M₂] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] (f : continuous_linear_map R M M₂) (g : continuous_linear_map R M M₂) [topological_add_group M₂] : ↑(f - g) = ↑f - ↑g :=
  rfl

@[simp] theorem coe_sub' {R : Type u_1} [ring R] {M : Type u_2} [topological_space M] [add_comm_group M] {M₂ : Type u_3} [topological_space M₂] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] (f : continuous_linear_map R M M₂) (g : continuous_linear_map R M M₂) [topological_add_group M₂] : ⇑(f - g) = ⇑f - ⇑g :=
  rfl

protected instance ring {R : Type u_1} [ring R] {M : Type u_2} [topological_space M] [add_comm_group M] [semimodule R M] [topological_add_group M] : ring (continuous_linear_map R M M) :=
  ring.mk add_comm_group.add sorry add_comm_group.zero sorry sorry add_comm_group.neg add_comm_group.sub sorry sorry
    Mul.mul sorry 1 sorry sorry sorry sorry

theorem smul_right_one_pow {R : Type u_1} [ring R] [topological_space R] [topological_add_group R] [topological_semimodule R R] (c : R) (n : ℕ) : smul_right 1 c ^ n = smul_right 1 (c ^ n) := sorry

/-- Given a right inverse `f₂ : M₂ →L[R] M` to `f₁ : M →L[R] M₂`,
`proj_ker_of_right_inverse f₁ f₂ h` is the projection `M →L[R] f₁.ker` along `f₂.range`. -/
def proj_ker_of_right_inverse {R : Type u_1} [ring R] {M : Type u_2} [topological_space M] [add_comm_group M] {M₂ : Type u_3} [topological_space M₂] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] [topological_add_group M] (f₁ : continuous_linear_map R M M₂) (f₂ : continuous_linear_map R M₂ M) (h : function.right_inverse ⇑f₂ ⇑f₁) : continuous_linear_map R M ↥(ker f₁) :=
  cod_restrict (id R M - comp f₂ f₁) (ker f₁) sorry

@[simp] theorem coe_proj_ker_of_right_inverse_apply {R : Type u_1} [ring R] {M : Type u_2} [topological_space M] [add_comm_group M] {M₂ : Type u_3} [topological_space M₂] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] [topological_add_group M] (f₁ : continuous_linear_map R M M₂) (f₂ : continuous_linear_map R M₂ M) (h : function.right_inverse ⇑f₂ ⇑f₁) (x : M) : ↑(coe_fn (proj_ker_of_right_inverse f₁ f₂ h) x) = x - coe_fn f₂ (coe_fn f₁ x) :=
  rfl

@[simp] theorem proj_ker_of_right_inverse_apply_idem {R : Type u_1} [ring R] {M : Type u_2} [topological_space M] [add_comm_group M] {M₂ : Type u_3} [topological_space M₂] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] [topological_add_group M] (f₁ : continuous_linear_map R M M₂) (f₂ : continuous_linear_map R M₂ M) (h : function.right_inverse ⇑f₂ ⇑f₁) (x : ↥(ker f₁)) : coe_fn (proj_ker_of_right_inverse f₁ f₂ h) ↑x = x := sorry

@[simp] theorem proj_ker_of_right_inverse_comp_inv {R : Type u_1} [ring R] {M : Type u_2} [topological_space M] [add_comm_group M] {M₂ : Type u_3} [topological_space M₂] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] [topological_add_group M] (f₁ : continuous_linear_map R M M₂) (f₂ : continuous_linear_map R M₂ M) (h : function.right_inverse ⇑f₂ ⇑f₁) (y : M₂) : coe_fn (proj_ker_of_right_inverse f₁ f₂ h) (coe_fn f₂ y) = 0 := sorry

protected instance has_scalar {R : Type u_1} [comm_ring R] [topological_space R] {M : Type u_2} [topological_space M] [add_comm_group M] {M₃ : Type u_4} [topological_space M₃] [add_comm_group M₃] [module R M] [module R M₃] [topological_module R M₃] : has_scalar R (continuous_linear_map R M M₃) :=
  has_scalar.mk fun (c : R) (f : continuous_linear_map R M M₃) => mk (c • ↑f)

@[simp] theorem smul_comp {R : Type u_1} [comm_ring R] [topological_space R] {M : Type u_2} [topological_space M] [add_comm_group M] {M₂ : Type u_3} [topological_space M₂] [add_comm_group M₂] {M₃ : Type u_4} [topological_space M₃] [add_comm_group M₃] [module R M] [module R M₂] [module R M₃] [topological_module R M₃] (c : R) (h : continuous_linear_map R M₂ M₃) (f : continuous_linear_map R M M₂) : comp (c • h) f = c • comp h f :=
  rfl

@[simp] theorem smul_apply {R : Type u_1} [comm_ring R] [topological_space R] {M : Type u_2} [topological_space M] [add_comm_group M] {M₂ : Type u_3} [topological_space M₂] [add_comm_group M₂] [module R M] [module R M₂] (c : R) (f : continuous_linear_map R M M₂) (x : M) [topological_module R M₂] : coe_fn (c • f) x = c • coe_fn f x :=
  rfl

@[simp] theorem coe_apply {R : Type u_1} [comm_ring R] [topological_space R] {M : Type u_2} [topological_space M] [add_comm_group M] {M₂ : Type u_3} [topological_space M₂] [add_comm_group M₂] [module R M] [module R M₂] (c : R) (f : continuous_linear_map R M M₂) [topological_module R M₂] : ↑(c • f) = c • ↑f :=
  rfl

theorem coe_apply' {R : Type u_1} [comm_ring R] [topological_space R] {M : Type u_2} [topological_space M] [add_comm_group M] {M₂ : Type u_3} [topological_space M₂] [add_comm_group M₂] [module R M] [module R M₂] (c : R) (f : continuous_linear_map R M M₂) [topological_module R M₂] : ⇑(c • f) = c • ⇑f :=
  rfl

@[simp] theorem comp_smul {R : Type u_1} [comm_ring R] [topological_space R] {M : Type u_2} [topological_space M] [add_comm_group M] {M₂ : Type u_3} [topological_space M₂] [add_comm_group M₂] {M₃ : Type u_4} [topological_space M₃] [add_comm_group M₃] [module R M] [module R M₂] [module R M₃] [topological_module R M₃] (c : R) (h : continuous_linear_map R M₂ M₃) (f : continuous_linear_map R M M₂) [topological_module R M₂] : comp h (c • f) = c • comp h f := sorry

protected instance module {R : Type u_1} [comm_ring R] [topological_space R] {M : Type u_2} [topological_space M] [add_comm_group M] {M₂ : Type u_3} [topological_space M₂] [add_comm_group M₂] [module R M] [module R M₂] [topological_module R M₂] [topological_add_group M₂] : module R (continuous_linear_map R M M₂) :=
  semimodule.mk sorry sorry

protected instance algebra {R : Type u_1} [comm_ring R] [topological_space R] {M₂ : Type u_3} [topological_space M₂] [add_comm_group M₂] [module R M₂] [topological_module R M₂] [topological_add_group M₂] : algebra R (continuous_linear_map R M₂ M₂) :=
  algebra.of_semimodule' sorry sorry

/-- Given `c : E →L[𝕜] 𝕜`, `c.smul_rightₗ` is the linear map from `F` to `E →L[𝕜] F`
sending `f` to `λ e, c e • f`. See also `continuous_linear_map.smul_rightL`. -/
def smul_rightₗ {R : Type u_1} [comm_ring R] [topological_space R] {M : Type u_2} [topological_space M] [add_comm_group M] {M₂ : Type u_3} [topological_space M₂] [add_comm_group M₂] [module R M] [module R M₂] [topological_module R M₂] [topological_add_group M₂] (c : continuous_linear_map R M R) : linear_map R M₂ (continuous_linear_map R M M₂) :=
  linear_map.mk (smul_right c) sorry sorry

end continuous_linear_map


namespace continuous_linear_equiv


/-- A continuous linear equivalence induces a continuous linear map. -/
def to_continuous_linear_map {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (e : continuous_linear_equiv R M M₂) : continuous_linear_map R M M₂ :=
  continuous_linear_map.mk
    (linear_map.mk (linear_map.to_fun (linear_equiv.to_linear_map (to_linear_equiv e))) sorry sorry)

/-- Coerce continuous linear equivs to continuous linear maps. -/
protected instance continuous_linear_map.has_coe {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : has_coe (continuous_linear_equiv R M M₂) (continuous_linear_map R M M₂) :=
  has_coe.mk to_continuous_linear_map

/-- Coerce continuous linear equivs to maps. -/
-- see Note [function coercion]

protected instance has_coe_to_fun {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : has_coe_to_fun (continuous_linear_equiv R M M₂) :=
  has_coe_to_fun.mk (fun (_x : continuous_linear_equiv R M M₂) => M → M₂) fun (f : continuous_linear_equiv R M M₂) => ⇑f

@[simp] theorem coe_def_rev {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (e : continuous_linear_equiv R M M₂) : to_continuous_linear_map e = ↑e :=
  rfl

@[simp] theorem coe_apply {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (e : continuous_linear_equiv R M M₂) (b : M) : coe_fn (↑e) b = coe_fn e b :=
  rfl

@[simp] theorem coe_to_linear_equiv {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : continuous_linear_equiv R M M₂) : ⇑(to_linear_equiv f) = ⇑f :=
  rfl

theorem coe_coe {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (e : continuous_linear_equiv R M M₂) : ⇑↑e = ⇑e :=
  rfl

theorem ext {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {f : continuous_linear_equiv R M M₂} {g : continuous_linear_equiv R M M₂} (h : ⇑f = ⇑g) : f = g := sorry

/-- A continuous linear equivalence induces a homeomorphism. -/
def to_homeomorph {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (e : continuous_linear_equiv R M M₂) : M ≃ₜ M₂ :=
  homeomorph.mk
    (equiv.mk (linear_equiv.to_fun (to_linear_equiv e)) (linear_equiv.inv_fun (to_linear_equiv e)) sorry sorry)

-- Make some straightforward lemmas available to `simp`.

@[simp] theorem map_zero {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (e : continuous_linear_equiv R M M₂) : coe_fn e 0 = 0 :=
  continuous_linear_map.map_zero ↑e

@[simp] theorem map_add {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (e : continuous_linear_equiv R M M₂) (x : M) (y : M) : coe_fn e (x + y) = coe_fn e x + coe_fn e y :=
  continuous_linear_map.map_add (↑e) x y

@[simp] theorem map_smul {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (e : continuous_linear_equiv R M M₂) (c : R) (x : M) : coe_fn e (c • x) = c • coe_fn e x :=
  continuous_linear_map.map_smul c (↑e) x

@[simp] theorem map_eq_zero_iff {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (e : continuous_linear_equiv R M M₂) {x : M} : coe_fn e x = 0 ↔ x = 0 :=
  linear_equiv.map_eq_zero_iff (to_linear_equiv e)

protected theorem continuous {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (e : continuous_linear_equiv R M M₂) : continuous ⇑e :=
  continuous_to_fun e

protected theorem continuous_on {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (e : continuous_linear_equiv R M M₂) {s : set M} : continuous_on (⇑e) s :=
  continuous.continuous_on (continuous_linear_equiv.continuous e)

protected theorem continuous_at {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (e : continuous_linear_equiv R M M₂) {x : M} : continuous_at (⇑e) x :=
  continuous.continuous_at (continuous_linear_equiv.continuous e)

protected theorem continuous_within_at {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (e : continuous_linear_equiv R M M₂) {s : set M} {x : M} : continuous_within_at (⇑e) s x :=
  continuous.continuous_within_at (continuous_linear_equiv.continuous e)

theorem comp_continuous_on_iff {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {α : Type u_4} [topological_space α] (e : continuous_linear_equiv R M M₂) {f : α → M} {s : set α} : continuous_on (⇑e ∘ f) s ↔ continuous_on f s :=
  homeomorph.comp_continuous_on_iff (to_homeomorph e) f s

theorem comp_continuous_iff {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {α : Type u_4} [topological_space α] (e : continuous_linear_equiv R M M₂) {f : α → M} : continuous (⇑e ∘ f) ↔ continuous f :=
  homeomorph.comp_continuous_iff (to_homeomorph e)

/-- An extensionality lemma for `R ≃L[R] M`. -/
theorem ext₁ {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] [semimodule R M] [topological_space R] {f : continuous_linear_equiv R R M} {g : continuous_linear_equiv R R M} (h : coe_fn f 1 = coe_fn g 1) : f = g := sorry

/-- The identity map as a continuous linear equivalence. -/
protected def refl (R : Type u_1) [semiring R] (M : Type u_2) [topological_space M] [add_comm_monoid M] [semimodule R M] : continuous_linear_equiv R M M :=
  mk
    (linear_equiv.mk (linear_equiv.to_fun (linear_equiv.refl R M)) sorry sorry
      (linear_equiv.inv_fun (linear_equiv.refl R M)) sorry sorry)

@[simp] theorem coe_refl {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] [semimodule R M] : ↑(continuous_linear_equiv.refl R M) = continuous_linear_map.id R M :=
  rfl

@[simp] theorem coe_refl' {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] [semimodule R M] : ⇑(continuous_linear_equiv.refl R M) = id :=
  rfl

/-- The inverse of a continuous linear equivalence as a continuous linear equivalence-/
protected def symm {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (e : continuous_linear_equiv R M M₂) : continuous_linear_equiv R M₂ M :=
  mk
    (linear_equiv.mk (linear_equiv.to_fun (linear_equiv.symm (to_linear_equiv e))) sorry sorry
      (linear_equiv.inv_fun (linear_equiv.symm (to_linear_equiv e))) sorry sorry)

@[simp] theorem symm_to_linear_equiv {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (e : continuous_linear_equiv R M M₂) : to_linear_equiv (continuous_linear_equiv.symm e) = linear_equiv.symm (to_linear_equiv e) :=
  linear_equiv.ext fun (x : M₂) => Eq.refl (coe_fn (to_linear_equiv (continuous_linear_equiv.symm e)) x)

/-- The composition of two continuous linear equivalences as a continuous linear equivalence. -/
protected def trans {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] {M₃ : Type u_4} [topological_space M₃] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (e₁ : continuous_linear_equiv R M M₂) (e₂ : continuous_linear_equiv R M₂ M₃) : continuous_linear_equiv R M M₃ :=
  mk
    (linear_equiv.mk (linear_equiv.to_fun (linear_equiv.trans (to_linear_equiv e₁) (to_linear_equiv e₂))) sorry sorry
      (linear_equiv.inv_fun (linear_equiv.trans (to_linear_equiv e₁) (to_linear_equiv e₂))) sorry sorry)

@[simp] theorem trans_to_linear_equiv {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] {M₃ : Type u_4} [topological_space M₃] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (e₁ : continuous_linear_equiv R M M₂) (e₂ : continuous_linear_equiv R M₂ M₃) : to_linear_equiv (continuous_linear_equiv.trans e₁ e₂) = linear_equiv.trans (to_linear_equiv e₁) (to_linear_equiv e₂) :=
  linear_equiv.ext fun (x : M) => Eq.refl (coe_fn (to_linear_equiv (continuous_linear_equiv.trans e₁ e₂)) x)

/-- Product of two continuous linear equivalences. The map comes from `equiv.prod_congr`. -/
def prod {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] {M₃ : Type u_4} [topological_space M₃] [add_comm_monoid M₃] {M₄ : Type u_5} [topological_space M₄] [add_comm_monoid M₄] [semimodule R M] [semimodule R M₂] [semimodule R M₃] [semimodule R M₄] (e : continuous_linear_equiv R M M₂) (e' : continuous_linear_equiv R M₃ M₄) : continuous_linear_equiv R (M × M₃) (M₂ × M₄) :=
  mk
    (linear_equiv.mk (linear_equiv.to_fun (linear_equiv.prod (to_linear_equiv e) (to_linear_equiv e'))) sorry sorry
      (linear_equiv.inv_fun (linear_equiv.prod (to_linear_equiv e) (to_linear_equiv e'))) sorry sorry)

@[simp] theorem prod_apply {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] {M₃ : Type u_4} [topological_space M₃] [add_comm_monoid M₃] {M₄ : Type u_5} [topological_space M₄] [add_comm_monoid M₄] [semimodule R M] [semimodule R M₂] [semimodule R M₃] [semimodule R M₄] (e : continuous_linear_equiv R M M₂) (e' : continuous_linear_equiv R M₃ M₄) (x : M × M₃) : coe_fn (prod e e') x = (coe_fn e (prod.fst x), coe_fn e' (prod.snd x)) :=
  rfl

@[simp] theorem coe_prod {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] {M₃ : Type u_4} [topological_space M₃] [add_comm_monoid M₃] {M₄ : Type u_5} [topological_space M₄] [add_comm_monoid M₄] [semimodule R M] [semimodule R M₂] [semimodule R M₃] [semimodule R M₄] (e : continuous_linear_equiv R M M₂) (e' : continuous_linear_equiv R M₃ M₄) : ↑(prod e e') = continuous_linear_map.prod_map ↑e ↑e' :=
  rfl

theorem bijective {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (e : continuous_linear_equiv R M M₂) : function.bijective ⇑e :=
  equiv.bijective (linear_equiv.to_equiv (to_linear_equiv e))

theorem injective {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (e : continuous_linear_equiv R M M₂) : function.injective ⇑e :=
  equiv.injective (linear_equiv.to_equiv (to_linear_equiv e))

theorem surjective {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (e : continuous_linear_equiv R M M₂) : function.surjective ⇑e :=
  equiv.surjective (linear_equiv.to_equiv (to_linear_equiv e))

@[simp] theorem trans_apply {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] {M₃ : Type u_4} [topological_space M₃] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (e₁ : continuous_linear_equiv R M M₂) (e₂ : continuous_linear_equiv R M₂ M₃) (c : M) : coe_fn (continuous_linear_equiv.trans e₁ e₂) c = coe_fn e₂ (coe_fn e₁ c) :=
  rfl

@[simp] theorem apply_symm_apply {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (e : continuous_linear_equiv R M M₂) (c : M₂) : coe_fn e (coe_fn (continuous_linear_equiv.symm e) c) = c :=
  linear_equiv.right_inv (to_linear_equiv e) c

@[simp] theorem symm_apply_apply {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (e : continuous_linear_equiv R M M₂) (b : M) : coe_fn (continuous_linear_equiv.symm e) (coe_fn e b) = b :=
  linear_equiv.left_inv (to_linear_equiv e) b

@[simp] theorem symm_trans_apply {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] {M₃ : Type u_4} [topological_space M₃] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (e₁ : continuous_linear_equiv R M₂ M) (e₂ : continuous_linear_equiv R M₃ M₂) (c : M) : coe_fn (continuous_linear_equiv.symm (continuous_linear_equiv.trans e₂ e₁)) c =
  coe_fn (continuous_linear_equiv.symm e₂) (coe_fn (continuous_linear_equiv.symm e₁) c) :=
  rfl

@[simp] theorem comp_coe {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] {M₃ : Type u_4} [topological_space M₃] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (f : continuous_linear_equiv R M M₂) (f' : continuous_linear_equiv R M₂ M₃) : continuous_linear_map.comp ↑f' ↑f = ↑(continuous_linear_equiv.trans f f') :=
  rfl

@[simp] theorem coe_comp_coe_symm {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (e : continuous_linear_equiv R M M₂) : continuous_linear_map.comp ↑e ↑(continuous_linear_equiv.symm e) = continuous_linear_map.id R M₂ :=
  continuous_linear_map.ext (apply_symm_apply e)

@[simp] theorem coe_symm_comp_coe {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (e : continuous_linear_equiv R M M₂) : continuous_linear_map.comp ↑(continuous_linear_equiv.symm e) ↑e = continuous_linear_map.id R M :=
  continuous_linear_map.ext (symm_apply_apply e)

theorem symm_comp_self {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (e : continuous_linear_equiv R M M₂) : ⇑(continuous_linear_equiv.symm e) ∘ ⇑e = id :=
  funext fun (x : M) => symm_apply_apply e x

theorem self_comp_symm {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (e : continuous_linear_equiv R M M₂) : ⇑e ∘ ⇑(continuous_linear_equiv.symm e) = id :=
  funext fun (x : M₂) => apply_symm_apply e x

@[simp] theorem symm_comp_self' {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (e : continuous_linear_equiv R M M₂) : ⇑↑(continuous_linear_equiv.symm e) ∘ ⇑↑e = id :=
  symm_comp_self e

@[simp] theorem self_comp_symm' {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (e : continuous_linear_equiv R M M₂) : ⇑↑e ∘ ⇑↑(continuous_linear_equiv.symm e) = id :=
  self_comp_symm e

@[simp] theorem symm_symm {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (e : continuous_linear_equiv R M M₂) : continuous_linear_equiv.symm (continuous_linear_equiv.symm e) = e :=
  ext (funext fun (x : M) => Eq.refl (coe_fn (continuous_linear_equiv.symm (continuous_linear_equiv.symm e)) x))

@[simp] theorem refl_symm {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] [semimodule R M] : continuous_linear_equiv.symm (continuous_linear_equiv.refl R M) = continuous_linear_equiv.refl R M :=
  rfl

theorem symm_symm_apply {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (e : continuous_linear_equiv R M M₂) (x : M) : coe_fn (continuous_linear_equiv.symm (continuous_linear_equiv.symm e)) x = coe_fn e x :=
  rfl

theorem symm_apply_eq {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (e : continuous_linear_equiv R M M₂) {x : M₂} {y : M} : coe_fn (continuous_linear_equiv.symm e) x = y ↔ x = coe_fn e y :=
  linear_equiv.symm_apply_eq (to_linear_equiv e)

theorem eq_symm_apply {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (e : continuous_linear_equiv R M M₂) {x : M₂} {y : M} : y = coe_fn (continuous_linear_equiv.symm e) x ↔ coe_fn e y = x :=
  linear_equiv.eq_symm_apply (to_linear_equiv e)

/-- Create a `continuous_linear_equiv` from two `continuous_linear_map`s that are
inverse of each other. -/
def equiv_of_inverse {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f₁ : continuous_linear_map R M M₂) (f₂ : continuous_linear_map R M₂ M) (h₁ : function.left_inverse ⇑f₂ ⇑f₁) (h₂ : function.right_inverse ⇑f₂ ⇑f₁) : continuous_linear_equiv R M M₂ :=
  mk (linear_equiv.mk ⇑f₁ sorry sorry (⇑f₂) h₁ h₂)

@[simp] theorem equiv_of_inverse_apply {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f₁ : continuous_linear_map R M M₂) (f₂ : continuous_linear_map R M₂ M) (h₁ : function.left_inverse ⇑f₂ ⇑f₁) (h₂ : function.right_inverse ⇑f₂ ⇑f₁) (x : M) : coe_fn (equiv_of_inverse f₁ f₂ h₁ h₂) x = coe_fn f₁ x :=
  rfl

@[simp] theorem symm_equiv_of_inverse {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_monoid M] {M₂ : Type u_3} [topological_space M₂] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f₁ : continuous_linear_map R M M₂) (f₂ : continuous_linear_map R M₂ M) (h₁ : function.left_inverse ⇑f₂ ⇑f₁) (h₂ : function.right_inverse ⇑f₂ ⇑f₁) : continuous_linear_equiv.symm (equiv_of_inverse f₁ f₂ h₁ h₂) = equiv_of_inverse f₂ f₁ h₂ h₁ :=
  rfl

/-- The continuous linear equivalences from `M` to itself form a group under composition. -/
protected instance automorphism_group {R : Type u_1} [semiring R] (M : Type u_2) [topological_space M] [add_comm_monoid M] [semimodule R M] : group (continuous_linear_equiv R M M) :=
  group.mk (fun (f g : continuous_linear_equiv R M M) => continuous_linear_equiv.trans g f) sorry
    (continuous_linear_equiv.refl R M) sorry sorry
    (fun (f : continuous_linear_equiv R M M) => continuous_linear_equiv.symm f)
    (div_inv_monoid.div._default (fun (f g : continuous_linear_equiv R M M) => continuous_linear_equiv.trans g f) sorry
      (continuous_linear_equiv.refl R M) sorry sorry
      fun (f : continuous_linear_equiv R M M) => continuous_linear_equiv.symm f)
    sorry

/-- Equivalence given by a block lower diagonal matrix. `e` and `e'` are diagonal square blocks,
  and `f` is a rectangular block below the diagonal. -/
def skew_prod {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_group M] {M₂ : Type u_3} [topological_space M₂] [add_comm_group M₂] {M₃ : Type u_4} [topological_space M₃] [add_comm_group M₃] {M₄ : Type u_5} [topological_space M₄] [add_comm_group M₄] [semimodule R M] [semimodule R M₂] [semimodule R M₃] [semimodule R M₄] [topological_add_group M₄] (e : continuous_linear_equiv R M M₂) (e' : continuous_linear_equiv R M₃ M₄) (f : continuous_linear_map R M M₄) : continuous_linear_equiv R (M × M₃) (M₂ × M₄) :=
  mk
    (linear_equiv.mk (linear_equiv.to_fun (linear_equiv.skew_prod (to_linear_equiv e) (to_linear_equiv e') ↑f)) sorry
      sorry (linear_equiv.inv_fun (linear_equiv.skew_prod (to_linear_equiv e) (to_linear_equiv e') ↑f)) sorry sorry)

@[simp] theorem skew_prod_apply {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_group M] {M₂ : Type u_3} [topological_space M₂] [add_comm_group M₂] {M₃ : Type u_4} [topological_space M₃] [add_comm_group M₃] {M₄ : Type u_5} [topological_space M₄] [add_comm_group M₄] [semimodule R M] [semimodule R M₂] [semimodule R M₃] [semimodule R M₄] [topological_add_group M₄] (e : continuous_linear_equiv R M M₂) (e' : continuous_linear_equiv R M₃ M₄) (f : continuous_linear_map R M M₄) (x : M × M₃) : coe_fn (skew_prod e e' f) x = (coe_fn e (prod.fst x), coe_fn e' (prod.snd x) + coe_fn f (prod.fst x)) :=
  rfl

@[simp] theorem skew_prod_symm_apply {R : Type u_1} [semiring R] {M : Type u_2} [topological_space M] [add_comm_group M] {M₂ : Type u_3} [topological_space M₂] [add_comm_group M₂] {M₃ : Type u_4} [topological_space M₃] [add_comm_group M₃] {M₄ : Type u_5} [topological_space M₄] [add_comm_group M₄] [semimodule R M] [semimodule R M₂] [semimodule R M₃] [semimodule R M₄] [topological_add_group M₄] (e : continuous_linear_equiv R M M₂) (e' : continuous_linear_equiv R M₃ M₄) (f : continuous_linear_map R M M₄) (x : M₂ × M₄) : coe_fn (continuous_linear_equiv.symm (skew_prod e e' f)) x =
  (coe_fn (continuous_linear_equiv.symm e) (prod.fst x),
  coe_fn (continuous_linear_equiv.symm e')
    (prod.snd x - coe_fn f (coe_fn (continuous_linear_equiv.symm e) (prod.fst x)))) :=
  rfl

@[simp] theorem map_sub {R : Type u_1} [ring R] {M : Type u_2} [topological_space M] [add_comm_group M] [semimodule R M] {M₂ : Type u_3} [topological_space M₂] [add_comm_group M₂] [semimodule R M₂] (e : continuous_linear_equiv R M M₂) (x : M) (y : M) : coe_fn e (x - y) = coe_fn e x - coe_fn e y :=
  continuous_linear_map.map_sub (↑e) x y

@[simp] theorem map_neg {R : Type u_1} [ring R] {M : Type u_2} [topological_space M] [add_comm_group M] [semimodule R M] {M₂ : Type u_3} [topological_space M₂] [add_comm_group M₂] [semimodule R M₂] (e : continuous_linear_equiv R M M₂) (x : M) : coe_fn e (-x) = -coe_fn e x :=
  continuous_linear_map.map_neg (↑e) x

/-! The next theorems cover the identification between `M ≃L[𝕜] M`and the group of units of the ring
`M →L[R] M`. -/

/-- An invertible continuous linear map `f` determines a continuous equivalence from `M` to itself.
-/
def of_unit {R : Type u_1} [ring R] {M : Type u_2} [topological_space M] [add_comm_group M] [semimodule R M] [topological_add_group M] (f : units (continuous_linear_map R M M)) : continuous_linear_equiv R M M :=
  mk (linear_equiv.mk ⇑(units.val f) sorry sorry ⇑(units.inv f) sorry sorry)

/-- A continuous equivalence from `M` to itself determines an invertible continuous linear map. -/
def to_unit {R : Type u_1} [ring R] {M : Type u_2} [topological_space M] [add_comm_group M] [semimodule R M] [topological_add_group M] (f : continuous_linear_equiv R M M) : units (continuous_linear_map R M M) :=
  units.mk ↑f ↑(continuous_linear_equiv.symm f) sorry sorry

/-- The units of the algebra of continuous `R`-linear endomorphisms of `M` is multiplicatively
equivalent to the type of continuous linear equivalences between `M` and itself. -/
def units_equiv (R : Type u_1) [ring R] (M : Type u_2) [topological_space M] [add_comm_group M] [semimodule R M] [topological_add_group M] : units (continuous_linear_map R M M) ≃* continuous_linear_equiv R M M :=
  mul_equiv.mk of_unit to_unit sorry sorry sorry

@[simp] theorem units_equiv_apply (R : Type u_1) [ring R] (M : Type u_2) [topological_space M] [add_comm_group M] [semimodule R M] [topological_add_group M] (f : units (continuous_linear_map R M M)) (x : M) : coe_fn (coe_fn (units_equiv R M) f) x = coe_fn f x :=
  rfl

/-- Continuous linear equivalences `R ≃L[R] R` are enumerated by `units R`. -/
def units_equiv_aut (R : Type u_1) [ring R] [topological_space R] [topological_module R R] : units R ≃ continuous_linear_equiv R R R :=
  equiv.mk
    (fun (u : units R) =>
      equiv_of_inverse (continuous_linear_map.smul_right 1 ↑u) (continuous_linear_map.smul_right 1 ↑(u⁻¹)) sorry sorry)
    (fun (e : continuous_linear_equiv R R R) =>
      units.mk (coe_fn e 1) (coe_fn (continuous_linear_equiv.symm e) 1) sorry sorry)
    sorry sorry

@[simp] theorem units_equiv_aut_apply {R : Type u_1} [ring R] [topological_space R] [topological_module R R] (u : units R) (x : R) : coe_fn (coe_fn (units_equiv_aut R) u) x = x * ↑u :=
  rfl

@[simp] theorem units_equiv_aut_apply_symm {R : Type u_1} [ring R] [topological_space R] [topological_module R R] (u : units R) (x : R) : coe_fn (continuous_linear_equiv.symm (coe_fn (units_equiv_aut R) u)) x = x * ↑(u⁻¹) :=
  rfl

@[simp] theorem units_equiv_aut_symm_apply {R : Type u_1} [ring R] [topological_space R] [topological_module R R] (e : continuous_linear_equiv R R R) : ↑(coe_fn (equiv.symm (units_equiv_aut R)) e) = coe_fn e 1 :=
  rfl

/-- A pair of continuous linear maps such that `f₁ ∘ f₂ = id` generates a continuous
linear equivalence `e` between `M` and `M₂ × f₁.ker` such that `(e x).2 = x` for `x ∈ f₁.ker`,
`(e x).1 = f₁ x`, and `(e (f₂ y)).2 = 0`. The map is given by `e x = (f₁ x, x - f₂ (f₁ x))`. -/
def equiv_of_right_inverse {R : Type u_1} [ring R] {M : Type u_2} [topological_space M] [add_comm_group M] [semimodule R M] {M₂ : Type u_3} [topological_space M₂] [add_comm_group M₂] [semimodule R M₂] [topological_add_group M] (f₁ : continuous_linear_map R M M₂) (f₂ : continuous_linear_map R M₂ M) (h : function.right_inverse ⇑f₂ ⇑f₁) : continuous_linear_equiv R M (M₂ × ↥(continuous_linear_map.ker f₁)) :=
  equiv_of_inverse (continuous_linear_map.prod f₁ (continuous_linear_map.proj_ker_of_right_inverse f₁ f₂ h))
    (continuous_linear_map.coprod f₂ (continuous_linear_map.subtype_val (continuous_linear_map.ker f₁))) sorry sorry

@[simp] theorem fst_equiv_of_right_inverse {R : Type u_1} [ring R] {M : Type u_2} [topological_space M] [add_comm_group M] [semimodule R M] {M₂ : Type u_3} [topological_space M₂] [add_comm_group M₂] [semimodule R M₂] [topological_add_group M] (f₁ : continuous_linear_map R M M₂) (f₂ : continuous_linear_map R M₂ M) (h : function.right_inverse ⇑f₂ ⇑f₁) (x : M) : prod.fst (coe_fn (equiv_of_right_inverse f₁ f₂ h) x) = coe_fn f₁ x :=
  rfl

@[simp] theorem snd_equiv_of_right_inverse {R : Type u_1} [ring R] {M : Type u_2} [topological_space M] [add_comm_group M] [semimodule R M] {M₂ : Type u_3} [topological_space M₂] [add_comm_group M₂] [semimodule R M₂] [topological_add_group M] (f₁ : continuous_linear_map R M M₂) (f₂ : continuous_linear_map R M₂ M) (h : function.right_inverse ⇑f₂ ⇑f₁) (x : M) : ↑(prod.snd (coe_fn (equiv_of_right_inverse f₁ f₂ h) x)) = x - coe_fn f₂ (coe_fn f₁ x) :=
  rfl

@[simp] theorem equiv_of_right_inverse_symm_apply {R : Type u_1} [ring R] {M : Type u_2} [topological_space M] [add_comm_group M] [semimodule R M] {M₂ : Type u_3} [topological_space M₂] [add_comm_group M₂] [semimodule R M₂] [topological_add_group M] (f₁ : continuous_linear_map R M M₂) (f₂ : continuous_linear_map R M₂ M) (h : function.right_inverse ⇑f₂ ⇑f₁) (y : M₂ × ↥(continuous_linear_map.ker f₁)) : coe_fn (continuous_linear_equiv.symm (equiv_of_right_inverse f₁ f₂ h)) y = coe_fn f₂ (prod.fst y) + ↑(prod.snd y) :=
  rfl

end continuous_linear_equiv


namespace continuous_linear_map


/-- Introduce a function `inverse` from `M →L[R] M₂` to `M₂ →L[R] M`, which sends `f` to `f.symm` if
`f` is a continuous linear equivalence and to `0` otherwise.  This definition is somewhat ad hoc,
but one needs a fully (rather than partially) defined inverse function for some purposes, including
for calculus. -/
def inverse {R : Type u_1} {M : Type u_2} {M₂ : Type u_3} [topological_space M] [topological_space M₂] [semiring R] [add_comm_monoid M₂] [semimodule R M₂] [add_comm_monoid M] [semimodule R M] : continuous_linear_map R M M₂ → continuous_linear_map R M₂ M :=
  fun (f : continuous_linear_map R M M₂) =>
    dite (∃ (e : continuous_linear_equiv R M M₂), ↑e = f)
      (fun (h : ∃ (e : continuous_linear_equiv R M M₂), ↑e = f) => ↑(continuous_linear_equiv.symm (classical.some h)))
      fun (h : ¬∃ (e : continuous_linear_equiv R M M₂), ↑e = f) => 0

/-- By definition, if `f` is invertible then `inverse f = f.symm`. -/
@[simp] theorem inverse_equiv {R : Type u_1} {M : Type u_2} {M₂ : Type u_3} [topological_space M] [topological_space M₂] [semiring R] [add_comm_monoid M₂] [semimodule R M₂] [add_comm_monoid M] [semimodule R M] (e : continuous_linear_equiv R M M₂) : inverse ↑e = ↑(continuous_linear_equiv.symm e) := sorry

/-- By definition, if `f` is not invertible then `inverse f = 0`. -/
@[simp] theorem inverse_non_equiv {R : Type u_1} {M : Type u_2} {M₂ : Type u_3} [topological_space M] [topological_space M₂] [semiring R] [add_comm_monoid M₂] [semimodule R M₂] [add_comm_monoid M] [semimodule R M] (f : continuous_linear_map R M M₂) (h : ¬∃ (e' : continuous_linear_equiv R M M₂), ↑e' = f) : inverse f = 0 :=
  dif_neg h

@[simp] theorem ring_inverse_equiv {R : Type u_1} {M : Type u_2} [topological_space M] [ring R] [add_comm_group M] [topological_add_group M] [module R M] (e : continuous_linear_equiv R M M) : ring.inverse ↑e = inverse ↑e := sorry

/-- The function `continuous_linear_equiv.inverse` can be written in terms of `ring.inverse` for the
ring of self-maps of the domain. -/
theorem to_ring_inverse {R : Type u_1} {M : Type u_2} {M₂ : Type u_3} [topological_space M] [topological_space M₂] [ring R] [add_comm_group M] [topological_add_group M] [module R M] [add_comm_group M₂] [module R M₂] (e : continuous_linear_equiv R M M₂) (f : continuous_linear_map R M M₂) : inverse f = comp (ring.inverse (comp (↑(continuous_linear_equiv.symm e)) f)) ↑(continuous_linear_equiv.symm e) := sorry

theorem ring_inverse_eq_map_inverse {R : Type u_1} {M : Type u_2} [topological_space M] [ring R] [add_comm_group M] [topological_add_group M] [module R M] : ring.inverse = inverse := sorry

end continuous_linear_map


namespace submodule


/-- A submodule `p` is called *complemented* if there exists a continuous projection `M →ₗ[R] p`. -/
def closed_complemented {R : Type u_1} [ring R] {M : Type u_2} [topological_space M] [add_comm_group M] [module R M] (p : submodule R M)  :=
  ∃ (f : continuous_linear_map R M ↥p), ∀ (x : ↥p), coe_fn f ↑x = x

theorem closed_complemented.has_closed_complement {R : Type u_1} [ring R] {M : Type u_2} [topological_space M] [add_comm_group M] [module R M] {p : submodule R M} [t1_space ↥p] (h : closed_complemented p) : ∃ (q : submodule R M), ∃ (hq : is_closed ↑q), is_compl p q := sorry

protected theorem closed_complemented.is_closed {R : Type u_1} [ring R] {M : Type u_2} [topological_space M] [add_comm_group M] [module R M] [topological_add_group M] [t1_space M] {p : submodule R M} (h : closed_complemented p) : is_closed ↑p := sorry

@[simp] theorem closed_complemented_bot {R : Type u_1} [ring R] {M : Type u_2} [topological_space M] [add_comm_group M] [module R M] : closed_complemented ⊥ := sorry

@[simp] theorem closed_complemented_top {R : Type u_1} [ring R] {M : Type u_2} [topological_space M] [add_comm_group M] [module R M] : closed_complemented ⊤ := sorry

end submodule


theorem continuous_linear_map.closed_complemented_ker_of_right_inverse {R : Type u_1} [ring R] {M : Type u_2} [topological_space M] [add_comm_group M] {M₂ : Type u_3} [topological_space M₂] [add_comm_group M₂] [module R M] [module R M₂] [topological_add_group M] (f₁ : continuous_linear_map R M M₂) (f₂ : continuous_linear_map R M₂ M) (h : function.right_inverse ⇑f₂ ⇑f₁) : submodule.closed_complemented (continuous_linear_map.ker f₁) :=
  Exists.intro (continuous_linear_map.proj_ker_of_right_inverse f₁ f₂ h)
    (continuous_linear_map.proj_ker_of_right_inverse_apply_idem f₁ f₂ h)

