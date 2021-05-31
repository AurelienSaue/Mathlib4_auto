/-
Copyright (c) 2018 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.bases
import Mathlib.topology.dense_embedding
import Mathlib.PostPort

universes u u_1 

namespace Mathlib

/-! # Stone-Čech compactification

Construction of the Stone-Čech compactification using ultrafilters.

Parts of the formalization are based on "Ultrafilters and Topology"
by Marius Stekelenburg, particularly section 5.
-/

/- The set of ultrafilters on α carries a natural topology which makes
  it the Stone-Čech compactification of α (viewed as a discrete space). -/

/-- Basis for the topology on `ultrafilter α`. -/
def ultrafilter_basis (α : Type u) : set (set (ultrafilter α)) :=
  set.range fun (s : set α) => set_of fun (u : ultrafilter α) => s ∈ u

protected instance ultrafilter.topological_space {α : Type u} : topological_space (ultrafilter α) :=
  topological_space.generate_from (ultrafilter_basis α)

theorem ultrafilter_basis_is_basis {α : Type u} : topological_space.is_topological_basis (ultrafilter_basis α) := sorry

/-- The basic open sets for the topology on ultrafilters are open. -/
theorem ultrafilter_is_open_basic {α : Type u} (s : set α) : is_open (set_of fun (u : ultrafilter α) => s ∈ u) :=
  topological_space.is_open_of_is_topological_basis ultrafilter_basis_is_basis (Exists.intro s rfl)

/-- The basic open sets for the topology on ultrafilters are also closed. -/
theorem ultrafilter_is_closed_basic {α : Type u} (s : set α) : is_closed (set_of fun (u : ultrafilter α) => s ∈ u) := sorry

/-- Every ultrafilter `u` on `ultrafilter α` converges to a unique
  point of `ultrafilter α`, namely `mjoin u`. -/
theorem ultrafilter_converges_iff {α : Type u} {u : ultrafilter (ultrafilter α)} {x : ultrafilter α} : ↑u ≤ nhds x ↔ x = mjoin u := sorry

protected instance ultrafilter_compact {α : Type u} : compact_space (ultrafilter α) :=
  compact_space.mk
    (iff.mpr compact_iff_ultrafilter_le_nhds
      fun (f : ultrafilter (ultrafilter α)) (_x : ↑f ≤ filter.principal set.univ) =>
        Exists.intro (mjoin f) (Exists.intro trivial (iff.mpr ultrafilter_converges_iff rfl)))

protected instance ultrafilter.t2_space {α : Type u} : t2_space (ultrafilter α) :=
  iff.mpr t2_iff_ultrafilter
    fun (x y : ultrafilter α) (f : ultrafilter (ultrafilter α)) (fx : ↑f ≤ nhds x) (fy : ↑f ≤ nhds y) =>
      (fun (hx : x = mjoin f) =>
          (fun (hy : y = mjoin f) => Eq.trans hx (Eq.symm hy)) (iff.mp ultrafilter_converges_iff fy))
        (iff.mp ultrafilter_converges_iff fx)

theorem ultrafilter_comap_pure_nhds {α : Type u} (b : ultrafilter α) : filter.comap pure (nhds b) ≤ ↑b := sorry

theorem ultrafilter_pure_injective {α : Type u} : function.injective pure := sorry

/-- The range of `pure : α → ultrafilter α` is dense in `ultrafilter α`. -/
theorem dense_range_pure {α : Type u} : dense_range pure := sorry

/-- The map `pure : α → ultra_filter α` induces on `α` the discrete topology. -/
theorem induced_topology_pure {α : Type u} : topological_space.induced pure ultrafilter.topological_space = ⊥ := sorry

/-- `pure : α → ultrafilter α` defines a dense inducing of `α` in `ultrafilter α`. -/
theorem dense_inducing_pure {α : Type u} : dense_inducing pure :=
  dense_inducing.mk (inducing.mk (Eq.symm induced_topology_pure)) dense_range_pure

-- The following refined version will never be used

/-- `pure : α → ultrafilter α` defines a dense embedding of `α` in `ultrafilter α`. -/
theorem dense_embedding_pure {α : Type u} : dense_embedding pure :=
  dense_embedding.mk
    (dense_inducing.mk (dense_inducing.to_inducing dense_inducing_pure) (dense_inducing.dense dense_inducing_pure))
    ultrafilter_pure_injective

/- Goal: Any function `α → γ` to a compact Hausdorff space `γ` has a
  unique extension to a continuous function `ultrafilter α → γ`. We
  already know it must be unique because `α → ultrafilter α` is a
  dense embedding and `γ` is Hausdorff. For existence, we will invoke
  `dense_embedding.continuous_extend`. -/

/-- The extension of a function `α → γ` to a function `ultrafilter α → γ`.
  When `γ` is a compact Hausdorff space it will be continuous. -/
def ultrafilter.extend {α : Type u} {γ : Type u_1} [topological_space γ] (f : α → γ) : ultrafilter α → γ :=
  dense_inducing.extend dense_inducing_pure f

theorem ultrafilter_extend_extends {α : Type u} {γ : Type u_1} [topological_space γ] [t2_space γ] (f : α → γ) : ultrafilter.extend f ∘ pure = f :=
  let _inst : topological_space α := ⊥;
  funext (dense_inducing.extend_eq dense_inducing_pure continuous_of_discrete_topology)

theorem continuous_ultrafilter_extend {α : Type u} {γ : Type u_1} [topological_space γ] [t2_space γ] [compact_space γ] (f : α → γ) : continuous (ultrafilter.extend f) := sorry

/-- The value of `ultrafilter.extend f` on an ultrafilter `b` is the
  unique limit of the ultrafilter `b.map f` in `γ`. -/
theorem ultrafilter_extend_eq_iff {α : Type u} {γ : Type u_1} [topological_space γ] [t2_space γ] [compact_space γ] {f : α → γ} {b : ultrafilter α} {c : γ} : ultrafilter.extend f b = c ↔ ↑(ultrafilter.map f b) ≤ nhds c := sorry

/- Now, we start with a (not necessarily discrete) topological space α
  and we want to construct its Stone-Čech compactification. We can
  build it as a quotient of `ultrafilter α` by the relation which
  identifies two points if the extension of every continuous function
  α → γ to a compact Hausdorff space sends the two points to the same
  point of γ. -/

protected instance stone_cech_setoid (α : Type u) [topological_space α] : setoid (ultrafilter α) :=
  setoid.mk
    (fun (x y : ultrafilter α) =>
      ∀ (γ : Type u) [_inst_2 : topological_space γ] [_inst_3 : t2_space γ] [_inst_4 : compact_space γ] (f : α → γ),
        continuous f → ultrafilter.extend f x = ultrafilter.extend f y)
    sorry

/-- The Stone-Čech compactification of a topological space. -/
def stone_cech (α : Type u) [topological_space α] :=
  quotient (Mathlib.stone_cech_setoid α)

protected instance stone_cech.topological_space {α : Type u} [topological_space α] : topological_space (stone_cech α) :=
  eq.mpr sorry quotient.topological_space

protected instance stone_cech.inhabited {α : Type u} [topological_space α] [Inhabited α] : Inhabited (stone_cech α) :=
  eq.mpr sorry quotient.inhabited

/-- The natural map from α to its Stone-Čech compactification. -/
def stone_cech_unit {α : Type u} [topological_space α] (x : α) : stone_cech α :=
  quotient.mk (pure x)

/-- The image of stone_cech_unit is dense. (But stone_cech_unit need
  not be an embedding, for example if α is not Hausdorff.) -/
theorem dense_range_stone_cech_unit {α : Type u} [topological_space α] : dense_range stone_cech_unit :=
  dense_range.quotient dense_range_pure

/-- The extension of a continuous function from α to a compact
  Hausdorff space γ to the Stone-Čech compactification of α. -/
def stone_cech_extend {α : Type u} [topological_space α] {γ : Type u} [topological_space γ] [t2_space γ] [compact_space γ] {f : α → γ} (hf : continuous f) : stone_cech α → γ :=
  quotient.lift (ultrafilter.extend f) sorry

theorem stone_cech_extend_extends {α : Type u} [topological_space α] {γ : Type u} [topological_space γ] [t2_space γ] [compact_space γ] {f : α → γ} (hf : continuous f) : stone_cech_extend hf ∘ stone_cech_unit = f :=
  ultrafilter_extend_extends f

theorem continuous_stone_cech_extend {α : Type u} [topological_space α] {γ : Type u} [topological_space γ] [t2_space γ] [compact_space γ] {f : α → γ} (hf : continuous f) : continuous (stone_cech_extend hf) :=
  continuous_quot_lift (stone_cech_extend._proof_1 hf) (continuous_ultrafilter_extend f)

theorem convergent_eqv_pure {α : Type u} [topological_space α] {u : ultrafilter α} {x : α} (ux : ↑u ≤ nhds x) : u ≈ pure x := sorry

theorem continuous_stone_cech_unit {α : Type u} [topological_space α] : continuous stone_cech_unit := sorry

protected instance stone_cech.t2_space {α : Type u} [topological_space α] : t2_space (stone_cech α) := sorry

protected instance stone_cech.compact_space {α : Type u} [topological_space α] : compact_space (stone_cech α) :=
  quotient.compact_space

