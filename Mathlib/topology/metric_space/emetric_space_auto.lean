/-
Copyright (c) 2015, 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.real.ennreal
import Mathlib.data.finset.intervals
import Mathlib.topology.uniform_space.uniform_embedding
import Mathlib.topology.uniform_space.pi
import Mathlib.topology.uniform_space.uniform_convergence
import Mathlib.PostPort

universes u v u_1 l u_2 

namespace Mathlib

/-!
# Extended metric spaces

This file is devoted to the definition and study of `emetric_spaces`, i.e., metric
spaces in which the distance is allowed to take the value ∞. This extended distance is
called `edist`, and takes values in `ennreal`.

Many definitions and theorems expected on emetric spaces are already introduced on uniform spaces and
topological spaces. For example:
  open and closed sets, compactness, completeness, continuity and uniform continuity

The class `emetric_space` therefore extends `uniform_space` (and `topological_space`).
-/

/-- Characterizing uniformities associated to a (generalized) distance function `D`
in terms of the elements of the uniformity. -/
theorem uniformity_dist_of_mem_uniformity {α : Type u} {β : Type v} [linear_order β]
    {U : filter (α × α)} (z : β) (D : α → α → β)
    (H :
      ∀ (s : set (α × α)), s ∈ U ↔ ∃ (ε : β), ∃ (H : ε > z), ∀ {a b : α}, D a b < ε → (a, b) ∈ s) :
    U =
        infi
          fun (ε : β) =>
            infi
              fun (H : ε > z) =>
                filter.principal (set_of fun (p : α × α) => D (prod.fst p) (prod.snd p) < ε) :=
  sorry

class has_edist (α : Type u_1) where
  edist : α → α → ennreal

/-- Creating a uniform space from an extended distance. -/
def uniform_space_of_edist {α : Type u} (edist : α → α → ennreal)
    (edist_self : ∀ (x : α), edist x x = 0) (edist_comm : ∀ (x y : α), edist x y = edist y x)
    (edist_triangle : ∀ (x y z : α), edist x z ≤ edist x y + edist y z) : uniform_space α :=
  uniform_space.of_core
    (uniform_space.core.mk
      (infi
        fun (ε : ennreal) =>
          infi
            fun (H : ε > 0) =>
              filter.principal (set_of fun (p : α × α) => edist (prod.fst p) (prod.snd p) < ε))
      sorry sorry sorry)

-- the uniform structure is embedded in the emetric space structure

-- to avoid instance diamond issues. See Note [forgetful inheritance].

/-- Extended metric spaces, with an extended distance `edist` possibly taking the
value ∞

Each emetric space induces a canonical `uniform_space` and hence a canonical `topological_space`.
This is enforced in the type class definition, by extending the `uniform_space` structure. When
instantiating an `emetric_space` structure, the uniformity fields are not necessary, they will be
filled in by default. There is a default value for the uniformity, that can be substituted
in cases of interest, for instance when instantiating an `emetric_space` structure
on a product.

Continuity of `edist` is proved in `topology.instances.ennreal`
-/
class emetric_space (α : Type u)
    extends has_edist α,
      emetric_space.to_uniform_space._default #2 #1 #0 α _to_has_edist =
        id (uniform_space_of_edist edist #0 α _to_has_edist),
      uniform_space #2, uniform_space α
    where
  edist_self : ∀ (x : α), edist x x = 0
  eq_of_edist_eq_zero : ∀ {x y : α}, edist x y = 0 → x = y
  edist_comm : ∀ (x y : α), edist x y = edist y x
  edist_triangle : ∀ (x y z : α), edist x z ≤ edist x y + edist y z
  to_uniform_space : uniform_space α
  uniformity_edist :
    autoParam
      (uniformity α =
        infi
          fun (ε : ennreal) =>
            infi
              fun (H : ε > 0) =>
                filter.principal (set_of fun (p : α × α) => edist (prod.fst p) (prod.snd p) < ε))
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.control_laws_tac")
        (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "control_laws_tac") [])

/- emetric spaces are less common than metric spaces. Therefore, we work in a dedicated
namespace, while notions associated to metric spaces are mostly in the root namespace. -/

protected instance emetric_space.to_uniform_space' {α : Type u} [emetric_space α] :
    uniform_space α :=
  emetric_space.to_uniform_space

/-- Characterize the equality of points by the vanishing of their extended distance -/
@[simp] theorem edist_eq_zero {α : Type u} [emetric_space α] {x : α} {y : α} :
    edist x y = 0 ↔ x = y :=
  { mp := eq_of_edist_eq_zero, mpr := fun (this : x = y) => this ▸ edist_self x }

@[simp] theorem zero_eq_edist {α : Type u} [emetric_space α] {x : α} {y : α} :
    0 = edist x y ↔ x = y :=
  { mp := fun (h : 0 = edist x y) => eq_of_edist_eq_zero (Eq.symm h),
    mpr := fun (this : x = y) => this ▸ Eq.symm (edist_self x) }

theorem edist_le_zero {α : Type u} [emetric_space α] {x : α} {y : α} : edist x y ≤ 0 ↔ x = y :=
  iff.trans nonpos_iff_eq_zero edist_eq_zero

/-- Triangle inequality for the extended distance -/
theorem edist_triangle_left {α : Type u} [emetric_space α] (x : α) (y : α) (z : α) :
    edist x y ≤ edist z x + edist z y :=
  eq.mpr (id (Eq._oldrec (Eq.refl (edist x y ≤ edist z x + edist z y)) (edist_comm z x)))
    (edist_triangle x z y)

theorem edist_triangle_right {α : Type u} [emetric_space α] (x : α) (y : α) (z : α) :
    edist x y ≤ edist x z + edist y z :=
  eq.mpr (id (Eq._oldrec (Eq.refl (edist x y ≤ edist x z + edist y z)) (edist_comm y z)))
    (edist_triangle x z y)

theorem edist_triangle4 {α : Type u} [emetric_space α] (x : α) (y : α) (z : α) (t : α) :
    edist x t ≤ edist x y + edist y z + edist z t :=
  le_trans (edist_triangle x z t) (add_le_add_right (edist_triangle x y z) (edist z t))

/-- The triangle (polygon) inequality for sequences of points; `finset.Ico` version. -/
theorem edist_le_Ico_sum_edist {α : Type u} [emetric_space α] (f : ℕ → α) {m : ℕ} {n : ℕ}
    (h : m ≤ n) :
    edist (f m) (f n) ≤ finset.sum (finset.Ico m n) fun (i : ℕ) => edist (f i) (f (i + 1)) :=
  sorry

/-- The triangle (polygon) inequality for sequences of points; `finset.range` version. -/
theorem edist_le_range_sum_edist {α : Type u} [emetric_space α] (f : ℕ → α) (n : ℕ) :
    edist (f 0) (f n) ≤ finset.sum (finset.range n) fun (i : ℕ) => edist (f i) (f (i + 1)) :=
  finset.Ico.zero_bot n ▸ edist_le_Ico_sum_edist f (nat.zero_le n)

/-- A version of `edist_le_Ico_sum_edist` with each intermediate distance replaced
with an upper estimate. -/
theorem edist_le_Ico_sum_of_edist_le {α : Type u} [emetric_space α] {f : ℕ → α} {m : ℕ} {n : ℕ}
    (hmn : m ≤ n) {d : ℕ → ennreal}
    (hd : ∀ {k : ℕ}, m ≤ k → k < n → edist (f k) (f (k + 1)) ≤ d k) :
    edist (f m) (f n) ≤ finset.sum (finset.Ico m n) fun (i : ℕ) => d i :=
  sorry

/-- A version of `edist_le_range_sum_edist` with each intermediate distance replaced
with an upper estimate. -/
theorem edist_le_range_sum_of_edist_le {α : Type u} [emetric_space α] {f : ℕ → α} (n : ℕ)
    {d : ℕ → ennreal} (hd : ∀ {k : ℕ}, k < n → edist (f k) (f (k + 1)) ≤ d k) :
    edist (f 0) (f n) ≤ finset.sum (finset.range n) fun (i : ℕ) => d i :=
  finset.Ico.zero_bot n ▸
    edist_le_Ico_sum_of_edist_le (zero_le n) fun (_x : ℕ) (_x_1 : 0 ≤ _x) => hd

/-- Two points coincide if their distance is `< ε` for all positive ε -/
theorem eq_of_forall_edist_le {α : Type u} [emetric_space α] {x : α} {y : α}
    (h : ∀ (ε : ennreal), ε > 0 → edist x y ≤ ε) : x = y :=
  eq_of_edist_eq_zero (eq_of_le_of_forall_le_of_dense bot_le h)

/-- Reformulation of the uniform structure in terms of the extended distance -/
theorem uniformity_edist {α : Type u} [emetric_space α] :
    uniformity α =
        infi
          fun (ε : ennreal) =>
            infi
              fun (H : ε > 0) =>
                filter.principal (set_of fun (p : α × α) => edist (prod.fst p) (prod.snd p) < ε) :=
  emetric_space.uniformity_edist

theorem uniformity_basis_edist {α : Type u} [emetric_space α] :
    filter.has_basis (uniformity α) (fun (ε : ennreal) => 0 < ε)
        fun (ε : ennreal) => set_of fun (p : α × α) => edist (prod.fst p) (prod.snd p) < ε :=
  sorry

/-- Characterization of the elements of the uniformity in terms of the extended distance -/
theorem mem_uniformity_edist {α : Type u} [emetric_space α] {s : set (α × α)} :
    s ∈ uniformity α ↔ ∃ (ε : ennreal), ∃ (H : ε > 0), ∀ {a b : α}, edist a b < ε → (a, b) ∈ s :=
  filter.has_basis.mem_uniformity_iff uniformity_basis_edist

/-- Given `f : β → ennreal`, if `f` sends `{i | p i}` to a set of positive numbers
accumulating to zero, then `f i`-neighborhoods of the diagonal form a basis of `𝓤 α`.

For specific bases see `uniformity_basis_edist`, `uniformity_basis_edist'`,
`uniformity_basis_edist_nnreal`, and `uniformity_basis_edist_inv_nat`. -/
protected theorem emetric.mk_uniformity_basis {α : Type u} [emetric_space α] {β : Type u_1}
    {p : β → Prop} {f : β → ennreal} (hf₀ : ∀ (x : β), p x → 0 < f x)
    (hf : ∀ (ε : ennreal), 0 < ε → ∃ (x : β), ∃ (hx : p x), f x ≤ ε) :
    filter.has_basis (uniformity α) p
        fun (x : β) => set_of fun (p : α × α) => edist (prod.fst p) (prod.snd p) < f x :=
  sorry

/-- Given `f : β → ennreal`, if `f` sends `{i | p i}` to a set of positive numbers
accumulating to zero, then closed `f i`-neighborhoods of the diagonal form a basis of `𝓤 α`.

For specific bases see `uniformity_basis_edist_le` and `uniformity_basis_edist_le'`. -/
protected theorem emetric.mk_uniformity_basis_le {α : Type u} [emetric_space α] {β : Type u_1}
    {p : β → Prop} {f : β → ennreal} (hf₀ : ∀ (x : β), p x → 0 < f x)
    (hf : ∀ (ε : ennreal), 0 < ε → ∃ (x : β), ∃ (hx : p x), f x ≤ ε) :
    filter.has_basis (uniformity α) p
        fun (x : β) => set_of fun (p : α × α) => edist (prod.fst p) (prod.snd p) ≤ f x :=
  sorry

theorem uniformity_basis_edist_le {α : Type u} [emetric_space α] :
    filter.has_basis (uniformity α) (fun (ε : ennreal) => 0 < ε)
        fun (ε : ennreal) => set_of fun (p : α × α) => edist (prod.fst p) (prod.snd p) ≤ ε :=
  emetric.mk_uniformity_basis_le (fun (_x : ennreal) => id)
    fun (ε : ennreal) (ε₀ : 0 < ε) => Exists.intro ε (Exists.intro ε₀ (le_refl ε))

theorem uniformity_basis_edist' {α : Type u} [emetric_space α] (ε' : ennreal) (hε' : 0 < ε') :
    filter.has_basis (uniformity α) (fun (ε : ennreal) => ε ∈ set.Ioo 0 ε')
        fun (ε : ennreal) => set_of fun (p : α × α) => edist (prod.fst p) (prod.snd p) < ε :=
  sorry

theorem uniformity_basis_edist_le' {α : Type u} [emetric_space α] (ε' : ennreal) (hε' : 0 < ε') :
    filter.has_basis (uniformity α) (fun (ε : ennreal) => ε ∈ set.Ioo 0 ε')
        fun (ε : ennreal) => set_of fun (p : α × α) => edist (prod.fst p) (prod.snd p) ≤ ε :=
  sorry

theorem uniformity_basis_edist_nnreal {α : Type u} [emetric_space α] :
    filter.has_basis (uniformity α) (fun (ε : nnreal) => 0 < ε)
        fun (ε : nnreal) => set_of fun (p : α × α) => edist (prod.fst p) (prod.snd p) < ↑ε :=
  sorry

theorem uniformity_basis_edist_inv_nat {α : Type u} [emetric_space α] :
    filter.has_basis (uniformity α) (fun (_x : ℕ) => True)
        fun (n : ℕ) => set_of fun (p : α × α) => edist (prod.fst p) (prod.snd p) < (↑n⁻¹) :=
  sorry

/-- Fixed size neighborhoods of the diagonal belong to the uniform structure -/
theorem edist_mem_uniformity {α : Type u} [emetric_space α] {ε : ennreal} (ε0 : 0 < ε) :
    (set_of fun (p : α × α) => edist (prod.fst p) (prod.snd p) < ε) ∈ uniformity α :=
  iff.mpr mem_uniformity_edist (Exists.intro ε (Exists.intro ε0 fun (a b : α) => id))

namespace emetric


theorem uniformity_has_countable_basis {α : Type u} [emetric_space α] :
    filter.is_countably_generated (uniformity α) :=
  filter.is_countably_generated_of_seq
    (Exists.intro
      (fun (i : ℕ) => set_of fun (p : α × α) => edist (prod.fst p) (prod.snd p) < (↑i⁻¹))
      (filter.has_basis.eq_infi uniformity_basis_edist_inv_nat))

/-- ε-δ characterization of uniform continuity on a set for emetric spaces -/
theorem uniform_continuous_on_iff {α : Type u} {β : Type v} [emetric_space α] [emetric_space β]
    {f : α → β} {s : set α} :
    uniform_continuous_on f s ↔
        ∀ (ε : ennreal) (H : ε > 0),
          ∃ (δ : ennreal),
            ∃ (H : δ > 0), ∀ {a b : α}, a ∈ s → b ∈ s → edist a b < δ → edist (f a) (f b) < ε :=
  filter.has_basis.uniform_continuous_on_iff uniformity_basis_edist uniformity_basis_edist

/-- ε-δ characterization of uniform continuity on emetric spaces -/
theorem uniform_continuous_iff {α : Type u} {β : Type v} [emetric_space α] [emetric_space β]
    {f : α → β} :
    uniform_continuous f ↔
        ∀ (ε : ennreal) (H : ε > 0),
          ∃ (δ : ennreal), ∃ (H : δ > 0), ∀ {a b : α}, edist a b < δ → edist (f a) (f b) < ε :=
  filter.has_basis.uniform_continuous_iff uniformity_basis_edist uniformity_basis_edist

/-- ε-δ characterization of uniform embeddings on emetric spaces -/
theorem uniform_embedding_iff {α : Type u} {β : Type v} [emetric_space α] [emetric_space β]
    {f : α → β} :
    uniform_embedding f ↔
        function.injective f ∧
          uniform_continuous f ∧
            ∀ (δ : ennreal) (H : δ > 0),
              ∃ (ε : ennreal), ∃ (H : ε > 0), ∀ {a b : α}, edist (f a) (f b) < ε → edist a b < δ :=
  sorry

/-- A map between emetric spaces is a uniform embedding if and only if the edistance between `f x`
and `f y` is controlled in terms of the distance between `x` and `y` and conversely. -/
theorem uniform_embedding_iff' {α : Type u} {β : Type v} [emetric_space α] [emetric_space β]
    {f : α → β} :
    uniform_embedding f ↔
        (∀ (ε : ennreal) (H : ε > 0),
            ∃ (δ : ennreal), ∃ (H : δ > 0), ∀ {a b : α}, edist a b < δ → edist (f a) (f b) < ε) ∧
          ∀ (δ : ennreal) (H : δ > 0),
            ∃ (ε : ennreal), ∃ (H : ε > 0), ∀ {a b : α}, edist (f a) (f b) < ε → edist a b < δ :=
  sorry

/-- ε-δ characterization of Cauchy sequences on emetric spaces -/
protected theorem cauchy_iff {α : Type u} [emetric_space α] {f : filter α} :
    cauchy f ↔
        f ≠ ⊥ ∧
          ∀ (ε : ennreal) (H : ε > 0),
            ∃ (t : set α), ∃ (H : t ∈ f), ∀ (x y : α), x ∈ t → y ∈ t → edist x y < ε :=
  filter.has_basis.cauchy_iff uniformity_basis_edist

/-- A very useful criterion to show that a space is complete is to show that all sequences
which satisfy a bound of the form `edist (u n) (u m) < B N` for all `n m ≥ N` are
converging. This is often applied for `B N = 2^{-N}`, i.e., with a very fast convergence to
`0`, which makes it possible to use arguments of converging series, while this is impossible
to do in general for arbitrary Cauchy sequences. -/
theorem complete_of_convergent_controlled_sequences {α : Type u} [emetric_space α] (B : ℕ → ennreal)
    (hB : ∀ (n : ℕ), 0 < B n)
    (H :
      ∀ (u : ℕ → α),
        (∀ (N n m : ℕ), N ≤ n → N ≤ m → edist (u n) (u m) < B N) →
          ∃ (x : α), filter.tendsto u filter.at_top (nhds x)) :
    complete_space α :=
  uniform_space.complete_of_convergent_controlled_sequences uniformity_has_countable_basis
    (fun (n : ℕ) => set_of fun (p : α × α) => edist (prod.fst p) (prod.snd p) < B n)
    (fun (n : ℕ) => edist_mem_uniformity (hB n)) H

/-- A sequentially complete emetric space is complete. -/
theorem complete_of_cauchy_seq_tendsto {α : Type u} [emetric_space α] :
    (∀ (u : ℕ → α), cauchy_seq u → ∃ (a : α), filter.tendsto u filter.at_top (nhds a)) →
        complete_space α :=
  uniform_space.complete_of_cauchy_seq_tendsto uniformity_has_countable_basis

/-- Expressing locally uniform convergence on a set using `edist`. -/
theorem tendsto_locally_uniformly_on_iff {α : Type u} {β : Type v} [emetric_space α] {ι : Type u_1}
    [topological_space β] {F : ι → β → α} {f : β → α} {p : filter ι} {s : set β} :
    tendsto_locally_uniformly_on F f p s ↔
        ∀ (ε : ennreal) (H : ε > 0) (x : β) (H : x ∈ s),
          ∃ (t : set β),
            ∃ (H : t ∈ nhds_within x s),
              filter.eventually (fun (n : ι) => ∀ (y : β), y ∈ t → edist (f y) (F n y) < ε) p :=
  sorry

/-- Expressing uniform convergence on a set using `edist`. -/
theorem tendsto_uniformly_on_iff {α : Type u} {β : Type v} [emetric_space α] {ι : Type u_1}
    {F : ι → β → α} {f : β → α} {p : filter ι} {s : set β} :
    tendsto_uniformly_on F f p s ↔
        ∀ (ε : ennreal),
          ε > 0 → filter.eventually (fun (n : ι) => ∀ (x : β), x ∈ s → edist (f x) (F n x) < ε) p :=
  sorry

/-- Expressing locally uniform convergence using `edist`. -/
theorem tendsto_locally_uniformly_iff {α : Type u} {β : Type v} [emetric_space α] {ι : Type u_1}
    [topological_space β] {F : ι → β → α} {f : β → α} {p : filter ι} :
    tendsto_locally_uniformly F f p ↔
        ∀ (ε : ennreal) (H : ε > 0) (x : β),
          ∃ (t : set β),
            ∃ (H : t ∈ nhds x),
              filter.eventually (fun (n : ι) => ∀ (y : β), y ∈ t → edist (f y) (F n y) < ε) p :=
  sorry

/-- Expressing uniform convergence using `edist`. -/
theorem tendsto_uniformly_iff {α : Type u} {β : Type v} [emetric_space α] {ι : Type u_1}
    {F : ι → β → α} {f : β → α} {p : filter ι} :
    tendsto_uniformly F f p ↔
        ∀ (ε : ennreal),
          ε > 0 → filter.eventually (fun (n : ι) => ∀ (x : β), edist (f x) (F n x) < ε) p :=
  sorry

end emetric


/-- An emetric space is separated -/
protected instance to_separated {α : Type u} [emetric_space α] : separated_space α :=
  iff.mpr separated_def
    fun (x y : α) (h : ∀ (r : set (α × α)), r ∈ uniformity α → (x, y) ∈ r) =>
      eq_of_forall_edist_le
        fun (ε : ennreal) (ε0 : ε > 0) =>
          le_of_lt
            (h (set_of fun (p : α × α) => edist (prod.fst p) (prod.snd p) < ε)
              (edist_mem_uniformity ε0))

/-- Auxiliary function to replace the uniformity on an emetric space with
a uniformity which is equal to the original one, but maybe not defeq.
This is useful if one wants to construct an emetric space with a
specified uniformity. See Note [forgetful inheritance] explaining why having definitionally
the right uniformity is often important.
-/
def emetric_space.replace_uniformity {α : Type u_1} [U : uniform_space α] (m : emetric_space α)
    (H : uniformity α = uniformity α) : emetric_space α :=
  emetric_space.mk edist_self eq_of_edist_eq_zero edist_comm edist_triangle U

/-- The extended metric induced by an injective function taking values in an emetric space. -/
def emetric_space.induced {α : Type u_1} {β : Type u_2} (f : α → β) (hf : function.injective f)
    (m : emetric_space β) : emetric_space α :=
  emetric_space.mk sorry sorry sorry sorry (uniform_space.comap f emetric_space.to_uniform_space)

/-- Emetric space instance on subsets of emetric spaces -/
protected instance subtype.emetric_space {α : Type u_1} {p : α → Prop} [t : emetric_space α] :
    emetric_space (Subtype p) :=
  emetric_space.induced coe sorry t

/-- The extended distance on a subset of an emetric space is the restriction of
the original distance, by definition -/
theorem subtype.edist_eq {α : Type u} [emetric_space α] {p : α → Prop} (x : Subtype p)
    (y : Subtype p) : edist x y = edist ↑x ↑y :=
  rfl

/-- The product of two emetric spaces, with the max distance, is an extended
metric spaces. We make sure that the uniform structure thus constructed is the one
corresponding to the product of uniform spaces, to avoid diamond problems. -/
protected instance prod.emetric_space_max {α : Type u} {β : Type v} [emetric_space α]
    [emetric_space β] : emetric_space (α × β) :=
  emetric_space.mk sorry sorry sorry sorry prod.uniform_space

theorem prod.edist_eq {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] (x : α × β)
    (y : α × β) :
    edist x y = max (edist (prod.fst x) (prod.fst y)) (edist (prod.snd x) (prod.snd y)) :=
  rfl

/-- The product of a finite number of emetric spaces, with the max distance, is still
an emetric space.
This construction would also work for infinite products, but it would not give rise
to the product topology. Hence, we only formalize it in the good situation of finitely many
spaces. -/
protected instance emetric_space_pi {β : Type v} {π : β → Type u_1} [fintype β]
    [(b : β) → emetric_space (π b)] : emetric_space ((b : β) → π b) :=
  emetric_space.mk sorry sorry sorry sorry (Pi.uniform_space fun (b : β) => π b)

theorem edist_pi_def {β : Type v} {π : β → Type u_1} [fintype β] [(b : β) → emetric_space (π b)]
    (f : (b : β) → π b) (g : (b : β) → π b) :
    edist f g = finset.sup finset.univ fun (b : β) => edist (f b) (g b) :=
  rfl

@[simp] theorem edist_pi_const {α : Type u} {β : Type v} [emetric_space α] [fintype β] [Nonempty β]
    (a : α) (b : α) : (edist (fun (x : β) => a) fun (_x : β) => b) = edist a b :=
  finset.sup_const finset.univ_nonempty (edist a b)

namespace emetric


/-- `emetric.ball x ε` is the set of all points `y` with `edist y x < ε` -/
def ball {α : Type u} [emetric_space α] (x : α) (ε : ennreal) : set α :=
  set_of fun (y : α) => edist y x < ε

@[simp] theorem mem_ball {α : Type u} [emetric_space α] {x : α} {y : α} {ε : ennreal} :
    y ∈ ball x ε ↔ edist y x < ε :=
  iff.rfl

theorem mem_ball' {α : Type u} [emetric_space α] {x : α} {y : α} {ε : ennreal} :
    y ∈ ball x ε ↔ edist x y < ε :=
  eq.mpr (id (Eq._oldrec (Eq.refl (y ∈ ball x ε ↔ edist x y < ε)) (edist_comm x y)))
    (iff.refl (y ∈ ball x ε))

/-- `emetric.closed_ball x ε` is the set of all points `y` with `edist y x ≤ ε` -/
def closed_ball {α : Type u} [emetric_space α] (x : α) (ε : ennreal) : set α :=
  set_of fun (y : α) => edist y x ≤ ε

@[simp] theorem mem_closed_ball {α : Type u} [emetric_space α] {x : α} {y : α} {ε : ennreal} :
    y ∈ closed_ball x ε ↔ edist y x ≤ ε :=
  iff.rfl

theorem ball_subset_closed_ball {α : Type u} [emetric_space α] {x : α} {ε : ennreal} :
    ball x ε ⊆ closed_ball x ε :=
  fun (y : α) =>
    eq.mpr (id (imp_congr_eq (propext mem_ball) (propext mem_closed_ball)))
      fun (h : edist y x < ε) => le_of_lt h

theorem pos_of_mem_ball {α : Type u} [emetric_space α] {x : α} {y : α} {ε : ennreal}
    (hy : y ∈ ball x ε) : 0 < ε :=
  lt_of_le_of_lt (zero_le (edist y x)) hy

theorem mem_ball_self {α : Type u} [emetric_space α] {x : α} {ε : ennreal} (h : 0 < ε) :
    x ∈ ball x ε :=
  (fun (this : edist x x < ε) => this)
    (eq.mpr (id (Eq._oldrec (Eq.refl (edist x x < ε)) (edist_self x))) h)

theorem mem_closed_ball_self {α : Type u} [emetric_space α] {x : α} {ε : ennreal} :
    x ∈ closed_ball x ε :=
  (fun (this : edist x x ≤ ε) => this)
    (eq.mpr (id (Eq._oldrec (Eq.refl (edist x x ≤ ε)) (edist_self x))) bot_le)

theorem mem_ball_comm {α : Type u} [emetric_space α] {x : α} {y : α} {ε : ennreal} :
    x ∈ ball y ε ↔ y ∈ ball x ε :=
  sorry

theorem ball_subset_ball {α : Type u} [emetric_space α] {x : α} {ε₁ : ennreal} {ε₂ : ennreal}
    (h : ε₁ ≤ ε₂) : ball x ε₁ ⊆ ball x ε₂ :=
  fun (y : α) (yx : edist y x < ε₁) => lt_of_lt_of_le yx h

theorem closed_ball_subset_closed_ball {α : Type u} [emetric_space α] {x : α} {ε₁ : ennreal}
    {ε₂ : ennreal} (h : ε₁ ≤ ε₂) : closed_ball x ε₁ ⊆ closed_ball x ε₂ :=
  fun (y : α) (yx : edist y x ≤ ε₁) => le_trans yx h

theorem ball_disjoint {α : Type u} [emetric_space α] {x : α} {y : α} {ε₁ : ennreal} {ε₂ : ennreal}
    (h : ε₁ + ε₂ ≤ edist x y) : ball x ε₁ ∩ ball y ε₂ = ∅ :=
  sorry

theorem ball_subset {α : Type u} [emetric_space α] {x : α} {y : α} {ε₁ : ennreal} {ε₂ : ennreal}
    (h : edist x y + ε₁ ≤ ε₂) (h' : edist x y < ⊤) : ball x ε₁ ⊆ ball y ε₂ :=
  sorry

theorem exists_ball_subset_ball {α : Type u} [emetric_space α] {x : α} {y : α} {ε : ennreal}
    (h : y ∈ ball x ε) : ∃ (ε' : ennreal), ∃ (H : ε' > 0), ball y ε' ⊆ ball x ε :=
  sorry

theorem ball_eq_empty_iff {α : Type u} [emetric_space α] {x : α} {ε : ennreal} :
    ball x ε = ∅ ↔ ε = 0 :=
  sorry

/-- Relation “two points are at a finite edistance” is an equivalence relation. -/
def edist_lt_top_setoid {α : Type u} [emetric_space α] : setoid α :=
  setoid.mk (fun (x y : α) => edist x y < ⊤) sorry

@[simp] theorem ball_zero {α : Type u} [emetric_space α] {x : α} : ball x 0 = ∅ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (ball x 0 = ∅)) (propext ball_eq_empty_iff))) (Eq.refl 0)

theorem nhds_basis_eball {α : Type u} [emetric_space α] {x : α} :
    filter.has_basis (nhds x) (fun (ε : ennreal) => 0 < ε) (ball x) :=
  nhds_basis_uniformity uniformity_basis_edist

theorem nhds_basis_closed_eball {α : Type u} [emetric_space α] {x : α} :
    filter.has_basis (nhds x) (fun (ε : ennreal) => 0 < ε) (closed_ball x) :=
  nhds_basis_uniformity uniformity_basis_edist_le

theorem nhds_eq {α : Type u} [emetric_space α] {x : α} :
    nhds x = infi fun (ε : ennreal) => infi fun (H : ε > 0) => filter.principal (ball x ε) :=
  filter.has_basis.eq_binfi nhds_basis_eball

theorem mem_nhds_iff {α : Type u} [emetric_space α] {x : α} {s : set α} :
    s ∈ nhds x ↔ ∃ (ε : ennreal), ∃ (H : ε > 0), ball x ε ⊆ s :=
  filter.has_basis.mem_iff nhds_basis_eball

theorem is_open_iff {α : Type u} [emetric_space α] {s : set α} :
    is_open s ↔ ∀ (x : α) (H : x ∈ s), ∃ (ε : ennreal), ∃ (H : ε > 0), ball x ε ⊆ s :=
  sorry

theorem is_open_ball {α : Type u} [emetric_space α] {x : α} {ε : ennreal} : is_open (ball x ε) :=
  iff.mpr is_open_iff fun (y : α) => exists_ball_subset_ball

theorem is_closed_ball_top {α : Type u} [emetric_space α] {x : α} : is_closed (ball x ⊤) := sorry

theorem ball_mem_nhds {α : Type u} [emetric_space α] (x : α) {ε : ennreal} (ε0 : 0 < ε) :
    ball x ε ∈ nhds x :=
  mem_nhds_sets is_open_ball (mem_ball_self ε0)

theorem ball_prod_same {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] (x : α) (y : β)
    (r : ennreal) : set.prod (ball x r) (ball y r) = ball (x, y) r :=
  set.ext fun (z : α × β) => iff.symm max_lt_iff

theorem closed_ball_prod_same {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] (x : α)
    (y : β) (r : ennreal) : set.prod (closed_ball x r) (closed_ball y r) = closed_ball (x, y) r :=
  set.ext fun (z : α × β) => iff.symm max_le_iff

/-- ε-characterization of the closure in emetric spaces -/
theorem mem_closure_iff {α : Type u} [emetric_space α] {x : α} {s : set α} :
    x ∈ closure s ↔ ∀ (ε : ennreal) (H : ε > 0), ∃ (y : α), ∃ (H : y ∈ s), edist x y < ε :=
  sorry

theorem tendsto_nhds {α : Type u} {β : Type v} [emetric_space α] {f : filter β} {u : β → α}
    {a : α} :
    filter.tendsto u f (nhds a) ↔
        ∀ (ε : ennreal), ε > 0 → filter.eventually (fun (x : β) => edist (u x) a < ε) f :=
  filter.has_basis.tendsto_right_iff nhds_basis_eball

theorem tendsto_at_top {α : Type u} {β : Type v} [emetric_space α] [Nonempty β] [semilattice_sup β]
    {u : β → α} {a : α} :
    filter.tendsto u filter.at_top (nhds a) ↔
        ∀ (ε : ennreal), ε > 0 → ∃ (N : β), ∀ (n : β), n ≥ N → edist (u n) a < ε :=
  sorry

/-- In an emetric space, Cauchy sequences are characterized by the fact that, eventually,
the edistance between its elements is arbitrarily small -/
theorem cauchy_seq_iff {α : Type u} {β : Type v} [emetric_space α] [Nonempty β] [semilattice_sup β]
    {u : β → α} :
    cauchy_seq u ↔
        ∀ (ε : ennreal), ε > 0 → ∃ (N : β), ∀ (m n : β), m ≥ N → n ≥ N → edist (u m) (u n) < ε :=
  filter.has_basis.cauchy_seq_iff uniformity_basis_edist

/-- A variation around the emetric characterization of Cauchy sequences -/
theorem cauchy_seq_iff' {α : Type u} {β : Type v} [emetric_space α] [Nonempty β] [semilattice_sup β]
    {u : β → α} :
    cauchy_seq u ↔ ∀ (ε : ennreal), ε > 0 → ∃ (N : β), ∀ (n : β), n ≥ N → edist (u n) (u N) < ε :=
  filter.has_basis.cauchy_seq_iff' uniformity_basis_edist

/-- A variation of the emetric characterization of Cauchy sequences that deals with
`ℝ≥0` upper bounds. -/
theorem cauchy_seq_iff_nnreal {α : Type u} {β : Type v} [emetric_space α] [Nonempty β]
    [semilattice_sup β] {u : β → α} :
    cauchy_seq u ↔ ∀ (ε : nnreal), 0 < ε → ∃ (N : β), ∀ (n : β), N ≤ n → edist (u n) (u N) < ↑ε :=
  filter.has_basis.cauchy_seq_iff' uniformity_basis_edist_nnreal

theorem totally_bounded_iff {α : Type u} [emetric_space α] {s : set α} :
    totally_bounded s ↔
        ∀ (ε : ennreal) (H : ε > 0),
          ∃ (t : set α),
            set.finite t ∧ s ⊆ set.Union fun (y : α) => set.Union fun (H : y ∈ t) => ball y ε :=
  sorry

theorem totally_bounded_iff' {α : Type u} [emetric_space α] {s : set α} :
    totally_bounded s ↔
        ∀ (ε : ennreal) (H : ε > 0),
          ∃ (t : set α),
            ∃ (H : t ⊆ s),
              set.finite t ∧ s ⊆ set.Union fun (y : α) => set.Union fun (H : y ∈ t) => ball y ε :=
  sorry

/-- A compact set in an emetric space is separable, i.e., it is the closure of a countable set -/
theorem countable_closure_of_compact {α : Type u} [emetric_space α] {s : set α}
    (hs : is_compact s) : ∃ (t : set α), ∃ (H : t ⊆ s), set.countable t ∧ s = closure t :=
  sorry

--    assume e, finite_cover_balls_of_compact hs,

protected instance topological_space.first_countable_topology (α : Type u) [emetric_space α] :
    topological_space.first_countable_topology α :=
  uniform_space.first_countable_topology uniformity_has_countable_basis

/-- A separable emetric space is second countable: one obtains a countable basis by taking
the balls centered at points in a dense subset, and with rational radii. We do not register
this as an instance, as there is already an instance going in the other direction
from second countable spaces to separable spaces, and we want to avoid loops. -/
theorem second_countable_of_separable (α : Type u) [emetric_space α]
    [topological_space.separable_space α] : topological_space.second_countable_topology α :=
  uniform_space.second_countable_of_separable uniformity_has_countable_basis

/-- The diameter of a set in an emetric space, named `emetric.diam` -/
def diam {α : Type u} [emetric_space α] (s : set α) : ennreal :=
  supr fun (x : α) => supr fun (H : x ∈ s) => supr fun (y : α) => supr fun (H : y ∈ s) => edist x y

theorem diam_le_iff_forall_edist_le {α : Type u} [emetric_space α] {s : set α} {d : ennreal} :
    diam s ≤ d ↔ ∀ (x : α), x ∈ s → ∀ (y : α), y ∈ s → edist x y ≤ d :=
  sorry

/-- If two points belong to some set, their edistance is bounded by the diameter of the set -/
theorem edist_le_diam_of_mem {α : Type u} [emetric_space α] {x : α} {y : α} {s : set α} (hx : x ∈ s)
    (hy : y ∈ s) : edist x y ≤ diam s :=
  iff.mp diam_le_iff_forall_edist_le (le_refl (diam s)) x hx y hy

/-- If the distance between any two points in a set is bounded by some constant, this constant
bounds the diameter. -/
theorem diam_le_of_forall_edist_le {α : Type u} [emetric_space α] {s : set α} {d : ennreal}
    (h : ∀ (x : α), x ∈ s → ∀ (y : α), y ∈ s → edist x y ≤ d) : diam s ≤ d :=
  iff.mpr diam_le_iff_forall_edist_le h

/-- The diameter of a subsingleton vanishes. -/
theorem diam_subsingleton {α : Type u} [emetric_space α] {s : set α} (hs : set.subsingleton s) :
    diam s = 0 :=
  iff.mp nonpos_iff_eq_zero
    (diam_le_of_forall_edist_le
      fun (x : α) (hx : x ∈ s) (y : α) (hy : y ∈ s) =>
        Eq.symm (hs hx hy) ▸ edist_self y ▸ le_refl (edist y y))

/-- The diameter of the empty set vanishes -/
@[simp] theorem diam_empty {α : Type u} [emetric_space α] : diam ∅ = 0 :=
  diam_subsingleton set.subsingleton_empty

/-- The diameter of a singleton vanishes -/
@[simp] theorem diam_singleton {α : Type u} [emetric_space α] {x : α} : diam (singleton x) = 0 :=
  diam_subsingleton set.subsingleton_singleton

theorem diam_eq_zero_iff {α : Type u} [emetric_space α] {s : set α} :
    diam s = 0 ↔ set.subsingleton s :=
  sorry

theorem diam_pos_iff {α : Type u} [emetric_space α] {s : set α} :
    0 < diam s ↔ ∃ (x : α), ∃ (H : x ∈ s), ∃ (y : α), ∃ (H : y ∈ s), x ≠ y :=
  sorry

theorem diam_insert {α : Type u} [emetric_space α] {x : α} {s : set α} :
    diam (insert x s) = max (supr fun (y : α) => supr fun (H : y ∈ s) => edist x y) (diam s) :=
  sorry

theorem diam_pair {α : Type u} [emetric_space α] {x : α} {y : α} :
    diam (insert x (singleton y)) = edist x y :=
  sorry

theorem diam_triple {α : Type u} [emetric_space α] {x : α} {y : α} {z : α} :
    diam (insert x (insert y (singleton z))) = max (max (edist x y) (edist x z)) (edist y z) :=
  sorry

/-- The diameter is monotonous with respect to inclusion -/
theorem diam_mono {α : Type u} [emetric_space α] {s : set α} {t : set α} (h : s ⊆ t) :
    diam s ≤ diam t :=
  diam_le_of_forall_edist_le
    fun (x : α) (hx : x ∈ s) (y : α) (hy : y ∈ s) => edist_le_diam_of_mem (h hx) (h hy)

/-- The diameter of a union is controlled by the diameter of the sets, and the edistance
between two points in the sets. -/
theorem diam_union {α : Type u} [emetric_space α] {x : α} {y : α} {s : set α} {t : set α}
    (xs : x ∈ s) (yt : y ∈ t) : diam (s ∪ t) ≤ diam s + edist x y + diam t :=
  sorry

theorem diam_union' {α : Type u} [emetric_space α] {s : set α} {t : set α}
    (h : set.nonempty (s ∩ t)) : diam (s ∪ t) ≤ diam s + diam t :=
  sorry

theorem diam_closed_ball {α : Type u} [emetric_space α] {x : α} {r : ennreal} :
    diam (closed_ball x r) ≤ bit0 1 * r :=
  sorry

theorem diam_ball {α : Type u} [emetric_space α] {x : α} {r : ennreal} :
    diam (ball x r) ≤ bit0 1 * r :=
  le_trans (diam_mono ball_subset_closed_ball) diam_closed_ball

end Mathlib