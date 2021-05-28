/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.continuous_on
import Mathlib.group_theory.submonoid.basic
import Mathlib.algebra.group.prod
import Mathlib.algebra.pointwise
import Mathlib.PostPort

universes u_5 l u_3 u_1 u_4 u_2 

namespace Mathlib

/-!
# Theory of topological monoids

In this file we define mixin classes `has_continuous_mul` and `has_continuous_add`. While in many
applications the underlying type is a monoid (multiplicative or additive), we do not require this in
the definitions.
-/

/-- Basic hypothesis to talk about a topological additive monoid or a topological additive
semigroup. A topological additive monoid over `α`, for example, is obtained by requiring both the
instances `add_monoid α` and `has_continuous_add α`. -/
class has_continuous_add (M : Type u_5) [topological_space M] [Add M] 
where
  continuous_add : continuous fun (p : M × M) => prod.fst p + prod.snd p

/-- Basic hypothesis to talk about a topological monoid or a topological semigroup.
A topological monoid over `α`, for example, is obtained by requiring both the instances `monoid α`
and `has_continuous_mul α`. -/
class has_continuous_mul (M : Type u_5) [topological_space M] [Mul M] 
where
  continuous_mul : continuous fun (p : M × M) => prod.fst p * prod.snd p

theorem continuous_add {M : Type u_3} [topological_space M] [Add M] [has_continuous_add M] : continuous fun (p : M × M) => prod.fst p + prod.snd p :=
  has_continuous_add.continuous_add

theorem continuous.mul {α : Type u_1} {M : Type u_3} [topological_space M] [Mul M] [has_continuous_mul M] [topological_space α] {f : α → M} {g : α → M} (hf : continuous f) (hg : continuous g) : continuous fun (x : α) => f x * g x :=
  continuous.comp continuous_mul (continuous.prod_mk hf hg)

-- should `to_additive` be doing this?

theorem continuous_add_left {M : Type u_3} [topological_space M] [Add M] [has_continuous_add M] (a : M) : continuous fun (b : M) => a + b :=
  continuous.add continuous_const continuous_id

theorem continuous_add_right {M : Type u_3} [topological_space M] [Add M] [has_continuous_add M] (a : M) : continuous fun (b : M) => b + a :=
  continuous.add continuous_id continuous_const

theorem continuous_on.add {α : Type u_1} {M : Type u_3} [topological_space M] [Add M] [has_continuous_add M] [topological_space α] {f : α → M} {g : α → M} {s : set α} (hf : continuous_on f s) (hg : continuous_on g s) : continuous_on (fun (x : α) => f x + g x) s :=
  continuous.comp_continuous_on continuous_add (continuous_on.prod hf hg)

theorem tendsto_add {M : Type u_3} [topological_space M] [Add M] [has_continuous_add M] {a : M} {b : M} : filter.tendsto (fun (p : M × M) => prod.fst p + prod.snd p) (nhds (a, b)) (nhds (a + b)) :=
  iff.mp continuous_iff_continuous_at has_continuous_add.continuous_add (a, b)

theorem filter.tendsto.add {α : Type u_1} {M : Type u_3} [topological_space M] [Add M] [has_continuous_add M] {f : α → M} {g : α → M} {x : filter α} {a : M} {b : M} (hf : filter.tendsto f x (nhds a)) (hg : filter.tendsto g x (nhds b)) : filter.tendsto (fun (x : α) => f x + g x) x (nhds (a + b)) :=
  filter.tendsto.comp tendsto_add (filter.tendsto.prod_mk_nhds hf hg)

theorem tendsto.const_mul {α : Type u_1} {M : Type u_3} [topological_space M] [Mul M] [has_continuous_mul M] (b : M) {c : M} {f : α → M} {l : filter α} (h : filter.tendsto (fun (k : α) => f k) l (nhds c)) : filter.tendsto (fun (k : α) => b * f k) l (nhds (b * c)) :=
  filter.tendsto.mul tendsto_const_nhds h

theorem tendsto.add_const {α : Type u_1} {M : Type u_3} [topological_space M] [Add M] [has_continuous_add M] (b : M) {c : M} {f : α → M} {l : filter α} (h : filter.tendsto (fun (k : α) => f k) l (nhds c)) : filter.tendsto (fun (k : α) => f k + b) l (nhds (c + b)) :=
  filter.tendsto.add h tendsto_const_nhds

theorem continuous_at.add {α : Type u_1} {M : Type u_3} [topological_space M] [Add M] [has_continuous_add M] [topological_space α] {f : α → M} {g : α → M} {x : α} (hf : continuous_at f x) (hg : continuous_at g x) : continuous_at (fun (x : α) => f x + g x) x :=
  filter.tendsto.add hf hg

theorem continuous_within_at.add {α : Type u_1} {M : Type u_3} [topological_space M] [Add M] [has_continuous_add M] [topological_space α] {f : α → M} {g : α → M} {s : set α} {x : α} (hf : continuous_within_at f s x) (hg : continuous_within_at g s x) : continuous_within_at (fun (x : α) => f x + g x) s x :=
  filter.tendsto.add hf hg

protected instance prod.has_continuous_mul {M : Type u_3} {N : Type u_4} [topological_space M] [Mul M] [has_continuous_mul M] [topological_space N] [Mul N] [has_continuous_mul N] : has_continuous_mul (M × N) :=
  has_continuous_mul.mk
    (continuous.prod_mk
      (continuous.mul (continuous.comp continuous_fst continuous_fst) (continuous.comp continuous_fst continuous_snd))
      (continuous.mul (continuous.comp continuous_snd continuous_fst) (continuous.comp continuous_snd continuous_snd)))

protected instance has_continuous_mul_of_discrete_topology {N : Type u_4} [topological_space N] [Mul N] [discrete_topology N] : has_continuous_mul N :=
  has_continuous_mul.mk continuous_of_discrete_topology

theorem has_continuous_mul.of_nhds_one {M : Type (max u_1 u_2)} [monoid M] [topological_space M] (hmul : filter.tendsto (function.uncurry Mul.mul) (filter.prod (nhds 1) (nhds 1)) (nhds 1)) (hleft : ∀ (x₀ : M), nhds x₀ = filter.map (fun (x : M) => x₀ * x) (nhds 1)) (hright : ∀ (x₀ : M), nhds x₀ = filter.map (fun (x : M) => x * x₀) (nhds 1)) : has_continuous_mul M := sorry

theorem has_continuous_mul_of_comm_of_nhds_one (M : Type (max u_1 u_2)) [comm_monoid M] [topological_space M] (hmul : filter.tendsto (function.uncurry Mul.mul) (filter.prod (nhds 1) (nhds 1)) (nhds 1)) (hleft : ∀ (x₀ : M), nhds x₀ = filter.map (fun (x : M) => x₀ * x) (nhds 1)) : has_continuous_mul M := sorry

theorem add_submonoid.top_closure_add_self_subset {M : Type u_3} [topological_space M] [add_monoid M] [has_continuous_add M] (s : add_submonoid M) : closure ↑s + closure ↑s ⊆ closure ↑s := sorry

theorem submonoid.top_closure_mul_self_eq {M : Type u_3} [topological_space M] [monoid M] [has_continuous_mul M] (s : submonoid M) : closure ↑s * closure ↑s = closure ↑s := sorry

/-- The (topological-space) closure of a submonoid of a space `M` with `has_continuous_mul` is
itself a submonoid. -/
def add_submonoid.topological_closure {M : Type u_3} [topological_space M] [add_monoid M] [has_continuous_add M] (s : add_submonoid M) : add_submonoid M :=
  add_submonoid.mk (closure ↑s) sorry sorry

theorem submonoid.submonoid_topological_closure {M : Type u_3} [topological_space M] [monoid M] [has_continuous_mul M] (s : submonoid M) : s ≤ submonoid.topological_closure s :=
  subset_closure

theorem submonoid.is_closed_topological_closure {M : Type u_3} [topological_space M] [monoid M] [has_continuous_mul M] (s : submonoid M) : is_closed ↑(submonoid.topological_closure s) := sorry

theorem submonoid.topological_closure_minimal {M : Type u_3} [topological_space M] [monoid M] [has_continuous_mul M] (s : submonoid M) {t : submonoid M} (h : s ≤ t) (ht : is_closed ↑t) : submonoid.topological_closure s ≤ t :=
  closure_minimal h ht

theorem exists_open_nhds_zero_half {M : Type u_3} [topological_space M] [add_monoid M] [has_continuous_add M] {s : set M} (hs : s ∈ nhds 0) : ∃ (V : set M), is_open V ∧ 0 ∈ V ∧ ∀ (v : M), v ∈ V → ∀ (w : M), w ∈ V → v + w ∈ s := sorry

theorem exists_nhds_zero_half {M : Type u_3} [topological_space M] [add_monoid M] [has_continuous_add M] {s : set M} (hs : s ∈ nhds 0) : ∃ (V : set M), ∃ (H : V ∈ nhds 0), ∀ (v : M), v ∈ V → ∀ (w : M), w ∈ V → v + w ∈ s := sorry

theorem exists_nhds_one_split4 {M : Type u_3} [topological_space M] [monoid M] [has_continuous_mul M] {u : set M} (hu : u ∈ nhds 1) : ∃ (V : set M), ∃ (H : V ∈ nhds 1), ∀ {v w s t : M}, v ∈ V → w ∈ V → s ∈ V → t ∈ V → v * w * s * t ∈ u := sorry

/-- Given a neighborhood `U` of `1` there is an open neighborhood `V` of `1`
such that `VV ⊆ U`. -/
theorem exists_open_nhds_one_mul_subset {M : Type u_3} [topological_space M] [monoid M] [has_continuous_mul M] {U : set M} (hU : U ∈ nhds 1) : ∃ (V : set M), is_open V ∧ 1 ∈ V ∧ V * V ⊆ U := sorry

theorem tendsto_list_sum {α : Type u_1} {β : Type u_2} {M : Type u_3} [topological_space M] [add_monoid M] [has_continuous_add M] {f : β → α → M} {x : filter α} {a : β → M} (l : List β) : (∀ (c : β), c ∈ l → filter.tendsto (f c) x (nhds (a c))) →
  filter.tendsto (fun (b : α) => list.sum (list.map (fun (c : β) => f c b) l)) x (nhds (list.sum (list.map a l))) := sorry

theorem continuous_list_sum {α : Type u_1} {β : Type u_2} {M : Type u_3} [topological_space M] [add_monoid M] [has_continuous_add M] [topological_space α] {f : β → α → M} (l : List β) (h : ∀ (c : β), c ∈ l → continuous (f c)) : continuous fun (a : α) => list.sum (list.map (fun (c : β) => f c a) l) :=
  iff.mpr continuous_iff_continuous_at
    fun (x : α) => tendsto_list_sum l fun (c : β) (hc : c ∈ l) => iff.mp continuous_iff_continuous_at (h c hc) x

-- @[to_additive continuous_smul]

theorem continuous_pow {M : Type u_3} [topological_space M] [monoid M] [has_continuous_mul M] (n : ℕ) : continuous fun (a : M) => a ^ n := sorry

theorem continuous.pow {α : Type u_1} {M : Type u_3} [topological_space M] [monoid M] [has_continuous_mul M] {f : α → M} [topological_space α] (h : continuous f) (n : ℕ) : continuous fun (b : α) => f b ^ n :=
  continuous.comp (continuous_pow n) h

theorem submonoid.mem_nhds_one {M : Type u_3} [topological_space M] [comm_monoid M] (S : submonoid M) (oS : is_open ↑S) : ↑S ∈ nhds 1 :=
  mem_nhds_sets oS (submonoid.one_mem S)

theorem tendsto_multiset_prod {α : Type u_1} {β : Type u_2} {M : Type u_3} [topological_space M] [comm_monoid M] [has_continuous_mul M] {f : β → α → M} {x : filter α} {a : β → M} (s : multiset β) : (∀ (c : β), c ∈ s → filter.tendsto (f c) x (nhds (a c))) →
  filter.tendsto (fun (b : α) => multiset.prod (multiset.map (fun (c : β) => f c b) s)) x
    (nhds (multiset.prod (multiset.map a s))) := sorry

theorem tendsto_finset_sum {α : Type u_1} {β : Type u_2} {M : Type u_3} [topological_space M] [add_comm_monoid M] [has_continuous_add M] {f : β → α → M} {x : filter α} {a : β → M} (s : finset β) : (∀ (c : β), c ∈ s → filter.tendsto (f c) x (nhds (a c))) →
  filter.tendsto (fun (b : α) => finset.sum s fun (c : β) => f c b) x (nhds (finset.sum s fun (c : β) => a c)) :=
  tendsto_multiset_sum (finset.val s)

theorem continuous_multiset_prod {α : Type u_1} {β : Type u_2} {M : Type u_3} [topological_space M] [comm_monoid M] [has_continuous_mul M] [topological_space α] {f : β → α → M} (s : multiset β) : (∀ (c : β), c ∈ s → continuous (f c)) → continuous fun (a : α) => multiset.prod (multiset.map (fun (c : β) => f c a) s) := sorry

theorem continuous_finset_prod {α : Type u_1} {β : Type u_2} {M : Type u_3} [topological_space M] [comm_monoid M] [has_continuous_mul M] [topological_space α] {f : β → α → M} (s : finset β) : (∀ (c : β), c ∈ s → continuous (f c)) → continuous fun (a : α) => finset.prod s fun (c : β) => f c a :=
  continuous_multiset_prod (finset.val s)

-- should `to_additive` be doing this?

protected instance additive.has_continuous_add {M : Type u_1} [h : topological_space M] [Mul M] [has_continuous_mul M] : has_continuous_add (additive M) :=
  has_continuous_add.mk continuous_mul

protected instance multiplicative.has_continuous_mul {M : Type u_1} [h : topological_space M] [Add M] [has_continuous_add M] : has_continuous_mul (multiplicative M) :=
  has_continuous_mul.mk continuous_add

