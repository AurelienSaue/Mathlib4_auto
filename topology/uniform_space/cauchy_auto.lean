/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.topology.uniform_space.basic
import Mathlib.topology.bases
import Mathlib.data.set.intervals.default
import PostPort

universes u v u_1 l 

namespace Mathlib

/-!
# Theory of Cauchy filters in uniform spaces. Complete uniform spaces. Totally bounded subsets.
-/

/-- A filter `f` is Cauchy if for every entourage `r`, there exists an
  `s ∈ f` such that `s × s ⊆ r`. This is a generalization of Cauchy
  sequences, because if `a : ℕ → α` then the filter of sets containing
  cofinitely many of the `a n` is Cauchy iff `a` is a Cauchy sequence. -/
def cauchy {α : Type u} [uniform_space α] (f : filter α)  :=
  filter.ne_bot f ∧ filter.prod f f ≤ uniformity α

/-- A set `s` is called *complete*, if any Cauchy filter `f` such that `s ∈ f`
has a limit in `s` (formally, it satisfies `f ≤ 𝓝 x` for some `x ∈ s`). -/
def is_complete {α : Type u} [uniform_space α] (s : set α)  :=
  ∀ (f : filter α), cauchy f → f ≤ filter.principal s → ∃ (x : α), ∃ (H : x ∈ s), f ≤ nhds x

theorem filter.has_basis.cauchy_iff {α : Type u} {β : Type v} [uniform_space α] {p : β → Prop} {s : β → set (α × α)} (h : filter.has_basis (uniformity α) p s) {f : filter α} : cauchy f ↔ filter.ne_bot f ∧ ∀ (i : β), p i → ∃ (t : set α), ∃ (H : t ∈ f), ∀ (x y : α), x ∈ t → y ∈ t → (x, y) ∈ s i := sorry

theorem cauchy_iff' {α : Type u} [uniform_space α] {f : filter α} : cauchy f ↔
  filter.ne_bot f ∧
    ∀ (s : set (α × α)) (H : s ∈ uniformity α), ∃ (t : set α), ∃ (H : t ∈ f), ∀ (x y : α), x ∈ t → y ∈ t → (x, y) ∈ s :=
  filter.has_basis.cauchy_iff (filter.basis_sets (uniformity α))

theorem cauchy_iff {α : Type u} [uniform_space α] {f : filter α} : cauchy f ↔ filter.ne_bot f ∧ ∀ (s : set (α × α)) (H : s ∈ uniformity α), ∃ (t : set α), ∃ (H : t ∈ f), set.prod t t ⊆ s := sorry

theorem cauchy_map_iff {α : Type u} {β : Type v} [uniform_space α] {l : filter β} {f : β → α} : cauchy (filter.map f l) ↔
  filter.ne_bot l ∧
    filter.tendsto (fun (p : β × β) => (f (prod.fst p), f (prod.snd p))) (filter.prod l l) (uniformity α) := sorry

theorem cauchy_map_iff' {α : Type u} {β : Type v} [uniform_space α] {l : filter β} [hl : filter.ne_bot l] {f : β → α} : cauchy (filter.map f l) ↔
  filter.tendsto (fun (p : β × β) => (f (prod.fst p), f (prod.snd p))) (filter.prod l l) (uniformity α) :=
  iff.trans cauchy_map_iff (and_iff_right hl)

theorem cauchy.mono {α : Type u} [uniform_space α] {f : filter α} {g : filter α} [hg : filter.ne_bot g] (h_c : cauchy f) (h_le : g ≤ f) : cauchy g :=
  { left := hg, right := le_trans (filter.prod_mono h_le h_le) (and.right h_c) }

theorem cauchy.mono' {α : Type u} [uniform_space α] {f : filter α} {g : filter α} (h_c : cauchy f) (hg : filter.ne_bot g) (h_le : g ≤ f) : cauchy g :=
  cauchy.mono h_c h_le

theorem cauchy_nhds {α : Type u} [uniform_space α] {a : α} : cauchy (nhds a) := sorry

theorem cauchy_pure {α : Type u} [uniform_space α] {a : α} : cauchy (pure a) :=
  cauchy.mono cauchy_nhds (pure_le_nhds a)

theorem filter.tendsto.cauchy_map {α : Type u} {β : Type v} [uniform_space α] {l : filter β} [filter.ne_bot l] {f : β → α} {a : α} (h : filter.tendsto f l (nhds a)) : cauchy (filter.map f l) :=
  cauchy.mono cauchy_nhds h

/-- The common part of the proofs of `le_nhds_of_cauchy_adhp` and
`sequentially_complete.le_nhds_of_seq_tendsto_nhds`: if for any entourage `s`
one can choose a set `t ∈ f` of diameter `s` such that it contains a point `y`
with `(x, y) ∈ s`, then `f` converges to `x`. -/
theorem le_nhds_of_cauchy_adhp_aux {α : Type u} [uniform_space α] {f : filter α} {x : α} (adhs : ∀ (s : set (α × α)) (H : s ∈ uniformity α),
  ∃ (t : set α), ∃ (H : t ∈ f), set.prod t t ⊆ s ∧ ∃ (y : α), (x, y) ∈ s ∧ y ∈ t) : f ≤ nhds x := sorry

/-- If `x` is an adherent (cluster) point for a Cauchy filter `f`, then it is a limit point
for `f`. -/
theorem le_nhds_of_cauchy_adhp {α : Type u} [uniform_space α] {f : filter α} {x : α} (hf : cauchy f) (adhs : cluster_pt x f) : f ≤ nhds x := sorry

theorem le_nhds_iff_adhp_of_cauchy {α : Type u} [uniform_space α] {f : filter α} {x : α} (hf : cauchy f) : f ≤ nhds x ↔ cluster_pt x f :=
  { mp := fun (h : f ≤ nhds x) => cluster_pt.of_le_nhds' h (and.left hf), mpr := le_nhds_of_cauchy_adhp hf }

theorem cauchy.map {α : Type u} {β : Type v} [uniform_space α] [uniform_space β] {f : filter α} {m : α → β} (hf : cauchy f) (hm : uniform_continuous m) : cauchy (filter.map m f) :=
  { left := filter.ne_bot.map (and.left hf) m,
    right := le_trans (trans_rel_right LessEq filter.prod_map_map_eq (filter.map_mono (and.right hf))) hm }

theorem cauchy.comap {α : Type u} {β : Type v} [uniform_space α] [uniform_space β] {f : filter β} {m : α → β} (hf : cauchy f) (hm : filter.comap (fun (p : α × α) => (m (prod.fst p), m (prod.snd p))) (uniformity β) ≤ uniformity α) [filter.ne_bot (filter.comap m f)] : cauchy (filter.comap m f) :=
  { left := _inst_3,
    right := le_trans (trans_rel_right LessEq filter.prod_comap_comap_eq (filter.comap_mono (and.right hf))) hm }

theorem cauchy.comap' {α : Type u} {β : Type v} [uniform_space α] [uniform_space β] {f : filter β} {m : α → β} (hf : cauchy f) (hm : filter.comap (fun (p : α × α) => (m (prod.fst p), m (prod.snd p))) (uniformity β) ≤ uniformity α) (hb : filter.ne_bot (filter.comap m f)) : cauchy (filter.comap m f) :=
  cauchy.comap hf hm

/-- Cauchy sequences. Usually defined on ℕ, but often it is also useful to say that a function
defined on ℝ is Cauchy at +∞ to deduce convergence. Therefore, we define it in a type class that
is general enough to cover both ℕ and ℝ, which are the main motivating examples. -/
def cauchy_seq {α : Type u} {β : Type v} [uniform_space α] [semilattice_sup β] (u : β → α)  :=
  cauchy (filter.map u filter.at_top)

theorem cauchy_seq.mem_entourage {α : Type u} [uniform_space α] {ι : Type u_1} [Nonempty ι] [linear_order ι] {u : ι → α} (h : cauchy_seq u) {V : set (α × α)} (hV : V ∈ uniformity α) : ∃ (k₀ : ι), ∀ (i j : ι), k₀ ≤ i → k₀ ≤ j → (u i, u j) ∈ V := sorry

theorem filter.tendsto.cauchy_seq {α : Type u} {β : Type v} [uniform_space α] [semilattice_sup β] [Nonempty β] {f : β → α} {x : α} (hx : filter.tendsto f filter.at_top (nhds x)) : cauchy_seq f :=
  filter.tendsto.cauchy_map hx

theorem cauchy_seq_iff_tendsto {α : Type u} {β : Type v} [uniform_space α] [Nonempty β] [semilattice_sup β] {u : β → α} : cauchy_seq u ↔ filter.tendsto (prod.map u u) filter.at_top (uniformity α) := sorry

/-- If a Cauchy sequence has a convergent subsequence, then it converges. -/
theorem tendsto_nhds_of_cauchy_seq_of_subseq {α : Type u} {β : Type v} [uniform_space α] [semilattice_sup β] {u : β → α} (hu : cauchy_seq u) {ι : Type u_1} {f : ι → β} {p : filter ι} [filter.ne_bot p] (hf : filter.tendsto f p filter.at_top) {a : α} (ha : filter.tendsto (u ∘ f) p (nhds a)) : filter.tendsto u filter.at_top (nhds a) :=
  le_nhds_of_cauchy_adhp hu (map_cluster_pt_of_comp hf ha)

theorem filter.has_basis.cauchy_seq_iff {α : Type u} {β : Type v} [uniform_space α] {γ : Type u_1} [Nonempty β] [semilattice_sup β] {u : β → α} {p : γ → Prop} {s : γ → set (α × α)} (h : filter.has_basis (uniformity α) p s) : cauchy_seq u ↔ ∀ (i : γ), p i → ∃ (N : β), ∀ (m n : β), m ≥ N → n ≥ N → (u m, u n) ∈ s i := sorry

theorem filter.has_basis.cauchy_seq_iff' {α : Type u} {β : Type v} [uniform_space α] {γ : Type u_1} [Nonempty β] [semilattice_sup β] {u : β → α} {p : γ → Prop} {s : γ → set (α × α)} (H : filter.has_basis (uniformity α) p s) : cauchy_seq u ↔ ∀ (i : γ), p i → ∃ (N : β), ∀ (n : β), n ≥ N → (u n, u N) ∈ s i := sorry

theorem cauchy_seq_of_controlled {α : Type u} {β : Type v} [uniform_space α] [semilattice_sup β] [Nonempty β] (U : β → set (α × α)) (hU : ∀ (s : set (α × α)), s ∈ uniformity α → ∃ (n : β), U n ⊆ s) {f : β → α} (hf : ∀ {N m n : β}, N ≤ m → N ≤ n → (f m, f n) ∈ U N) : cauchy_seq f := sorry

/-- A complete space is defined here using uniformities. A uniform space
  is complete if every Cauchy filter converges. -/
class complete_space (α : Type u) [uniform_space α] 
where
  complete : ∀ {f : filter α}, cauchy f → ∃ (x : α), f ≤ nhds x

theorem complete_univ {α : Type u} [uniform_space α] [complete_space α] : is_complete set.univ := sorry

theorem cauchy_prod {α : Type u} {β : Type v} [uniform_space α] [uniform_space β] {f : filter α} {g : filter β} : cauchy f → cauchy g → cauchy (filter.prod f g) := sorry

protected instance complete_space.prod {α : Type u} {β : Type v} [uniform_space α] [uniform_space β] [complete_space α] [complete_space β] : complete_space (α × β) :=
  complete_space.mk fun (f : filter (α × β)) (hf : cauchy f) => sorry

/--If `univ` is complete, the space is a complete space -/
theorem complete_space_of_is_complete_univ {α : Type u} [uniform_space α] (h : is_complete set.univ) : complete_space α := sorry

theorem complete_space_iff_is_complete_univ {α : Type u} [uniform_space α] : complete_space α ↔ is_complete set.univ :=
  { mp := complete_univ, mpr := complete_space_of_is_complete_univ }

theorem cauchy_iff_exists_le_nhds {α : Type u} [uniform_space α] [complete_space α] {l : filter α} [filter.ne_bot l] : cauchy l ↔ ∃ (x : α), l ≤ nhds x := sorry

theorem cauchy_map_iff_exists_tendsto {α : Type u} {β : Type v} [uniform_space α] [complete_space α] {l : filter β} {f : β → α} [filter.ne_bot l] : cauchy (filter.map f l) ↔ ∃ (x : α), filter.tendsto f l (nhds x) :=
  cauchy_iff_exists_le_nhds

/-- A Cauchy sequence in a complete space converges -/
theorem cauchy_seq_tendsto_of_complete {α : Type u} {β : Type v} [uniform_space α] [semilattice_sup β] [complete_space α] {u : β → α} (H : cauchy_seq u) : ∃ (x : α), filter.tendsto u filter.at_top (nhds x) :=
  complete_space.complete H

/-- If `K` is a complete subset, then any cauchy sequence in `K` converges to a point in `K` -/
theorem cauchy_seq_tendsto_of_is_complete {α : Type u} {β : Type v} [uniform_space α] [semilattice_sup β] {K : set α} (h₁ : is_complete K) {u : β → α} (h₂ : ∀ (n : β), u n ∈ K) (h₃ : cauchy_seq u) : ∃ (v : α), ∃ (H : v ∈ K), filter.tendsto u filter.at_top (nhds v) := sorry

theorem cauchy.le_nhds_Lim {α : Type u} [uniform_space α] [complete_space α] [Nonempty α] {f : filter α} (hf : cauchy f) : f ≤ nhds (Lim f) :=
  le_nhds_Lim (complete_space.complete hf)

theorem cauchy_seq.tendsto_lim {α : Type u} {β : Type v} [uniform_space α] [semilattice_sup β] [complete_space α] [Nonempty α] {u : β → α} (h : cauchy_seq u) : filter.tendsto u filter.at_top (nhds (lim filter.at_top u)) :=
  cauchy.le_nhds_Lim h

theorem is_closed.is_complete {α : Type u} [uniform_space α] [complete_space α] {s : set α} (h : is_closed s) : is_complete s := sorry

/-- A set `s` is totally bounded if for every entourage `d` there is a finite
  set of points `t` such that every element of `s` is `d`-near to some element of `t`. -/
def totally_bounded {α : Type u} [uniform_space α] (s : set α)  :=
  ∀ (d : set (α × α)) (H : d ∈ uniformity α),
    ∃ (t : set α),
      set.finite t ∧ s ⊆ set.Union fun (y : α) => set.Union fun (H : y ∈ t) => set_of fun (x : α) => (x, y) ∈ d

theorem totally_bounded_iff_subset {α : Type u} [uniform_space α] {s : set α} : totally_bounded s ↔
  ∀ (d : set (α × α)) (H : d ∈ uniformity α),
    ∃ (t : set α),
      ∃ (H : t ⊆ s),
        set.finite t ∧ s ⊆ set.Union fun (y : α) => set.Union fun (H : y ∈ t) => set_of fun (x : α) => (x, y) ∈ d := sorry

theorem totally_bounded_of_forall_symm {α : Type u} [uniform_space α] {s : set α} (h : ∀ (V : set (α × α)) (H : V ∈ uniformity α),
  symmetric_rel V →
    ∃ (t : set α), set.finite t ∧ s ⊆ set.Union fun (y : α) => set.Union fun (H : y ∈ t) => uniform_space.ball y V) : totally_bounded s := sorry

theorem totally_bounded_subset {α : Type u} [uniform_space α] {s₁ : set α} {s₂ : set α} (hs : s₁ ⊆ s₂) (h : totally_bounded s₂) : totally_bounded s₁ := sorry

theorem totally_bounded_empty {α : Type u} [uniform_space α] : totally_bounded ∅ := sorry

/-- The closure of a totally bounded set is totally bounded. -/
theorem totally_bounded.closure {α : Type u} [uniform_space α] {s : set α} (h : totally_bounded s) : totally_bounded (closure s) := sorry

/-- The image of a totally bounded set under a unifromly continuous map is totally bounded. -/
theorem totally_bounded.image {α : Type u} {β : Type v} [uniform_space α] [uniform_space β] {f : α → β} {s : set α} (hs : totally_bounded s) (hf : uniform_continuous f) : totally_bounded (f '' s) := sorry

theorem ultrafilter.cauchy_of_totally_bounded {α : Type u} [uniform_space α] {s : set α} (f : ultrafilter α) (hs : totally_bounded s) (h : ↑f ≤ filter.principal s) : cauchy ↑f := sorry

theorem totally_bounded_iff_filter {α : Type u} [uniform_space α] {s : set α} : totally_bounded s ↔
  ∀ (f : filter α), filter.ne_bot f → f ≤ filter.principal s → ∃ (c : filter α), ∃ (H : c ≤ f), cauchy c := sorry

theorem totally_bounded_iff_ultrafilter {α : Type u} [uniform_space α] {s : set α} : totally_bounded s ↔ ∀ (f : ultrafilter α), ↑f ≤ filter.principal s → cauchy ↑f := sorry

theorem compact_iff_totally_bounded_complete {α : Type u} [uniform_space α] {s : set α} : is_compact s ↔ totally_bounded s ∧ is_complete s := sorry

protected instance complete_of_compact {α : Type u} [uniform_space α] [compact_space α] : complete_space α := sorry

theorem compact_of_totally_bounded_is_closed {α : Type u} [uniform_space α] [complete_space α] {s : set α} (ht : totally_bounded s) (hc : is_closed s) : is_compact s :=
  iff.mpr compact_iff_totally_bounded_complete { left := ht, right := is_closed.is_complete hc }

/-!
### Sequentially complete space

In this section we prove that a uniform space is complete provided that it is sequentially complete
(i.e., any Cauchy sequence converges) and its uniformity filter admits a countable generating set.
In particular, this applies to (e)metric spaces, see the files `topology/metric_space/emetric_space`
and `topology/metric_space/basic`.

More precisely, we assume that there is a sequence of entourages `U_n` such that any other
entourage includes one of `U_n`. Then any Cauchy filter `f` generates a decreasing sequence of
sets `s_n ∈ f` such that `s_n × s_n ⊆ U_n`. Choose a sequence `x_n∈s_n`. It is easy to show
that this is a Cauchy sequence. If this sequence converges to some `a`, then `f ≤ 𝓝 a`. -/

namespace sequentially_complete


/-- An auxiliary sequence of sets approximating a Cauchy filter. -/
def set_seq_aux {α : Type u} [uniform_space α] {f : filter α} (hf : cauchy f) {U : ℕ → set (α × α)} (U_mem : ∀ (n : ℕ), U n ∈ uniformity α) (n : ℕ) : Subtype fun (s : set α) => ∃ (_x : s ∈ f), set.prod s s ⊆ U n :=
  classical.indefinite_description (fun (s : set α) => ∃ (_x : s ∈ f), set.prod s s ⊆ U n) sorry

/-- Given a Cauchy filter `f` and a sequence `U` of entourages, `set_seq` provides
a sequence of monotonically decreasing sets `s n ∈ f` such that `(s n).prod (s n) ⊆ U`. -/
def set_seq {α : Type u} [uniform_space α] {f : filter α} (hf : cauchy f) {U : ℕ → set (α × α)} (U_mem : ∀ (n : ℕ), U n ∈ uniformity α) (n : ℕ) : set α :=
  set.Inter fun (m : ℕ) => set.Inter fun (H : m ∈ set.Iic n) => subtype.val (set_seq_aux hf U_mem m)

theorem set_seq_mem {α : Type u} [uniform_space α] {f : filter α} (hf : cauchy f) {U : ℕ → set (α × α)} (U_mem : ∀ (n : ℕ), U n ∈ uniformity α) (n : ℕ) : set_seq hf U_mem n ∈ f :=
  iff.mpr (filter.bInter_mem_sets (set.finite_le_nat n))
    fun (m : ℕ) (_x : m ∈ set_of fun (i : ℕ) => i ≤ n) => Exists.fst (subtype.property (set_seq_aux hf U_mem m))

theorem set_seq_mono {α : Type u} [uniform_space α] {f : filter α} (hf : cauchy f) {U : ℕ → set (α × α)} (U_mem : ∀ (n : ℕ), U n ∈ uniformity α) {m : ℕ} {n : ℕ} (h : m ≤ n) : set_seq hf U_mem n ⊆ set_seq hf U_mem m :=
  set.bInter_subset_bInter_left fun (k : ℕ) (hk : k ∈ set.Iic m) => le_trans hk h

theorem set_seq_sub_aux {α : Type u} [uniform_space α] {f : filter α} (hf : cauchy f) {U : ℕ → set (α × α)} (U_mem : ∀ (n : ℕ), U n ∈ uniformity α) (n : ℕ) : set_seq hf U_mem n ⊆ ↑(set_seq_aux hf U_mem n) :=
  set.bInter_subset_of_mem set.right_mem_Iic

theorem set_seq_prod_subset {α : Type u} [uniform_space α] {f : filter α} (hf : cauchy f) {U : ℕ → set (α × α)} (U_mem : ∀ (n : ℕ), U n ∈ uniformity α) {N : ℕ} {m : ℕ} {n : ℕ} (hm : N ≤ m) (hn : N ≤ n) : set.prod (set_seq hf U_mem m) (set_seq hf U_mem n) ⊆ U N := sorry

/-- A sequence of points such that `seq n ∈ set_seq n`. Here `set_seq` is a monotonically
decreasing sequence of sets `set_seq n ∈ f` with diameters controlled by a given sequence
of entourages. -/
def seq {α : Type u} [uniform_space α] {f : filter α} (hf : cauchy f) {U : ℕ → set (α × α)} (U_mem : ∀ (n : ℕ), U n ∈ uniformity α) (n : ℕ) : α :=
  classical.some sorry

theorem seq_mem {α : Type u} [uniform_space α] {f : filter α} (hf : cauchy f) {U : ℕ → set (α × α)} (U_mem : ∀ (n : ℕ), U n ∈ uniformity α) (n : ℕ) : seq hf U_mem n ∈ set_seq hf U_mem n :=
  classical.some_spec (filter.ne_bot.nonempty_of_mem (and.left hf) (set_seq_mem hf U_mem n))

theorem seq_pair_mem {α : Type u} [uniform_space α] {f : filter α} (hf : cauchy f) {U : ℕ → set (α × α)} (U_mem : ∀ (n : ℕ), U n ∈ uniformity α) {N : ℕ} {m : ℕ} {n : ℕ} (hm : N ≤ m) (hn : N ≤ n) : (seq hf U_mem m, seq hf U_mem n) ∈ U N :=
  set_seq_prod_subset hf U_mem hm hn { left := seq_mem hf U_mem m, right := seq_mem hf U_mem n }

theorem seq_is_cauchy_seq {α : Type u} [uniform_space α] {f : filter α} (hf : cauchy f) {U : ℕ → set (α × α)} (U_mem : ∀ (n : ℕ), U n ∈ uniformity α) (U_le : ∀ (s : set (α × α)), s ∈ uniformity α → ∃ (n : ℕ), U n ⊆ s) : cauchy_seq (seq hf U_mem) :=
  cauchy_seq_of_controlled U U_le (seq_pair_mem hf U_mem)

/-- If the sequence `sequentially_complete.seq` converges to `a`, then `f ≤ 𝓝 a`. -/
theorem le_nhds_of_seq_tendsto_nhds {α : Type u} [uniform_space α] {f : filter α} (hf : cauchy f) {U : ℕ → set (α × α)} (U_mem : ∀ (n : ℕ), U n ∈ uniformity α) (U_le : ∀ (s : set (α × α)), s ∈ uniformity α → ∃ (n : ℕ), U n ⊆ s) {a : α} (ha : filter.tendsto (seq hf U_mem) filter.at_top (nhds a)) : f ≤ nhds a := sorry

end sequentially_complete


namespace uniform_space


/-- A uniform space is complete provided that (a) its uniformity filter has a countable basis;
(b) any sequence satisfying a "controlled" version of the Cauchy condition converges. -/
theorem complete_of_convergent_controlled_sequences {α : Type u} [uniform_space α] (H : filter.is_countably_generated (uniformity α)) (U : ℕ → set (α × α)) (U_mem : ∀ (n : ℕ), U n ∈ uniformity α) (HU : ∀ (u : ℕ → α), (∀ (N m n : ℕ), N ≤ m → N ≤ n → (u m, u n) ∈ U N) → ∃ (a : α), filter.tendsto u filter.at_top (nhds a)) : complete_space α := sorry

/-- A sequentially complete uniform space with a countable basis of the uniformity filter is
complete. -/
theorem complete_of_cauchy_seq_tendsto {α : Type u} [uniform_space α] (H : filter.is_countably_generated (uniformity α)) (H' : ∀ (u : ℕ → α), cauchy_seq u → ∃ (a : α), filter.tendsto u filter.at_top (nhds a)) : complete_space α := sorry

protected theorem first_countable_topology {α : Type u} [uniform_space α] (H : filter.is_countably_generated (uniformity α)) : topological_space.first_countable_topology α := sorry

/-- A separable uniform space with countably generated uniformity filter is second countable:
one obtains a countable basis by taking the balls centered at points in a dense subset,
and with rational "radii" from a countable open symmetric antimono basis of `𝓤 α`. We do not
register this as an instance, as there is already an instance going in the other direction
from second countable spaces to separable spaces, and we want to avoid loops. -/
theorem second_countable_of_separable {α : Type u} [uniform_space α] (H : filter.is_countably_generated (uniformity α)) [topological_space.separable_space α] : topological_space.second_countable_topology α := sorry

