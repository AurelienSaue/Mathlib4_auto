/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.instances.nnreal
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Extended non-negative reals
-/

namespace ennreal


/-- Topology on `ennreal`.

Note: this is different from the `emetric_space` topology. The `emetric_space` topology has
`is_open {⊤}`, while this topology doesn't have singleton elements. -/
protected instance topological_space : topological_space ennreal :=
  preorder.topology ennreal

protected instance order_topology : order_topology ennreal :=
  order_topology.mk rfl

protected instance t2_space : t2_space ennreal :=
  regular_space.t2_space ennreal

protected instance topological_space.second_countable_topology : topological_space.second_countable_topology ennreal := sorry

theorem embedding_coe : embedding coe := sorry

theorem is_open_ne_top : is_open (set_of fun (a : ennreal) => a ≠ ⊤) :=
  is_open_ne

theorem is_open_Ico_zero {b : ennreal} : is_open (set.Ico 0 b) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_open (set.Ico 0 b))) ennreal.Ico_eq_Iio)) is_open_Iio

theorem coe_range_mem_nhds {r : nnreal} : set.range coe ∈ nhds ↑r := sorry

theorem tendsto_coe {α : Type u_1} {f : filter α} {m : α → nnreal} {a : nnreal} : filter.tendsto (fun (a : α) => ↑(m a)) f (nhds ↑a) ↔ filter.tendsto m f (nhds a) :=
  iff.symm (embedding.tendsto_nhds_iff embedding_coe)

theorem continuous_coe : continuous coe :=
  embedding.continuous embedding_coe

theorem continuous_coe_iff {α : Type u_1} [topological_space α] {f : α → nnreal} : (continuous fun (a : α) => ↑(f a)) ↔ continuous f :=
  iff.symm (embedding.continuous_iff embedding_coe)

theorem nhds_coe {r : nnreal} : nhds ↑r = filter.map coe (nhds r) := sorry

theorem nhds_coe_coe {r : nnreal} {p : nnreal} : nhds (↑r, ↑p) = filter.map (fun (p : nnreal × nnreal) => (↑(prod.fst p), ↑(prod.snd p))) (nhds (r, p)) := sorry

theorem continuous_of_real : continuous ennreal.of_real :=
  continuous.comp (iff.mpr continuous_coe_iff continuous_id) nnreal.continuous_of_real

theorem tendsto_of_real {α : Type u_1} {f : filter α} {m : α → ℝ} {a : ℝ} (h : filter.tendsto m f (nhds a)) : filter.tendsto (fun (a : α) => ennreal.of_real (m a)) f (nhds (ennreal.of_real a)) :=
  filter.tendsto.comp (continuous.tendsto continuous_of_real a) h

theorem tendsto_to_nnreal {a : ennreal} : a ≠ ⊤ → filter.tendsto ennreal.to_nnreal (nhds a) (nhds (ennreal.to_nnreal a)) := sorry

theorem continuous_on_to_nnreal : continuous_on ennreal.to_nnreal (set_of fun (a : ennreal) => a ≠ ⊤) := sorry

theorem tendsto_to_real {a : ennreal} : a ≠ ⊤ → filter.tendsto ennreal.to_real (nhds a) (nhds (ennreal.to_real a)) :=
  fun (ha : a ≠ ⊤) => filter.tendsto.comp (iff.mpr nnreal.tendsto_coe filter.tendsto_id) (tendsto_to_nnreal ha)

/-- The set of finite `ennreal` numbers is homeomorphic to `ℝ≥0`. -/
def ne_top_homeomorph_nnreal : ↥(set_of fun (a : ennreal) => a ≠ ⊤) ≃ₜ nnreal :=
  homeomorph.mk (equiv.mk (equiv.to_fun ne_top_equiv_nnreal) (equiv.inv_fun ne_top_equiv_nnreal) sorry sorry)

/-- The set of finite `ennreal` numbers is homeomorphic to `ℝ≥0`. -/
def lt_top_homeomorph_nnreal : ↥(set_of fun (a : ennreal) => a < ⊤) ≃ₜ nnreal :=
  homeomorph.trans (homeomorph.set_congr sorry) ne_top_homeomorph_nnreal

theorem nhds_top : nhds ⊤ = infi fun (a : ennreal) => infi fun (H : a ≠ ⊤) => filter.principal (set.Ioi a) := sorry

theorem nhds_top' : nhds ⊤ = infi fun (r : nnreal) => filter.principal (set.Ioi ↑r) :=
  Eq.trans nhds_top (infi_ne_top fun (a : ennreal) => filter.principal (set.Ioi a))

theorem tendsto_nhds_top_iff_nnreal {α : Type u_1} {m : α → ennreal} {f : filter α} : filter.tendsto m f (nhds ⊤) ↔ ∀ (x : nnreal), filter.eventually (fun (a : α) => ↑x < m a) f := sorry

theorem tendsto_nhds_top_iff_nat {α : Type u_1} {m : α → ennreal} {f : filter α} : filter.tendsto m f (nhds ⊤) ↔ ∀ (n : ℕ), filter.eventually (fun (a : α) => ↑n < m a) f := sorry

theorem tendsto_nhds_top {α : Type u_1} {m : α → ennreal} {f : filter α} (h : ∀ (n : ℕ), filter.eventually (fun (a : α) => ↑n < m a) f) : filter.tendsto m f (nhds ⊤) :=
  iff.mpr tendsto_nhds_top_iff_nat h

theorem tendsto_nat_nhds_top : filter.tendsto (fun (n : ℕ) => ↑n) filter.at_top (nhds ⊤) := sorry

@[simp] theorem tendsto_coe_nhds_top {α : Type u_1} {f : α → nnreal} {l : filter α} : filter.tendsto (fun (x : α) => ↑(f x)) l (nhds ⊤) ↔ filter.tendsto f l filter.at_top := sorry

theorem nhds_zero : nhds 0 = infi fun (a : ennreal) => infi fun (H : a ≠ 0) => filter.principal (set.Iio a) := sorry

instance nhds_within_Ioi_coe_ne_bot {r : nnreal} : filter.ne_bot (nhds_within (↑r) (set.Ioi ↑r)) :=
  nhds_within_Ioi_self_ne_bot' coe_lt_top

instance nhds_within_Ioi_zero_ne_bot : filter.ne_bot (nhds_within 0 (set.Ioi 0)) :=
  nhds_within_Ioi_coe_ne_bot

-- using Icc because

-- • don't have 'Ioo (x - ε) (x + ε) ∈ 𝓝 x' unless x > 0

-- • (x - y ≤ ε ↔ x ≤ ε + y) is true, while (x - y < ε ↔ x < ε + y) is not

theorem Icc_mem_nhds {x : ennreal} {ε : ennreal} : x ≠ ⊤ → 0 < ε → set.Icc (x - ε) (x + ε) ∈ nhds x := sorry

theorem nhds_of_ne_top {x : ennreal} : x ≠ ⊤ → nhds x = infi fun (ε : ennreal) => infi fun (H : ε > 0) => filter.principal (set.Icc (x - ε) (x + ε)) := sorry

/-- Characterization of neighborhoods for `ennreal` numbers. See also `tendsto_order`
for a version with strict inequalities. -/
protected theorem tendsto_nhds {α : Type u_1} {f : filter α} {u : α → ennreal} {a : ennreal} (ha : a ≠ ⊤) : filter.tendsto u f (nhds a) ↔
  ∀ (ε : ennreal), ε > 0 → filter.eventually (fun (x : α) => u x ∈ set.Icc (a - ε) (a + ε)) f := sorry

protected theorem tendsto_at_top {β : Type u_2} [Nonempty β] [semilattice_sup β] {f : β → ennreal} {a : ennreal} (ha : a ≠ ⊤) : filter.tendsto f filter.at_top (nhds a) ↔
  ∀ (ε : ennreal), ε > 0 → ∃ (N : β), ∀ (n : β), n ≥ N → f n ∈ set.Icc (a - ε) (a + ε) := sorry

protected instance has_continuous_add : has_continuous_add ennreal := sorry

protected theorem tendsto_mul {a : ennreal} {b : ennreal} (ha : a ≠ 0 ∨ b ≠ ⊤) (hb : b ≠ 0 ∨ a ≠ ⊤) : filter.tendsto (fun (p : ennreal × ennreal) => prod.fst p * prod.snd p) (nhds (a, b)) (nhds (a * b)) := sorry

protected theorem tendsto.mul {α : Type u_1} {f : filter α} {ma : α → ennreal} {mb : α → ennreal} {a : ennreal} {b : ennreal} (hma : filter.tendsto ma f (nhds a)) (ha : a ≠ 0 ∨ b ≠ ⊤) (hmb : filter.tendsto mb f (nhds b)) (hb : b ≠ 0 ∨ a ≠ ⊤) : filter.tendsto (fun (a : α) => ma a * mb a) f (nhds (a * b)) := sorry

protected theorem tendsto.const_mul {α : Type u_1} {f : filter α} {m : α → ennreal} {a : ennreal} {b : ennreal} (hm : filter.tendsto m f (nhds b)) (hb : b ≠ 0 ∨ a ≠ ⊤) : filter.tendsto (fun (b : α) => a * m b) f (nhds (a * b)) := sorry

protected theorem tendsto.mul_const {α : Type u_1} {f : filter α} {m : α → ennreal} {a : ennreal} {b : ennreal} (hm : filter.tendsto m f (nhds a)) (ha : a ≠ 0 ∨ b ≠ ⊤) : filter.tendsto (fun (x : α) => m x * b) f (nhds (a * b)) := sorry

protected theorem continuous_at_const_mul {a : ennreal} {b : ennreal} (h : a ≠ ⊤ ∨ b ≠ 0) : continuous_at (Mul.mul a) b :=
  tendsto.const_mul filter.tendsto_id (or.symm h)

protected theorem continuous_at_mul_const {a : ennreal} {b : ennreal} (h : a ≠ ⊤ ∨ b ≠ 0) : continuous_at (fun (x : ennreal) => x * a) b :=
  tendsto.mul_const filter.tendsto_id (or.symm h)

protected theorem continuous_const_mul {a : ennreal} (ha : a ≠ ⊤) : continuous (Mul.mul a) :=
  iff.mpr continuous_iff_continuous_at fun (x : ennreal) => ennreal.continuous_at_const_mul (Or.inl ha)

protected theorem continuous_mul_const {a : ennreal} (ha : a ≠ ⊤) : continuous fun (x : ennreal) => x * a :=
  iff.mpr continuous_iff_continuous_at fun (x : ennreal) => ennreal.continuous_at_mul_const (Or.inl ha)

theorem le_of_forall_lt_one_mul_le {x : ennreal} {y : ennreal} (h : ∀ (a : ennreal), a < 1 → a * x ≤ y) : x ≤ y := sorry

theorem infi_mul_left {ι : Sort u_1} [Nonempty ι] {f : ι → ennreal} {a : ennreal} (h : a = ⊤ → (infi fun (i : ι) => f i) = 0 → ∃ (i : ι), f i = 0) : (infi fun (i : ι) => a * f i) = a * infi fun (i : ι) => f i := sorry

theorem infi_mul_right {ι : Sort u_1} [Nonempty ι] {f : ι → ennreal} {a : ennreal} (h : a = ⊤ → (infi fun (i : ι) => f i) = 0 → ∃ (i : ι), f i = 0) : (infi fun (i : ι) => f i * a) = (infi fun (i : ι) => f i) * a := sorry

protected theorem continuous_inv : continuous has_inv.inv := sorry

@[simp] protected theorem tendsto_inv_iff {α : Type u_1} {f : filter α} {m : α → ennreal} {a : ennreal} : filter.tendsto (fun (x : α) => m x⁻¹) f (nhds (a⁻¹)) ↔ filter.tendsto m f (nhds a) := sorry

protected theorem tendsto.div {α : Type u_1} {f : filter α} {ma : α → ennreal} {mb : α → ennreal} {a : ennreal} {b : ennreal} (hma : filter.tendsto ma f (nhds a)) (ha : a ≠ 0 ∨ b ≠ 0) (hmb : filter.tendsto mb f (nhds b)) (hb : b ≠ ⊤ ∨ a ≠ ⊤) : filter.tendsto (fun (a : α) => ma a / mb a) f (nhds (a / b)) := sorry

protected theorem tendsto.const_div {α : Type u_1} {f : filter α} {m : α → ennreal} {a : ennreal} {b : ennreal} (hm : filter.tendsto m f (nhds b)) (hb : b ≠ ⊤ ∨ a ≠ ⊤) : filter.tendsto (fun (b : α) => a / m b) f (nhds (a / b)) := sorry

protected theorem tendsto.div_const {α : Type u_1} {f : filter α} {m : α → ennreal} {a : ennreal} {b : ennreal} (hm : filter.tendsto m f (nhds a)) (ha : a ≠ 0 ∨ b ≠ 0) : filter.tendsto (fun (x : α) => m x / b) f (nhds (a / b)) := sorry

protected theorem tendsto_inv_nat_nhds_zero : filter.tendsto (fun (n : ℕ) => ↑n⁻¹) filter.at_top (nhds 0) :=
  inv_top ▸ iff.mpr ennreal.tendsto_inv_iff tendsto_nat_nhds_top

theorem bsupr_add {a : ennreal} {ι : Type u_1} {s : set ι} (hs : set.nonempty s) {f : ι → ennreal} : (supr fun (i : ι) => supr fun (H : i ∈ s) => f i) + a = supr fun (i : ι) => supr fun (H : i ∈ s) => f i + a := sorry

theorem Sup_add {a : ennreal} {s : set ennreal} (hs : set.nonempty s) : Sup s + a = supr fun (b : ennreal) => supr fun (H : b ∈ s) => b + a := sorry

theorem supr_add {a : ennreal} {ι : Sort u_1} {s : ι → ennreal} [h : Nonempty ι] : supr s + a = supr fun (b : ι) => s b + a := sorry

theorem add_supr {a : ennreal} {ι : Sort u_1} {s : ι → ennreal} [h : Nonempty ι] : a + supr s = supr fun (b : ι) => a + s b := sorry

theorem supr_add_supr {ι : Sort u_1} {f : ι → ennreal} {g : ι → ennreal} (h : ∀ (i j : ι), ∃ (k : ι), f i + g j ≤ f k + g k) : supr f + supr g = supr fun (a : ι) => f a + g a := sorry

theorem supr_add_supr_of_monotone {ι : Type u_1} [semilattice_sup ι] {f : ι → ennreal} {g : ι → ennreal} (hf : monotone f) (hg : monotone g) : supr f + supr g = supr fun (a : ι) => f a + g a :=
  supr_add_supr fun (i j : ι) => Exists.intro (i ⊔ j) (add_le_add (hf le_sup_left) (hg le_sup_right))

theorem finset_sum_supr_nat {α : Type u_1} {ι : Type u_2} [semilattice_sup ι] {s : finset α} {f : α → ι → ennreal} (hf : ∀ (a : α), monotone (f a)) : (finset.sum s fun (a : α) => supr (f a)) = supr fun (n : ι) => finset.sum s fun (a : α) => f a n := sorry

theorem mul_Sup {s : set ennreal} {a : ennreal} : a * Sup s = supr fun (i : ennreal) => supr fun (H : i ∈ s) => a * i := sorry

theorem mul_supr {ι : Sort u_1} {f : ι → ennreal} {a : ennreal} : a * supr f = supr fun (i : ι) => a * f i := sorry

theorem supr_mul {ι : Sort u_1} {f : ι → ennreal} {a : ennreal} : supr f * a = supr fun (i : ι) => f i * a := sorry

protected theorem tendsto_coe_sub {r : nnreal} {b : ennreal} : filter.tendsto (fun (b : ennreal) => ↑r - b) (nhds b) (nhds (↑r - b)) := sorry

theorem sub_supr {a : ennreal} {ι : Sort u_1} [hι : Nonempty ι] {b : ι → ennreal} (hr : a < ⊤) : (a - supr fun (i : ι) => b i) = infi fun (i : ι) => a - b i := sorry

theorem supr_eq_zero {ι : Sort u_1} {f : ι → ennreal} : (supr fun (i : ι) => f i) = 0 ↔ ∀ (i : ι), f i = 0 := sorry

protected theorem has_sum_coe {α : Type u_1} {f : α → nnreal} {r : nnreal} : has_sum (fun (a : α) => ↑(f a)) ↑r ↔ has_sum f r := sorry

protected theorem tsum_coe_eq {α : Type u_1} {r : nnreal} {f : α → nnreal} (h : has_sum f r) : (tsum fun (a : α) => ↑(f a)) = ↑r :=
  has_sum.tsum_eq (iff.mpr ennreal.has_sum_coe h)

protected theorem coe_tsum {α : Type u_1} {f : α → nnreal} : summable f → ↑(tsum f) = tsum fun (a : α) => ↑(f a) := sorry

protected theorem has_sum {α : Type u_1} {f : α → ennreal} : has_sum f (supr fun (s : finset α) => finset.sum s fun (a : α) => f a) :=
  tendsto_at_top_supr fun (s t : finset α) => finset.sum_le_sum_of_subset

@[simp] protected theorem summable {α : Type u_1} {f : α → ennreal} : summable f :=
  Exists.intro (supr fun (s : finset α) => finset.sum s fun (a : α) => f a) ennreal.has_sum

theorem tsum_coe_ne_top_iff_summable {β : Type u_2} {f : β → nnreal} : (tsum fun (b : β) => ↑(f b)) ≠ ⊤ ↔ summable f := sorry

protected theorem tsum_eq_supr_sum {α : Type u_1} {f : α → ennreal} : (tsum fun (a : α) => f a) = supr fun (s : finset α) => finset.sum s fun (a : α) => f a :=
  has_sum.tsum_eq ennreal.has_sum

protected theorem tsum_eq_supr_sum' {α : Type u_1} {f : α → ennreal} {ι : Type u_2} (s : ι → finset α) (hs : ∀ (t : finset α), ∃ (i : ι), t ⊆ s i) : (tsum fun (a : α) => f a) = supr fun (i : ι) => finset.sum (s i) fun (a : α) => f a := sorry

protected theorem tsum_sigma {α : Type u_1} {β : α → Type u_2} (f : (a : α) → β a → ennreal) : (tsum fun (p : sigma fun (a : α) => β a) => f (sigma.fst p) (sigma.snd p)) =
  tsum fun (a : α) => tsum fun (b : β a) => f a b :=
  tsum_sigma' (fun (b : α) => ennreal.summable) ennreal.summable

protected theorem tsum_sigma' {α : Type u_1} {β : α → Type u_2} (f : (sigma fun (a : α) => β a) → ennreal) : (tsum fun (p : sigma fun (a : α) => β a) => f p) = tsum fun (a : α) => tsum fun (b : β a) => f (sigma.mk a b) :=
  tsum_sigma' (fun (b : α) => ennreal.summable) ennreal.summable

protected theorem tsum_prod {α : Type u_1} {β : Type u_2} {f : α → β → ennreal} : (tsum fun (p : α × β) => f (prod.fst p) (prod.snd p)) = tsum fun (a : α) => tsum fun (b : β) => f a b :=
  tsum_prod' ennreal.summable fun (_x : α) => ennreal.summable

protected theorem tsum_comm {α : Type u_1} {β : Type u_2} {f : α → β → ennreal} : (tsum fun (a : α) => tsum fun (b : β) => f a b) = tsum fun (b : β) => tsum fun (a : α) => f a b :=
  tsum_comm' ennreal.summable (fun (_x : β) => ennreal.summable) fun (_x : α) => ennreal.summable

protected theorem tsum_add {α : Type u_1} {f : α → ennreal} {g : α → ennreal} : (tsum fun (a : α) => f a + g a) = (tsum fun (a : α) => f a) + tsum fun (a : α) => g a :=
  tsum_add ennreal.summable ennreal.summable

protected theorem tsum_le_tsum {α : Type u_1} {f : α → ennreal} {g : α → ennreal} (h : ∀ (a : α), f a ≤ g a) : (tsum fun (a : α) => f a) ≤ tsum fun (a : α) => g a :=
  tsum_le_tsum h ennreal.summable ennreal.summable

protected theorem sum_le_tsum {α : Type u_1} {f : α → ennreal} (s : finset α) : (finset.sum s fun (x : α) => f x) ≤ tsum fun (x : α) => f x :=
  sum_le_tsum s (fun (x : α) (hx : ¬x ∈ s) => zero_le (f x)) ennreal.summable

protected theorem tsum_eq_supr_nat' {f : ℕ → ennreal} {N : ℕ → ℕ} (hN : filter.tendsto N filter.at_top filter.at_top) : (tsum fun (i : ℕ) => f i) = supr fun (i : ℕ) => finset.sum (finset.range (N i)) fun (i : ℕ) => f i := sorry

protected theorem tsum_eq_supr_nat {f : ℕ → ennreal} : (tsum fun (i : ℕ) => f i) = supr fun (i : ℕ) => finset.sum (finset.range i) fun (i : ℕ) => f i :=
  ennreal.tsum_eq_supr_sum' (fun (i : ℕ) => finset.range i) finset.exists_nat_subset_range

protected theorem le_tsum {α : Type u_1} {f : α → ennreal} (a : α) : f a ≤ tsum fun (a : α) => f a :=
  le_tsum' ennreal.summable a

protected theorem tsum_eq_top_of_eq_top {α : Type u_1} {f : α → ennreal} : (∃ (a : α), f a = ⊤) → (tsum fun (a : α) => f a) = ⊤ :=
  fun (ᾰ : ∃ (a : α), f a = ⊤) =>
    Exists.dcases_on ᾰ
      fun (ᾰ_w : α) (ᾰ_h : f ᾰ_w = ⊤) => idRhs ((tsum fun (a : α) => f a) = ⊤) (top_unique (ᾰ_h ▸ ennreal.le_tsum ᾰ_w))

protected theorem ne_top_of_tsum_ne_top {α : Type u_1} {f : α → ennreal} (h : (tsum fun (a : α) => f a) ≠ ⊤) (a : α) : f a ≠ ⊤ :=
  fun (ha : f a = ⊤) => h (ennreal.tsum_eq_top_of_eq_top (Exists.intro a ha))

protected theorem tsum_mul_left {α : Type u_1} {a : ennreal} {f : α → ennreal} : (tsum fun (i : α) => a * f i) = a * tsum fun (i : α) => f i := sorry

protected theorem tsum_mul_right {α : Type u_1} {a : ennreal} {f : α → ennreal} : (tsum fun (i : α) => f i * a) = (tsum fun (i : α) => f i) * a := sorry

@[simp] theorem tsum_supr_eq {α : Type u_1} (a : α) {f : α → ennreal} : (tsum fun (b : α) => supr fun (h : a = b) => f b) = f a := sorry

theorem has_sum_iff_tendsto_nat {f : ℕ → ennreal} (r : ennreal) : has_sum f r ↔ filter.tendsto (fun (n : ℕ) => finset.sum (finset.range n) fun (i : ℕ) => f i) filter.at_top (nhds r) := sorry

theorem to_nnreal_apply_of_tsum_ne_top {α : Type u_1} {f : α → ennreal} (hf : (tsum fun (i : α) => f i) ≠ ⊤) (x : α) : ↑(function.comp ennreal.to_nnreal f x) = f x :=
  coe_to_nnreal (ennreal.ne_top_of_tsum_ne_top hf x)

theorem summable_to_nnreal_of_tsum_ne_top {α : Type u_1} {f : α → ennreal} (hf : (tsum fun (i : α) => f i) ≠ ⊤) : summable (ennreal.to_nnreal ∘ f) := sorry

protected theorem tsum_apply {ι : Type u_1} {α : Type u_2} {f : ι → α → ennreal} {x : α} : tsum (fun (i : ι) => f i) x = tsum fun (i : ι) => f i x :=
  tsum_apply (iff.mpr pi.summable fun (_x : α) => ennreal.summable)

theorem tsum_sub {f : ℕ → ennreal} {g : ℕ → ennreal} (h₁ : (tsum fun (i : ℕ) => g i) < ⊤) (h₂ : g ≤ f) : (tsum fun (i : ℕ) => f i - g i) = (tsum fun (i : ℕ) => f i) - tsum fun (i : ℕ) => g i := sorry

end ennreal


namespace nnreal


/-- Comparison test of convergence of `ℝ≥0`-valued series. -/
theorem exists_le_has_sum_of_le {β : Type u_2} {f : β → nnreal} {g : β → nnreal} {r : nnreal} (hgf : ∀ (b : β), g b ≤ f b) (hfr : has_sum f r) : ∃ (p : nnreal), ∃ (H : p ≤ r), has_sum g p := sorry

/-- Comparison test of convergence of `ℝ≥0`-valued series. -/
theorem summable_of_le {β : Type u_2} {f : β → nnreal} {g : β → nnreal} (hgf : ∀ (b : β), g b ≤ f b) : summable f → summable g := sorry

/-- A series of non-negative real numbers converges to `r` in the sense of `has_sum` if and only if
the sequence of partial sum converges to `r`. -/
theorem has_sum_iff_tendsto_nat {f : ℕ → nnreal} {r : nnreal} : has_sum f r ↔ filter.tendsto (fun (n : ℕ) => finset.sum (finset.range n) fun (i : ℕ) => f i) filter.at_top (nhds r) := sorry

theorem not_summable_iff_tendsto_nat_at_top {f : ℕ → nnreal} : ¬summable f ↔ filter.tendsto (fun (n : ℕ) => finset.sum (finset.range n) fun (i : ℕ) => f i) filter.at_top filter.at_top := sorry

theorem summable_iff_not_tendsto_nat_at_top {f : ℕ → nnreal} : summable f ↔ ¬filter.tendsto (fun (n : ℕ) => finset.sum (finset.range n) fun (i : ℕ) => f i) filter.at_top filter.at_top := sorry

theorem summable_of_sum_range_le {f : ℕ → nnreal} {c : nnreal} (h : ∀ (n : ℕ), (finset.sum (finset.range n) fun (i : ℕ) => f i) ≤ c) : summable f := sorry

theorem tsum_le_of_sum_range_le {f : ℕ → nnreal} {c : nnreal} (h : ∀ (n : ℕ), (finset.sum (finset.range n) fun (i : ℕ) => f i) ≤ c) : (tsum fun (i : ℕ) => f i) ≤ c :=
  le_of_tendsto' (iff.mp has_sum_iff_tendsto_nat (summable.has_sum (summable_of_sum_range_le h))) h

theorem tsum_comp_le_tsum_of_inj {α : Type u_1} {β : Type u_2} {f : α → nnreal} (hf : summable f) {i : β → α} (hi : function.injective i) : (tsum fun (x : β) => f (i x)) ≤ tsum fun (x : α) => f x :=
  tsum_le_tsum_of_inj i hi (fun (c : α) (hc : ¬c ∈ set.range i) => zero_le (f c)) (fun (b : β) => le_refl (f (i b)))
    (summable_comp_injective hf hi) hf

theorem summable_sigma {α : Type u_1} {β : α → Type u_2} {f : (sigma fun (x : α) => β x) → nnreal} : summable f ↔
  (∀ (x : α), summable fun (y : β x) => f (sigma.mk x y)) ∧
    summable fun (x : α) => tsum fun (y : β x) => f (sigma.mk x y) := sorry

/-- For `f : ℕ → ℝ≥0`, then `∑' k, f (k + i)` tends to zero. This does not require a summability
assumption on `f`, as otherwise all sums are zero. -/
theorem tendsto_sum_nat_add (f : ℕ → nnreal) : filter.tendsto (fun (i : ℕ) => tsum fun (k : ℕ) => f (k + i)) filter.at_top (nhds 0) := sorry

end nnreal


namespace ennreal


theorem tendsto_sum_nat_add (f : ℕ → ennreal) (hf : (tsum fun (i : ℕ) => f i) ≠ ⊤) : filter.tendsto (fun (i : ℕ) => tsum fun (k : ℕ) => f (k + i)) filter.at_top (nhds 0) := sorry

end ennreal


theorem tsum_comp_le_tsum_of_inj {α : Type u_1} {β : Type u_2} {f : α → ℝ} (hf : summable f) (hn : ∀ (a : α), 0 ≤ f a) {i : β → α} (hi : function.injective i) : tsum (f ∘ i) ≤ tsum f := sorry

/-- Comparison test of convergence of series of non-negative real numbers. -/
theorem summable_of_nonneg_of_le {β : Type u_2} {f : β → ℝ} {g : β → ℝ} (hg : ∀ (b : β), 0 ≤ g b) (hgf : ∀ (b : β), g b ≤ f b) (hf : summable f) : summable g := sorry

/-- A series of non-negative real numbers converges to `r` in the sense of `has_sum` if and only if
the sequence of partial sum converges to `r`. -/
theorem has_sum_iff_tendsto_nat_of_nonneg {f : ℕ → ℝ} (hf : ∀ (i : ℕ), 0 ≤ f i) (r : ℝ) : has_sum f r ↔ filter.tendsto (fun (n : ℕ) => finset.sum (finset.range n) fun (i : ℕ) => f i) filter.at_top (nhds r) := sorry

theorem ennreal.of_real_tsum_of_nonneg {α : Type u_1} {f : α → ℝ} (hf_nonneg : ∀ (n : α), 0 ≤ f n) (hf : summable f) : ennreal.of_real (tsum fun (n : α) => f n) = tsum fun (n : α) => ennreal.of_real (f n) := sorry

theorem not_summable_iff_tendsto_nat_at_top_of_nonneg {f : ℕ → ℝ} (hf : ∀ (n : ℕ), 0 ≤ f n) : ¬summable f ↔ filter.tendsto (fun (n : ℕ) => finset.sum (finset.range n) fun (i : ℕ) => f i) filter.at_top filter.at_top := sorry

theorem summable_iff_not_tendsto_nat_at_top_of_nonneg {f : ℕ → ℝ} (hf : ∀ (n : ℕ), 0 ≤ f n) : summable f ↔ ¬filter.tendsto (fun (n : ℕ) => finset.sum (finset.range n) fun (i : ℕ) => f i) filter.at_top filter.at_top := sorry

theorem summable_sigma_of_nonneg {α : Type u_1} {β : α → Type u_2} {f : (sigma fun (x : α) => β x) → ℝ} (hf : ∀ (x : sigma fun (x : α) => β x), 0 ≤ f x) : summable f ↔
  (∀ (x : α), summable fun (y : β x) => f (sigma.mk x y)) ∧
    summable fun (x : α) => tsum fun (y : β x) => f (sigma.mk x y) := sorry

theorem summable_of_sum_range_le {f : ℕ → ℝ} {c : ℝ} (hf : ∀ (n : ℕ), 0 ≤ f n) (h : ∀ (n : ℕ), (finset.sum (finset.range n) fun (i : ℕ) => f i) ≤ c) : summable f := sorry

theorem tsum_le_of_sum_range_le {f : ℕ → ℝ} {c : ℝ} (hf : ∀ (n : ℕ), 0 ≤ f n) (h : ∀ (n : ℕ), (finset.sum (finset.range n) fun (i : ℕ) => f i) ≤ c) : (tsum fun (i : ℕ) => f i) ≤ c := sorry

/-- In an emetric ball, the distance between points is everywhere finite -/
theorem edist_ne_top_of_mem_ball {β : Type u_2} [emetric_space β] {a : β} {r : ennreal} (x : ↥(emetric.ball a r)) (y : ↥(emetric.ball a r)) : edist (subtype.val x) (subtype.val y) ≠ ⊤ := sorry

/-- Each ball in an extended metric space gives us a metric space, as the edist
is everywhere finite. -/
def metric_space_emetric_ball {β : Type u_2} [emetric_space β] (a : β) (r : ennreal) : metric_space ↥(emetric.ball a r) :=
  emetric_space.to_metric_space edist_ne_top_of_mem_ball

theorem nhds_eq_nhds_emetric_ball {β : Type u_2} [emetric_space β] (a : β) (x : β) (r : ennreal) (h : x ∈ emetric.ball a r) : nhds x = filter.map coe (nhds { val := x, property := h }) :=
  Eq.symm (map_nhds_subtype_coe_eq h (mem_nhds_sets emetric.is_open_ball h))

theorem tendsto_iff_edist_tendsto_0 {α : Type u_1} {β : Type u_2} [emetric_space α] {l : filter β} {f : β → α} {y : α} : filter.tendsto f l (nhds y) ↔ filter.tendsto (fun (x : β) => edist (f x) y) l (nhds 0) := sorry

/-- Yet another metric characterization of Cauchy sequences on integers. This one is often the
most efficient. -/
theorem emetric.cauchy_seq_iff_le_tendsto_0 {α : Type u_1} {β : Type u_2} [emetric_space α] [Nonempty β] [semilattice_sup β] {s : β → α} : cauchy_seq s ↔
  ∃ (b : β → ennreal),
    (∀ (n m N : β), N ≤ n → N ≤ m → edist (s n) (s m) ≤ b N) ∧ filter.tendsto b filter.at_top (nhds 0) := sorry

theorem continuous_of_le_add_edist {α : Type u_1} [emetric_space α] {f : α → ennreal} (C : ennreal) (hC : C ≠ ⊤) (h : ∀ (x y : α), f x ≤ f y + C * edist x y) : continuous f := sorry

theorem continuous_edist {α : Type u_1} [emetric_space α] : continuous fun (p : α × α) => edist (prod.fst p) (prod.snd p) := sorry

theorem continuous.edist {α : Type u_1} {β : Type u_2} [emetric_space α] [topological_space β] {f : β → α} {g : β → α} (hf : continuous f) (hg : continuous g) : continuous fun (b : β) => edist (f b) (g b) :=
  continuous.comp continuous_edist (continuous.prod_mk hf hg)

theorem filter.tendsto.edist {α : Type u_1} {β : Type u_2} [emetric_space α] {f : β → α} {g : β → α} {x : filter β} {a : α} {b : α} (hf : filter.tendsto f x (nhds a)) (hg : filter.tendsto g x (nhds b)) : filter.tendsto (fun (x : β) => edist (f x) (g x)) x (nhds (edist a b)) :=
  filter.tendsto.comp (continuous.tendsto continuous_edist (a, b)) (filter.tendsto.prod_mk_nhds hf hg)

theorem cauchy_seq_of_edist_le_of_tsum_ne_top {α : Type u_1} [emetric_space α] {f : ℕ → α} (d : ℕ → ennreal) (hf : ∀ (n : ℕ), edist (f n) (f (Nat.succ n)) ≤ d n) (hd : tsum d ≠ ⊤) : cauchy_seq f := sorry

theorem emetric.is_closed_ball {α : Type u_1} [emetric_space α] {a : α} {r : ennreal} : is_closed (emetric.closed_ball a r) :=
  is_closed_le (continuous.edist continuous_id continuous_const) continuous_const

/-- If `edist (f n) (f (n+1))` is bounded above by a function `d : ℕ → ennreal`,
then the distance from `f n` to the limit is bounded by `∑'_{k=n}^∞ d k`. -/
theorem edist_le_tsum_of_edist_le_of_tendsto {α : Type u_1} [emetric_space α] {f : ℕ → α} (d : ℕ → ennreal) (hf : ∀ (n : ℕ), edist (f n) (f (Nat.succ n)) ≤ d n) {a : α} (ha : filter.tendsto f filter.at_top (nhds a)) (n : ℕ) : edist (f n) a ≤ tsum fun (m : ℕ) => d (n + m) := sorry

/-- If `edist (f n) (f (n+1))` is bounded above by a function `d : ℕ → ennreal`,
then the distance from `f 0` to the limit is bounded by `∑'_{k=0}^∞ d k`. -/
theorem edist_le_tsum_of_edist_le_of_tendsto₀ {α : Type u_1} [emetric_space α] {f : ℕ → α} (d : ℕ → ennreal) (hf : ∀ (n : ℕ), edist (f n) (f (Nat.succ n)) ≤ d n) {a : α} (ha : filter.tendsto f filter.at_top (nhds a)) : edist (f 0) a ≤ tsum fun (m : ℕ) => d m := sorry

