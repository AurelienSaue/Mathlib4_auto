/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

Nonnegative real numbers.
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.topology.algebra.infinite_sum
import Mathlib.topology.algebra.group_with_zero
import PostPort

universes u_1 u_2 

namespace Mathlib

namespace nnreal


protected instance topological_space : topological_space nnreal :=
  infer_instance

protected instance topological_semiring : topological_semiring nnreal :=
  topological_semiring.mk

protected instance topological_space.second_countable_topology : topological_space.second_countable_topology nnreal :=
  topological_space.subtype.second_countable_topology ℝ fun (r : ℝ) => real.le 0 r

protected instance order_topology : order_topology nnreal :=
  Mathlib.order_topology_of_ord_connected

theorem continuous_of_real : continuous nnreal.of_real :=
  continuous_subtype_mk (fun (r : ℝ) => of_real._proof_1 r) (continuous.max continuous_id continuous_const)

theorem continuous_coe : continuous coe :=
  continuous_subtype_val

@[simp] theorem tendsto_coe {α : Type u_1} {f : filter α} {m : α → nnreal} {x : nnreal} : filter.tendsto (fun (a : α) => ↑(m a)) f (nhds ↑x) ↔ filter.tendsto m f (nhds x) :=
  iff.symm tendsto_subtype_rng

theorem tendsto_coe' {α : Type u_1} {f : filter α} [filter.ne_bot f] {m : α → nnreal} {x : ℝ} : filter.tendsto (fun (a : α) => ↑(m a)) f (nhds x) ↔
  ∃ (hx : 0 ≤ x), filter.tendsto m f (nhds { val := x, property := hx }) := sorry

@[simp] theorem map_coe_at_top : filter.map coe filter.at_top = filter.at_top :=
  filter.map_coe_Ici_at_top 0

theorem comap_coe_at_top : filter.comap coe filter.at_top = filter.at_top :=
  Eq.symm (filter.at_top_Ici_eq 0)

@[simp] theorem tendsto_coe_at_top {α : Type u_1} {f : filter α} {m : α → nnreal} : filter.tendsto (fun (a : α) => ↑(m a)) f filter.at_top ↔ filter.tendsto m f filter.at_top :=
  iff.symm filter.tendsto_Ici_at_top

theorem tendsto_of_real {α : Type u_1} {f : filter α} {m : α → ℝ} {x : ℝ} (h : filter.tendsto m f (nhds x)) : filter.tendsto (fun (a : α) => nnreal.of_real (m a)) f (nhds (nnreal.of_real x)) :=
  filter.tendsto.comp (continuous.tendsto continuous_of_real x) h

protected instance has_continuous_sub : has_continuous_sub nnreal :=
  has_continuous_sub.mk
    (continuous_subtype_mk (fun (p : nnreal × nnreal) => of_real._proof_1 (↑(prod.fst p) - ↑(prod.snd p)))
      (continuous.max
        (continuous.sub (continuous.comp continuous_coe continuous_fst) (continuous.comp continuous_coe continuous_snd))
        continuous_const))

protected instance has_continuous_inv' : has_continuous_inv' nnreal :=
  has_continuous_inv'.mk sorry

theorem has_sum_coe {α : Type u_1} {f : α → nnreal} {r : nnreal} : has_sum (fun (a : α) => ↑(f a)) ↑r ↔ has_sum f r := sorry

theorem has_sum_of_real_of_nonneg {α : Type u_1} {f : α → ℝ} (hf_nonneg : ∀ (n : α), 0 ≤ f n) (hf : summable f) : has_sum (fun (n : α) => nnreal.of_real (f n)) (nnreal.of_real (tsum fun (n : α) => f n)) := sorry

theorem summable_coe {α : Type u_1} {f : α → nnreal} : (summable fun (a : α) => ↑(f a)) ↔ summable f := sorry

theorem coe_tsum {α : Type u_1} {f : α → nnreal} : ↑(tsum fun (a : α) => f a) = tsum fun (a : α) => ↑(f a) := sorry

theorem tsum_mul_left {α : Type u_1} (a : nnreal) (f : α → nnreal) : (tsum fun (x : α) => a * f x) = a * tsum fun (x : α) => f x := sorry

theorem tsum_mul_right {α : Type u_1} (f : α → nnreal) (a : nnreal) : (tsum fun (x : α) => f x * a) = (tsum fun (x : α) => f x) * a := sorry

theorem summable_comp_injective {α : Type u_1} {β : Type u_2} {f : α → nnreal} (hf : summable f) {i : β → α} (hi : function.injective i) : summable (f ∘ i) :=
  iff.mp summable_coe
    ((fun (this : summable ((coe ∘ f) ∘ i)) => this) (summable.comp_injective (iff.mpr summable_coe hf) hi))

theorem summable_nat_add (f : ℕ → nnreal) (hf : summable f) (k : ℕ) : summable fun (i : ℕ) => f (i + k) :=
  summable_comp_injective hf (add_left_injective k)

theorem summable_nat_add_iff {f : ℕ → nnreal} (k : ℕ) : (summable fun (i : ℕ) => f (i + k)) ↔ summable f := sorry

theorem sum_add_tsum_nat_add {f : ℕ → nnreal} (k : ℕ) (hf : summable f) : (tsum fun (i : ℕ) => f i) = (finset.sum (finset.range k) fun (i : ℕ) => f i) + tsum fun (i : ℕ) => f (i + k) := sorry

theorem infi_real_pos_eq_infi_nnreal_pos {α : Type u_1} [complete_lattice α] {f : ℝ → α} : (infi fun (n : ℝ) => infi fun (h : 0 < n) => f n) = infi fun (n : nnreal) => infi fun (h : 0 < n) => f ↑n := sorry

