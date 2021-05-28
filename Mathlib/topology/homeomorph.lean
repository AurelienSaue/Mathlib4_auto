/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Sébastien Gouëzel, Zhouhang Zhou, Reid Barton
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.dense_embedding
import Mathlib.PostPort

universes u_5 u_6 l u_1 u_2 u_3 u_4 u v 

namespace Mathlib

/-- Homeomorphism between `α` and `β`, also called topological isomorphism -/
structure homeomorph (α : Type u_5) (β : Type u_6) [topological_space α] [topological_space β] 
extends α ≃ β
where
  continuous_to_fun : autoParam (continuous (equiv.to_fun _to_equiv))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.tactic.interactive.continuity'")
    (Lean.Name.mkStr
      (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "tactic") "interactive")
      "continuity'")
    [])
  continuous_inv_fun : autoParam (continuous (equiv.inv_fun _to_equiv))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.tactic.interactive.continuity'")
    (Lean.Name.mkStr
      (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "tactic") "interactive")
      "continuity'")
    [])

infixl:25 " ≃ₜ " => Mathlib.homeomorph

namespace homeomorph


protected instance has_coe_to_fun {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] : has_coe_to_fun (α ≃ₜ β) :=
  has_coe_to_fun.mk (fun (_x : α ≃ₜ β) => α → β) fun (e : α ≃ₜ β) => ⇑(to_equiv e)

@[simp] theorem homeomorph_mk_coe {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (a : α ≃ β) (b : autoParam (continuous (equiv.to_fun a))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.tactic.interactive.continuity'")
    (Lean.Name.mkStr
      (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "tactic") "interactive")
      "continuity'")
    [])) (c : autoParam (continuous (equiv.inv_fun a))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.tactic.interactive.continuity'")
    (Lean.Name.mkStr
      (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "tactic") "interactive")
      "continuity'")
    [])) : ⇑(mk a) = ⇑a :=
  rfl

theorem coe_eq_to_equiv {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (h : α ≃ₜ β) (a : α) : coe_fn h a = coe_fn (to_equiv h) a :=
  rfl

theorem to_equiv_injective {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] : function.injective to_equiv := sorry

theorem ext {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {h : α ≃ₜ β} {h' : α ≃ₜ β} (H : ∀ (x : α), coe_fn h x = coe_fn h' x) : h = h' :=
  to_equiv_injective (equiv.ext H)

/-- Identity map as a homeomorphism. -/
protected def refl (α : Type u_1) [topological_space α] : α ≃ₜ α :=
  mk (equiv.mk (equiv.to_fun (equiv.refl α)) (equiv.inv_fun (equiv.refl α)) sorry sorry)

/-- Composition of two homeomorphisms. -/
protected def trans {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α] [topological_space β] [topological_space γ] (h₁ : α ≃ₜ β) (h₂ : β ≃ₜ γ) : α ≃ₜ γ :=
  mk
    (equiv.mk (equiv.to_fun (equiv.trans (to_equiv h₁) (to_equiv h₂)))
      (equiv.inv_fun (equiv.trans (to_equiv h₁) (to_equiv h₂))) sorry sorry)

/-- Inverse of a homeomorphism. -/
protected def symm {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (h : α ≃ₜ β) : β ≃ₜ α :=
  mk (equiv.mk (equiv.to_fun (equiv.symm (to_equiv h))) (equiv.inv_fun (equiv.symm (to_equiv h))) sorry sorry)

@[simp] theorem homeomorph_mk_coe_symm {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (a : α ≃ β) (b : autoParam (continuous (equiv.to_fun a))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.tactic.interactive.continuity'")
    (Lean.Name.mkStr
      (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "tactic") "interactive")
      "continuity'")
    [])) (c : autoParam (continuous (equiv.inv_fun a))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.tactic.interactive.continuity'")
    (Lean.Name.mkStr
      (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "tactic") "interactive")
      "continuity'")
    [])) : ⇑(homeomorph.symm (mk a)) = ⇑(equiv.symm a) :=
  rfl

protected theorem continuous {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (h : α ≃ₜ β) : continuous ⇑h :=
  continuous_to_fun h

@[simp] theorem apply_symm_apply {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (h : α ≃ₜ β) (x : β) : coe_fn h (coe_fn (homeomorph.symm h) x) = x :=
  equiv.apply_symm_apply (to_equiv h) x

@[simp] theorem symm_apply_apply {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (h : α ≃ₜ β) (x : α) : coe_fn (homeomorph.symm h) (coe_fn h x) = x :=
  equiv.symm_apply_apply (to_equiv h) x

protected theorem bijective {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (h : α ≃ₜ β) : function.bijective ⇑h :=
  equiv.bijective (to_equiv h)

protected theorem injective {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (h : α ≃ₜ β) : function.injective ⇑h :=
  equiv.injective (to_equiv h)

protected theorem surjective {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (h : α ≃ₜ β) : function.surjective ⇑h :=
  equiv.surjective (to_equiv h)

/-- Change the homeomorphism `f` to make the inverse function definitionally equal to `g`. -/
def change_inv {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (f : α ≃ₜ β) (g : β → α) (hg : function.right_inverse g ⇑f) : α ≃ₜ β :=
  (fun (this : g = ⇑(homeomorph.symm f)) => mk (equiv.mk (⇑f) g sorry sorry)) sorry

@[simp] theorem symm_comp_self {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (h : α ≃ₜ β) : ⇑(homeomorph.symm h) ∘ ⇑h = id :=
  funext (symm_apply_apply h)

@[simp] theorem self_comp_symm {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (h : α ≃ₜ β) : ⇑h ∘ ⇑(homeomorph.symm h) = id :=
  funext (apply_symm_apply h)

@[simp] theorem range_coe {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (h : α ≃ₜ β) : set.range ⇑h = set.univ :=
  function.surjective.range_eq (homeomorph.surjective h)

theorem image_symm {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (h : α ≃ₜ β) : set.image ⇑(homeomorph.symm h) = set.preimage ⇑h :=
  funext (equiv.image_eq_preimage (to_equiv (homeomorph.symm h)))

theorem preimage_symm {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (h : α ≃ₜ β) : set.preimage ⇑(homeomorph.symm h) = set.image ⇑h :=
  Eq.symm (funext (equiv.image_eq_preimage (to_equiv h)))

@[simp] theorem image_preimage {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (h : α ≃ₜ β) (s : set β) : ⇑h '' (⇑h ⁻¹' s) = s :=
  equiv.image_preimage (to_equiv h) s

@[simp] theorem preimage_image {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (h : α ≃ₜ β) (s : set α) : ⇑h ⁻¹' (⇑h '' s) = s :=
  equiv.preimage_image (to_equiv h) s

protected theorem inducing {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (h : α ≃ₜ β) : inducing ⇑h := sorry

theorem induced_eq {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (h : α ≃ₜ β) : topological_space.induced (⇑h) _inst_2 = _inst_1 :=
  Eq.symm (inducing.induced (homeomorph.inducing h))

protected theorem quotient_map {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (h : α ≃ₜ β) : quotient_map ⇑h := sorry

theorem coinduced_eq {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (h : α ≃ₜ β) : topological_space.coinduced (⇑h) _inst_1 = _inst_2 :=
  Eq.symm (and.right (homeomorph.quotient_map h))

protected theorem embedding {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (h : α ≃ₜ β) : embedding ⇑h :=
  embedding.mk (homeomorph.inducing h) (equiv.injective (to_equiv h))

theorem compact_image {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {s : set α} (h : α ≃ₜ β) : is_compact (⇑h '' s) ↔ is_compact s :=
  iff.symm (embedding.compact_iff_compact_image (homeomorph.embedding h))

theorem compact_preimage {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {s : set β} (h : α ≃ₜ β) : is_compact (⇑h ⁻¹' s) ↔ is_compact s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_compact (⇑h ⁻¹' s) ↔ is_compact s)) (Eq.symm (image_symm h))))
    (compact_image (homeomorph.symm h))

protected theorem dense_embedding {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (h : α ≃ₜ β) : dense_embedding ⇑h :=
  dense_embedding.mk
    (dense_inducing.mk (inducing.mk (Eq.symm (induced_eq h))) (function.surjective.dense_range (homeomorph.surjective h)))
    (homeomorph.injective h)

@[simp] theorem is_open_preimage {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (h : α ≃ₜ β) {s : set β} : is_open (⇑h ⁻¹' s) ↔ is_open s :=
  quotient_map.is_open_preimage (homeomorph.quotient_map h)

@[simp] theorem is_open_image {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (h : α ≃ₜ β) {s : set α} : is_open (⇑h '' s) ↔ is_open s := sorry

@[simp] theorem is_closed_preimage {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (h : α ≃ₜ β) {s : set β} : is_closed (⇑h ⁻¹' s) ↔ is_closed s := sorry

@[simp] theorem is_closed_image {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (h : α ≃ₜ β) {s : set α} : is_closed (⇑h '' s) ↔ is_closed s := sorry

theorem preimage_closure {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (h : α ≃ₜ β) (s : set β) : ⇑h ⁻¹' closure s = closure (⇑h ⁻¹' s) := sorry

theorem image_closure {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (h : α ≃ₜ β) (s : set α) : ⇑h '' closure s = closure (⇑h '' s) := sorry

protected theorem is_open_map {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (h : α ≃ₜ β) : is_open_map ⇑h :=
  fun (s : set α) => iff.mpr (is_open_image h)

protected theorem is_closed_map {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (h : α ≃ₜ β) : is_closed_map ⇑h :=
  fun (s : set α) => iff.mpr (is_closed_image h)

protected theorem closed_embedding {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (h : α ≃ₜ β) : closed_embedding ⇑h :=
  closed_embedding_of_embedding_closed (homeomorph.embedding h) (homeomorph.is_closed_map h)

@[simp] theorem map_nhds_eq {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (h : α ≃ₜ β) (x : α) : filter.map (⇑h) (nhds x) = nhds (coe_fn h x) := sorry

@[simp] theorem comap_nhds_eq {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (h : α ≃ₜ β) (y : β) : filter.comap (⇑h) (nhds y) = nhds (coe_fn (homeomorph.symm h) y) := sorry

theorem nhds_eq_comap {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (h : α ≃ₜ β) (x : α) : nhds x = filter.comap (⇑h) (nhds (coe_fn h x)) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (nhds x = filter.comap (⇑h) (nhds (coe_fn h x)))) (comap_nhds_eq h (coe_fn h x))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (nhds x = nhds (coe_fn (homeomorph.symm h) (coe_fn h x)))) (symm_apply_apply h x)))
      (Eq.refl (nhds x)))

/-- If an bijective map `e : α ≃ β` is continuous and open, then it is a homeomorphism. -/
def homeomorph_of_continuous_open {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (e : α ≃ β) (h₁ : continuous ⇑e) (h₂ : is_open_map ⇑e) : α ≃ₜ β :=
  mk (equiv.mk (equiv.to_fun e) (equiv.inv_fun e) (equiv.left_inv e) (equiv.right_inv e))

@[simp] theorem comp_continuous_on_iff {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α] [topological_space β] [topological_space γ] (h : α ≃ₜ β) (f : γ → α) (s : set γ) : continuous_on (⇑h ∘ f) s ↔ continuous_on f s :=
  iff.symm (inducing.continuous_on_iff (homeomorph.inducing h))

@[simp] theorem comp_continuous_iff {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α] [topological_space β] [topological_space γ] (h : α ≃ₜ β) {f : γ → α} : continuous (⇑h ∘ f) ↔ continuous f :=
  iff.symm (inducing.continuous_iff (homeomorph.inducing h))

@[simp] theorem comp_continuous_iff' {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α] [topological_space β] [topological_space γ] (h : α ≃ₜ β) {f : β → γ} : continuous (f ∘ ⇑h) ↔ continuous f :=
  iff.symm (quotient_map.continuous_iff (homeomorph.quotient_map h))

/-- If two sets are equal, then they are homeomorphic. -/
def set_congr {α : Type u_1} [topological_space α] {s : set α} {t : set α} (h : s = t) : ↥s ≃ₜ ↥t :=
  mk (equiv.mk (equiv.to_fun (equiv.set_congr h)) (equiv.inv_fun (equiv.set_congr h)) sorry sorry)

/-- Sum of two homeomorphisms. -/
def sum_congr {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} [topological_space α] [topological_space β] [topological_space γ] [topological_space δ] (h₁ : α ≃ₜ β) (h₂ : γ ≃ₜ δ) : α ⊕ γ ≃ₜ β ⊕ δ :=
  mk
    (equiv.mk (equiv.to_fun (equiv.sum_congr (to_equiv h₁) (to_equiv h₂)))
      (equiv.inv_fun (equiv.sum_congr (to_equiv h₁) (to_equiv h₂))) sorry sorry)

/-- Product of two homeomorphisms. -/
def prod_congr {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} [topological_space α] [topological_space β] [topological_space γ] [topological_space δ] (h₁ : α ≃ₜ β) (h₂ : γ ≃ₜ δ) : α × γ ≃ₜ β × δ :=
  mk
    (equiv.mk (equiv.to_fun (equiv.prod_congr (to_equiv h₁) (to_equiv h₂)))
      (equiv.inv_fun (equiv.prod_congr (to_equiv h₁) (to_equiv h₂))) sorry sorry)

/-- `α × β` is homeomorphic to `β × α`. -/
def prod_comm (α : Type u_1) (β : Type u_2) [topological_space α] [topological_space β] : α × β ≃ₜ β × α :=
  mk (equiv.mk (equiv.to_fun (equiv.prod_comm α β)) (equiv.inv_fun (equiv.prod_comm α β)) sorry sorry)

/-- `(α × β) × γ` is homeomorphic to `α × (β × γ)`. -/
def prod_assoc (α : Type u_1) (β : Type u_2) (γ : Type u_3) [topological_space α] [topological_space β] [topological_space γ] : (α × β) × γ ≃ₜ α × β × γ :=
  mk (equiv.mk (equiv.to_fun (equiv.prod_assoc α β γ)) (equiv.inv_fun (equiv.prod_assoc α β γ)) sorry sorry)

/-- `ulift α` is homeomorphic to `α`. -/
def ulift {α : Type u} [topological_space α] : ulift α ≃ₜ α :=
  mk (equiv.mk (equiv.to_fun equiv.ulift) (equiv.inv_fun equiv.ulift) sorry sorry)

/-- `(α ⊕ β) × γ` is homeomorphic to `α × γ ⊕ β × γ`. -/
def sum_prod_distrib {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α] [topological_space β] [topological_space γ] : (α ⊕ β) × γ ≃ₜ α × γ ⊕ β × γ :=
  homeomorph.symm (homeomorph_of_continuous_open (equiv.symm (equiv.sum_prod_distrib α β γ)) sorry sorry)

/-- `α × (β ⊕ γ)` is homeomorphic to `α × β ⊕ α × γ`. -/
def prod_sum_distrib {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α] [topological_space β] [topological_space γ] : α × (β ⊕ γ) ≃ₜ α × β ⊕ α × γ :=
  homeomorph.trans (prod_comm α (β ⊕ γ)) (homeomorph.trans sum_prod_distrib (sum_congr (prod_comm β α) (prod_comm γ α)))

/-- `(Σ i, σ i) × β` is homeomorphic to `Σ i, (σ i × β)`. -/
def sigma_prod_distrib {β : Type u_2} [topological_space β] {ι : Type u_5} {σ : ι → Type u_6} [(i : ι) → topological_space (σ i)] : (sigma fun (i : ι) => σ i) × β ≃ₜ sigma fun (i : ι) => σ i × β :=
  homeomorph.symm (homeomorph_of_continuous_open (equiv.symm (equiv.sigma_prod_distrib σ β)) sorry sorry)

