/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

Computational realization of topological spaces (experimental).
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.bases
import Mathlib.data.analysis.filter
import Mathlib.PostPort

universes u_1 u_2 l u_3 u_4 u_5 u_6 

namespace Mathlib

/-- A `ctop α σ` is a realization of a topology (basis) on `α`,
  represented by a type `σ` together with operations for the top element and
  the intersection operation. -/
structure ctop (α : Type u_1) (σ : Type u_2) 
where
  f : σ → set α
  top : α → σ
  top_mem : ∀ (x : α), x ∈ f (top x)
  inter : (a b : σ) → (x : α) → x ∈ f a ∩ f b → σ
  inter_mem : ∀ (a b : σ) (x : α) (h : x ∈ f a ∩ f b), x ∈ f (inter a b x h)
  inter_sub : ∀ (a b : σ) (x : α) (h : x ∈ f a ∩ f b), f (inter a b x h) ⊆ f a ∩ f b

namespace ctop


protected instance has_coe_to_fun {α : Type u_1} {σ : Type u_3} : has_coe_to_fun (ctop α σ) :=
  has_coe_to_fun.mk (fun (x : ctop α σ) => σ → set α) f

@[simp] theorem coe_mk {α : Type u_1} {σ : Type u_3} (f : σ → set α) (T : α → σ) (h₁ : ∀ (x : α), x ∈ f (T x)) (I : (a b : σ) → (x : α) → x ∈ f a ∩ f b → σ) (h₂ : ∀ (a b : σ) (x : α) (h : x ∈ f a ∩ f b), x ∈ f (I a b x h)) (h₃ : ∀ (a b : σ) (x : α) (h : x ∈ f a ∩ f b), f (I a b x h) ⊆ f a ∩ f b) (a : σ) : coe_fn (mk f T h₁ I h₂ h₃) a = f a :=
  rfl

/-- Map a ctop to an equivalent representation type. -/
def of_equiv {α : Type u_1} {σ : Type u_3} {τ : Type u_4} (E : σ ≃ τ) : ctop α σ → ctop α τ :=
  sorry

@[simp] theorem of_equiv_val {α : Type u_1} {σ : Type u_3} {τ : Type u_4} (E : σ ≃ τ) (F : ctop α σ) (a : τ) : coe_fn (of_equiv E F) a = coe_fn F (coe_fn (equiv.symm E) a) := sorry

/-- Every `ctop` is a topological space. -/
def to_topsp {α : Type u_1} {σ : Type u_3} (F : ctop α σ) : topological_space α :=
  topological_space.generate_from (set.range (f F))

theorem to_topsp_is_topological_basis {α : Type u_1} {σ : Type u_3} (F : ctop α σ) : topological_space.is_topological_basis (set.range (f F)) := sorry

@[simp] theorem mem_nhds_to_topsp {α : Type u_1} {σ : Type u_3} (F : ctop α σ) {s : set α} {a : α} : s ∈ nhds a ↔ ∃ (b : σ), a ∈ coe_fn F b ∧ coe_fn F b ⊆ s := sorry

end ctop


/-- A `ctop` realizer for the topological space `T` is a `ctop`
  which generates `T`. -/
structure ctop.realizer (α : Type u_5) [T : topological_space α] 
where
  σ : Type u_6
  F : ctop α σ
  eq : ctop.to_topsp F = T

protected def ctop.to_realizer {α : Type u_1} {σ : Type u_3} (F : ctop α σ) : ctop.realizer α :=
  ctop.realizer.mk σ F sorry

namespace ctop.realizer


protected theorem is_basis {α : Type u_1} [T : topological_space α] (F : realizer α) : topological_space.is_topological_basis (set.range (f (F F))) :=
  eq.mp (Eq._oldrec (Eq.refl (topological_space.is_topological_basis (set.range (f (F F))))) (eq F))
    (to_topsp_is_topological_basis (F F))

protected theorem mem_nhds {α : Type u_1} [T : topological_space α] (F : realizer α) {s : set α} {a : α} : s ∈ nhds a ↔ ∃ (b : σ F), a ∈ coe_fn (F F) b ∧ coe_fn (F F) b ⊆ s :=
  eq.mp (Eq._oldrec (Eq.refl (s ∈ nhds a ↔ ∃ (b : σ F), a ∈ coe_fn (F F) b ∧ coe_fn (F F) b ⊆ s)) (eq F))
    (mem_nhds_to_topsp (F F))

theorem is_open_iff {α : Type u_1} [topological_space α] (F : realizer α) {s : set α} : is_open s ↔ ∀ (a : α), a ∈ s → ∃ (b : σ F), a ∈ coe_fn (F F) b ∧ coe_fn (F F) b ⊆ s :=
  iff.trans is_open_iff_mem_nhds (ball_congr fun (a : α) (h : a ∈ s) => realizer.mem_nhds F)

theorem is_closed_iff {α : Type u_1} [topological_space α] (F : realizer α) {s : set α} : is_closed s ↔ ∀ (a : α), (∀ (b : σ F), a ∈ coe_fn (F F) b → ∃ (z : α), z ∈ coe_fn (F F) b ∩ s) → a ∈ s := sorry

theorem mem_interior_iff {α : Type u_1} [topological_space α] (F : realizer α) {s : set α} {a : α} : a ∈ interior s ↔ ∃ (b : σ F), a ∈ coe_fn (F F) b ∧ coe_fn (F F) b ⊆ s :=
  iff.trans mem_interior_iff_mem_nhds (realizer.mem_nhds F)

protected theorem is_open {α : Type u_1} [topological_space α] (F : realizer α) (s : σ F) : is_open (coe_fn (F F) s) := sorry

theorem ext' {α : Type u_1} [T : topological_space α] {σ : Type u_2} {F : ctop α σ} (H : ∀ (a : α) (s : set α), s ∈ nhds a ↔ ∃ (b : σ), a ∈ coe_fn F b ∧ coe_fn F b ⊆ s) : to_topsp F = T := sorry

theorem ext {α : Type u_1} [T : topological_space α] {σ : Type u_2} {F : ctop α σ} (H₁ : ∀ (a : σ), is_open (coe_fn F a)) (H₂ : ∀ (a : α) (s : set α), s ∈ nhds a → ∃ (b : σ), a ∈ coe_fn F b ∧ coe_fn F b ⊆ s) : to_topsp F = T := sorry

protected def id {α : Type u_1} [topological_space α] : realizer α :=
  mk (Subtype fun (x : set α) => is_open x)
    (mk subtype.val (fun (_x : α) => { val := set.univ, property := is_open_univ }) set.mem_univ
      (fun (_x : Subtype fun (x : set α) => is_open x) => sorry) sorry sorry)
    sorry

def of_equiv {α : Type u_1} {τ : Type u_4} [topological_space α] (F : realizer α) (E : σ F ≃ τ) : realizer α :=
  mk τ (of_equiv E (F F)) sorry

@[simp] theorem of_equiv_σ {α : Type u_1} {τ : Type u_4} [topological_space α] (F : realizer α) (E : σ F ≃ τ) : σ (of_equiv F E) = τ :=
  rfl

@[simp] theorem of_equiv_F {α : Type u_1} {τ : Type u_4} [topological_space α] (F : realizer α) (E : σ F ≃ τ) (s : τ) : coe_fn (F (of_equiv F E)) s = coe_fn (F F) (coe_fn (equiv.symm E) s) := sorry

protected def nhds {α : Type u_1} [topological_space α] (F : realizer α) (a : α) : filter.realizer (nhds a) :=
  filter.realizer.mk (Subtype fun (s : σ F) => a ∈ coe_fn (F F) s)
    (cfilter.mk (fun (s : Subtype fun (s : σ F) => a ∈ coe_fn (F F) s) => coe_fn (F F) (subtype.val s))
      { val := top (F F) a, property := sorry } (fun (_x : Subtype fun (s : σ F) => a ∈ coe_fn (F F) s) => sorry) sorry
      sorry)
    sorry

@[simp] theorem nhds_σ {α : Type u_1} {β : Type u_2} [topological_space α] (m : α → β) (F : realizer α) (a : α) : filter.realizer.σ (realizer.nhds F a) = Subtype fun (s : σ F) => a ∈ coe_fn (F F) s :=
  rfl

@[simp] theorem nhds_F {α : Type u_1} {β : Type u_2} [topological_space α] (m : α → β) (F : realizer α) (a : α) (s : filter.realizer.σ (realizer.nhds F a)) : coe_fn (filter.realizer.F (realizer.nhds F a)) s = coe_fn (F F) (subtype.val s) :=
  rfl

theorem tendsto_nhds_iff {α : Type u_1} {β : Type u_2} [topological_space α] {m : β → α} {f : filter β} (F : filter.realizer f) (R : realizer α) {a : α} : filter.tendsto m f (nhds a) ↔
  ∀ (t : σ R),
    a ∈ coe_fn (F R) t →
      ∃ (s : filter.realizer.σ F), ∀ (x : β), x ∈ coe_fn (filter.realizer.F F) s → m x ∈ coe_fn (F R) t :=
  iff.trans (filter.realizer.tendsto_iff m F (realizer.nhds R a)) subtype.forall

end ctop.realizer


structure locally_finite.realizer {α : Type u_1} {β : Type u_2} [topological_space α] (F : ctop.realizer α) (f : β → set α) 
where
  bas : (a : α) → Subtype fun (s : ctop.realizer.σ F) => a ∈ coe_fn (ctop.realizer.F F) s
  sets : (x : α) → fintype ↥(set_of fun (i : β) => set.nonempty (f i ∩ coe_fn (ctop.realizer.F F) ↑(bas x)))

theorem locally_finite.realizer.to_locally_finite {α : Type u_1} {β : Type u_2} [topological_space α] {F : ctop.realizer α} {f : β → set α} (R : locally_finite.realizer F f) : locally_finite f := sorry

theorem locally_finite_iff_exists_realizer {α : Type u_1} {β : Type u_2} [topological_space α] (F : ctop.realizer α) {f : β → set α} : locally_finite f ↔ Nonempty (locally_finite.realizer F f) := sorry

def compact.realizer {α : Type u_1} [topological_space α] (R : ctop.realizer α) (s : set α) :=
  {f : filter α} →
    (F : filter.realizer f) →
      (x : filter.realizer.σ F) →
        f ≠ ⊥ → coe_fn (filter.realizer.F F) x ⊆ s → Subtype fun (a : α) => a ∈ s ∧ nhds a ⊓ f ≠ ⊥

