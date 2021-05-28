/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.order.filter.cofinite
import PostPort

universes u_1 l u v 

namespace Mathlib

/-!
# Ultrafilters

An ultrafilter is a minimal (maximal in the set order) proper filter.
In this file we define

* `ultrafilter.of`: an ultrafilter that is less than or equal to a given filter;
* `ultrafilter`: subtype of ultrafilters;
* `ultrafilter.pure`: `pure x` as an `ultrafiler`;
* `ultrafilter.map`, `ultrafilter.bind`, `ultrafilter.comap` : operations on ultrafilters;
* `hyperfilter`: the ultrafilter extending the cofinite filter.
-/

/-- An ultrafilter is a minimal (maximal in the set order) proper filter. -/
structure ultrafilter (α : Type u_1) 
extends filter α
where
  ne_bot' : filter.ne_bot _to_filter
  le_of_le : ∀ (g : filter α), filter.ne_bot g → g ≤ _to_filter → _to_filter ≤ g

namespace ultrafilter


protected instance filter.has_coe_t {α : Type u} : has_coe_t (ultrafilter α) (filter α) :=
  has_coe_t.mk ultrafilter.to_filter

protected instance has_mem {α : Type u} : has_mem (set α) (ultrafilter α) :=
  has_mem.mk fun (s : set α) (f : ultrafilter α) => s ∈ ↑f

theorem unique {α : Type u} (f : ultrafilter α) {g : filter α} (h : g ≤ ↑f) (hne : autoParam (filter.ne_bot g)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.tactic.apply_instance")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "tactic") "apply_instance") [])) : g = ↑f :=
  le_antisymm h (ultrafilter.le_of_le f g hne h)

protected instance ne_bot {α : Type u} (f : ultrafilter α) : filter.ne_bot ↑f :=
  ultrafilter.ne_bot' f

@[simp] theorem mem_coe {α : Type u} {f : ultrafilter α} {s : set α} : s ∈ ↑f ↔ s ∈ f :=
  iff.rfl

theorem coe_injective {α : Type u} : function.injective coe := sorry

@[simp] theorem coe_le_coe {α : Type u} {f : ultrafilter α} {g : ultrafilter α} : ↑f ≤ ↑g ↔ f = g :=
  { mp := fun (h : ↑f ≤ ↑g) => coe_injective (unique g h), mpr := fun (h : f = g) => h ▸ le_rfl }

@[simp] theorem coe_inj {α : Type u} {f : ultrafilter α} {g : ultrafilter α} : ↑f = ↑g ↔ f = g :=
  function.injective.eq_iff coe_injective

theorem ext {α : Type u} {f : ultrafilter α} {g : ultrafilter α} (h : ∀ (s : set α), s ∈ f ↔ s ∈ g) : f = g :=
  coe_injective (filter.ext h)

theorem le_of_inf_ne_bot {α : Type u} (f : ultrafilter α) {g : filter α} (hg : filter.ne_bot (↑f ⊓ g)) : ↑f ≤ g :=
  le_of_inf_eq (unique f inf_le_left)

theorem le_of_inf_ne_bot' {α : Type u} (f : ultrafilter α) {g : filter α} (hg : filter.ne_bot (g ⊓ ↑f)) : ↑f ≤ g :=
  le_of_inf_ne_bot f (eq.mpr (id (Eq._oldrec (Eq.refl (filter.ne_bot (↑f ⊓ g))) inf_comm)) hg)

@[simp] theorem compl_not_mem_iff {α : Type u} {f : ultrafilter α} {s : set α} : ¬sᶜ ∈ f ↔ s ∈ f := sorry

@[simp] theorem frequently_iff_eventually {α : Type u} {f : ultrafilter α} {p : α → Prop} : filter.frequently (fun (x : α) => p x) ↑f ↔ filter.eventually (fun (x : α) => p x) ↑f :=
  compl_not_mem_iff

theorem Mathlib.filter.frequently.eventually {α : Type u} {f : ultrafilter α} {p : α → Prop} : filter.frequently (fun (x : α) => p x) ↑f → filter.eventually (fun (x : α) => p x) ↑f :=
  iff.mp frequently_iff_eventually

theorem compl_mem_iff_not_mem {α : Type u} {f : ultrafilter α} {s : set α} : sᶜ ∈ f ↔ ¬s ∈ f :=
  eq.mpr (id (Eq._oldrec (Eq.refl (sᶜ ∈ f ↔ ¬s ∈ f)) (Eq.symm (propext compl_not_mem_iff))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (¬sᶜᶜ ∈ f ↔ ¬s ∈ f)) (compl_compl s))) (iff.refl (¬s ∈ f)))

/-- If `sᶜ ∉ f ↔ s ∈ f`, then `f` is an ultrafilter. The other implication is given by
`ultrafilter.compl_not_mem_iff`.  -/
def of_compl_not_mem_iff {α : Type u} (f : filter α) (h : ∀ (s : set α), ¬sᶜ ∈ f ↔ s ∈ f) : ultrafilter α :=
  mk f sorry sorry

theorem nonempty_of_mem {α : Type u} {f : ultrafilter α} {s : set α} (hs : s ∈ f) : set.nonempty s :=
  filter.nonempty_of_mem_sets hs

theorem ne_empty_of_mem {α : Type u} {f : ultrafilter α} {s : set α} (hs : s ∈ f) : s ≠ ∅ :=
  set.nonempty.ne_empty (nonempty_of_mem hs)

@[simp] theorem empty_not_mem {α : Type u} {f : ultrafilter α} : ¬∅ ∈ f :=
  filter.empty_nmem_sets ↑f

theorem mem_or_compl_mem {α : Type u} (f : ultrafilter α) (s : set α) : s ∈ f ∨ sᶜ ∈ f :=
  iff.mpr or_iff_not_imp_left (iff.mpr compl_mem_iff_not_mem)

protected theorem em {α : Type u} (f : ultrafilter α) (p : α → Prop) : filter.eventually (fun (x : α) => p x) ↑f ∨ filter.eventually (fun (x : α) => ¬p x) ↑f :=
  mem_or_compl_mem f (set_of fun (x : α) => p x)

theorem eventually_or {α : Type u} {f : ultrafilter α} {p : α → Prop} {q : α → Prop} : filter.eventually (fun (x : α) => p x ∨ q x) ↑f ↔
  filter.eventually (fun (x : α) => p x) ↑f ∨ filter.eventually (fun (x : α) => q x) ↑f := sorry

theorem union_mem_iff {α : Type u} {f : ultrafilter α} {s : set α} {t : set α} : s ∪ t ∈ f ↔ s ∈ f ∨ t ∈ f :=
  eventually_or

theorem eventually_not {α : Type u} {f : ultrafilter α} {p : α → Prop} : filter.eventually (fun (x : α) => ¬p x) ↑f ↔ ¬filter.eventually (fun (x : α) => p x) ↑f :=
  compl_mem_iff_not_mem

theorem eventually_imp {α : Type u} {f : ultrafilter α} {p : α → Prop} {q : α → Prop} : filter.eventually (fun (x : α) => p x → q x) ↑f ↔
  filter.eventually (fun (x : α) => p x) ↑f → filter.eventually (fun (x : α) => q x) ↑f := sorry

theorem finite_sUnion_mem_iff {α : Type u} {f : ultrafilter α} {s : set (set α)} (hs : set.finite s) : ⋃₀s ∈ f ↔ ∃ (t : set α), ∃ (H : t ∈ s), t ∈ f := sorry

theorem finite_bUnion_mem_iff {α : Type u} {β : Type v} {f : ultrafilter α} {is : set β} {s : β → set α} (his : set.finite is) : (set.Union fun (i : β) => set.Union fun (H : i ∈ is) => s i) ∈ f ↔ ∃ (i : β), ∃ (H : i ∈ is), s i ∈ f := sorry

/-- Pushforward for ultrafilters. -/
def map {α : Type u} {β : Type v} (m : α → β) (f : ultrafilter α) : ultrafilter β :=
  of_compl_not_mem_iff (filter.map m ↑f) sorry

@[simp] theorem coe_map {α : Type u} {β : Type v} (m : α → β) (f : ultrafilter α) : ↑(map m f) = filter.map m ↑f :=
  rfl

@[simp] theorem mem_map {α : Type u} {β : Type v} {m : α → β} {f : ultrafilter α} {s : set β} : s ∈ map m f ↔ m ⁻¹' s ∈ f :=
  iff.rfl

/-- The pullback of an ultrafilter along an injection whose range is large with respect to the given
ultrafilter. -/
def comap {α : Type u} {β : Type v} {m : α → β} (u : ultrafilter β) (inj : function.injective m) (large : set.range m ∈ u) : ultrafilter α :=
  mk (filter.comap m ↑u) sorry sorry

/-- The principal ultrafilter associated to a point `x`. -/
protected instance has_pure : Pure ultrafilter :=
  { pure := fun (α : Type u_1) (a : α) => of_compl_not_mem_iff (pure a) sorry }

@[simp] theorem mem_pure_sets {α : Type u} {a : α} {s : set α} : s ∈ pure a ↔ a ∈ s :=
  iff.rfl

protected instance inhabited {α : Type u} [Inhabited α] : Inhabited (ultrafilter α) :=
  { default := pure Inhabited.default }

/-- Monadic bind for ultrafilters, coming from the one on filters
defined in terms of map and join.-/
def bind {α : Type u} {β : Type v} (f : ultrafilter α) (m : α → ultrafilter β) : ultrafilter β :=
  of_compl_not_mem_iff (filter.bind ↑f fun (x : α) => ↑(m x)) sorry

protected instance ultrafilter.has_bind : Bind ultrafilter :=
  { bind := bind }

protected instance ultrafilter.functor : Functor ultrafilter :=
  { map := map, mapConst := fun (α β : Type u_1) => map ∘ function.const β }

protected instance ultrafilter.monad : Monad ultrafilter := sorry

protected instance ultrafilter.is_lawful_monad : is_lawful_monad ultrafilter :=
  is_lawful_monad.mk
    (fun (α β : Type u_1) (a : α) (f : α → ultrafilter β) => coe_injective (filter.pure_bind a (coe ∘ f)))
    fun (α β γ : Type u_1) (f : ultrafilter α) (m₁ : α → ultrafilter β) (m₂ : β → ultrafilter γ) =>
      coe_injective (filter.filter_eq rfl)

/-- The ultrafilter lemma: Any proper filter is contained in an ultrafilter. -/
theorem exists_le {α : Type u} (f : filter α) [h : filter.ne_bot f] : ∃ (u : ultrafilter α), ↑u ≤ f := sorry

theorem Mathlib.filter.exists_ultrafilter_le {α : Type u} (f : filter α) [h : filter.ne_bot f] : ∃ (u : ultrafilter α), ↑u ≤ f :=
  exists_le

/-- Construct an ultrafilter extending a given filter.
  The ultrafilter lemma is the assertion that such a filter exists;
  we use the axiom of choice to pick one. -/
def of {α : Type u} (f : filter α) [filter.ne_bot f] : ultrafilter α :=
  classical.some (exists_le f)

theorem of_le {α : Type u} (f : filter α) [filter.ne_bot f] : ↑(of f) ≤ f :=
  classical.some_spec (exists_le f)

theorem of_coe {α : Type u} (f : ultrafilter α) : of ↑f = f :=
  iff.mp coe_inj (unique f (of_le ↑f))

theorem exists_ultrafilter_of_finite_inter_nonempty {α : Type u} (S : set (set α)) (cond : ∀ (T : finset (set α)), ↑T ⊆ S → set.nonempty (⋂₀↑T)) : ∃ (F : ultrafilter α), S ⊆ filter.sets (ultrafilter.to_filter F) := sorry

end ultrafilter


namespace filter


theorem mem_iff_ultrafilter {α : Type u} {s : set α} {f : filter α} : s ∈ f ↔ ∀ (g : ultrafilter α), ↑g ≤ f → s ∈ g := sorry

theorem le_iff_ultrafilter {α : Type u} {f₁ : filter α} {f₂ : filter α} : f₁ ≤ f₂ ↔ ∀ (g : ultrafilter α), ↑g ≤ f₁ → ↑g ≤ f₂ := sorry

/-- A filter equals the intersection of all the ultrafilters which contain it. -/
theorem supr_ultrafilter_le_eq {α : Type u} (f : filter α) : (supr fun (g : ultrafilter α) => supr fun (hg : ↑g ≤ f) => ↑g) = f := sorry

/-- The `tendsto` relation can be checked on ultrafilters. -/
theorem tendsto_iff_ultrafilter {α : Type u} {β : Type v} (f : α → β) (l₁ : filter α) (l₂ : filter β) : tendsto f l₁ l₂ ↔ ∀ (g : ultrafilter α), ↑g ≤ l₁ → tendsto f (↑g) l₂ := sorry

theorem exists_ultrafilter_iff {α : Type u} {f : filter α} : (∃ (u : ultrafilter α), ↑u ≤ f) ↔ ne_bot f := sorry

theorem forall_ne_bot_le_iff {α : Type u} {g : filter α} {p : filter α → Prop} (hp : monotone p) : (∀ (f : filter α), ne_bot f → f ≤ g → p f) ↔ ∀ (f : ultrafilter α), ↑f ≤ g → p ↑f := sorry

/-- The ultrafilter extending the cofinite filter. -/
def hyperfilter (α : Type u) [infinite α] : ultrafilter α :=
  ultrafilter.of cofinite

theorem hyperfilter_le_cofinite {α : Type u} [infinite α] : ↑(hyperfilter α) ≤ cofinite :=
  ultrafilter.of_le cofinite

@[simp] theorem bot_ne_hyperfilter {α : Type u} [infinite α] : ⊥ ≠ ↑(hyperfilter α) :=
  ne.symm ((fun (this : ne_bot ↑(hyperfilter α)) => this) (ultrafilter.ne_bot (hyperfilter α)))

theorem nmem_hyperfilter_of_finite {α : Type u} [infinite α] {s : set α} (hf : set.finite s) : ¬s ∈ hyperfilter α :=
  fun (hy : s ∈ hyperfilter α) => compl_not_mem_sets hy (hyperfilter_le_cofinite (set.finite.compl_mem_cofinite hf))

theorem Mathlib.set.finite.nmem_hyperfilter {α : Type u} [infinite α] {s : set α} (hf : set.finite s) : ¬s ∈ hyperfilter α :=
  nmem_hyperfilter_of_finite

theorem compl_mem_hyperfilter_of_finite {α : Type u} [infinite α] {s : set α} (hf : set.finite s) : sᶜ ∈ hyperfilter α :=
  iff.mpr ultrafilter.compl_mem_iff_not_mem (set.finite.nmem_hyperfilter hf)

theorem Mathlib.set.finite.compl_mem_hyperfilter {α : Type u} [infinite α] {s : set α} (hf : set.finite s) : sᶜ ∈ hyperfilter α :=
  compl_mem_hyperfilter_of_finite

theorem mem_hyperfilter_of_finite_compl {α : Type u} [infinite α] {s : set α} (hf : set.finite (sᶜ)) : s ∈ hyperfilter α :=
  compl_compl s ▸ set.finite.compl_mem_hyperfilter hf

