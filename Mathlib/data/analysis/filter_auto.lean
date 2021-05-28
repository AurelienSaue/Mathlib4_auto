/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

Computational realization of filters (experimental).
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.order.filter.cofinite
import PostPort

universes u_1 u_2 l u_3 u_4 u_5 

namespace Mathlib

/-- A `cfilter α σ` is a realization of a filter (base) on `α`,
  represented by a type `σ` together with operations for the top element and
  the binary inf operation. -/
structure cfilter (α : Type u_1) (σ : Type u_2) [partial_order α] 
where
  f : σ → α
  pt : σ
  inf : σ → σ → σ
  inf_le_left : ∀ (a b : σ), f (inf a b) ≤ f a
  inf_le_right : ∀ (a b : σ), f (inf a b) ≤ f b

namespace cfilter


protected instance has_coe_to_fun {α : Type u_1} {σ : Type u_3} [partial_order α] : has_coe_to_fun (cfilter α σ) :=
  has_coe_to_fun.mk (fun (x : cfilter α σ) => σ → α) f

@[simp] theorem coe_mk {α : Type u_1} {σ : Type u_3} [partial_order α] (f : σ → α) (pt : σ) (inf : σ → σ → σ) (h₁ : ∀ (a b : σ), f (inf a b) ≤ f a) (h₂ : ∀ (a b : σ), f (inf a b) ≤ f b) (a : σ) : coe_fn (mk f pt inf h₁ h₂) a = f a :=
  rfl

/-- Map a cfilter to an equivalent representation type. -/
def of_equiv {α : Type u_1} {σ : Type u_3} {τ : Type u_4} [partial_order α] (E : σ ≃ τ) : cfilter α σ → cfilter α τ :=
  sorry

@[simp] theorem of_equiv_val {α : Type u_1} {σ : Type u_3} {τ : Type u_4} [partial_order α] (E : σ ≃ τ) (F : cfilter α σ) (a : τ) : coe_fn (of_equiv E F) a = coe_fn F (coe_fn (equiv.symm E) a) := sorry

/-- The filter represented by a `cfilter` is the collection of supersets of
  elements of the filter base. -/
def to_filter {α : Type u_1} {σ : Type u_3} (F : cfilter (set α) σ) : filter α :=
  filter.mk (set_of fun (a : set α) => ∃ (b : σ), coe_fn F b ⊆ a) sorry sorry sorry

@[simp] theorem mem_to_filter_sets {α : Type u_1} {σ : Type u_3} (F : cfilter (set α) σ) {a : set α} : a ∈ to_filter F ↔ ∃ (b : σ), coe_fn F b ⊆ a :=
  iff.rfl

end cfilter


/-- A realizer for filter `f` is a cfilter which generates `f`. -/
structure filter.realizer {α : Type u_1} (f : filter α) 
where
  σ : Type u_5
  F : cfilter (set α) σ
  eq : cfilter.to_filter F = f

protected def cfilter.to_realizer {α : Type u_1} {σ : Type u_3} (F : cfilter (set α) σ) : filter.realizer (cfilter.to_filter F) :=
  filter.realizer.mk σ F sorry

namespace filter.realizer


theorem mem_sets {α : Type u_1} {f : filter α} (F : realizer f) {a : set α} : a ∈ f ↔ ∃ (b : σ F), coe_fn (F F) b ⊆ a := sorry

-- Used because it has better definitional equalities than the eq.rec proof

def of_eq {α : Type u_1} {f : filter α} {g : filter α} (e : f = g) (F : realizer f) : realizer g :=
  mk (σ F) (F F) sorry

/-- A filter realizes itself. -/
def of_filter {α : Type u_1} (f : filter α) : realizer f :=
  mk (↥(sets f))
    (cfilter.mk subtype.val { val := set.univ, property := univ_mem_sets } (fun (_x : ↥(sets f)) => sorry) sorry sorry)
    sorry

/-- Transfer a filter realizer to another realizer on a different base type. -/
def of_equiv {α : Type u_1} {τ : Type u_4} {f : filter α} (F : realizer f) (E : σ F ≃ τ) : realizer f :=
  mk τ (cfilter.of_equiv E (F F)) sorry

@[simp] theorem of_equiv_σ {α : Type u_1} {τ : Type u_4} {f : filter α} (F : realizer f) (E : σ F ≃ τ) : σ (of_equiv F E) = τ :=
  rfl

@[simp] theorem of_equiv_F {α : Type u_1} {τ : Type u_4} {f : filter α} (F : realizer f) (E : σ F ≃ τ) (s : τ) : coe_fn (F (of_equiv F E)) s = coe_fn (F F) (coe_fn (equiv.symm E) s) := sorry

/-- `unit` is a realizer for the principal filter -/
protected def principal {α : Type u_1} (s : set α) : realizer (principal s) :=
  mk Unit (cfilter.mk (fun (_x : Unit) => s) Unit.unit (fun (_x _x : Unit) => Unit.unit) sorry sorry) sorry

@[simp] theorem principal_σ {α : Type u_1} (s : set α) : σ (realizer.principal s) = Unit :=
  rfl

@[simp] theorem principal_F {α : Type u_1} (s : set α) (u : Unit) : coe_fn (F (realizer.principal s)) u = s :=
  rfl

/-- `unit` is a realizer for the top filter -/
protected def top {α : Type u_1} : realizer ⊤ :=
  of_eq principal_univ (realizer.principal set.univ)

@[simp] theorem top_σ {α : Type u_1} : σ realizer.top = Unit :=
  rfl

@[simp] theorem top_F {α : Type u_1} (u : Unit) : coe_fn (F realizer.top) u = set.univ :=
  rfl

/-- `unit` is a realizer for the bottom filter -/
protected def bot {α : Type u_1} : realizer ⊥ :=
  of_eq principal_empty (realizer.principal ∅)

@[simp] theorem bot_σ {α : Type u_1} : σ realizer.bot = Unit :=
  rfl

@[simp] theorem bot_F {α : Type u_1} (u : Unit) : coe_fn (F realizer.bot) u = ∅ :=
  rfl

/-- Construct a realizer for `map m f` given a realizer for `f` -/
protected def map {α : Type u_1} {β : Type u_2} (m : α → β) {f : filter α} (F : realizer f) : realizer (map m f) :=
  mk (σ F) (cfilter.mk (fun (s : σ F) => m '' coe_fn (F F) s) (cfilter.pt (F F)) (cfilter.inf (F F)) sorry sorry) sorry

@[simp] theorem map_σ {α : Type u_1} {β : Type u_2} (m : α → β) {f : filter α} (F : realizer f) : σ (realizer.map m F) = σ F :=
  rfl

@[simp] theorem map_F {α : Type u_1} {β : Type u_2} (m : α → β) {f : filter α} (F : realizer f) (s : σ (realizer.map m F)) : coe_fn (F (realizer.map m F)) s = m '' coe_fn (F F) s :=
  rfl

/-- Construct a realizer for `comap m f` given a realizer for `f` -/
protected def comap {α : Type u_1} {β : Type u_2} (m : α → β) {f : filter β} (F : realizer f) : realizer (comap m f) :=
  mk (σ F) (cfilter.mk (fun (s : σ F) => m ⁻¹' coe_fn (F F) s) (cfilter.pt (F F)) (cfilter.inf (F F)) sorry sorry) sorry

/-- Construct a realizer for the sup of two filters -/
protected def sup {α : Type u_1} {f : filter α} {g : filter α} (F : realizer f) (G : realizer g) : realizer (f ⊔ g) :=
  mk (σ F × σ G)
    (cfilter.mk (fun (_x : σ F × σ G) => sorry) (cfilter.pt (F F), cfilter.pt (F G)) (fun (_x : σ F × σ G) => sorry) sorry
      sorry)
    sorry

/-- Construct a realizer for the inf of two filters -/
protected def inf {α : Type u_1} {f : filter α} {g : filter α} (F : realizer f) (G : realizer g) : realizer (f ⊓ g) :=
  mk (σ F × σ G)
    (cfilter.mk (fun (_x : σ F × σ G) => sorry) (cfilter.pt (F F), cfilter.pt (F G)) (fun (_x : σ F × σ G) => sorry) sorry
      sorry)
    sorry

/-- Construct a realizer for the cofinite filter -/
protected def cofinite {α : Type u_1} [DecidableEq α] : realizer cofinite :=
  mk (finset α) (cfilter.mk (fun (s : finset α) => set_of fun (a : α) => ¬a ∈ s) ∅ has_union.union sorry sorry) sorry

/-- Construct a realizer for filter bind -/
protected def bind {α : Type u_1} {β : Type u_2} {f : filter α} {m : α → filter β} (F : realizer f) (G : (i : α) → realizer (m i)) : realizer (bind f m) :=
  mk (sigma fun (s : σ F) => (i : α) → i ∈ coe_fn (F F) s → σ (G i))
    (cfilter.mk (fun (_x : sigma fun (s : σ F) => (i : α) → i ∈ coe_fn (F F) s → σ (G i)) => sorry)
      (sigma.mk (cfilter.pt (F F)) fun (i : α) (H : i ∈ coe_fn (F F) (cfilter.pt (F F))) => cfilter.pt (F (G i)))
      (fun (_x : sigma fun (s : σ F) => (i : α) → i ∈ coe_fn (F F) s → σ (G i)) => sorry) sorry sorry)
    sorry

/-- Construct a realizer for indexed supremum -/
protected def Sup {α : Type u_1} {β : Type u_2} {f : α → filter β} (F : (i : α) → realizer (f i)) : realizer (supr fun (i : α) => f i) :=
  let F' : realizer (supr fun (i : α) => f i) := of_eq sorry (realizer.bind realizer.top F);
  of_equiv F'
    ((fun (this : (sigma fun (u : Unit) => (i : α) → True → σ (F i)) ≃ ((i : α) → σ (F i))) => this)
      (equiv.mk (fun (_x : sigma fun (u : Unit) => (i : α) → True → σ (F i)) => sorry)
        (fun (f_1 : (i : α) → σ (F i)) => sigma.mk Unit.unit fun (i : α) (_x : True) => f_1 i) sorry sorry))

/-- Construct a realizer for the product of filters -/
protected def prod {α : Type u_1} {f : filter α} {g : filter α} (F : realizer f) (G : realizer g) : realizer (filter.prod f g) :=
  realizer.inf (realizer.comap prod.fst F) (realizer.comap prod.snd G)

theorem le_iff {α : Type u_1} {f : filter α} {g : filter α} (F : realizer f) (G : realizer g) : f ≤ g ↔ ∀ (b : σ G), ∃ (a : σ F), coe_fn (F F) a ≤ coe_fn (F G) b := sorry

theorem tendsto_iff {α : Type u_1} {β : Type u_2} (f : α → β) {l₁ : filter α} {l₂ : filter β} (L₁ : realizer l₁) (L₂ : realizer l₂) : tendsto f l₁ l₂ ↔ ∀ (b : σ L₂), ∃ (a : σ L₁), ∀ (x : α), x ∈ coe_fn (F L₁) a → f x ∈ coe_fn (F L₂) b :=
  iff.trans (le_iff (realizer.map f L₁) L₂)
    (forall_congr fun (b : σ L₂) => exists_congr fun (a : σ (realizer.map f L₁)) => set.image_subset_iff)

theorem ne_bot_iff {α : Type u_1} {f : filter α} (F : realizer f) : f ≠ ⊥ ↔ ∀ (a : σ F), set.nonempty (coe_fn (F F) a) := sorry

