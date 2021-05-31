/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.logic.embedding
import Mathlib.order.rel_classes
import Mathlib.data.set.intervals.basic
import Mathlib.PostPort

universes u_4 u_5 l u_1 u_2 u_3 

namespace Mathlib

/-- A relation homomorphism with respect to a given pair of relations `r` and `s`
is a function `f : α → β` such that `r a b → s (f a) (f b)`. -/
structure rel_hom {α : Type u_4} {β : Type u_5} (r : α → α → Prop) (s : β → β → Prop) 
where
  to_fun : α → β
  map_rel' : ∀ {a b : α}, r a b → s (to_fun a) (to_fun b)

infixl:25 " →r " => Mathlib.rel_hom

namespace rel_hom


protected instance has_coe_to_fun {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} : has_coe_to_fun (r →r s) :=
  has_coe_to_fun.mk (fun (_x : r →r s) => α → β) fun (o : r →r s) => to_fun o

theorem map_rel {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : r →r s) {a : α} {b : α} : r a b → s (coe_fn f a) (coe_fn f b) :=
  map_rel' f

@[simp] theorem coe_fn_mk {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : α → β) (o : ∀ {a b : α}, r a b → s (f a) (f b)) : ⇑(mk f o) = f :=
  rfl

@[simp] theorem coe_fn_to_fun {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : r →r s) : to_fun f = ⇑f :=
  rfl

/-- The map `coe_fn : (r →r s) → (α → β)` is injective. We can't use `function.injective`
here but mimic its signature by using `⦃e₁ e₂⦄`. -/
theorem coe_fn_inj {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} {e₁ : r →r s} {e₂ : r →r s} : ⇑e₁ = ⇑e₂ → e₁ = e₂ := sorry

theorem ext {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} {f : r →r s} {g : r →r s} (h : ∀ (x : α), coe_fn f x = coe_fn g x) : f = g :=
  coe_fn_inj (funext h)

theorem ext_iff {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} {f : r →r s} {g : r →r s} : f = g ↔ ∀ (x : α), coe_fn f x = coe_fn g x :=
  { mp := fun (h : f = g) (x : α) => h ▸ rfl, mpr := fun (h : ∀ (x : α), coe_fn f x = coe_fn g x) => ext h }

/-- Identity map is a relation homomorphism. -/
protected def id {α : Type u_1} (r : α → α → Prop) : r →r r :=
  mk id sorry

/-- Composition of two relation homomorphisms is a relation homomorphism. -/
protected def comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop} (g : s →r t) (f : r →r s) : r →r t :=
  mk (to_fun g ∘ to_fun f) sorry

@[simp] theorem id_apply {α : Type u_1} {r : α → α → Prop} (x : α) : coe_fn (rel_hom.id r) x = x :=
  rfl

@[simp] theorem comp_apply {α : Type u_1} {β : Type u_2} {γ : Type u_3} {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop} (g : s →r t) (f : r →r s) (a : α) : coe_fn (rel_hom.comp g f) a = coe_fn g (coe_fn f a) :=
  rfl

/-- A relation homomorphism is also a relation homomorphism between dual relations. -/
protected def swap {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : r →r s) : function.swap r →r function.swap s :=
  mk ⇑f sorry

/-- A function is a relation homomorphism from the preimage relation of `s` to `s`. -/
def preimage {α : Type u_1} {β : Type u_2} (f : α → β) (s : β → β → Prop) : f ⁻¹'o s →r s :=
  mk f sorry

protected theorem is_irrefl {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : r →r s) [is_irrefl β s] : is_irrefl α r := sorry

protected theorem is_asymm {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : r →r s) [is_asymm β s] : is_asymm α r := sorry

protected theorem acc {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : r →r s) (a : α) : acc s (coe_fn f a) → acc r a := sorry

protected theorem well_founded {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : r →r s) (h : well_founded s) : well_founded r :=
  well_founded.dcases_on h
    fun (h : ∀ (a : β), acc s a) =>
      idRhs (well_founded r) (well_founded.intro fun (a : α) => rel_hom.acc f a (h (coe_fn f a)))

theorem map_inf {α : Type u_1} {β : Type u_2} [semilattice_inf α] [linear_order β] (a : Less →r Less) (m : β) (n : β) : coe_fn a (m ⊓ n) = coe_fn a m ⊓ coe_fn a n := sorry

theorem map_sup {α : Type u_1} {β : Type u_2} [semilattice_sup α] [linear_order β] (a : gt →r gt) (m : β) (n : β) : coe_fn a (m ⊔ n) = coe_fn a m ⊔ coe_fn a n := sorry

end rel_hom


/-- An increasing function is injective -/
theorem injective_of_increasing {α : Type u_1} {β : Type u_2} (r : α → α → Prop) (s : β → β → Prop) [is_trichotomous α r] [is_irrefl β s] (f : α → β) (hf : ∀ {x y : α}, r x y → s (f x) (f y)) : function.injective f := sorry

/-- An increasing function is injective -/
theorem rel_hom.injective_of_increasing {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} [is_trichotomous α r] [is_irrefl β s] (f : r →r s) : function.injective ⇑f :=
  injective_of_increasing r s ⇑f fun (x y : α) => rel_hom.map_rel f

theorem surjective.well_founded_iff {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} {f : α → β} (hf : function.surjective f) (o : ∀ {a b : α}, r a b ↔ s (f a) (f b)) : well_founded r ↔ well_founded s := sorry

/-- A relation embedding with respect to a given pair of relations `r` and `s`
is an embedding `f : α ↪ β` such that `r a b ↔ s (f a) (f b)`. -/
structure rel_embedding {α : Type u_4} {β : Type u_5} (r : α → α → Prop) (s : β → β → Prop) 
extends α ↪ β
where
  map_rel_iff' : ∀ {a b : α}, s (coe_fn _to_embedding a) (coe_fn _to_embedding b) ↔ r a b

infixl:25 " ↪r " => Mathlib.rel_embedding

/-- An order embedding is an embedding `f : α ↪ β` such that `a ≤ b ↔ (f a) ≤ (f b)`.
This definition is an abbreviation of `rel_embedding (≤) (≤)`. -/
def order_embedding (α : Type u_1) (β : Type u_2) [HasLessEq α] [HasLessEq β] :=
  LessEq ↪r LessEq

infixl:25 " ↪o " => Mathlib.order_embedding

/-- The induced relation on a subtype is an embedding under the natural inclusion. -/
def subtype.rel_embedding {X : Type u_1} (r : X → X → Prop) (p : X → Prop) : subtype.val ⁻¹'o r ↪r r :=
  rel_embedding.mk (function.embedding.subtype p) sorry

theorem preimage_equivalence {α : Sort u_1} {β : Sort u_2} (f : α → β) {s : β → β → Prop} (hs : equivalence s) : equivalence (f ⁻¹'o s) := sorry

namespace rel_embedding


/-- A relation embedding is also a relation homomorphism -/
def to_rel_hom {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : r ↪r s) : r →r s :=
  rel_hom.mk (function.embedding.to_fun (to_embedding f)) sorry

-- see Note [function coercion]

protected instance rel_hom.has_coe {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} : has_coe (r ↪r s) (r →r s) :=
  has_coe.mk to_rel_hom

protected instance has_coe_to_fun {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} : has_coe_to_fun (r ↪r s) :=
  has_coe_to_fun.mk (fun (_x : r ↪r s) => α → β) fun (o : r ↪r s) => ⇑(to_embedding o)

@[simp] theorem to_rel_hom_eq_coe {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : r ↪r s) : to_rel_hom f = ↑f :=
  rfl

@[simp] theorem coe_coe_fn {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : r ↪r s) : ⇑↑f = ⇑f :=
  rfl

theorem injective {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : r ↪r s) : function.injective ⇑f :=
  function.embedding.inj' (to_embedding f)

theorem map_rel_iff {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : r ↪r s) {a : α} {b : α} : s (coe_fn f a) (coe_fn f b) ↔ r a b :=
  map_rel_iff' f

@[simp] theorem coe_fn_mk {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : α ↪ β) (o : ∀ {a b : α}, s (coe_fn f a) (coe_fn f b) ↔ r a b) : ⇑(mk f o) = ⇑f :=
  rfl

@[simp] theorem coe_fn_to_embedding {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : r ↪r s) : ⇑(to_embedding f) = ⇑f :=
  rfl

/-- The map `coe_fn : (r ↪r s) → (α → β)` is injective. We can't use `function.injective`
here but mimic its signature by using `⦃e₁ e₂⦄`. -/
theorem coe_fn_inj {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} {e₁ : r ↪r s} {e₂ : r ↪r s} : ⇑e₁ = ⇑e₂ → e₁ = e₂ := sorry

theorem ext {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} {f : r ↪r s} {g : r ↪r s} (h : ∀ (x : α), coe_fn f x = coe_fn g x) : f = g :=
  coe_fn_inj (funext h)

theorem ext_iff {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} {f : r ↪r s} {g : r ↪r s} : f = g ↔ ∀ (x : α), coe_fn f x = coe_fn g x :=
  { mp := fun (h : f = g) (x : α) => h ▸ rfl, mpr := fun (h : ∀ (x : α), coe_fn f x = coe_fn g x) => ext h }

/-- Identity map is a relation embedding. -/
protected def refl {α : Type u_1} (r : α → α → Prop) : r ↪r r :=
  mk (function.embedding.refl α) sorry

/-- Composition of two relation embeddings is a relation embedding. -/
protected def trans {α : Type u_1} {β : Type u_2} {γ : Type u_3} {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop} (f : r ↪r s) (g : s ↪r t) : r ↪r t :=
  mk (function.embedding.trans (to_embedding f) (to_embedding g)) sorry

protected instance inhabited {α : Type u_1} (r : α → α → Prop) : Inhabited (r ↪r r) :=
  { default := rel_embedding.refl r }

@[simp] theorem refl_apply {α : Type u_1} {r : α → α → Prop} (x : α) : coe_fn (rel_embedding.refl r) x = x :=
  rfl

theorem trans_apply {α : Type u_1} {β : Type u_2} {γ : Type u_3} {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop} (f : r ↪r s) (g : s ↪r t) (a : α) : coe_fn (rel_embedding.trans f g) a = coe_fn g (coe_fn f a) :=
  rfl

@[simp] theorem coe_trans {α : Type u_1} {β : Type u_2} {γ : Type u_3} {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop} (f : r ↪r s) (g : s ↪r t) : ⇑(rel_embedding.trans f g) = ⇑g ∘ ⇑f :=
  rfl

/-- A relation embedding is also a relation embedding between dual relations. -/
protected def swap {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : r ↪r s) : function.swap r ↪r function.swap s :=
  mk (to_embedding f) sorry

/-- If `f` is injective, then it is a relation embedding from the
  preimage relation of `s` to `s`. -/
def preimage {α : Type u_1} {β : Type u_2} (f : α ↪ β) (s : β → β → Prop) : ⇑f ⁻¹'o s ↪r s :=
  mk f sorry

theorem eq_preimage {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : r ↪r s) : r = ⇑f ⁻¹'o s :=
  funext fun (a : α) => funext fun (b : α) => propext (iff.symm (map_rel_iff f))

protected theorem is_irrefl {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : r ↪r s) [is_irrefl β s] : is_irrefl α r :=
  is_irrefl.mk fun (a : α) => mt (iff.mpr (map_rel_iff f)) (irrefl (coe_fn f a))

protected theorem is_refl {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : r ↪r s) [is_refl β s] : is_refl α r :=
  is_refl.mk fun (a : α) => iff.mp (map_rel_iff f) (refl (coe_fn f a))

protected theorem is_symm {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : r ↪r s) [is_symm β s] : is_symm α r :=
  is_symm.mk fun (a b : α) => imp_imp_imp (iff.mpr (map_rel_iff f)) (iff.mp (map_rel_iff f)) symm

protected theorem is_asymm {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : r ↪r s) [is_asymm β s] : is_asymm α r :=
  is_asymm.mk fun (a b : α) (h₁ : r a b) (h₂ : r b a) => asymm (iff.mpr (map_rel_iff f) h₁) (iff.mpr (map_rel_iff f) h₂)

protected theorem is_antisymm {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : r ↪r s) [is_antisymm β s] : is_antisymm α r := sorry

protected theorem is_trans {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : r ↪r s) [is_trans β s] : is_trans α r := sorry

protected theorem is_total {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : r ↪r s) [is_total β s] : is_total α r := sorry

protected theorem is_preorder {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : r ↪r s) [is_preorder β s] : is_preorder α r :=
  idRhs (is_preorder α r) is_preorder.mk

protected theorem is_partial_order {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : r ↪r s) [is_partial_order β s] : is_partial_order α r :=
  idRhs (is_partial_order α r) is_partial_order.mk

protected theorem is_linear_order {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : r ↪r s) [is_linear_order β s] : is_linear_order α r :=
  idRhs (is_linear_order α r) is_linear_order.mk

protected theorem is_strict_order {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : r ↪r s) [is_strict_order β s] : is_strict_order α r :=
  idRhs (is_strict_order α r) is_strict_order.mk

protected theorem is_trichotomous {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : r ↪r s) [is_trichotomous β s] : is_trichotomous α r := sorry

protected theorem is_strict_total_order' {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : r ↪r s) [is_strict_total_order' β s] : is_strict_total_order' α r :=
  idRhs (is_strict_total_order' α r) is_strict_total_order'.mk

protected theorem acc {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : r ↪r s) (a : α) : acc s (coe_fn f a) → acc r a := sorry

protected theorem well_founded {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : r ↪r s) (h : well_founded s) : well_founded r :=
  well_founded.dcases_on h
    fun (h : ∀ (a : β), acc s a) =>
      idRhs (well_founded r) (well_founded.intro fun (a : α) => rel_embedding.acc f a (h (coe_fn f a)))

protected theorem is_well_order {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : r ↪r s) [is_well_order β s] : is_well_order α r :=
  idRhs (is_well_order α r) (is_well_order.mk (rel_embedding.well_founded f is_well_order.wf))

/-- It suffices to prove `f` is monotone between strict relations
  to show it is a relation embedding. -/
def of_monotone {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} [is_trichotomous α r] [is_asymm β s] (f : α → β) (H : ∀ (a b : α), r a b → s (f a) (f b)) : r ↪r s :=
  mk (function.embedding.mk f sorry) sorry

@[simp] theorem of_monotone_coe {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} [is_trichotomous α r] [is_asymm β s] (f : α → β) (H : ∀ (a b : α), r a b → s (f a) (f b)) : ⇑(of_monotone f H) = f :=
  rfl

/-- Embeddings of partial orders that preserve `<` also preserve `≤`  -/
def order_embedding_of_lt_embedding {α : Type u_1} {β : Type u_2} [partial_order α] [partial_order β] (f : Less ↪r Less) : α ↪o β :=
  mk (to_embedding f) sorry

end rel_embedding


namespace order_embedding


/-- lt is preserved by order embeddings of preorders -/
def lt_embedding {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] (f : α ↪o β) : Less ↪r Less :=
  rel_embedding.mk (rel_embedding.to_embedding f) sorry

@[simp] theorem lt_embedding_apply {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] (f : α ↪o β) (x : α) : coe_fn (lt_embedding f) x = coe_fn f x :=
  rfl

@[simp] theorem le_iff_le {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] (f : α ↪o β) {a : α} {b : α} : coe_fn f a ≤ coe_fn f b ↔ a ≤ b :=
  rel_embedding.map_rel_iff f

@[simp] theorem lt_iff_lt {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] (f : α ↪o β) {a : α} {b : α} : coe_fn f a < coe_fn f b ↔ a < b :=
  rel_embedding.map_rel_iff (lt_embedding f)

@[simp] theorem eq_iff_eq {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] (f : α ↪o β) {a : α} {b : α} : coe_fn f a = coe_fn f b ↔ a = b :=
  function.injective.eq_iff (rel_embedding.injective f)

protected theorem monotone {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] (f : α ↪o β) : monotone ⇑f :=
  fun (x y : α) => iff.mpr (le_iff_le f)

protected theorem strict_mono {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] (f : α ↪o β) : strict_mono ⇑f :=
  fun (x y : α) => iff.mpr (lt_iff_lt f)

protected theorem acc {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] (f : α ↪o β) (a : α) : acc Less (coe_fn f a) → acc Less a :=
  rel_embedding.acc (lt_embedding f) a

protected theorem well_founded {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] (f : α ↪o β) : well_founded Less → well_founded Less :=
  rel_embedding.well_founded (lt_embedding f)

protected theorem is_well_order {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] (f : α ↪o β) [is_well_order β Less] : is_well_order α Less :=
  rel_embedding.is_well_order (lt_embedding f)

/-- An order embedding is also an order embedding between dual orders. -/
protected def dual {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] (f : α ↪o β) : order_dual α ↪o order_dual β :=
  rel_embedding.mk (rel_embedding.to_embedding f) sorry

/-- A sctrictly monotone map from a linear order is an order embedding. --/
def of_strict_mono {α : Type u_1} {β : Type u_2} [linear_order α] [preorder β] (f : α → β) (h : strict_mono f) : α ↪o β :=
  rel_embedding.mk (function.embedding.mk f (strict_mono.injective h)) sorry

@[simp] theorem coe_of_strict_mono {α : Type u_1} {β : Type u_2} [linear_order α] [preorder β] {f : α → β} (h : strict_mono f) : ⇑(of_strict_mono f h) = f :=
  rfl

/-- Embedding of a subtype into the ambient type as an `order_embedding`. -/
def subtype {α : Type u_1} [preorder α] (p : α → Prop) : Subtype p ↪o α :=
  rel_embedding.mk (function.embedding.subtype p) sorry

@[simp] theorem coe_subtype {α : Type u_1} [preorder α] (p : α → Prop) : ⇑(subtype p) = coe :=
  rfl

end order_embedding


/-- A relation isomorphism is an equivalence that is also a relation embedding. -/
structure rel_iso {α : Type u_4} {β : Type u_5} (r : α → α → Prop) (s : β → β → Prop) 
extends α ≃ β
where
  map_rel_iff' : ∀ {a b : α}, s (coe_fn _to_equiv a) (coe_fn _to_equiv b) ↔ r a b

infixl:25 " ≃r " => Mathlib.rel_iso

/-- An order isomorphism is an equivalence such that `a ≤ b ↔ (f a) ≤ (f b)`.
This definition is an abbreviation of `rel_iso (≤) (≤)`. -/
def order_iso (α : Type u_1) (β : Type u_2) [HasLessEq α] [HasLessEq β] :=
  LessEq ≃r LessEq

infixl:25 " ≃o " => Mathlib.order_iso

namespace rel_iso


/-- Convert an `rel_iso` to an `rel_embedding`. This function is also available as a coercion
but often it is easier to write `f.to_rel_embedding` than to write explicitly `r` and `s`
in the target type. -/
def to_rel_embedding {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : r ≃r s) : r ↪r s :=
  rel_embedding.mk (equiv.to_embedding (to_equiv f)) (map_rel_iff' f)

-- see Note [function coercion]

protected instance rel_embedding.has_coe {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} : has_coe (r ≃r s) (r ↪r s) :=
  has_coe.mk to_rel_embedding

protected instance has_coe_to_fun {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} : has_coe_to_fun (r ≃r s) :=
  has_coe_to_fun.mk (fun (_x : r ≃r s) => α → β) fun (f : r ≃r s) => ⇑f

@[simp] theorem to_rel_embedding_eq_coe {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : r ≃r s) : to_rel_embedding f = ↑f :=
  rfl

@[simp] theorem coe_coe_fn {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : r ≃r s) : ⇑↑f = ⇑f :=
  rfl

theorem map_rel_iff {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : r ≃r s) {a : α} {b : α} : s (coe_fn f a) (coe_fn f b) ↔ r a b :=
  map_rel_iff' f

@[simp] theorem coe_fn_mk {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : α ≃ β) (o : ∀ {a b : α}, s (coe_fn f a) (coe_fn f b) ↔ r a b) : ⇑(mk f o) = ⇑f :=
  rfl

@[simp] theorem coe_fn_to_equiv {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : r ≃r s) : ⇑(to_equiv f) = ⇑f :=
  rfl

theorem injective_to_equiv {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} : function.injective to_equiv := sorry

/-- The map `coe_fn : (r ≃r s) → (α → β)` is injective. Lean fails to parse
`function.injective (λ e : r ≃r s, (e : α → β))`, so we use a trick to say the same. -/
theorem injective_coe_fn {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} : function.injective fun (e : r ≃r s) (x : α) => coe_fn e x :=
  function.injective.comp equiv.injective_coe_fn injective_to_equiv

theorem ext {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} {f : r ≃r s} {g : r ≃r s} (h : ∀ (x : α), coe_fn f x = coe_fn g x) : f = g :=
  injective_coe_fn (funext h)

theorem ext_iff {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} {f : r ≃r s} {g : r ≃r s} : f = g ↔ ∀ (x : α), coe_fn f x = coe_fn g x :=
  { mp := fun (h : f = g) (x : α) => h ▸ rfl, mpr := fun (h : ∀ (x : α), coe_fn f x = coe_fn g x) => ext h }

/-- Identity map is a relation isomorphism. -/
protected def refl {α : Type u_1} (r : α → α → Prop) : r ≃r r :=
  mk (equiv.refl α) sorry

/-- Inverse map of a relation isomorphism is a relation isomorphism. -/
protected def symm {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : r ≃r s) : s ≃r r :=
  mk (equiv.symm (to_equiv f)) sorry

/-- Composition of two relation isomorphisms is a relation isomorphism. -/
protected def trans {α : Type u_1} {β : Type u_2} {γ : Type u_3} {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop} (f₁ : r ≃r s) (f₂ : s ≃r t) : r ≃r t :=
  mk (equiv.trans (to_equiv f₁) (to_equiv f₂)) sorry

protected instance inhabited {α : Type u_1} (r : α → α → Prop) : Inhabited (r ≃r r) :=
  { default := rel_iso.refl r }

@[simp] theorem default_def {α : Type u_1} (r : α → α → Prop) : Inhabited.default = rel_iso.refl r :=
  rfl

/-- a relation isomorphism is also a relation isomorphism between dual relations. -/
protected def swap {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : r ≃r s) : function.swap r ≃r function.swap s :=
  mk (to_equiv f) sorry

@[simp] theorem coe_fn_symm_mk {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : α ≃ β) (o : ∀ {a b : α}, s (coe_fn f a) (coe_fn f b) ↔ r a b) : ⇑(rel_iso.symm (mk f o)) = ⇑(equiv.symm f) :=
  rfl

@[simp] theorem refl_apply {α : Type u_1} {r : α → α → Prop} (x : α) : coe_fn (rel_iso.refl r) x = x :=
  rfl

@[simp] theorem trans_apply {α : Type u_1} {β : Type u_2} {γ : Type u_3} {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop} (f : r ≃r s) (g : s ≃r t) (a : α) : coe_fn (rel_iso.trans f g) a = coe_fn g (coe_fn f a) :=
  rfl

@[simp] theorem apply_symm_apply {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (e : r ≃r s) (x : β) : coe_fn e (coe_fn (rel_iso.symm e) x) = x :=
  equiv.apply_symm_apply (to_equiv e) x

@[simp] theorem symm_apply_apply {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (e : r ≃r s) (x : α) : coe_fn (rel_iso.symm e) (coe_fn e x) = x :=
  equiv.symm_apply_apply (to_equiv e) x

theorem rel_symm_apply {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (e : r ≃r s) {x : α} {y : β} : r x (coe_fn (rel_iso.symm e) y) ↔ s (coe_fn e x) y := sorry

theorem symm_apply_rel {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (e : r ≃r s) {x : β} {y : α} : r (coe_fn (rel_iso.symm e) x) y ↔ s x (coe_fn e y) := sorry

protected theorem bijective {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (e : r ≃r s) : function.bijective ⇑e :=
  equiv.bijective (to_equiv e)

protected theorem injective {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (e : r ≃r s) : function.injective ⇑e :=
  equiv.injective (to_equiv e)

protected theorem surjective {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (e : r ≃r s) : function.surjective ⇑e :=
  equiv.surjective (to_equiv e)

@[simp] theorem range_eq {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (e : r ≃r s) : set.range ⇑e = set.univ :=
  function.surjective.range_eq (rel_iso.surjective e)

@[simp] theorem eq_iff_eq {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : r ≃r s) {a : α} {b : α} : coe_fn f a = coe_fn f b ↔ a = b :=
  function.injective.eq_iff (rel_iso.injective f)

/-- Any equivalence lifts to a relation isomorphism between `s` and its preimage. -/
protected def preimage {α : Type u_1} {β : Type u_2} (f : α ≃ β) (s : β → β → Prop) : ⇑f ⁻¹'o s ≃r s :=
  mk f sorry

/-- A surjective relation embedding is a relation isomorphism. -/
def of_surjective {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : r ↪r s) (H : function.surjective ⇑f) : r ≃r s :=
  mk (equiv.of_bijective ⇑f sorry) sorry

@[simp] theorem of_surjective_coe {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : r ↪r s) (H : function.surjective ⇑f) : ⇑(of_surjective f H) = ⇑f :=
  rfl

/--
Given relation isomorphisms `r₁ ≃r r₂` and `s₁ ≃r s₂`, construct a relation isomorphism for the
lexicographic orders on the sum.
-/
def sum_lex_congr {α₁ : Type u_1} {α₂ : Type u_2} {β₁ : Type u_3} {β₂ : Type u_4} {r₁ : α₁ → α₁ → Prop} {r₂ : α₂ → α₂ → Prop} {s₁ : β₁ → β₁ → Prop} {s₂ : β₂ → β₂ → Prop} (e₁ : r₁ ≃r r₂) (e₂ : s₁ ≃r s₂) : sum.lex r₁ s₁ ≃r sum.lex r₂ s₂ :=
  mk (equiv.sum_congr (to_equiv e₁) (to_equiv e₂)) sorry

/--
Given relation isomorphisms `r₁ ≃r r₂` and `s₁ ≃r s₂`, construct a relation isomorphism for the
lexicographic orders on the product.
-/
def prod_lex_congr {α₁ : Type u_1} {α₂ : Type u_2} {β₁ : Type u_3} {β₂ : Type u_4} {r₁ : α₁ → α₁ → Prop} {r₂ : α₂ → α₂ → Prop} {s₁ : β₁ → β₁ → Prop} {s₂ : β₂ → β₂ → Prop} (e₁ : r₁ ≃r r₂) (e₂ : s₁ ≃r s₂) : prod.lex r₁ s₁ ≃r prod.lex r₂ s₂ :=
  mk (equiv.prod_congr (to_equiv e₁) (to_equiv e₂)) sorry

protected instance group {α : Type u_1} {r : α → α → Prop} : group (r ≃r r) :=
  group.mk (fun (f₁ f₂ : r ≃r r) => rel_iso.trans f₂ f₁) sorry (rel_iso.refl r) sorry sorry rel_iso.symm
    (div_inv_monoid.div._default (fun (f₁ f₂ : r ≃r r) => rel_iso.trans f₂ f₁) sorry (rel_iso.refl r) sorry sorry
      rel_iso.symm)
    sorry

@[simp] theorem coe_one {α : Type u_1} {r : α → α → Prop} : ⇑1 = id :=
  rfl

@[simp] theorem coe_mul {α : Type u_1} {r : α → α → Prop} (e₁ : r ≃r r) (e₂ : r ≃r r) : ⇑(e₁ * e₂) = ⇑e₁ ∘ ⇑e₂ :=
  rfl

theorem mul_apply {α : Type u_1} {r : α → α → Prop} (e₁ : r ≃r r) (e₂ : r ≃r r) (x : α) : coe_fn (e₁ * e₂) x = coe_fn e₁ (coe_fn e₂ x) :=
  rfl

@[simp] theorem inv_apply_self {α : Type u_1} {r : α → α → Prop} (e : r ≃r r) (x : α) : coe_fn (e⁻¹) (coe_fn e x) = x :=
  symm_apply_apply e x

@[simp] theorem apply_inv_self {α : Type u_1} {r : α → α → Prop} (e : r ≃r r) (x : α) : coe_fn e (coe_fn (e⁻¹) x) = x :=
  apply_symm_apply e x

end rel_iso


namespace order_iso


/-- Reinterpret an order isomorphism as an order embedding. -/
def to_order_embedding {α : Type u_1} {β : Type u_2} [HasLessEq α] [HasLessEq β] (e : α ≃o β) : α ↪o β :=
  rel_iso.to_rel_embedding e

@[simp] theorem coe_to_order_embedding {α : Type u_1} {β : Type u_2} [HasLessEq α] [HasLessEq β] (e : α ≃o β) : ⇑(to_order_embedding e) = ⇑e :=
  rfl

protected theorem bijective {α : Type u_1} {β : Type u_2} [HasLessEq α] [HasLessEq β] (e : α ≃o β) : function.bijective ⇑e :=
  equiv.bijective (rel_iso.to_equiv e)

protected theorem injective {α : Type u_1} {β : Type u_2} [HasLessEq α] [HasLessEq β] (e : α ≃o β) : function.injective ⇑e :=
  equiv.injective (rel_iso.to_equiv e)

protected theorem surjective {α : Type u_1} {β : Type u_2} [HasLessEq α] [HasLessEq β] (e : α ≃o β) : function.surjective ⇑e :=
  equiv.surjective (rel_iso.to_equiv e)

@[simp] theorem range_eq {α : Type u_1} {β : Type u_2} [HasLessEq α] [HasLessEq β] (e : α ≃o β) : set.range ⇑e = set.univ :=
  function.surjective.range_eq (order_iso.surjective e)

@[simp] theorem apply_eq_iff_eq {α : Type u_1} {β : Type u_2} [HasLessEq α] [HasLessEq β] (e : α ≃o β) {x : α} {y : α} : coe_fn e x = coe_fn e y ↔ x = y :=
  equiv.apply_eq_iff_eq (rel_iso.to_equiv e)

/-- Inverse of an order isomorphism. -/
def symm {α : Type u_1} {β : Type u_2} [HasLessEq α] [HasLessEq β] (e : α ≃o β) : β ≃o α :=
  rel_iso.symm e

@[simp] theorem apply_symm_apply {α : Type u_1} {β : Type u_2} [HasLessEq α] [HasLessEq β] (e : α ≃o β) (x : β) : coe_fn e (coe_fn (symm e) x) = x :=
  equiv.apply_symm_apply (rel_iso.to_equiv e) x

@[simp] theorem symm_apply_apply {α : Type u_1} {β : Type u_2} [HasLessEq α] [HasLessEq β] (e : α ≃o β) (x : α) : coe_fn (symm e) (coe_fn e x) = x :=
  equiv.symm_apply_apply (rel_iso.to_equiv e) x

theorem symm_apply_eq {α : Type u_1} {β : Type u_2} [HasLessEq α] [HasLessEq β] (e : α ≃o β) {x : α} {y : β} : coe_fn (symm e) y = x ↔ y = coe_fn e x :=
  equiv.symm_apply_eq (rel_iso.to_equiv e)

@[simp] theorem symm_symm {α : Type u_1} {β : Type u_2} [HasLessEq α] [HasLessEq β] (e : α ≃o β) : symm (symm e) = e :=
  rel_iso.ext fun (x : α) => Eq.refl (coe_fn (symm (symm e)) x)

theorem symm_injective {α : Type u_1} {β : Type u_2} [HasLessEq α] [HasLessEq β] : function.injective symm := sorry

@[simp] theorem to_equiv_symm {α : Type u_1} {β : Type u_2} [HasLessEq α] [HasLessEq β] (e : α ≃o β) : equiv.symm (rel_iso.to_equiv e) = rel_iso.to_equiv (symm e) :=
  rfl

/-- Composition of two order isomorphisms is an order isomorphism. -/
def trans {α : Type u_1} {β : Type u_2} {γ : Type u_3} [HasLessEq α] [HasLessEq β] [HasLessEq γ] (e : α ≃o β) (e' : β ≃o γ) : α ≃o γ :=
  rel_iso.trans e e'

@[simp] theorem coe_trans {α : Type u_1} {β : Type u_2} {γ : Type u_3} [HasLessEq α] [HasLessEq β] [HasLessEq γ] (e : α ≃o β) (e' : β ≃o γ) : ⇑(trans e e') = ⇑e' ∘ ⇑e :=
  rfl

theorem trans_apply {α : Type u_1} {β : Type u_2} {γ : Type u_3} [HasLessEq α] [HasLessEq β] [HasLessEq γ] (e : α ≃o β) (e' : β ≃o γ) (x : α) : coe_fn (trans e e') x = coe_fn e' (coe_fn e x) :=
  rfl

protected theorem monotone {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] (e : α ≃o β) : monotone ⇑e :=
  order_embedding.monotone (to_order_embedding e)

protected theorem strict_mono {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] (e : α ≃o β) : strict_mono ⇑e :=
  order_embedding.strict_mono (to_order_embedding e)

@[simp] theorem le_iff_le {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] (e : α ≃o β) {x : α} {y : α} : coe_fn e x ≤ coe_fn e y ↔ x ≤ y :=
  rel_iso.map_rel_iff e

@[simp] theorem lt_iff_lt {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] (e : α ≃o β) {x : α} {y : α} : coe_fn e x < coe_fn e y ↔ x < y :=
  order_embedding.lt_iff_lt (to_order_embedding e)

@[simp] theorem preimage_Iic {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] (e : α ≃o β) (b : β) : ⇑e ⁻¹' set.Iic b = set.Iic (coe_fn (symm e) b) := sorry

@[simp] theorem preimage_Ici {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] (e : α ≃o β) (b : β) : ⇑e ⁻¹' set.Ici b = set.Ici (coe_fn (symm e) b) := sorry

@[simp] theorem preimage_Iio {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] (e : α ≃o β) (b : β) : ⇑e ⁻¹' set.Iio b = set.Iio (coe_fn (symm e) b) := sorry

@[simp] theorem preimage_Ioi {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] (e : α ≃o β) (b : β) : ⇑e ⁻¹' set.Ioi b = set.Ioi (coe_fn (symm e) b) := sorry

@[simp] theorem preimage_Icc {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] (e : α ≃o β) (a : β) (b : β) : ⇑e ⁻¹' set.Icc a b = set.Icc (coe_fn (symm e) a) (coe_fn (symm e) b) := sorry

@[simp] theorem preimage_Ico {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] (e : α ≃o β) (a : β) (b : β) : ⇑e ⁻¹' set.Ico a b = set.Ico (coe_fn (symm e) a) (coe_fn (symm e) b) := sorry

@[simp] theorem preimage_Ioc {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] (e : α ≃o β) (a : β) (b : β) : ⇑e ⁻¹' set.Ioc a b = set.Ioc (coe_fn (symm e) a) (coe_fn (symm e) b) := sorry

@[simp] theorem preimage_Ioo {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] (e : α ≃o β) (a : β) (b : β) : ⇑e ⁻¹' set.Ioo a b = set.Ioo (coe_fn (symm e) a) (coe_fn (symm e) b) := sorry

/-- To show that `f : α → β`, `g : β → α` make up an order isomorphism of linear orders,
    it suffices to prove `cmp a (g b) = cmp (f a) b`. --/
def of_cmp_eq_cmp {α : Type u_1} {β : Type u_2} [linear_order α] [linear_order β] (f : α → β) (g : β → α) (h : ∀ (a : α) (b : β), cmp a (g b) = cmp (f a) b) : α ≃o β :=
  (fun (gf : ∀ (a : α), a = g (f a)) => rel_iso.mk (equiv.mk f g sorry sorry) sorry) sorry

/-- Order isomorphism between two equal sets. -/
def set_congr {α : Type u_1} [preorder α] (s : set α) (t : set α) (h : s = t) : ↥s ≃o ↥t :=
  rel_iso.mk (equiv.set_congr h) sorry

/-- Order isomorphism between `univ : set α` and `α`. -/
def set.univ {α : Type u_1} [preorder α] : ↥set.univ ≃o α :=
  rel_iso.mk (equiv.set.univ α) sorry

end order_iso


/-- If a function `f` is strictly monotone on a set `s`, then it defines an order isomorphism
between `s` and its image. -/
protected def strict_mono_incr_on.order_iso {α : Type u_1} {β : Type u_2} [linear_order α] [preorder β] (f : α → β) (s : set α) (hf : strict_mono_incr_on f s) : ↥s ≃o ↥(f '' s) :=
  rel_iso.mk (set.bij_on.equiv f sorry) sorry

/-- A strictly monotone function from a linear order is an order isomorphism between its domain and
its range. -/
protected def strict_mono.order_iso {α : Type u_1} {β : Type u_2} [linear_order α] [preorder β] (f : α → β) (h_mono : strict_mono f) : α ≃o ↥(set.range f) :=
  rel_iso.mk (equiv.set.range f (strict_mono.injective h_mono)) sorry

/-- A strictly monotone surjective function from a linear order is an order isomorphism. -/
def strict_mono.order_iso_of_surjective {α : Type u_1} {β : Type u_2} [linear_order α] [preorder β] (f : α → β) (h_mono : strict_mono f) (h_surj : function.surjective f) : α ≃o β :=
  order_iso.trans (strict_mono.order_iso f h_mono)
    (order_iso.trans (order_iso.set_congr (set.range f) set.univ (function.surjective.range_eq h_surj))
      order_iso.set.univ)

/-- `subrel r p` is the inherited relation on a subset. -/
def subrel {α : Type u_1} (r : α → α → Prop) (p : set α) : ↥p → ↥p → Prop :=
  coe ⁻¹'o r

@[simp] theorem subrel_val {α : Type u_1} (r : α → α → Prop) (p : set α) {a : ↥p} {b : ↥p} : subrel r p a b ↔ r (subtype.val a) (subtype.val b) :=
  iff.rfl

namespace subrel


/-- The relation embedding from the inherited relation on a subset. -/
protected def rel_embedding {α : Type u_1} (r : α → α → Prop) (p : set α) : subrel r p ↪r r :=
  rel_embedding.mk (function.embedding.subtype fun (x : α) => x ∈ p) sorry

@[simp] theorem rel_embedding_apply {α : Type u_1} (r : α → α → Prop) (p : set α) (a : ↥p) : coe_fn (subrel.rel_embedding r p) a = subtype.val a :=
  rfl

protected instance is_well_order {α : Type u_1} (r : α → α → Prop) [is_well_order α r] (p : set α) : is_well_order (↥p) (subrel r p) :=
  rel_embedding.is_well_order (subrel.rel_embedding r p)

end subrel


/-- Restrict the codomain of a relation embedding. -/
def rel_embedding.cod_restrict {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (p : set β) (f : r ↪r s) (H : ∀ (a : α), coe_fn f a ∈ p) : r ↪r subrel s p :=
  rel_embedding.mk (function.embedding.cod_restrict p (rel_embedding.to_embedding f) H) (rel_embedding.map_rel_iff' f)

@[simp] theorem rel_embedding.cod_restrict_apply {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (p : set β) (f : r ↪r s) (H : ∀ (a : α), coe_fn f a ∈ p) (a : α) : coe_fn (rel_embedding.cod_restrict p f H) a = { val := coe_fn f a, property := H a } :=
  rfl

protected def order_iso.dual {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] (f : α ≃o β) : order_dual α ≃o order_dual β :=
  rel_iso.mk (rel_iso.to_equiv f) sorry

theorem order_iso.map_bot' {α : Type u_1} {β : Type u_2} [partial_order α] [partial_order β] (f : α ≃o β) {x : α} {y : β} (hx : ∀ (x' : α), x ≤ x') (hy : ∀ (y' : β), y ≤ y') : coe_fn f x = y := sorry

theorem order_iso.map_bot {α : Type u_1} {β : Type u_2} [order_bot α] [order_bot β] (f : α ≃o β) : coe_fn f ⊥ = ⊥ :=
  order_iso.map_bot' f (fun (_x : α) => bot_le) fun (_x : β) => bot_le

theorem order_iso.map_top' {α : Type u_1} {β : Type u_2} [partial_order α] [partial_order β] (f : α ≃o β) {x : α} {y : β} (hx : ∀ (x' : α), x' ≤ x) (hy : ∀ (y' : β), y' ≤ y) : coe_fn f x = y :=
  order_iso.map_bot' (order_iso.dual f) hx hy

theorem order_iso.map_top {α : Type u_1} {β : Type u_2} [order_top α] [order_top β] (f : α ≃o β) : coe_fn f ⊤ = ⊤ :=
  order_iso.map_bot (order_iso.dual f)

theorem order_embedding.map_inf_le {α : Type u_1} {β : Type u_2} [semilattice_inf α] [semilattice_inf β] (f : α ↪o β) (x : α) (y : α) : coe_fn f (x ⊓ y) ≤ coe_fn f x ⊓ coe_fn f y :=
  monotone.map_inf_le (order_embedding.monotone f) x y

theorem order_iso.map_inf {α : Type u_1} {β : Type u_2} [semilattice_inf α] [semilattice_inf β] (f : α ≃o β) (x : α) (y : α) : coe_fn f (x ⊓ y) = coe_fn f x ⊓ coe_fn f y := sorry

theorem order_embedding.le_map_sup {α : Type u_1} {β : Type u_2} [semilattice_sup α] [semilattice_sup β] (f : α ↪o β) (x : α) (y : α) : coe_fn f x ⊔ coe_fn f y ≤ coe_fn f (x ⊔ y) :=
  monotone.le_map_sup (order_embedding.monotone f) x y

theorem order_iso.map_sup {α : Type u_1} {β : Type u_2} [semilattice_sup α] [semilattice_sup β] (f : α ≃o β) (x : α) (y : α) : coe_fn f (x ⊔ y) = coe_fn f x ⊔ coe_fn f y :=
  order_iso.map_inf (order_iso.dual f) x y

