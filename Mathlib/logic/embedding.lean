/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.equiv.basic
import Mathlib.data.sigma.basic
import Mathlib.algebra.group.defs
import Mathlib.PostPort

universes u_1 u_2 l u v u_3 w x u_4 

namespace Mathlib

/-!
# Injective functions
-/

namespace function


/-- `α ↪ β` is a bundled injective function. -/
structure embedding (α : Sort u_1) (β : Sort u_2) 
where
  to_fun : α → β
  inj' : injective to_fun

infixr:25 " ↪ " => Mathlib.function.embedding

protected instance embedding.has_coe_to_fun {α : Sort u} {β : Sort v} : has_coe_to_fun (α ↪ β) :=
  has_coe_to_fun.mk (fun (x : α ↪ β) => α → β) embedding.to_fun

end function


/-- Convert an `α ≃ β` to `α ↪ β`. -/
@[simp] theorem equiv.to_embedding_apply {α : Sort u} {β : Sort v} (f : α ≃ β) : ∀ (ᾰ : α), coe_fn (equiv.to_embedding f) ᾰ = coe_fn f ᾰ :=
  fun (ᾰ : α) => Eq.refl (coe_fn (equiv.to_embedding f) ᾰ)

namespace function


namespace embedding


theorem ext {α : Sort u_1} {β : Sort u_2} {f : α ↪ β} {g : α ↪ β} (h : ∀ (x : α), coe_fn f x = coe_fn g x) : f = g := sorry

theorem ext_iff {α : Sort u_1} {β : Sort u_2} {f : α ↪ β} {g : α ↪ β} : (∀ (x : α), coe_fn f x = coe_fn g x) ↔ f = g := sorry

@[simp] theorem to_fun_eq_coe {α : Sort u_1} {β : Sort u_2} (f : α ↪ β) : to_fun f = ⇑f :=
  rfl

@[simp] theorem coe_fn_mk {α : Sort u_1} {β : Sort u_2} (f : α → β) (i : injective f) : ⇑(mk f i) = f :=
  rfl

theorem injective {α : Sort u_1} {β : Sort u_2} (f : α ↪ β) : injective ⇑f :=
  inj' f

@[simp] theorem refl_apply (α : Sort u_1) (a : α) : coe_fn (embedding.refl α) a = a :=
  Eq.refl a

@[simp] theorem trans_apply {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α ↪ β) (g : β ↪ γ) : ∀ (ᾰ : α), coe_fn (embedding.trans f g) ᾰ = coe_fn g (coe_fn f ᾰ) :=
  fun (ᾰ : α) => Eq.refl (coe_fn g (coe_fn f ᾰ))

@[simp] theorem equiv_to_embedding_trans_symm_to_embedding {α : Sort u_1} {β : Sort u_2} (e : α ≃ β) : embedding.trans (equiv.to_embedding e) (equiv.to_embedding (equiv.symm e)) = embedding.refl α := sorry

@[simp] theorem equiv_symm_to_embedding_trans_to_embedding {α : Sort u_1} {β : Sort u_2} (e : α ≃ β) : embedding.trans (equiv.to_embedding (equiv.symm e)) (equiv.to_embedding e) = embedding.refl β := sorry

protected def congr {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort x} (e₁ : α ≃ β) (e₂ : γ ≃ δ) (f : α ↪ γ) : β ↪ δ :=
  embedding.trans (equiv.to_embedding (equiv.symm e₁)) (embedding.trans f (equiv.to_embedding e₂))

/-- A right inverse `surj_inv` of a surjective function as an `embedding`. -/
protected def of_surjective {α : Sort u_1} {β : Sort u_2} (f : β → α) (hf : surjective f) : α ↪ β :=
  mk (surj_inv hf) (injective_surj_inv hf)

/-- Convert a surjective `embedding` to an `equiv` -/
protected def equiv_of_surjective {α : Sort u_1} {β : Type u_2} (f : α ↪ β) (hf : surjective ⇑f) : α ≃ β :=
  equiv.of_bijective ⇑f sorry

protected def of_not_nonempty {α : Sort u_1} {β : Sort u_2} (hα : ¬Nonempty α) : α ↪ β :=
  mk (fun (a : α) => false.elim sorry) sorry

/-- Change the value of an embedding `f` at one point. If the prescribed image
is already occupied by some `f a'`, then swap the values at these two points. -/
def set_value {α : Sort u_1} {β : Sort u_2} (f : α ↪ β) (a : α) (b : β) [(a' : α) → Decidable (a' = a)] [(a' : α) → Decidable (coe_fn f a' = b)] : α ↪ β :=
  mk (fun (a' : α) => ite (a' = a) b (ite (coe_fn f a' = b) (coe_fn f a) (coe_fn f a'))) sorry

theorem set_value_eq {α : Sort u_1} {β : Sort u_2} (f : α ↪ β) (a : α) (b : β) [(a' : α) → Decidable (a' = a)] [(a' : α) → Decidable (coe_fn f a' = b)] : coe_fn (set_value f a b) a = b := sorry

/-- Embedding into `option` -/
protected def some {α : Type u_1} : α ↪ Option α :=
  mk some (option.some_injective α)

/-- Embedding of a `subtype`. -/
def subtype {α : Sort u_1} (p : α → Prop) : Subtype p ↪ α :=
  mk coe sorry

@[simp] theorem coe_subtype {α : Sort u_1} (p : α → Prop) : ⇑(subtype p) = coe :=
  rfl

/-- Choosing an element `b : β` gives an embedding of `punit` into `β`. -/
def punit {β : Sort u_1} (b : β) : PUnit ↪ β :=
  mk (fun (_x : PUnit) => b) sorry

/-- Fixing an element `b : β` gives an embedding `α ↪ α × β`. -/
def sectl (α : Type u_1) {β : Type u_2} (b : β) : α ↪ α × β :=
  mk (fun (a : α) => (a, b)) sorry

/-- Fixing an element `a : α` gives an embedding `β ↪ α × β`. -/
def sectr {α : Type u_1} (a : α) (β : Type u_2) : β ↪ α × β :=
  mk (fun (b : β) => (a, b)) sorry

/-- Restrict the codomain of an embedding. -/
def cod_restrict {α : Sort u_1} {β : Type u_2} (p : set β) (f : α ↪ β) (H : ∀ (a : α), coe_fn f a ∈ p) : α ↪ ↥p :=
  mk (fun (a : α) => { val := coe_fn f a, property := H a }) sorry

@[simp] theorem cod_restrict_apply {α : Sort u_1} {β : Type u_2} (p : set β) (f : α ↪ β) (H : ∀ (a : α), coe_fn f a ∈ p) (a : α) : coe_fn (cod_restrict p f H) a = { val := coe_fn f a, property := H a } :=
  rfl

/-- If `e₁` and `e₂` are embeddings, then so is `prod.map e₁ e₂ : (a, b) ↦ (e₁ a, e₂ b)`. -/
def prod_map {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : α × γ ↪ β × δ :=
  mk (prod.map ⇑e₁ ⇑e₂) sorry

@[simp] theorem coe_prod_map {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : ⇑(prod_map e₁ e₂) = prod.map ⇑e₁ ⇑e₂ :=
  rfl

/-- If `e₁` and `e₂` are embeddings, then so is `sum.map e₁ e₂`. -/
def sum_map {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : α ⊕ γ ↪ β ⊕ δ :=
  mk (sum.map ⇑e₁ ⇑e₂) sorry

@[simp] theorem coe_sum_map {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : ⇑(sum_map e₁ e₂) = sum.map ⇑e₁ ⇑e₂ :=
  rfl

/-- The embedding of `α` into the sum `α ⊕ β`. -/
@[simp] theorem inl_apply {α : Type u_1} {β : Type u_2} (val : α) : coe_fn inl val = sum.inl val :=
  Eq.refl (coe_fn inl val)

/-- The embedding of `β` into the sum `α ⊕ β`. -/
@[simp] theorem inr_apply {α : Type u_1} {β : Type u_2} (val : β) : coe_fn inr val = sum.inr val :=
  Eq.refl (coe_fn inr val)

/-- `sigma.mk` as an `function.embedding`. -/
@[simp] theorem sigma_mk_apply {α : Type u_1} {β : α → Type u_3} (a : α) (snd : β a) : coe_fn (sigma_mk a) snd = sigma.mk a snd :=
  Eq.refl (coe_fn (sigma_mk a) snd)

/-- If `f : α ↪ α'` is an embedding and `g : Π a, β α ↪ β' (f α)` is a family
of embeddings, then `sigma.map f g` is an embedding. -/
@[simp] theorem sigma_map_apply {α : Type u_1} {α' : Type u_2} {β : α → Type u_3} {β' : α' → Type u_4} (f : α ↪ α') (g : (a : α) → β a ↪ β' (coe_fn f a)) (x : sigma fun (a : α) => β a) : coe_fn (sigma_map f g) x = sigma.map (⇑f) (fun (a : α) => ⇑(g a)) x :=
  Eq.refl (coe_fn (sigma_map f g) x)

def Pi_congr_right {α : Sort u_1} {β : α → Sort u_2} {γ : α → Sort u_3} (e : (a : α) → β a ↪ γ a) : ((a : α) → β a) ↪ (a : α) → γ a :=
  mk (fun (f : (a : α) → β a) (a : α) => coe_fn (e a) (f a)) sorry

def arrow_congr_left {α : Sort u} {β : Sort v} {γ : Sort w} (e : α ↪ β) : (γ → α) ↪ γ → β :=
  Pi_congr_right fun (_x : γ) => e

def arrow_congr_right {α : Sort u} {β : Sort v} {γ : Sort w} [Inhabited γ] (e : α ↪ β) : (α → γ) ↪ β → γ :=
  let f' : (α → γ) → β → γ :=
    fun (f : α → γ) (b : β) =>
      dite (∃ (c : α), coe_fn e c = b) (fun (h : ∃ (c : α), coe_fn e c = b) => f (classical.some h))
        fun (h : ¬∃ (c : α), coe_fn e c = b) => Inhabited.default;
  mk f' sorry

protected def subtype_map {α : Sort u_1} {β : Sort u_2} {p : α → Prop} {q : β → Prop} (f : α ↪ β) (h : ∀ {x : α}, p x → q (coe_fn f x)) : (Subtype fun (x : α) => p x) ↪ Subtype fun (y : β) => q y :=
  mk (subtype.map (⇑f) h) sorry

/-- `set.image` as an embedding `set α ↪ set β`. -/
protected def image {α : Type u_1} {β : Type u_2} (f : α ↪ β) : set α ↪ set β :=
  mk (set.image ⇑f) sorry

theorem swap_apply {α : Type u_1} {β : Type u_2} [DecidableEq α] [DecidableEq β] (f : α ↪ β) (x : α) (y : α) (z : α) : coe_fn (equiv.swap (coe_fn f x) (coe_fn f y)) (coe_fn f z) = coe_fn f (coe_fn (equiv.swap x y) z) :=
  injective.swap_apply (injective f) x y z

theorem swap_comp {α : Type u_1} {β : Type u_2} [DecidableEq α] [DecidableEq β] (f : α ↪ β) (x : α) (y : α) : ⇑(equiv.swap (coe_fn f x) (coe_fn f y)) ∘ ⇑f = ⇑f ∘ ⇑(equiv.swap x y) :=
  injective.swap_comp (injective f) x y

end embedding


end function


namespace equiv


@[simp] theorem refl_to_embedding {α : Type u_1} : equiv.to_embedding (equiv.refl α) = function.embedding.refl α :=
  rfl

@[simp] theorem trans_to_embedding {α : Type u_1} {β : Type u_2} {γ : Type u_3} (e : α ≃ β) (f : β ≃ γ) : equiv.to_embedding (equiv.trans e f) = function.embedding.trans (equiv.to_embedding e) (equiv.to_embedding f) :=
  rfl

end equiv


namespace set


/-- The injection map is an embedding between subsets. -/
def embedding_of_subset {α : Type u_1} (s : set α) (t : set α) (h : s ⊆ t) : ↥s ↪ ↥t :=
  function.embedding.mk (fun (x : ↥s) => { val := subtype.val x, property := sorry }) sorry

end set


-- TODO: these two definitions probably belong somewhere else, so that we can remove the

-- `algebra.group.defs` import.

/--
The embedding of a left cancellative semigroup into itself
by left multiplication by a fixed element.
 -/
@[simp] theorem add_left_embedding_apply {G : Type u} [add_left_cancel_semigroup G] (g : G) (h : G) : coe_fn (add_left_embedding g) h = g + h :=
  Eq.refl (coe_fn (add_left_embedding g) h)

/--
The embedding of a right cancellative semigroup into itself
by right multiplication by a fixed element.
 -/
def mul_right_embedding {G : Type u} [right_cancel_semigroup G] (g : G) : G ↪ G :=
  function.embedding.mk (fun (h : G) => h * g) (mul_left_injective g)

