/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.set.lattice
import PostPort

universes u v l u_1 w x u_2 u_3 

namespace Mathlib

/-- A `pequiv` is a partial equivalence, a representation of a bijection between a subset
  of `α` and a subset of `β` -/
structure pequiv (α : Type u) (β : Type v) 
where
  to_fun : α → Option β
  inv_fun : β → Option α
  inv : ∀ (a : α) (b : β), a ∈ inv_fun b ↔ b ∈ to_fun a

infixr:25 " ≃. " => Mathlib.pequiv

namespace pequiv


protected instance has_coe_to_fun {α : Type u} {β : Type v} : has_coe_to_fun (α ≃. β) :=
  has_coe_to_fun.mk (fun (x : α ≃. β) => α → Option β) to_fun

@[simp] theorem coe_mk_apply {α : Type u} {β : Type v} (f₁ : α → Option β) (f₂ : β → Option α) (h : ∀ (a : α) (b : β), a ∈ f₂ b ↔ b ∈ f₁ a) (x : α) : coe_fn (mk f₁ f₂ h) x = f₁ x :=
  rfl

theorem ext {α : Type u} {β : Type v} {f : α ≃. β} {g : α ≃. β} (h : ∀ (x : α), coe_fn f x = coe_fn g x) : f = g := sorry

theorem ext_iff {α : Type u} {β : Type v} {f : α ≃. β} {g : α ≃. β} : f = g ↔ ∀ (x : α), coe_fn f x = coe_fn g x :=
  { mp := congr_fun ∘ congr_arg fun {f : α ≃. β} (x : α) => coe_fn f x, mpr := ext }

protected def refl (α : Type u_1) : α ≃. α :=
  mk some some sorry

protected def symm {α : Type u} {β : Type v} (f : α ≃. β) : β ≃. α :=
  mk (inv_fun f) (to_fun f) sorry

theorem mem_iff_mem {α : Type u} {β : Type v} (f : α ≃. β) {a : α} {b : β} : a ∈ coe_fn (pequiv.symm f) b ↔ b ∈ coe_fn f a :=
  inv f

theorem eq_some_iff {α : Type u} {β : Type v} (f : α ≃. β) {a : α} {b : β} : coe_fn (pequiv.symm f) b = some a ↔ coe_fn f a = some b :=
  inv f

protected def trans {α : Type u} {β : Type v} {γ : Type w} (f : α ≃. β) (g : β ≃. γ) : α ≃. γ :=
  mk (fun (a : α) => option.bind (coe_fn f a) ⇑g) (fun (a : γ) => option.bind (coe_fn (pequiv.symm g) a) ⇑(pequiv.symm f))
    sorry

@[simp] theorem refl_apply {α : Type u} (a : α) : coe_fn (pequiv.refl α) a = some a :=
  rfl

@[simp] theorem symm_refl {α : Type u} : pequiv.symm (pequiv.refl α) = pequiv.refl α :=
  rfl

@[simp] theorem symm_symm {α : Type u} {β : Type v} (f : α ≃. β) : pequiv.symm (pequiv.symm f) = f := sorry

theorem symm_injective {α : Type u} {β : Type v} : function.injective pequiv.symm :=
  function.left_inverse.injective symm_symm

theorem trans_assoc {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} (f : α ≃. β) (g : β ≃. γ) (h : γ ≃. δ) : pequiv.trans (pequiv.trans f g) h = pequiv.trans f (pequiv.trans g h) :=
  ext fun (_x : α) => option.bind_assoc (coe_fn f _x) ⇑g ⇑h

theorem mem_trans {α : Type u} {β : Type v} {γ : Type w} (f : α ≃. β) (g : β ≃. γ) (a : α) (c : γ) : c ∈ coe_fn (pequiv.trans f g) a ↔ ∃ (b : β), b ∈ coe_fn f a ∧ c ∈ coe_fn g b :=
  option.bind_eq_some'

theorem trans_eq_some {α : Type u} {β : Type v} {γ : Type w} (f : α ≃. β) (g : β ≃. γ) (a : α) (c : γ) : coe_fn (pequiv.trans f g) a = some c ↔ ∃ (b : β), coe_fn f a = some b ∧ coe_fn g b = some c :=
  option.bind_eq_some'

theorem trans_eq_none {α : Type u} {β : Type v} {γ : Type w} (f : α ≃. β) (g : β ≃. γ) (a : α) : coe_fn (pequiv.trans f g) a = none ↔ ∀ (b : β) (c : γ), ¬b ∈ coe_fn f a ∨ ¬c ∈ coe_fn g b := sorry

@[simp] theorem refl_trans {α : Type u} {β : Type v} (f : α ≃. β) : pequiv.trans (pequiv.refl α) f = f :=
  ext fun (x : α) => option.ext fun (a : β) => id (iff.refl (a ∈ coe_fn f x))

@[simp] theorem trans_refl {α : Type u} {β : Type v} (f : α ≃. β) : pequiv.trans f (pequiv.refl β) = f := sorry

protected theorem inj {α : Type u} {β : Type v} (f : α ≃. β) {a₁ : α} {a₂ : α} {b : β} (h₁ : b ∈ coe_fn f a₁) (h₂ : b ∈ coe_fn f a₂) : a₁ = a₂ := sorry

theorem injective_of_forall_ne_is_some {α : Type u} {β : Type v} (f : α ≃. β) (a₂ : α) (h : ∀ (a₁ : α), a₁ ≠ a₂ → ↥(option.is_some (coe_fn f a₁))) : function.injective ⇑f := sorry

theorem injective_of_forall_is_some {α : Type u} {β : Type v} {f : α ≃. β} (h : ∀ (a : α), ↥(option.is_some (coe_fn f a))) : function.injective ⇑f := sorry

def of_set {α : Type u} (s : set α) [decidable_pred s] : α ≃. α :=
  mk (fun (a : α) => ite (a ∈ s) (some a) none) (fun (a : α) => ite (a ∈ s) (some a) none) sorry

theorem mem_of_set_self_iff {α : Type u} {s : set α} [decidable_pred s] {a : α} : a ∈ coe_fn (of_set s) a ↔ a ∈ s := sorry

theorem mem_of_set_iff {α : Type u} {s : set α} [decidable_pred s] {a : α} {b : α} : a ∈ coe_fn (of_set s) b ↔ a = b ∧ a ∈ s := sorry

@[simp] theorem of_set_eq_some_iff {α : Type u} {s : set α} {h : decidable_pred s} {a : α} {b : α} : coe_fn (of_set s) b = some a ↔ a = b ∧ a ∈ s :=
  mem_of_set_iff

@[simp] theorem of_set_eq_some_self_iff {α : Type u} {s : set α} {h : decidable_pred s} {a : α} : coe_fn (of_set s) a = some a ↔ a ∈ s :=
  mem_of_set_self_iff

@[simp] theorem of_set_symm {α : Type u} (s : set α) [decidable_pred s] : pequiv.symm (of_set s) = of_set s :=
  rfl

@[simp] theorem of_set_univ {α : Type u} : of_set set.univ = pequiv.refl α :=
  rfl

@[simp] theorem of_set_eq_refl {α : Type u} {s : set α} [decidable_pred s] : of_set s = pequiv.refl α ↔ s = set.univ := sorry

theorem symm_trans_rev {α : Type u} {β : Type v} {γ : Type w} (f : α ≃. β) (g : β ≃. γ) : pequiv.symm (pequiv.trans f g) = pequiv.trans (pequiv.symm g) (pequiv.symm f) :=
  rfl

theorem trans_symm {α : Type u} {β : Type v} (f : α ≃. β) : pequiv.trans f (pequiv.symm f) = of_set (set_of fun (a : α) => ↥(option.is_some (coe_fn f a))) := sorry

theorem symm_trans {α : Type u} {β : Type v} (f : α ≃. β) : pequiv.trans (pequiv.symm f) f = of_set (set_of fun (b : β) => ↥(option.is_some (coe_fn (pequiv.symm f) b))) := sorry

theorem trans_symm_eq_iff_forall_is_some {α : Type u} {β : Type v} {f : α ≃. β} : pequiv.trans f (pequiv.symm f) = pequiv.refl α ↔ ∀ (a : α), ↥(option.is_some (coe_fn f a)) := sorry

protected instance has_bot {α : Type u} {β : Type v} : has_bot (α ≃. β) :=
  has_bot.mk (mk (fun (_x : α) => none) (fun (_x : β) => none) sorry)

@[simp] theorem bot_apply {α : Type u} {β : Type v} (a : α) : coe_fn ⊥ a = none :=
  rfl

@[simp] theorem symm_bot {α : Type u} {β : Type v} : pequiv.symm ⊥ = ⊥ :=
  rfl

@[simp] theorem trans_bot {α : Type u} {β : Type v} {γ : Type w} (f : α ≃. β) : pequiv.trans f ⊥ = ⊥ := sorry

@[simp] theorem bot_trans {α : Type u} {β : Type v} {γ : Type w} (f : β ≃. γ) : pequiv.trans ⊥ f = ⊥ := sorry

theorem is_some_symm_get {α : Type u} {β : Type v} (f : α ≃. β) {a : α} (h : ↥(option.is_some (coe_fn f a))) : ↥(option.is_some (coe_fn (pequiv.symm f) (option.get h))) := sorry

def single {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β] (a : α) (b : β) : α ≃. β :=
  mk (fun (x : α) => ite (x = a) (some b) none) (fun (x : β) => ite (x = b) (some a) none) sorry

theorem mem_single {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β] (a : α) (b : β) : b ∈ coe_fn (single a b) a :=
  if_pos rfl

theorem mem_single_iff {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β] (a₁ : α) (a₂ : α) (b₁ : β) (b₂ : β) : b₁ ∈ coe_fn (single a₂ b₂) a₁ ↔ a₁ = a₂ ∧ b₁ = b₂ := sorry

@[simp] theorem symm_single {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β] (a : α) (b : β) : pequiv.symm (single a b) = single b a :=
  rfl

@[simp] theorem single_apply {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β] (a : α) (b : β) : coe_fn (single a b) a = some b :=
  if_pos rfl

theorem single_apply_of_ne {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β] {a₁ : α} {a₂ : α} (h : a₁ ≠ a₂) (b : β) : coe_fn (single a₁ b) a₂ = none :=
  if_neg (ne.symm h)

theorem single_trans_of_mem {α : Type u} {β : Type v} {γ : Type w} [DecidableEq α] [DecidableEq β] [DecidableEq γ] (a : α) {b : β} {c : γ} {f : β ≃. γ} (h : c ∈ coe_fn f b) : pequiv.trans (single a b) f = single a c := sorry

theorem trans_single_of_mem {α : Type u} {β : Type v} {γ : Type w} [DecidableEq α] [DecidableEq β] [DecidableEq γ] {a : α} {b : β} (c : γ) {f : α ≃. β} (h : b ∈ coe_fn f a) : pequiv.trans f (single b c) = single a c :=
  symm_injective (single_trans_of_mem c (iff.mpr (mem_iff_mem f) h))

@[simp] theorem single_trans_single {α : Type u} {β : Type v} {γ : Type w} [DecidableEq α] [DecidableEq β] [DecidableEq γ] (a : α) (b : β) (c : γ) : pequiv.trans (single a b) (single b c) = single a c :=
  single_trans_of_mem a (mem_single b c)

@[simp] theorem single_subsingleton_eq_refl {α : Type u} [DecidableEq α] [subsingleton α] (a : α) (b : α) : single a b = pequiv.refl α := sorry

theorem trans_single_of_eq_none {β : Type v} {γ : Type w} {δ : Type x} [DecidableEq β] [DecidableEq γ] {b : β} (c : γ) {f : δ ≃. β} (h : coe_fn (pequiv.symm f) b = none) : pequiv.trans f (single b c) = ⊥ := sorry

theorem single_trans_of_eq_none {α : Type u} {β : Type v} {δ : Type x} [DecidableEq α] [DecidableEq β] (a : α) {b : β} {f : β ≃. δ} (h : coe_fn f b = none) : pequiv.trans (single a b) f = ⊥ :=
  symm_injective (trans_single_of_eq_none a h)

theorem single_trans_single_of_ne {α : Type u} {β : Type v} {γ : Type w} [DecidableEq α] [DecidableEq β] [DecidableEq γ] {b₁ : β} {b₂ : β} (h : b₁ ≠ b₂) (a : α) (c : γ) : pequiv.trans (single a b₁) (single b₂ c) = ⊥ :=
  single_trans_of_eq_none a (single_apply_of_ne (ne.symm h) c)

protected instance partial_order {α : Type u} {β : Type v} : partial_order (α ≃. β) :=
  partial_order.mk (fun (f g : α ≃. β) => ∀ (a : α) (b : β), b ∈ coe_fn f a → b ∈ coe_fn g a)
    (preorder.lt._default fun (f g : α ≃. β) => ∀ (a : α) (b : β), b ∈ coe_fn f a → b ∈ coe_fn g a) sorry sorry sorry

theorem le_def {α : Type u} {β : Type v} {f : α ≃. β} {g : α ≃. β} : f ≤ g ↔ ∀ (a : α) (b : β), b ∈ coe_fn f a → b ∈ coe_fn g a :=
  iff.rfl

protected instance order_bot {α : Type u} {β : Type v} : order_bot (α ≃. β) :=
  order_bot.mk ⊥ partial_order.le partial_order.lt sorry sorry sorry sorry

protected instance semilattice_inf_bot {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β] : semilattice_inf_bot (α ≃. β) :=
  semilattice_inf_bot.mk order_bot.bot order_bot.le order_bot.lt sorry sorry sorry sorry
    (fun (f g : α ≃. β) =>
      mk (fun (a : α) => ite (coe_fn f a = coe_fn g a) (coe_fn f a) none)
        (fun (b : β) => ite (coe_fn (pequiv.symm f) b = coe_fn (pequiv.symm g) b) (coe_fn (pequiv.symm f) b) none) sorry)
    sorry sorry sorry

end pequiv


namespace equiv


def to_pequiv {α : Type u_1} {β : Type u_2} (f : α ≃ β) : α ≃. β :=
  pequiv.mk (some ∘ ⇑f) (some ∘ ⇑(equiv.symm f)) sorry

@[simp] theorem to_pequiv_refl {α : Type u_1} : to_pequiv (equiv.refl α) = pequiv.refl α :=
  rfl

theorem to_pequiv_trans {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : α ≃ β) (g : β ≃ γ) : to_pequiv (equiv.trans f g) = pequiv.trans (to_pequiv f) (to_pequiv g) :=
  rfl

theorem to_pequiv_symm {α : Type u_1} {β : Type u_2} (f : α ≃ β) : to_pequiv (equiv.symm f) = pequiv.symm (to_pequiv f) :=
  rfl

theorem to_pequiv_apply {α : Type u_1} {β : Type u_2} (f : α ≃ β) (x : α) : coe_fn (to_pequiv f) x = some (coe_fn f x) :=
  rfl

