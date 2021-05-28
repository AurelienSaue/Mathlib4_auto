/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury G. Kudryashov
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.logic.function.basic
import PostPort

universes u_1 u_2 u v w x u_3 u_4 

namespace Mathlib

/-!
# More theorems about the sum type
-/

/-- Check if a sum is `inl` and if so, retrieve its contents. -/
@[simp] def sum.get_left {α : Type u_1} {β : Type u_2} : α ⊕ β → Option α :=
  sorry

/-- Check if a sum is `inr` and if so, retrieve its contents. -/
@[simp] def sum.get_right {α : Type u_1} {β : Type u_2} : α ⊕ β → Option β :=
  sorry

/-- Check if a sum is `inl`. -/
@[simp] def sum.is_left {α : Type u_1} {β : Type u_2} : α ⊕ β → Bool :=
  sorry

/-- Check if a sum is `inr`. -/
@[simp] def sum.is_right {α : Type u_1} {β : Type u_2} : α ⊕ β → Bool :=
  sorry

protected instance sum.decidable_eq (α : Type u) [a : DecidableEq α] (β : Type v) : [a : DecidableEq β] → DecidableEq (α ⊕ β) := sorry

@[simp] theorem sum.forall {α : Type u} {β : Type v} {p : α ⊕ β → Prop} : (∀ (x : α ⊕ β), p x) ↔ (∀ (a : α), p (sum.inl a)) ∧ ∀ (b : β), p (sum.inr b) := sorry

@[simp] theorem sum.exists {α : Type u} {β : Type v} {p : α ⊕ β → Prop} : (∃ (x : α ⊕ β), p x) ↔ (∃ (a : α), p (sum.inl a)) ∨ ∃ (b : β), p (sum.inr b) := sorry

namespace sum


theorem injective_inl {α : Type u} {β : Type v} : function.injective inl :=
  fun (x y : α) => inl.inj

theorem injective_inr {α : Type u} {β : Type v} : function.injective inr :=
  fun (x y : β) => inr.inj

/-- Map `α ⊕ β` to `α' ⊕ β'` sending `α` to `α'` and `β` to `β'`. -/
protected def map {α : Type u} {α' : Type w} {β : Type v} {β' : Type x} (f : α → α') (g : β → β') : α ⊕ β → α' ⊕ β' :=
  sorry

@[simp] theorem map_inl {α : Type u} {α' : Type w} {β : Type v} {β' : Type x} (f : α → α') (g : β → β') (x : α) : sum.map f g (inl x) = inl (f x) :=
  rfl

@[simp] theorem map_inr {α : Type u} {α' : Type w} {β : Type v} {β' : Type x} (f : α → α') (g : β → β') (x : β) : sum.map f g (inr x) = inr (g x) :=
  rfl

@[simp] theorem map_map {α : Type u} {α' : Type w} {β : Type v} {β' : Type x} {α'' : Type u_1} {β'' : Type u_2} (f' : α' → α'') (g' : β' → β'') (f : α → α') (g : β → β') (x : α ⊕ β) : sum.map f' g' (sum.map f g x) = sum.map (f' ∘ f) (g' ∘ g) x :=
  sum.cases_on x (fun (x : α) => idRhs (sum.map f' g' (sum.map f g (inl x)) = sum.map f' g' (sum.map f g (inl x))) rfl)
    fun (x : β) => idRhs (sum.map f' g' (sum.map f g (inr x)) = sum.map f' g' (sum.map f g (inr x))) rfl

@[simp] theorem map_comp_map {α : Type u} {α' : Type w} {β : Type v} {β' : Type x} {α'' : Type u_1} {β'' : Type u_2} (f' : α' → α'') (g' : β' → β'') (f : α → α') (g : β → β') : sum.map f' g' ∘ sum.map f g = sum.map (f' ∘ f) (g' ∘ g) :=
  funext (map_map f' g' f g)

@[simp] theorem map_id_id (α : Type u_1) (β : Type u_2) : sum.map id id = id :=
  funext fun (x : α ⊕ β) => sum.rec_on x (fun (_x : α) => rfl) fun (_x : β) => rfl

theorem inl.inj_iff {α : Type u} {β : Type v} {a : α} {b : α} : inl a = inl b ↔ a = b :=
  { mp := inl.inj, mpr := congr_arg fun {a : α} => inl a }

theorem inr.inj_iff {α : Type u} {β : Type v} {a : β} {b : β} : inr a = inr b ↔ a = b :=
  { mp := inr.inj, mpr := congr_arg fun {a : β} => inr a }

theorem inl_ne_inr {α : Type u} {β : Type v} {a : α} {b : β} : inl a ≠ inr b :=
  fun (ᾰ : inl a = inr b) =>
    eq.dcases_on ᾰ (fun (H_1 : inr b = inl a) => sum.no_confusion H_1) (Eq.refl (inr b)) (HEq.refl ᾰ)

theorem inr_ne_inl {α : Type u} {β : Type v} {a : α} {b : β} : inr b ≠ inl a :=
  fun (ᾰ : inr b = inl a) =>
    eq.dcases_on ᾰ (fun (H_1 : inl a = inr b) => sum.no_confusion H_1) (Eq.refl (inl a)) (HEq.refl ᾰ)

/-- Define a function on `α ⊕ β` by giving separate definitions on `α` and `β`. -/
protected def elim {α : Type u_1} {β : Type u_2} {γ : Sort u_3} (f : α → γ) (g : β → γ) : α ⊕ β → γ :=
  fun (x : α ⊕ β) => sum.rec_on x f g

@[simp] theorem elim_inl {α : Type u_1} {β : Type u_2} {γ : Sort u_3} (f : α → γ) (g : β → γ) (x : α) : sum.elim f g (inl x) = f x :=
  rfl

@[simp] theorem elim_inr {α : Type u_1} {β : Type u_2} {γ : Sort u_3} (f : α → γ) (g : β → γ) (x : β) : sum.elim f g (inr x) = g x :=
  rfl

@[simp] theorem elim_comp_inl {α : Type u_1} {β : Type u_2} {γ : Sort u_3} (f : α → γ) (g : β → γ) : sum.elim f g ∘ inl = f :=
  rfl

@[simp] theorem elim_comp_inr {α : Type u_1} {β : Type u_2} {γ : Sort u_3} (f : α → γ) (g : β → γ) : sum.elim f g ∘ inr = g :=
  rfl

@[simp] theorem elim_inl_inr {α : Type u_1} {β : Type u_2} : sum.elim inl inr = id :=
  funext fun (x : α ⊕ β) => sum.cases_on x (fun (_x : α) => rfl) fun (_x : β) => rfl

theorem comp_elim {α : Type u_1} {β : Type u_2} {γ : Sort u_3} {δ : Sort u_4} (f : γ → δ) (g : α → γ) (h : β → γ) : f ∘ sum.elim g h = sum.elim (f ∘ g) (f ∘ h) :=
  funext fun (x : α ⊕ β) => sum.cases_on x (fun (_x : α) => rfl) fun (_x : β) => rfl

@[simp] theorem elim_comp_inl_inr {α : Type u_1} {β : Type u_2} {γ : Sort u_3} (f : α ⊕ β → γ) : sum.elim (f ∘ inl) (f ∘ inr) = f :=
  funext fun (x : α ⊕ β) => sum.cases_on x (fun (_x : α) => rfl) fun (_x : β) => rfl

@[simp] theorem update_elim_inl {α : Type u_1} {β : Type u_2} {γ : Sort u_3} [DecidableEq α] [DecidableEq (α ⊕ β)] {f : α → γ} {g : β → γ} {i : α} {x : γ} : function.update (sum.elim f g) (inl i) x = sum.elim (function.update f i x) g := sorry

@[simp] theorem update_elim_inr {α : Type u_1} {β : Type u_2} {γ : Sort u_3} [DecidableEq β] [DecidableEq (α ⊕ β)] {f : α → γ} {g : β → γ} {i : β} {x : γ} : function.update (sum.elim f g) (inr i) x = sum.elim f (function.update g i x) := sorry

@[simp] theorem update_inl_comp_inl {α : Type u_1} {β : Type u_2} {γ : Sort u_3} [DecidableEq α] [DecidableEq (α ⊕ β)] {f : α ⊕ β → γ} {i : α} {x : γ} : function.update f (inl i) x ∘ inl = function.update (f ∘ inl) i x :=
  function.update_comp_eq_of_injective f injective_inl i x

@[simp] theorem update_inl_apply_inl {α : Type u_1} {β : Type u_2} {γ : Sort u_3} [DecidableEq α] [DecidableEq (α ⊕ β)] {f : α ⊕ β → γ} {i : α} {j : α} {x : γ} : function.update f (inl i) x (inl j) = function.update (f ∘ inl) i x j := sorry

@[simp] theorem update_inl_comp_inr {α : Type u_1} {β : Type u_2} {γ : Sort u_3} [DecidableEq (α ⊕ β)] {f : α ⊕ β → γ} {i : α} {x : γ} : function.update f (inl i) x ∘ inr = f ∘ inr :=
  function.update_comp_eq_of_forall_ne f x fun (_x : β) => inr_ne_inl

@[simp] theorem update_inl_apply_inr {α : Type u_1} {β : Type u_2} {γ : Sort u_3} [DecidableEq (α ⊕ β)] {f : α ⊕ β → γ} {i : α} {j : β} {x : γ} : function.update f (inl i) x (inr j) = f (inr j) :=
  function.update_noteq inr_ne_inl x f

@[simp] theorem update_inr_comp_inl {α : Type u_1} {β : Type u_2} {γ : Sort u_3} [DecidableEq (α ⊕ β)] {f : α ⊕ β → γ} {i : β} {x : γ} : function.update f (inr i) x ∘ inl = f ∘ inl :=
  function.update_comp_eq_of_forall_ne f x fun (_x : α) => inl_ne_inr

@[simp] theorem update_inr_apply_inl {α : Type u_1} {β : Type u_2} {γ : Sort u_3} [DecidableEq (α ⊕ β)] {f : α ⊕ β → γ} {i : α} {j : β} {x : γ} : function.update f (inr j) x (inl i) = f (inl i) :=
  function.update_noteq inl_ne_inr x f

@[simp] theorem update_inr_comp_inr {α : Type u_1} {β : Type u_2} {γ : Sort u_3} [DecidableEq β] [DecidableEq (α ⊕ β)] {f : α ⊕ β → γ} {i : β} {x : γ} : function.update f (inr i) x ∘ inr = function.update (f ∘ inr) i x :=
  function.update_comp_eq_of_injective f injective_inr i x

@[simp] theorem update_inr_apply_inr {α : Type u_1} {β : Type u_2} {γ : Sort u_3} [DecidableEq β] [DecidableEq (α ⊕ β)] {f : α ⊕ β → γ} {i : β} {j : β} {x : γ} : function.update f (inr i) x (inr j) = function.update (f ∘ inr) i x j := sorry

inductive lex {α : Type u} {β : Type v} (ra : α → α → Prop) (rb : β → β → Prop) : α ⊕ β → α ⊕ β → Prop
where
| inl : ∀ {a₁ a₂ : α}, ra a₁ a₂ → lex ra rb (inl a₁) (inl a₂)
| inr : ∀ {b₁ b₂ : β}, rb b₁ b₂ → lex ra rb (inr b₁) (inr b₂)
| sep : ∀ (a : α) (b : β), lex ra rb (inl a) (inr b)

@[simp] theorem lex_inl_inl {α : Type u} {β : Type v} {ra : α → α → Prop} {rb : β → β → Prop} {a₁ : α} {a₂ : α} : lex ra rb (inl a₁) (inl a₂) ↔ ra a₁ a₂ := sorry

@[simp] theorem lex_inr_inr {α : Type u} {β : Type v} {ra : α → α → Prop} {rb : β → β → Prop} {b₁ : β} {b₂ : β} : lex ra rb (inr b₁) (inr b₂) ↔ rb b₁ b₂ := sorry

@[simp] theorem lex_inr_inl {α : Type u} {β : Type v} {ra : α → α → Prop} {rb : β → β → Prop} {b : β} {a : α} : ¬lex ra rb (inr b) (inl a) := sorry

theorem lex_acc_inl {α : Type u} {β : Type v} {ra : α → α → Prop} {rb : β → β → Prop} {a : α} (aca : acc ra a) : acc (lex ra rb) (inl a) := sorry

theorem lex_acc_inr {α : Type u} {β : Type v} {ra : α → α → Prop} {rb : β → β → Prop} (aca : ∀ (a : α), acc (lex ra rb) (inl a)) {b : β} (acb : acc rb b) : acc (lex ra rb) (inr b) := sorry

theorem lex_wf {α : Type u} {β : Type v} {ra : α → α → Prop} {rb : β → β → Prop} (ha : well_founded ra) (hb : well_founded rb) : well_founded (lex ra rb) :=
  (fun (aca : ∀ (a : α), acc (lex ra rb) (inl a)) =>
      well_founded.intro fun (x : α ⊕ β) => sum.rec_on x aca fun (b : β) => lex_acc_inr aca (well_founded.apply hb b))
    fun (a : α) => lex_acc_inl (well_founded.apply ha a)

/-- Swap the factors of a sum type -/
@[simp] def swap {α : Type u} {β : Type v} : α ⊕ β → β ⊕ α :=
  sorry

@[simp] theorem swap_swap {α : Type u} {β : Type v} (x : α ⊕ β) : swap (swap x) = x :=
  sum.cases_on x (fun (x : α) => Eq.refl (swap (swap (inl x)))) fun (x : β) => Eq.refl (swap (swap (inr x)))

@[simp] theorem swap_swap_eq {α : Type u} {β : Type v} : swap ∘ swap = id :=
  funext swap_swap

@[simp] theorem swap_left_inverse {α : Type u} {β : Type v} : function.left_inverse swap swap :=
  swap_swap

@[simp] theorem swap_right_inverse {α : Type u} {β : Type v} : function.right_inverse swap swap :=
  swap_swap

end sum


namespace function


theorem injective.sum_elim {α : Type u} {β : Type v} {γ : Sort u_1} {f : α → γ} {g : β → γ} (hf : injective f) (hg : injective g) (hfg : ∀ (a : α) (b : β), f a ≠ g b) : injective (sum.elim f g) := sorry

theorem injective.sum_map {α : Type u} {α' : Type w} {β : Type v} {β' : Type x} {f : α → β} {g : α' → β'} (hf : injective f) (hg : injective g) : injective (sum.map f g) := sorry

theorem surjective.sum_map {α : Type u} {α' : Type w} {β : Type v} {β' : Type x} {f : α → β} {g : α' → β'} (hf : surjective f) (hg : surjective g) : surjective (sum.map f g) := sorry

