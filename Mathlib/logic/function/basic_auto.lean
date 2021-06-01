/-
Copyright (c) 2016 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.logic.basic
import Mathlib.data.option.defs
import Mathlib.PostPort

universes u_1 u_2 u v w u_3 u_4 u_5 u_6 u_7 l 

namespace Mathlib

/-!
# Miscellaneous function constructions and lemmas
-/

namespace function


/-- Evaluate a function at an argument. Useful if you want to talk about the partially applied
  `function.eval x : (Π x, β x) → β x`. -/
def eval {α : Sort u_1} {β : α → Sort u_2} (x : α) (f : (x : α) → β x) : β x := f x

@[simp] theorem eval_apply {α : Sort u_1} {β : α → Sort u_2} (x : α) (f : (x : α) → β x) :
    eval x f = f x :=
  rfl

theorem comp_apply {α : Sort u} {β : Sort v} {φ : Sort w} (f : β → φ) (g : α → β) (a : α) :
    comp f g a = f (g a) :=
  rfl

theorem const_def {α : Sort u_1} {β : Sort u_2} {y : β} : (fun (x : α) => y) = const α y := rfl

@[simp] theorem const_apply {α : Sort u_1} {β : Sort u_2} {y : β} {x : α} : const α y x = y := rfl

@[simp] theorem const_comp {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} {f : α → β} {c : γ} :
    const β c ∘ f = const α c :=
  rfl

@[simp] theorem comp_const {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} {f : β → γ} {b : β} :
    f ∘ const α b = const α (f b) :=
  rfl

theorem id_def {α : Sort u_1} : id = fun (x : α) => x := rfl

theorem hfunext {α : Sort u} {α' : Sort u} {β : α → Sort v} {β' : α' → Sort v} {f : (a : α) → β a}
    {f' : (a : α') → β' a} (hα : α = α') (h : ∀ (a : α) (a' : α'), a == a' → f a == f' a') :
    f == f' :=
  sorry

theorem funext_iff {α : Sort u_1} {β : α → Sort u_2} {f₁ : (x : α) → β x} {f₂ : (x : α) → β x} :
    f₁ = f₂ ↔ ∀ (a : α), f₁ a = f₂ a :=
  { mp := fun (h : f₁ = f₂) (a : α) => h ▸ rfl, mpr := funext }

@[simp] theorem injective.eq_iff {α : Sort u_1} {β : Sort u_2} {f : α → β} (I : injective f) {a : α}
    {b : α} : f a = f b ↔ a = b :=
  { mp := I, mpr := congr_arg f }

theorem injective.eq_iff' {α : Sort u_1} {β : Sort u_2} {f : α → β} (I : injective f) {a : α}
    {b : α} {c : β} (h : f b = c) : f a = c ↔ a = b :=
  h ▸ injective.eq_iff I

theorem injective.ne {α : Sort u_1} {β : Sort u_2} {f : α → β} (hf : injective f) {a₁ : α}
    {a₂ : α} : a₁ ≠ a₂ → f a₁ ≠ f a₂ :=
  mt fun (h : f a₁ = f a₂) => hf h

theorem injective.ne_iff {α : Sort u_1} {β : Sort u_2} {f : α → β} (hf : injective f) {x : α}
    {y : α} : f x ≠ f y ↔ x ≠ y :=
  { mp := mt (congr_arg f), mpr := injective.ne hf }

theorem injective.ne_iff' {α : Sort u_1} {β : Sort u_2} {f : α → β} (hf : injective f) {x : α}
    {y : α} {z : β} (h : f y = z) : f x ≠ z ↔ x ≠ y :=
  h ▸ injective.ne_iff hf

/-- If the co-domain `β` of an injective function `f : α → β` has decidable equality, then
the domain `α` also has decidable equality. -/
def injective.decidable_eq {α : Sort u_1} {β : Sort u_2} {f : α → β} [DecidableEq β]
    (I : injective f) : DecidableEq α :=
  fun (a b : α) => decidable_of_iff (f a = f b) (injective.eq_iff I)

theorem injective.of_comp {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} {f : α → β} {g : γ → α}
    (I : injective (f ∘ g)) : injective g :=
  fun (x y : γ) (h : g x = g y) => I ((fun (this : f (g x) = f (g y)) => this) (congr_arg f h))

theorem surjective.of_comp {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} {f : α → β} {g : γ → α}
    (S : surjective (f ∘ g)) : surjective f :=
  sorry

protected instance decidable_eq_pfun (p : Prop) [Decidable p] (α : p → Type u_1)
    [(hp : p) → DecidableEq (α hp)] : DecidableEq ((hp : p) → α hp) :=
  sorry

theorem surjective.forall {α : Sort u_1} {β : Sort u_2} {f : α → β} (hf : surjective f)
    {p : β → Prop} : (∀ (y : β), p y) ↔ ∀ (x : α), p (f x) :=
  sorry

theorem surjective.forall₂ {α : Sort u_1} {β : Sort u_2} {f : α → β} (hf : surjective f)
    {p : β → β → Prop} : (∀ (y₁ y₂ : β), p y₁ y₂) ↔ ∀ (x₁ x₂ : α), p (f x₁) (f x₂) :=
  iff.trans (surjective.forall hf) (forall_congr fun (x : α) => surjective.forall hf)

theorem surjective.forall₃ {α : Sort u_1} {β : Sort u_2} {f : α → β} (hf : surjective f)
    {p : β → β → β → Prop} :
    (∀ (y₁ y₂ y₃ : β), p y₁ y₂ y₃) ↔ ∀ (x₁ x₂ x₃ : α), p (f x₁) (f x₂) (f x₃) :=
  iff.trans (surjective.forall hf) (forall_congr fun (x : α) => surjective.forall₂ hf)

theorem surjective.exists {α : Sort u_1} {β : Sort u_2} {f : α → β} (hf : surjective f)
    {p : β → Prop} : (∃ (y : β), p y) ↔ ∃ (x : α), p (f x) :=
  sorry

theorem surjective.exists₂ {α : Sort u_1} {β : Sort u_2} {f : α → β} (hf : surjective f)
    {p : β → β → Prop} :
    (∃ (y₁ : β), ∃ (y₂ : β), p y₁ y₂) ↔ ∃ (x₁ : α), ∃ (x₂ : α), p (f x₁) (f x₂) :=
  iff.trans (surjective.exists hf) (exists_congr fun (x : α) => surjective.exists hf)

theorem surjective.exists₃ {α : Sort u_1} {β : Sort u_2} {f : α → β} (hf : surjective f)
    {p : β → β → β → Prop} :
    (∃ (y₁ : β), ∃ (y₂ : β), ∃ (y₃ : β), p y₁ y₂ y₃) ↔
        ∃ (x₁ : α), ∃ (x₂ : α), ∃ (x₃ : α), p (f x₁) (f x₂) (f x₃) :=
  iff.trans (surjective.exists hf) (exists_congr fun (x : α) => surjective.exists₂ hf)

/-- Cantor's diagonal argument implies that there are no surjective functions from `α`
to `set α`. -/
theorem cantor_surjective {α : Type u_1} (f : α → set α) : ¬surjective f := sorry

/-- Cantor's diagonal argument implies that there are no injective functions from `set α` to `α`. -/
theorem cantor_injective {α : Type u_1} (f : set α → α) : ¬injective f := sorry

/-- `g` is a partial inverse to `f` (an injective but not necessarily
  surjective function) if `g y = some x` implies `f x = y`, and `g y = none`
  implies that `y` is not in the range of `f`. -/
def is_partial_inv {α : Type u_1} {β : Sort u_2} (f : α → β) (g : β → Option α) :=
  ∀ (x : α) (y : β), g y = some x ↔ f x = y

theorem is_partial_inv_left {α : Type u_1} {β : Sort u_2} {f : α → β} {g : β → Option α}
    (H : is_partial_inv f g) (x : α) : g (f x) = some x :=
  iff.mpr (H x (f x)) rfl

theorem injective_of_partial_inv {α : Type u_1} {β : Sort u_2} {f : α → β} {g : β → Option α}
    (H : is_partial_inv f g) : injective f :=
  fun (a b : α) (h : f a = f b) =>
    option.some.inj (Eq.trans (Eq.symm (iff.mpr (H a (f b)) h)) (iff.mpr (H b (f b)) rfl))

theorem injective_of_partial_inv_right {α : Type u_1} {β : Sort u_2} {f : α → β} {g : β → Option α}
    (H : is_partial_inv f g) (x : β) (y : β) (b : α) (h₁ : b ∈ g x) (h₂ : b ∈ g y) : x = y :=
  Eq.trans (Eq.symm (iff.mp (H b x) h₁)) (iff.mp (H b y) h₂)

theorem left_inverse.comp_eq_id {α : Sort u_1} {β : Sort u_2} {f : α → β} {g : β → α}
    (h : left_inverse f g) : f ∘ g = id :=
  funext h

theorem left_inverse_iff_comp {α : Sort u_1} {β : Sort u_2} {f : α → β} {g : β → α} :
    left_inverse f g ↔ f ∘ g = id :=
  { mp := left_inverse.comp_eq_id, mpr := congr_fun }

theorem right_inverse.comp_eq_id {α : Sort u_1} {β : Sort u_2} {f : α → β} {g : β → α}
    (h : right_inverse f g) : g ∘ f = id :=
  funext h

theorem right_inverse_iff_comp {α : Sort u_1} {β : Sort u_2} {f : α → β} {g : β → α} :
    right_inverse f g ↔ g ∘ f = id :=
  { mp := right_inverse.comp_eq_id, mpr := congr_fun }

theorem left_inverse.comp {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} {f : α → β} {g : β → α}
    {h : β → γ} {i : γ → β} (hf : left_inverse f g) (hh : left_inverse h i) :
    left_inverse (h ∘ f) (g ∘ i) :=
  sorry

theorem right_inverse.comp {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} {f : α → β} {g : β → α}
    {h : β → γ} {i : γ → β} (hf : right_inverse f g) (hh : right_inverse h i) :
    right_inverse (h ∘ f) (g ∘ i) :=
  left_inverse.comp hh hf

theorem left_inverse.right_inverse {α : Sort u_1} {β : Sort u_2} {f : α → β} {g : β → α}
    (h : left_inverse g f) : right_inverse f g :=
  h

theorem right_inverse.left_inverse {α : Sort u_1} {β : Sort u_2} {f : α → β} {g : β → α}
    (h : right_inverse g f) : left_inverse f g :=
  h

theorem left_inverse.surjective {α : Sort u_1} {β : Sort u_2} {f : α → β} {g : β → α}
    (h : left_inverse f g) : surjective f :=
  right_inverse.surjective (left_inverse.right_inverse h)

theorem right_inverse.injective {α : Sort u_1} {β : Sort u_2} {f : α → β} {g : β → α}
    (h : right_inverse f g) : injective f :=
  left_inverse.injective (right_inverse.left_inverse h)

theorem left_inverse.eq_right_inverse {α : Sort u_1} {β : Sort u_2} {f : α → β} {g₁ : β → α}
    {g₂ : β → α} (h₁ : left_inverse g₁ f) (h₂ : right_inverse g₂ f) : g₁ = g₂ :=
  sorry

/-- We can use choice to construct explicitly a partial inverse for
  a given injective function `f`. -/
def partial_inv {α : Type u_1} {β : Sort u_2} (f : α → β) (b : β) : Option α :=
  dite (∃ (a : α), f a = b) (fun (h : ∃ (a : α), f a = b) => some (classical.some h))
    fun (h : ¬∃ (a : α), f a = b) => none

theorem partial_inv_of_injective {α : Type u_1} {β : Sort u_2} {f : α → β} (I : injective f) :
    is_partial_inv f (partial_inv f) :=
  sorry

theorem partial_inv_left {α : Type u_1} {β : Sort u_2} {f : α → β} (I : injective f) (x : α) :
    partial_inv f (f x) = some x :=
  is_partial_inv_left (partial_inv_of_injective I)

/-- Construct the inverse for a function `f` on domain `s`. This function is a right inverse of `f`
on `f '' s`. -/
def inv_fun_on {α : Type u} [n : Nonempty α] {β : Sort v} (f : α → β) (s : set α) (b : β) : α :=
  dite (∃ (a : α), a ∈ s ∧ f a = b) (fun (h : ∃ (a : α), a ∈ s ∧ f a = b) => classical.some h)
    fun (h : ¬∃ (a : α), a ∈ s ∧ f a = b) => Classical.choice n

theorem inv_fun_on_pos {α : Type u} [n : Nonempty α] {β : Sort v} {f : α → β} {s : set α} {b : β}
    (h : ∃ (a : α), ∃ (H : a ∈ s), f a = b) : inv_fun_on f s b ∈ s ∧ f (inv_fun_on f s b) = b :=
  sorry

theorem inv_fun_on_mem {α : Type u} [n : Nonempty α] {β : Sort v} {f : α → β} {s : set α} {b : β}
    (h : ∃ (a : α), ∃ (H : a ∈ s), f a = b) : inv_fun_on f s b ∈ s :=
  and.left (inv_fun_on_pos h)

theorem inv_fun_on_eq {α : Type u} [n : Nonempty α] {β : Sort v} {f : α → β} {s : set α} {b : β}
    (h : ∃ (a : α), ∃ (H : a ∈ s), f a = b) : f (inv_fun_on f s b) = b :=
  and.right (inv_fun_on_pos h)

theorem inv_fun_on_eq' {α : Type u} [n : Nonempty α] {β : Sort v} {f : α → β} {s : set α} {a : α}
    (h : ∀ (x : α), x ∈ s → ∀ (y : α), y ∈ s → f x = f y → x = y) (ha : a ∈ s) :
    inv_fun_on f s (f a) = a :=
  (fun (this : ∃ (a' : α), ∃ (H : a' ∈ s), f a' = f a) =>
      h (inv_fun_on (fun (a' : α) => f a') s (f a)) (inv_fun_on_mem this) a ha (inv_fun_on_eq this))
    (Exists.intro a (Exists.intro ha rfl))

theorem inv_fun_on_neg {α : Type u} [n : Nonempty α] {β : Sort v} {f : α → β} {s : set α} {b : β}
    (h : ¬∃ (a : α), ∃ (H : a ∈ s), f a = b) : inv_fun_on f s b = Classical.choice n :=
  sorry

/-- The inverse of a function (which is a left inverse if `f` is injective
  and a right inverse if `f` is surjective). -/
def inv_fun {α : Type u} [n : Nonempty α] {β : Sort v} (f : α → β) : β → α := inv_fun_on f set.univ

theorem inv_fun_eq {α : Type u} [n : Nonempty α] {β : Sort v} {f : α → β} {b : β}
    (h : ∃ (a : α), f a = b) : f (inv_fun f b) = b :=
  sorry

theorem inv_fun_neg {α : Type u} [n : Nonempty α] {β : Sort v} {f : α → β} {b : β}
    (h : ¬∃ (a : α), f a = b) : inv_fun f b = Classical.choice n :=
  sorry

theorem inv_fun_eq_of_injective_of_right_inverse {α : Type u} [n : Nonempty α] {β : Sort v}
    {f : α → β} {g : β → α} (hf : injective f) (hg : right_inverse g f) : inv_fun f = g :=
  funext
    fun (b : β) =>
      hf
        (eq.mpr (id (Eq._oldrec (Eq.refl (f (inv_fun f b) = f (g b))) (hg b)))
          (inv_fun_eq (Exists.intro (g b) (hg b))))

theorem right_inverse_inv_fun {α : Type u} [n : Nonempty α] {β : Sort v} {f : α → β}
    (hf : surjective f) : right_inverse (inv_fun f) f :=
  fun (b : β) => inv_fun_eq (hf b)

theorem left_inverse_inv_fun {α : Type u} [n : Nonempty α] {β : Sort v} {f : α → β}
    (hf : injective f) : left_inverse (inv_fun f) f :=
  fun (b : α) =>
    (fun (this : f (inv_fun f (f b)) = f b) => hf this) (inv_fun_eq (Exists.intro b rfl))

theorem inv_fun_surjective {α : Type u} [n : Nonempty α] {β : Sort v} {f : α → β}
    (hf : injective f) : surjective (inv_fun f) :=
  left_inverse.surjective (left_inverse_inv_fun hf)

theorem inv_fun_comp {α : Type u} [n : Nonempty α] {β : Sort v} {f : α → β} (hf : injective f) :
    inv_fun f ∘ f = id :=
  funext (left_inverse_inv_fun hf)

theorem injective.has_left_inverse {α : Type u} [i : Nonempty α] {β : Sort v} {f : α → β}
    (hf : injective f) : has_left_inverse f :=
  Exists.intro (inv_fun f) (left_inverse_inv_fun hf)

theorem injective_iff_has_left_inverse {α : Type u} [i : Nonempty α] {β : Sort v} {f : α → β} :
    injective f ↔ has_left_inverse f :=
  { mp := injective.has_left_inverse, mpr := has_left_inverse.injective }

/-- The inverse of a surjective function. (Unlike `inv_fun`, this does not require
  `α` to be inhabited.) -/
def surj_inv {α : Sort u} {β : Sort v} {f : α → β} (h : surjective f) (b : β) : α :=
  classical.some (h b)

theorem surj_inv_eq {α : Sort u} {β : Sort v} {f : α → β} (h : surjective f) (b : β) :
    f (surj_inv h b) = b :=
  classical.some_spec (h b)

theorem right_inverse_surj_inv {α : Sort u} {β : Sort v} {f : α → β} (hf : surjective f) :
    right_inverse (surj_inv hf) f :=
  surj_inv_eq hf

theorem left_inverse_surj_inv {α : Sort u} {β : Sort v} {f : α → β} (hf : bijective f) :
    left_inverse (surj_inv (and.right hf)) f :=
  right_inverse_of_injective_of_left_inverse (and.left hf) (right_inverse_surj_inv (and.right hf))

theorem surjective.has_right_inverse {α : Sort u} {β : Sort v} {f : α → β} (hf : surjective f) :
    has_right_inverse f :=
  Exists.intro (surj_inv hf) (right_inverse_surj_inv hf)

theorem surjective_iff_has_right_inverse {α : Sort u} {β : Sort v} {f : α → β} :
    surjective f ↔ has_right_inverse f :=
  { mp := surjective.has_right_inverse, mpr := has_right_inverse.surjective }

theorem bijective_iff_has_inverse {α : Sort u} {β : Sort v} {f : α → β} :
    bijective f ↔ ∃ (g : β → α), left_inverse g f ∧ right_inverse g f :=
  sorry

theorem injective_surj_inv {α : Sort u} {β : Sort v} {f : α → β} (h : surjective f) :
    injective (surj_inv h) :=
  right_inverse.injective (right_inverse_surj_inv h)

/-- Replacing the value of a function at a given point by a given value. -/
def update {α : Sort u} {β : α → Sort v} [DecidableEq α] (f : (a : α) → β a) (a' : α) (v : β a')
    (a : α) : β a :=
  dite (a = a') (fun (h : a = a') => Eq._oldrec v (Eq.symm h)) fun (h : ¬a = a') => f a

/-- On non-dependent functions, `function.update` can be expressed as an `ite` -/
theorem update_apply {α : Sort u} [DecidableEq α] {β : Sort u_1} (f : α → β) (a' : α) (b : β)
    (a : α) : update f a' b a = ite (a = a') b (f a) :=
  sorry

@[simp] theorem update_same {α : Sort u} {β : α → Sort v} [DecidableEq α] (a : α) (v : β a)
    (f : (a : α) → β a) : update f a v a = v :=
  dif_pos rfl

theorem update_injective {α : Sort u} {β : α → Sort v} [DecidableEq α] (f : (a : α) → β a)
    (a' : α) : injective (update f a') :=
  sorry

@[simp] theorem update_noteq {α : Sort u} {β : α → Sort v} [DecidableEq α] {a : α} {a' : α}
    (h : a ≠ a') (v : β a') (f : (a : α) → β a) : update f a' v a = f a :=
  dif_neg h

theorem forall_update_iff {α : Sort u} {β : α → Sort v} [DecidableEq α] (f : (a : α) → β a) {a : α}
    {b : β a} (p : (a : α) → β a → Prop) :
    (∀ (x : α), p x (update f a b x)) ↔ p a b ∧ ∀ (x : α), x ≠ a → p x (f x) :=
  sorry

theorem update_eq_iff {α : Sort u} {β : α → Sort v} [DecidableEq α] {a : α} {b : β a}
    {f : (a : α) → β a} {g : (a : α) → β a} :
    update f a b = g ↔ b = g a ∧ ∀ (x : α), x ≠ a → f x = g x :=
  iff.trans funext_iff (forall_update_iff f fun (x : α) (y : β x) => y = g x)

theorem eq_update_iff {α : Sort u} {β : α → Sort v} [DecidableEq α] {a : α} {b : β a}
    {f : (a : α) → β a} {g : (a : α) → β a} :
    g = update f a b ↔ g a = b ∧ ∀ (x : α), x ≠ a → g x = f x :=
  iff.trans funext_iff (forall_update_iff f fun (x : α) (y : β x) => g x = y)

@[simp] theorem update_eq_self {α : Sort u} {β : α → Sort v} [DecidableEq α] (a : α)
    (f : (a : α) → β a) : update f a (f a) = f :=
  iff.mpr update_eq_iff { left := rfl, right := fun (_x : α) (_x_1 : _x ≠ a) => rfl }

theorem update_comp_eq_of_forall_ne' {α : Sort u} {β : α → Sort v} [DecidableEq α] {α' : Sort u_1}
    (g : (a : α) → β a) {f : α' → α} {i : α} (a : β i) (h : ∀ (x : α'), f x ≠ i) :
    (fun (j : α') => update g i a (f j)) = fun (j : α') => g (f j) :=
  funext fun (x : α') => update_noteq (h x) a g

/-- Non-dependent version of `function.update_comp_eq_of_forall_ne'` -/
theorem update_comp_eq_of_forall_ne {α' : Sort w} [DecidableEq α'] {α : Sort u_1} {β : Sort u_2}
    (g : α' → β) {f : α → α'} {i : α'} (a : β) (h : ∀ (x : α), f x ≠ i) :
    update g i a ∘ f = g ∘ f :=
  update_comp_eq_of_forall_ne' g a h

theorem update_comp_eq_of_injective' {α : Sort u} {β : α → Sort v} {α' : Sort w} [DecidableEq α]
    [DecidableEq α'] (g : (a : α) → β a) {f : α' → α} (hf : injective f) (i : α') (a : β (f i)) :
    (fun (j : α') => update g (f i) a (f j)) = update (fun (i : α') => g (f i)) i a :=
  iff.mpr eq_update_iff
    { left := update_same (f i) a g,
      right := fun (j : α') (hj : j ≠ i) => update_noteq (injective.ne hf hj) a g }

/-- Non-dependent version of `function.update_comp_eq_of_injective'` -/
theorem update_comp_eq_of_injective {α : Sort u} {α' : Sort w} [DecidableEq α] [DecidableEq α']
    {β : Sort u_1} (g : α' → β) {f : α → α'} (hf : injective f) (i : α) (a : β) :
    update g (f i) a ∘ f = update (g ∘ f) i a :=
  update_comp_eq_of_injective' g hf i a

theorem apply_update {ι : Sort u_1} [DecidableEq ι] {α : ι → Sort u_2} {β : ι → Sort u_3}
    (f : (i : ι) → α i → β i) (g : (i : ι) → α i) (i : ι) (v : α i) (j : ι) :
    f j (update g i v j) = update (fun (k : ι) => f k (g k)) i (f i v) j :=
  sorry

theorem comp_update {α : Sort u} [DecidableEq α] {α' : Sort u_1} {β : Sort u_2} (f : α' → β)
    (g : α → α') (i : α) (v : α') : f ∘ update g i v = update (f ∘ g) i (f v) :=
  funext (apply_update (fun (x : α) => f) g i v)

theorem update_comm {α : Sort u_1} [DecidableEq α] {β : α → Sort u_2} {a : α} {b : α} (h : a ≠ b)
    (v : β a) (w : β b) (f : (a : α) → β a) :
    update (update f a v) b w = update (update f b w) a v :=
  sorry

@[simp] theorem update_idem {α : Sort u_1} [DecidableEq α] {β : α → Sort u_2} {a : α} (v : β a)
    (w : β a) (f : (a : α) → β a) : update (update f a v) a w = update f a w :=
  sorry

/-- `extend f g e'` extends a function `g : α → γ`
along a function `f : α → β` to a function `β → γ`,
by using the values of `g` on the range of `f`
and the values of an auxiliary function `e' : β → γ` elsewhere.

Mostly useful when `f` is injective. -/
def extend {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : α → β) (g : α → γ) (e' : β → γ) :
    β → γ :=
  fun (b : β) =>
    dite (∃ (a : α), f a = b) (fun (h : ∃ (a : α), f a = b) => g (classical.some h))
      fun (h : ¬∃ (a : α), f a = b) => e' b

theorem extend_def {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : α → β) (g : α → γ) (e' : β → γ)
    (b : β) :
    extend f g e' b =
        dite (∃ (a : α), f a = b) (fun (h : ∃ (a : α), f a = b) => g (classical.some h))
          fun (h : ¬∃ (a : α), f a = b) => e' b :=
  rfl

@[simp] theorem extend_apply {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β}
    (hf : injective f) (g : α → γ) (e' : β → γ) (a : α) : extend f g e' (f a) = g a :=
  sorry

@[simp] theorem extend_comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β}
    (hf : injective f) (g : α → γ) (e' : β → γ) : extend f g e' ∘ f = g :=
  funext fun (a : α) => extend_apply hf g e' a

theorem uncurry_def {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : α → β → γ) :
    uncurry f = fun (p : α × β) => f (prod.fst p) (prod.snd p) :=
  rfl

@[simp] theorem uncurry_apply_pair {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : α → β → γ)
    (x : α) (y : β) : uncurry f (x, y) = f x y :=
  rfl

@[simp] theorem curry_apply {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : α × β → γ) (x : α)
    (y : β) : curry f x y = f (x, y) :=
  rfl

/-- Compose a binary function `f` with a pair of unary functions `g` and `h`.
If both arguments of `f` have the same type and `g = h`, then `bicompl f g g = f on g`. -/
def bicompl {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {ε : Type u_5}
    (f : γ → δ → ε) (g : α → γ) (h : β → δ) (a : α) (b : β) : ε :=
  f (g a) (h b)

/-- Compose an unary function `f` with a binary function `g`. -/
def bicompr {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} (f : γ → δ) (g : α → β → γ)
    (a : α) (b : β) : δ :=
  f (g a b)

-- Suggested local notation:

theorem uncurry_bicompr {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} (f : α → β → γ)
    (g : γ → δ) : uncurry (bicompr g f) = g ∘ uncurry f :=
  rfl

theorem uncurry_bicompl {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {ε : Type u_5}
    (f : γ → δ → ε) (g : α → γ) (h : β → δ) : uncurry (bicompl f g h) = uncurry f ∘ prod.map g h :=
  rfl

/-- Records a way to turn an element of `α` into a function from `β` to `γ`. The most generic use
is to recursively uncurry. For instance `f : α → β → γ → δ` will be turned into
`↿f : α × β × γ → δ`. One can also add instances for bundled maps. -/
class has_uncurry (α : Type u_5) (β : outParam (Type u_6)) (γ : outParam (Type u_7)) where
  uncurry : α → β → γ

prefix:1024 "↿" => Mathlib.function.has_uncurry.uncurry

/-- Uncurrying operator. The most generic use is to recursively uncurry. For instance
`f : α → β → γ → δ` will be turned into `↿f : α × β × γ → δ`. One can also add instances
for bundled maps.-/
protected instance has_uncurry_base {α : Type u_1} {β : Type u_2} : has_uncurry (α → β) α β :=
  has_uncurry.mk id

protected instance has_uncurry_induction {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4}
    [has_uncurry β γ δ] : has_uncurry (α → β) (α × γ) δ :=
  has_uncurry.mk fun (f : α → β) (p : α × γ) => has_uncurry.uncurry (f (prod.fst p)) (prod.snd p)

/-- A function is involutive, if `f ∘ f = id`. -/
def involutive {α : Sort u_1} (f : α → α) := ∀ (x : α), f (f x) = x

theorem involutive_iff_iter_2_eq_id {α : Sort u_1} {f : α → α} :
    involutive f ↔ nat.iterate f (bit0 1) = id :=
  iff.symm funext_iff

namespace involutive


@[simp] theorem comp_self {α : Sort u} {f : α → α} (h : involutive f) : f ∘ f = id := funext h

protected theorem left_inverse {α : Sort u} {f : α → α} (h : involutive f) : left_inverse f f := h

protected theorem right_inverse {α : Sort u} {f : α → α} (h : involutive f) : right_inverse f f := h

protected theorem injective {α : Sort u} {f : α → α} (h : involutive f) : injective f :=
  left_inverse.injective (involutive.left_inverse h)

protected theorem surjective {α : Sort u} {f : α → α} (h : involutive f) : surjective f :=
  fun (x : α) => Exists.intro (f x) (h x)

protected theorem bijective {α : Sort u} {f : α → α} (h : involutive f) : bijective f :=
  { left := involutive.injective h, right := involutive.surjective h }

/-- Involuting an `ite` of an involuted value `x : α` negates the `Prop` condition in the `ite`. -/
protected theorem ite_not {α : Sort u} {f : α → α} (h : involutive f) (P : Prop) [Decidable P]
    (x : α) : f (ite P x (f x)) = ite (¬P) x (f x) :=
  sorry

end involutive


/-- The property of a binary function `f : α → β → γ` being injective.
  Mathematically this should be thought of as the corresponding function `α × β → γ` being injective.
-/
def injective2 {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → γ) :=
  ∀ {a₁ a₂ : α} {b₁ b₂ : β}, f a₁ b₁ = f a₂ b₂ → a₁ = a₂ ∧ b₁ = b₂

namespace injective2


protected theorem left {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : α → β → γ)
    (hf : injective2 f) {a₁ : α} {a₂ : α} {b₁ : β} {b₂ : β} (h : f a₁ b₁ = f a₂ b₂) : a₁ = a₂ :=
  and.left (hf h)

protected theorem right {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : α → β → γ)
    (hf : injective2 f) {a₁ : α} {a₂ : α} {b₁ : β} {b₂ : β} (h : f a₁ b₁ = f a₂ b₂) : b₁ = b₂ :=
  and.right (hf h)

theorem eq_iff {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : α → β → γ) (hf : injective2 f)
    {a₁ : α} {a₂ : α} {b₁ : β} {b₂ : β} : f a₁ b₁ = f a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ :=
  sorry

end injective2


/-- `sometimes f` evaluates to some value of `f`, if it exists. This function is especially
interesting in the case where `α` is a proposition, in which case `f` is necessarily a
constant function, so that `sometimes f = f a` for all `a`. -/
def sometimes {α : Sort u_1} {β : Sort u_2} [Nonempty β] (f : α → β) : β :=
  dite (Nonempty α) (fun (h : Nonempty α) => f (Classical.choice h))
    fun (h : ¬Nonempty α) => Classical.choice _inst_1

theorem sometimes_eq {p : Prop} {α : Sort u_1} [Nonempty α] (f : p → α) (a : p) :
    sometimes f = f a :=
  dif_pos (Nonempty.intro a)

theorem sometimes_spec {p : Prop} {α : Sort u_1} [Nonempty α] (P : α → Prop) (f : p → α) (a : p)
    (h : P (f a)) : P (sometimes f) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (P (sometimes f))) (sometimes_eq f a))) h

end function


/-- `s.piecewise f g` is the function equal to `f` on the set `s`, and to `g` on its complement. -/
def set.piecewise {α : Type u} {β : α → Sort v} (s : set α) (f : (i : α) → β i) (g : (i : α) → β i)
    [(j : α) → Decidable (j ∈ s)] (i : α) : β i :=
  ite (i ∈ s) (f i) (g i)

end Mathlib