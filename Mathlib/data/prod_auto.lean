/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.basic
import Mathlib.PostPort

universes u_1 u_2 u_3 u_4 u_5 u_6 

namespace Mathlib

/-!
# Extra facts about `prod`

This file defines `prod.swap : α × β → β × α` and proves various simple lemmas about `prod`.
-/

@[simp] theorem prod_map {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} (f : α → γ)
    (g : β → δ) (p : α × β) : prod.map f g p = (f (prod.fst p), g (prod.snd p)) :=
  rfl

namespace prod


@[simp] theorem forall {α : Type u_1} {β : Type u_2} {p : α × β → Prop} :
    (∀ (x : α × β), p x) ↔ ∀ (a : α) (b : β), p (a, b) :=
  sorry

@[simp] theorem exists {α : Type u_1} {β : Type u_2} {p : α × β → Prop} :
    (∃ (x : α × β), p x) ↔ ∃ (a : α), ∃ (b : β), p (a, b) :=
  sorry

theorem forall' {α : Type u_1} {β : Type u_2} {p : α → β → Prop} :
    (∀ (x : α × β), p (fst x) (snd x)) ↔ ∀ (a : α) (b : β), p a b :=
  forall

theorem exists' {α : Type u_1} {β : Type u_2} {p : α → β → Prop} :
    (∃ (x : α × β), p (fst x) (snd x)) ↔ ∃ (a : α), ∃ (b : β), p a b :=
  exists

@[simp] theorem map_mk {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} (f : α → γ)
    (g : β → δ) (a : α) (b : β) : map f g (a, b) = (f a, g b) :=
  rfl

theorem map_fst {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} (f : α → γ) (g : β → δ)
    (p : α × β) : fst (map f g p) = f (fst p) :=
  rfl

theorem map_snd {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} (f : α → γ) (g : β → δ)
    (p : α × β) : snd (map f g p) = g (snd p) :=
  rfl

theorem map_fst' {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} (f : α → γ)
    (g : β → δ) : fst ∘ map f g = f ∘ fst :=
  funext (map_fst f g)

theorem map_snd' {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} (f : α → γ)
    (g : β → δ) : snd ∘ map f g = g ∘ snd :=
  funext (map_snd f g)

/--
Composing a `prod.map` with another `prod.map` is equal to
a single `prod.map` of composed functions.
-/
theorem map_comp_map {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {ε : Type u_5}
    {ζ : Type u_6} (f : α → β) (f' : γ → δ) (g : β → ε) (g' : δ → ζ) :
    map g g' ∘ map f f' = map (g ∘ f) (g' ∘ f') :=
  rfl

/--
Composing a `prod.map` with another `prod.map` is equal to
a single `prod.map` of composed functions, fully applied.
-/
theorem map_map {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {ε : Type u_5}
    {ζ : Type u_6} (f : α → β) (f' : γ → δ) (g : β → ε) (g' : δ → ζ) (x : α × γ) :
    map g g' (map f f' x) = map (g ∘ f) (g' ∘ f') x :=
  rfl

@[simp] theorem mk.inj_iff {α : Type u_1} {β : Type u_2} {a₁ : α} {a₂ : α} {b₁ : β} {b₂ : β} :
    (a₁, b₁) = (a₂, b₂) ↔ a₁ = a₂ ∧ b₁ = b₂ :=
  sorry

theorem mk.inj_left {α : Type u_1} {β : Type u_2} (a : α) : function.injective (Prod.mk a) := sorry

theorem mk.inj_right {α : Type u_1} {β : Type u_2} (b : β) :
    function.injective fun (a : α) => (a, b) :=
  sorry

theorem ext_iff {α : Type u_1} {β : Type u_2} {p : α × β} {q : α × β} :
    p = q ↔ fst p = fst q ∧ snd p = snd q :=
  sorry

theorem ext {α : Type u_1} {β : Type u_2} {p : α × β} {q : α × β} (h₁ : fst p = fst q)
    (h₂ : snd p = snd q) : p = q :=
  iff.mpr ext_iff { left := h₁, right := h₂ }

theorem map_def {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {f : α → γ}
    {g : β → δ} : map f g = fun (p : α × β) => (f (fst p), g (snd p)) :=
  funext fun (p : α × β) => ext (map_fst f g p) (map_snd f g p)

theorem id_prod {α : Type u_1} : (fun (p : α × α) => (fst p, snd p)) = id := sorry

theorem fst_surjective {α : Type u_1} {β : Type u_2} [h : Nonempty β] : function.surjective fst :=
  fun (x : α) => nonempty.elim h fun (y : β) => Exists.intro (x, y) rfl

theorem snd_surjective {α : Type u_1} {β : Type u_2} [h : Nonempty α] : function.surjective snd :=
  fun (y : β) => nonempty.elim h fun (x : α) => Exists.intro (x, y) rfl

theorem fst_injective {α : Type u_1} {β : Type u_2} [subsingleton β] : function.injective fst :=
  fun (x y : α × β) (h : fst x = fst y) => ext h (subsingleton.elim (snd x) (snd y))

theorem snd_injective {α : Type u_1} {β : Type u_2} [subsingleton α] : function.injective snd :=
  fun (x y : α × β) (h : snd x = snd y) => ext (subsingleton.elim (fst x) (fst y)) h

/-- Swap the factors of a product. `swap (a, b) = (b, a)` -/
def swap {α : Type u_1} {β : Type u_2} : α × β → β × α := fun (p : α × β) => (snd p, fst p)

@[simp] theorem swap_swap {α : Type u_1} {β : Type u_2} (x : α × β) : swap (swap x) = x :=
  cases_on x
    fun (x_fst : α) (x_snd : β) =>
      idRhs (swap (swap (x_fst, x_snd)) = swap (swap (x_fst, x_snd))) rfl

@[simp] theorem fst_swap {α : Type u_1} {β : Type u_2} {p : α × β} : fst (swap p) = snd p := rfl

@[simp] theorem snd_swap {α : Type u_1} {β : Type u_2} {p : α × β} : snd (swap p) = fst p := rfl

@[simp] theorem swap_prod_mk {α : Type u_1} {β : Type u_2} {a : α} {b : β} : swap (a, b) = (b, a) :=
  rfl

@[simp] theorem swap_swap_eq {α : Type u_1} {β : Type u_2} : swap ∘ swap = id := funext swap_swap

@[simp] theorem swap_left_inverse {α : Type u_1} {β : Type u_2} : function.left_inverse swap swap :=
  swap_swap

@[simp] theorem swap_right_inverse {α : Type u_1} {β : Type u_2} :
    function.right_inverse swap swap :=
  swap_swap

theorem swap_injective {α : Type u_1} {β : Type u_2} : function.injective swap :=
  function.left_inverse.injective swap_left_inverse

theorem swap_surjective {α : Type u_1} {β : Type u_2} : function.surjective swap :=
  function.left_inverse.surjective swap_left_inverse

theorem swap_bijective {α : Type u_1} {β : Type u_2} : function.bijective swap :=
  { left := swap_injective, right := swap_surjective }

@[simp] theorem swap_inj {α : Type u_1} {β : Type u_2} {p : α × β} {q : α × β} :
    swap p = swap q ↔ p = q :=
  function.injective.eq_iff swap_injective

theorem eq_iff_fst_eq_snd_eq {α : Type u_1} {β : Type u_2} {p : α × β} {q : α × β} :
    p = q ↔ fst p = fst q ∧ snd p = snd q :=
  sorry

theorem fst_eq_iff {α : Type u_1} {β : Type u_2} {p : α × β} {x : α} : fst p = x ↔ p = (x, snd p) :=
  sorry

theorem snd_eq_iff {α : Type u_1} {β : Type u_2} {p : α × β} {x : β} : snd p = x ↔ p = (fst p, x) :=
  sorry

theorem lex_def {α : Type u_1} {β : Type u_2} (r : α → α → Prop) (s : β → β → Prop) {p : α × β}
    {q : α × β} : lex r s p q ↔ r (fst p) (fst q) ∨ fst p = fst q ∧ s (snd p) (snd q) :=
  sorry

protected instance lex.decidable {α : Type u_1} {β : Type u_2} [DecidableEq α] (r : α → α → Prop)
    (s : β → β → Prop) [DecidableRel r] [DecidableRel s] : DecidableRel (lex r s) :=
  fun (p q : α × β) => decidable_of_decidable_of_iff or.decidable sorry

end prod


theorem function.injective.prod_map {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4}
    {f : α → γ} {g : β → δ} (hf : function.injective f) (hg : function.injective g) :
    function.injective (prod.map f g) :=
  fun (x y : α × β) (h : prod.map f g x = prod.map f g y) =>
    prod.ext (hf (and.left (iff.mp prod.ext_iff h))) (hg (and.right (iff.mp prod.ext_iff h)))

theorem function.surjective.prod_map {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4}
    {f : α → γ} {g : β → δ} (hf : function.surjective f) (hg : function.surjective g) :
    function.surjective (prod.map f g) :=
  sorry

end Mathlib