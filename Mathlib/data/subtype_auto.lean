/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.tactic.lint.default
import Mathlib.tactic.ext
import Mathlib.tactic.simps
import PostPort

universes u_1 u_2 u_3 

namespace Mathlib

namespace subtype


/-- See Note [custom simps projection] -/
def simps.val {α : Sort u_1} {p : α → Prop} (x : Subtype p) : α :=
  ↑x

/-- A version of `x.property` or `x.2` where `p` is syntactically applied to the coercion of `x`
  instead of `x.1`. A similar result is `subtype.mem` in `data.set.basic`. -/
theorem prop {α : Sort u_1} {p : α → Prop} (x : Subtype p) : p ↑x :=
  property x

@[simp] theorem val_eq_coe {α : Sort u_1} {p : α → Prop} {x : Subtype p} : val x = ↑x :=
  rfl

@[simp] protected theorem forall {α : Sort u_1} {p : α → Prop} {q : (Subtype fun (a : α) => p a) → Prop} : (∀ (x : Subtype fun (a : α) => p a), q x) ↔ ∀ (a : α) (b : p a), q { val := a, property := b } := sorry

/-- An alternative version of `subtype.forall`. This one is useful if Lean cannot figure out `q`
  when using `subtype.forall` from right to left. -/
protected theorem forall' {α : Sort u_1} {p : α → Prop} {q : (x : α) → p x → Prop} : (∀ (x : α) (h : p x), q x h) ↔ ∀ (x : Subtype fun (a : α) => p a), q (↑x) (property x) :=
  iff.symm subtype.forall

@[simp] protected theorem exists {α : Sort u_1} {p : α → Prop} {q : (Subtype fun (a : α) => p a) → Prop} : (∃ (x : Subtype fun (a : α) => p a), q x) ↔ ∃ (a : α), ∃ (b : p a), q { val := a, property := b } := sorry

protected theorem ext {α : Sort u_1} {p : α → Prop} {a1 : Subtype fun (x : α) => p x} {a2 : Subtype fun (x : α) => p x} : ↑a1 = ↑a2 → a1 = a2 := sorry

theorem ext_iff {α : Sort u_1} {p : α → Prop} {a1 : Subtype fun (x : α) => p x} {a2 : Subtype fun (x : α) => p x} : a1 = a2 ↔ ↑a1 = ↑a2 :=
  { mp := congr_arg fun {a1 : Subtype fun (x : α) => p x} => ↑a1, mpr := subtype.ext }

theorem heq_iff_coe_eq {α : Sort u_1} {p : α → Prop} {q : α → Prop} (h : ∀ (x : α), p x ↔ q x) {a1 : Subtype fun (x : α) => p x} {a2 : Subtype fun (x : α) => q x} : a1 == a2 ↔ ↑a1 = ↑a2 :=
  Eq._oldrec (fun (a2' : Subtype fun (x : α) => p x) => iff.trans heq_iff_eq ext_iff)
    (funext fun (x : α) => propext (h x)) a2

theorem ext_val {α : Sort u_1} {p : α → Prop} {a1 : Subtype fun (x : α) => p x} {a2 : Subtype fun (x : α) => p x} : val a1 = val a2 → a1 = a2 :=
  subtype.ext

theorem ext_iff_val {α : Sort u_1} {p : α → Prop} {a1 : Subtype fun (x : α) => p x} {a2 : Subtype fun (x : α) => p x} : a1 = a2 ↔ val a1 = val a2 :=
  ext_iff

@[simp] theorem coe_eta {α : Sort u_1} {p : α → Prop} (a : Subtype fun (a : α) => p a) (h : p ↑a) : { val := ↑a, property := h } = a :=
  subtype.ext rfl

@[simp] theorem coe_mk {α : Sort u_1} {p : α → Prop} (a : α) (h : p a) : ↑{ val := a, property := h } = a :=
  rfl

@[simp] theorem mk_eq_mk {α : Sort u_1} {p : α → Prop} {a : α} {h : p a} {a' : α} {h' : p a'} : { val := a, property := h } = { val := a', property := h' } ↔ a = a' :=
  ext_iff

theorem coe_eq_iff {α : Sort u_1} {p : α → Prop} {a : Subtype fun (a : α) => p a} {b : α} : ↑a = b ↔ ∃ (h : p b), a = { val := b, property := h } := sorry

theorem coe_injective {α : Sort u_1} {p : α → Prop} : function.injective coe :=
  fun (a b : Subtype p) => subtype.ext

theorem val_injective {α : Sort u_1} {p : α → Prop} : function.injective val :=
  coe_injective

/-- Restrict a (dependent) function to a subtype -/
def restrict {α : Sort u_1} {β : α → Type u_2} (f : (x : α) → β x) (p : α → Prop) (x : Subtype p) : β (val x) :=
  f ↑x

theorem restrict_apply {α : Sort u_1} {β : α → Type u_2} (f : (x : α) → β x) (p : α → Prop) (x : Subtype p) : restrict f p x = f (val x) :=
  Eq.refl (restrict f p x)

theorem restrict_def {α : Sort u_1} {β : Type u_2} (f : α → β) (p : α → Prop) : restrict f p = f ∘ coe :=
  Eq.refl (restrict f p)

theorem restrict_injective {α : Sort u_1} {β : Type u_2} {f : α → β} (p : α → Prop) (h : function.injective f) : function.injective (restrict f p) :=
  function.injective.comp h coe_injective

/-- Defining a map into a subtype, this can be seen as an "coinduction principle" of `subtype`-/
def coind {α : Sort u_1} {β : Sort u_2} (f : α → β) {p : β → Prop} (h : ∀ (a : α), p (f a)) : α → Subtype p :=
  fun (a : α) => { val := f a, property := h a }

theorem coind_injective {α : Sort u_1} {β : Sort u_2} {f : α → β} {p : β → Prop} (h : ∀ (a : α), p (f a)) (hf : function.injective f) : function.injective (coind f h) :=
  fun (x y : α) (hxy : coind f h x = coind f h y) => hf (congr_arg val hxy)

theorem coind_surjective {α : Sort u_1} {β : Sort u_2} {f : α → β} {p : β → Prop} (h : ∀ (a : α), p (f a)) (hf : function.surjective f) : function.surjective (coind f h) := sorry

theorem coind_bijective {α : Sort u_1} {β : Sort u_2} {f : α → β} {p : β → Prop} (h : ∀ (a : α), p (f a)) (hf : function.bijective f) : function.bijective (coind f h) :=
  { left := coind_injective h (and.left hf), right := coind_surjective h (and.right hf) }

/-- Restriction of a function to a function on subtypes. -/
@[simp] theorem map_coe {α : Sort u_1} {β : Sort u_2} {p : α → Prop} {q : β → Prop} (f : α → β) (h : ∀ (a : α), p a → q (f a)) : ∀ (ᾰ : Subtype p), ↑(map f h ᾰ) = f ↑ᾰ :=
  fun (ᾰ : Subtype p) => Eq.refl ↑(map f h ᾰ)

theorem map_comp {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} {p : α → Prop} {q : β → Prop} {r : γ → Prop} {x : Subtype p} (f : α → β) (h : ∀ (a : α), p a → q (f a)) (g : β → γ) (l : ∀ (a : β), q a → r (g a)) : map g l (map f h x) = map (g ∘ f) (fun (a : α) (ha : p a) => l (f a) (h a ha)) x :=
  rfl

theorem map_id {α : Sort u_1} {p : α → Prop} {h : ∀ (a : α), p a → p (id a)} : map id h = id := sorry

theorem map_injective {α : Sort u_1} {β : Sort u_2} {p : α → Prop} {q : β → Prop} {f : α → β} (h : ∀ (a : α), p a → q (f a)) (hf : function.injective f) : function.injective (map f h) :=
  coind_injective (fun (x : Subtype fun (a : α) => p a) => map._proof_1 f h x) (function.injective.comp hf coe_injective)

theorem map_involutive {α : Sort u_1} {p : α → Prop} {f : α → α} (h : ∀ (a : α), p a → p (f a)) (hf : function.involutive f) : function.involutive (map f h) :=
  fun (x : Subtype fun (a : α) => p a) => subtype.ext (hf ↑x)

protected instance has_equiv {α : Sort u_1} [has_equiv α] (p : α → Prop) : has_equiv (Subtype p) :=
  has_equiv.mk fun (s t : Subtype p) => ↑s ≈ ↑t

theorem equiv_iff {α : Sort u_1} [has_equiv α] {p : α → Prop} {s : Subtype p} {t : Subtype p} : s ≈ t ↔ ↑s ≈ ↑t :=
  iff.rfl

protected theorem refl {α : Sort u_1} {p : α → Prop} [setoid α] (s : Subtype p) : s ≈ s :=
  setoid.refl ↑s

protected theorem symm {α : Sort u_1} {p : α → Prop} [setoid α] {s : Subtype p} {t : Subtype p} (h : s ≈ t) : t ≈ s :=
  setoid.symm h

protected theorem trans {α : Sort u_1} {p : α → Prop} [setoid α] {s : Subtype p} {t : Subtype p} {u : Subtype p} (h₁ : s ≈ t) (h₂ : t ≈ u) : s ≈ u :=
  setoid.trans h₁ h₂

theorem equivalence {α : Sort u_1} [setoid α] (p : α → Prop) : equivalence has_equiv.equiv :=
  mk_equivalence has_equiv.equiv subtype.refl subtype.symm subtype.trans

protected instance setoid {α : Sort u_1} [setoid α] (p : α → Prop) : setoid (Subtype p) :=
  setoid.mk has_equiv.equiv (equivalence p)

end subtype


namespace subtype


/-! Some facts about sets, which require that `α` is a type. -/

@[simp] theorem coe_prop {α : Type u_1} {S : set α} (a : Subtype fun (a : α) => a ∈ S) : ↑a ∈ S :=
  prop a

theorem val_prop {α : Type u_1} {S : set α} (a : Subtype fun (a : α) => a ∈ S) : val a ∈ S :=
  property a

