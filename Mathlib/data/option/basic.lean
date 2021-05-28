/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.basic
import Mathlib.PostPort

universes u_1 u_2 u_3 

namespace Mathlib

namespace option


theorem coe_def {α : Type u_1} : coe = some :=
  rfl

theorem some_ne_none {α : Type u_1} (x : α) : some x ≠ none :=
  fun (h : some x = none) => option.no_confusion h

@[simp] theorem get_mem {α : Type u_1} {o : Option α} (h : ↥(is_some o)) : get h ∈ o :=
  option.cases_on o
    (fun (h : ↥(is_some none)) => eq.dcases_on h (fun (a : tt = false) => bool.no_confusion a) (Eq.refl tt) (HEq.refl h))
    (fun (o : α) (h : ↥(is_some (some o))) => idRhs (some o = some o) rfl) h

theorem get_of_mem {α : Type u_1} {a : α} {o : Option α} (h : ↥(is_some o)) : a ∈ o → get h = a := sorry

@[simp] theorem not_mem_none {α : Type u_1} (a : α) : ¬a ∈ none :=
  fun (h : a ∈ none) => option.no_confusion h

@[simp] theorem some_get {α : Type u_1} {x : Option α} (h : ↥(is_some x)) : some (get h) = x :=
  option.cases_on x
    (fun (h : ↥(is_some none)) => eq.dcases_on h (fun (a : tt = false) => bool.no_confusion a) (Eq.refl tt) (HEq.refl h))
    (fun (x : α) (h : ↥(is_some (some x))) => idRhs (some (get h) = some (get h)) rfl) h

@[simp] theorem get_some {α : Type u_1} (x : α) (h : ↥(is_some (some x))) : get h = x :=
  rfl

@[simp] theorem get_or_else_some {α : Type u_1} (x : α) (y : α) : get_or_else (some x) y = x :=
  rfl

@[simp] theorem get_or_else_coe {α : Type u_1} (x : α) (y : α) : get_or_else (↑x) y = x :=
  rfl

theorem get_or_else_of_ne_none {α : Type u_1} {x : Option α} (hx : x ≠ none) (y : α) : some (get_or_else x y) = x := sorry

theorem mem_unique {α : Type u_1} {o : Option α} {a : α} {b : α} (ha : a ∈ o) (hb : b ∈ o) : a = b :=
  some.inj (Eq.trans (Eq.symm ha) hb)

theorem some_injective (α : Type u_1) : function.injective some :=
  fun (_x _x_1 : α) => iff.mp some_inj

/-- `option.map f` is injective if `f` is injective. -/
theorem map_injective {α : Type u_1} {β : Type u_2} {f : α → β} (Hf : function.injective f) : function.injective (option.map f) := sorry

theorem ext {α : Type u_1} {o₁ : Option α} {o₂ : Option α} : (∀ (a : α), a ∈ o₁ ↔ a ∈ o₂) → o₁ = o₂ := sorry

theorem eq_none_iff_forall_not_mem {α : Type u_1} {o : Option α} : o = none ↔ ∀ (a : α), ¬a ∈ o := sorry

@[simp] theorem none_bind {α : Type u_1} {β : Type u_1} (f : α → Option β) : none >>= f = none :=
  rfl

@[simp] theorem some_bind {α : Type u_1} {β : Type u_1} (a : α) (f : α → Option β) : some a >>= f = f a :=
  rfl

@[simp] theorem none_bind' {α : Type u_1} {β : Type u_2} (f : α → Option β) : option.bind none f = none :=
  rfl

@[simp] theorem some_bind' {α : Type u_1} {β : Type u_2} (a : α) (f : α → Option β) : option.bind (some a) f = f a :=
  rfl

@[simp] theorem bind_some {α : Type u_1} (x : Option α) : x >>= some = x :=
  bind_pure

@[simp] theorem bind_eq_some {α : Type u_1} {β : Type u_1} {x : Option α} {f : α → Option β} {b : β} : x >>= f = some b ↔ ∃ (a : α), x = some a ∧ f a = some b := sorry

@[simp] theorem bind_eq_some' {α : Type u_1} {β : Type u_2} {x : Option α} {f : α → Option β} {b : β} : option.bind x f = some b ↔ ∃ (a : α), x = some a ∧ f a = some b := sorry

@[simp] theorem bind_eq_none' {α : Type u_1} {β : Type u_2} {o : Option α} {f : α → Option β} : option.bind o f = none ↔ ∀ (b : β) (a : α), a ∈ o → ¬b ∈ f a := sorry

@[simp] theorem bind_eq_none {α : Type u_1} {β : Type u_1} {o : Option α} {f : α → Option β} : o >>= f = none ↔ ∀ (b : β) (a : α), a ∈ o → ¬b ∈ f a :=
  bind_eq_none'

theorem bind_comm {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β → Option γ} (a : Option α) (b : Option β) : (option.bind a fun (x : α) => option.bind b (f x)) = option.bind b fun (y : β) => option.bind a fun (x : α) => f x y := sorry

theorem bind_assoc {α : Type u_1} {β : Type u_2} {γ : Type u_3} (x : Option α) (f : α → Option β) (g : β → Option γ) : option.bind (option.bind x f) g = option.bind x fun (y : α) => option.bind (f y) g :=
  option.cases_on x (Eq.refl (option.bind (option.bind none f) g))
    fun (x : α) => Eq.refl (option.bind (option.bind (some x) f) g)

theorem join_eq_some {α : Type u_1} {x : Option (Option α)} {a : α} : join x = some a ↔ x = some (some a) := sorry

theorem join_ne_none {α : Type u_1} {x : Option (Option α)} : join x ≠ none ↔ ∃ (z : α), x = some (some z) := sorry

theorem join_ne_none' {α : Type u_1} {x : Option (Option α)} : ¬join x = none ↔ ∃ (z : α), x = some (some z) := sorry

theorem bind_id_eq_join {α : Type u_1} {x : Option (Option α)} : x >>= id = join x := sorry

theorem join_eq_join {α : Type u_1} : mjoin = join := sorry

theorem bind_eq_bind {α : Type u_1} {β : Type u_1} {f : α → Option β} {x : Option α} : x >>= f = option.bind x f :=
  rfl

@[simp] theorem map_eq_map {α : Type u_1} {β : Type u_1} {f : α → β} : Functor.map f = option.map f :=
  rfl

theorem map_none {α : Type u_1} {β : Type u_1} {f : α → β} : f <$> none = none :=
  rfl

theorem map_some {α : Type u_1} {β : Type u_1} {a : α} {f : α → β} : f <$> some a = some (f a) :=
  rfl

@[simp] theorem map_none' {α : Type u_1} {β : Type u_2} {f : α → β} : option.map f none = none :=
  rfl

@[simp] theorem map_some' {α : Type u_1} {β : Type u_2} {a : α} {f : α → β} : option.map f (some a) = some (f a) :=
  rfl

theorem map_eq_some {α : Type u_1} {β : Type u_1} {x : Option α} {f : α → β} {b : β} : f <$> x = some b ↔ ∃ (a : α), x = some a ∧ f a = b := sorry

@[simp] theorem map_eq_some' {α : Type u_1} {β : Type u_2} {x : Option α} {f : α → β} {b : β} : option.map f x = some b ↔ ∃ (a : α), x = some a ∧ f a = b := sorry

theorem map_eq_none {α : Type u_1} {β : Type u_1} {x : Option α} {f : α → β} : f <$> x = none ↔ x = none := sorry

@[simp] theorem map_eq_none' {α : Type u_1} {β : Type u_2} {x : Option α} {f : α → β} : option.map f x = none ↔ x = none := sorry

theorem map_congr {α : Type u_1} {β : Type u_2} {f : α → β} {g : α → β} {x : Option α} (h : ∀ (a : α), a ∈ x → f a = g a) : option.map f x = option.map g x := sorry

@[simp] theorem map_id' {α : Type u_1} : option.map id = id :=
  map_id

@[simp] theorem map_map {α : Type u_1} {β : Type u_2} {γ : Type u_3} (h : β → γ) (g : α → β) (x : Option α) : option.map h (option.map g x) = option.map (h ∘ g) x := sorry

theorem comp_map {α : Type u_1} {β : Type u_2} {γ : Type u_3} (h : β → γ) (g : α → β) (x : Option α) : option.map (h ∘ g) x = option.map h (option.map g x) :=
  Eq.symm (map_map h g x)

@[simp] theorem map_comp_map {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : α → β) (g : β → γ) : option.map g ∘ option.map f = option.map (g ∘ f) := sorry

theorem mem_map_of_mem {α : Type u_1} {β : Type u_2} {a : α} {x : Option α} (g : α → β) (h : a ∈ x) : g a ∈ option.map g x :=
  iff.mpr mem_def (Eq.symm (iff.mp mem_def h) ▸ map_some')

theorem bind_map_comm {α : Type u_1} {β : Type u_1} {x : Option (Option α)} {f : α → β} : x >>= option.map f = option.map (option.map f) x >>= id := sorry

theorem join_map_eq_map_join {α : Type u_1} {β : Type u_2} {f : α → β} {x : Option (Option α)} : join (option.map (option.map f) x) = option.map f (join x) := sorry

theorem join_join {α : Type u_1} {x : Option (Option (Option α))} : join (join x) = join (option.map join x) := sorry

theorem mem_of_mem_join {α : Type u_1} {a : α} {x : Option (Option α)} (h : a ∈ join x) : some a ∈ x :=
  iff.mpr mem_def (Eq.symm (iff.mp mem_def h) ▸ iff.mp join_eq_some h)

@[simp] theorem pbind_eq_bind {α : Type u_1} {β : Type u_2} (f : α → Option β) (x : Option α) : (pbind x fun (a : α) (_x : a ∈ x) => f a) = option.bind x f := sorry

theorem map_bind {α : Type u_1} {β : Type u_1} {γ : Type u_1} (f : β → γ) (x : Option α) (g : α → Option β) : option.map f (x >>= g) =
  do 
    let a ← x 
    option.map f (g a) := sorry

theorem map_bind' {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : β → γ) (x : Option α) (g : α → Option β) : option.map f (option.bind x g) = option.bind x fun (a : α) => option.map f (g a) := sorry

theorem map_pbind {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : β → γ) (x : Option α) (g : (a : α) → a ∈ x → Option β) : option.map f (pbind x g) = pbind x fun (a : α) (H : a ∈ x) => option.map f (g a H) := sorry

theorem pbind_map {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : α → β) (x : Option α) (g : (b : β) → b ∈ option.map f x → Option γ) : pbind (option.map f x) g = pbind x fun (a : α) (h : a ∈ x) => g (f a) (mem_map_of_mem f h) :=
  option.cases_on x (fun (g : (b : β) → b ∈ option.map f none → Option γ) => Eq.refl (pbind (option.map f none) g))
    (fun (x : α) (g : (b : β) → b ∈ option.map f (some x) → Option γ) => Eq.refl (pbind (option.map f (some x)) g)) g

@[simp] theorem pmap_none {α : Type u_1} {β : Type u_2} {p : α → Prop} (f : (a : α) → p a → β) {H : ∀ (a : α), a ∈ none → p a} : pmap f none H = none :=
  rfl

@[simp] theorem pmap_some {α : Type u_1} {β : Type u_2} {p : α → Prop} (f : (a : α) → p a → β) {x : α} (h : p x) : pmap f (some x) = fun (_x : ∀ (a : α), a ∈ some x → p a) => some (f x h) :=
  rfl

theorem mem_pmem {α : Type u_1} {β : Type u_2} {p : α → Prop} (f : (a : α) → p a → β) (x : Option α) {a : α} (h : ∀ (a : α), a ∈ x → p a) (ha : a ∈ x) : f a (h a ha) ∈ pmap f x h :=
  eq.mpr (id (Eq._oldrec (Eq.refl (f a (h a ha) ∈ pmap f x h)) (propext mem_def)))
    (Eq._oldrec (fun (h : ∀ (a_1 : α), a_1 ∈ some a → p a_1) (ha : a ∈ some a) => Eq.refl (pmap f (some a) h))
      (Eq.symm (eq.mp (Eq._oldrec (Eq.refl (a ∈ x)) (propext mem_def)) ha)) h ha)

theorem pmap_map {α : Type u_1} {β : Type u_2} {γ : Type u_3} {p : α → Prop} (f : (a : α) → p a → β) (g : γ → α) (x : Option γ) (H : ∀ (a : α), a ∈ option.map g x → p a) : pmap f (option.map g x) H =
  pmap (fun (a : γ) (h : p (g a)) => f (g a) h) x fun (a : γ) (h : a ∈ x) => H (g a) (mem_map_of_mem g h) := sorry

theorem map_pmap {α : Type u_1} {β : Type u_2} {γ : Type u_3} {p : α → Prop} (g : β → γ) (f : (a : α) → p a → β) (x : Option α) (H : ∀ (a : α), a ∈ x → p a) : option.map g (pmap f x H) = pmap (fun (a : α) (h : p a) => g (f a h)) x H := sorry

@[simp] theorem pmap_eq_map {α : Type u_1} {β : Type u_2} (p : α → Prop) (f : α → β) (x : Option α) (H : ∀ (a : α), a ∈ x → p a) : pmap (fun (a : α) (_x : p a) => f a) x H = option.map f x := sorry

theorem pmap_bind {α : Type u_1} {β : Type u_1} {γ : Type u_1} {x : Option α} {g : α → Option β} {p : β → Prop} {f : (b : β) → p b → γ} (H : ∀ (a : β), a ∈ x >>= g → p a) (H' : ∀ (a : α) (b : β), b ∈ g a → b ∈ x >>= g) : pmap f (x >>= g) H =
  do 
    let a ← x 
    pmap f (g a) fun (b : β) (h : b ∈ g a) => H b (H' a b h) := sorry

theorem bind_pmap {α : Type u_1} {β : Type u_2} {γ : Type u_2} {p : α → Prop} (f : (a : α) → p a → β) (x : Option α) (g : β → Option γ) (H : ∀ (a : α), a ∈ x → p a) : pmap f x H >>= g = pbind x fun (a : α) (h : a ∈ x) => g (f a (H a h)) := sorry

theorem pbind_eq_none {α : Type u_1} {β : Type u_2} {x : Option α} {f : (a : α) → a ∈ x → Option β} (h' : ∀ (a : α) (H : a ∈ x), f a H = none → x = none) : pbind x f = none ↔ x = none := sorry

theorem pbind_eq_some {α : Type u_1} {β : Type u_2} {x : Option α} {f : (a : α) → a ∈ x → Option β} {y : β} : pbind x f = some y ↔ ∃ (z : α), ∃ (H : z ∈ x), f z H = some y := sorry

@[simp] theorem pmap_eq_none_iff {α : Type u_1} {β : Type u_2} {p : α → Prop} {f : (a : α) → p a → β} {x : Option α} {h : ∀ (a : α), a ∈ x → p a} : pmap f x h = none ↔ x = none := sorry

@[simp] theorem pmap_eq_some_iff {α : Type u_1} {β : Type u_2} {p : α → Prop} {f : (a : α) → p a → β} {x : Option α} {hf : ∀ (a : α), a ∈ x → p a} {y : β} : pmap f x hf = some y ↔ ∃ (a : α), ∃ (H : x = some a), f a (hf a H) = y := sorry

@[simp] theorem join_pmap_eq_pmap_join {α : Type u_1} {β : Type u_2} {p : α → Prop} {f : (a : α) → p a → β} {x : Option (Option α)} (H : ∀ (a : Option α), a ∈ x → ∀ (a_1 : α), a_1 ∈ a → p a_1) : join (pmap (pmap f) x H) = pmap f (join x) fun (a : α) (h : a ∈ join x) => H (some a) (mem_of_mem_join h) a rfl := sorry

@[simp] theorem seq_some {α : Type u_1} {β : Type u_1} {a : α} {f : α → β} : some f <*> some a = some (f a) :=
  rfl

@[simp] theorem some_orelse' {α : Type u_1} (a : α) (x : Option α) : option.orelse (some a) x = some a :=
  rfl

@[simp] theorem some_orelse {α : Type u_1} (a : α) (x : Option α) : (some a <|> x) = some a :=
  rfl

@[simp] theorem none_orelse' {α : Type u_1} (x : Option α) : option.orelse none x = x :=
  option.cases_on x (Eq.refl (option.orelse none none)) fun (x : α) => Eq.refl (option.orelse none (some x))

@[simp] theorem none_orelse {α : Type u_1} (x : Option α) : (none <|> x) = x :=
  none_orelse' x

@[simp] theorem orelse_none' {α : Type u_1} (x : Option α) : option.orelse x none = x :=
  option.cases_on x (Eq.refl (option.orelse none none)) fun (x : α) => Eq.refl (option.orelse (some x) none)

@[simp] theorem orelse_none {α : Type u_1} (x : Option α) : (x <|> none) = x :=
  orelse_none' x

@[simp] theorem is_some_none {α : Type u_1} : is_some none = false :=
  rfl

@[simp] theorem is_some_some {α : Type u_1} {a : α} : is_some (some a) = tt :=
  rfl

theorem is_some_iff_exists {α : Type u_1} {x : Option α} : ↥(is_some x) ↔ ∃ (a : α), x = some a := sorry

@[simp] theorem is_none_none {α : Type u_1} : is_none none = tt :=
  rfl

@[simp] theorem is_none_some {α : Type u_1} {a : α} : is_none (some a) = false :=
  rfl

@[simp] theorem not_is_some {α : Type u_1} {a : Option α} : is_some a = false ↔ is_none a = tt := sorry

theorem eq_some_iff_get_eq {α : Type u_1} {o : Option α} {a : α} : o = some a ↔ ∃ (h : ↥(is_some o)), get h = a := sorry

theorem not_is_some_iff_eq_none {α : Type u_1} {o : Option α} : ¬↥(is_some o) ↔ o = none := sorry

theorem ne_none_iff_is_some {α : Type u_1} {o : Option α} : o ≠ none ↔ ↥(is_some o) := sorry

theorem ne_none_iff_exists {α : Type u_1} {o : Option α} : o ≠ none ↔ ∃ (x : α), some x = o := sorry

theorem ne_none_iff_exists' {α : Type u_1} {o : Option α} : o ≠ none ↔ ∃ (x : α), o = some x :=
  iff.trans ne_none_iff_exists (exists_congr fun (_x : α) => eq_comm)

theorem bex_ne_none {α : Type u_1} {p : Option α → Prop} : (∃ (x : Option α), ∃ (H : x ≠ none), p x) ↔ ∃ (x : α), p (some x) := sorry

theorem ball_ne_none {α : Type u_1} {p : Option α → Prop} : (∀ (x : Option α), x ≠ none → p x) ↔ ∀ (x : α), p (some x) := sorry

theorem iget_mem {α : Type u_1} [Inhabited α] {o : Option α} : ↥(is_some o) → iget o ∈ o := sorry

theorem iget_of_mem {α : Type u_1} [Inhabited α] {a : α} {o : Option α} : a ∈ o → iget o = a := sorry

@[simp] theorem guard_eq_some {α : Type u_1} {p : α → Prop} [decidable_pred p] {a : α} {b : α} : guard p a = some b ↔ a = b ∧ p a := sorry

@[simp] theorem guard_eq_some' {p : Prop} [Decidable p] (u : Unit) : guard p = some u ↔ p := sorry

theorem lift_or_get_choice {α : Type u_1} {f : α → α → α} (h : ∀ (a b : α), f a b = a ∨ f a b = b) (o₁ : Option α) (o₂ : Option α) : lift_or_get f o₁ o₂ = o₁ ∨ lift_or_get f o₁ o₂ = o₂ := sorry

@[simp] theorem lift_or_get_none_left {α : Type u_1} {f : α → α → α} {b : Option α} : lift_or_get f none b = b :=
  option.cases_on b (Eq.refl (lift_or_get f none none)) fun (b : α) => Eq.refl (lift_or_get f none (some b))

@[simp] theorem lift_or_get_none_right {α : Type u_1} {f : α → α → α} {a : Option α} : lift_or_get f a none = a :=
  option.cases_on a (Eq.refl (lift_or_get f none none)) fun (a : α) => Eq.refl (lift_or_get f (some a) none)

@[simp] theorem lift_or_get_some_some {α : Type u_1} {f : α → α → α} {a : α} {b : α} : lift_or_get f (some a) (some b) = ↑(f a b) :=
  rfl

/-- given an element of `a : option α`, a default element `b : β` and a function `α → β`, apply this
function to `a` if it comes from `α`, and return `b` otherwise. -/
def cases_on' {α : Type u_1} {β : Type u_2} : Option α → β → (α → β) → β :=
  sorry

@[simp] theorem cases_on'_none {α : Type u_1} {β : Type u_2} (x : β) (f : α → β) : cases_on' none x f = x :=
  rfl

@[simp] theorem cases_on'_some {α : Type u_1} {β : Type u_2} (x : β) (f : α → β) (a : α) : cases_on' (some a) x f = f a :=
  rfl

@[simp] theorem cases_on'_coe {α : Type u_1} {β : Type u_2} (x : β) (f : α → β) (a : α) : cases_on' (↑a) x f = f a :=
  rfl

@[simp] theorem cases_on'_none_coe {α : Type u_1} {β : Type u_2} (f : Option α → β) (o : Option α) : cases_on' o (f none) (f ∘ coe) = f o :=
  option.cases_on o (Eq.refl (cases_on' none (f none) (f ∘ coe)))
    fun (o : α) => Eq.refl (cases_on' (some o) (f none) (f ∘ coe))

