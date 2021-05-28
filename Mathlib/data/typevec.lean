/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad, Mario Carneiro, Simon Hudon
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.fin2
import Mathlib.logic.function.basic
import Mathlib.tactic.basic
import Mathlib.PostPort

universes u_1 u u_2 u_3 u_4 

namespace Mathlib

/-!

# Tuples of types, and their categorical structure.

## Features

* `typevec n` - n-tuples of types
* `α ⟹ β`    - n-tuples of maps
* `f ⊚ g`     - composition

Also, support functions for operating with n-tuples of types, such as:

* `append1 α β`    - append type `β` to n-tuple `α` to obtain an (n+1)-tuple
* `drop α`         - drops the last element of an (n+1)-tuple
* `last α`         - returns the last element of an (n+1)-tuple
* `append_fun f g` - appends a function g to an n-tuple of functions
* `drop_fun f`     - drops the last function from an n+1-tuple
* `last_fun f`     - returns the last function of a tuple.

Since e.g. `append1 α.drop α.last` is propositionally equal to `α` but not definitionally equal
to it, we need support functions and lemmas to mediate between constructions.
-/

/--
n-tuples of types, as a category
-/
def typevec (n : ℕ)  :=
  fin2 n → Type u_1

protected instance typevec.inhabited {n : ℕ} : Inhabited (typevec n) :=
  { default := fun (_x : fin2 n) => PUnit }

namespace typevec


/-- arrow in the category of `typevec` -/
def arrow {n : ℕ} (α : typevec n) (β : typevec n)  :=
  (i : fin2 n) → α i → β i

protected instance arrow.inhabited {n : ℕ} (α : typevec n) (β : typevec n) [(i : fin2 n) → Inhabited (β i)] : Inhabited (arrow α β) :=
  { default := fun (_x : fin2 n) (_x_1 : α _x) => Inhabited.default }

/-- identity of arrow composition -/
def id {n : ℕ} {α : typevec n} : arrow α α :=
  fun (i : fin2 n) (x : α i) => x

/-- arrow composition in the category of `typevec` -/
def comp {n : ℕ} {α : typevec n} {β : typevec n} {γ : typevec n} (g : arrow β γ) (f : arrow α β) : arrow α γ :=
  fun (i : fin2 n) (x : α i) => g i (f i x)

@[simp] theorem id_comp {n : ℕ} {α : typevec n} {β : typevec n} (f : arrow α β) : comp id f = f :=
  rfl

@[simp] theorem comp_id {n : ℕ} {α : typevec n} {β : typevec n} (f : arrow α β) : comp f id = f :=
  rfl

theorem comp_assoc {n : ℕ} {α : typevec n} {β : typevec n} {γ : typevec n} {δ : typevec n} (h : arrow γ δ) (g : arrow β γ) (f : arrow α β) : comp (comp h g) f = comp h (comp g f) :=
  rfl

/--
Support for extending a typevec by one element.
-/
def append1 {n : ℕ} (α : typevec n) (β : Type u_1) : typevec (n + 1) :=
  sorry

infixl:67 " ::: " => Mathlib.typevec.append1

/-- retain only a `n-length` prefix of the argument -/
def drop {n : ℕ} (α : typevec (n + 1)) : typevec n :=
  fun (i : fin2 n) => α (fin2.fs i)

/-- take the last value of a `(n+1)-length` vector -/
def last {n : ℕ} (α : typevec (n + 1))  :=
  α fin2.fz

protected instance last.inhabited {n : ℕ} (α : typevec (n + 1)) [Inhabited (α fin2.fz)] : Inhabited (last α) :=
  { default := Inhabited.default }

theorem drop_append1 {n : ℕ} {α : typevec n} {β : Type u_1} {i : fin2 n} : drop (α ::: β) i = α i :=
  rfl

@[simp] theorem drop_append1' {n : ℕ} {α : typevec n} {β : Type u_1} : drop (α ::: β) = α :=
  funext fun (x : fin2 n) => drop_append1

theorem last_append1 {n : ℕ} {α : typevec n} {β : Type u_1} : last (α ::: β) = β :=
  rfl

@[simp] theorem append1_drop_last {n : ℕ} (α : typevec (n + 1)) : drop α ::: last α = α := sorry

/-- cases on `(n+1)-length` vectors -/
def append1_cases {n : ℕ} {C : typevec (n + 1) → Sort u} (H : (α : typevec n) → (β : Type u_1) → C (α ::: β)) (γ : typevec (n + 1)) : C γ :=
  eq.mpr sorry (H (drop γ) (last γ))

@[simp] theorem append1_cases_append1 {n : ℕ} {C : typevec (n + 1) → Sort u} (H : (α : typevec n) → (β : Type u_1) → C (α ::: β)) (α : typevec n) (β : Type u_1) : append1_cases H (α ::: β) = H α β :=
  rfl

/-- append an arrow and a function for arbitrary source and target
type vectors -/
def split_fun {n : ℕ} {α : typevec (n + 1)} {α' : typevec (n + 1)} (f : arrow (drop α) (drop α')) (g : last α → last α') : arrow α α' :=
  sorry

/-- append an arrow and a function as well as their respective source
and target types / typevecs -/
def append_fun {n : ℕ} {α : typevec n} {α' : typevec n} {β : Type u_1} {β' : Type u_2} (f : arrow α α') (g : β → β') : arrow (α ::: β) (α' ::: β') :=
  split_fun f g

infixl:67 " ::: " => Mathlib.typevec.append_fun

/-- split off the prefix of an arrow -/
def drop_fun {n : ℕ} {α : typevec (n + 1)} {β : typevec (n + 1)} (f : arrow α β) : arrow (drop α) (drop β) :=
  fun (i : fin2 n) => f (fin2.fs i)

/-- split off the last function of an arrow -/
def last_fun {n : ℕ} {α : typevec (n + 1)} {β : typevec (n + 1)} (f : arrow α β) : last α → last β :=
  f fin2.fz

/-- arrow in the category of `0-length` vectors -/
def nil_fun {α : typevec 0} {β : typevec 0} : arrow α β :=
  fun (i : fin2 0) => fin2.elim0 i

theorem eq_of_drop_last_eq {n : ℕ} {α : typevec (n + 1)} {β : typevec (n + 1)} {f : arrow α β} {g : arrow α β} (h₀ : drop_fun f = drop_fun g) (h₁ : last_fun f = last_fun g) : f = g := sorry

@[simp] theorem drop_fun_split_fun {n : ℕ} {α : typevec (n + 1)} {α' : typevec (n + 1)} (f : arrow (drop α) (drop α')) (g : last α → last α') : drop_fun (split_fun f g) = f :=
  rfl

/-- turn an equality into an arrow -/
def arrow.mp {n : ℕ} {α : typevec n} {β : typevec n} (h : α = β) : arrow α β :=
  sorry

/-- turn an equality into an arrow, with reverse direction -/
def arrow.mpr {n : ℕ} {α : typevec n} {β : typevec n} (h : α = β) : arrow β α :=
  sorry

/-- decompose a vector into its prefix appended with its last element -/
def to_append1_drop_last {n : ℕ} {α : typevec (n + 1)} : arrow α (drop α ::: last α) :=
  arrow.mpr (append1_drop_last α)

/-- stitch two bits of a vector back together -/
def from_append1_drop_last {n : ℕ} {α : typevec (n + 1)} : arrow (drop α ::: last α) α :=
  arrow.mp (append1_drop_last α)

@[simp] theorem last_fun_split_fun {n : ℕ} {α : typevec (n + 1)} {α' : typevec (n + 1)} (f : arrow (drop α) (drop α')) (g : last α → last α') : last_fun (split_fun f g) = g :=
  rfl

@[simp] theorem drop_fun_append_fun {n : ℕ} {α : typevec n} {α' : typevec n} {β : Type u_1} {β' : Type u_2} (f : arrow α α') (g : β → β') : drop_fun (f ::: g) = f :=
  rfl

@[simp] theorem last_fun_append_fun {n : ℕ} {α : typevec n} {α' : typevec n} {β : Type u_1} {β' : Type u_2} (f : arrow α α') (g : β → β') : last_fun (f ::: g) = g :=
  rfl

theorem split_drop_fun_last_fun {n : ℕ} {α : typevec (n + 1)} {α' : typevec (n + 1)} (f : arrow α α') : split_fun (drop_fun f) (last_fun f) = f :=
  eq_of_drop_last_eq rfl rfl

theorem split_fun_inj {n : ℕ} {α : typevec (n + 1)} {α' : typevec (n + 1)} {f : arrow (drop α) (drop α')} {f' : arrow (drop α) (drop α')} {g : last α → last α'} {g' : last α → last α'} (H : split_fun f g = split_fun f' g') : f = f' ∧ g = g' := sorry

theorem append_fun_inj {n : ℕ} {α : typevec n} {α' : typevec n} {β : Type u_1} {β' : Type u_2} {f : arrow α α'} {f' : arrow α α'} {g : β → β'} {g' : β → β'} : f ::: g = f' ::: g' → f = f' ∧ g = g' :=
  split_fun_inj

theorem split_fun_comp {n : ℕ} {α₀ : typevec (n + 1)} {α₁ : typevec (n + 1)} {α₂ : typevec (n + 1)} (f₀ : arrow (drop α₀) (drop α₁)) (f₁ : arrow (drop α₁) (drop α₂)) (g₀ : last α₀ → last α₁) (g₁ : last α₁ → last α₂) : split_fun (comp f₁ f₀) (g₁ ∘ g₀) = comp (split_fun f₁ g₁) (split_fun f₀ g₀) :=
  eq_of_drop_last_eq rfl rfl

theorem append_fun_comp_split_fun {n : ℕ} {α : typevec n} {γ : typevec n} {β : Type u_1} {δ : Type u_2} {ε : typevec (n + 1)} (f₀ : arrow (drop ε) α) (f₁ : arrow α γ) (g₀ : last ε → β) (g₁ : β → δ) : comp (f₁ ::: g₁) (split_fun f₀ g₀) = split_fun (comp f₁ f₀) (g₁ ∘ g₀) :=
  Eq.symm (split_fun_comp f₀ f₁ g₀ g₁)

theorem append_fun_comp {n : ℕ} {α₀ : typevec n} {α₁ : typevec n} {α₂ : typevec n} {β₀ : Type u_1} {β₁ : Type u_2} {β₂ : Type u_3} (f₀ : arrow α₀ α₁) (f₁ : arrow α₁ α₂) (g₀ : β₀ → β₁) (g₁ : β₁ → β₂) : comp f₁ f₀ ::: g₁ ∘ g₀ = comp (f₁ ::: g₁) (f₀ ::: g₀) :=
  eq_of_drop_last_eq rfl rfl

theorem append_fun_comp' {n : ℕ} {α₀ : typevec n} {α₁ : typevec n} {α₂ : typevec n} {β₀ : Type u_1} {β₁ : Type u_2} {β₂ : Type u_3} (f₀ : arrow α₀ α₁) (f₁ : arrow α₁ α₂) (g₀ : β₀ → β₁) (g₁ : β₁ → β₂) : comp (f₁ ::: g₁) (f₀ ::: g₀) = comp f₁ f₀ ::: g₁ ∘ g₀ :=
  eq_of_drop_last_eq rfl rfl

theorem nil_fun_comp {α₀ : typevec 0} (f₀ : arrow α₀ fin2.elim0) : comp nil_fun f₀ = f₀ :=
  funext fun (x : fin2 0) => fin2.elim0 x

theorem append_fun_comp_id {n : ℕ} {α : typevec n} {β₀ : Type u_1} {β₁ : Type u_1} {β₂ : Type u_1} (g₀ : β₀ → β₁) (g₁ : β₁ → β₂) : id ::: g₁ ∘ g₀ = comp (id ::: g₁) (id ::: g₀) :=
  eq_of_drop_last_eq rfl rfl

@[simp] theorem drop_fun_comp {n : ℕ} {α₀ : typevec (n + 1)} {α₁ : typevec (n + 1)} {α₂ : typevec (n + 1)} (f₀ : arrow α₀ α₁) (f₁ : arrow α₁ α₂) : drop_fun (comp f₁ f₀) = comp (drop_fun f₁) (drop_fun f₀) :=
  rfl

@[simp] theorem last_fun_comp {n : ℕ} {α₀ : typevec (n + 1)} {α₁ : typevec (n + 1)} {α₂ : typevec (n + 1)} (f₀ : arrow α₀ α₁) (f₁ : arrow α₁ α₂) : last_fun (comp f₁ f₀) = last_fun f₁ ∘ last_fun f₀ :=
  rfl

theorem append_fun_aux {n : ℕ} {α : typevec n} {α' : typevec n} {β : Type u_1} {β' : Type u_2} (f : arrow (α ::: β) (α' ::: β')) : drop_fun f ::: last_fun f = f :=
  eq_of_drop_last_eq rfl rfl

theorem append_fun_id_id {n : ℕ} {α : typevec n} {β : Type u_1} : id ::: id = id :=
  eq_of_drop_last_eq rfl rfl

protected instance subsingleton0 : subsingleton (typevec 0) :=
  subsingleton.intro fun (a b : typevec 0) => funext fun (a_1 : fin2 0) => fin2.elim0 a_1

/-- cases distinction for 0-length type vector -/
protected def cases_nil {β : typevec 0 → Sort u_2} (f : β fin2.elim0) (v : typevec 0) : β v :=
  cast sorry f

/-- cases distinction for (n+1)-length type vector -/
protected def cases_cons (n : ℕ) {β : typevec (n + 1) → Sort u_2} (f : (t : Type u_1) → (v : typevec n) → β (v ::: t)) (v : typevec (n + 1)) : β v :=
  cast sorry (f (last v) (drop v))

protected theorem cases_nil_append1 {β : typevec 0 → Sort u_2} (f : β fin2.elim0) : typevec.cases_nil f fin2.elim0 = f :=
  rfl

protected theorem cases_cons_append1 (n : ℕ) {β : typevec (n + 1) → Sort u_2} (f : (t : Type u_1) → (v : typevec n) → β (v ::: t)) (v : typevec n) (α : Type u_1) : typevec.cases_cons n f (v ::: α) = f α v :=
  rfl

/-- cases distinction for an arrow in the category of 0-length type vectors -/
def typevec_cases_nil₃ {β : (v : typevec 0) → (v' : typevec 0) → arrow v v' → Sort u_3} (f : β fin2.elim0 fin2.elim0 nil_fun) (v : typevec 0) (v' : typevec 0) (fs : arrow v v') : β v v' fs :=
  cast sorry f

/-- cases distinction for an arrow in the category of (n+1)-length type vectors -/
def typevec_cases_cons₃ (n : ℕ) {β : (v : typevec (n + 1)) → (v' : typevec (n + 1)) → arrow v v' → Sort u_3} (F : (t : Type u_1) →
  (t' : Type u_2) →
    (f : t → t') → (v : typevec n) → (v' : typevec n) → (fs : arrow v v') → β (v ::: t) (v' ::: t') (fs ::: f)) (v : typevec (n + 1)) (v' : typevec (n + 1)) (fs : arrow v v') : β v v' fs :=
  eq.mpr sorry
    (eq.mpr sorry
      fun (fs : arrow (drop v ::: last v) (drop v' ::: last v')) =>
        eq.mpr sorry (F (last v) (last v') (last_fun fs) (drop v) (drop v') (drop_fun fs)))

/-- specialized cases distinction for an arrow in the category of 0-length type vectors -/
def typevec_cases_nil₂ {β : arrow fin2.elim0 fin2.elim0 → Sort u_3} (f : β nil_fun) : (f : arrow fin2.elim0 fin2.elim0) → β f :=
  fun (g : arrow fin2.elim0 fin2.elim0) => eq.mpr sorry f

/-- specialized cases distinction for an arrow in the category of (n+1)-length type vectors -/
def typevec_cases_cons₂ (n : ℕ) (t : Type u_1) (t' : Type u_2) (v : typevec n) (v' : typevec n) {β : arrow (v ::: t) (v' ::: t') → Sort u_3} (F : (f : t → t') → (fs : arrow v v') → β (fs ::: f)) (fs : arrow (v ::: t) (v' ::: t')) : β fs :=
  eq.mpr sorry (F (last_fun fs) (drop_fun fs))

theorem typevec_cases_nil₂_append_fun {β : arrow fin2.elim0 fin2.elim0 → Sort u_3} (f : β nil_fun) : typevec_cases_nil₂ f nil_fun = f :=
  rfl

theorem typevec_cases_cons₂_append_fun (n : ℕ) (t : Type u_1) (t' : Type u_2) (v : typevec n) (v' : typevec n) {β : arrow (v ::: t) (v' ::: t') → Sort u_3} (F : (f : t → t') → (fs : arrow v v') → β (fs ::: f)) (f : t → t') (fs : arrow v v') : typevec_cases_cons₂ n t t' v v' F (fs ::: f) = F f fs :=
  rfl

/- for lifting predicates and relations -/

/-- `pred_last α p x` predicates `p` of the last element of `x : α.append1 β`. -/
def pred_last {n : ℕ} (α : typevec n) {β : Type u_1} (p : β → Prop) {i : fin2 (n + 1)} : append1 α β i → Prop :=
  sorry

/-- `rel_last α r x y` says that `p` the last elements of `x y : α.append1 β` are related by `r` and
all the other elements are equal. -/
def rel_last {n : ℕ} (α : typevec n) {β : Type u_1} {γ : Type u_1} (r : β → γ → Prop) {i : fin2 (n + 1)} : append1 α β i → append1 α γ i → Prop :=
  sorry

/-- `repeat n t` is a `n-length` type vector that contains `n` occurences of `t` -/
def repeat (n : ℕ) (t : Type u_1) : typevec n :=
  sorry

/-- `prod α β` is the pointwise product of the components of `α` and `β` -/
def prod {n : ℕ} (α : typevec n) (β : typevec n) : typevec n :=
  sorry

/-- `const x α` is an arrow that ignores its source and constructs a `typevec` that
contains nothing but `x` -/
protected def const {β : Type u_1} (x : β) {n : ℕ} (α : typevec n) : arrow α (repeat n β) :=
  sorry

/-- vector of equality on a product of vectors -/
def repeat_eq {n : ℕ} (α : typevec n) : arrow (prod α α) (repeat n Prop) :=
  sorry

theorem const_append1 {β : Type u_1} {γ : Type u_2} (x : γ) {n : ℕ} (α : typevec n) : typevec.const x (α ::: β) = typevec.const x α ::: fun (_x : β) => x := sorry

theorem eq_nil_fun {α : typevec 0} {β : typevec 0} (f : arrow α β) : f = nil_fun := sorry

theorem id_eq_nil_fun {α : typevec 0} : id = nil_fun := sorry

theorem const_nil {β : Type u_1} (x : β) (α : typevec 0) : typevec.const x α = nil_fun := sorry

theorem repeat_eq_append1 {β : Type u_1} {n : ℕ} (α : typevec n) : repeat_eq (α ::: β) = split_fun (repeat_eq α) (function.uncurry Eq) := sorry

theorem repeat_eq_nil (α : typevec 0) : repeat_eq α = nil_fun := sorry

/-- predicate on a type vector to constrain only the last object -/
def pred_last' {n : ℕ} (α : typevec n) {β : Type u_1} (p : β → Prop) : arrow (α ::: β) (repeat (n + 1) Prop) :=
  split_fun (typevec.const True α) p

/-- predicate on the product of two type vectors to constrain only their last object -/
def rel_last' {n : ℕ} (α : typevec n) {β : Type u_1} (p : β → β → Prop) : arrow (prod (α ::: β) (α ::: β)) (repeat (n + 1) Prop) :=
  split_fun (repeat_eq α) (function.uncurry p)

/-- given `F : typevec.{u} (n+1) → Type u`, `curry F : Type u → typevec.{u} → Type u`,
i.e. its first argument can be fed in separately from the rest of the vector of arguments -/
def curry {n : ℕ} (F : typevec (n + 1) → Type u_1) (α : Type u) (β : typevec n)  :=
  F (β ::: α)

protected instance curry.inhabited {n : ℕ} (F : typevec (n + 1) → Type u_1) (α : Type u) (β : typevec n) [I : Inhabited (F (β ::: α))] : Inhabited (curry F α β) :=
  I

/-- arrow to remove one element of a `repeat` vector -/
def drop_repeat (α : Type u_1) {n : ℕ} : arrow (drop (repeat (Nat.succ n) α)) (repeat n α) :=
  sorry

/-- projection for a repeat vector -/
def of_repeat {α : Type u_1} {n : ℕ} {i : fin2 n} : repeat n α i → α :=
  sorry

theorem const_iff_true {n : ℕ} {α : typevec n} {i : fin2 n} {x : α i} {p : Prop} : of_repeat (typevec.const p α i x) ↔ p := sorry

-- variables  {F : typevec.{u} n → Type*} [mvfunctor F]

/-- left projection of a `prod` vector -/
def prod.fst {n : ℕ} {α : typevec n} {β : typevec n} : arrow (prod α β) α :=
  sorry

/-- right projection of a `prod` vector -/
def prod.snd {n : ℕ} {α : typevec n} {β : typevec n} : arrow (prod α β) β :=
  sorry

/-- introduce a product where both components are the same -/
def prod.diag {n : ℕ} {α : typevec n} : arrow α (prod α α) :=
  sorry

/-- constructor for `prod` -/
def prod.mk {n : ℕ} {α : typevec n} {β : typevec n} (i : fin2 n) : α i → β i → prod α β i :=
  sorry

@[simp] theorem prod_fst_mk {n : ℕ} {α : typevec n} {β : typevec n} (i : fin2 n) (a : α i) (b : β i) : prod.fst i (prod.mk i a b) = a := sorry

@[simp] theorem prod_snd_mk {n : ℕ} {α : typevec n} {β : typevec n} (i : fin2 n) (a : α i) (b : β i) : prod.snd i (prod.mk i a b) = b := sorry

/-- `prod` is functorial -/
protected def prod.map {n : ℕ} {α : typevec n} {α' : typevec n} {β : typevec n} {β' : typevec n} : arrow α β → arrow α' β' → arrow (prod α α') (prod β β') :=
  sorry

theorem fst_prod_mk {n : ℕ} {α : typevec n} {α' : typevec n} {β : typevec n} {β' : typevec n} (f : arrow α β) (g : arrow α' β') : comp prod.fst (prod.map f g) = comp f prod.fst := sorry

theorem snd_prod_mk {n : ℕ} {α : typevec n} {α' : typevec n} {β : typevec n} {β' : typevec n} (f : arrow α β) (g : arrow α' β') : comp prod.snd (prod.map f g) = comp g prod.snd := sorry

theorem fst_diag {n : ℕ} {α : typevec n} : comp prod.fst prod.diag = id := sorry

theorem snd_diag {n : ℕ} {α : typevec n} : comp prod.snd prod.diag = id := sorry

theorem repeat_eq_iff_eq {n : ℕ} {α : typevec n} {i : fin2 n} {x : α i} {y : α i} : of_repeat (repeat_eq α i (prod.mk i x y)) ↔ x = y := sorry

/-- given a predicate vector `p` over vector `α`, `subtype_ p` is the type of vectors
that contain an `α` that satisfies `p` -/
def subtype_ {n : ℕ} {α : typevec n} (p : arrow α (repeat n Prop)) : typevec n :=
  sorry

/-- projection on `subtype_` -/
def subtype_val {n : ℕ} {α : typevec n} (p : arrow α (repeat n Prop)) : arrow (subtype_ p) α :=
  sorry

/-- arrow that rearranges the type of `subtype_` to turn a subtype of vector into
a vector of subtypes -/
def to_subtype {n : ℕ} {α : typevec n} (p : arrow α (repeat n Prop)) : arrow (fun (i : fin2 n) => Subtype fun (x : α i) => of_repeat (p i x)) (subtype_ p) :=
  sorry

/-- arrow that rearranges the type of `subtype_` to turn a vector of subtypes
into a subtype of vector -/
def of_subtype {n : ℕ} {α : typevec n} (p : arrow α (repeat n Prop)) : arrow (subtype_ p) fun (i : fin2 n) => Subtype fun (x : α i) => of_repeat (p i x) :=
  sorry

/-- similar to `to_subtype` adapted to relations (i.e. predicate on product) -/
def to_subtype' {n : ℕ} {α : typevec n} (p : arrow (prod α α) (repeat n Prop)) : arrow (fun (i : fin2 n) => Subtype fun (x : α i × α i) => of_repeat (p i (prod.mk i (prod.fst x) (prod.snd x))))
  (subtype_ p) :=
  sorry

/-- similar to `of_subtype` adapted to relations (i.e. predicate on product) -/
def of_subtype' {n : ℕ} {α : typevec n} (p : arrow (prod α α) (repeat n Prop)) : arrow (subtype_ p)
  fun (i : fin2 n) => Subtype fun (x : α i × α i) => of_repeat (p i (prod.mk i (prod.fst x) (prod.snd x))) :=
  sorry

/-- similar to `diag` but the target vector is a `subtype_`
guaranteeing the equality of the components -/
def diag_sub {n : ℕ} {α : typevec n} : arrow α (subtype_ (repeat_eq α)) :=
  sorry

theorem subtype_val_nil {α : typevec 0} (ps : arrow α (repeat 0 Prop)) : subtype_val ps = nil_fun := sorry

theorem diag_sub_val {n : ℕ} {α : typevec n} : comp (subtype_val (repeat_eq α)) diag_sub = prod.diag := sorry

theorem prod_id {n : ℕ} {α : typevec n} {β : typevec n} : prod.map id id = id := sorry

theorem append_prod_append_fun {n : ℕ} {α : typevec n} {α' : typevec n} {β : typevec n} {β' : typevec n} {φ : Type u} {φ' : Type u} {ψ : Type u} {ψ' : Type u} {f₀ : arrow α α'} {g₀ : arrow β β'} {f₁ : φ → φ'} {g₁ : ψ → ψ'} : prod.map f₀ g₀ ::: prod.map f₁ g₁ = prod.map (f₀ ::: f₁) (g₀ ::: g₁) := sorry

@[simp] theorem drop_fun_diag {n : ℕ} {α : typevec (n + 1)} : drop_fun prod.diag = prod.diag := sorry

@[simp] theorem drop_fun_subtype_val {n : ℕ} {α : typevec (n + 1)} (p : arrow α (repeat (n + 1) Prop)) : drop_fun (subtype_val p) = subtype_val (drop_fun p) :=
  rfl

@[simp] theorem last_fun_subtype_val {n : ℕ} {α : typevec (n + 1)} (p : arrow α (repeat (n + 1) Prop)) : last_fun (subtype_val p) = subtype.val :=
  rfl

@[simp] theorem drop_fun_to_subtype {n : ℕ} {α : typevec (n + 1)} (p : arrow α (repeat (n + 1) Prop)) : drop_fun (to_subtype p) = to_subtype fun (i : fin2 n) (x : α (fin2.fs i)) => p (fin2.fs i) x := sorry

@[simp] theorem last_fun_to_subtype {n : ℕ} {α : typevec (n + 1)} (p : arrow α (repeat (n + 1) Prop)) : last_fun (to_subtype p) = id := sorry

@[simp] theorem drop_fun_of_subtype {n : ℕ} {α : typevec (n + 1)} (p : arrow α (repeat (n + 1) Prop)) : drop_fun (of_subtype p) = of_subtype (drop_fun p) := sorry

@[simp] theorem last_fun_of_subtype {n : ℕ} {α : typevec (n + 1)} (p : arrow α (repeat (n + 1) Prop)) : last_fun (of_subtype p) = id := sorry

@[simp] theorem drop_fun_rel_last {n : ℕ} {α : typevec n} {β : Type u_1} (R : β → β → Prop) : drop_fun (rel_last' α R) = repeat_eq α :=
  rfl

@[simp] theorem drop_fun_prod {n : ℕ} {α : typevec (n + 1)} {α' : typevec (n + 1)} {β : typevec (n + 1)} {β' : typevec (n + 1)} (f : arrow α β) (f' : arrow α' β') : drop_fun (prod.map f f') = prod.map (drop_fun f) (drop_fun f') := sorry

@[simp] theorem last_fun_prod {n : ℕ} {α : typevec (n + 1)} {α' : typevec (n + 1)} {β : typevec (n + 1)} {β' : typevec (n + 1)} (f : arrow α β) (f' : arrow α' β') : last_fun (prod.map f f') = prod.map (last_fun f) (last_fun f') := sorry

@[simp] theorem drop_fun_from_append1_drop_last {n : ℕ} {α : typevec (n + 1)} : drop_fun from_append1_drop_last = id :=
  rfl

@[simp] theorem last_fun_from_append1_drop_last {n : ℕ} {α : typevec (n + 1)} : last_fun from_append1_drop_last = id :=
  rfl

@[simp] theorem drop_fun_id {n : ℕ} {α : typevec (n + 1)} : drop_fun id = id :=
  rfl

@[simp] theorem prod_map_id {n : ℕ} {α : typevec n} {β : typevec n} : prod.map id id = id := sorry

@[simp] theorem subtype_val_diag_sub {n : ℕ} {α : typevec n} : comp (subtype_val (repeat_eq α)) diag_sub = prod.diag := sorry

@[simp] theorem to_subtype_of_subtype {n : ℕ} {α : typevec n} (p : arrow α (repeat n Prop)) : comp (to_subtype p) (of_subtype p) = id := sorry

@[simp] theorem subtype_val_to_subtype {n : ℕ} {α : typevec n} (p : arrow α (repeat n Prop)) : comp (subtype_val p) (to_subtype p) = fun (_x : fin2 n) => subtype.val := sorry

@[simp] theorem to_subtype_of_subtype_assoc {n : ℕ} {α : typevec n} {β : typevec n} (p : arrow α (repeat n Prop)) (f : arrow β (subtype_ p)) : comp (to_subtype p) (comp (of_subtype fun (i : fin2 n) (x : α i) => p i x) f) = f := sorry

@[simp] theorem to_subtype'_of_subtype' {n : ℕ} {α : typevec n} (r : arrow (prod α α) (repeat n Prop)) : comp (to_subtype' r) (of_subtype' r) = id := sorry

theorem subtype_val_to_subtype' {n : ℕ} {α : typevec n} (r : arrow (prod α α) (repeat n Prop)) : comp (subtype_val r) (to_subtype' r) =
  fun (i : fin2 n) (x : Subtype fun (x : α i × α i) => of_repeat (r i (prod.mk i (prod.fst x) (prod.snd x)))) =>
    prod.mk i (prod.fst (subtype.val x)) (prod.snd (subtype.val x)) := sorry

