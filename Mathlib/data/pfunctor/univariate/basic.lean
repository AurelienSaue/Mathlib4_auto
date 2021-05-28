/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.W
import Mathlib.PostPort

universes u l u_1 u_2 u_3 

namespace Mathlib

/-!
# Polynomial functors

This file defines polynomial functors and the W-type construction as a
polynomial functor.  (For the M-type construction, see
pfunctor/M.lean.)
-/

/--
A polynomial functor `P` is given by a type `A` and a family `B` of types over `A`. `P` maps
any type `α` to a new type `P.obj α`, which is defined as the sigma type `Σ x, P.B x → α`.

An element of `P.obj α` is a pair `⟨a, f⟩`, where `a` is an element of a type `A` and
`f : B a → α`. Think of `a` as the shape of the object and `f` as an index to the relevant
elements of `α`.
-/
structure pfunctor 
where
  A : Type u
  B : A → Type u

namespace pfunctor


protected instance inhabited : Inhabited pfunctor :=
  { default := mk Inhabited.default Inhabited.default }

/-- Applying `P` to an object of `Type` -/
def obj (P : pfunctor) (α : Type u_2)  :=
  sigma fun (x : A P) => B P x → α

/-- Applying `P` to a morphism of `Type` -/
def map (P : pfunctor) {α : Type u_2} {β : Type u_3} (f : α → β) : obj P α → obj P β :=
  fun (_x : obj P α) => sorry

protected instance obj.inhabited (P : pfunctor) {α : Type u} [Inhabited (A P)] [Inhabited α] : Inhabited (obj P α) :=
  { default := sigma.mk Inhabited.default fun (_x : B P Inhabited.default) => Inhabited.default }

protected instance obj.functor (P : pfunctor) : Functor (obj P) :=
  { map := map P, mapConst := fun (α β : Type u_2) => map P ∘ function.const β }

protected theorem map_eq (P : pfunctor) {α : Type u_2} {β : Type u_2} (f : α → β) (a : A P) (g : B P a → α) : f <$> sigma.mk a g = sigma.mk a (f ∘ g) :=
  rfl

protected theorem id_map (P : pfunctor) {α : Type u_2} (x : obj P α) : id <$> x = id x := sorry

protected theorem comp_map (P : pfunctor) {α : Type u_2} {β : Type u_2} {γ : Type u_2} (f : α → β) (g : β → γ) (x : obj P α) : (g ∘ f) <$> x = g <$> f <$> x := sorry

protected instance obj.is_lawful_functor (P : pfunctor) : is_lawful_functor (obj P) :=
  is_lawful_functor.mk (pfunctor.id_map P) (pfunctor.comp_map P)

/-- re-export existing definition of W-types and
adapt it to a packaged definition of polynomial functor -/
def W (P : pfunctor)  :=
  W_type (B P)

/- inhabitants of W types is awkward to encode as an instance
assumption because there needs to be a value `a : P.A`
such that `P.B a` is empty to yield a finite tree -/

/-- root element  of a W tree -/
def W.head {P : pfunctor} : W P → A P :=
  sorry

/-- children of the root of a W tree -/
def W.children {P : pfunctor} (x : W P) : B P (W.head x) → W P :=
  sorry

/-- destructor for W-types -/
def W.dest {P : pfunctor} : W P → obj P (W P) :=
  sorry

/-- constructor for W-types -/
def W.mk {P : pfunctor} : obj P (W P) → W P :=
  sorry

@[simp] theorem W.dest_mk {P : pfunctor} (p : obj P (W P)) : W.dest (W.mk p) = p :=
  sigma.cases_on p fun (p_fst : A P) (p_snd : B P p_fst → W P) => Eq.refl (W.dest (W.mk (sigma.mk p_fst p_snd)))

@[simp] theorem W.mk_dest {P : pfunctor} (p : W P) : W.mk (W.dest p) = p :=
  W_type.cases_on p fun (p_a : A P) (p_f : B P p_a → W_type (B P)) => Eq.refl (W.mk (W.dest (W_type.mk p_a p_f)))

/-- `Idx` identifies a location inside the application of a pfunctor.
For `F : pfunctor`, `x : F.obj α` and `i : F.Idx`, `i` can designate
one part of `x` or is invalid, if `i.1 ≠ x.1` -/
def Idx (P : pfunctor)  :=
  sigma fun (x : A P) => B P x

protected instance Idx.inhabited (P : pfunctor) [Inhabited (A P)] [Inhabited (B P Inhabited.default)] : Inhabited (Idx P) :=
  { default := sigma.mk Inhabited.default Inhabited.default }

/-- `x.iget i` takes the component of `x` designated by `i` if any is or returns
a default value -/
def obj.iget {P : pfunctor} [DecidableEq (A P)] {α : Type u_2} [Inhabited α] (x : obj P α) (i : Idx P) : α :=
  dite (sigma.fst i = sigma.fst x) (fun (h : sigma.fst i = sigma.fst x) => sigma.snd x (cast sorry (sigma.snd i)))
    fun (h : ¬sigma.fst i = sigma.fst x) => Inhabited.default

@[simp] theorem fst_map {P : pfunctor} {α : Type u} {β : Type u} (x : obj P α) (f : α → β) : sigma.fst (f <$> x) = sigma.fst x :=
  sigma.cases_on x fun (x_fst : A P) (x_snd : B P x_fst → α) => Eq.refl (sigma.fst (f <$> sigma.mk x_fst x_snd))

@[simp] theorem iget_map {P : pfunctor} [DecidableEq (A P)] {α : Type u} {β : Type u} [Inhabited α] [Inhabited β] (x : obj P α) (f : α → β) (i : Idx P) (h : sigma.fst i = sigma.fst x) : obj.iget (f <$> x) i = f (obj.iget x i) := sorry

end pfunctor


/-
Composition of polynomial functors.
-/

namespace pfunctor


/-- functor composition for polynomial functors -/
def comp (P₂ : pfunctor) (P₁ : pfunctor) : pfunctor :=
  mk (sigma fun (a₂ : A P₂) => B P₂ a₂ → A P₁)
    fun (a₂a₁ : sigma fun (a₂ : A P₂) => B P₂ a₂ → A P₁) =>
      sigma fun (u : B P₂ (sigma.fst a₂a₁)) => B P₁ (sigma.snd a₂a₁ u)

/-- constructor for composition -/
def comp.mk (P₂ : pfunctor) (P₁ : pfunctor) {α : Type} (x : obj P₂ (obj P₁ α)) : obj (comp P₂ P₁) α :=
  sigma.mk (sigma.mk (sigma.fst x) (sigma.fst ∘ sigma.snd x))
    fun (a₂a₁ : B (comp P₂ P₁) (sigma.mk (sigma.fst x) (sigma.fst ∘ sigma.snd x))) =>
      sigma.snd (sigma.snd x (sigma.fst a₂a₁)) (sigma.snd a₂a₁)

/-- destructor for composition -/
def comp.get (P₂ : pfunctor) (P₁ : pfunctor) {α : Type} (x : obj (comp P₂ P₁) α) : obj P₂ (obj P₁ α) :=
  sigma.mk (sigma.fst (sigma.fst x))
    fun (a₂ : B P₂ (sigma.fst (sigma.fst x))) =>
      sigma.mk (sigma.snd (sigma.fst x) a₂) fun (a₁ : B P₁ (sigma.snd (sigma.fst x) a₂)) => sigma.snd x (sigma.mk a₂ a₁)

end pfunctor


/-
Lifting predicates and relations.
-/

namespace pfunctor


theorem liftp_iff {P : pfunctor} {α : Type u} (p : α → Prop) (x : obj P α) : functor.liftp p x ↔ ∃ (a : A P), ∃ (f : B P a → α), x = sigma.mk a f ∧ ∀ (i : B P a), p (f i) := sorry

theorem liftp_iff' {P : pfunctor} {α : Type u} (p : α → Prop) (a : A P) (f : B P a → α) : functor.liftp p (sigma.mk a f) ↔ ∀ (i : B P a), p (f i) := sorry

theorem liftr_iff {P : pfunctor} {α : Type u} (r : α → α → Prop) (x : obj P α) (y : obj P α) : functor.liftr r x y ↔
  ∃ (a : A P),
    ∃ (f₀ : B P a → α), ∃ (f₁ : B P a → α), x = sigma.mk a f₀ ∧ y = sigma.mk a f₁ ∧ ∀ (i : B P a), r (f₀ i) (f₁ i) := sorry

theorem supp_eq {P : pfunctor} {α : Type u} (a : A P) (f : B P a → α) : functor.supp (sigma.mk a f) = f '' set.univ := sorry

