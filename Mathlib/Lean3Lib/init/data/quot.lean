/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

Quotient types.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.data.sigma.basic
import Mathlib.Lean3Lib.init.logic
import Mathlib.Lean3Lib.init.propext
import Mathlib.Lean3Lib.init.data.setoid
 

universes u v u_a u_b u_c 

namespace Mathlib

/- We import propext here, otherwise we would need a quot.lift for propositions. -/

-- iff can now be used to do substitutions in a calculation

theorem iff_subst {a : Prop} {b : Prop} {p : Prop → Prop} (h₁ : a ↔ b) (h₂ : p a) : p b :=
  propext h₁ ▸ h₂

namespace quot


axiom sound {α : Sort u} {r : α → α → Prop} {a : α} {b : α} : r a b → Quot.mk r a = Quot.mk r bprotected theorem lift_beta {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β) (c : ∀ (a b : α), r a b → f a = f b) (a : α) : Quot.lift f c (Quot.mk r a) = f a :=
  rfl

protected theorem ind_beta {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop} (p : ∀ (a : α), β (Quot.mk r a)) (a : α) : Quot.ind p (Quot.mk r a) = p a :=
  rfl

protected def lift_on {α : Sort u} {β : Sort v} {r : α → α → Prop} (q : Quot r) (f : α → β) (c : ∀ (a b : α), r a b → f a = f b) : β :=
  Quot.lift f c q

protected theorem induction_on {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop} (q : Quot r) (h : ∀ (a : α), β (Quot.mk r a)) : β q :=
  Quot.ind h q

theorem exists_rep {α : Sort u} {r : α → α → Prop} (q : Quot r) : ∃ (a : α), Quot.mk r a = q :=
  quot.induction_on q fun (a : α) => Exists.intro a rfl

protected def indep {α : Sort u} {r : α → α → Prop} {β : Quot r → Sort v} (f : (a : α) → β (Quot.mk r a)) (a : α) : psigma β :=
  psigma.mk (Quot.mk r a) (f a)

protected theorem indep_coherent {α : Sort u} {r : α → α → Prop} {β : Quot r → Sort v} (f : (a : α) → β (Quot.mk r a)) (h : ∀ (a b : α) (p : r a b), Eq._oldrec (f a) (sound p) = f b) (a : α) (b : α) : r a b → quot.indep f a = quot.indep f b :=
  fun (e : r a b) => psigma.eq (sound e) (h a b e)

protected theorem lift_indep_pr1 {α : Sort u} {r : α → α → Prop} {β : Quot r → Sort v} (f : (a : α) → β (Quot.mk r a)) (h : ∀ (a b : α) (p : r a b), Eq._oldrec (f a) (sound p) = f b) (q : Quot r) : psigma.fst (Quot.lift (quot.indep f) (quot.indep_coherent f h) q) = q :=
  Quot.ind (fun (a : α) => Eq.refl (psigma.fst (quot.indep f a))) q

protected def rec {α : Sort u} {r : α → α → Prop} {β : Quot r → Sort v} (f : (a : α) → β (Quot.mk r a)) (h : ∀ (a b : α) (p : r a b), Eq._oldrec (f a) (sound p) = f b) (q : Quot r) : β q :=
  eq.rec_on (quot.lift_indep_pr1 f h q) (psigma.snd (Quot.lift (quot.indep f) (quot.indep_coherent f h) q))

protected def rec_on {α : Sort u} {r : α → α → Prop} {β : Quot r → Sort v} (q : Quot r) (f : (a : α) → β (Quot.mk r a)) (h : ∀ (a b : α) (p : r a b), Eq._oldrec (f a) (sound p) = f b) : β q :=
  quot.rec f h q

protected def rec_on_subsingleton {α : Sort u} {r : α → α → Prop} {β : Quot r → Sort v} [h : ∀ (a : α), subsingleton (β (Quot.mk r a))] (q : Quot r) (f : (a : α) → β (Quot.mk r a)) : β q :=
  quot.rec f sorry q

protected def hrec_on {α : Sort u} {r : α → α → Prop} {β : Quot r → Sort v} (q : Quot r) (f : (a : α) → β (Quot.mk r a)) (c : ∀ (a b : α), r a b → f a == f b) : β q :=
  quot.rec_on q f sorry

end quot


def quotient {α : Sort u} (s : setoid α) :=
  Quot setoid.r

namespace quotient


protected def mk {α : Sort u} [s : setoid α] (a : α) : quotient s :=
  Quot.mk setoid.r a

def sound {α : Sort u} [s : setoid α] {a : α} {b : α} : a ≈ b → quotient.mk a = quotient.mk b :=
  quot.sound

protected def lift {α : Sort u} {β : Sort v} [s : setoid α] (f : α → β) : (∀ (a b : α), a ≈ b → f a = f b) → quotient s → β :=
  Quot.lift f

protected theorem ind {α : Sort u} [s : setoid α] {β : quotient s → Prop} : (∀ (a : α), β (quotient.mk a)) → ∀ (q : quotient s), β q :=
  Quot.ind

protected def lift_on {α : Sort u} {β : Sort v} [s : setoid α] (q : quotient s) (f : α → β) (c : ∀ (a b : α), a ≈ b → f a = f b) : β :=
  quot.lift_on q f c

protected theorem induction_on {α : Sort u} [s : setoid α] {β : quotient s → Prop} (q : quotient s) (h : ∀ (a : α), β (quotient.mk a)) : β q :=
  quot.induction_on q h

theorem exists_rep {α : Sort u} [s : setoid α] (q : quotient s) : ∃ (a : α), quotient.mk a = q :=
  quot.exists_rep q

protected def rec {α : Sort u} [s : setoid α] {β : quotient s → Sort v} (f : (a : α) → β (quotient.mk a)) (h : ∀ (a b : α) (p : a ≈ b), Eq._oldrec (f a) (sound p) = f b) (q : quotient s) : β q :=
  quot.rec f h q

protected def rec_on {α : Sort u} [s : setoid α] {β : quotient s → Sort v} (q : quotient s) (f : (a : α) → β (quotient.mk a)) (h : ∀ (a b : α) (p : a ≈ b), Eq._oldrec (f a) (sound p) = f b) : β q :=
  quot.rec_on q f h

protected def rec_on_subsingleton {α : Sort u} [s : setoid α] {β : quotient s → Sort v} [h : ∀ (a : α), subsingleton (β (quotient.mk a))] (q : quotient s) (f : (a : α) → β (quotient.mk a)) : β q :=
  quot.rec_on_subsingleton q f

protected def hrec_on {α : Sort u} [s : setoid α] {β : quotient s → Sort v} (q : quotient s) (f : (a : α) → β (quotient.mk a)) (c : ∀ (a b : α), a ≈ b → f a == f b) : β q :=
  quot.hrec_on q f c

protected def lift₂ {α : Sort u_a} {β : Sort u_b} {φ : Sort u_c} [s₁ : setoid α] [s₂ : setoid β] (f : α → β → φ) (c : ∀ (a₁ : α) (a₂ : β) (b₁ : α) (b₂ : β), a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ = f b₁ b₂) (q₁ : quotient s₁) (q₂ : quotient s₂) : φ :=
  quotient.lift (fun (a₁ : α) => quotient.lift (f a₁) sorry q₂) sorry q₁

protected def lift_on₂ {α : Sort u_a} {β : Sort u_b} {φ : Sort u_c} [s₁ : setoid α] [s₂ : setoid β] (q₁ : quotient s₁) (q₂ : quotient s₂) (f : α → β → φ) (c : ∀ (a₁ : α) (a₂ : β) (b₁ : α) (b₂ : β), a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ = f b₁ b₂) : φ :=
  quotient.lift₂ f c q₁ q₂

protected theorem ind₂ {α : Sort u_a} {β : Sort u_b} [s₁ : setoid α] [s₂ : setoid β] {φ : quotient s₁ → quotient s₂ → Prop} (h : ∀ (a : α) (b : β), φ (quotient.mk a) (quotient.mk b)) (q₁ : quotient s₁) (q₂ : quotient s₂) : φ q₁ q₂ :=
  quotient.ind (fun (a₁ : α) => quotient.ind (fun (a₂ : β) => h a₁ a₂) q₂) q₁

protected theorem induction_on₂ {α : Sort u_a} {β : Sort u_b} [s₁ : setoid α] [s₂ : setoid β] {φ : quotient s₁ → quotient s₂ → Prop} (q₁ : quotient s₁) (q₂ : quotient s₂) (h : ∀ (a : α) (b : β), φ (quotient.mk a) (quotient.mk b)) : φ q₁ q₂ :=
  quotient.ind (fun (a₁ : α) => quotient.ind (fun (a₂ : β) => h a₁ a₂) q₂) q₁

protected theorem induction_on₃ {α : Sort u_a} {β : Sort u_b} {φ : Sort u_c} [s₁ : setoid α] [s₂ : setoid β] [s₃ : setoid φ] {δ : quotient s₁ → quotient s₂ → quotient s₃ → Prop} (q₁ : quotient s₁) (q₂ : quotient s₂) (q₃ : quotient s₃) (h : ∀ (a : α) (b : β) (c : φ), δ (quotient.mk a) (quotient.mk b) (quotient.mk c)) : δ q₁ q₂ q₃ :=
  quotient.ind (fun (a₁ : α) => quotient.ind (fun (a₂ : β) => quotient.ind (fun (a₃ : φ) => h a₁ a₂ a₃) q₃) q₂) q₁

theorem exact {α : Sort u} [s : setoid α] {a : α} {b : α} : quotient.mk a = quotient.mk b → a ≈ b :=
  fun (h : quotient.mk a = quotient.mk b) => eq_imp_rel h

protected def rec_on_subsingleton₂ {α : Sort u_a} {β : Sort u_b} [s₁ : setoid α] [s₂ : setoid β] {φ : quotient s₁ → quotient s₂ → Sort u_c} [h : ∀ (a : α) (b : β), subsingleton (φ (quotient.mk a) (quotient.mk b))] (q₁ : quotient s₁) (q₂ : quotient s₂) (f : (a : α) → (b : β) → φ (quotient.mk a) (quotient.mk b)) : φ q₁ q₂ :=
  quotient.rec_on_subsingleton q₁ fun (a : α) => quotient.rec_on_subsingleton q₂ fun (b : β) => f a b

end quotient


inductive eqv_gen {α : Type u} (r : α → α → Prop) : α → α → Prop
where
| rel : ∀ (x y : α), r x y → eqv_gen r x y
| refl : ∀ (x : α), eqv_gen r x x
| symm : ∀ (x y : α), eqv_gen r x y → eqv_gen r y x
| trans : ∀ (x y z : α), eqv_gen r x y → eqv_gen r y z → eqv_gen r x z

theorem eqv_gen.is_equivalence {α : Type u} (r : α → α → Prop) : equivalence (eqv_gen r) :=
  mk_equivalence (eqv_gen r) eqv_gen.refl eqv_gen.symm eqv_gen.trans

def eqv_gen.setoid {α : Type u} (r : α → α → Prop) : setoid α :=
  setoid.mk (eqv_gen r) (eqv_gen.is_equivalence r)

theorem quot.exact {α : Type u} (r : α → α → Prop) {a : α} {b : α} (H : Quot.mk r a = Quot.mk r b) : eqv_gen r a b :=
  quotient.exact (congr_arg (Quot.lift quotient.mk fun (x y : α) (h : r x y) => quot.sound (eqv_gen.rel x y h)) H)

theorem quot.eqv_gen_sound {α : Type u} {r : α → α → Prop} {a : α} {b : α} (H : eqv_gen r a b) : Quot.mk r a = Quot.mk r b := sorry

protected instance quotient.decidable_eq {α : Sort u} {s : setoid α} [d : (a b : α) → Decidable (a ≈ b)] : DecidableEq (quotient s) :=
  fun (q₁ q₂ : quotient s) => quotient.rec_on_subsingleton₂ q₁ q₂ fun (a₁ a₂ : α) => sorry

