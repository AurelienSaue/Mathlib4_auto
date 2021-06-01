/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.logic.relator
import Mathlib.PostPort

universes u_1 u_2 u_3 u_4 u 

namespace Mathlib

/-!
# Quotient types

This module extends the core library's treatment of quotient types (`init.data.quot`).

## Tags

quotient
-/

namespace setoid


theorem ext {α : Sort u_1} {s : setoid α} {t : setoid α} : (∀ (a b : α), r a b ↔ r a b) → s = t :=
  sorry

end setoid


namespace quot


protected instance inhabited {α : Sort u_1} {ra : α → α → Prop} [Inhabited α] :
    Inhabited (Quot ra) :=
  { default := Quot.mk ra Inhabited.default }

/-- Recursion on two `quotient` arguments `a` and `b`, result type depends on `⟦a⟧` and `⟦b⟧`. -/
protected def hrec_on₂ {α : Sort u_1} {β : Sort u_2} {ra : α → α → Prop} {rb : β → β → Prop}
    {φ : Quot ra → Quot rb → Sort u_3} (qa : Quot ra) (qb : Quot rb)
    (f : (a : α) → (b : β) → φ (Quot.mk ra a) (Quot.mk rb b))
    (ca : ∀ {b : β} {a₁ a₂ : α}, ra a₁ a₂ → f a₁ b == f a₂ b)
    (cb : ∀ {a : α} {b₁ b₂ : β}, rb b₁ b₂ → f a b₁ == f a b₂) : φ qa qb :=
  quot.hrec_on qa (fun (a : α) => quot.hrec_on qb (f a) sorry) sorry

/-- Map a function `f : α → β` such that `ra x y` implies `rb (f x) (f y)`
to a map `quot ra → quot rb`. -/
protected def map {α : Sort u_1} {β : Sort u_2} {ra : α → α → Prop} {rb : β → β → Prop} (f : α → β)
    (h : relator.lift_fun ra rb f f) : Quot ra → Quot rb :=
  Quot.lift (fun (x : α) => Quot.mk rb (f x)) sorry

/-- If `ra` is a subrelation of `ra'`, then we have a natural map `quot ra → quot ra'`. -/
protected def map_right {α : Sort u_1} {ra : α → α → Prop} {ra' : α → α → Prop}
    (h : ∀ (a₁ a₂ : α), ra a₁ a₂ → ra' a₁ a₂) : Quot ra → Quot ra' :=
  quot.map id h

/-- weaken the relation of a quotient -/
def factor {α : Type u_1} (r : α → α → Prop) (s : α → α → Prop) (h : ∀ (x y : α), r x y → s x y) :
    Quot r → Quot s :=
  Quot.lift (Quot.mk s) sorry

theorem factor_mk_eq {α : Type u_1} (r : α → α → Prop) (s : α → α → Prop)
    (h : ∀ (x y : α), r x y → s x y) : factor r s h ∘ Quot.mk r = Quot.mk s :=
  rfl

/-- Descends a function `f : α → β → γ` to quotients of `α` and `β`. -/
protected def lift₂ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_4} {r : α → α → Prop}
    {s : β → β → Prop} (f : α → β → γ) (hr : ∀ (a : α) (b₁ b₂ : β), s b₁ b₂ → f a b₁ = f a b₂)
    (hs : ∀ (a₁ a₂ : α) (b : β), r a₁ a₂ → f a₁ b = f a₂ b) (q₁ : Quot r) (q₂ : Quot s) : γ :=
  Quot.lift (fun (a : α) => Quot.lift (f a) (hr a)) sorry q₁ q₂

@[simp] theorem lift₂_mk {α : Sort u_1} {β : Sort u_2} {γ : Sort u_4} {r : α → α → Prop}
    {s : β → β → Prop} (a : α) (b : β) (f : α → β → γ)
    (hr : ∀ (a : α) (b₁ b₂ : β), s b₁ b₂ → f a b₁ = f a b₂)
    (hs : ∀ (a₁ a₂ : α) (b : β), r a₁ a₂ → f a₁ b = f a₂ b) :
    quot.lift₂ f hr hs (Quot.mk r a) (Quot.mk s b) = f a b :=
  rfl

/-- Descends a function `f : α → β → γ` to quotients of `α` and `β` and applies it. -/
protected def lift_on₂ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_4} {r : α → α → Prop}
    {s : β → β → Prop} (p : Quot r) (q : Quot s) (f : α → β → γ)
    (hr : ∀ (a : α) (b₁ b₂ : β), s b₁ b₂ → f a b₁ = f a b₂)
    (hs : ∀ (a₁ a₂ : α) (b : β), r a₁ a₂ → f a₁ b = f a₂ b) : γ :=
  quot.lift₂ f hr hs p q

@[simp] theorem lift_on₂_mk {α : Sort u_1} {β : Sort u_2} {γ : Sort u_4} {r : α → α → Prop}
    {s : β → β → Prop} (a : α) (b : β) (f : α → β → γ)
    (hr : ∀ (a : α) (b₁ b₂ : β), s b₁ b₂ → f a b₁ = f a b₂)
    (hs : ∀ (a₁ a₂ : α) (b : β), r a₁ a₂ → f a₁ b = f a₂ b) :
    quot.lift_on₂ (Quot.mk r a) (Quot.mk s b) f hr hs = f a b :=
  rfl

/-- Descends a function `f : α → β → γ` to quotients of `α` and `β` wih values in a quotient of
`γ`. -/
protected def map₂ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_4} {r : α → α → Prop}
    {s : β → β → Prop} {t : γ → γ → Prop} (f : α → β → γ)
    (hr : ∀ (a : α) (b₁ b₂ : β), s b₁ b₂ → t (f a b₁) (f a b₂))
    (hs : ∀ (a₁ a₂ : α) (b : β), r a₁ a₂ → t (f a₁ b) (f a₂ b)) (q₁ : Quot r) (q₂ : Quot s) :
    Quot t :=
  quot.lift₂ (fun (a : α) (b : β) => Quot.mk t (f a b)) sorry sorry q₁ q₂

@[simp] theorem map₂_mk {α : Sort u_1} {β : Sort u_2} {γ : Sort u_4} {r : α → α → Prop}
    {s : β → β → Prop} {t : γ → γ → Prop} (f : α → β → γ)
    (hr : ∀ (a : α) (b₁ b₂ : β), s b₁ b₂ → t (f a b₁) (f a b₂))
    (hs : ∀ (a₁ a₂ : α) (b : β), r a₁ a₂ → t (f a₁ b) (f a₂ b)) (a : α) (b : β) :
    quot.map₂ f hr hs (Quot.mk r a) (Quot.mk s b) = Quot.mk t (f a b) :=
  rfl

protected theorem induction_on₂ {α : Sort u_1} {β : Sort u_2} {r : α → α → Prop} {s : β → β → Prop}
    {δ : Quot r → Quot s → Prop} (q₁ : Quot r) (q₂ : Quot s)
    (h : ∀ (a : α) (b : β), δ (Quot.mk r a) (Quot.mk s b)) : δ q₁ q₂ :=
  Quot.ind (fun (a₁ : α) => Quot.ind (fun (a₂ : β) => h a₁ a₂) q₂) q₁

protected theorem induction_on₃ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_4} {r : α → α → Prop}
    {s : β → β → Prop} {t : γ → γ → Prop} {δ : Quot r → Quot s → Quot t → Prop} (q₁ : Quot r)
    (q₂ : Quot s) (q₃ : Quot t)
    (h : ∀ (a : α) (b : β) (c : γ), δ (Quot.mk r a) (Quot.mk s b) (Quot.mk t c)) : δ q₁ q₂ q₃ :=
  Quot.ind (fun (a₁ : α) => Quot.ind (fun (a₂ : β) => Quot.ind (fun (a₃ : γ) => h a₁ a₂ a₃) q₃) q₂)
    q₁

end quot


namespace quotient


protected instance inhabited {α : Sort u_1} [sa : setoid α] [Inhabited α] :
    Inhabited (quotient sa) :=
  { default := quotient.mk Inhabited.default }

/-- Induction on two `quotient` arguments `a` and `b`, result type depends on `⟦a⟧` and `⟦b⟧`. -/
protected def hrec_on₂ {α : Sort u_1} {β : Sort u_2} [sa : setoid α] [sb : setoid β]
    {φ : quotient sa → quotient sb → Sort u_3} (qa : quotient sa) (qb : quotient sb)
    (f : (a : α) → (b : β) → φ (quotient.mk a) (quotient.mk b))
    (c : ∀ (a₁ : α) (b₁ : β) (a₂ : α) (b₂ : β), a₁ ≈ a₂ → b₁ ≈ b₂ → f a₁ b₁ == f a₂ b₂) : φ qa qb :=
  quot.hrec_on₂ qa qb f sorry sorry

/-- Map a function `f : α → β` that sends equivalent elements to equivalent elements
to a function `quotient sa → quotient sb`. Useful to define unary operations on quotients. -/
protected def map {α : Sort u_1} {β : Sort u_2} [sa : setoid α] [sb : setoid β] (f : α → β)
    (h : relator.lift_fun has_equiv.equiv has_equiv.equiv f f) : quotient sa → quotient sb :=
  quot.map f h

@[simp] theorem map_mk {α : Sort u_1} {β : Sort u_2} [sa : setoid α] [sb : setoid β] (f : α → β)
    (h : relator.lift_fun has_equiv.equiv has_equiv.equiv f f) (x : α) :
    quotient.map f h (quotient.mk x) = quotient.mk (f x) :=
  rfl

/-- Map a function `f : α → β → γ` that sends equivalent elements to equivalent elements
to a function `f : quotient sa → quotient sb → quotient sc`.
Useful to define binary operations on quotients. -/
protected def map₂ {α : Sort u_1} {β : Sort u_2} [sa : setoid α] [sb : setoid β] {γ : Sort u_4}
    [sc : setoid γ] (f : α → β → γ)
    (h : relator.lift_fun has_equiv.equiv (has_equiv.equiv ⇒ has_equiv.equiv) f f) :
    quotient sa → quotient sb → quotient sc :=
  quotient.lift₂ (fun (x : α) (y : β) => quotient.mk (f x y)) sorry

end quotient


theorem quot.eq {α : Type u_1} {r : α → α → Prop} {x : α} {y : α} :
    Quot.mk r x = Quot.mk r y ↔ eqv_gen r x y :=
  { mp := quot.exact r, mpr := quot.eqv_gen_sound }

@[simp] theorem quotient.eq {α : Sort u_1} [r : setoid α] {x : α} {y : α} :
    quotient.mk x = quotient.mk y ↔ x ≈ y :=
  { mp := quotient.exact, mpr := quotient.sound }

theorem forall_quotient_iff {α : Type u_1} [r : setoid α] {p : quotient r → Prop} :
    (∀ (a : quotient r), p a) ↔ ∀ (a : α), p (quotient.mk a) :=
  { mp := fun (h : ∀ (a : quotient r), p a) (x : α) => h (quotient.mk x),
    mpr := fun (h : ∀ (a : α), p (quotient.mk a)) (a : quotient r) => quotient.induction_on a h }

@[simp] theorem quotient.lift_beta {α : Sort u_1} {β : Sort u_2} [s : setoid α] (f : α → β)
    (h : ∀ (a b : α), a ≈ b → f a = f b) (x : α) : quotient.lift f h (quotient.mk x) = f x :=
  rfl

@[simp] theorem quotient.lift_on_beta {α : Sort u_1} {β : Sort u_2} [s : setoid α] (f : α → β)
    (h : ∀ (a b : α), a ≈ b → f a = f b) (x : α) : quotient.lift_on (quotient.mk x) f h = f x :=
  rfl

@[simp] theorem quotient.lift_on_beta₂ {α : Sort u_1} {β : Sort u_2} [setoid α] (f : α → α → β)
    (h : ∀ (a₁ a₂ b₁ b₂ : α), a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ = f b₁ b₂) (x : α) (y : α) :
    quotient.lift_on₂ (quotient.mk x) (quotient.mk y) f h = f x y :=
  rfl

/-- `quot.mk r` is a surjective function. -/
theorem surjective_quot_mk {α : Sort u_1} (r : α → α → Prop) : function.surjective (Quot.mk r) :=
  quot.exists_rep

/-- `quotient.mk` is a surjective function. -/
theorem surjective_quotient_mk (α : Sort u_1) [s : setoid α] : function.surjective quotient.mk :=
  quot.exists_rep

/-- Choose an element of the equivalence class using the axiom of choice.
  Sound but noncomputable. -/
def quot.out {α : Sort u_1} {r : α → α → Prop} (q : Quot r) : α :=
  classical.some (quot.exists_rep q)

/-- Unwrap the VM representation of a quotient to obtain an element of the equivalence class.
  Computable but unsound. -/
@[simp] theorem quot.out_eq {α : Sort u_1} {r : α → α → Prop} (q : Quot r) :
    Quot.mk r (quot.out q) = q :=
  classical.some_spec (quot.exists_rep q)

/-- Choose an element of the equivalence class using the axiom of choice.
  Sound but noncomputable. -/
def quotient.out {α : Sort u_1} [s : setoid α] : quotient s → α := quot.out

@[simp] theorem quotient.out_eq {α : Sort u_1} [s : setoid α] (q : quotient s) :
    quotient.mk (quotient.out q) = q :=
  quot.out_eq q

theorem quotient.mk_out {α : Sort u_1} [s : setoid α] (a : α) : quotient.out (quotient.mk a) ≈ a :=
  quotient.exact (quotient.out_eq (quotient.mk a))

protected instance pi_setoid {ι : Sort u_1} {α : ι → Sort u_2} [(i : ι) → setoid (α i)] :
    setoid ((i : ι) → α i) :=
  setoid.mk (fun (a b : (i : ι) → α i) => ∀ (i : ι), a i ≈ b i) sorry

/-- Given a function `f : Π i, quotient (S i)`, returns the class of functions `Π i, α i` sending
each `i` to an element of the class `f i`. -/
def quotient.choice {ι : Type u_1} {α : ι → Type u_2} [S : (i : ι) → setoid (α i)]
    (f : (i : ι) → quotient (S i)) : quotient Mathlib.pi_setoid :=
  quotient.mk fun (i : ι) => quotient.out (f i)

theorem quotient.choice_eq {ι : Type u_1} {α : ι → Type u_2} [(i : ι) → setoid (α i)]
    (f : (i : ι) → α i) : (quotient.choice fun (i : ι) => quotient.mk (f i)) = quotient.mk f :=
  quotient.sound fun (i : ι) => quotient.mk_out (f i)

theorem nonempty_quotient_iff {α : Sort u_1} (s : setoid α) : Nonempty (quotient s) ↔ Nonempty α :=
  sorry

/-- `trunc α` is the quotient of `α` by the always-true relation. This
  is related to the propositional truncation in HoTT, and is similar
  in effect to `nonempty α`, but unlike `nonempty α`, `trunc α` is data,
  so the VM representation is the same as `α`, and so this can be used to
  maintain computability. -/
def trunc (α : Sort u) := Quot fun (_x _x : α) => True

theorem true_equivalence {α : Sort u_1} : equivalence fun (_x _x : α) => True :=
  { left := fun (_x : α) => trivial,
    right :=
      { left := fun (_x _x : α) (_x : True) => trivial,
        right := fun (_x _x _x : α) (_x _x : True) => trivial } }

namespace trunc


/-- Constructor for `trunc α` -/
def mk {α : Sort u_1} (a : α) : trunc α := Quot.mk (fun (_x _x : α) => True) a

protected instance inhabited {α : Sort u_1} [Inhabited α] : Inhabited (trunc α) :=
  { default := mk Inhabited.default }

/-- Any constant function lifts to a function out of the truncation -/
def lift {α : Sort u_1} {β : Sort u_2} (f : α → β) (c : ∀ (a b : α), f a = f b) : trunc α → β :=
  Quot.lift f sorry

theorem ind {α : Sort u_1} {β : trunc α → Prop} : (∀ (a : α), β (mk a)) → ∀ (q : trunc α), β q :=
  Quot.ind

protected theorem lift_beta {α : Sort u_1} {β : Sort u_2} (f : α → β) (c : ∀ (a b : α), f a = f b)
    (a : α) : lift f c (mk a) = f a :=
  rfl

/-- Lift a constant function on `q : trunc α`. -/
protected def lift_on {α : Sort u_1} {β : Sort u_2} (q : trunc α) (f : α → β)
    (c : ∀ (a b : α), f a = f b) : β :=
  lift f c q

protected theorem induction_on {α : Sort u_1} {β : trunc α → Prop} (q : trunc α)
    (h : ∀ (a : α), β (mk a)) : β q :=
  ind h q

theorem exists_rep {α : Sort u_1} (q : trunc α) : ∃ (a : α), mk a = q := quot.exists_rep q

protected theorem induction_on₂ {α : Sort u_1} {β : Sort u_2} {C : trunc α → trunc β → Prop}
    (q₁ : trunc α) (q₂ : trunc β) (h : ∀ (a : α) (b : β), C (mk a) (mk b)) : C q₁ q₂ :=
  trunc.induction_on q₁ fun (a₁ : α) => trunc.induction_on q₂ (h a₁)

protected theorem eq {α : Sort u_1} (a : trunc α) (b : trunc α) : a = b :=
  trunc.induction_on₂ a b fun (x y : α) => quot.sound trivial

protected instance subsingleton {α : Sort u_1} : subsingleton (trunc α) :=
  subsingleton.intro trunc.eq

/-- The `bind` operator for the `trunc` monad. -/
def bind {α : Sort u_1} {β : Sort u_2} (q : trunc α) (f : α → trunc β) : trunc β :=
  trunc.lift_on q f sorry

/-- A function `f : α → β` defines a function `map f : trunc α → trunc β`. -/
def map {α : Sort u_1} {β : Sort u_2} (f : α → β) (q : trunc α) : trunc β := bind q (mk ∘ f)

protected instance monad : Monad trunc := sorry

protected instance is_lawful_monad : is_lawful_monad trunc :=
  is_lawful_monad.mk (fun (α β : Type u_1) (q : α) (f : α → trunc β) => rfl)
    fun (α β γ : Type u_1) (x : trunc α) (f : α → trunc β) (g : β → trunc γ) =>
      trunc.eq (x >>= f >>= g) (x >>= fun (x : α) => f x >>= g)

/-- Recursion/induction principle for `trunc`. -/
protected def rec {α : Sort u_1} {C : trunc α → Sort u_3} (f : (a : α) → C (mk a))
    (h : ∀ (a b : α), Eq._oldrec (f a) (rec._proof_1 a b) = f b) (q : trunc α) : C q :=
  quot.rec f sorry q

/-- A version of `trunc.rec` taking `q : trunc α` as the first argument. -/
protected def rec_on {α : Sort u_1} {C : trunc α → Sort u_3} (q : trunc α) (f : (a : α) → C (mk a))
    (h : ∀ (a b : α), Eq._oldrec (f a) (rec_on._proof_1 a b) = f b) : C q :=
  trunc.rec f h q

/-- A version of `trunc.rec_on` assuming the codomain is a `subsingleton`. -/
protected def rec_on_subsingleton {α : Sort u_1} {C : trunc α → Sort u_3}
    [∀ (a : α), subsingleton (C (mk a))] (q : trunc α) (f : (a : α) → C (mk a)) : C q :=
  trunc.rec f sorry q

/-- Noncomputably extract a representative of `trunc α` (using the axiom of choice). -/
def out {α : Sort u_1} : trunc α → α := quot.out

@[simp] theorem out_eq {α : Sort u_1} (q : trunc α) : mk (out q) = q := trunc.eq (mk (out q)) q

end trunc


theorem nonempty_of_trunc {α : Sort u_1} (q : trunc α) : Nonempty α :=
  (fun (_a : ∃ (a : α), trunc.mk a = q) =>
      Exists.dcases_on _a fun (w : α) (h : trunc.mk w = q) => idRhs (Nonempty α) (Nonempty.intro w))
    (trunc.exists_rep q)

namespace quotient


/- Versions of quotient definitions and lemmas ending in `'` use unification instead
of typeclass inference for inferring the `setoid` argument. This is useful when there are
several different quotient relations on a type, for example quotient groups, rings and modules -/

/-- A version of `quotient.mk` taking `{s : setoid α}` as an implicit argument instead of an
instance argument. -/
protected def mk' {α : Sort u_1} {s₁ : setoid α} (a : α) : quotient s₁ := Quot.mk setoid.r a

/-- `quotient.mk'` is a surjective function. -/
theorem surjective_quotient_mk' {α : Sort u_1} {s₁ : setoid α} : function.surjective quotient.mk' :=
  quot.exists_rep

/-- A version of `quotient.lift_on` taking `{s : setoid α}` as an implicit argument instead of an
instance argument. -/
protected def lift_on' {α : Sort u_1} {φ : Sort u_4} {s₁ : setoid α} (q : quotient s₁) (f : α → φ)
    (h : ∀ (a b : α), setoid.r a b → f a = f b) : φ :=
  quotient.lift_on q f h

@[simp] protected theorem lift_on'_beta {α : Sort u_1} {φ : Sort u_4} {s₁ : setoid α} (f : α → φ)
    (h : ∀ (a b : α), setoid.r a b → f a = f b) (x : α) :
    quotient.lift_on' (quotient.mk' x) f h = f x :=
  rfl

/-- A version of `quotient.lift_on₂` taking `{s₁ : setoid α} {s₂ : setoid β}` as implicit arguments
instead of instance arguments. -/
protected def lift_on₂' {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} {s₁ : setoid α} {s₂ : setoid β}
    (q₁ : quotient s₁) (q₂ : quotient s₂) (f : α → β → γ)
    (h :
      ∀ (a₁ : α) (a₂ : β) (b₁ : α) (b₂ : β), setoid.r a₁ b₁ → setoid.r a₂ b₂ → f a₁ a₂ = f b₁ b₂) :
    γ :=
  quotient.lift_on₂ q₁ q₂ f h

@[simp] protected theorem lift_on₂'_beta {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
    {s₁ : setoid α} {s₂ : setoid β} (f : α → β → γ)
    (h : ∀ (a₁ : α) (a₂ : β) (b₁ : α) (b₂ : β), setoid.r a₁ b₁ → setoid.r a₂ b₂ → f a₁ a₂ = f b₁ b₂)
    (a : α) (b : β) : quotient.lift_on₂' (quotient.mk' a) (quotient.mk' b) f h = f a b :=
  rfl

/-- A version of `quotient.ind` taking `{s : setoid α}` as an implicit argument instead of an
instance argument. -/
protected theorem ind' {α : Sort u_1} {s₁ : setoid α} {p : quotient s₁ → Prop}
    (h : ∀ (a : α), p (quotient.mk' a)) (q : quotient s₁) : p q :=
  quotient.ind h q

/-- A version of `quotient.ind₂` taking `{s₁ : setoid α} {s₂ : setoid β}` as implicit arguments
instead of instance arguments. -/
protected theorem ind₂' {α : Sort u_1} {β : Sort u_2} {s₁ : setoid α} {s₂ : setoid β}
    {p : quotient s₁ → quotient s₂ → Prop}
    (h : ∀ (a₁ : α) (a₂ : β), p (quotient.mk' a₁) (quotient.mk' a₂)) (q₁ : quotient s₁)
    (q₂ : quotient s₂) : p q₁ q₂ :=
  quotient.ind₂ h q₁ q₂

/-- A version of `quotient.induction_on` taking `{s : setoid α}` as an implicit argument instead
of an instance argument. -/
protected theorem induction_on' {α : Sort u_1} {s₁ : setoid α} {p : quotient s₁ → Prop}
    (q : quotient s₁) (h : ∀ (a : α), p (quotient.mk' a)) : p q :=
  quotient.induction_on q h

/-- A version of `quotient.induction_on₂` taking `{s₁ : setoid α} {s₂ : setoid β}` as implicit
arguments instead of instance arguments. -/
protected theorem induction_on₂' {α : Sort u_1} {β : Sort u_2} {s₁ : setoid α} {s₂ : setoid β}
    {p : quotient s₁ → quotient s₂ → Prop} (q₁ : quotient s₁) (q₂ : quotient s₂)
    (h : ∀ (a₁ : α) (a₂ : β), p (quotient.mk' a₁) (quotient.mk' a₂)) : p q₁ q₂ :=
  quotient.induction_on₂ q₁ q₂ h

/-- A version of `quotient.induction_on₃` taking `{s₁ : setoid α} {s₂ : setoid β} {s₃ : setoid γ}`
as implicit arguments instead of instance arguments. -/
protected theorem induction_on₃' {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} {s₁ : setoid α}
    {s₂ : setoid β} {s₃ : setoid γ} {p : quotient s₁ → quotient s₂ → quotient s₃ → Prop}
    (q₁ : quotient s₁) (q₂ : quotient s₂) (q₃ : quotient s₃)
    (h : ∀ (a₁ : α) (a₂ : β) (a₃ : γ), p (quotient.mk' a₁) (quotient.mk' a₂) (quotient.mk' a₃)) :
    p q₁ q₂ q₃ :=
  quotient.induction_on₃ q₁ q₂ q₃ h

/-- Recursion on a `quotient` argument `a`, result type depends on `⟦a⟧`. -/
protected def hrec_on' {α : Sort u_1} {s₁ : setoid α} {φ : quotient s₁ → Sort u_2}
    (qa : quotient s₁) (f : (a : α) → φ (quotient.mk' a))
    (c : ∀ (a₁ a₂ : α), a₁ ≈ a₂ → f a₁ == f a₂) : φ qa :=
  quot.hrec_on qa f c

@[simp] theorem hrec_on'_mk' {α : Sort u_1} {s₁ : setoid α} {φ : quotient s₁ → Sort u_2}
    (f : (a : α) → φ (quotient.mk' a)) (c : ∀ (a₁ a₂ : α), a₁ ≈ a₂ → f a₁ == f a₂) (x : α) :
    quotient.hrec_on' (quotient.mk' x) f c = f x :=
  rfl

/-- Recursion on two `quotient` arguments `a` and `b`, result type depends on `⟦a⟧` and `⟦b⟧`. -/
protected def hrec_on₂' {α : Sort u_1} {β : Sort u_2} {s₁ : setoid α} {s₂ : setoid β}
    {φ : quotient s₁ → quotient s₂ → Sort u_3} (qa : quotient s₁) (qb : quotient s₂)
    (f : (a : α) → (b : β) → φ (quotient.mk' a) (quotient.mk' b))
    (c : ∀ (a₁ : α) (b₁ : β) (a₂ : α) (b₂ : β), a₁ ≈ a₂ → b₁ ≈ b₂ → f a₁ b₁ == f a₂ b₂) : φ qa qb :=
  quotient.hrec_on₂ qa qb f c

@[simp] theorem hrec_on₂'_mk' {α : Sort u_1} {β : Sort u_2} {s₁ : setoid α} {s₂ : setoid β}
    {φ : quotient s₁ → quotient s₂ → Sort u_3}
    (f : (a : α) → (b : β) → φ (quotient.mk' a) (quotient.mk' b))
    (c : ∀ (a₁ : α) (b₁ : β) (a₂ : α) (b₂ : β), a₁ ≈ a₂ → b₁ ≈ b₂ → f a₁ b₁ == f a₂ b₂) (x : α)
    (qb : quotient s₂) :
    quotient.hrec_on₂' (quotient.mk' x) qb f c =
        quotient.hrec_on' qb (f x) fun (b₁ b₂ : β) => c x b₁ x b₂ (setoid.refl x) :=
  rfl

/-- Map a function `f : α → β` that sends equivalent elements to equivalent elements
to a function `quotient sa → quotient sb`. Useful to define unary operations on quotients. -/
protected def map' {α : Sort u_1} {β : Sort u_2} {s₁ : setoid α} {s₂ : setoid β} (f : α → β)
    (h : relator.lift_fun has_equiv.equiv has_equiv.equiv f f) : quotient s₁ → quotient s₂ :=
  quot.map f h

@[simp] theorem map'_mk' {α : Sort u_1} {β : Sort u_2} {s₁ : setoid α} {s₂ : setoid β} (f : α → β)
    (h : relator.lift_fun has_equiv.equiv has_equiv.equiv f f) (x : α) :
    quotient.map' f h (quotient.mk' x) = quotient.mk' (f x) :=
  rfl

/-- A version of `quotient.map₂` using curly braces and unification. -/
protected def map₂' {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} {s₁ : setoid α} {s₂ : setoid β}
    {s₃ : setoid γ} (f : α → β → γ)
    (h : relator.lift_fun has_equiv.equiv (has_equiv.equiv ⇒ has_equiv.equiv) f f) :
    quotient s₁ → quotient s₂ → quotient s₃ :=
  quotient.map₂ f h

@[simp] theorem map₂'_mk' {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} {s₁ : setoid α}
    {s₂ : setoid β} {s₃ : setoid γ} (f : α → β → γ)
    (h : relator.lift_fun has_equiv.equiv (has_equiv.equiv ⇒ has_equiv.equiv) f f) (x : α) :
    quotient.map₂' f h (quotient.mk' x) = quotient.map' (f x) (h (setoid.refl x)) :=
  rfl

theorem exact' {α : Sort u_1} {s₁ : setoid α} {a : α} {b : α} :
    quotient.mk' a = quotient.mk' b → setoid.r a b :=
  exact

theorem sound' {α : Sort u_1} {s₁ : setoid α} {a : α} {b : α} :
    setoid.r a b → quotient.mk' a = quotient.mk' b :=
  sound

@[simp] protected theorem eq' {α : Sort u_1} {s₁ : setoid α} {a : α} {b : α} :
    quotient.mk' a = quotient.mk' b ↔ setoid.r a b :=
  eq

/-- A version of `quotient.out` taking `{s₁ : setoid α}` as an implicit argument instead of an
instance argument. -/
def out' {α : Sort u_1} {s₁ : setoid α} (a : quotient s₁) : α := out a

@[simp] theorem out_eq' {α : Sort u_1} {s₁ : setoid α} (q : quotient s₁) :
    quotient.mk' (out' q) = q :=
  out_eq q

theorem mk_out' {α : Sort u_1} {s₁ : setoid α} (a : α) : setoid.r (out' (quotient.mk' a)) a :=
  exact (out_eq (quotient.mk' a))

end Mathlib