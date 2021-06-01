/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.doc_commands
import Mathlib.tactic.reserved_notation
import Mathlib.PostPort

universes u_1 u_2 u_3 u_4 u l w v 

namespace Mathlib

/-!
# Basic logic properties

This file is one of the earliest imports in mathlib.

## Implementation notes

Theorems that require decidability hypotheses are in the namespace "decidable".
Classical versions are in the namespace "classical".

In the presence of automation, this whole file may be unnecessary. On the other hand,
maybe it is useful for writing automation.
-/

/- We add the `inline` attribute to optimize VM computation using these declarations. For example,
  `if p ∧ q then ... else ...` will not evaluate the decidability of `q` if `p` is false. -/

/-- An identity function with its main argument implicit. This will be printed as `hidden` even
if it is applied to a large term, so it can be used for elision,
as done in the `elide` and `unelide` tactics. -/
def hidden {α : Sort u_1} {a : α} : α :=
  a

/-- Ex falso, the nondependent eliminator for the `empty` type. -/
def empty.elim {C : Sort u_1} : empty → C :=
  sorry

protected instance empty.subsingleton : subsingleton empty :=
  subsingleton.intro fun (a : empty) => empty.elim a

protected instance subsingleton.prod {α : Type u_1} {β : Type u_2} [subsingleton α] [subsingleton β] : subsingleton (α × β) :=
  subsingleton.intro
    fun (a b : α × β) =>
      prod.cases_on a
        fun (a_fst : α) (a_snd : β) =>
          prod.cases_on b
            fun (b_fst : α) (b_snd : β) =>
              (fun (fst fst_1 : α) (snd snd_1 : β) =>
                  Eq.trans ((fun (fst : α) (snd : β) => Eq.refl (fst, snd)) fst snd)
                    (congr (congr (Eq.refl Prod.mk) (subsingleton.elim fst fst_1)) (subsingleton.elim snd snd_1)))
                a_fst b_fst a_snd b_snd

protected instance empty.decidable_eq : DecidableEq empty :=
  fun (a : empty) => empty.elim a

protected instance sort.inhabited : Inhabited (Sort u_1) :=
  { default := PUnit }

protected instance sort.inhabited' : Inhabited Inhabited.default :=
  { default := PUnit.unit }

protected instance psum.inhabited_left {α : Sort u_1} {β : Sort u_2} [Inhabited α] : Inhabited (psum α β) :=
  { default := psum.inl Inhabited.default }

protected instance psum.inhabited_right {α : Sort u_1} {β : Sort u_2} [Inhabited β] : Inhabited (psum α β) :=
  { default := psum.inr Inhabited.default }

protected instance decidable_eq_of_subsingleton {α : Sort u_1} [subsingleton α] : DecidableEq α :=
  sorry

@[simp] theorem eq_iff_true_of_subsingleton {α : Type u_1} [subsingleton α] (x : α) (y : α) : x = y ↔ True :=
  of_eq_true (Eq.trans (iff_eq_of_eq_true_right (Eq.refl True)) (eq_true_intro (Eq.symm (subsingleton.elim y x))))

/-- Add an instance to "undo" coercion transitivity into a chain of coercions, because
   most simp lemmas are stated with respect to simple coercions and will not match when
   part of a chain. -/
@[simp] theorem coe_coe {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} [has_coe α β] [has_coe_t β γ] (a : α) : ↑a = ↑↑a :=
  rfl

theorem coe_fn_coe_trans {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} [has_coe α β] [has_coe_t_aux β γ] [has_coe_to_fun γ] (x : α) : ⇑x = ⇑↑x :=
  rfl

@[simp] theorem coe_fn_coe_base {α : Sort u_1} {β : Sort u_2} [has_coe α β] [has_coe_to_fun β] (x : α) : ⇑x = ⇑↑x :=
  rfl

theorem coe_sort_coe_trans {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} [has_coe α β] [has_coe_t_aux β γ] [has_coe_to_sort γ] (x : α) : ↥x = ↥↑x :=
  rfl

/--
Many structures such as bundled morphisms coerce to functions so that you can
transparently apply them to arguments. For example, if `e : α ≃ β` and `a : α`
then you can write `e a` and this is elaborated as `⇑e a`. This type of
coercion is implemented using the `has_coe_to_fun` type class. There is one
important consideration:

If a type coerces to another type which in turn coerces to a function,
then it **must** implement `has_coe_to_fun` directly:
```lean
structure sparkling_equiv (α β) extends α ≃ β

-- if we add a `has_coe` instance,

-- if we add a `has_coe` instance,
instance {α β} : has_coe (sparkling_equiv α β) (α ≃ β) :=
⟨sparkling_equiv.to_equiv⟩

-- then a `has_coe_to_fun` instance **must** be added as well:

-- then a `has_coe_to_fun` instance **must** be added as well:
instance {α β} : has_coe_to_fun (sparkling_equiv α β) :=
⟨λ _, α → β, λ f, f.to_equiv.to_fun⟩
```

(Rationale: if we do not declare the direct coercion, then `⇑e a` is not in
simp-normal form. The lemma `coe_fn_coe_base` will unfold it to `⇑↑e a`. This
often causes loops in the simplifier.)
-/
@[simp] theorem coe_sort_coe_base {α : Sort u_1} {β : Sort u_2} [has_coe α β] [has_coe_to_sort β] (x : α) : ↥x = ↥↑x :=
  rfl

/-- `pempty` is the universe-polymorphic analogue of `empty`. -/
inductive pempty 
where

/-- Ex falso, the nondependent eliminator for the `pempty` type. -/
def pempty.elim {C : Sort u_1} : pempty → C :=
  sorry

protected instance subsingleton_pempty : subsingleton pempty :=
  subsingleton.intro fun (a : pempty) => pempty.elim a

@[simp] theorem not_nonempty_pempty : ¬Nonempty pempty :=
  fun (_x : Nonempty pempty) =>
    (fun (_a : Nonempty pempty) => nonempty.dcases_on _a fun (val : pempty) => idRhs False (pempty.elim val)) _x

@[simp] theorem forall_pempty {P : pempty → Prop} : (∀ (x : pempty), P x) ↔ True :=
  { mp := fun (h : ∀ (x : pempty), P x) => trivial,
    mpr := fun (h : True) (x : pempty) => pempty.cases_on (fun (x : pempty) => P x) x }

@[simp] theorem exists_pempty {P : pempty → Prop} : (∃ (x : pempty), P x) ↔ False := sorry

theorem congr_arg_heq {α : Sort u_1} {β : α → Sort u_2} (f : (a : α) → β a) {a₁ : α} {a₂ : α} : a₁ = a₂ → f a₁ == f a₂ := sorry

theorem plift.down_inj {α : Sort u_1} (a : plift α) (b : plift α) : plift.down a = plift.down b → a = b := sorry

-- missing [symm] attribute for ne in core.

theorem ne_comm {α : Sort u_1} {a : α} {b : α} : a ≠ b ↔ b ≠ a :=
  { mp := ne.symm, mpr := ne.symm }

@[simp] theorem eq_iff_eq_cancel_left {α : Type u_1} {b : α} {c : α} : (∀ {a : α}, a = b ↔ a = c) ↔ b = c :=
  { mp :=
      fun (h : ∀ {a : α}, a = b ↔ a = c) => eq.mpr (id (Eq._oldrec (Eq.refl (b = c)) (Eq.symm (propext h)))) (Eq.refl b),
    mpr := fun (h : b = c) (a : α) => eq.mpr (id (Eq._oldrec (Eq.refl (a = b ↔ a = c)) h)) (iff.refl (a = c)) }

@[simp] theorem eq_iff_eq_cancel_right {α : Type u_1} {a : α} {b : α} : (∀ {c : α}, a = c ↔ b = c) ↔ a = b :=
  { mp := fun (h : ∀ {c : α}, a = c ↔ b = c) => eq.mpr (id (Eq._oldrec (Eq.refl (a = b)) (propext h))) (Eq.refl b),
    mpr := fun (h : a = b) (a_1 : α) => eq.mpr (id (Eq._oldrec (Eq.refl (a = a_1 ↔ b = a_1)) h)) (iff.refl (b = a_1)) }

/-- Wrapper for adding elementary propositions to the type class systems.
Warning: this can easily be abused. See the rest of this docstring for details.

Certain propositions should not be treated as a class globally,
but sometimes it is very convenient to be able to use the type class system
in specific circumstances.

For example, `zmod p` is a field if and only if `p` is a prime number.
In order to be able to find this field instance automatically by type class search,
we have to turn `p.prime` into an instance implicit assumption.

On the other hand, making `nat.prime` a class would require a major refactoring of the library,
and it is questionable whether making `nat.prime` a class is desirable at all.
The compromise is to add the assumption `[fact p.prime]` to `zmod.field`.

In particular, this class is not intended for turning the type class system
into an automated theorem prover for first order logic. -/
def fact (p : Prop) :=
  p

theorem fact.elim {p : Prop} (h : fact p) : p :=
  h

/-!
### Declarations about propositional connectives
-/

theorem false_ne_true : False ≠ True :=
  fun (ᾰ : False = True) => idRhs ((fun (_x : Prop) => _x) False) (Eq.symm ᾰ ▸ trivial)

/-! ### Declarations about `implies` -/

theorem iff_of_eq {a : Prop} {b : Prop} (e : a = b) : a ↔ b :=
  e ▸ iff.rfl

theorem iff_iff_eq {a : Prop} {b : Prop} : a ↔ b ↔ a = b :=
  { mp := propext, mpr := iff_of_eq }

@[simp] theorem eq_iff_iff {p : Prop} {q : Prop} : p = q ↔ (p ↔ q) :=
  iff.symm iff_iff_eq

@[simp] theorem imp_self {a : Prop} : a → a ↔ True :=
  iff_true_intro id

theorem imp_intro {α : Prop} {β : Prop} (h : α) : β → α :=
  fun (_x : β) => h

theorem imp_false {a : Prop} : a → False ↔ ¬a :=
  iff.rfl

theorem imp_and_distrib {b : Prop} {c : Prop} {α : Sort u_1} : α → b ∧ c ↔ (α → b) ∧ (α → c) :=
  { mp := fun (h : α → b ∧ c) => { left := fun (ha : α) => and.left (h ha), right := fun (ha : α) => and.right (h ha) },
    mpr := fun (h : (α → b) ∧ (α → c)) (ha : α) => { left := and.left h ha, right := and.right h ha } }

@[simp] theorem and_imp {a : Prop} {b : Prop} {c : Prop} : a ∧ b → c ↔ a → b → c := sorry

theorem iff_def {a : Prop} {b : Prop} : a ↔ b ↔ (a → b) ∧ (b → a) :=
  iff_iff_implies_and_implies a b

theorem iff_def' {a : Prop} {b : Prop} : a ↔ b ↔ (b → a) ∧ (a → b) :=
  iff.trans iff_def and.comm

theorem imp_true_iff {α : Sort u_1} : α → True ↔ True :=
  iff_true_intro fun (_x : α) => trivial

@[simp] theorem imp_iff_right {a : Prop} {b : Prop} (ha : a) : a → b ↔ b :=
  { mp := fun (f : a → b) => f ha, mpr := imp_intro }

/-! ### Declarations about `not` -/

/-- Ex falso for negation. From `¬ a` and `a` anything follows. This is the same as `absurd` with
the arguments flipped, but it is in the `not` namespace so that projection notation can be used. -/
def not.elim {a : Prop} {α : Sort u_1} (H1 : ¬a) (H2 : a) : α :=
  absurd H2 H1

theorem not.imp {a : Prop} {b : Prop} (H2 : ¬b) (H1 : a → b) : ¬a :=
  mt H1 H2

theorem not_not_of_not_imp {a : Prop} {b : Prop} : ¬(a → b) → ¬¬a :=
  mt not.elim

theorem not_of_not_imp {b : Prop} {a : Prop} : ¬(a → b) → ¬b :=
  mt imp_intro

theorem dec_em (p : Prop) [Decidable p] : p ∨ ¬p :=
  decidable.em p

theorem em (p : Prop) : p ∨ ¬p :=
  classical.em p

theorem or_not {p : Prop} : p ∨ ¬p :=
  em p

theorem by_contradiction {p : Prop} : (¬p → False) → p :=
  decidable.by_contradiction

-- alias by_contradiction ← by_contra

theorem by_contra {p : Prop} : (¬p → False) → p :=
  decidable.by_contradiction

/--
In most of mathlib, we use the law of excluded middle (LEM) and the axiom of choice (AC) freely.
The `decidable` namespace contains versions of lemmas from the root namespace that explicitly
attempt to avoid the axiom of choice, usually by adding decidability assumptions on the inputs.

You can check if a lemma uses the axiom of choice by using `#print axioms foo` and seeing if
`classical.choice` appears in the list.
-/
-- See Note [decidable namespace]

protected theorem decidable.not_not {a : Prop} [Decidable a] : ¬¬a ↔ a :=
  { mp := decidable.by_contradiction, mpr := not_not_intro }

/-- The Double Negation Theorem: `¬ ¬ P` is equivalent to `P`.
The left-to-right direction, double negation elimination (DNE),
is classically true but not constructively. -/
@[simp] theorem not_not {a : Prop} : ¬¬a ↔ a :=
  decidable.not_not

theorem of_not_not {a : Prop} : ¬¬a → a :=
  by_contra

-- See Note [decidable namespace]

protected theorem decidable.of_not_imp {a : Prop} {b : Prop} [Decidable a] (h : ¬(a → b)) : a :=
  decidable.by_contradiction (not_not_of_not_imp h)

theorem of_not_imp {a : Prop} {b : Prop} : ¬(a → b) → a :=
  decidable.of_not_imp

-- See Note [decidable namespace]

protected theorem decidable.not_imp_symm {a : Prop} {b : Prop} [Decidable a] (h : ¬a → b) (hb : ¬b) : a :=
  decidable.by_contradiction (hb ∘ h)

theorem not.decidable_imp_symm {a : Prop} {b : Prop} [Decidable a] : (¬a → b) → ¬b → a :=
  decidable.not_imp_symm

theorem not.imp_symm {a : Prop} {b : Prop} : (¬a → b) → ¬b → a :=
  not.decidable_imp_symm

-- See Note [decidable namespace]

protected theorem decidable.not_imp_comm {a : Prop} {b : Prop} [Decidable a] [Decidable b] : ¬a → b ↔ ¬b → a :=
  { mp := not.decidable_imp_symm, mpr := not.decidable_imp_symm }

theorem not_imp_comm {a : Prop} {b : Prop} : ¬a → b ↔ ¬b → a :=
  decidable.not_imp_comm

@[simp] theorem imp_not_self {a : Prop} : a → ¬a ↔ ¬a :=
  { mp := fun (h : a → ¬a) (ha : a) => h ha ha, mpr := fun (h : ¬a) (_x : a) => h }

theorem decidable.not_imp_self {a : Prop} [Decidable a] : ¬a → a ↔ a :=
  eq.mp (Eq._oldrec (Eq.refl (¬a → ¬¬a ↔ ¬¬a)) (propext decidable.not_not)) imp_not_self

@[simp] theorem not_imp_self {a : Prop} : ¬a → a ↔ a :=
  decidable.not_imp_self

theorem imp.swap {a : Prop} {b : Prop} {c : Prop} : a → b → c ↔ b → a → c :=
  { mp := function.swap, mpr := function.swap }

theorem imp_not_comm {a : Prop} {b : Prop} : a → ¬b ↔ b → ¬a :=
  imp.swap

/-! ### Declarations about `and` -/

theorem and_congr_left {a : Prop} {b : Prop} {c : Prop} (h : c → (a ↔ b)) : a ∧ c ↔ b ∧ c :=
  iff.trans and.comm (iff.trans (and_congr_right h) and.comm)

theorem and_congr_left' {a : Prop} {b : Prop} {c : Prop} (h : a ↔ b) : a ∧ c ↔ b ∧ c :=
  and_congr h iff.rfl

theorem and_congr_right' {a : Prop} {b : Prop} {c : Prop} (h : b ↔ c) : a ∧ b ↔ a ∧ c :=
  and_congr iff.rfl h

theorem not_and_of_not_left {a : Prop} (b : Prop) : ¬a → ¬(a ∧ b) :=
  mt and.left

theorem not_and_of_not_right (a : Prop) {b : Prop} : ¬b → ¬(a ∧ b) :=
  mt and.right

theorem and.imp_left {a : Prop} {b : Prop} {c : Prop} (h : a → b) : a ∧ c → b ∧ c :=
  and.imp h id

theorem and.imp_right {a : Prop} {b : Prop} {c : Prop} (h : a → b) : c ∧ a → c ∧ b :=
  and.imp id h

theorem and.right_comm {a : Prop} {b : Prop} {c : Prop} : (a ∧ b) ∧ c ↔ (a ∧ c) ∧ b := sorry

theorem and.rotate {a : Prop} {b : Prop} {c : Prop} : a ∧ b ∧ c ↔ b ∧ c ∧ a := sorry

theorem and_not_self_iff (a : Prop) : a ∧ ¬a ↔ False :=
  { mp := fun (h : a ∧ ¬a) => and.right h (and.left h), mpr := fun (h : False) => false.elim h }

theorem not_and_self_iff (a : Prop) : ¬a ∧ a ↔ False := sorry

theorem and_iff_left_of_imp {a : Prop} {b : Prop} (h : a → b) : a ∧ b ↔ a :=
  { mp := and.left, mpr := fun (ha : a) => { left := ha, right := h ha } }

theorem and_iff_right_of_imp {a : Prop} {b : Prop} (h : b → a) : a ∧ b ↔ b :=
  { mp := and.right, mpr := fun (hb : b) => { left := h hb, right := hb } }

@[simp] theorem and_iff_left_iff_imp {a : Prop} {b : Prop} : a ∧ b ↔ a ↔ a → b :=
  { mp := fun (h : a ∧ b ↔ a) (ha : a) => and.right (iff.mpr h ha), mpr := and_iff_left_of_imp }

@[simp] theorem and_iff_right_iff_imp {a : Prop} {b : Prop} : a ∧ b ↔ b ↔ b → a :=
  { mp := fun (h : a ∧ b ↔ b) (ha : b) => and.left (iff.mpr h ha), mpr := and_iff_right_of_imp }

@[simp] theorem and.congr_right_iff {a : Prop} {b : Prop} {c : Prop} : a ∧ b ↔ a ∧ c ↔ a → (b ↔ c) := sorry

@[simp] theorem and.congr_left_iff {a : Prop} {b : Prop} {c : Prop} : a ∧ c ↔ b ∧ c ↔ c → (a ↔ b) := sorry

@[simp] theorem and_self_left {a : Prop} {b : Prop} : a ∧ a ∧ b ↔ a ∧ b :=
  { mp := fun (h : a ∧ a ∧ b) => { left := and.left h, right := and.right (and.right h) },
    mpr := fun (h : a ∧ b) => { left := and.left h, right := { left := and.left h, right := and.right h } } }

@[simp] theorem and_self_right {a : Prop} {b : Prop} : (a ∧ b) ∧ b ↔ a ∧ b :=
  { mp := fun (h : (a ∧ b) ∧ b) => { left := and.left (and.left h), right := and.right h },
    mpr := fun (h : a ∧ b) => { left := { left := and.left h, right := and.right h }, right := and.right h } }

/-! ### Declarations about `or` -/

theorem or_congr_left {a : Prop} {b : Prop} {c : Prop} (h : a ↔ b) : a ∨ c ↔ b ∨ c :=
  or_congr h iff.rfl

theorem or_congr_right {a : Prop} {b : Prop} {c : Prop} (h : b ↔ c) : a ∨ b ↔ a ∨ c :=
  or_congr iff.rfl h

theorem or.right_comm {a : Prop} {b : Prop} {c : Prop} : (a ∨ b) ∨ c ↔ (a ∨ c) ∨ b :=
  eq.mpr (id (Eq._oldrec (Eq.refl ((a ∨ b) ∨ c ↔ (a ∨ c) ∨ b)) (propext (or_assoc a b))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a ∨ b ∨ c ↔ (a ∨ c) ∨ b)) (propext (or_assoc a c))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a ∨ b ∨ c ↔ a ∨ c ∨ b)) (propext (or_comm b c)))) (iff.refl (a ∨ c ∨ b))))

theorem or_of_or_of_imp_of_imp {a : Prop} {b : Prop} {c : Prop} {d : Prop} (h₁ : a ∨ b) (h₂ : a → c) (h₃ : b → d) : c ∨ d :=
  or.imp h₂ h₃ h₁

theorem or_of_or_of_imp_left {a : Prop} {b : Prop} {c : Prop} (h₁ : a ∨ c) (h : a → b) : b ∨ c :=
  or.imp_left h h₁

theorem or_of_or_of_imp_right {a : Prop} {b : Prop} {c : Prop} (h₁ : c ∨ a) (h : a → b) : c ∨ b :=
  or.imp_right h h₁

theorem or.elim3 {a : Prop} {b : Prop} {c : Prop} {d : Prop} (h : a ∨ b ∨ c) (ha : a → d) (hb : b → d) (hc : c → d) : d :=
  or.elim h ha fun (h₂ : b ∨ c) => or.elim h₂ hb hc

theorem or_imp_distrib {a : Prop} {b : Prop} {c : Prop} : a ∨ b → c ↔ (a → c) ∧ (b → c) := sorry

-- See Note [decidable namespace]

protected theorem decidable.or_iff_not_imp_left {a : Prop} {b : Prop} [Decidable a] : a ∨ b ↔ ¬a → b :=
  { mp := or.resolve_left, mpr := fun (h : ¬a → b) => dite a Or.inl (Or.inr ∘ h) }

theorem or_iff_not_imp_left {a : Prop} {b : Prop} : a ∨ b ↔ ¬a → b :=
  decidable.or_iff_not_imp_left

-- See Note [decidable namespace]

protected theorem decidable.or_iff_not_imp_right {a : Prop} {b : Prop} [Decidable b] : a ∨ b ↔ ¬b → a :=
  iff.trans or.comm decidable.or_iff_not_imp_left

theorem or_iff_not_imp_right {a : Prop} {b : Prop} : a ∨ b ↔ ¬b → a :=
  decidable.or_iff_not_imp_right

-- See Note [decidable namespace]

protected theorem decidable.not_imp_not {a : Prop} {b : Prop} [Decidable a] : ¬a → ¬b ↔ b → a :=
  { mp := fun (h : ¬a → ¬b) (hb : b) => decidable.by_contradiction fun (na : ¬a) => h na hb, mpr := mt }

theorem not_imp_not {a : Prop} {b : Prop} : ¬a → ¬b ↔ b → a :=
  decidable.not_imp_not

@[simp] theorem or_iff_left_iff_imp {a : Prop} {b : Prop} : a ∨ b ↔ a ↔ b → a :=
  { mp := fun (h : a ∨ b ↔ a) (hb : b) => iff.mp h (Or.inr hb), mpr := or_iff_left_of_imp }

@[simp] theorem or_iff_right_iff_imp {a : Prop} {b : Prop} : a ∨ b ↔ b ↔ a → b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ∨ b ↔ b ↔ a → b)) (propext (or_comm a b))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b ∨ a ↔ b ↔ a → b)) (propext or_iff_left_iff_imp))) (iff.refl (a → b)))

/-! ### Declarations about distributivity -/

/-- `∧` distributes over `∨` (on the left). -/
theorem and_or_distrib_left {a : Prop} {b : Prop} {c : Prop} : a ∧ (b ∨ c) ↔ a ∧ b ∨ a ∧ c := sorry

/-- `∧` distributes over `∨` (on the right). -/
theorem or_and_distrib_right {a : Prop} {b : Prop} {c : Prop} : (a ∨ b) ∧ c ↔ a ∧ c ∨ b ∧ c :=
  iff.trans (iff.trans and.comm and_or_distrib_left) (or_congr and.comm and.comm)

/-- `∨` distributes over `∧` (on the left). -/
theorem or_and_distrib_left {a : Prop} {b : Prop} {c : Prop} : a ∨ b ∧ c ↔ (a ∨ b) ∧ (a ∨ c) :=
  { mp := Or._oldrec (fun (ha : a) => { left := Or.inl ha, right := Or.inl ha }) (and.imp Or.inr Or.inr),
    mpr := And._oldrec (Or._oldrec (imp_intro ∘ Or.inl) (or.imp_right ∘ And.intro)) }

/-- `∨` distributes over `∧` (on the right). -/
theorem and_or_distrib_right {a : Prop} {b : Prop} {c : Prop} : a ∧ b ∨ c ↔ (a ∨ c) ∧ (b ∨ c) :=
  iff.trans (iff.trans or.comm or_and_distrib_left) (and_congr or.comm or.comm)

@[simp] theorem or_self_left {a : Prop} {b : Prop} : a ∨ a ∨ b ↔ a ∨ b :=
  { mp := fun (h : a ∨ a ∨ b) => or.elim h Or.inl id, mpr := fun (h : a ∨ b) => or.elim h Or.inl (Or.inr ∘ Or.inr) }

@[simp] theorem or_self_right {a : Prop} {b : Prop} : (a ∨ b) ∨ b ↔ a ∨ b :=
  { mp := fun (h : (a ∨ b) ∨ b) => or.elim h id Or.inr, mpr := fun (h : a ∨ b) => or.elim h (Or.inl ∘ Or.inl) Or.inr }

/-! Declarations about `iff` -/

theorem iff_of_true {a : Prop} {b : Prop} (ha : a) (hb : b) : a ↔ b :=
  { mp := fun (_x : a) => hb, mpr := fun (_x : b) => ha }

theorem iff_of_false {a : Prop} {b : Prop} (ha : ¬a) (hb : ¬b) : a ↔ b :=
  { mp := not.elim ha, mpr := not.elim hb }

theorem iff_true_left {a : Prop} {b : Prop} (ha : a) : a ↔ b ↔ b :=
  { mp := fun (h : a ↔ b) => iff.mp h ha, mpr := iff_of_true ha }

theorem iff_true_right {a : Prop} {b : Prop} (ha : a) : b ↔ a ↔ b :=
  iff.trans iff.comm (iff_true_left ha)

theorem iff_false_left {a : Prop} {b : Prop} (ha : ¬a) : a ↔ b ↔ ¬b :=
  { mp := fun (h : a ↔ b) => mt (iff.mpr h) ha, mpr := iff_of_false ha }

theorem iff_false_right {a : Prop} {b : Prop} (ha : ¬a) : b ↔ a ↔ ¬b :=
  iff.trans iff.comm (iff_false_left ha)

-- See Note [decidable namespace]

protected theorem decidable.not_or_of_imp {a : Prop} {b : Prop} [Decidable a] (h : a → b) : ¬a ∨ b :=
  dite a (fun (ha : a) => Or.inr (h ha)) fun (ha : ¬a) => Or.inl ha

theorem not_or_of_imp {a : Prop} {b : Prop} : (a → b) → ¬a ∨ b :=
  decidable.not_or_of_imp

-- See Note [decidable namespace]

protected theorem decidable.imp_iff_not_or {a : Prop} {b : Prop} [Decidable a] : a → b ↔ ¬a ∨ b :=
  { mp := decidable.not_or_of_imp, mpr := or.neg_resolve_left }

theorem imp_iff_not_or {a : Prop} {b : Prop} : a → b ↔ ¬a ∨ b :=
  decidable.imp_iff_not_or

-- See Note [decidable namespace]

protected theorem decidable.imp_or_distrib {a : Prop} {b : Prop} {c : Prop} [Decidable a] : a → b ∨ c ↔ (a → b) ∨ (a → c) := sorry

theorem imp_or_distrib {a : Prop} {b : Prop} {c : Prop} : a → b ∨ c ↔ (a → b) ∨ (a → c) :=
  decidable.imp_or_distrib

-- See Note [decidable namespace]

protected theorem decidable.imp_or_distrib' {a : Prop} {b : Prop} {c : Prop} [Decidable b] : a → b ∨ c ↔ (a → b) ∨ (a → c) := sorry

theorem imp_or_distrib' {a : Prop} {b : Prop} {c : Prop} : a → b ∨ c ↔ (a → b) ∨ (a → c) :=
  decidable.imp_or_distrib'

theorem not_imp_of_and_not {a : Prop} {b : Prop} : a ∧ ¬b → ¬(a → b) :=
  fun (ᾰ : a ∧ ¬b) (ᾰ_1 : a → b) => and.dcases_on ᾰ fun (ᾰ_left : a) (ᾰ_right : ¬b) => idRhs False (ᾰ_right (ᾰ_1 ᾰ_left))

-- See Note [decidable namespace]

protected theorem decidable.not_imp {a : Prop} {b : Prop} [Decidable a] : ¬(a → b) ↔ a ∧ ¬b :=
  { mp := fun (h : ¬(a → b)) => { left := decidable.of_not_imp h, right := not_of_not_imp h }, mpr := not_imp_of_and_not }

theorem not_imp {a : Prop} {b : Prop} : ¬(a → b) ↔ a ∧ ¬b :=
  decidable.not_imp

-- for monotonicity

theorem imp_imp_imp {a : Prop} {b : Prop} {c : Prop} {d : Prop} (h₀ : c → a) (h₁ : b → d) : (a → b) → c → d :=
  fun (h₂ : a → b) => h₁ ∘ h₂ ∘ h₀

-- See Note [decidable namespace]

protected theorem decidable.peirce (a : Prop) (b : Prop) [Decidable a] : ((a → b) → a) → a :=
  dite a (fun (ha : a) (h : (a → b) → a) => ha) fun (ha : ¬a) (h : (a → b) → a) => h (not.elim ha)

theorem peirce (a : Prop) (b : Prop) : ((a → b) → a) → a :=
  decidable.peirce a b

theorem peirce' {a : Prop} (H : ∀ (b : Prop), (a → b) → a) : a :=
  H a id

-- See Note [decidable namespace]

protected theorem decidable.not_iff_not {a : Prop} {b : Prop} [Decidable a] [Decidable b] : ¬a ↔ ¬b ↔ (a ↔ b) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (¬a ↔ ¬b ↔ (a ↔ b))) (propext iff_def)))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((¬a → ¬b) ∧ (¬b → ¬a) ↔ (a ↔ b))) (propext iff_def')))
      (and_congr decidable.not_imp_not decidable.not_imp_not))

theorem not_iff_not {a : Prop} {b : Prop} : ¬a ↔ ¬b ↔ (a ↔ b) :=
  decidable.not_iff_not

-- See Note [decidable namespace]

protected theorem decidable.not_iff_comm {a : Prop} {b : Prop} [Decidable a] [Decidable b] : ¬a ↔ b ↔ (¬b ↔ a) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (¬a ↔ b ↔ (¬b ↔ a))) (propext iff_def)))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((¬a → b) ∧ (b → ¬a) ↔ (¬b ↔ a))) (propext iff_def)))
      (and_congr decidable.not_imp_comm imp_not_comm))

theorem not_iff_comm {a : Prop} {b : Prop} : ¬a ↔ b ↔ (¬b ↔ a) :=
  decidable.not_iff_comm

-- See Note [decidable namespace]

protected theorem decidable.not_iff {a : Prop} {b : Prop} [Decidable b] : ¬(a ↔ b) ↔ (¬a ↔ b) := sorry

theorem not_iff {a : Prop} {b : Prop} : ¬(a ↔ b) ↔ (¬a ↔ b) :=
  decidable.not_iff

-- See Note [decidable namespace]

protected theorem decidable.iff_not_comm {a : Prop} {b : Prop} [Decidable a] [Decidable b] : a ↔ ¬b ↔ (b ↔ ¬a) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ↔ ¬b ↔ (b ↔ ¬a))) (propext iff_def)))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((a → ¬b) ∧ (¬b → a) ↔ (b ↔ ¬a))) (propext iff_def)))
      (and_congr imp_not_comm decidable.not_imp_comm))

theorem iff_not_comm {a : Prop} {b : Prop} : a ↔ ¬b ↔ (b ↔ ¬a) :=
  decidable.iff_not_comm

-- See Note [decidable namespace]

protected theorem decidable.iff_iff_and_or_not_and_not {a : Prop} {b : Prop} [Decidable b] : a ↔ b ↔ a ∧ b ∨ ¬a ∧ ¬b := sorry

theorem iff_iff_and_or_not_and_not {a : Prop} {b : Prop} : a ↔ b ↔ a ∧ b ∨ ¬a ∧ ¬b :=
  decidable.iff_iff_and_or_not_and_not

theorem decidable.iff_iff_not_or_and_or_not {a : Prop} {b : Prop} [Decidable a] [Decidable b] : a ↔ b ↔ (¬a ∨ b) ∧ (a ∨ ¬b) := sorry

theorem iff_iff_not_or_and_or_not {a : Prop} {b : Prop} : a ↔ b ↔ (¬a ∨ b) ∧ (a ∨ ¬b) :=
  decidable.iff_iff_not_or_and_or_not

-- See Note [decidable namespace]

protected theorem decidable.not_and_not_right {a : Prop} {b : Prop} [Decidable b] : ¬(a ∧ ¬b) ↔ a → b := sorry

theorem not_and_not_right {a : Prop} {b : Prop} : ¬(a ∧ ¬b) ↔ a → b :=
  decidable.not_and_not_right

/-- Transfer decidability of `a` to decidability of `b`, if the propositions are equivalent.
**Important**: this function should be used instead of `rw` on `decidable b`, because the
kernel will get stuck reducing the usage of `propext` otherwise,
and `dec_trivial` will not work. -/
def decidable_of_iff {b : Prop} (a : Prop) (h : a ↔ b) [D : Decidable a] : Decidable b :=
  decidable_of_decidable_of_iff D h

/-- Transfer decidability of `b` to decidability of `a`, if the propositions are equivalent.
This is the same as `decidable_of_iff` but the iff is flipped. -/
def decidable_of_iff' {a : Prop} (b : Prop) (h : a ↔ b) [D : Decidable b] : Decidable a :=
  decidable_of_decidable_of_iff D (iff.symm h)

/-- Prove that `a` is decidable by constructing a boolean `b` and a proof that `b ↔ a`.
(This is sometimes taken as an alternate definition of decidability.) -/
def decidable_of_bool {a : Prop} (b : Bool) (h : ↥b ↔ a) : Decidable a :=
  sorry

/-! ### De Morgan's laws -/

theorem not_and_of_not_or_not {a : Prop} {b : Prop} (h : ¬a ∨ ¬b) : ¬(a ∧ b) :=
  fun (ᾰ : a ∧ b) =>
    and.dcases_on ᾰ fun (ᾰ_left : a) (ᾰ_right : b) => idRhs False (or.elim h (absurd ᾰ_left) (absurd ᾰ_right))

-- See Note [decidable namespace]

protected theorem decidable.not_and_distrib {a : Prop} {b : Prop} [Decidable a] : ¬(a ∧ b) ↔ ¬a ∨ ¬b := sorry

-- See Note [decidable namespace]

protected theorem decidable.not_and_distrib' {a : Prop} {b : Prop} [Decidable b] : ¬(a ∧ b) ↔ ¬a ∨ ¬b := sorry

/-- One of de Morgan's laws: the negation of a conjunction is logically equivalent to the
disjunction of the negations. -/
theorem not_and_distrib {a : Prop} {b : Prop} : ¬(a ∧ b) ↔ ¬a ∨ ¬b :=
  decidable.not_and_distrib

@[simp] theorem not_and {a : Prop} {b : Prop} : ¬(a ∧ b) ↔ a → ¬b :=
  and_imp

theorem not_and' {a : Prop} {b : Prop} : ¬(a ∧ b) ↔ b → ¬a :=
  iff.trans not_and imp_not_comm

/-- One of de Morgan's laws: the negation of a disjunction is logically equivalent to the
conjunction of the negations. -/
theorem not_or_distrib {a : Prop} {b : Prop} : ¬(a ∨ b) ↔ ¬a ∧ ¬b := sorry

-- See Note [decidable namespace]

protected theorem decidable.or_iff_not_and_not {a : Prop} {b : Prop} [Decidable a] [Decidable b] : a ∨ b ↔ ¬(¬a ∧ ¬b) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ∨ b ↔ ¬(¬a ∧ ¬b))) (Eq.symm (propext not_or_distrib))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a ∨ b ↔ ¬¬(a ∨ b))) (propext decidable.not_not))) (iff.refl (a ∨ b)))

theorem or_iff_not_and_not {a : Prop} {b : Prop} : a ∨ b ↔ ¬(¬a ∧ ¬b) :=
  decidable.or_iff_not_and_not

-- See Note [decidable namespace]

protected theorem decidable.and_iff_not_or_not {a : Prop} {b : Prop} [Decidable a] [Decidable b] : a ∧ b ↔ ¬(¬a ∨ ¬b) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ∧ b ↔ ¬(¬a ∨ ¬b))) (Eq.symm (propext decidable.not_and_distrib))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a ∧ b ↔ ¬¬(a ∧ b))) (propext decidable.not_not))) (iff.refl (a ∧ b)))

theorem and_iff_not_or_not {a : Prop} {b : Prop} : a ∧ b ↔ ¬(¬a ∨ ¬b) :=
  decidable.and_iff_not_or_not

/-! ### Declarations about equality -/

@[simp] theorem heq_iff_eq {α : Sort u_1} {a : α} {b : α} : a == b ↔ a = b :=
  { mp := eq_of_heq, mpr := heq_of_eq }

theorem proof_irrel_heq {p : Prop} {q : Prop} (hp : p) (hq : q) : hp == hq :=
  (fun (this : p = q) => Eq._oldrec (fun (hq : p) => HEq.refl hp) this hq)
    (propext { mp := fun (_x : p) => hq, mpr := fun (_x : q) => hp })

theorem ne_of_mem_of_not_mem {α : outParam (Type u_1)} {β : Type u_2} [has_mem α β] {s : β} {a : α} {b : α} (h : a ∈ s) : ¬b ∈ s → a ≠ b :=
  mt fun (e : a = b) => e ▸ h

theorem eq_equivalence {α : Sort u_1} : equivalence Eq :=
  { left := Eq.refl, right := { left := Eq.symm, right := Eq.trans } }

/-- Transport through trivial families is the identity. -/
@[simp] theorem eq_rec_constant {α : Sort u_1} {a : α} {a' : α} {β : Sort u_2} (y : β) (h : a = a') : Eq._oldrec y h = y := sorry

@[simp] theorem eq_mp_rfl {α : Sort u_1} {a : α} : eq.mp (Eq.refl α) a = a :=
  rfl

@[simp] theorem eq_mpr_rfl {α : Sort u_1} {a : α} : eq.mpr (Eq.refl α) a = a :=
  rfl

theorem heq_of_eq_mp {α : Sort u_1} {β : Sort u_1} {a : α} {a' : β} (e : α = β) (h₂ : eq.mp e a = a') : a == a' := sorry

theorem rec_heq_of_heq {α : Sort u_1} {a : α} {b : α} {β : Sort u_2} {C : α → Sort u_2} {x : C a} {y : β} (eq : a = b) (h : x == y) : Eq._oldrec x eq == y :=
  eq.drec h eq

@[simp] theorem eq_mpr_heq {α : Sort u} {β : Sort u} (h : β = α) (x : α) : eq.mpr h x == x :=
  eq.drec (fun (x : β) => HEq.refl (eq.mpr (Eq.refl β) x)) h x

protected theorem eq.congr {α : Sort u_1} {x₁ : α} {x₂ : α} {y₁ : α} {y₂ : α} (h₁ : x₁ = y₁) (h₂ : x₂ = y₂) : x₁ = x₂ ↔ y₁ = y₂ :=
  Eq._oldrec (Eq._oldrec (iff.refl (x₁ = x₂)) h₂) h₁

theorem eq.congr_left {α : Sort u_1} {x : α} {y : α} {z : α} (h : x = y) : x = z ↔ y = z :=
  eq.mpr (id (Eq._oldrec (Eq.refl (x = z ↔ y = z)) h)) (iff.refl (y = z))

theorem eq.congr_right {α : Sort u_1} {x : α} {y : α} {z : α} (h : x = y) : z = x ↔ z = y :=
  eq.mpr (id (Eq._oldrec (Eq.refl (z = x ↔ z = y)) h)) (iff.refl (z = y))

theorem congr_arg2 {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : α → β → γ) {x : α} {x' : α} {y : β} {y' : β} (hx : x = x') (hy : y = y') : f x y = f x' y' :=
  Eq._oldrec (Eq._oldrec (Eq.refl (f x y)) hy) hx

/-! ### Declarations about quantifiers -/

theorem forall_imp {α : Sort u_1} {p : α → Prop} {q : α → Prop} (h : ∀ (a : α), p a → q a) : (∀ (a : α), p a) → ∀ (a : α), q a :=
  fun (h' : ∀ (a : α), p a) (a : α) => h a (h' a)

theorem forall₂_congr {α : Sort u_1} {β : Sort u_2} {p : α → β → Prop} {q : α → β → Prop} (h : ∀ (a : α) (b : β), p a b ↔ q a b) : (∀ (a : α) (b : β), p a b) ↔ ∀ (a : α) (b : β), q a b :=
  forall_congr fun (a : α) => forall_congr (h a)

theorem forall₃_congr {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} {p : α → β → γ → Prop} {q : α → β → γ → Prop} (h : ∀ (a : α) (b : β) (c : γ), p a b c ↔ q a b c) : (∀ (a : α) (b : β) (c : γ), p a b c) ↔ ∀ (a : α) (b : β) (c : γ), q a b c :=
  forall_congr fun (a : α) => forall₂_congr (h a)

theorem forall₄_congr {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} {δ : Sort u_4} {p : α → β → γ → δ → Prop} {q : α → β → γ → δ → Prop} (h : ∀ (a : α) (b : β) (c : γ) (d : δ), p a b c d ↔ q a b c d) : (∀ (a : α) (b : β) (c : γ) (d : δ), p a b c d) ↔ ∀ (a : α) (b : β) (c : γ) (d : δ), q a b c d :=
  forall_congr fun (a : α) => forall₃_congr (h a)

theorem Exists.imp {α : Sort u_1} {q : α → Prop} {p : α → Prop} (h : ∀ (a : α), p a → q a) : (∃ (a : α), p a) → ∃ (a : α), q a :=
  fun (p_1 : ∃ (a : α), p a) => exists_imp_exists h p_1

theorem exists_imp_exists' {α : Sort u_1} {β : Sort u_2} {p : α → Prop} {q : β → Prop} (f : α → β) (hpq : ∀ (a : α), p a → q (f a)) (hp : ∃ (a : α), p a) : ∃ (b : β), q b :=
  exists.elim hp fun (a : α) (hp' : p a) => Exists.intro (f a) (hpq a hp')

theorem exists₂_congr {α : Sort u_1} {β : Sort u_2} {p : α → β → Prop} {q : α → β → Prop} (h : ∀ (a : α) (b : β), p a b ↔ q a b) : (∃ (a : α), ∃ (b : β), p a b) ↔ ∃ (a : α), ∃ (b : β), q a b :=
  exists_congr fun (a : α) => exists_congr (h a)

theorem exists₃_congr {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} {p : α → β → γ → Prop} {q : α → β → γ → Prop} (h : ∀ (a : α) (b : β) (c : γ), p a b c ↔ q a b c) : (∃ (a : α), ∃ (b : β), ∃ (c : γ), p a b c) ↔ ∃ (a : α), ∃ (b : β), ∃ (c : γ), q a b c :=
  exists_congr fun (a : α) => exists₂_congr (h a)

theorem exists₄_congr {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} {δ : Sort u_4} {p : α → β → γ → δ → Prop} {q : α → β → γ → δ → Prop} (h : ∀ (a : α) (b : β) (c : γ) (d : δ), p a b c d ↔ q a b c d) : (∃ (a : α), ∃ (b : β), ∃ (c : γ), ∃ (d : δ), p a b c d) ↔ ∃ (a : α), ∃ (b : β), ∃ (c : γ), ∃ (d : δ), q a b c d :=
  exists_congr fun (a : α) => exists₃_congr (h a)

theorem forall_swap {α : Sort u_1} {β : Sort u_2} {p : α → β → Prop} : (∀ (x : α) (y : β), p x y) ↔ ∀ (y : β) (x : α), p x y :=
  { mp := function.swap, mpr := function.swap }

theorem exists_swap {α : Sort u_1} {β : Sort u_2} {p : α → β → Prop} : (∃ (x : α), ∃ (y : β), p x y) ↔ ∃ (y : β), ∃ (x : α), p x y := sorry

@[simp] theorem exists_imp_distrib {α : Sort u_1} {p : α → Prop} {b : Prop} : (∃ (x : α), p x) → b ↔ ∀ (x : α), p x → b := sorry

/--
Extract an element from a existential statement, using `classical.some`.
-/
-- This enables projection notation.

def Exists.some {α : Sort u_1} {p : α → Prop} (P : ∃ (a : α), p a) : α :=
  classical.some P

/--
Show that an element extracted from `P : ∃ a, p a` using `P.some` satisfies `p`.
-/
theorem Exists.some_spec {α : Sort u_1} {p : α → Prop} (P : ∃ (a : α), p a) : p (Exists.some P) :=
  classical.some_spec P

--theorem forall_not_of_not_exists (h : ¬ ∃ x, p x) : ∀ x, ¬ p x :=

--forall_imp_of_exists_imp h

theorem not_exists_of_forall_not {α : Sort u_1} {p : α → Prop} (h : ∀ (x : α), ¬p x) : ¬∃ (x : α), p x :=
  iff.mpr exists_imp_distrib h

@[simp] theorem not_exists {α : Sort u_1} {p : α → Prop} : (¬∃ (x : α), p x) ↔ ∀ (x : α), ¬p x :=
  exists_imp_distrib

theorem not_forall_of_exists_not {α : Sort u_1} {p : α → Prop} : (∃ (x : α), ¬p x) → ¬∀ (x : α), p x :=
  fun (ᾰ : ∃ (x : α), ¬p x) (ᾰ_1 : ∀ (x : α), p x) =>
    Exists.dcases_on ᾰ fun (ᾰ_w : α) (ᾰ_h : ¬p ᾰ_w) => idRhs False (ᾰ_h (ᾰ_1 ᾰ_w))

-- See Note [decidable namespace]

protected theorem decidable.not_forall {α : Sort u_1} {p : α → Prop} [Decidable (∃ (x : α), ¬p x)] [(x : α) → Decidable (p x)] : (¬∀ (x : α), p x) ↔ ∃ (x : α), ¬p x := sorry

@[simp] theorem not_forall {α : Sort u_1} {p : α → Prop} : (¬∀ (x : α), p x) ↔ ∃ (x : α), ¬p x :=
  decidable.not_forall

-- See Note [decidable namespace]

protected theorem decidable.not_forall_not {α : Sort u_1} {p : α → Prop} [Decidable (∃ (x : α), p x)] : (¬∀ (x : α), ¬p x) ↔ ∃ (x : α), p x :=
  iff.mp decidable.not_iff_comm not_exists

theorem not_forall_not {α : Sort u_1} {p : α → Prop} : (¬∀ (x : α), ¬p x) ↔ ∃ (x : α), p x :=
  decidable.not_forall_not

-- See Note [decidable namespace]

protected theorem decidable.not_exists_not {α : Sort u_1} {p : α → Prop} [(x : α) → Decidable (p x)] : (¬∃ (x : α), ¬p x) ↔ ∀ (x : α), p x := sorry

@[simp] theorem not_exists_not {α : Sort u_1} {p : α → Prop} : (¬∃ (x : α), ¬p x) ↔ ∀ (x : α), p x :=
  decidable.not_exists_not

@[simp] theorem forall_true_iff {α : Sort u_1} : α → True ↔ True :=
  iff_true_intro fun (_x : α) => trivial

-- Unfortunately this causes simp to loop sometimes, so we

-- add the 2 and 3 cases as simp lemmas instead

theorem forall_true_iff' {α : Sort u_1} {p : α → Prop} (h : ∀ (a : α), p a ↔ True) : (∀ (a : α), p a) ↔ True :=
  iff_true_intro fun (_x : α) => of_iff_true (h _x)

@[simp] theorem forall_2_true_iff {α : Sort u_1} {β : α → Sort u_2} : (∀ (a : α), β a → True) ↔ True :=
  forall_true_iff' fun (_x : α) => forall_true_iff

@[simp] theorem forall_3_true_iff {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → Sort u_3} : (∀ (a : α) (b : β a), γ a b → True) ↔ True :=
  forall_true_iff' fun (_x : α) => forall_2_true_iff

@[simp] theorem forall_const {b : Prop} (α : Sort u_1) [i : Nonempty α] : α → b ↔ b :=
  { mp := nonempty.elim i, mpr := fun (hb : b) (x : α) => hb }

@[simp] theorem exists_const {b : Prop} (α : Sort u_1) [i : Nonempty α] : (∃ (x : α), b) ↔ b :=
  { mp := fun (_x : ∃ (x : α), b) => (fun (_a : ∃ (x : α), b) => Exists.dcases_on _a fun (w : α) (h : b) => idRhs b h) _x,
    mpr := nonempty.elim i exists.intro }

theorem forall_and_distrib {α : Sort u_1} {p : α → Prop} {q : α → Prop} : (∀ (x : α), p x ∧ q x) ↔ (∀ (x : α), p x) ∧ ∀ (x : α), q x := sorry

theorem exists_or_distrib {α : Sort u_1} {p : α → Prop} {q : α → Prop} : (∃ (x : α), p x ∨ q x) ↔ (∃ (x : α), p x) ∨ ∃ (x : α), q x := sorry

@[simp] theorem exists_and_distrib_left {α : Sort u_1} {q : Prop} {p : α → Prop} : (∃ (x : α), q ∧ p x) ↔ q ∧ ∃ (x : α), p x := sorry

@[simp] theorem exists_and_distrib_right {α : Sort u_1} {q : Prop} {p : α → Prop} : (∃ (x : α), p x ∧ q) ↔ (∃ (x : α), p x) ∧ q := sorry

@[simp] theorem forall_eq {α : Sort u_1} {p : α → Prop} {a' : α} : (∀ (a : α), a = a' → p a) ↔ p a' :=
  { mp := fun (h : ∀ (a : α), a = a' → p a) => h a' rfl, mpr := fun (h : p a') (a : α) (e : a = a') => Eq.symm e ▸ h }

@[simp] theorem forall_eq' {α : Sort u_1} {p : α → Prop} {a' : α} : (∀ (a : α), a' = a → p a) ↔ p a' := sorry

-- this lemma is needed to simplify the output of `list.mem_cons_iff`

@[simp] theorem forall_eq_or_imp {α : Sort u_1} {p : α → Prop} {q : α → Prop} {a' : α} : (∀ (a : α), a = a' ∨ q a → p a) ↔ p a' ∧ ∀ (a : α), q a → p a := sorry

@[simp] theorem exists_eq {α : Sort u_1} {a' : α} : ∃ (a : α), a = a' :=
  Exists.intro a' rfl

@[simp] theorem exists_eq' {α : Sort u_1} {a' : α} : ∃ (a : α), a' = a :=
  Exists.intro a' rfl

@[simp] theorem exists_eq_left {α : Sort u_1} {p : α → Prop} {a' : α} : (∃ (a : α), a = a' ∧ p a) ↔ p a' := sorry

@[simp] theorem exists_eq_right {α : Sort u_1} {p : α → Prop} {a' : α} : (∃ (a : α), p a ∧ a = a') ↔ p a' :=
  iff.trans (exists_congr fun (a : α) => and.comm) exists_eq_left

@[simp] theorem exists_eq_right_right {α : Sort u_1} {p : α → Prop} {b : Prop} {a' : α} : (∃ (a : α), p a ∧ b ∧ a = a') ↔ p a' ∧ b := sorry

@[simp] theorem exists_eq_right_right' {α : Sort u_1} {p : α → Prop} {b : Prop} {a' : α} : (∃ (a : α), p a ∧ b ∧ a' = a) ↔ p a' ∧ b := sorry

@[simp] theorem exists_apply_eq_apply {α : Type u_1} {β : Type u_2} (f : α → β) (a' : α) : ∃ (a : α), f a = f a' :=
  Exists.intro a' rfl

@[simp] theorem exists_apply_eq_apply' {α : Type u_1} {β : Type u_2} (f : α → β) (a' : α) : ∃ (a : α), f a' = f a :=
  Exists.intro a' rfl

@[simp] theorem exists_exists_and_eq_and {α : Sort u_1} {β : Sort u_2} {f : α → β} {p : α → Prop} {q : β → Prop} : (∃ (b : β), (∃ (a : α), p a ∧ f a = b) ∧ q b) ↔ ∃ (a : α), p a ∧ q (f a) := sorry

@[simp] theorem exists_exists_eq_and {α : Sort u_1} {β : Sort u_2} {f : α → β} {p : β → Prop} : (∃ (b : β), (∃ (a : α), f a = b) ∧ p b) ↔ ∃ (a : α), p (f a) := sorry

@[simp] theorem forall_apply_eq_imp_iff {α : Sort u_1} {β : Sort u_2} {f : α → β} {p : β → Prop} : (∀ (a : α) (b : β), f a = b → p b) ↔ ∀ (a : α), p (f a) :=
  { mp := fun (h : ∀ (a : α) (b : β), f a = b → p b) (a : α) => h a (f a) rfl,
    mpr := fun (h : ∀ (a : α), p (f a)) (a : α) (b : β) (hab : f a = b) => hab ▸ h a }

@[simp] theorem forall_apply_eq_imp_iff' {α : Sort u_1} {β : Sort u_2} {f : α → β} {p : β → Prop} : (∀ (b : β) (a : α), f a = b → p b) ↔ ∀ (a : α), p (f a) := sorry

@[simp] theorem forall_eq_apply_imp_iff {α : Sort u_1} {β : Sort u_2} {f : α → β} {p : β → Prop} : (∀ (a : α) (b : β), b = f a → p b) ↔ ∀ (a : α), p (f a) := sorry

@[simp] theorem forall_eq_apply_imp_iff' {α : Sort u_1} {β : Sort u_2} {f : α → β} {p : β → Prop} : (∀ (b : β) (a : α), b = f a → p b) ↔ ∀ (a : α), p (f a) := sorry

@[simp] theorem forall_apply_eq_imp_iff₂ {α : Sort u_1} {β : Sort u_2} {f : α → β} {p : α → Prop} {q : β → Prop} : (∀ (b : β) (a : α), p a → f a = b → q b) ↔ ∀ (a : α), p a → q (f a) :=
  { mp := fun (h : ∀ (b : β) (a : α), p a → f a = b → q b) (a : α) (ha : p a) => h (f a) a ha rfl,
    mpr := fun (h : ∀ (a : α), p a → q (f a)) (b : β) (a : α) (ha : p a) (hb : f a = b) => hb ▸ h a ha }

@[simp] theorem exists_eq_left' {α : Sort u_1} {p : α → Prop} {a' : α} : (∃ (a : α), a' = a ∧ p a) ↔ p a' := sorry

@[simp] theorem exists_eq_right' {α : Sort u_1} {p : α → Prop} {a' : α} : (∃ (a : α), p a ∧ a' = a) ↔ p a' := sorry

theorem exists_comm {α : Sort u_1} {β : Sort u_2} {p : α → β → Prop} : (∃ (a : α), ∃ (b : β), p a b) ↔ ∃ (b : β), ∃ (a : α), p a b := sorry

theorem forall_or_of_or_forall {α : Sort u_1} {p : α → Prop} {b : Prop} (h : b ∨ ∀ (x : α), p x) (x : α) : b ∨ p x :=
  or.imp_right (fun (h₂ : ∀ (x : α), p x) => h₂ x) h

-- See Note [decidable namespace]

protected theorem decidable.forall_or_distrib_left {α : Sort u_1} {q : Prop} {p : α → Prop} [Decidable q] : (∀ (x : α), q ∨ p x) ↔ q ∨ ∀ (x : α), p x := sorry

theorem forall_or_distrib_left {α : Sort u_1} {q : Prop} {p : α → Prop} : (∀ (x : α), q ∨ p x) ↔ q ∨ ∀ (x : α), p x :=
  decidable.forall_or_distrib_left

-- See Note [decidable namespace]

protected theorem decidable.forall_or_distrib_right {α : Sort u_1} {q : Prop} {p : α → Prop} [Decidable q] : (∀ (x : α), p x ∨ q) ↔ (∀ (x : α), p x) ∨ q := sorry

theorem forall_or_distrib_right {α : Sort u_1} {q : Prop} {p : α → Prop} : (∀ (x : α), p x ∨ q) ↔ (∀ (x : α), p x) ∨ q :=
  decidable.forall_or_distrib_right

/-- A predicate holds everywhere on the image of a surjective functions iff
    it holds everywhere. -/
theorem forall_iff_forall_surj {α : Type u_1} {β : Type u_2} {f : α → β} (h : function.surjective f) {P : β → Prop} : (∀ (a : α), P (f a)) ↔ ∀ (b : β), P b := sorry

@[simp] theorem exists_prop {p : Prop} {q : Prop} : (∃ (h : p), q) ↔ p ∧ q := sorry

@[simp] theorem exists_false {α : Sort u_1} : ¬∃ (a : α), False :=
  fun (_x : ∃ (a : α), False) =>
    (fun (_a : ∃ (a : α), False) => Exists.dcases_on _a fun (w : α) (h : False) => idRhs False h) _x

@[simp] theorem exists_unique_false {α : Sort u_1} : ¬exists_unique fun (a : α) => False := sorry

theorem Exists.fst {b : Prop} {p : b → Prop} : Exists p → b :=
  fun (ᾰ : Exists p) => Exists.dcases_on ᾰ fun (ᾰ_w : b) (ᾰ_h : p ᾰ_w) => idRhs b ᾰ_w

theorem Exists.snd {b : Prop} {p : b → Prop} (h : Exists p) : p (Exists.fst h) :=
  Exists.dcases_on h fun (h_w : b) (h_h : p h_w) => idRhs (p h_w) h_h

@[simp] theorem forall_prop_of_true {p : Prop} {q : p → Prop} (h : p) : (∀ (h' : p), q h') ↔ q h :=
  forall_const p

@[simp] theorem exists_prop_of_true {p : Prop} {q : p → Prop} (h : p) : (∃ (h' : p), q h') ↔ q h :=
  exists_const p

@[simp] theorem forall_prop_of_false {p : Prop} {q : p → Prop} (hn : ¬p) : (∀ (h' : p), q h') ↔ True :=
  iff_true_intro fun (h : p) => not.elim hn h

@[simp] theorem exists_prop_of_false {p : Prop} {q : p → Prop} : ¬p → ¬∃ (h' : p), q h' :=
  mt Exists.fst

theorem exists_unique.exists {α : Sort u_1} {p : α → Prop} (h : exists_unique fun (x : α) => p x) : ∃ (x : α), p x :=
  exists.elim h fun (x : α) (hx : (fun (x : α) => p x) x ∧ ∀ (y : α), p y → y = x) => Exists.intro x (and.left hx)

theorem exists_unique.unique {α : Sort u_1} {p : α → Prop} (h : exists_unique fun (x : α) => p x) {y₁ : α} {y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂ :=
  unique_of_exists_unique h py₁ py₂

@[simp] theorem exists_unique_iff_exists {α : Sort u_1} [subsingleton α] {p : α → Prop} : (exists_unique fun (x : α) => p x) ↔ ∃ (x : α), p x :=
  { mp := fun (h : exists_unique fun (x : α) => p x) => exists_unique.exists h,
    mpr := Exists.imp fun (x : α) (hx : p x) => { left := hx, right := fun (y : α) (_x : p y) => subsingleton.elim y x } }

theorem exists_unique.elim2 {α : Sort u_1} {p : α → Sort u_2} [∀ (x : α), subsingleton (p x)] {q : (x : α) → p x → Prop} {b : Prop} (h₂ : exists_unique fun (x : α) => exists_unique fun (h : p x) => q x h) (h₁ : ∀ (x : α) (h : p x), q x h → (∀ (y : α) (hy : p y), q y hy → y = x) → b) : b := sorry

theorem exists_unique.intro2 {α : Sort u_1} {p : α → Sort u_2} [∀ (x : α), subsingleton (p x)] {q : (x : α) → p x → Prop} (w : α) (hp : p w) (hq : q w hp) (H : ∀ (y : α) (hy : p y), q y hy → y = w) : exists_unique fun (x : α) => exists_unique fun (hx : p x) => q x hx := sorry

theorem exists_unique.exists2 {α : Sort u_1} {p : α → Sort u_2} {q : (x : α) → p x → Prop} (h : exists_unique fun (x : α) => exists_unique fun (hx : p x) => q x hx) : ∃ (x : α), ∃ (hx : p x), q x hx :=
  Exists.imp (fun (x : α) (hx : exists_unique fun (hx : p x) => q x hx) => exists_unique.exists hx)
    (exists_unique.exists h)

theorem exists_unique.unique2 {α : Sort u_1} {p : α → Sort u_2} [∀ (x : α), subsingleton (p x)] {q : (x : α) → p x → Prop} (h : exists_unique fun (x : α) => exists_unique fun (hx : p x) => q x hx) {y₁ : α} {y₂ : α} (hpy₁ : p y₁) (hqy₁ : q y₁ hpy₁) (hpy₂ : p y₂) (hqy₂ : q y₂ hpy₂) : y₁ = y₂ := sorry

/-! ### Classical lemmas -/

namespace classical


theorem cases {p : Prop → Prop} (h1 : p True) (h2 : p False) (a : Prop) : p a :=
  cases_on a h1 h2

/- use shortened names to avoid conflict when classical namespace is open. -/

theorem dec (p : Prop) : Decidable p :=
  prop_decidable p

theorem dec_pred {α : Sort u_1} (p : α → Prop) : decidable_pred p :=
  fun (a : α) => prop_decidable (p a)

theorem dec_rel {α : Sort u_1} (p : α → α → Prop) : DecidableRel p :=
  fun (a b : α) => prop_decidable (p a b)

theorem dec_eq (α : Sort u_1) : DecidableEq α :=
  fun (a b : α) => prop_decidable (a = b)

/--
We make decidability results that depends on `classical.choice` noncomputable lemmas.
* We have to mark them as noncomputable, because otherwise Lean will try to generate bytecode
  for them, and fail because it depends on `classical.choice`.
* We make them lemmas, and not definitions, because otherwise later definitions will raise
  \"failed to generate bytecode\" errors when writing something like
  `letI := classical.dec_eq _`.
Cf. <https://leanprover-community.github.io/archive/113488general/08268noncomputabletheorem.html>
-/
/-- Construct a function from a default value `H0`, and a function to use if there exists a value
satisfying the predicate. -/
def exists_cases {α : Sort u_1} {p : α → Prop} {C : Sort u} (H0 : C) (H : (a : α) → p a → C) : C :=
  dite (∃ (a : α), p a) (fun (h : ∃ (a : α), p a) => H (some h) sorry) fun (h : ¬∃ (a : α), p a) => H0

theorem some_spec2 {α : Sort u_1} {p : α → Prop} {h : ∃ (a : α), p a} (q : α → Prop) (hpq : ∀ (a : α), p a → q a) : q (some h) :=
  hpq (some h) (some_spec h)

/-- A version of classical.indefinite_description which is definitionally equal to a pair -/
def subtype_of_exists {α : Type u_1} {P : α → Prop} (h : ∃ (x : α), P x) : Subtype fun (x : α) => P x :=
  { val := some h, property := sorry }

end classical


/-- This function has the same type as `exists.rec_on`, and can be used to case on an equality,
but `exists.rec_on` can only eliminate into Prop, while this version eliminates into any universe
using the axiom of choice. -/
def exists.classical_rec_on {α : Sort u_1} {p : α → Prop} (h : ∃ (a : α), p a) {C : Sort u} (H : (a : α) → p a → C) : C :=
  H (classical.some h) sorry

/-! ### Declarations about bounded quantifiers -/

theorem bex_def {α : Sort u_1} {p : α → Prop} {q : α → Prop} : (∃ (x : α), ∃ (h : p x), q x) ↔ ∃ (x : α), p x ∧ q x := sorry

theorem bex.elim {α : Sort u_1} {p : α → Prop} {P : (x : α) → p x → Prop} {b : Prop} : (∃ (x : α), ∃ (h : p x), P x h) → (∀ (a : α) (h : p a), P a h → b) → b := sorry

theorem bex.intro {α : Sort u_1} {p : α → Prop} {P : (x : α) → p x → Prop} (a : α) (h₁ : p a) (h₂ : P a h₁) : ∃ (x : α), ∃ (h : p x), P x h :=
  Exists.intro a (Exists.intro h₁ h₂)

theorem ball_congr {α : Sort u_1} {p : α → Prop} {P : (x : α) → p x → Prop} {Q : (x : α) → p x → Prop} (H : ∀ (x : α) (h : p x), P x h ↔ Q x h) : (∀ (x : α) (h : p x), P x h) ↔ ∀ (x : α) (h : p x), Q x h :=
  forall_congr fun (x : α) => forall_congr (H x)

theorem bex_congr {α : Sort u_1} {p : α → Prop} {P : (x : α) → p x → Prop} {Q : (x : α) → p x → Prop} (H : ∀ (x : α) (h : p x), P x h ↔ Q x h) : (∃ (x : α), ∃ (h : p x), P x h) ↔ ∃ (x : α), ∃ (h : p x), Q x h :=
  exists_congr fun (x : α) => exists_congr (H x)

theorem bex_eq_left {α : Sort u_1} {p : α → Prop} {a : α} : (∃ (x : α), ∃ (_x : x = a), p x) ↔ p a := sorry

theorem ball.imp_right {α : Sort u_1} {p : α → Prop} {P : (x : α) → p x → Prop} {Q : (x : α) → p x → Prop} (H : ∀ (x : α) (h : p x), P x h → Q x h) (h₁ : ∀ (x : α) (h : p x), P x h) (x : α) (h : p x) : Q x h :=
  H x h (h₁ x h)

theorem bex.imp_right {α : Sort u_1} {p : α → Prop} {P : (x : α) → p x → Prop} {Q : (x : α) → p x → Prop} (H : ∀ (x : α) (h : p x), P x h → Q x h) : (∃ (x : α), ∃ (h : p x), P x h) → ∃ (x : α), ∃ (h : p x), Q x h := sorry

theorem ball.imp_left {α : Sort u_1} {r : α → Prop} {p : α → Prop} {q : α → Prop} (H : ∀ (x : α), p x → q x) (h₁ : ∀ (x : α), q x → r x) (x : α) (h : p x) : r x :=
  h₁ x (H x h)

theorem bex.imp_left {α : Sort u_1} {r : α → Prop} {p : α → Prop} {q : α → Prop} (H : ∀ (x : α), p x → q x) : (∃ (x : α), ∃ (_x : p x), r x) → ∃ (x : α), ∃ (_x : q x), r x := sorry

theorem ball_of_forall {α : Sort u_1} {p : α → Prop} (h : ∀ (x : α), p x) (x : α) : p x :=
  h x

theorem forall_of_ball {α : Sort u_1} {p : α → Prop} {q : α → Prop} (H : ∀ (x : α), p x) (h : ∀ (x : α), p x → q x) (x : α) : q x :=
  h x (H x)

theorem bex_of_exists {α : Sort u_1} {p : α → Prop} {q : α → Prop} (H : ∀ (x : α), p x) : (∃ (x : α), q x) → ∃ (x : α), ∃ (_x : p x), q x :=
  fun (ᾰ : ∃ (x : α), q x) =>
    Exists.dcases_on ᾰ
      fun (ᾰ_w : α) (ᾰ_h : q ᾰ_w) => idRhs (∃ (x : α), ∃ (_x : p x), q x) (Exists.intro ᾰ_w (Exists.intro (H ᾰ_w) ᾰ_h))

theorem exists_of_bex {α : Sort u_1} {p : α → Prop} {q : α → Prop} : (∃ (x : α), ∃ (_x : p x), q x) → ∃ (x : α), q x := sorry

@[simp] theorem bex_imp_distrib {α : Sort u_1} {p : α → Prop} {P : (x : α) → p x → Prop} {b : Prop} : (∃ (x : α), ∃ (h : p x), P x h) → b ↔ ∀ (x : α) (h : p x), P x h → b := sorry

theorem not_bex {α : Sort u_1} {p : α → Prop} {P : (x : α) → p x → Prop} : (¬∃ (x : α), ∃ (h : p x), P x h) ↔ ∀ (x : α) (h : p x), ¬P x h :=
  bex_imp_distrib

theorem not_ball_of_bex_not {α : Sort u_1} {p : α → Prop} {P : (x : α) → p x → Prop} : (∃ (x : α), ∃ (h : p x), ¬P x h) → ¬∀ (x : α) (h : p x), P x h := sorry

-- See Note [decidable namespace]

protected theorem decidable.not_ball {α : Sort u_1} {p : α → Prop} {P : (x : α) → p x → Prop} [Decidable (∃ (x : α), ∃ (h : p x), ¬P x h)] [(x : α) → (h : p x) → Decidable (P x h)] : (¬∀ (x : α) (h : p x), P x h) ↔ ∃ (x : α), ∃ (h : p x), ¬P x h := sorry

theorem not_ball {α : Sort u_1} {p : α → Prop} {P : (x : α) → p x → Prop} : (¬∀ (x : α) (h : p x), P x h) ↔ ∃ (x : α), ∃ (h : p x), ¬P x h :=
  decidable.not_ball

theorem ball_true_iff {α : Sort u_1} (p : α → Prop) : (∀ (x : α), p x → True) ↔ True :=
  iff_true_intro fun (h : α) (hrx : p h) => trivial

theorem ball_and_distrib {α : Sort u_1} {p : α → Prop} {P : (x : α) → p x → Prop} {Q : (x : α) → p x → Prop} : (∀ (x : α) (h : p x), P x h ∧ Q x h) ↔ (∀ (x : α) (h : p x), P x h) ∧ ∀ (x : α) (h : p x), Q x h :=
  iff.trans (forall_congr fun (x : α) => forall_and_distrib) forall_and_distrib

theorem bex_or_distrib {α : Sort u_1} {p : α → Prop} {P : (x : α) → p x → Prop} {Q : (x : α) → p x → Prop} : (∃ (x : α), ∃ (h : p x), P x h ∨ Q x h) ↔ (∃ (x : α), ∃ (h : p x), P x h) ∨ ∃ (x : α), ∃ (h : p x), Q x h :=
  iff.trans (exists_congr fun (x : α) => exists_or_distrib) exists_or_distrib

theorem ball_or_left_distrib {α : Sort u_1} {r : α → Prop} {p : α → Prop} {q : α → Prop} : (∀ (x : α), p x ∨ q x → r x) ↔ (∀ (x : α), p x → r x) ∧ ∀ (x : α), q x → r x :=
  iff.trans (forall_congr fun (x : α) => or_imp_distrib) forall_and_distrib

theorem bex_or_left_distrib {α : Sort u_1} {r : α → Prop} {p : α → Prop} {q : α → Prop} : (∃ (x : α), ∃ (_x : p x ∨ q x), r x) ↔ (∃ (x : α), ∃ (_x : p x), r x) ∨ ∃ (x : α), ∃ (_x : q x), r x := sorry

namespace classical


theorem not_ball {α : Sort u_1} {p : α → Prop} {P : (x : α) → p x → Prop} : (¬∀ (x : α) (h : p x), P x h) ↔ ∃ (x : α), ∃ (h : p x), ¬P x h :=
  not_ball

end classical


theorem ite_eq_iff {α : Sort u_1} {p : Prop} [Decidable p] {a : α} {b : α} {c : α} : ite p a b = c ↔ p ∧ a = c ∨ ¬p ∧ b = c := sorry

@[simp] theorem ite_eq_left_iff {α : Sort u_1} {p : Prop} [Decidable p] {a : α} {b : α} : ite p a b = a ↔ ¬p → b = a := sorry

@[simp] theorem ite_eq_right_iff {α : Sort u_1} {p : Prop} [Decidable p] {a : α} {b : α} : ite p a b = b ↔ p → a = b := sorry

/-! ### Declarations about `nonempty` -/

protected instance has_zero.nonempty {α : Type u} [HasZero α] : Nonempty α :=
  Nonempty.intro 0

protected instance has_one.nonempty {α : Type u} [HasOne α] : Nonempty α :=
  Nonempty.intro 1

theorem exists_true_iff_nonempty {α : Sort u_1} : (∃ (a : α), True) ↔ Nonempty α := sorry

@[simp] theorem nonempty_Prop {p : Prop} : Nonempty p ↔ p :=
  { mp := fun (_x : Nonempty p) => (fun (_a : Nonempty p) => nonempty.dcases_on _a fun (val : p) => idRhs p val) _x,
    mpr := fun (h : p) => Nonempty.intro h }

theorem not_nonempty_iff_imp_false {α : Type u} : ¬Nonempty α ↔ α → False := sorry

@[simp] theorem nonempty_sigma {α : Type u} {γ : α → Type w} : Nonempty (sigma fun (a : α) => γ a) ↔ ∃ (a : α), Nonempty (γ a) := sorry

@[simp] theorem nonempty_subtype {α : Sort u} {p : α → Prop} : Nonempty (Subtype p) ↔ ∃ (a : α), p a := sorry

@[simp] theorem nonempty_prod {α : Type u} {β : Type v} : Nonempty (α × β) ↔ Nonempty α ∧ Nonempty β := sorry

@[simp] theorem nonempty_pprod {α : Sort u} {β : Sort v} : Nonempty (PProd α β) ↔ Nonempty α ∧ Nonempty β := sorry

@[simp] theorem nonempty_sum {α : Type u} {β : Type v} : Nonempty (α ⊕ β) ↔ Nonempty α ∨ Nonempty β := sorry

@[simp] theorem nonempty_psum {α : Sort u} {β : Sort v} : Nonempty (psum α β) ↔ Nonempty α ∨ Nonempty β := sorry

@[simp] theorem nonempty_psigma {α : Sort u} {β : α → Sort v} : Nonempty (psigma β) ↔ ∃ (a : α), Nonempty (β a) := sorry

@[simp] theorem nonempty_empty : ¬Nonempty empty :=
  fun (_x : Nonempty empty) =>
    (fun (_a : Nonempty empty) => nonempty.dcases_on _a fun (val : empty) => idRhs False (empty.elim val)) _x

@[simp] theorem nonempty_ulift {α : Type u} : Nonempty (ulift α) ↔ Nonempty α := sorry

@[simp] theorem nonempty_plift {α : Sort u} : Nonempty (plift α) ↔ Nonempty α := sorry

@[simp] theorem nonempty.forall {α : Sort u} {p : Nonempty α → Prop} : (∀ (h : Nonempty α), p h) ↔ ∀ (a : α), p (Nonempty.intro a) := sorry

@[simp] theorem nonempty.exists {α : Sort u} {p : Nonempty α → Prop} : (∃ (h : Nonempty α), p h) ↔ ∃ (a : α), p (Nonempty.intro a) := sorry

theorem classical.nonempty_pi {α : Sort u} {β : α → Sort v} : Nonempty ((a : α) → β a) ↔ ∀ (a : α), Nonempty (β a) := sorry

/-- Using `classical.choice`, lifts a (`Prop`-valued) `nonempty` instance to a (`Type`-valued)
  `inhabited` instance. `classical.inhabited_of_nonempty` already exists, in
  `core/init/classical.lean`, but the assumption is not a type class argument,
  which makes it unsuitable for some applications. -/
def classical.inhabited_of_nonempty' {α : Sort u} [h : Nonempty α] : Inhabited α :=
  { default := Classical.choice h }

/-- Using `classical.choice`, extracts a term from a `nonempty` type. -/
protected def nonempty.some {α : Sort u} (h : Nonempty α) : α :=
  Classical.choice h

/-- Using `classical.choice`, extracts a term from a `nonempty` type. -/
protected def classical.arbitrary (α : Sort u) [h : Nonempty α] : α :=
  Classical.choice h

/-- Given `f : α → β`, if `α` is nonempty then `β` is also nonempty.
  `nonempty` cannot be a `functor`, because `functor` is restricted to `Type`. -/
theorem nonempty.map {α : Sort u} {β : Sort v} (f : α → β) : Nonempty α → Nonempty β :=
  fun (ᾰ : Nonempty α) => nonempty.dcases_on ᾰ fun (ᾰ : α) => idRhs (Nonempty β) (Nonempty.intro (f ᾰ))

protected theorem nonempty.map2 {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → γ) : Nonempty α → Nonempty β → Nonempty γ :=
  fun (ᾰ : Nonempty α) (ᾰ_1 : Nonempty β) =>
    nonempty.dcases_on ᾰ
      fun (ᾰ_1_1 : α) => nonempty.dcases_on ᾰ_1 fun (ᾰ : β) => idRhs (Nonempty γ) (Nonempty.intro (f ᾰ_1_1 ᾰ))

protected theorem nonempty.congr {α : Sort u} {β : Sort v} (f : α → β) (g : β → α) : Nonempty α ↔ Nonempty β :=
  { mp := nonempty.map f, mpr := nonempty.map g }

theorem nonempty.elim_to_inhabited {α : Sort u_1} [h : Nonempty α] {p : Prop} (f : Inhabited α → p) : p :=
  nonempty.elim h (f ∘ Inhabited.mk)

protected instance prod.nonempty {α : Type u_1} {β : Type u_2} [h : Nonempty α] [h2 : Nonempty β] : Nonempty (α × β) :=
  nonempty.elim h fun (g : α) => nonempty.elim h2 fun (g2 : β) => Nonempty.intro (g, g2)

/-- A function applied to a `dite` is a `dite` of that function applied to each of the branches. -/
theorem apply_dite {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [Decidable P] (x : P → α) (y : ¬P → α) : f (dite P x y) = dite P (fun (h : P) => f (x h)) fun (h : ¬P) => f (y h) := sorry

/-- A function applied to a `ite` is a `ite` of that function applied to each of the branches. -/
theorem apply_ite {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [Decidable P] (x : α) (y : α) : f (ite P x y) = ite P (f x) (f y) :=
  apply_dite f P (fun (_x : P) => x) fun (_x : ¬P) => y

/-- A two-argument function applied to two `dite`s is a `dite` of that two-argument function
applied to each of the branches. -/
theorem apply_dite2 {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → γ) (P : Prop) [Decidable P] (a : P → α) (b : ¬P → α) (c : P → β) (d : ¬P → β) : f (dite P a b) (dite P c d) = dite P (fun (h : P) => f (a h) (c h)) fun (h : ¬P) => f (b h) (d h) := sorry

/-- A two-argument function applied to two `ite`s is a `ite` of that two-argument function
applied to each of the branches. -/
theorem apply_ite2 {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → γ) (P : Prop) [Decidable P] (a : α) (b : α) (c : β) (d : β) : f (ite P a b) (ite P c d) = ite P (f a c) (f b d) :=
  apply_dite2 f P (fun (_x : P) => a) (fun (_x : ¬P) => b) (fun (_x : P) => c) fun (_x : ¬P) => d

/-- A 'dite' producing a `Pi` type `Π a, β a`, applied to a value `x : α`
is a `dite` that applies either branch to `x`. -/
theorem dite_apply {α : Sort u_1} {β : α → Sort u_2} (P : Prop) [Decidable P] (f : P → (a : α) → β a) (g : ¬P → (a : α) → β a) (x : α) : dite P f g x = dite P (fun (h : P) => f h x) fun (h : ¬P) => g h x := sorry

/-- A 'ite' producing a `Pi` type `Π a, β a`, applied to a value `x : α`
is a `ite` that applies either branch to `x` -/
theorem ite_apply {α : Sort u_1} {β : α → Sort u_2} (P : Prop) [Decidable P] (f : (a : α) → β a) (g : (a : α) → β a) (x : α) : ite P f g x = ite P (f x) (g x) :=
  dite_apply P (fun (_x : P) => f) (fun (_x : ¬P) => g) x

/-- Negation of the condition `P : Prop` in a `dite` is the same as swapping the branches. -/
@[simp] theorem dite_not {α : Sort u_1} (P : Prop) [Decidable P] (x : ¬P → α) (y : ¬¬P → α) : dite (¬P) x y = dite P (fun (h : P) => y (not_not_intro h)) x := sorry

/-- Negation of the condition `P : Prop` in a `ite` is the same as swapping the branches. -/
@[simp] theorem ite_not {α : Sort u_1} (P : Prop) [Decidable P] (x : α) (y : α) : ite (¬P) x y = ite P y x :=
  dite_not P (fun (_x : ¬P) => x) fun (_x : ¬¬P) => y

theorem ite_and {α : Sort u_1} {p : Prop} {q : Prop} [Decidable p] [Decidable q] {x : α} {y : α} : ite (p ∧ q) x y = ite p (ite q x y) y := sorry

