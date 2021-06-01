/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.equiv.list
import Mathlib.logic.function.iterate
import Mathlib.PostPort

universes u_1 l u_2 u_3 u_5 u_4 

namespace Mathlib

/-!
# The primitive recursive functions

The primitive recursive functions are the least collection of functions
`nat → nat` which are closed under projections (using the mkpair
pairing function), composition, zero, successor, and primitive recursion
(i.e. nat.rec where the motive is C n := nat).

We can extend this definition to a large class of basic types by
using canonical encodings of types as natural numbers (Gödel numbering),
which we implement through the type class `encodable`. (More precisely,
we need that the composition of encode with decode yields a
primitive recursive function, so we have the `primcodable` type class
for this.)

## References

* [Mario Carneiro, *Formalizing computability theory via partial recursive functions*][carneiro2019]
-/

namespace nat


def elim {C : Sort u_1} : C → (ℕ → C → C) → ℕ → C := Nat.rec

@[simp] theorem elim_zero {C : Sort u_1} (a : C) (f : ℕ → C → C) : elim a f 0 = a := rfl

@[simp] theorem elim_succ {C : Sort u_1} (a : C) (f : ℕ → C → C) (n : ℕ) :
    elim a f (Nat.succ n) = f n (elim a f n) :=
  rfl

def cases {C : Sort u_1} (a : C) (f : ℕ → C) : ℕ → C := elim a fun (n : ℕ) (_x : C) => f n

@[simp] theorem cases_zero {C : Sort u_1} (a : C) (f : ℕ → C) : cases a f 0 = a := rfl

@[simp] theorem cases_succ {C : Sort u_1} (a : C) (f : ℕ → C) (n : ℕ) :
    cases a f (Nat.succ n) = f n :=
  rfl

@[simp] def unpaired {α : Sort u_1} (f : ℕ → ℕ → α) (n : ℕ) : α :=
  f (prod.fst (unpair n)) (prod.snd (unpair n))

/-- The primitive recursive functions `ℕ → ℕ`. -/
inductive primrec : (ℕ → ℕ) → Prop where
| zero : primrec fun (n : ℕ) => 0
| succ : primrec Nat.succ
| left : primrec fun (n : ℕ) => prod.fst (unpair n)
| right : primrec fun (n : ℕ) => prod.snd (unpair n)
| pair : ∀ {f g : ℕ → ℕ}, primrec f → primrec g → primrec fun (n : ℕ) => mkpair (f n) (g n)
| comp : ∀ {f g : ℕ → ℕ}, primrec f → primrec g → primrec fun (n : ℕ) => f (g n)
| prec :
    ∀ {f g : ℕ → ℕ},
      primrec f →
        primrec g →
          primrec
            (unpaired fun (z n : ℕ) => elim (f z) (fun (y IH : ℕ) => g (mkpair z (mkpair y IH))) n)

namespace primrec


theorem of_eq {f : ℕ → ℕ} {g : ℕ → ℕ} (hf : primrec f) (H : ∀ (n : ℕ), f n = g n) : primrec g :=
  funext H ▸ hf

theorem const (n : ℕ) : primrec fun (_x : ℕ) => n := sorry

protected theorem id : primrec id := sorry

theorem prec1 {f : ℕ → ℕ} (m : ℕ) (hf : primrec f) :
    primrec fun (n : ℕ) => elim m (fun (y IH : ℕ) => f (mkpair y IH)) n :=
  sorry

theorem cases1 {f : ℕ → ℕ} (m : ℕ) (hf : primrec f) : primrec (cases m f) := sorry

theorem cases {f : ℕ → ℕ} {g : ℕ → ℕ} (hf : primrec f) (hg : primrec g) :
    primrec (unpaired fun (z n : ℕ) => cases (f z) (fun (y : ℕ) => g (mkpair z y)) n) :=
  sorry

protected theorem swap : primrec (unpaired (function.swap mkpair)) := sorry

theorem swap' {f : ℕ → ℕ → ℕ} (hf : primrec (unpaired f)) : primrec (unpaired (function.swap f)) :=
  sorry

theorem pred : primrec Nat.pred := sorry

theorem add : primrec (unpaired Add.add) := sorry

theorem sub : primrec (unpaired Sub.sub) := sorry

theorem mul : primrec (unpaired Mul.mul) := sorry

theorem pow : primrec (unpaired pow) := sorry

end primrec


end nat


/-- A `primcodable` type is an `encodable` type for which
  the encode/decode functions are primitive recursive. -/
class primcodable (α : Type u_1) extends encodable α where
  prim : nat.primrec fun (n : ℕ) => encodable.encode (encodable.decode α n)

namespace primcodable


protected instance of_denumerable (α : Type u_1) [denumerable α] : primcodable α := mk sorry

def of_equiv (α : Type u_1) {β : Type u_2} [primcodable α] (e : β ≃ α) : primcodable β := mk sorry

protected instance empty : primcodable empty := mk nat.primrec.zero

protected instance unit : primcodable PUnit := mk sorry

protected instance option {α : Type u_1} [h : primcodable α] : primcodable (Option α) := mk sorry

protected instance bool : primcodable Bool := mk sorry

end primcodable


/-- `primrec f` means `f` is primitive recursive (after
  encoding its input and output as natural numbers). -/
def primrec {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] (f : α → β) :=
  nat.primrec fun (n : ℕ) => encodable.encode (option.map f (encodable.decode α n))

namespace primrec


protected theorem encode {α : Type u_1} [primcodable α] : primrec encodable.encode := sorry

protected theorem decode {α : Type u_1} [primcodable α] : primrec (encodable.decode α) :=
  nat.primrec.comp nat.primrec.succ (primcodable.prim α)

theorem dom_denumerable {α : Type u_1} {β : Type u_2} [denumerable α] [primcodable β] {f : α → β} :
    primrec f ↔ nat.primrec fun (n : ℕ) => encodable.encode (f (denumerable.of_nat α n)) :=
  sorry

theorem nat_iff {f : ℕ → ℕ} : primrec f ↔ nat.primrec f := dom_denumerable

theorem encdec {α : Type u_1} [primcodable α] :
    primrec fun (n : ℕ) => encodable.encode (encodable.decode α n) :=
  iff.mpr nat_iff (primcodable.prim α)

theorem option_some {α : Type u_1} [primcodable α] : primrec some := sorry

theorem of_eq {α : Type u_1} {σ : Type u_3} [primcodable α] [primcodable σ] {f : α → σ} {g : α → σ}
    (hf : primrec f) (H : ∀ (n : α), f n = g n) : primrec g :=
  funext H ▸ hf

theorem const {α : Type u_1} {σ : Type u_3} [primcodable α] [primcodable σ] (x : σ) :
    primrec fun (a : α) => x :=
  sorry

protected theorem id {α : Type u_1} [primcodable α] : primrec id := sorry

theorem comp {α : Type u_1} {β : Type u_2} {σ : Type u_3} [primcodable α] [primcodable β]
    [primcodable σ] {f : β → σ} {g : α → β} (hf : primrec f) (hg : primrec g) :
    primrec fun (a : α) => f (g a) :=
  sorry

theorem succ : primrec Nat.succ := iff.mpr nat_iff nat.primrec.succ

theorem pred : primrec Nat.pred := iff.mpr nat_iff nat.primrec.pred

theorem encode_iff {α : Type u_1} {σ : Type u_3} [primcodable α] [primcodable σ] {f : α → σ} :
    (primrec fun (a : α) => encodable.encode (f a)) ↔ primrec f :=
  sorry

theorem of_nat_iff {α : Type u_1} {β : Type u_2} [denumerable α] [primcodable β] {f : α → β} :
    primrec f ↔ primrec fun (n : ℕ) => f (denumerable.of_nat α n) :=
  iff.trans dom_denumerable (iff.trans (iff.symm nat_iff) encode_iff)

protected theorem of_nat (α : Type u_1) [denumerable α] : primrec (denumerable.of_nat α) :=
  iff.mp of_nat_iff primrec.id

theorem option_some_iff {α : Type u_1} {σ : Type u_3} [primcodable α] [primcodable σ] {f : α → σ} :
    (primrec fun (a : α) => some (f a)) ↔ primrec f :=
  { mp :=
      fun (h : primrec fun (a : α) => some (f a)) =>
        iff.mp encode_iff (comp pred (iff.mpr encode_iff h)),
    mpr := comp option_some }

theorem of_equiv {α : Type u_1} [primcodable α] {β : Type u_2} {e : β ≃ α} : primrec ⇑e :=
  iff.mp encode_iff primrec.encode

theorem of_equiv_symm {α : Type u_1} [primcodable α] {β : Type u_2} {e : β ≃ α} :
    primrec ⇑(equiv.symm e) :=
  sorry

theorem of_equiv_iff {α : Type u_1} {σ : Type u_3} [primcodable α] [primcodable σ] {β : Type u_2}
    (e : β ≃ α) {f : σ → β} : (primrec fun (a : σ) => coe_fn e (f a)) ↔ primrec f :=
  sorry

theorem of_equiv_symm_iff {α : Type u_1} {σ : Type u_3} [primcodable α] [primcodable σ]
    {β : Type u_2} (e : β ≃ α) {f : σ → α} :
    (primrec fun (a : σ) => coe_fn (equiv.symm e) (f a)) ↔ primrec f :=
  sorry

end primrec


namespace primcodable


protected instance prod {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] :
    primcodable (α × β) :=
  mk sorry

end primcodable


namespace primrec


theorem fst {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] : primrec prod.fst :=
  sorry

theorem snd {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] : primrec prod.snd :=
  sorry

theorem pair {α : Type u_1} {β : Type u_2} {γ : Type u_3} [primcodable α] [primcodable β]
    [primcodable γ] {f : α → β} {g : α → γ} (hf : primrec f) (hg : primrec g) :
    primrec fun (a : α) => (f a, g a) :=
  sorry

theorem unpair : primrec nat.unpair := sorry

theorem list_nth₁ {α : Type u_1} [primcodable α] (l : List α) : primrec (list.nth l) := sorry

end primrec


/-- `primrec₂ f` means `f` is a binary primitive recursive function.
  This is technically unnecessary since we can always curry all
  the arguments together, but there are enough natural two-arg
  functions that it is convenient to express this directly. -/
def primrec₂ {α : Type u_1} {β : Type u_2} {σ : Type u_3} [primcodable α] [primcodable β]
    [primcodable σ] (f : α → β → σ) :=
  primrec fun (p : α × β) => f (prod.fst p) (prod.snd p)

/-- `primrec_pred p` means `p : α → Prop` is a (decidable)
  primitive recursive predicate, which is to say that
  `to_bool ∘ p : α → bool` is primitive recursive. -/
def primrec_pred {α : Type u_1} [primcodable α] (p : α → Prop) [decidable_pred p] :=
  primrec fun (a : α) => to_bool (p a)

/-- `primrec_rel p` means `p : α → β → Prop` is a (decidable)
  primitive recursive relation, which is to say that
  `to_bool ∘ p : α → β → bool` is primitive recursive. -/
def primrec_rel {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] (s : α → β → Prop)
    [(a : α) → (b : β) → Decidable (s a b)] :=
  primrec₂ fun (a : α) (b : β) => to_bool (s a b)

namespace primrec₂


theorem of_eq {α : Type u_1} {β : Type u_2} {σ : Type u_3} [primcodable α] [primcodable β]
    [primcodable σ] {f : α → β → σ} {g : α → β → σ} (hg : primrec₂ f)
    (H : ∀ (a : α) (b : β), f a b = g a b) : primrec₂ g :=
  (funext fun (a : α) => funext fun (b : β) => H a b) ▸ hg

theorem const {α : Type u_1} {β : Type u_2} {σ : Type u_3} [primcodable α] [primcodable β]
    [primcodable σ] (x : σ) : primrec₂ fun (a : α) (b : β) => x :=
  primrec.const x

protected theorem pair {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] :
    primrec₂ Prod.mk :=
  primrec.pair primrec.fst primrec.snd

theorem left {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] :
    primrec₂ fun (a : α) (b : β) => a :=
  primrec.fst

theorem right {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] :
    primrec₂ fun (a : α) (b : β) => b :=
  primrec.snd

theorem mkpair : primrec₂ nat.mkpair := sorry

theorem unpaired {α : Type u_1} [primcodable α] {f : ℕ → ℕ → α} :
    primrec (nat.unpaired f) ↔ primrec₂ f :=
  sorry

theorem unpaired' {f : ℕ → ℕ → ℕ} : nat.primrec (nat.unpaired f) ↔ primrec₂ f :=
  iff.trans (iff.symm primrec.nat_iff) unpaired

theorem encode_iff {α : Type u_1} {β : Type u_2} {σ : Type u_3} [primcodable α] [primcodable β]
    [primcodable σ] {f : α → β → σ} :
    (primrec₂ fun (a : α) (b : β) => encodable.encode (f a b)) ↔ primrec₂ f :=
  primrec.encode_iff

theorem option_some_iff {α : Type u_1} {β : Type u_2} {σ : Type u_3} [primcodable α] [primcodable β]
    [primcodable σ] {f : α → β → σ} : (primrec₂ fun (a : α) (b : β) => some (f a b)) ↔ primrec₂ f :=
  primrec.option_some_iff

theorem of_nat_iff {α : Type u_1} {β : Type u_2} {σ : Type u_3} [denumerable α] [denumerable β]
    [primcodable σ] {f : α → β → σ} :
    primrec₂ f ↔ primrec₂ fun (m n : ℕ) => f (denumerable.of_nat α m) (denumerable.of_nat β n) :=
  sorry

theorem uncurry {α : Type u_1} {β : Type u_2} {σ : Type u_3} [primcodable α] [primcodable β]
    [primcodable σ] {f : α → β → σ} : primrec (function.uncurry f) ↔ primrec₂ f :=
  sorry

theorem curry {α : Type u_1} {β : Type u_2} {σ : Type u_3} [primcodable α] [primcodable β]
    [primcodable σ] {f : α × β → σ} : primrec₂ (function.curry f) ↔ primrec f :=
  sorry

end primrec₂


theorem primrec.comp₂ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {σ : Type u_5} [primcodable α]
    [primcodable β] [primcodable γ] [primcodable σ] {f : γ → σ} {g : α → β → γ} (hf : primrec f)
    (hg : primrec₂ g) : primrec₂ fun (a : α) (b : β) => f (g a b) :=
  primrec.comp hf hg

theorem primrec₂.comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} {σ : Type u_5} [primcodable α]
    [primcodable β] [primcodable γ] [primcodable σ] {f : β → γ → σ} {g : α → β} {h : α → γ}
    (hf : primrec₂ f) (hg : primrec g) (hh : primrec h) : primrec fun (a : α) => f (g a) (h a) :=
  primrec.comp hf (primrec.pair hg hh)

theorem primrec₂.comp₂ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {σ : Type u_5}
    [primcodable α] [primcodable β] [primcodable γ] [primcodable δ] [primcodable σ] {f : γ → δ → σ}
    {g : α → β → γ} {h : α → β → δ} (hf : primrec₂ f) (hg : primrec₂ g) (hh : primrec₂ h) :
    primrec₂ fun (a : α) (b : β) => f (g a b) (h a b) :=
  primrec₂.comp hf hg hh

theorem primrec_pred.comp {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β]
    {p : β → Prop} [decidable_pred p] {f : α → β} :
    primrec_pred p → primrec f → primrec_pred fun (a : α) => p (f a) :=
  primrec.comp

theorem primrec_rel.comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} [primcodable α]
    [primcodable β] [primcodable γ] {R : β → γ → Prop} [(a : β) → (b : γ) → Decidable (R a b)]
    {f : α → β} {g : α → γ} :
    primrec_rel R → primrec f → primrec g → primrec_pred fun (a : α) => R (f a) (g a) :=
  primrec₂.comp

theorem primrec_rel.comp₂ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4}
    [primcodable α] [primcodable β] [primcodable γ] [primcodable δ] {R : γ → δ → Prop}
    [(a : γ) → (b : δ) → Decidable (R a b)] {f : α → β → γ} {g : α → β → δ} :
    primrec_rel R →
        primrec₂ f → primrec₂ g → primrec_rel fun (a : α) (b : β) => R (f a b) (g a b) :=
  primrec_rel.comp

theorem primrec_pred.of_eq {α : Type u_1} [primcodable α] {p : α → Prop} {q : α → Prop}
    [decidable_pred p] [decidable_pred q] (hp : primrec_pred p) (H : ∀ (a : α), p a ↔ q a) :
    primrec_pred q :=
  primrec.of_eq hp fun (a : α) => to_bool_congr (H a)

theorem primrec_rel.of_eq {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β]
    {r : α → β → Prop} {s : α → β → Prop} [(a : α) → (b : β) → Decidable (r a b)]
    [(a : α) → (b : β) → Decidable (s a b)] (hr : primrec_rel r)
    (H : ∀ (a : α) (b : β), r a b ↔ s a b) : primrec_rel s :=
  primrec₂.of_eq hr fun (a : α) (b : β) => to_bool_congr (H a b)

namespace primrec₂


theorem swap {α : Type u_1} {β : Type u_2} {σ : Type u_3} [primcodable α] [primcodable β]
    [primcodable σ] {f : α → β → σ} (h : primrec₂ f) : primrec₂ (function.swap f) :=
  comp₂ h right left

theorem nat_iff {α : Type u_1} {β : Type u_2} {σ : Type u_3} [primcodable α] [primcodable β]
    [primcodable σ] {f : α → β → σ} :
    primrec₂ f ↔
        nat.primrec
          (nat.unpaired
            fun (m n : ℕ) =>
              encodable.encode
                (option.bind (encodable.decode α m)
                  fun (a : α) => option.map (f a) (encodable.decode β n))) :=
  sorry

theorem nat_iff' {α : Type u_1} {β : Type u_2} {σ : Type u_3} [primcodable α] [primcodable β]
    [primcodable σ] {f : α → β → σ} :
    primrec₂ f ↔
        primrec₂
          fun (m n : ℕ) =>
            option.bind (encodable.decode α m)
              fun (a : α) => option.map (f a) (encodable.decode β n) :=
  iff.trans nat_iff (iff.trans unpaired' encode_iff)

end primrec₂


namespace primrec


theorem to₂ {α : Type u_1} {β : Type u_2} {σ : Type u_5} [primcodable α] [primcodable β]
    [primcodable σ] {f : α × β → σ} (hf : primrec f) : primrec₂ fun (a : α) (b : β) => f (a, b) :=
  of_eq hf
    fun (_x : α × β) =>
      (fun (_a : α × β) =>
          prod.cases_on _a fun (fst : α) (snd : β) => idRhs (f (fst, snd) = f (fst, snd)) rfl)
        _x

theorem nat_elim {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] {f : α → β}
    {g : α → ℕ × β → β} (hf : primrec f) (hg : primrec₂ g) :
    primrec₂ fun (a : α) (n : ℕ) => nat.elim (f a) (fun (n : ℕ) (IH : β) => g a (n, IH)) n :=
  sorry

theorem nat_elim' {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] {f : α → ℕ}
    {g : α → β} {h : α → ℕ × β → β} (hf : primrec f) (hg : primrec g) (hh : primrec₂ h) :
    primrec fun (a : α) => nat.elim (g a) (fun (n : ℕ) (IH : β) => h a (n, IH)) (f a) :=
  primrec₂.comp (nat_elim hg hh) primrec.id hf

theorem nat_elim₁ {α : Type u_1} [primcodable α] {f : ℕ → α → α} (a : α) (hf : primrec₂ f) :
    primrec (nat.elim a f) :=
  nat_elim' primrec.id (const a) (comp₂ hf primrec₂.right)

theorem nat_cases' {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] {f : α → β}
    {g : α → ℕ → β} (hf : primrec f) (hg : primrec₂ g) :
    primrec₂ fun (a : α) => nat.cases (f a) (g a) :=
  nat_elim hf (primrec₂.comp₂ hg primrec₂.left (comp₂ fst primrec₂.right))

theorem nat_cases {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] {f : α → ℕ}
    {g : α → β} {h : α → ℕ → β} (hf : primrec f) (hg : primrec g) (hh : primrec₂ h) :
    primrec fun (a : α) => nat.cases (g a) (h a) (f a) :=
  primrec₂.comp (nat_cases' hg hh) primrec.id hf

theorem nat_cases₁ {α : Type u_1} [primcodable α] {f : ℕ → α} (a : α) (hf : primrec f) :
    primrec (nat.cases a f) :=
  nat_cases primrec.id (const a) (comp₂ hf primrec₂.right)

theorem nat_iterate {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] {f : α → ℕ}
    {g : α → β} {h : α → β → β} (hf : primrec f) (hg : primrec g) (hh : primrec₂ h) :
    primrec fun (a : α) => nat.iterate (h a) (f a) (g a) :=
  sorry

theorem option_cases {α : Type u_1} {β : Type u_2} {σ : Type u_5} [primcodable α] [primcodable β]
    [primcodable σ] {o : α → Option β} {f : α → σ} {g : α → β → σ} (ho : primrec o) (hf : primrec f)
    (hg : primrec₂ g) : primrec fun (a : α) => option.cases_on (o a) (f a) (g a) :=
  sorry

theorem option_bind {α : Type u_1} {β : Type u_2} {σ : Type u_5} [primcodable α] [primcodable β]
    [primcodable σ] {f : α → Option β} {g : α → β → Option σ} (hf : primrec f) (hg : primrec₂ g) :
    primrec fun (a : α) => option.bind (f a) (g a) :=
  sorry

theorem option_bind₁ {α : Type u_1} {σ : Type u_5} [primcodable α] [primcodable σ]
    {f : α → Option σ} (hf : primrec f) : primrec fun (o : Option α) => option.bind o f :=
  option_bind primrec.id (to₂ (comp hf snd))

theorem option_map {α : Type u_1} {β : Type u_2} {σ : Type u_5} [primcodable α] [primcodable β]
    [primcodable σ] {f : α → Option β} {g : α → β → σ} (hf : primrec f) (hg : primrec₂ g) :
    primrec fun (a : α) => option.map (g a) (f a) :=
  option_bind hf (comp₂ option_some hg)

theorem option_map₁ {α : Type u_1} {σ : Type u_5} [primcodable α] [primcodable σ] {f : α → σ}
    (hf : primrec f) : primrec (option.map f) :=
  option_map primrec.id (to₂ (comp hf snd))

theorem option_iget {α : Type u_1} [primcodable α] [Inhabited α] : primrec option.iget := sorry

theorem option_is_some {α : Type u_1} [primcodable α] : primrec option.is_some := sorry

theorem option_get_or_else {α : Type u_1} [primcodable α] : primrec₂ option.get_or_else := sorry

theorem bind_decode_iff {α : Type u_1} {β : Type u_2} {σ : Type u_5} [primcodable α] [primcodable β]
    [primcodable σ] {f : α → β → Option σ} :
    (primrec₂ fun (a : α) (n : ℕ) => option.bind (encodable.decode β n) (f a)) ↔ primrec₂ f :=
  sorry

theorem map_decode_iff {α : Type u_1} {β : Type u_2} {σ : Type u_5} [primcodable α] [primcodable β]
    [primcodable σ] {f : α → β → σ} :
    (primrec₂ fun (a : α) (n : ℕ) => option.map (f a) (encodable.decode β n)) ↔ primrec₂ f :=
  iff.trans bind_decode_iff primrec₂.option_some_iff

theorem nat_add : primrec₂ Add.add := iff.mp primrec₂.unpaired' nat.primrec.add

theorem nat_sub : primrec₂ Sub.sub := iff.mp primrec₂.unpaired' nat.primrec.sub

theorem nat_mul : primrec₂ Mul.mul := iff.mp primrec₂.unpaired' nat.primrec.mul

theorem cond {α : Type u_1} {σ : Type u_5} [primcodable α] [primcodable σ] {c : α → Bool}
    {f : α → σ} {g : α → σ} (hc : primrec c) (hf : primrec f) (hg : primrec g) :
    primrec fun (a : α) => cond (c a) (f a) (g a) :=
  sorry

theorem ite {α : Type u_1} {σ : Type u_5} [primcodable α] [primcodable σ] {c : α → Prop}
    [decidable_pred c] {f : α → σ} {g : α → σ} (hc : primrec_pred c) (hf : primrec f)
    (hg : primrec g) : primrec fun (a : α) => ite (c a) (f a) (g a) :=
  sorry

theorem nat_le : primrec_rel LessEq := sorry

theorem nat_min : primrec₂ min := ite nat_le fst snd

theorem nat_max : primrec₂ max := ite (primrec_rel.comp nat_le snd fst) fst snd

theorem dom_bool {α : Type u_1} [primcodable α] (f : Bool → α) : primrec f :=
  of_eq (cond primrec.id (const (f tt)) (const (f false)))
    fun (b : Bool) =>
      bool.cases_on b (Eq.refl (cond (id false) (f tt) (f false)))
        (Eq.refl (cond (id tt) (f tt) (f false)))

theorem dom_bool₂ {α : Type u_1} [primcodable α] (f : Bool → Bool → α) : primrec₂ f := sorry

protected theorem bnot : primrec bnot := dom_bool bnot

protected theorem band : primrec₂ band := dom_bool₂ band

protected theorem bor : primrec₂ bor := dom_bool₂ bor

protected theorem not {α : Type u_1} [primcodable α] {p : α → Prop} [decidable_pred p]
    (hp : primrec_pred p) : primrec_pred fun (a : α) => ¬p a :=
  sorry

protected theorem and {α : Type u_1} [primcodable α] {p : α → Prop} {q : α → Prop}
    [decidable_pred p] [decidable_pred q] (hp : primrec_pred p) (hq : primrec_pred q) :
    primrec_pred fun (a : α) => p a ∧ q a :=
  sorry

protected theorem or {α : Type u_1} [primcodable α] {p : α → Prop} {q : α → Prop} [decidable_pred p]
    [decidable_pred q] (hp : primrec_pred p) (hq : primrec_pred q) :
    primrec_pred fun (a : α) => p a ∨ q a :=
  sorry

protected theorem eq {α : Type u_1} [primcodable α] [DecidableEq α] : primrec_rel Eq := sorry

theorem nat_lt : primrec_rel Less := sorry

theorem option_guard {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β]
    {p : α → β → Prop} [(a : α) → (b : β) → Decidable (p a b)] (hp : primrec_rel p) {f : α → β}
    (hf : primrec f) : primrec fun (a : α) => option.guard (p a) (f a) :=
  ite (primrec_rel.comp hp primrec.id hf) (iff.mpr option_some_iff hf) (const none)

theorem option_orelse {α : Type u_1} [primcodable α] : primrec₂ has_orelse.orelse := sorry

protected theorem decode2 {α : Type u_1} [primcodable α] : primrec (encodable.decode2 α) :=
  option_bind primrec.decode
    (option_guard (primrec_rel.comp primrec.eq (iff.mpr encode_iff snd) (comp fst fst)) snd)

theorem list_find_index₁ {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β]
    {p : α → β → Prop} [(a : α) → (b : β) → Decidable (p a b)] (hp : primrec_rel p) (l : List β) :
    primrec fun (a : α) => list.find_index (p a) l :=
  sorry

theorem list_index_of₁ {α : Type u_1} [primcodable α] [DecidableEq α] (l : List α) :
    primrec fun (a : α) => list.index_of a l :=
  list_find_index₁ primrec.eq l

theorem dom_fintype {α : Type u_1} {σ : Type u_5} [primcodable α] [primcodable σ] [fintype α]
    (f : α → σ) : primrec f :=
  sorry

theorem nat_bodd_div2 : primrec nat.bodd_div2 := sorry

theorem nat_bodd : primrec nat.bodd := comp fst nat_bodd_div2

theorem nat_div2 : primrec nat.div2 := comp snd nat_bodd_div2

theorem nat_bit0 : primrec bit0 := primrec₂.comp nat_add primrec.id primrec.id

theorem nat_bit1 : primrec bit1 := primrec₂.comp nat_add nat_bit0 (const 1)

theorem nat_bit : primrec₂ nat.bit := sorry

theorem nat_div_mod : primrec₂ fun (n k : ℕ) => (n / k, n % k) := sorry

theorem nat_div : primrec₂ Div.div := comp₂ fst nat_div_mod

theorem nat_mod : primrec₂ Mod.mod := comp₂ snd nat_div_mod

end primrec


namespace primcodable


protected instance sum {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] :
    primcodable (α ⊕ β) :=
  mk sorry

protected instance list {α : Type u_1} [primcodable α] : primcodable (List α) := mk sorry

end primcodable


namespace primrec


theorem sum_inl {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] : primrec sum.inl :=
  iff.mp encode_iff (comp nat_bit0 primrec.encode)

theorem sum_inr {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] : primrec sum.inr :=
  iff.mp encode_iff (comp nat_bit1 primrec.encode)

theorem sum_cases {α : Type u_1} {β : Type u_2} {γ : Type u_3} {σ : Type u_4} [primcodable α]
    [primcodable β] [primcodable γ] [primcodable σ] {f : α → β ⊕ γ} {g : α → β → σ} {h : α → γ → σ}
    (hf : primrec f) (hg : primrec₂ g) (hh : primrec₂ h) :
    primrec fun (a : α) => sum.cases_on (f a) (g a) (h a) :=
  sorry

theorem list_cons {α : Type u_1} [primcodable α] : primrec₂ List.cons :=
  list_cons' (primcodable.prim (List α))

theorem list_cases {α : Type u_1} {β : Type u_2} {σ : Type u_4} [primcodable α] [primcodable β]
    [primcodable σ] {f : α → List β} {g : α → σ} {h : α → β × List β → σ} :
    primrec f →
        primrec g →
          primrec₂ h →
            primrec
              fun (a : α) => list.cases_on (f a) (g a) fun (b : β) (l : List β) => h a (b, l) :=
  list_cases' (primcodable.prim (List β))

theorem list_foldl {α : Type u_1} {β : Type u_2} {σ : Type u_4} [primcodable α] [primcodable β]
    [primcodable σ] {f : α → List β} {g : α → σ} {h : α → σ × β → σ} :
    primrec f →
        primrec g →
          primrec₂ h →
            primrec fun (a : α) => list.foldl (fun (s : σ) (b : β) => h a (s, b)) (g a) (f a) :=
  list_foldl' (primcodable.prim (List β))

theorem list_reverse {α : Type u_1} [primcodable α] : primrec list.reverse :=
  list_reverse' (primcodable.prim (List α))

theorem list_foldr {α : Type u_1} {β : Type u_2} {σ : Type u_4} [primcodable α] [primcodable β]
    [primcodable σ] {f : α → List β} {g : α → σ} {h : α → β × σ → σ} (hf : primrec f)
    (hg : primrec g) (hh : primrec₂ h) :
    primrec fun (a : α) => list.foldr (fun (b : β) (s : σ) => h a (b, s)) (g a) (f a) :=
  sorry

theorem list_head' {α : Type u_1} [primcodable α] : primrec list.head' := sorry

theorem list_head {α : Type u_1} [primcodable α] [Inhabited α] : primrec list.head :=
  of_eq (comp option_iget list_head') fun (l : List α) => Eq.symm (list.head_eq_head' l)

theorem list_tail {α : Type u_1} [primcodable α] : primrec list.tail := sorry

theorem list_rec {α : Type u_1} {β : Type u_2} {σ : Type u_4} [primcodable α] [primcodable β]
    [primcodable σ] {f : α → List β} {g : α → σ} {h : α → β × List β × σ → σ} (hf : primrec f)
    (hg : primrec g) (hh : primrec₂ h) :
    primrec
        fun (a : α) =>
          list.rec_on (f a) (g a) fun (b : β) (l : List β) (IH : σ) => h a (b, l, IH) :=
  sorry

theorem list_nth {α : Type u_1} [primcodable α] : primrec₂ list.nth := sorry

theorem list_inth {α : Type u_1} [primcodable α] [Inhabited α] : primrec₂ list.inth :=
  comp₂ option_iget list_nth

theorem list_append {α : Type u_1} [primcodable α] : primrec₂ append := sorry

theorem list_concat {α : Type u_1} [primcodable α] :
    primrec₂ fun (l : List α) (a : α) => l ++ [a] :=
  primrec₂.comp list_append fst (primrec₂.comp list_cons snd (const []))

theorem list_map {α : Type u_1} {β : Type u_2} {σ : Type u_4} [primcodable α] [primcodable β]
    [primcodable σ] {f : α → List β} {g : α → β → σ} (hf : primrec f) (hg : primrec₂ g) :
    primrec fun (a : α) => list.map (g a) (f a) :=
  sorry

theorem list_range : primrec list.range := sorry

theorem list_join {α : Type u_1} [primcodable α] : primrec list.join := sorry

theorem list_length {α : Type u_1} [primcodable α] : primrec list.length := sorry

theorem list_find_index {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β]
    {f : α → List β} {p : α → β → Prop} [(a : α) → (b : β) → Decidable (p a b)] (hf : primrec f)
    (hp : primrec_rel p) : primrec fun (a : α) => list.find_index (p a) (f a) :=
  sorry

theorem list_index_of {α : Type u_1} [primcodable α] [DecidableEq α] : primrec₂ list.index_of :=
  to₂ (list_find_index snd (primrec_rel.comp₂ primrec.eq (to₂ (comp fst fst)) (to₂ snd)))

theorem nat_strong_rec {α : Type u_1} {σ : Type u_4} [primcodable α] [primcodable σ] (f : α → ℕ → σ)
    {g : α → List σ → Option σ} (hg : primrec₂ g)
    (H : ∀ (a : α) (n : ℕ), g a (list.map (f a) (list.range n)) = some (f a n)) : primrec₂ f :=
  sorry

end primrec


namespace primcodable


def subtype {α : Type u_1} [primcodable α] {p : α → Prop} [decidable_pred p] (hp : primrec_pred p) :
    primcodable (Subtype p) :=
  mk sorry

protected instance fin {n : ℕ} : primcodable (fin n) :=
  of_equiv (Subtype fun (a : ℕ) => id a < n) (equiv.fin_equiv_subtype n)

protected instance vector {α : Type u_1} [primcodable α] {n : ℕ} : primcodable (vector α n) :=
  subtype sorry

protected instance fin_arrow {α : Type u_1} [primcodable α] {n : ℕ} : primcodable (fin n → α) :=
  of_equiv (vector α n) (equiv.symm (equiv.vector_equiv_fin α n))

protected instance array {α : Type u_1} [primcodable α] {n : ℕ} : primcodable (array n α) :=
  of_equiv (fin n → α) (equiv.array_equiv_fin n α)

protected instance ulower {α : Type u_1} [primcodable α] : primcodable (ulower α) :=
  (fun (this : primrec_pred fun (n : ℕ) => encodable.decode2 α n ≠ none) => subtype sorry) sorry

end primcodable


namespace primrec


theorem subtype_val {α : Type u_1} [primcodable α] {p : α → Prop} [decidable_pred p]
    {hp : primrec_pred p} : primrec subtype.val :=
  sorry

theorem subtype_val_iff {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] {p : β → Prop}
    [decidable_pred p] {hp : primrec_pred p} {f : α → Subtype p} :
    (primrec fun (a : α) => subtype.val (f a)) ↔ primrec f :=
  sorry

theorem subtype_mk {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] {p : β → Prop}
    [decidable_pred p] {hp : primrec_pred p} {f : α → β} {h : ∀ (a : α), p (f a)} (hf : primrec f) :
    primrec fun (a : α) => { val := f a, property := h a } :=
  iff.mp subtype_val_iff hf

theorem option_get {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] {f : α → Option β}
    {h : ∀ (a : α), ↥(option.is_some (f a))} :
    primrec f → primrec fun (a : α) => option.get (h a) :=
  sorry

theorem ulower_down {α : Type u_1} [primcodable α] : primrec ulower.down :=
  subtype_mk primrec.encode

theorem ulower_up {α : Type u_1} [primcodable α] : primrec ulower.up :=
  option_get (comp primrec.decode2 subtype_val)

theorem fin_val_iff {α : Type u_1} [primcodable α] {n : ℕ} {f : α → fin n} :
    (primrec fun (a : α) => subtype.val (f a)) ↔ primrec f :=
  iff.trans (iff.trans (iff.refl (primrec fun (a : α) => subtype.val (f a))) subtype_val_iff)
    (of_equiv_iff (equiv.fin_equiv_subtype n))

theorem fin_val {n : ℕ} : primrec coe := iff.mpr fin_val_iff primrec.id

theorem fin_succ {n : ℕ} : primrec fin.succ := sorry

theorem vector_to_list {α : Type u_1} [primcodable α] {n : ℕ} : primrec vector.to_list :=
  subtype_val

theorem vector_to_list_iff {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] {n : ℕ}
    {f : α → vector β n} : (primrec fun (a : α) => vector.to_list (f a)) ↔ primrec f :=
  subtype_val_iff

theorem vector_cons {α : Type u_1} [primcodable α] {n : ℕ} : primrec₂ vector.cons := sorry

theorem vector_length {α : Type u_1} [primcodable α] {n : ℕ} : primrec vector.length := const n

theorem vector_head {α : Type u_1} [primcodable α] {n : ℕ} : primrec vector.head := sorry

theorem vector_tail {α : Type u_1} [primcodable α] {n : ℕ} : primrec vector.tail := sorry

theorem vector_nth {α : Type u_1} [primcodable α] {n : ℕ} : primrec₂ vector.nth := sorry

theorem list_of_fn {α : Type u_1} {σ : Type u_4} [primcodable α] [primcodable σ] {n : ℕ}
    {f : fin n → α → σ} :
    (∀ (i : fin n), primrec (f i)) → primrec fun (a : α) => list.of_fn fun (i : fin n) => f i a :=
  sorry

theorem vector_of_fn {α : Type u_1} {σ : Type u_4} [primcodable α] [primcodable σ] {n : ℕ}
    {f : fin n → α → σ} (hf : ∀ (i : fin n), primrec (f i)) :
    primrec fun (a : α) => vector.of_fn fun (i : fin n) => f i a :=
  sorry

theorem vector_nth' {α : Type u_1} [primcodable α] {n : ℕ} : primrec vector.nth := of_equiv_symm

theorem vector_of_fn' {α : Type u_1} [primcodable α] {n : ℕ} : primrec vector.of_fn := of_equiv

theorem fin_app {σ : Type u_4} [primcodable σ] {n : ℕ} : primrec₂ id := sorry

theorem fin_curry₁ {α : Type u_1} {σ : Type u_4} [primcodable α] [primcodable σ] {n : ℕ}
    {f : fin n → α → σ} : primrec₂ f ↔ ∀ (i : fin n), primrec (f i) :=
  sorry

theorem fin_curry {α : Type u_1} {σ : Type u_4} [primcodable α] [primcodable σ] {n : ℕ}
    {f : α → fin n → σ} : primrec f ↔ primrec₂ f :=
  sorry

end primrec


namespace nat


/-- An alternative inductive definition of `primrec` which
  does not use the pairing function on ℕ, and so has to
  work with n-ary functions on ℕ instead of unary functions.
  We prove that this is equivalent to the regular notion
  in `to_prim` and `of_prim`. -/
inductive primrec' : {n : ℕ} → (vector ℕ n → ℕ) → Prop where
| zero : primrec' fun (_x : vector ℕ 0) => 0
| succ : primrec' fun (v : vector ℕ 1) => Nat.succ (vector.head v)
| nth : ∀ {n : ℕ} (i : fin n), primrec' fun (v : vector ℕ n) => vector.nth v i
| comp :
    ∀ {m n : ℕ} {f : vector ℕ n → ℕ} (g : fin n → vector ℕ m → ℕ),
      primrec' f →
        (∀ (i : fin n), primrec' (g i)) →
          primrec' fun (a : vector ℕ m) => f (vector.of_fn fun (i : fin n) => g i a)
| prec :
    ∀ {n : ℕ} {f : vector ℕ n → ℕ} {g : vector ℕ (n + bit0 1) → ℕ},
      primrec' f →
        primrec' g →
          primrec'
            fun (v : vector ℕ (n + 1)) =>
              elim (f (vector.tail v)) (fun (y IH : ℕ) => g (y::ᵥIH::ᵥvector.tail v))
                (vector.head v)

end nat


namespace nat.primrec'


theorem to_prim {n : ℕ} {f : vector ℕ n → ℕ} (pf : primrec' f) : primrec f := sorry

theorem of_eq {n : ℕ} {f : vector ℕ n → ℕ} {g : vector ℕ n → ℕ} (hf : primrec' f)
    (H : ∀ (i : vector ℕ n), f i = g i) : primrec' g :=
  funext H ▸ hf

theorem const {n : ℕ} (m : ℕ) : primrec' fun (v : vector ℕ n) => m := sorry

theorem head {n : ℕ} : primrec' vector.head := sorry

theorem tail {n : ℕ} {f : vector ℕ n → ℕ} (hf : primrec' f) :
    primrec' fun (v : vector ℕ (Nat.succ n)) => f (vector.tail v) :=
  sorry

def vec {n : ℕ} {m : ℕ} (f : vector ℕ n → vector ℕ m) :=
  ∀ (i : fin m), primrec' fun (v : vector ℕ n) => vector.nth (f v) i

protected theorem nil {n : ℕ} : vec fun (_x : vector ℕ n) => vector.nil :=
  fun (i : fin 0) => fin.elim0 i

protected theorem cons {n : ℕ} {m : ℕ} {f : vector ℕ n → ℕ} {g : vector ℕ n → vector ℕ m}
    (hf : primrec' f) (hg : vec g) : vec fun (v : vector ℕ n) => f v::ᵥg v :=
  sorry

theorem idv {n : ℕ} : vec id := nth

theorem comp' {n : ℕ} {m : ℕ} {f : vector ℕ m → ℕ} {g : vector ℕ n → vector ℕ m} (hf : primrec' f)
    (hg : vec g) : primrec' fun (v : vector ℕ n) => f (g v) :=
  sorry

theorem comp₁ (f : ℕ → ℕ) (hf : primrec' fun (v : vector ℕ 1) => f (vector.head v)) {n : ℕ}
    {g : vector ℕ n → ℕ} (hg : primrec' g) : primrec' fun (v : vector ℕ n) => f (g v) :=
  comp (fun (i : fin 1) => g) hf fun (i : fin 1) => hg

theorem comp₂ (f : ℕ → ℕ → ℕ)
    (hf : primrec' fun (v : vector ℕ (bit0 1)) => f (vector.head v) (vector.head (vector.tail v)))
    {n : ℕ} {g : vector ℕ n → ℕ} {h : vector ℕ n → ℕ} (hg : primrec' g) (hh : primrec' h) :
    primrec' fun (v : vector ℕ n) => f (g v) (h v) :=
  sorry

theorem prec' {n : ℕ} {f : vector ℕ n → ℕ} {g : vector ℕ n → ℕ} {h : vector ℕ (n + bit0 1) → ℕ}
    (hf : primrec' f) (hg : primrec' g) (hh : primrec' h) :
    primrec' fun (v : vector ℕ n) => elim (g v) (fun (y IH : ℕ) => h (y::ᵥIH::ᵥv)) (f v) :=
  sorry

theorem pred : primrec' fun (v : vector ℕ 1) => Nat.pred (vector.head v) := sorry

theorem add : primrec' fun (v : vector ℕ (bit0 1)) => vector.head v + vector.head (vector.tail v) :=
  sorry

theorem sub : primrec' fun (v : vector ℕ (bit0 1)) => vector.head v - vector.head (vector.tail v) :=
  sorry

theorem mul : primrec' fun (v : vector ℕ (bit0 1)) => vector.head v * vector.head (vector.tail v) :=
  sorry

theorem if_lt {n : ℕ} {a : vector ℕ n → ℕ} {b : vector ℕ n → ℕ} {f : vector ℕ n → ℕ}
    {g : vector ℕ n → ℕ} (ha : primrec' a) (hb : primrec' b) (hf : primrec' f) (hg : primrec' g) :
    primrec' fun (v : vector ℕ n) => ite (a v < b v) (f v) (g v) :=
  sorry

theorem mkpair :
    primrec' fun (v : vector ℕ (bit0 1)) => mkpair (vector.head v) (vector.head (vector.tail v)) :=
  if_lt head (tail head) (comp₂ Add.add add (tail (comp₂ Mul.mul mul head head)) head)
    (comp₂ Add.add add (comp₂ Add.add add (comp₂ Mul.mul mul head head) head) (tail head))

protected theorem encode {n : ℕ} : primrec' encodable.encode := sorry

theorem sqrt : primrec' fun (v : vector ℕ 1) => sqrt (vector.head v) := sorry

theorem unpair₁ {n : ℕ} {f : vector ℕ n → ℕ} (hf : primrec' f) :
    primrec' fun (v : vector ℕ n) => prod.fst (unpair (f v)) :=
  sorry

theorem unpair₂ {n : ℕ} {f : vector ℕ n → ℕ} (hf : primrec' f) :
    primrec' fun (v : vector ℕ n) => prod.snd (unpair (f v)) :=
  sorry

theorem of_prim {n : ℕ} {f : vector ℕ n → ℕ} : primrec f → primrec' f := sorry

theorem prim_iff {n : ℕ} {f : vector ℕ n → ℕ} : primrec' f ↔ primrec f :=
  { mp := to_prim, mpr := of_prim }

theorem prim_iff₁ {f : ℕ → ℕ} : (primrec' fun (v : vector ℕ 1) => f (vector.head v)) ↔ primrec f :=
  sorry

theorem prim_iff₂ {f : ℕ → ℕ → ℕ} :
    (primrec' fun (v : vector ℕ (bit0 1)) => f (vector.head v) (vector.head (vector.tail v))) ↔
        primrec₂ f :=
  sorry

theorem vec_iff {m : ℕ} {n : ℕ} {f : vector ℕ m → vector ℕ n} : vec f ↔ primrec f := sorry

end nat.primrec'


theorem primrec.nat_sqrt : primrec nat.sqrt := iff.mp nat.primrec'.prim_iff₁ nat.primrec'.sqrt

end Mathlib