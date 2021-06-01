/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.computability.primrec
import Mathlib.data.nat.psub
import Mathlib.data.pfun
import Mathlib.PostPort

universes u_1 u_2 u_3 u_4 u_5 

namespace Mathlib

/-!
# The partial recursive functions

The partial recursive functions are defined similarly to the primitive
recursive functions, but now all functions are partial, implemented
using the `roption` monad, and there is an additional operation, called
μ-recursion, which performs unbounded minimization.

## References

* [Mario Carneiro, *Formalizing computability theory via partial recursive functions*][carneiro2019]
-/

namespace nat


def rfind_x (p : ℕ →. Bool) (H : ∃ (n : ℕ), tt ∈ p n ∧ ∀ (k : ℕ), k < n → roption.dom (p k)) :
    Subtype fun (n : ℕ) => tt ∈ p n ∧ ∀ (m : ℕ), m < n → false ∈ p m :=
  (fun
      (this :
      (k : ℕ) →
        (∀ (n : ℕ), n < k → false ∈ p n) →
          Subtype fun (n : ℕ) => tt ∈ p n ∧ ∀ (m : ℕ), m < n → false ∈ p m) =>
      this 0 sorry)
    (well_founded.fix (wf_lbp p H)
      fun (m : ℕ)
        (IH :
        (y : ℕ) →
          lbp p y m →
            (∀ (n : ℕ), n < y → false ∈ p n) →
              Subtype fun (n : ℕ) => tt ∈ p n ∧ ∀ (m : ℕ), m < n → false ∈ p m)
        (al : ∀ (n : ℕ), n < m → false ∈ p n) =>
        (fun (_x : Bool) (e : roption.get (p m) sorry = _x) =>
            bool.cases_on _x (fun (e : roption.get (p m) sorry = false) => IH (m + 1) sorry sorry)
              (fun (e : roption.get (p m) sorry = tt) => { val := m, property := sorry }) e)
          (roption.get (p m) sorry) sorry)

def rfind (p : ℕ →. Bool) : roption ℕ :=
  roption.mk (∃ (n : ℕ), tt ∈ p n ∧ ∀ (k : ℕ), k < n → roption.dom (p k))
    fun (h : ∃ (n : ℕ), tt ∈ p n ∧ ∀ (k : ℕ), k < n → roption.dom (p k)) =>
      subtype.val (rfind_x p h)

theorem rfind_spec {p : ℕ →. Bool} {n : ℕ} (h : n ∈ rfind p) : tt ∈ p n :=
  Exists.snd h ▸ and.left (subtype.property (rfind_x p (Exists.fst h)))

theorem rfind_min {p : ℕ →. Bool} {n : ℕ} (h : n ∈ rfind p) {m : ℕ} : m < n → false ∈ p m :=
  Exists.snd h ▸ and.right (subtype.property (rfind_x p (Exists.fst h)))

@[simp] theorem rfind_dom {p : ℕ →. Bool} :
    roption.dom (rfind p) ↔ ∃ (n : ℕ), tt ∈ p n ∧ ∀ {m : ℕ}, m < n → roption.dom (p m) :=
  iff.rfl

theorem rfind_dom' {p : ℕ →. Bool} :
    roption.dom (rfind p) ↔ ∃ (n : ℕ), tt ∈ p n ∧ ∀ {m : ℕ}, m ≤ n → roption.dom (p m) :=
  sorry

@[simp] theorem mem_rfind {p : ℕ →. Bool} {n : ℕ} :
    n ∈ rfind p ↔ tt ∈ p n ∧ ∀ {m : ℕ}, m < n → false ∈ p m :=
  sorry

theorem rfind_min' {p : ℕ → Bool} {m : ℕ} (pm : ↥(p m)) : ∃ (n : ℕ), ∃ (H : n ∈ rfind ↑p), n ≤ m :=
  sorry

theorem rfind_zero_none (p : ℕ →. Bool) (p0 : p 0 = roption.none) : rfind p = roption.none := sorry

def rfind_opt {α : Type u_1} (f : ℕ → Option α) : roption α :=
  roption.bind (rfind ↑fun (n : ℕ) => option.is_some (f n)) fun (n : ℕ) => ↑(f n)

theorem rfind_opt_spec {α : Type u_1} {f : ℕ → Option α} {a : α} (h : a ∈ rfind_opt f) :
    ∃ (n : ℕ), a ∈ f n :=
  sorry

theorem rfind_opt_dom {α : Type u_1} {f : ℕ → Option α} :
    roption.dom (rfind_opt f) ↔ ∃ (n : ℕ), ∃ (a : α), a ∈ f n :=
  sorry

theorem rfind_opt_mono {α : Type u_1} {f : ℕ → Option α}
    (H : ∀ {a : α} {m n : ℕ}, m ≤ n → a ∈ f m → a ∈ f n) {a : α} :
    a ∈ rfind_opt f ↔ ∃ (n : ℕ), a ∈ f n :=
  sorry

inductive partrec : (ℕ →. ℕ) → Prop where
| zero : partrec (pure 0)
| succ : partrec ↑Nat.succ
| left : partrec ↑fun (n : ℕ) => prod.fst (unpair n)
| right : partrec ↑fun (n : ℕ) => prod.snd (unpair n)
| pair : ∀ {f g : ℕ →. ℕ}, partrec f → partrec g → partrec fun (n : ℕ) => mkpair <$> f n <*> g n
| comp : ∀ {f g : ℕ →. ℕ}, partrec f → partrec g → partrec fun (n : ℕ) => g n >>= f
| prec :
    ∀ {f g : ℕ →. ℕ},
      partrec f →
        partrec g →
          partrec
            (unpaired
              fun (a n : ℕ) =>
                elim (f a)
                  (fun (y : ℕ) (IH : roption ℕ) =>
                    do 
                      let i ← IH 
                      g (mkpair a (mkpair y i)))
                  n)
| rfind :
    ∀ {f : ℕ →. ℕ},
      partrec f →
        partrec
          fun (a : ℕ) => rfind fun (n : ℕ) => (fun (m : ℕ) => to_bool (m = 0)) <$> f (mkpair a n)

namespace partrec


theorem of_eq {f : ℕ →. ℕ} {g : ℕ →. ℕ} (hf : partrec f) (H : ∀ (n : ℕ), f n = g n) : partrec g :=
  funext H ▸ hf

theorem of_eq_tot {f : ℕ →. ℕ} {g : ℕ → ℕ} (hf : partrec f) (H : ∀ (n : ℕ), g n ∈ f n) :
    partrec ↑g :=
  of_eq hf fun (n : ℕ) => iff.mpr roption.eq_some_iff (H n)

theorem of_primrec {f : ℕ → ℕ} (hf : primrec f) : partrec ↑f := sorry

protected theorem some : partrec roption.some := of_primrec primrec.id

theorem none : partrec fun (n : ℕ) => roption.none := sorry

theorem prec' {f : ℕ →. ℕ} {g : ℕ →. ℕ} {h : ℕ →. ℕ} (hf : partrec f) (hg : partrec g)
    (hh : partrec h) :
    partrec
        fun (a : ℕ) =>
          roption.bind (f a)
            fun (n : ℕ) =>
              elim (g a)
                (fun (y : ℕ) (IH : roption ℕ) =>
                  do 
                    let i ← IH 
                    h (mkpair a (mkpair y i)))
                n :=
  sorry

theorem ppred : partrec fun (n : ℕ) => ↑(ppred n) := sorry

end partrec


end nat


def partrec {α : Type u_1} {σ : Type u_2} [primcodable α] [primcodable σ] (f : α →. σ) :=
  nat.partrec
    fun (n : ℕ) =>
      roption.bind ↑(encodable.decode α n) fun (a : α) => roption.map encodable.encode (f a)

def partrec₂ {α : Type u_1} {β : Type u_2} {σ : Type u_3} [primcodable α] [primcodable β]
    [primcodable σ] (f : α → β →. σ) :=
  partrec fun (p : α × β) => f (prod.fst p) (prod.snd p)

def computable {α : Type u_1} {σ : Type u_2} [primcodable α] [primcodable σ] (f : α → σ) :=
  partrec ↑f

def computable₂ {α : Type u_1} {β : Type u_2} {σ : Type u_3} [primcodable α] [primcodable β]
    [primcodable σ] (f : α → β → σ) :=
  computable fun (p : α × β) => f (prod.fst p) (prod.snd p)

theorem primrec.to_comp {α : Type u_1} {σ : Type u_2} [primcodable α] [primcodable σ] {f : α → σ}
    (hf : primrec f) : computable f :=
  sorry

theorem primrec₂.to_comp {α : Type u_1} {β : Type u_2} {σ : Type u_3} [primcodable α]
    [primcodable β] [primcodable σ] {f : α → β → σ} (hf : primrec₂ f) : computable₂ f :=
  primrec.to_comp hf

theorem computable.part {α : Type u_1} {σ : Type u_2} [primcodable α] [primcodable σ] {f : α → σ}
    (hf : computable f) : partrec ↑f :=
  hf

theorem computable₂.part {α : Type u_1} {β : Type u_2} {σ : Type u_3} [primcodable α]
    [primcodable β] [primcodable σ] {f : α → β → σ} (hf : computable₂ f) :
    partrec₂ fun (a : α) => ↑(f a) :=
  hf

namespace computable


theorem of_eq {α : Type u_1} {σ : Type u_4} [primcodable α] [primcodable σ] {f : α → σ} {g : α → σ}
    (hf : computable f) (H : ∀ (n : α), f n = g n) : computable g :=
  funext H ▸ hf

theorem const {α : Type u_1} {σ : Type u_4} [primcodable α] [primcodable σ] (s : σ) :
    computable fun (a : α) => s :=
  primrec.to_comp (primrec.const s)

theorem of_option {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] {f : α → Option β}
    (hf : computable f) : partrec fun (a : α) => ↑(f a) :=
  sorry

theorem to₂ {α : Type u_1} {β : Type u_2} {σ : Type u_4} [primcodable α] [primcodable β]
    [primcodable σ] {f : α × β → σ} (hf : computable f) :
    computable₂ fun (a : α) (b : β) => f (a, b) :=
  of_eq hf
    fun (_x : α × β) =>
      (fun (_a : α × β) =>
          prod.cases_on _a fun (fst : α) (snd : β) => idRhs (f (fst, snd) = f (fst, snd)) rfl)
        _x

protected theorem id {α : Type u_1} [primcodable α] : computable id := primrec.to_comp primrec.id

theorem fst {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] : computable prod.fst :=
  primrec.to_comp primrec.fst

theorem snd {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] : computable prod.snd :=
  primrec.to_comp primrec.snd

theorem pair {α : Type u_1} {β : Type u_2} {γ : Type u_3} [primcodable α] [primcodable β]
    [primcodable γ] {f : α → β} {g : α → γ} (hf : computable f) (hg : computable g) :
    computable fun (a : α) => (f a, g a) :=
  sorry

theorem unpair : computable nat.unpair := primrec.to_comp primrec.unpair

theorem succ : computable Nat.succ := primrec.to_comp primrec.succ

theorem pred : computable Nat.pred := primrec.to_comp primrec.pred

theorem nat_bodd : computable nat.bodd := primrec.to_comp primrec.nat_bodd

theorem nat_div2 : computable nat.div2 := primrec.to_comp primrec.nat_div2

theorem sum_inl {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] :
    computable sum.inl :=
  primrec.to_comp primrec.sum_inl

theorem sum_inr {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] :
    computable sum.inr :=
  primrec.to_comp primrec.sum_inr

theorem list_cons {α : Type u_1} [primcodable α] : computable₂ List.cons :=
  primrec₂.to_comp primrec.list_cons

theorem list_reverse {α : Type u_1} [primcodable α] : computable list.reverse :=
  primrec.to_comp primrec.list_reverse

theorem list_nth {α : Type u_1} [primcodable α] : computable₂ list.nth :=
  primrec₂.to_comp primrec.list_nth

theorem list_append {α : Type u_1} [primcodable α] : computable₂ append :=
  primrec₂.to_comp primrec.list_append

theorem list_concat {α : Type u_1} [primcodable α] :
    computable₂ fun (l : List α) (a : α) => l ++ [a] :=
  primrec₂.to_comp primrec.list_concat

theorem list_length {α : Type u_1} [primcodable α] : computable list.length :=
  primrec.to_comp primrec.list_length

theorem vector_cons {α : Type u_1} [primcodable α] {n : ℕ} : computable₂ vector.cons :=
  primrec₂.to_comp primrec.vector_cons

theorem vector_to_list {α : Type u_1} [primcodable α] {n : ℕ} : computable vector.to_list :=
  primrec.to_comp primrec.vector_to_list

theorem vector_length {α : Type u_1} [primcodable α] {n : ℕ} : computable vector.length :=
  primrec.to_comp primrec.vector_length

theorem vector_head {α : Type u_1} [primcodable α] {n : ℕ} : computable vector.head :=
  primrec.to_comp primrec.vector_head

theorem vector_tail {α : Type u_1} [primcodable α] {n : ℕ} : computable vector.tail :=
  primrec.to_comp primrec.vector_tail

theorem vector_nth {α : Type u_1} [primcodable α] {n : ℕ} : computable₂ vector.nth :=
  primrec₂.to_comp primrec.vector_nth

theorem vector_nth' {α : Type u_1} [primcodable α] {n : ℕ} : computable vector.nth :=
  primrec.to_comp primrec.vector_nth'

theorem vector_of_fn' {α : Type u_1} [primcodable α] {n : ℕ} : computable vector.of_fn :=
  primrec.to_comp primrec.vector_of_fn'

theorem fin_app {σ : Type u_4} [primcodable σ] {n : ℕ} : computable₂ id :=
  primrec₂.to_comp primrec.fin_app

protected theorem encode {α : Type u_1} [primcodable α] : computable encodable.encode :=
  primrec.to_comp primrec.encode

protected theorem decode {α : Type u_1} [primcodable α] : computable (encodable.decode α) :=
  primrec.to_comp primrec.decode

protected theorem of_nat (α : Type u_1) [denumerable α] : computable (denumerable.of_nat α) :=
  primrec.to_comp (primrec.of_nat α)

theorem encode_iff {α : Type u_1} {σ : Type u_4} [primcodable α] [primcodable σ] {f : α → σ} :
    (computable fun (a : α) => encodable.encode (f a)) ↔ computable f :=
  iff.rfl

theorem option_some {α : Type u_1} [primcodable α] : computable some :=
  primrec.to_comp primrec.option_some

end computable


namespace partrec


theorem of_eq {α : Type u_1} {σ : Type u_4} [primcodable α] [primcodable σ] {f : α →. σ}
    {g : α →. σ} (hf : partrec f) (H : ∀ (n : α), f n = g n) : partrec g :=
  funext H ▸ hf

theorem of_eq_tot {α : Type u_1} {σ : Type u_4} [primcodable α] [primcodable σ] {f : α →. σ}
    {g : α → σ} (hf : partrec f) (H : ∀ (n : α), g n ∈ f n) : computable g :=
  of_eq hf fun (a : α) => iff.mpr roption.eq_some_iff (H a)

theorem none {α : Type u_1} {σ : Type u_4} [primcodable α] [primcodable σ] :
    partrec fun (a : α) => roption.none :=
  sorry

protected theorem some {α : Type u_1} [primcodable α] : partrec roption.some := computable.id

theorem const' {α : Type u_1} {σ : Type u_4} [primcodable α] [primcodable σ] (s : roption σ) :
    partrec fun (a : α) => s :=
  of_eq (computable.of_option (computable.const (roption.to_option s)))
    fun (a : α) => roption.of_to_option s

protected theorem bind {α : Type u_1} {β : Type u_2} {σ : Type u_4} [primcodable α] [primcodable β]
    [primcodable σ] {f : α →. β} {g : α → β →. σ} (hf : partrec f) (hg : partrec₂ g) :
    partrec fun (a : α) => roption.bind (f a) (g a) :=
  sorry

theorem map {α : Type u_1} {β : Type u_2} {σ : Type u_4} [primcodable α] [primcodable β]
    [primcodable σ] {f : α →. β} {g : α → β → σ} (hf : partrec f) (hg : computable₂ g) :
    partrec fun (a : α) => roption.map (g a) (f a) :=
  sorry

theorem to₂ {α : Type u_1} {β : Type u_2} {σ : Type u_4} [primcodable α] [primcodable β]
    [primcodable σ] {f : α × β →. σ} (hf : partrec f) : partrec₂ fun (a : α) (b : β) => f (a, b) :=
  of_eq hf
    fun (_x : α × β) =>
      (fun (_a : α × β) =>
          prod.cases_on _a fun (fst : α) (snd : β) => idRhs (f (fst, snd) = f (fst, snd)) rfl)
        _x

theorem nat_elim {α : Type u_1} {σ : Type u_4} [primcodable α] [primcodable σ] {f : α → ℕ}
    {g : α →. σ} {h : α → ℕ × σ →. σ} (hf : computable f) (hg : partrec g) (hh : partrec₂ h) :
    partrec
        fun (a : α) =>
          nat.elim (g a) (fun (y : ℕ) (IH : roption σ) => roption.bind IH fun (i : σ) => h a (y, i))
            (f a) :=
  sorry

theorem comp {α : Type u_1} {β : Type u_2} {σ : Type u_4} [primcodable α] [primcodable β]
    [primcodable σ] {f : β →. σ} {g : α → β} (hf : partrec f) (hg : computable g) :
    partrec fun (a : α) => f (g a) :=
  sorry

theorem nat_iff {f : ℕ →. ℕ} : partrec f ↔ nat.partrec f := sorry

theorem map_encode_iff {α : Type u_1} {σ : Type u_4} [primcodable α] [primcodable σ] {f : α →. σ} :
    (partrec fun (a : α) => roption.map encodable.encode (f a)) ↔ partrec f :=
  iff.rfl

end partrec


namespace partrec₂


theorem unpaired {α : Type u_1} [primcodable α] {f : ℕ → ℕ →. α} :
    partrec (nat.unpaired f) ↔ partrec₂ f :=
  sorry

theorem unpaired' {f : ℕ → ℕ →. ℕ} : nat.partrec (nat.unpaired f) ↔ partrec₂ f :=
  iff.trans (iff.symm partrec.nat_iff) unpaired

theorem comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} {σ : Type u_5} [primcodable α]
    [primcodable β] [primcodable γ] [primcodable σ] {f : β → γ →. σ} {g : α → β} {h : α → γ}
    (hf : partrec₂ f) (hg : computable g) (hh : computable h) :
    partrec fun (a : α) => f (g a) (h a) :=
  partrec.comp hf (computable.pair hg hh)

theorem comp₂ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {σ : Type u_5}
    [primcodable α] [primcodable β] [primcodable γ] [primcodable δ] [primcodable σ] {f : γ → δ →. σ}
    {g : α → β → γ} {h : α → β → δ} (hf : partrec₂ f) (hg : computable₂ g) (hh : computable₂ h) :
    partrec₂ fun (a : α) (b : β) => f (g a b) (h a b) :=
  comp hf hg hh

end partrec₂


namespace computable


theorem comp {α : Type u_1} {β : Type u_2} {σ : Type u_4} [primcodable α] [primcodable β]
    [primcodable σ] {f : β → σ} {g : α → β} (hf : computable f) (hg : computable g) :
    computable fun (a : α) => f (g a) :=
  partrec.comp hf hg

theorem comp₂ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {σ : Type u_4} [primcodable α]
    [primcodable β] [primcodable γ] [primcodable σ] {f : γ → σ} {g : α → β → γ} (hf : computable f)
    (hg : computable₂ g) : computable₂ fun (a : α) (b : β) => f (g a b) :=
  comp hf hg

end computable


namespace computable₂


theorem comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} {σ : Type u_5} [primcodable α]
    [primcodable β] [primcodable γ] [primcodable σ] {f : β → γ → σ} {g : α → β} {h : α → γ}
    (hf : computable₂ f) (hg : computable g) (hh : computable h) :
    computable fun (a : α) => f (g a) (h a) :=
  computable.comp hf (computable.pair hg hh)

theorem comp₂ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {σ : Type u_5}
    [primcodable α] [primcodable β] [primcodable γ] [primcodable δ] [primcodable σ] {f : γ → δ → σ}
    {g : α → β → γ} {h : α → β → δ} (hf : computable₂ f) (hg : computable₂ g) (hh : computable₂ h) :
    computable₂ fun (a : α) (b : β) => f (g a b) (h a b) :=
  comp hf hg hh

end computable₂


namespace partrec


theorem rfind {α : Type u_1} [primcodable α] {p : α → ℕ →. Bool} (hp : partrec₂ p) :
    partrec fun (a : α) => nat.rfind (p a) :=
  sorry

theorem rfind_opt {α : Type u_1} {σ : Type u_4} [primcodable α] [primcodable σ]
    {f : α → ℕ → Option σ} (hf : computable₂ f) : partrec fun (a : α) => nat.rfind_opt (f a) :=
  partrec.bind
    (rfind (to₂ (computable.part (computable.comp (primrec.to_comp primrec.option_is_some) hf))))
    (computable.of_option hf)

theorem nat_cases_right {α : Type u_1} {σ : Type u_4} [primcodable α] [primcodable σ] {f : α → ℕ}
    {g : α → σ} {h : α → ℕ →. σ} (hf : computable f) (hg : computable g) (hh : partrec₂ h) :
    partrec fun (a : α) => nat.cases (roption.some (g a)) (h a) (f a) :=
  sorry

theorem bind_decode2_iff {α : Type u_1} {σ : Type u_4} [primcodable α] [primcodable σ]
    {f : α →. σ} :
    partrec f ↔
        nat.partrec
          fun (n : ℕ) =>
            roption.bind ↑(encodable.decode2 α n)
              fun (a : α) => roption.map encodable.encode (f a) :=
  sorry

theorem vector_m_of_fn {α : Type u_1} {σ : Type u_4} [primcodable α] [primcodable σ] {n : ℕ}
    {f : fin n → α →. σ} :
    (∀ (i : fin n), partrec (f i)) →
        partrec fun (a : α) => vector.m_of_fn fun (i : fin n) => f i a :=
  sorry

end partrec


@[simp] theorem vector.m_of_fn_roption_some {α : Type u_1} {n : ℕ} (f : fin n → α) :
    (vector.m_of_fn fun (i : fin n) => roption.some (f i)) = roption.some (vector.of_fn f) :=
  vector.m_of_fn_pure

namespace computable


theorem option_some_iff {α : Type u_1} {σ : Type u_4} [primcodable α] [primcodable σ] {f : α → σ} :
    (computable fun (a : α) => some (f a)) ↔ computable f :=
  sorry

theorem bind_decode_iff {α : Type u_1} {β : Type u_2} {σ : Type u_4} [primcodable α] [primcodable β]
    [primcodable σ] {f : α → β → Option σ} :
    (computable₂ fun (a : α) (n : ℕ) => option.bind (encodable.decode β n) (f a)) ↔ computable₂ f :=
  sorry

theorem map_decode_iff {α : Type u_1} {β : Type u_2} {σ : Type u_4} [primcodable α] [primcodable β]
    [primcodable σ] {f : α → β → σ} :
    (computable₂ fun (a : α) (n : ℕ) => option.map (f a) (encodable.decode β n)) ↔ computable₂ f :=
  iff.trans bind_decode_iff option_some_iff

theorem nat_elim {α : Type u_1} {σ : Type u_4} [primcodable α] [primcodable σ] {f : α → ℕ}
    {g : α → σ} {h : α → ℕ × σ → σ} (hf : computable f) (hg : computable g) (hh : computable₂ h) :
    computable fun (a : α) => nat.elim (g a) (fun (y : ℕ) (IH : σ) => h a (y, IH)) (f a) :=
  sorry

theorem nat_cases {α : Type u_1} {σ : Type u_4} [primcodable α] [primcodable σ] {f : α → ℕ}
    {g : α → σ} {h : α → ℕ → σ} (hf : computable f) (hg : computable g) (hh : computable₂ h) :
    computable fun (a : α) => nat.cases (g a) (h a) (f a) :=
  nat_elim hf hg (to₂ (computable₂.comp hh fst (comp fst snd)))

theorem cond {α : Type u_1} {σ : Type u_4} [primcodable α] [primcodable σ] {c : α → Bool}
    {f : α → σ} {g : α → σ} (hc : computable c) (hf : computable f) (hg : computable g) :
    computable fun (a : α) => cond (c a) (f a) (g a) :=
  sorry

theorem option_cases {α : Type u_1} {β : Type u_2} {σ : Type u_4} [primcodable α] [primcodable β]
    [primcodable σ] {o : α → Option β} {f : α → σ} {g : α → β → σ} (ho : computable o)
    (hf : computable f) (hg : computable₂ g) :
    computable fun (a : α) => option.cases_on (o a) (f a) (g a) :=
  sorry

theorem option_bind {α : Type u_1} {β : Type u_2} {σ : Type u_4} [primcodable α] [primcodable β]
    [primcodable σ] {f : α → Option β} {g : α → β → Option σ} (hf : computable f)
    (hg : computable₂ g) : computable fun (a : α) => option.bind (f a) (g a) :=
  sorry

theorem option_map {α : Type u_1} {β : Type u_2} {σ : Type u_4} [primcodable α] [primcodable β]
    [primcodable σ] {f : α → Option β} {g : α → β → σ} (hf : computable f) (hg : computable₂ g) :
    computable fun (a : α) => option.map (g a) (f a) :=
  option_bind hf (comp₂ option_some hg)

theorem option_get_or_else {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β]
    {f : α → Option β} {g : α → β} (hf : computable f) (hg : computable g) :
    computable fun (a : α) => option.get_or_else (f a) (g a) :=
  sorry

theorem subtype_mk {α : Type u_1} {β : Type u_2} [primcodable α] [primcodable β] {f : α → β}
    {p : β → Prop} [decidable_pred p] {h : ∀ (a : α), p (f a)} (hp : primrec_pred p)
    (hf : computable f) : computable fun (a : α) => { val := f a, property := h a } :=
  sorry

theorem sum_cases {α : Type u_1} {β : Type u_2} {γ : Type u_3} {σ : Type u_4} [primcodable α]
    [primcodable β] [primcodable γ] [primcodable σ] {f : α → β ⊕ γ} {g : α → β → σ} {h : α → γ → σ}
    (hf : computable f) (hg : computable₂ g) (hh : computable₂ h) :
    computable fun (a : α) => sum.cases_on (f a) (g a) (h a) :=
  sorry

theorem nat_strong_rec {α : Type u_1} {σ : Type u_4} [primcodable α] [primcodable σ] (f : α → ℕ → σ)
    {g : α → List σ → Option σ} (hg : computable₂ g)
    (H : ∀ (a : α) (n : ℕ), g a (list.map (f a) (list.range n)) = some (f a n)) : computable₂ f :=
  sorry

theorem list_of_fn {α : Type u_1} {σ : Type u_4} [primcodable α] [primcodable σ] {n : ℕ}
    {f : fin n → α → σ} :
    (∀ (i : fin n), computable (f i)) →
        computable fun (a : α) => list.of_fn fun (i : fin n) => f i a :=
  sorry

theorem vector_of_fn {α : Type u_1} {σ : Type u_4} [primcodable α] [primcodable σ] {n : ℕ}
    {f : fin n → α → σ} (hf : ∀ (i : fin n), computable (f i)) :
    computable fun (a : α) => vector.of_fn fun (i : fin n) => f i a :=
  sorry

end computable


namespace partrec


theorem option_some_iff {α : Type u_1} {σ : Type u_4} [primcodable α] [primcodable σ] {f : α →. σ} :
    (partrec fun (a : α) => roption.map some (f a)) ↔ partrec f :=
  sorry

theorem option_cases_right {α : Type u_1} {β : Type u_2} {σ : Type u_4} [primcodable α]
    [primcodable β] [primcodable σ] {o : α → Option β} {f : α → σ} {g : α → β →. σ}
    (ho : computable o) (hf : computable f) (hg : partrec₂ g) :
    partrec fun (a : α) => option.cases_on (o a) (roption.some (f a)) (g a) :=
  sorry

theorem sum_cases_right {α : Type u_1} {β : Type u_2} {γ : Type u_3} {σ : Type u_4} [primcodable α]
    [primcodable β] [primcodable γ] [primcodable σ] {f : α → β ⊕ γ} {g : α → β → σ} {h : α → γ →. σ}
    (hf : computable f) (hg : computable₂ g) (hh : partrec₂ h) :
    partrec fun (a : α) => sum.cases_on (f a) (fun (b : β) => roption.some (g a b)) (h a) :=
  sorry

theorem sum_cases_left {α : Type u_1} {β : Type u_2} {γ : Type u_3} {σ : Type u_4} [primcodable α]
    [primcodable β] [primcodable γ] [primcodable σ] {f : α → β ⊕ γ} {g : α → β →. σ} {h : α → γ → σ}
    (hf : computable f) (hg : partrec₂ g) (hh : computable₂ h) :
    partrec fun (a : α) => sum.cases_on (f a) (g a) fun (c : γ) => roption.some (h a c) :=
  sorry

theorem fix {α : Type u_1} {σ : Type u_4} [primcodable α] [primcodable σ] {f : α →. σ ⊕ α}
    (hf : partrec f) : partrec (pfun.fix f) :=
  sorry

end Mathlib