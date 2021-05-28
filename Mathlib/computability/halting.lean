/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.computability.partrec_code
import Mathlib.PostPort

universes u_1 u_4 u_2 u_3 

namespace Mathlib

/-!
# Computability theory and the halting problem

A universal partial recursive function, Rice's theorem, and the halting problem.

## References

* [Mario Carneiro, *Formalizing computability theory via partial recursive functions*][carneiro2019]
-/

namespace nat.partrec


theorem merge' {f : ℕ →. ℕ} {g : ℕ →. ℕ} (hf : partrec f) (hg : partrec g) : ∃ (h : ℕ →. ℕ),
  partrec h ∧
    ∀ (a : ℕ), (∀ (x : ℕ), x ∈ h a → x ∈ f a ∨ x ∈ g a) ∧ (roption.dom (h a) ↔ roption.dom (f a) ∨ roption.dom (g a)) := sorry

end nat.partrec


namespace partrec


theorem merge' {α : Type u_1} {σ : Type u_4} [primcodable α] [primcodable σ] {f : α →. σ} {g : α →. σ} (hf : partrec f) (hg : partrec g) : ∃ (k : α →. σ),
  partrec k ∧
    ∀ (a : α), (∀ (x : σ), x ∈ k a → x ∈ f a ∨ x ∈ g a) ∧ (roption.dom (k a) ↔ roption.dom (f a) ∨ roption.dom (g a)) := sorry

theorem merge {α : Type u_1} {σ : Type u_4} [primcodable α] [primcodable σ] {f : α →. σ} {g : α →. σ} (hf : partrec f) (hg : partrec g) (H : ∀ (a : α) (x : σ), x ∈ f a → ∀ (y : σ), y ∈ g a → x = y) : ∃ (k : α →. σ), partrec k ∧ ∀ (a : α) (x : σ), x ∈ k a ↔ x ∈ f a ∨ x ∈ g a := sorry

theorem cond {α : Type u_1} {σ : Type u_4} [primcodable α] [primcodable σ] {c : α → Bool} {f : α →. σ} {g : α →. σ} (hc : computable c) (hf : partrec f) (hg : partrec g) : partrec fun (a : α) => cond (c a) (f a) (g a) := sorry

theorem sum_cases {α : Type u_1} {β : Type u_2} {γ : Type u_3} {σ : Type u_4} [primcodable α] [primcodable β] [primcodable γ] [primcodable σ] {f : α → β ⊕ γ} {g : α → β →. σ} {h : α → γ →. σ} (hf : computable f) (hg : partrec₂ g) (hh : partrec₂ h) : partrec fun (a : α) => sum.cases_on (f a) (g a) (h a) := sorry

end partrec


/-- A computable predicate is one whose indicator function is computable. -/
def computable_pred {α : Type u_1} [primcodable α] (p : α → Prop)  :=
  Exists (computable fun (a : α) => to_bool (p a))

/-- A recursively enumerable predicate is one which is the domain of a computable partial function.
 -/
def re_pred {α : Type u_1} [primcodable α] (p : α → Prop)  :=
  partrec fun (a : α) => roption.assert (p a) fun (_x : p a) => roption.some Unit.unit

theorem computable_pred.of_eq {α : Type u_1} [primcodable α] {p : α → Prop} {q : α → Prop} (hp : computable_pred p) (H : ∀ (a : α), p a ↔ q a) : computable_pred q :=
  (funext fun (a : α) => propext (H a)) ▸ hp

namespace computable_pred


theorem computable_iff {α : Type u_1} [primcodable α] {p : α → Prop} : computable_pred p ↔ ∃ (f : α → Bool), computable f ∧ p = fun (a : α) => ↥(f a) := sorry

protected theorem not {α : Type u_1} [primcodable α] {p : α → Prop} (hp : computable_pred p) : computable_pred fun (a : α) => ¬p a := sorry

theorem to_re {α : Type u_1} [primcodable α] {p : α → Prop} (hp : computable_pred p) : re_pred p := sorry

theorem rice (C : set (ℕ →. ℕ)) (h : computable_pred fun (c : nat.partrec.code) => nat.partrec.code.eval c ∈ C) {f : ℕ →. ℕ} {g : ℕ →. ℕ} (hf : nat.partrec f) (hg : nat.partrec g) (fC : f ∈ C) : g ∈ C := sorry

theorem rice₂ (C : set nat.partrec.code) (H : ∀ (cf cg : nat.partrec.code), nat.partrec.code.eval cf = nat.partrec.code.eval cg → (cf ∈ C ↔ cg ∈ C)) : (computable_pred fun (c : nat.partrec.code) => c ∈ C) ↔ C = ∅ ∨ C = set.univ := sorry

theorem halting_problem (n : ℕ) : ¬computable_pred fun (c : nat.partrec.code) => roption.dom (nat.partrec.code.eval c n) :=
  fun (ᾰ : computable_pred fun (c : nat.partrec.code) => roption.dom (nat.partrec.code.eval c n)) =>
    idRhs ((fun (n : ℕ) => roption.none) ∈ set_of fun (f : ℕ →. ℕ) => roption.dom (f n))
      (rice (set_of fun (f : ℕ →. ℕ) => roption.dom (f n)) ᾰ nat.partrec.zero nat.partrec.none trivial)

-- Post's theorem on the equivalence of r.e., co-r.e. sets and

-- computable sets. The assumption that p is decidable is required

-- unless we assume Markov's principle or LEM.

theorem computable_iff_re_compl_re {α : Type u_1} [primcodable α] {p : α → Prop} [decidable_pred p] : computable_pred p ↔ re_pred p ∧ re_pred fun (a : α) => ¬p a := sorry

end computable_pred


namespace nat


/-- A simplified basis for `partrec`. -/
inductive partrec' : {n : ℕ} → (vector ℕ n →. ℕ) → Prop
where
| prim : ∀ {n : ℕ} {f : vector ℕ n → ℕ}, primrec' f → partrec' ↑f
| comp : ∀ {m n : ℕ} {f : vector ℕ n →. ℕ} (g : fin n → vector ℕ m →. ℕ),
  partrec' f →
    (∀ (i : fin n), partrec' (g i)) → partrec' fun (v : vector ℕ m) => (vector.m_of_fn fun (i : fin n) => g i v) >>= f
| rfind : ∀ {n : ℕ} {f : vector ℕ (n + 1) → ℕ},
  partrec' ↑f → partrec' fun (v : vector ℕ n) => rfind fun (n_1 : ℕ) => roption.some (to_bool (f (n_1::ᵥv) = 0))

end nat


namespace nat.partrec'


theorem to_part {n : ℕ} {f : vector ℕ n →. ℕ} (pf : partrec' f) : partrec f := sorry

theorem of_eq {n : ℕ} {f : vector ℕ n →. ℕ} {g : vector ℕ n →. ℕ} (hf : partrec' f) (H : ∀ (i : vector ℕ n), f i = g i) : partrec' g :=
  funext H ▸ hf

theorem of_prim {n : ℕ} {f : vector ℕ n → ℕ} (hf : primrec f) : partrec' ↑f :=
  prim (primrec'.of_prim hf)

theorem head {n : ℕ} : partrec' ↑vector.head :=
  prim primrec'.head

theorem tail {n : ℕ} {f : vector ℕ n →. ℕ} (hf : partrec' f) : partrec' fun (v : vector ℕ (Nat.succ n)) => f (vector.tail v) := sorry

protected theorem bind {n : ℕ} {f : vector ℕ n →. ℕ} {g : vector ℕ (n + 1) →. ℕ} (hf : partrec' f) (hg : partrec' g) : partrec' fun (v : vector ℕ n) => roption.bind (f v) fun (a : ℕ) => g (a::ᵥv) := sorry

protected theorem map {n : ℕ} {f : vector ℕ n →. ℕ} {g : vector ℕ (n + 1) → ℕ} (hf : partrec' f) (hg : partrec' ↑g) : partrec' fun (v : vector ℕ n) => roption.map (fun (a : ℕ) => g (a::ᵥv)) (f v) := sorry

/-- Analogous to `nat.partrec'` for `ℕ`-valued functions, a predicate for partial recursive
  vector-valued functions.-/
def vec {n : ℕ} {m : ℕ} (f : vector ℕ n → vector ℕ m)  :=
  ∀ (i : fin m), partrec' ↑fun (v : vector ℕ n) => vector.nth (f v) i

theorem vec.prim {n : ℕ} {m : ℕ} {f : vector ℕ n → vector ℕ m} (hf : primrec'.vec f) : vec f :=
  fun (i : fin m) => prim (hf i)

protected theorem nil {n : ℕ} : vec fun (_x : vector ℕ n) => vector.nil :=
  fun (i : fin 0) => fin.elim0 i

protected theorem cons {n : ℕ} {m : ℕ} {f : vector ℕ n → ℕ} {g : vector ℕ n → vector ℕ m} (hf : partrec' ↑f) (hg : vec g) : vec fun (v : vector ℕ n) => f v::ᵥg v := sorry

theorem idv {n : ℕ} : vec id :=
  vec.prim primrec'.idv

theorem comp' {n : ℕ} {m : ℕ} {f : vector ℕ m →. ℕ} {g : vector ℕ n → vector ℕ m} (hf : partrec' f) (hg : vec g) : partrec' fun (v : vector ℕ n) => f (g v) := sorry

theorem comp₁ {n : ℕ} (f : ℕ →. ℕ) {g : vector ℕ n → ℕ} (hf : partrec' fun (v : vector ℕ 1) => f (vector.head v)) (hg : partrec' ↑g) : partrec' fun (v : vector ℕ n) => f (g v) := sorry

theorem rfind_opt {n : ℕ} {f : vector ℕ (n + 1) → ℕ} (hf : partrec' ↑f) : partrec' fun (v : vector ℕ n) => rfind_opt fun (a : ℕ) => denumerable.of_nat (Option ℕ) (f (a::ᵥv)) := sorry

theorem of_part {n : ℕ} {f : vector ℕ n →. ℕ} : partrec f → partrec' f := sorry

theorem part_iff {n : ℕ} {f : vector ℕ n →. ℕ} : partrec' f ↔ partrec f :=
  { mp := to_part, mpr := of_part }

theorem part_iff₁ {f : ℕ →. ℕ} : (partrec' fun (v : vector ℕ 1) => f (vector.head v)) ↔ partrec f := sorry

theorem part_iff₂ {f : ℕ → ℕ →. ℕ} : (partrec' fun (v : vector ℕ (bit0 1)) => f (vector.head v) (vector.head (vector.tail v))) ↔ partrec₂ f := sorry

theorem vec_iff {m : ℕ} {n : ℕ} {f : vector ℕ m → vector ℕ n} : vec f ↔ computable f := sorry

