/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

Additional equiv and encodable instances for lists, finsets, and fintypes.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.equiv.denumerable
import Mathlib.data.finset.sort
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

namespace encodable


def encode_list {α : Type u_1} [encodable α] : List α → ℕ :=
  sorry

def decode_list {α : Type u_1} [encodable α] : ℕ → Option (List α) :=
  sorry

protected instance list {α : Type u_1} [encodable α] : encodable (List α) :=
  mk encode_list decode_list sorry

@[simp] theorem encode_list_nil {α : Type u_1} [encodable α] : encode [] = 0 :=
  rfl

@[simp] theorem encode_list_cons {α : Type u_1} [encodable α] (a : α) (l : List α) : encode (a :: l) = Nat.succ (nat.mkpair (encode a) (encode l)) :=
  rfl

@[simp] theorem decode_list_zero {α : Type u_1} [encodable α] : decode (List α) 0 = some [] :=
  rfl

@[simp] theorem decode_list_succ {α : Type u_1} [encodable α] (v : ℕ) : decode (List α) (Nat.succ v) =
  (fun (_x : α) (_y : List α) => _x :: _y) <$> decode α (prod.fst (nat.unpair v)) <*>
    decode (List α) (prod.snd (nat.unpair v)) := sorry

theorem length_le_encode {α : Type u_1} [encodable α] (l : List α) : list.length l ≤ encode l := sorry

def encode_multiset {α : Type u_1} [encodable α] (s : multiset α) : ℕ :=
  encode (multiset.sort enle s)

def decode_multiset {α : Type u_1} [encodable α] (n : ℕ) : Option (multiset α) :=
  coe <$> decode (List α) n

protected instance multiset {α : Type u_1} [encodable α] : encodable (multiset α) :=
  mk encode_multiset decode_multiset sorry

def encodable_of_list {α : Type u_1} [DecidableEq α] (l : List α) (H : ∀ (x : α), x ∈ l) : encodable α :=
  mk (fun (a : α) => list.index_of a l) (list.nth l) sorry

def trunc_encodable_of_fintype (α : Type u_1) [DecidableEq α] [fintype α] : trunc (encodable α) :=
  quot.rec_on_subsingleton (finset.val finset.univ)
    (fun (l : List α) (H : ∀ (x : α), x ∈ Quot.mk setoid.r l) => trunc.mk (encodable_of_list l H)) finset.mem_univ

/-- A noncomputable way to arbitrarily choose an ordering on a finite type.
  It is not made into a global instance, since it involves an arbitrary choice.
  This can be locally made into an instance with `local attribute [instance] fintype.encodable`. -/
def fintype.encodable (α : Type u_1) [fintype α] : encodable α :=
  trunc.out (trunc_encodable_of_fintype α)

protected instance vector {α : Type u_1} [encodable α] {n : ℕ} : encodable (vector α n) :=
  encodable.subtype

protected instance fin_arrow {α : Type u_1} [encodable α] {n : ℕ} : encodable (fin n → α) :=
  of_equiv (vector α n) (equiv.symm (equiv.vector_equiv_fin α n))

protected instance fin_pi (n : ℕ) (π : fin n → Type u_1) [(i : fin n) → encodable (π i)] : encodable ((i : fin n) → π i) :=
  of_equiv (↥(set_of fun (f : fin n → sigma fun (i : fin n) => π i) => ∀ (i : fin n), sigma.fst (f i) = i))
    (equiv.pi_equiv_subtype_sigma (fin n) π)

protected instance array {α : Type u_1} [encodable α] {n : ℕ} : encodable (array n α) :=
  of_equiv (fin n → α) (equiv.array_equiv_fin n α)

protected instance finset {α : Type u_1} [encodable α] : encodable (finset α) :=
  of_equiv (Subtype fun (s : multiset α) => multiset.nodup s)
    (equiv.mk (fun (_x : finset α) => sorry) (fun (_x : Subtype fun (s : multiset α) => multiset.nodup s) => sorry) sorry
      sorry)

def fintype_arrow (α : Type u_1) (β : Type u_2) [DecidableEq α] [fintype α] [encodable β] : trunc (encodable (α → β)) :=
  trunc.map
    (fun (f : α ≃ fin (fintype.card α)) => of_equiv (fin (fintype.card α) → β) (equiv.arrow_congr f (equiv.refl β)))
    (fintype.equiv_fin α)

def fintype_pi (α : Type u_1) (π : α → Type u_2) [DecidableEq α] [fintype α] [(a : α) → encodable (π a)] : trunc (encodable ((a : α) → π a)) :=
  trunc.bind (trunc_encodable_of_fintype α)
    fun (a : encodable α) =>
      trunc.bind (fintype_arrow α (sigma fun (a : α) => π a))
        fun (f : encodable (α → sigma fun (a : α) => π a)) =>
          trunc.mk
            (of_equiv
              (Subtype
                fun (a : α → sigma fun (a : α) => π a) =>
                  a ∈ set_of fun (f : α → sigma fun (a : α) => π a) => ∀ (i : α), sigma.fst (f i) = i)
              (equiv.pi_equiv_subtype_sigma α π))

/-- The elements of a `fintype` as a sorted list. -/
def sorted_univ (α : Type u_1) [fintype α] [encodable α] : List α :=
  finset.sort (⇑(encode' α) ⁻¹'o LessEq) finset.univ

theorem mem_sorted_univ {α : Type u_1} [fintype α] [encodable α] (x : α) : x ∈ sorted_univ α :=
  iff.mpr (finset.mem_sort (⇑(encode' α) ⁻¹'o LessEq)) (finset.mem_univ x)

theorem length_sorted_univ {α : Type u_1} [fintype α] [encodable α] : list.length (sorted_univ α) = fintype.card α :=
  finset.length_sort (⇑(encode' α) ⁻¹'o LessEq)

theorem sorted_univ_nodup {α : Type u_1} [fintype α] [encodable α] : list.nodup (sorted_univ α) :=
  finset.sort_nodup (⇑(encode' α) ⁻¹'o LessEq) finset.univ

/-- An encodable `fintype` is equivalent a `fin`.-/
def fintype_equiv_fin {α : Type u_1} [fintype α] [encodable α] : α ≃ fin (fintype.card α) :=
  equiv.trans (fintype.equiv_fin_of_forall_mem_list mem_sorted_univ sorted_univ_nodup) (equiv.cast sorry)

protected instance fintype_arrow_of_encodable {α : Type u_1} {β : Type u_2} [encodable α] [fintype α] [encodable β] : encodable (α → β) :=
  of_equiv (fin (fintype.card α) → β) (equiv.arrow_congr fintype_equiv_fin (equiv.refl β))

end encodable


namespace denumerable


theorem denumerable_list_aux {α : Type u_1} [denumerable α] (n : ℕ) : ∃ (a : List α), ∃ (H : a ∈ encodable.decode_list n), encodable.encode_list a = n := sorry

protected instance denumerable_list {α : Type u_1} [denumerable α] : denumerable (List α) :=
  mk denumerable_list_aux

@[simp] theorem list_of_nat_zero {α : Type u_1} [denumerable α] : of_nat (List α) 0 = [] :=
  rfl

@[simp] theorem list_of_nat_succ {α : Type u_1} [denumerable α] (v : ℕ) : of_nat (List α) (Nat.succ v) = of_nat α (prod.fst (nat.unpair v)) :: of_nat (List α) (prod.snd (nat.unpair v)) := sorry

def lower : List ℕ → ℕ → List ℕ :=
  sorry

def raise : List ℕ → ℕ → List ℕ :=
  sorry

theorem lower_raise (l : List ℕ) (n : ℕ) : lower (raise l n) n = l := sorry

theorem raise_lower {l : List ℕ} {n : ℕ} : list.sorted LessEq (n :: l) → raise (lower l n) n = l := sorry

theorem raise_chain (l : List ℕ) (n : ℕ) : list.chain LessEq n (raise l n) := sorry

theorem raise_sorted (l : List ℕ) (n : ℕ) : list.sorted LessEq (raise l n) := sorry

/- Warning: this is not the same encoding as used in `encodable` -/

protected instance multiset {α : Type u_1} [denumerable α] : denumerable (multiset α) :=
  mk'
    (equiv.mk
      (fun (s : multiset α) => encodable.encode (lower (multiset.sort LessEq (multiset.map encodable.encode s)) 0))
      (fun (n : ℕ) => multiset.map (of_nat α) ↑(raise (of_nat (List ℕ) n) 0)) sorry sorry)

def lower' : List ℕ → ℕ → List ℕ :=
  sorry

def raise' : List ℕ → ℕ → List ℕ :=
  sorry

theorem lower_raise' (l : List ℕ) (n : ℕ) : lower' (raise' l n) n = l := sorry

theorem raise_lower' {l : List ℕ} {n : ℕ} : (∀ (m : ℕ), m ∈ l → n ≤ m) → list.sorted Less l → raise' (lower' l n) n = l := sorry

theorem raise'_chain (l : List ℕ) {m : ℕ} {n : ℕ} : m < n → list.chain Less m (raise' l n) := sorry

theorem raise'_sorted (l : List ℕ) (n : ℕ) : list.sorted Less (raise' l n) := sorry

def raise'_finset (l : List ℕ) (n : ℕ) : finset ℕ :=
  finset.mk ↑(raise' l n) sorry

/- Warning: this is not the same encoding as used in `encodable` -/

protected instance finset {α : Type u_1} [denumerable α] : denumerable (finset α) :=
  mk'
    (equiv.mk
      (fun (s : finset α) => encodable.encode (lower' (finset.sort LessEq (finset.map (equiv.to_embedding (eqv α)) s)) 0))
      (fun (n : ℕ) => finset.map (equiv.to_embedding (equiv.symm (eqv α))) (raise'_finset (of_nat (List ℕ) n) 0)) sorry
      sorry)

end denumerable


namespace equiv


/-- The type lists on unit is canonically equivalent to the natural numbers. -/
def list_unit_equiv : List Unit ≃ ℕ :=
  mk list.length (list.repeat Unit.unit) sorry sorry

def list_nat_equiv_nat : List ℕ ≃ ℕ :=
  denumerable.eqv (List ℕ)

def list_equiv_self_of_equiv_nat {α : Type} (e : α ≃ ℕ) : List α ≃ α :=
  equiv.trans (equiv.trans (list_equiv_of_equiv e) list_nat_equiv_nat) (equiv.symm e)

