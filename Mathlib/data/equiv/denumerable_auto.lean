/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

Denumerable (countably infinite) types, as a typeclass extending
encodable. This is used to provide explicit encode/decode functions
from nat, where the functions are known inverses of each other.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.equiv.encodable.basic
import Mathlib.data.sigma.default
import Mathlib.data.fintype.basic
import Mathlib.data.list.min_max
import Mathlib.PostPort

universes u_1 l u_2 u_3 

namespace Mathlib

/-- A denumerable type is one which is (constructively) bijective with ℕ.
  Although we already have a name for this property, namely `α ≃ ℕ`,
  we are here interested in using it as a typeclass. -/
class denumerable (α : Type u_1) extends encodable α where
  decode_inv : ∀ (n : ℕ), ∃ (a : α), ∃ (H : a ∈ encodable.decode α n), encodable.encode a = n

namespace denumerable


theorem decode_is_some (α : Type u_1) [denumerable α] (n : ℕ) :
    ↥(option.is_some (encodable.decode α n)) :=
  iff.mpr option.is_some_iff_exists (Exists.imp (fun (a : α) => Exists.fst) (decode_inv n))

def of_nat (α : Type u_1) [f : denumerable α] (n : ℕ) : α := option.get (decode_is_some α n)

@[simp] theorem decode_eq_of_nat (α : Type u_1) [denumerable α] (n : ℕ) :
    encodable.decode α n = some (of_nat α n) :=
  option.eq_some_of_is_some (decode_is_some α n)

@[simp] theorem of_nat_of_decode {α : Type u_1} [denumerable α] {n : ℕ} {b : α}
    (h : encodable.decode α n = some b) : of_nat α n = b :=
  option.some.inj (Eq.trans (Eq.symm (decode_eq_of_nat α n)) h)

@[simp] theorem encode_of_nat {α : Type u_1} [denumerable α] (n : ℕ) :
    encodable.encode (of_nat α n) = n :=
  sorry

@[simp] theorem of_nat_encode {α : Type u_1} [denumerable α] (a : α) :
    of_nat α (encodable.encode a) = a :=
  of_nat_of_decode (encodable.encodek a)

def eqv (α : Type u_1) [denumerable α] : α ≃ ℕ :=
  equiv.mk encodable.encode (of_nat α) of_nat_encode encode_of_nat

def mk' {α : Type u_1} (e : α ≃ ℕ) : denumerable α := mk sorry

def of_equiv (α : Type u_1) {β : Type u_2} [denumerable α] (e : β ≃ α) : denumerable β := mk sorry

@[simp] theorem of_equiv_of_nat (α : Type u_1) {β : Type u_2} [denumerable α] (e : β ≃ α) (n : ℕ) :
    of_nat β n = coe_fn (equiv.symm e) (of_nat α n) :=
  sorry

def equiv₂ (α : Type u_1) (β : Type u_2) [denumerable α] [denumerable β] : α ≃ β :=
  equiv.trans (eqv α) (equiv.symm (eqv β))

protected instance nat : denumerable ℕ := mk sorry

@[simp] theorem of_nat_nat (n : ℕ) : of_nat ℕ n = n := rfl

protected instance option {α : Type u_1} [denumerable α] : denumerable (Option α) := mk sorry

protected instance sum {α : Type u_1} {β : Type u_2} [denumerable α] [denumerable β] :
    denumerable (α ⊕ β) :=
  mk sorry

protected instance sigma {α : Type u_1} [denumerable α] {γ : α → Type u_3}
    [(a : α) → denumerable (γ a)] : denumerable (sigma γ) :=
  mk sorry

@[simp] theorem sigma_of_nat_val {α : Type u_1} [denumerable α] {γ : α → Type u_3}
    [(a : α) → denumerable (γ a)] (n : ℕ) :
    of_nat (sigma γ) n =
        sigma.mk (of_nat α (prod.fst (nat.unpair n)))
          (of_nat (γ (of_nat α (prod.fst (nat.unpair n)))) (prod.snd (nat.unpair n))) :=
  sorry

protected instance prod {α : Type u_1} {β : Type u_2} [denumerable α] [denumerable β] :
    denumerable (α × β) :=
  of_equiv (sigma fun (_x : α) => β) (equiv.symm (equiv.sigma_equiv_prod α β))

@[simp] theorem prod_of_nat_val {α : Type u_1} {β : Type u_2} [denumerable α] [denumerable β]
    (n : ℕ) :
    of_nat (α × β) n = (of_nat α (prod.fst (nat.unpair n)), of_nat β (prod.snd (nat.unpair n))) :=
  sorry

@[simp] theorem prod_nat_of_nat : of_nat (ℕ × ℕ) = nat.unpair := sorry

protected instance int : denumerable ℤ := mk' equiv.int_equiv_nat

protected instance pnat : denumerable ℕ+ := mk' equiv.pnat_equiv_nat

protected instance ulift {α : Type u_1} [denumerable α] : denumerable (ulift α) :=
  of_equiv α equiv.ulift

protected instance plift {α : Type u_1} [denumerable α] : denumerable (plift α) :=
  of_equiv α equiv.plift

def pair {α : Type u_1} [denumerable α] : α × α ≃ α := equiv₂ (α × α) α

end denumerable


namespace nat.subtype


theorem exists_succ {s : set ℕ} [infinite ↥s] (x : ↥s) : ∃ (n : ℕ), subtype.val x + n + 1 ∈ s :=
  sorry

def succ {s : set ℕ} [infinite ↥s] [decidable_pred s] (x : ↥s) : ↥s :=
  (fun (h : ∃ (m : ℕ), subtype.val x + m + 1 ∈ s) =>
      { val := subtype.val x + nat.find h + 1, property := sorry })
    (exists_succ x)

theorem succ_le_of_lt {s : set ℕ} [infinite ↥s] [decidable_pred s] {x : ↥s} {y : ↥s} (h : y < x) :
    succ y ≤ x :=
  sorry

theorem le_succ_of_forall_lt_le {s : set ℕ} [infinite ↥s] [decidable_pred s] {x : ↥s} {y : ↥s}
    (h : ∀ (z : ↥s), z < x → z ≤ y) : x ≤ succ y :=
  sorry

theorem lt_succ_self {s : set ℕ} [infinite ↥s] [decidable_pred s] (x : ↥s) : x < succ x :=
  lt_of_le_of_lt (le_add_right (le_refl (subtype.val x)))
    (lt_succ_self (subtype.val x + nat.find (exists_succ x)))

theorem lt_succ_iff_le {s : set ℕ} [infinite ↥s] [decidable_pred s] {x : ↥s} {y : ↥s} :
    x < succ y ↔ x ≤ y :=
  { mp :=
      fun (h : x < succ y) => le_of_not_gt fun (h' : x > y) => not_le_of_gt h (succ_le_of_lt h'),
    mpr := fun (h : x ≤ y) => lt_of_le_of_lt h (lt_succ_self y) }

def of_nat (s : set ℕ) [decidable_pred s] [infinite ↥s] : ℕ → ↥s := sorry

theorem of_nat_surjective_aux {s : set ℕ} [infinite ↥s] [decidable_pred s] {x : ℕ} (hx : x ∈ s) :
    ∃ (n : ℕ), of_nat s n = { val := x, property := hx } :=
  sorry

theorem of_nat_surjective {s : set ℕ} [infinite ↥s] [decidable_pred s] :
    function.surjective (of_nat s) :=
  sorry

def denumerable (s : set ℕ) [decidable_pred s] [infinite ↥s] : denumerable ↥s :=
  denumerable.of_equiv ℕ (equiv.mk to_fun_aux (of_nat s) sorry sorry)

end nat.subtype


namespace denumerable


def of_encodable_of_infinite (α : Type u_1) [encodable α] [infinite α] : denumerable α :=
  let _inst : decidable_pred (set.range encodable.encode) := encodable.decidable_range_encode α;
  let _inst_3 : infinite ↥(set.range encodable.encode) := sorry;
  let _inst_4 : denumerable ↥(set.range encodable.encode) :=
    nat.subtype.denumerable (set.range encodable.encode);
  of_equiv (↥(set.range encodable.encode)) (encodable.equiv_range_encode α)

end Mathlib