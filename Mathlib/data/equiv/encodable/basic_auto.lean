/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Mario Carneiro

Type class for encodable Types.
Note that every encodable Type is countable.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.equiv.nat
import Mathlib.order.rel_iso
import Mathlib.order.directed
import Mathlib.PostPort

universes u_1 l u_2 u_3 

namespace Mathlib

/-- An encodable type is a "constructively countable" type. This is where
  we have an explicit injection `encode : α → nat` and a partial inverse
  `decode : nat → option α`. This makes the range of `encode` decidable,
  although it is not decidable if `α` is finite or not. -/
class encodable (α : Type u_1) where
  encode : α → ℕ
  decode : ℕ → Option α
  encodek : ∀ (a : α), decode (encode a) = some a

namespace encodable


theorem encode_injective {α : Type u_1} [encodable α] : function.injective encode := sorry

/- This is not set as an instance because this is usually not the best way
  to infer decidability. -/

def decidable_eq_of_encodable (α : Type u_1) [encodable α] : DecidableEq α := sorry

def of_left_injection {α : Type u_1} {β : Type u_2} [encodable α] (f : β → α) (finv : α → Option β)
    (linv : ∀ (b : β), finv (f b) = some b) : encodable β :=
  mk (fun (b : β) => encode (f b)) (fun (n : ℕ) => option.bind (decode α n) finv) sorry

def of_left_inverse {α : Type u_1} {β : Type u_2} [encodable α] (f : β → α) (finv : α → β)
    (linv : ∀ (b : β), finv (f b) = b) : encodable β :=
  of_left_injection f (some ∘ finv) sorry

/-- If `α` is encodable and `β ≃ α`, then so is `β` -/
def of_equiv {β : Type u_2} (α : Type u_1) [encodable α] (e : β ≃ α) : encodable β :=
  of_left_inverse (⇑e) (⇑(equiv.symm e)) (equiv.left_inv e)

@[simp] theorem encode_of_equiv {α : Type u_1} {β : Type u_2} [encodable α] (e : β ≃ α) (b : β) :
    encode b = encode (coe_fn e b) :=
  rfl

@[simp] theorem decode_of_equiv {α : Type u_1} {β : Type u_2} [encodable α] (e : β ≃ α) (n : ℕ) :
    decode β n = option.map (⇑(equiv.symm e)) (decode α n) :=
  rfl

protected instance nat : encodable ℕ := mk id some sorry

@[simp] theorem encode_nat (n : ℕ) : encode n = n := rfl

@[simp] theorem decode_nat (n : ℕ) : decode ℕ n = some n := rfl

protected instance empty : encodable empty :=
  mk (fun (a : empty) => empty.rec (fun (a : empty) => ℕ) a) (fun (n : ℕ) => none) sorry

protected instance unit : encodable PUnit :=
  mk (fun (_x : PUnit) => 0) (fun (n : ℕ) => nat.cases_on n (some PUnit.unit) fun (_x : ℕ) => none)
    sorry

@[simp] theorem encode_star : encode PUnit.unit = 0 := rfl

@[simp] theorem decode_unit_zero : decode PUnit 0 = some PUnit.unit := rfl

@[simp] theorem decode_unit_succ (n : ℕ) : decode PUnit (Nat.succ n) = none := rfl

protected instance option {α : Type u_1} [h : encodable α] : encodable (Option α) :=
  mk (fun (o : Option α) => option.cases_on o 0 fun (a : α) => Nat.succ (encode a))
    (fun (n : ℕ) => nat.cases_on n (some none) fun (m : ℕ) => option.map some (decode α m)) sorry

@[simp] theorem encode_none {α : Type u_1} [encodable α] : encode none = 0 := rfl

@[simp] theorem encode_some {α : Type u_1} [encodable α] (a : α) :
    encode (some a) = Nat.succ (encode a) :=
  rfl

@[simp] theorem decode_option_zero {α : Type u_1} [encodable α] : decode (Option α) 0 = some none :=
  rfl

@[simp] theorem decode_option_succ {α : Type u_1} [encodable α] (n : ℕ) :
    decode (Option α) (Nat.succ n) = option.map some (decode α n) :=
  rfl

def decode2 (α : Type u_1) [encodable α] (n : ℕ) : Option α :=
  option.bind (decode α n) (option.guard fun (a : α) => encode a = n)

theorem mem_decode2' {α : Type u_1} [encodable α] {n : ℕ} {a : α} :
    a ∈ decode2 α n ↔ a ∈ decode α n ∧ encode a = n :=
  sorry

theorem mem_decode2 {α : Type u_1} [encodable α] {n : ℕ} {a : α} : a ∈ decode2 α n ↔ encode a = n :=
  iff.trans mem_decode2' (and_iff_right_of_imp fun (e : encode a = n) => e ▸ encodek a)

theorem decode2_is_partial_inv {α : Type u_1} [encodable α] :
    function.is_partial_inv encode (decode2 α) :=
  fun (a : α) (n : ℕ) => mem_decode2

theorem decode2_inj {α : Type u_1} [encodable α] {n : ℕ} {a₁ : α} {a₂ : α} (h₁ : a₁ ∈ decode2 α n)
    (h₂ : a₂ ∈ decode2 α n) : a₁ = a₂ :=
  encode_injective (Eq.trans (iff.mp mem_decode2 h₁) (Eq.symm (iff.mp mem_decode2 h₂)))

theorem encodek2 {α : Type u_1} [encodable α] (a : α) : decode2 α (encode a) = some a :=
  iff.mpr mem_decode2 rfl

def decidable_range_encode (α : Type u_1) [encodable α] : decidable_pred (set.range encode) :=
  fun (x : ℕ) => decidable_of_iff ↥(option.is_some (decode2 α x)) sorry

def equiv_range_encode (α : Type u_1) [encodable α] : α ≃ ↥(set.range encode) :=
  equiv.mk (fun (a : α) => { val := encode a, property := sorry })
    (fun (n : ↥(set.range encode)) => option.get sorry) sorry sorry

def encode_sum {α : Type u_1} {β : Type u_2} [encodable α] [encodable β] : α ⊕ β → ℕ := sorry

def decode_sum {α : Type u_1} {β : Type u_2} [encodable α] [encodable β] (n : ℕ) : Option (α ⊕ β) :=
  sorry

protected instance sum {α : Type u_1} {β : Type u_2} [encodable α] [encodable β] :
    encodable (α ⊕ β) :=
  mk encode_sum decode_sum sorry

@[simp] theorem encode_inl {α : Type u_1} {β : Type u_2} [encodable α] [encodable β] (a : α) :
    encode (sum.inl a) = bit0 (encode a) :=
  rfl

@[simp] theorem encode_inr {α : Type u_1} {β : Type u_2} [encodable α] [encodable β] (b : β) :
    encode (sum.inr b) = bit1 (encode b) :=
  rfl

@[simp] theorem decode_sum_val {α : Type u_1} {β : Type u_2} [encodable α] [encodable β] (n : ℕ) :
    decode (α ⊕ β) n = decode_sum n :=
  rfl

protected instance bool : encodable Bool := of_equiv (Unit ⊕ Unit) equiv.bool_equiv_punit_sum_punit

@[simp] theorem encode_tt : encode tt = 1 := rfl

@[simp] theorem encode_ff : encode false = 0 := rfl

@[simp] theorem decode_zero : decode Bool 0 = some false := rfl

@[simp] theorem decode_one : decode Bool 1 = some tt := rfl

theorem decode_ge_two (n : ℕ) (h : bit0 1 ≤ n) : decode Bool n = none := sorry

def encode_sigma {α : Type u_1} {γ : α → Type u_3} [encodable α] [(a : α) → encodable (γ a)] :
    sigma γ → ℕ :=
  sorry

def decode_sigma {α : Type u_1} {γ : α → Type u_3} [encodable α] [(a : α) → encodable (γ a)]
    (n : ℕ) : Option (sigma γ) :=
  sorry

protected instance sigma {α : Type u_1} {γ : α → Type u_3} [encodable α]
    [(a : α) → encodable (γ a)] : encodable (sigma γ) :=
  mk encode_sigma decode_sigma sorry

@[simp] theorem decode_sigma_val {α : Type u_1} {γ : α → Type u_3} [encodable α]
    [(a : α) → encodable (γ a)] (n : ℕ) :
    decode (sigma γ) n =
        option.bind (decode α (prod.fst (nat.unpair n)))
          fun (a : α) => option.map (sigma.mk a) (decode (γ a) (prod.snd (nat.unpair n))) :=
  sorry

@[simp] theorem encode_sigma_val {α : Type u_1} {γ : α → Type u_3} [encodable α]
    [(a : α) → encodable (γ a)] (a : α) (b : γ a) :
    encode (sigma.mk a b) = nat.mkpair (encode a) (encode b) :=
  rfl

protected instance prod {α : Type u_1} {β : Type u_2} [encodable α] [encodable β] :
    encodable (α × β) :=
  of_equiv (sigma fun (_x : α) => β) (equiv.symm (equiv.sigma_equiv_prod α β))

@[simp] theorem decode_prod_val {α : Type u_1} {β : Type u_2} [encodable α] [encodable β] (n : ℕ) :
    decode (α × β) n =
        option.bind (decode α (prod.fst (nat.unpair n)))
          fun (a : α) => option.map (Prod.mk a) (decode β (prod.snd (nat.unpair n))) :=
  sorry

@[simp] theorem encode_prod_val {α : Type u_1} {β : Type u_2} [encodable α] [encodable β] (a : α)
    (b : β) : encode (a, b) = nat.mkpair (encode a) (encode b) :=
  rfl

def encode_subtype {α : Type u_1} {P : α → Prop} [encA : encodable α] :
    (Subtype fun (a : α) => P a) → ℕ :=
  sorry

def decode_subtype {α : Type u_1} {P : α → Prop} [encA : encodable α] [decP : decidable_pred P]
    (v : ℕ) : Option (Subtype fun (a : α) => P a) :=
  option.bind (decode α v)
    fun (a : α) =>
      dite (P a) (fun (h : P a) => some { val := a, property := h }) fun (h : ¬P a) => none

protected instance subtype {α : Type u_1} {P : α → Prop} [encA : encodable α]
    [decP : decidable_pred P] : encodable (Subtype fun (a : α) => P a) :=
  mk encode_subtype decode_subtype sorry

theorem subtype.encode_eq {α : Type u_1} {P : α → Prop} [encA : encodable α]
    [decP : decidable_pred P] (a : Subtype P) : encode a = encode (subtype.val a) :=
  subtype.cases_on a
    fun (a_val : α) (a_property : P a_val) =>
      Eq.refl (encode { val := a_val, property := a_property })

protected instance fin (n : ℕ) : encodable (fin n) :=
  of_equiv (Subtype fun (m : ℕ) => m < n) (equiv.fin_equiv_subtype n)

protected instance int : encodable ℤ := of_equiv ℕ equiv.int_equiv_nat

protected instance ulift {α : Type u_1} [encodable α] : encodable (ulift α) :=
  of_equiv α equiv.ulift

protected instance plift {α : Type u_1} [encodable α] : encodable (plift α) :=
  of_equiv α equiv.plift

def of_inj {α : Type u_1} {β : Type u_2} [encodable β] (f : α → β) (hf : function.injective f) :
    encodable α :=
  of_left_injection f (function.partial_inv f) sorry

end encodable


/--
`ulower α : Type 0` is an equivalent type in the lowest universe, given `encodable α`.
-/
def ulower (α : Type u_1) [encodable α] := ↥(set.range encodable.encode)

namespace ulower


/--
The equivalence between the encodable type `α` and `ulower α : Type 0`.
-/
def equiv (α : Type u_1) [encodable α] : α ≃ ulower α := encodable.equiv_range_encode α

/--
Lowers an `a : α` into `ulower α`.
-/
def down {α : Type u_1} [encodable α] (a : α) : ulower α := coe_fn (equiv α) a

protected instance inhabited {α : Type u_1} [encodable α] [Inhabited α] : Inhabited (ulower α) :=
  { default := down Inhabited.default }

/--
Lifts an `a : ulower α` into `α`.
-/
def up {α : Type u_1} [encodable α] (a : ulower α) : α := coe_fn (equiv.symm (equiv α)) a

@[simp] theorem down_up {α : Type u_1} [encodable α] {a : ulower α} : down (up a) = a :=
  equiv.right_inv (equiv α) a

@[simp] theorem up_down {α : Type u_1} [encodable α] {a : α} : up (down a) = a :=
  equiv.left_inv (equiv α) a

@[simp] theorem up_eq_up {α : Type u_1} [encodable α] {a : ulower α} {b : ulower α} :
    up a = up b ↔ a = b :=
  equiv.apply_eq_iff_eq (equiv.symm (equiv α))

@[simp] theorem down_eq_down {α : Type u_1} [encodable α] {a : α} {b : α} :
    down a = down b ↔ a = b :=
  equiv.apply_eq_iff_eq (equiv α)

protected theorem ext {α : Type u_1} [encodable α] {a : ulower α} {b : ulower α} :
    up a = up b → a = b :=
  iff.mp up_eq_up

end ulower


/-
Choice function for encodable types and decidable predicates.
We provide the following API

choose      {α : Type*} {p : α → Prop} [c : encodable α] [d : decidable_pred p] : (∃ x, p x) → α :=
choose_spec {α : Type*} {p : α → Prop} [c : encodable α] [d : decidable_pred p] (ex : ∃ x, p x) :
  p (choose ex) :=
-/

namespace encodable


def choose_x {α : Type u_1} {p : α → Prop} [encodable α] [decidable_pred p] (h : ∃ (x : α), p x) :
    Subtype fun (x : α) => p x :=
  (fun (this : ∃ (n : ℕ), good p (decode α n)) => sorry) sorry

def choose {α : Type u_1} {p : α → Prop} [encodable α] [decidable_pred p] (h : ∃ (x : α), p x) :
    α :=
  subtype.val (choose_x h)

theorem choose_spec {α : Type u_1} {p : α → Prop} [encodable α] [decidable_pred p]
    (h : ∃ (x : α), p x) : p (choose h) :=
  subtype.property (choose_x h)

theorem axiom_of_choice {α : Type u_1} {β : α → Type u_2} {R : (x : α) → β x → Prop}
    [(a : α) → encodable (β a)] [(x : α) → (y : β x) → Decidable (R x y)]
    (H : ∀ (x : α), ∃ (y : β x), R x y) : ∃ (f : (a : α) → β a), ∀ (x : α), R x (f x) :=
  Exists.intro (fun (x : α) => choose (H x)) fun (x : α) => choose_spec (H x)

theorem skolem {α : Type u_1} {β : α → Type u_2} {P : (x : α) → β x → Prop}
    [c : (a : α) → encodable (β a)] [d : (x : α) → (y : β x) → Decidable (P x y)] :
    (∀ (x : α), ∃ (y : β x), P x y) ↔ ∃ (f : (a : α) → β a), ∀ (x : α), P x (f x) :=
  sorry

/-
There is a total ordering on the elements of an encodable type, induced by the map to ℕ.
-/

/-- The `encode` function, viewed as an embedding. -/
def encode' (α : Type u_1) [encodable α] : α ↪ ℕ := function.embedding.mk encode encode_injective

protected instance order.preimage.is_trans {α : Type u_1} [encodable α] :
    is_trans α (⇑(encode' α) ⁻¹'o LessEq) :=
  rel_embedding.is_trans (rel_embedding.preimage (encode' α) LessEq)

protected instance order.preimage.is_antisymm {α : Type u_1} [encodable α] :
    is_antisymm α (⇑(encode' α) ⁻¹'o LessEq) :=
  rel_embedding.is_antisymm (rel_embedding.preimage (encode' α) LessEq)

protected instance order.preimage.is_total {α : Type u_1} [encodable α] :
    is_total α (⇑(encode' α) ⁻¹'o LessEq) :=
  rel_embedding.is_total (rel_embedding.preimage (encode' α) LessEq)

end encodable


namespace directed


/-- Given a `directed r` function `f : α → β` defined on an encodable inhabited type,
construct a noncomputable sequence such that `r (f (x n)) (f (x (n + 1)))`
and `r (f a) (f (x (encode a + 1))`. -/
protected def sequence {α : Type u_1} {β : Type u_2} [encodable α] [Inhabited α] {r : β → β → Prop}
    (f : α → β) (hf : directed r f) : ℕ → α :=
  sorry

theorem sequence_mono_nat {α : Type u_1} {β : Type u_2} [encodable α] [Inhabited α]
    {r : β → β → Prop} {f : α → β} (hf : directed r f) (n : ℕ) :
    r (f (directed.sequence f hf n)) (f (directed.sequence f hf (n + 1))) :=
  sorry

theorem rel_sequence {α : Type u_1} {β : Type u_2} [encodable α] [Inhabited α] {r : β → β → Prop}
    {f : α → β} (hf : directed r f) (a : α) :
    r (f a) (f (directed.sequence f hf (encodable.encode a + 1))) :=
  sorry

theorem sequence_mono {α : Type u_1} {β : Type u_2} [encodable α] [Inhabited α] [preorder β]
    {f : α → β} (hf : directed LessEq f) : monotone (f ∘ directed.sequence f hf) :=
  monotone_of_monotone_nat (sequence_mono_nat hf)

theorem le_sequence {α : Type u_1} {β : Type u_2} [encodable α] [Inhabited α] [preorder β]
    {f : α → β} (hf : directed LessEq f) (a : α) :
    f a ≤ f (directed.sequence f hf (encodable.encode a + 1)) :=
  rel_sequence hf a

end directed


/-- Representative of an equivalence class. This is a computable version of `quot.out` for a setoid
on an encodable type. -/
def quotient.rep {α : Type u_1} {s : setoid α} [DecidableRel has_equiv.equiv] [encodable α]
    (q : quotient s) : α :=
  encodable.choose (quotient.exists_rep q)

theorem quotient.rep_spec {α : Type u_1} {s : setoid α} [DecidableRel has_equiv.equiv] [encodable α]
    (q : quotient s) : quotient.mk (quotient.rep q) = q :=
  encodable.choose_spec (quotient.exists_rep q)

/-- The quotient of an encodable space by a decidable equivalence relation is encodable. -/
def encodable_quotient {α : Type u_1} {s : setoid α} [DecidableRel has_equiv.equiv] [encodable α] :
    encodable (quotient s) :=
  encodable.mk (fun (q : quotient s) => encodable.encode (quotient.rep q))
    (fun (n : ℕ) => quotient.mk <$> encodable.decode α n) sorry

end Mathlib