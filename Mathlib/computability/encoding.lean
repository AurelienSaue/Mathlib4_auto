/-
Copyright (c) 2020 Pim Spelier, Daan van Gent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Spelier, Daan van Gent.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.fintype.basic
import Mathlib.data.num.lemmas
import Mathlib.tactic.derive_fintype
import Mathlib.PostPort

universes l 

namespace Mathlib

/-!
# Encodings

This file contains the definition of a (finite) encoding, a map from a type to
strings in an alphabet, used in defining computability by Turing machines.
It also contains several examples:

## Examples

- `fin_encoding_nat_bool`   : a binary encoding of ℕ in a simple alphabet.
- `fin_encoding_nat_Γ'`    : a binary encoding of ℕ in the alphabet used for TM's.
- `unary_fin_encoding_nat` : a unary encoding of ℕ
- `fin_encoding_bool_bool`  : an encoding of bool.
-/

namespace computability


/-- An encoding of a type in a certain alphabet, together with a decoding. -/
structure encoding (α : Type) 
where
  Γ : Type
  encode : α → List Γ
  decode : List Γ → Option α
  decode_encode : ∀ (x : α), decode (encode x) = some x

/-- An encoding plus a guarantee of finiteness of the alphabet. -/
structure fin_encoding (α : Type) 
extends encoding α
where
  Γ_fin : fintype (encoding.Γ _to_encoding)

/-- A standard Turing machine alphabet, consisting of blank,bit0,bit1,bra,ket,comma. -/
inductive Γ' 
where
| blank : Γ'
| bit : Bool → Γ'
| bra : Γ'
| ket : Γ'
| comma : Γ'

protected instance inhabited_Γ' : Inhabited Γ' :=
  { default := Γ'.blank }

/-- The natural inclusion of bool in Γ'. -/
def inclusion_bool_Γ' : Bool → Γ' :=
  Γ'.bit

/-- An arbitrary section of the natural inclusion of bool in Γ'. -/
def section_Γ'_bool : Γ' → Bool :=
  sorry

theorem left_inverse_section_inclusion : function.left_inverse section_Γ'_bool inclusion_bool_Γ' :=
  fun (x : Bool) => bool.cases_on x rfl rfl

theorem inclusion_bool_Γ'_injective : function.injective inclusion_bool_Γ' :=
  function.has_left_inverse.injective (Exists.intro section_Γ'_bool left_inverse_section_inclusion)

/-- An encoding function of the positive binary numbers in bool. -/
def encode_pos_num : pos_num → List Bool :=
  sorry

/-- An encoding function of the binary numbers in bool. -/
def encode_num : num → List Bool :=
  sorry

/-- An encoding function of ℕ in bool. -/
def encode_nat (n : ℕ) : List Bool :=
  encode_num ↑n

/-- A decoding function from `list bool` to the positive binary numbers. -/
def decode_pos_num : List Bool → pos_num :=
  sorry

/-- A decoding function from `list bool` to the binary numbers. -/
def decode_num : List Bool → num :=
  fun (l : List Bool) => ite (l = []) num.zero ↑(decode_pos_num l)

/-- A decoding function from `list bool` to ℕ. -/
def decode_nat : List Bool → ℕ :=
  fun (l : List Bool) => ↑(decode_num l)

theorem encode_pos_num_nonempty (n : pos_num) : encode_pos_num n ≠ [] :=
  pos_num.cases_on n (list.cons_ne_nil tt []) (fun (m : pos_num) => list.cons_ne_nil tt (encode_pos_num m))
    fun (m : pos_num) => list.cons_ne_nil false (encode_pos_num m)

theorem decode_encode_pos_num (n : pos_num) : decode_pos_num (encode_pos_num n) = n := sorry

theorem decode_encode_num (n : num) : decode_num (encode_num n) = n := sorry

theorem decode_encode_nat (n : ℕ) : decode_nat (encode_nat n) = n := sorry

/-- A binary encoding of ℕ in bool. -/
def encoding_nat_bool : encoding ℕ :=
  encoding.mk Bool encode_nat (fun (n : List Bool) => some (decode_nat n)) sorry

/-- A binary fin_encoding of ℕ in bool. -/
def fin_encoding_nat_bool : fin_encoding ℕ :=
  fin_encoding.mk encoding_nat_bool bool.fintype

/-- A binary encoding of ℕ in Γ'. -/
def encoding_nat_Γ' : encoding ℕ :=
  encoding.mk Γ' (fun (x : ℕ) => list.map inclusion_bool_Γ' (encode_nat x))
    (fun (x : List Γ') => some (decode_nat (list.map section_Γ'_bool x))) sorry

/-- A binary fin_encoding of ℕ in Γ'. -/
def fin_encoding_nat_Γ' : fin_encoding ℕ :=
  fin_encoding.mk encoding_nat_Γ' Γ'.fintype

/-- A unary encoding function of ℕ in bool. -/
def unary_encode_nat : ℕ → List Bool :=
  sorry

/-- A unary decoding function from `list bool` to ℕ. -/
def unary_decode_nat : List Bool → ℕ :=
  list.length

theorem unary_decode_encode_nat (n : ℕ) : unary_decode_nat (unary_encode_nat n) = n :=
  Nat.rec rfl (fun (m : ℕ) (hm : unary_decode_nat (unary_encode_nat m) = m) => Eq.symm (congr_arg Nat.succ (Eq.symm hm)))
    n

/-- A unary fin_encoding of ℕ. -/
def unary_fin_encoding_nat : fin_encoding ℕ :=
  fin_encoding.mk (encoding.mk Bool unary_encode_nat (fun (n : List Bool) => some (unary_decode_nat n)) sorry)
    bool.fintype

/-- An encoding function of bool in bool. -/
def encode_bool : Bool → List Bool :=
  list.ret

/-- A decoding function from `list bool` to bool. -/
def decode_bool : List Bool → Bool :=
  sorry

theorem decode_encode_bool (b : Bool) : decode_bool (encode_bool b) = b :=
  bool.cases_on b rfl rfl

/-- A fin_encoding of bool in bool. -/
def fin_encoding_bool_bool : fin_encoding Bool :=
  fin_encoding.mk (encoding.mk Bool encode_bool (fun (x : List Bool) => some (decode_bool x)) sorry) bool.fintype

protected instance inhabited_fin_encoding : Inhabited (fin_encoding Bool) :=
  { default := fin_encoding_bool_bool }

protected instance inhabited_encoding : Inhabited (encoding Bool) :=
  { default := fin_encoding.to_encoding fin_encoding_bool_bool }

