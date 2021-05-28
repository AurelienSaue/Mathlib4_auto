/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.data.string.basic
import Mathlib.Lean3Lib.init.data.bool.basic
import Mathlib.Lean3Lib.init.data.subtype.basic
import Mathlib.Lean3Lib.init.data.unsigned.basic
import Mathlib.Lean3Lib.init.data.prod
import Mathlib.Lean3Lib.init.data.sum.basic
import Mathlib.Lean3Lib.init.data.nat.div
import PostPort

universes u l v 

namespace Mathlib

/-- 
Implement `has_repr` if the output string is valid lean code that evaluates back to the original object.
If you just want to view the object as a string for a trace message, use `has_to_string`.

### Example:

```
#eval to_string "hello world"
-- [Lean] "hello world"

-- [Lean] "hello world"
#eval repr "hello world" 
-- [Lean] "\"hello world\""

-- [Lean] "\"hello world\""
```

Reference: https://github.com/leanprover/lean/issues/1664

 -/
class has_repr (α : Type u) 
where
  repr : α → string

/-- `repr` is similar to `to_string` except that we should have the property `eval (repr x) = x` for most sensible datatypes. 
Hence, `repr "hello"` has the value `"\"hello\""` not `"hello"`.  -/
def repr {α : Type u} [has_repr α] : α → string :=
  has_repr.repr

protected instance bool.has_repr : has_repr Bool :=
  has_repr.mk
    fun (b : Bool) =>
      cond b
        (string.str (string.str string.empty (char.of_nat (bit0 (bit0 (bit1 (bit0 (bit1 (bit1 1))))))))
          (char.of_nat (bit0 (bit0 (bit1 (bit0 (bit1 (bit1 1))))))))
        (string.str (string.str string.empty (char.of_nat (bit0 (bit1 (bit1 (bit0 (bit0 (bit1 1))))))))
          (char.of_nat (bit0 (bit1 (bit1 (bit0 (bit0 (bit1 1))))))))

-- Remark: type class inference will not consider local instance `b` in the new elaborator

protected instance decidable.has_repr {p : Prop} : has_repr (Decidable p) :=
  has_repr.mk
    fun (b : Decidable p) =>
      ite p
        (string.str (string.str string.empty (char.of_nat (bit0 (bit0 (bit1 (bit0 (bit1 (bit1 1))))))))
          (char.of_nat (bit0 (bit0 (bit1 (bit0 (bit1 (bit1 1))))))))
        (string.str (string.str string.empty (char.of_nat (bit0 (bit1 (bit1 (bit0 (bit0 (bit1 1))))))))
          (char.of_nat (bit0 (bit1 (bit1 (bit0 (bit0 (bit1 1))))))))

protected def list.repr_aux {α : Type u} [has_repr α] : Bool → List α → string :=
  sorry

protected def list.repr {α : Type u} [has_repr α] : List α → string :=
  sorry

protected instance list.has_repr {α : Type u} [has_repr α] : has_repr (List α) :=
  has_repr.mk list.repr

protected instance unit.has_repr : has_repr Unit :=
  has_repr.mk
    fun (u : Unit) =>
      string.str
        (string.str
          (string.str (string.str string.empty (char.of_nat (bit1 (bit1 (bit0 (bit0 (bit1 (bit1 1))))))))
            (char.of_nat (bit0 (bit0 (bit1 (bit0 (bit1 (bit1 1))))))))
          (char.of_nat (bit1 (bit0 (bit0 (bit0 (bit0 (bit1 1))))))))
        (char.of_nat (bit0 (bit1 (bit0 (bit0 (bit1 (bit1 1)))))))

protected instance option.has_repr {α : Type u} [has_repr α] : has_repr (Option α) :=
  has_repr.mk fun (o : Option α) => sorry

protected instance sum.has_repr {α : Type u} {β : Type v} [has_repr α] [has_repr β] : has_repr (α ⊕ β) :=
  has_repr.mk fun (s : α ⊕ β) => sorry

protected instance prod.has_repr {α : Type u} {β : Type v} [has_repr α] [has_repr β] : has_repr (α × β) :=
  has_repr.mk fun (_x : α × β) => sorry

protected instance sigma.has_repr {α : Type u} {β : α → Type v} [has_repr α] [s : (x : α) → has_repr (β x)] : has_repr (sigma β) :=
  has_repr.mk fun (_x : sigma β) => sorry

protected instance subtype.has_repr {α : Type u} {p : α → Prop} [has_repr α] : has_repr (Subtype p) :=
  has_repr.mk fun (s : Subtype p) => repr (subtype.val s)

namespace nat


def digit_char (n : ℕ) : char := sorry

def digit_succ (base : ℕ) : List ℕ → List ℕ :=
  sorry

def to_digits (base : ℕ) : ℕ → List ℕ :=
  sorry

protected def repr (n : ℕ) : string :=
  list.as_string (list.reverse (list.map digit_char (to_digits (bit0 (bit1 (bit0 1))) n)))

end nat


protected instance nat.has_repr : has_repr ℕ :=
  has_repr.mk nat.repr

def hex_digit_repr (n : ℕ) : string :=
  string.singleton (nat.digit_char n)

def char_to_hex (c : char) : string :=
  let n : ℕ := char.to_nat c;
  let d2 : ℕ := n / bit0 (bit0 (bit0 (bit0 1)));
  let d1 : ℕ := n % bit0 (bit0 (bit0 (bit0 1)));
  hex_digit_repr d2 ++ hex_digit_repr d1

def char.quote_core (c : char) : string := sorry

protected instance char.has_repr : has_repr char :=
  has_repr.mk
    fun (c : char) =>
      string.str string.empty (char.of_nat (bit1 (bit1 (bit1 (bit0 (bit0 1)))))) ++ char.quote_core c ++
        string.str string.empty (char.of_nat (bit1 (bit1 (bit1 (bit0 (bit0 1))))))

def string.quote_aux : List char → string :=
  sorry

def string.quote (s : string) : string :=
  ite (string.is_empty s = tt)
    (string.str (string.str string.empty (char.of_nat (bit0 (bit1 (bit0 (bit0 (bit0 1)))))))
      (char.of_nat (bit0 (bit1 (bit0 (bit0 (bit0 1)))))))
    (string.str string.empty (char.of_nat (bit0 (bit1 (bit0 (bit0 (bit0 1)))))) ++ string.quote_aux (string.to_list s) ++
      string.str string.empty (char.of_nat (bit0 (bit1 (bit0 (bit0 (bit0 1)))))))

protected instance string.has_repr : has_repr string :=
  has_repr.mk string.quote

protected instance fin.has_repr (n : ℕ) : has_repr (fin n) :=
  has_repr.mk fun (f : fin n) => repr (subtype.val f)

protected instance unsigned.has_repr : has_repr unsigned :=
  has_repr.mk fun (n : unsigned) => repr (subtype.val n)

def char.repr (c : char) : string :=
  repr c

