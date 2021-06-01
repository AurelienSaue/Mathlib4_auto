/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.data.list.basic
import Mathlib.Lean3Lib.init.data.char.basic

universes l u_1 

namespace Mathlib

/- In the VM, strings are implemented using a dynamic array and UTF-8 encoding.

   TODO: we currently cannot mark string_imp as private because
   we need to bind string_imp.mk and string_imp.cases_on in the VM.
-/

structure string_imp where
  data : List char

def string := string_imp

def list.as_string (s : List char) : string := string_imp.mk s

namespace string


protected instance has_lt : HasLess string :=
  { Less := fun (s₁ s₂ : string) => string_imp.data s₁ < string_imp.data s₂ }

/- Remark: this function has a VM builtin efficient implementation. -/

protected instance has_decidable_lt (s₁ : string) (s₂ : string) : Decidable (s₁ < s₂) :=
  list.has_decidable_lt (string_imp.data s₁) (string_imp.data s₂)

protected instance has_decidable_eq : DecidableEq string := fun (_x : string) => sorry

def empty : string := string_imp.mk []

def length : string → ℕ := sorry

/- The internal implementation uses dynamic arrays and will perform destructive updates
   if the string is not shared. -/

def push : string → char → string := sorry

/- The internal implementation uses dynamic arrays and will perform destructive updates
   if the string is not shared. -/

def append : string → string → string := sorry

/- O(n) in the VM, where n is the length of the string -/

def to_list : string → List char := sorry

def fold {α : Type u_1} (a : α) (f : α → char → α) (s : string) : α := list.foldl f a (to_list s)

/- In the VM, the string iterator is implemented as a pointer to the string being iterated + index.

   TODO: we currently cannot mark interator_imp as private because
   we need to bind string_imp.mk and string_imp.cases_on in the VM.
-/

structure iterator_imp where
  fst : List char
  snd : List char

def iterator := iterator_imp

def mk_iterator : string → iterator := sorry

namespace iterator


def curr : iterator → char := sorry

/- In the VM, `set_curr` is constant time if the string being iterated is not shared and linear time
   if it is. -/

def set_curr : iterator → char → iterator := sorry

def next : iterator → iterator := sorry

def prev : iterator → iterator := sorry

def has_next : iterator → Bool := sorry

def has_prev : iterator → Bool := sorry

def insert : iterator → string → iterator := sorry

def remove : iterator → ℕ → iterator := sorry

/- In the VM, `to_string` is a constant time operation. -/

def to_string : iterator → string := sorry

def to_end : iterator → iterator := sorry

def next_to_string : iterator → string := sorry

def prev_to_string : iterator → string := sorry

protected def extract_core : List char → List char → Option (List char) := sorry

def extract : iterator → iterator → Option string := sorry

end iterator


end string


/- The following definitions do not have builtin support in the VM -/

protected instance string.inhabited : Inhabited string := { default := string.empty }

protected instance string.has_sizeof : SizeOf string := { sizeOf := string.length }

protected instance string.has_append : Append string := { append := string.append }

namespace string


def str : string → char → string := push

def is_empty (s : string) : Bool := to_bool (length s = 0)

def front (s : string) : char := iterator.curr (mk_iterator s)

def back (s : string) : char := iterator.curr (iterator.prev (iterator.to_end (mk_iterator s)))

def join (l : List string) : string := list.foldl (fun (r s : string) => r ++ s) empty l

def singleton (c : char) : string := push empty c

def intercalate (s : string) (ss : List string) : string :=
  list.as_string (list.intercalate (to_list s) (list.map to_list ss))

namespace iterator


def nextn : iterator → ℕ → iterator := sorry

def prevn : iterator → ℕ → iterator := sorry

end iterator


def pop_back (s : string) : string :=
  iterator.prev_to_string (iterator.prev (iterator.to_end (mk_iterator s)))

def popn_back (s : string) (n : ℕ) : string :=
  iterator.prev_to_string (iterator.prevn (iterator.to_end (mk_iterator s)) n)

def backn (s : string) (n : ℕ) : string :=
  iterator.next_to_string (iterator.prevn (iterator.to_end (mk_iterator s)) n)

end string


protected def char.to_string (c : char) : string := string.singleton c

def string.to_nat (s : string) : ℕ := to_nat_core (string.mk_iterator s) (string.length s) 0

namespace string


theorem empty_ne_str (c : char) (s : string) : empty ≠ str s c := sorry

theorem str_ne_empty (c : char) (s : string) : str s c ≠ empty := ne.symm (empty_ne_str c s)

theorem str_ne_str_left {c₁ : char} {c₂ : char} (s₁ : string) (s₂ : string) :
    c₁ ≠ c₂ → str s₁ c₁ ≠ str s₂ c₂ :=
  sorry

theorem str_ne_str_right (c₁ : char) (c₂ : char) {s₁ : string} {s₂ : string} :
    s₁ ≠ s₂ → str s₁ c₁ ≠ str s₂ c₂ :=
  sorry

end Mathlib