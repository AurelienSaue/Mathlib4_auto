/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon, Keeley Hoek, Floris van Doorn
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.list.defs
import Mathlib.PostPort

namespace Mathlib

namespace string


/-- `s.split_on c` tokenizes `s : string` on `c : char`. -/
def split_on (s : string) (c : char) : List string :=
  split (fun (_x : char) => to_bool (_x = c)) s

/-- `string.map_tokens c f s` tokenizes `s : string` on `c : char`, maps `f` over each token, and
then reassembles the string by intercalating the separator token `c` over the mapped tokens. -/
def map_tokens (c : char) (f : string → string) : string → string :=
  intercalate (singleton c) ∘ list.map f ∘ split fun (_x : char) => to_bool (_x = c)

/-- Tests whether the first string is a prefix of the second string. -/
def is_prefix_of (x : string) (y : string) : Bool :=
  list.is_prefix_of (to_list x) (to_list y)

/-- Tests whether the first string is a suffix of the second string. -/
def is_suffix_of (x : string) (y : string) : Bool :=
  list.is_suffix_of (to_list x) (to_list y)

/-- `x.starts_with y` is true if `y` is a prefix of `x`, and is false otherwise. -/
def starts_with (x : string) (y : string) : Bool :=
  is_prefix_of y x

/-- `x.ends_with y` is true if `y` is a suffix of `x`, and is false otherwise. -/
def ends_with (x : string) (y : string) : Bool :=
  is_suffix_of y x

/-- `get_rest s t` returns `some r` if `s = t ++ r`.
  If `t` is not a prefix of `s`, returns `none` -/
def get_rest (s : string) (t : string) : Option string :=
  list.as_string <$> list.get_rest (to_list s) (to_list t)

/-- Removes the first `n` elements from the string `s` -/
def popn (s : string) (n : ℕ) : string :=
  iterator.next_to_string (iterator.nextn (mk_iterator s) n)

/-- `is_nat s` is true iff `s` is a nonempty sequence of digits. -/
def is_nat (s : string) : Bool :=
  to_bool (¬↥(is_empty s) ∧ ↥(list.all (to_list s) fun (c : char) => to_bool (char.is_digit c)))

/-- Produce the head character from the string `s`, if `s` is not empty, otherwise 'A'. -/
def head (s : string) : char :=
  iterator.curr (mk_iterator s)

