/-
Copyright (c) 2020 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Wong
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.list.basic
import PostPort

universes u_1 

namespace Mathlib

/-!
# Palindromes

This module defines *palindromes*, lists which are equal to their reverse.

The main result is the `palindrome` inductive type, and its associated `palindrome.rec_on` induction
principle. Also provided are conversions to and from other equivalent definitions.

## References

* [Pierre Castéran, *On palindromes*][casteran]

[casteran]: https://www.labri.fr/perso/casteran/CoqArt/inductive-prop-chap/palindrome.html

## Tags

palindrome, reverse, induction
-/

/--
`palindrome l` asserts that `l` is a palindrome. This is defined inductively:

* The empty list is a palindrome;
* A list with one element is a palindrome;
* Adding the same element to both ends of a palindrome results in a bigger palindrome.
-/
inductive palindrome {α : Type u_1} : List α → Prop
where
| nil : palindrome []
| singleton : ∀ (x : α), palindrome [x]
| cons_concat : ∀ (x : α) {l : List α}, palindrome l → palindrome (x :: (l ++ [x]))

namespace palindrome


theorem reverse_eq {α : Type u_1} {l : List α} (p : palindrome l) : list.reverse l = l := sorry

theorem of_reverse_eq {α : Type u_1} {l : List α} : list.reverse l = l → palindrome l := sorry

theorem iff_reverse_eq {α : Type u_1} {l : List α} : palindrome l ↔ list.reverse l = l :=
  { mp := reverse_eq, mpr := of_reverse_eq }

theorem append_reverse {α : Type u_1} (l : List α) : palindrome (l ++ list.reverse l) := sorry

protected instance decidable {α : Type u_1} [DecidableEq α] (l : List α) : Decidable (palindrome l) :=
  decidable_of_iff' (list.reverse l = l) iff_reverse_eq

