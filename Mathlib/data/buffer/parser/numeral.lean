/-
Copyright (c) 2020 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.fintype.card
import Mathlib.PostPort

namespace Mathlib

/-!
# Numeral parsers

This file expands on the existing `nat : parser ℕ` to provide parsers into any type `α` that
can be represented by a numeral, which relies on `α` having a 0, 1, and addition operation.
There are also convenience parsers that ensure that the numeral parsed in is not larger than
the cardinality of the type `α` , if it is known that `fintype α`. Additionally, there are
convenience parsers that parse in starting from "1", which can be useful for positive ordinals;
or parser from a given character or character range.

## Main definitions

* 'numeral` : The parser which uses `nat.cast` to map the result of `parser.nat` to the desired `α`
* `numeral.of_fintype` :  The parser which `guard`s to make sure the parsed numeral is within the
  cardinality of the target `fintype` type `α`.

## Implementation details

When the `numeral` or related parsers are invoked, the desired type is provided explicitly. In many
cases, it can be inferred, so one can write, for example
```lean
def get_fin : string → fin 5 :=
sum.elim (λ _, 0) id ∘ parser.run_string (parser.numeral.of_fintype _)
```

In the definitions of the parsers (except for `numeral`), there is an explicit `nat.bin_cast`
instead an explicit or implicit `nat.cast`
-/

namespace parser


/--
Parse a string of digits as a numeral while casting it to target type `α`.
-/
def numeral (α : Type) [HasZero α] [HasOne α] [Add α] : parser α :=
  nat.bin_cast <$> nat

/--
Parse a string of digits as a numeral while casting it to target type `α`,
which has a `[fintype α]` constraint. The parser ensures that the numeral parsed in
is within the cardinality of the type `α`.
-/
def numeral.of_fintype (α : Type) [HasZero α] [HasOne α] [Add α] [fintype α] : parser α := sorry

/--
Parse a string of digits as a numeral while casting it to target type `α`. The parsing starts
at "1", so `"1"` is parsed in as `nat.cast 0`. Providing `"0"` to the parser causes a failure.
-/
def numeral.from_one (α : Type) [HasZero α] [HasOne α] [Add α] : parser α := sorry

/--
Parse a string of digits as a numeral while casting it to target type `α`,
which has a `[fintype α]` constraint. The parser ensures that the numeral parsed in
is within the cardinality of the type `α`. The parsing starts
at "1", so `"1"` is parsed in as `nat.cast 0`. Providing `"0"` to the parser causes a failure.
-/
def numeral.from_one.of_fintype (α : Type) [HasZero α] [HasOne α] [Add α] [fintype α] : parser α := sorry

/--
Parse a character as a numeral while casting it to target type `α`,
The parser ensures that the character parsed in is within the bounds set by `fromc` and `toc`,
and subtracts the value of `fromc` from the parsed in character.
-/
def numeral.char (α : Type) [HasZero α] [HasOne α] [Add α] (fromc : char) (toc : char) : parser α := sorry

/--
Parse a character as a numeral while casting it to target type `α`,
which has a `[fintype α]` constraint.
The parser ensures that the character parsed in is greater or equal to `fromc` and
and subtracts the value of `fromc` from the parsed in character. There is also a check
that the resulting value is within the cardinality of the type `α`.
-/
def numeral.char.of_fintype (α : Type) [HasZero α] [HasOne α] [Add α] [fintype α] (fromc : char) : parser α := sorry

