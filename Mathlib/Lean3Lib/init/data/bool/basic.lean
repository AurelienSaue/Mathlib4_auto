/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.core
import PostPort

universes u 

namespace Mathlib

/-!
# Boolean operations
-/

/-- `cond b x y` is `x` if `b = tt` and `y` otherwise. -/
def cond {a : Type u} : Bool → a → a → a :=
  sorry

/-- Boolean OR -/
def bor : Bool → Bool → Bool :=
  sorry

/-- Boolean AND -/
def band : Bool → Bool → Bool :=
  sorry

/-- Boolean NOT -/
def bnot : Bool → Bool :=
  sorry

/-- Boolean XOR -/
def bxor : Bool → Bool → Bool :=
  sorry

infixl:65 " || " => Mathlib.bor

infixl:70 " && " => Mathlib.band

