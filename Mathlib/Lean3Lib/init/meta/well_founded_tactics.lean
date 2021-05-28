/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.meta.default
import Mathlib.Lean3Lib.init.data.sigma.lex
import Mathlib.Lean3Lib.init.data.nat.lemmas
import Mathlib.Lean3Lib.init.data.list.instances
import Mathlib.Lean3Lib.init.data.list.qsort
 

universes u v 

namespace Mathlib

/- TODO(Leo): move this lemma, or delete it after we add algebraic normalizer. -/

theorem nat.lt_add_of_zero_lt_left (a : ℕ) (b : ℕ) (h : 0 < b) : a < a + b :=
  (fun (this : a + 0 < a + b) => this) (nat.add_lt_add_left h a)

/- TODO(Leo): move this lemma, or delete it after we add algebraic normalizer. -/

theorem nat.zero_lt_one_add (a : ℕ) : 0 < 1 + a := sorry

/- TODO(Leo): move this lemma, or delete it after we add algebraic normalizer. -/

theorem nat.lt_add_right (a : ℕ) (b : ℕ) (c : ℕ) : a < b → a < b + c :=
  fun (h : a < b) => lt_of_lt_of_le h (nat.le_add_right b c)

/- TODO(Leo): move this lemma, or delete it after we add algebraic normalizer. -/

theorem nat.lt_add_left (a : ℕ) (b : ℕ) (c : ℕ) : a < b → a < c + b :=
  fun (h : a < b) => lt_of_lt_of_le h (nat.le_add_left b c)

protected def psum.alt.sizeof {α : Type u} {β : Type v} [SizeOf α] [SizeOf β] : psum α β → ℕ :=
  sorry

protected def psum.has_sizeof_alt (α : Type u) (β : Type v) [SizeOf α] [SizeOf β] : SizeOf (psum α β) :=
  { sizeOf := psum.alt.sizeof }

