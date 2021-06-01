/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.matrix.basic
import Mathlib.algebra.char_p.basic
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Matrices in prime characteristic
-/

protected instance matrix.char_p {n : Type u_1} [fintype n] {R : Type u_2} [ring R] [DecidableEq n]
    [Nonempty n] (p : ℕ) [char_p R p] : char_p (matrix n n R) p :=
  sorry

end Mathlib