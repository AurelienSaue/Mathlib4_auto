/-
Copyright (c) 2019 Chris Hughes All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.algebra.polynomial
import Mathlib.analysis.special_functions.pow
import Mathlib.PostPort

namespace Mathlib

/-!
# The fundamental theorem of algebra

This file proves that every nonconstant complex polynomial has a root.
-/

namespace complex


/- The following proof uses the method given at
  <https://ncatlab.org/nlab/show/fundamental+theorem+of+algebra#classical_fta_via_advanced_calculus> -/

/-- The fundamental theorem of algebra. Every non constant complex polynomial
  has a root -/
theorem exists_root {f : polynomial ℂ} (hf : 0 < polynomial.degree f) :
    ∃ (z : ℂ), polynomial.is_root f z :=
  sorry

end Mathlib