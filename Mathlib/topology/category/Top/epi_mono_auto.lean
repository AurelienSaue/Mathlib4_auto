/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.topology.category.Top.adjunctions
import Mathlib.category_theory.epi_mono
import PostPort

universes u 

namespace Mathlib

namespace Top


theorem epi_iff_surjective {X : Top} {Y : Top} (f : X ⟶ Y) : category_theory.epi f ↔ function.surjective ⇑f := sorry

theorem mono_iff_injective {X : Top} {Y : Top} (f : X ⟶ Y) : category_theory.mono f ↔ function.injective ⇑f := sorry

