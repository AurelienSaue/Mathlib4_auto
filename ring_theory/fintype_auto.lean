/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.associated
import Mathlib.data.fintype.basic
import PostPort

universes u_1 

namespace Mathlib

/-!
# Some facts about finite rings
-/

theorem card_units_lt (R : Type u_1) [semiring R] [nontrivial R] [fintype R] : fintype.card (units R) < fintype.card R :=
  card_lt_card_of_injective_of_not_mem coe units.ext not_is_unit_zero

