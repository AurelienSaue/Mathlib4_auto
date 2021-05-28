/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.category.Group.basic
import Mathlib.category_theory.preadditive.default
import PostPort

universes u_1 

namespace Mathlib

/-!
# The category of additive commutative groups is preadditive.
-/

namespace AddCommGroup


protected instance category_theory.preadditive : category_theory.preadditive AddCommGroup :=
  category_theory.preadditive.mk

