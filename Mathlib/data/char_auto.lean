/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

Supplementary theorems about the `char` type.
-/
import PrePort
import Lean3Lib.init.default
import PostPort

namespace Mathlib

protected instance char.linear_order : linear_order char :=
  linear_order.mk LessEq Less sorry sorry sorry sorry char.decidable_le char.decidable_eq char.decidable_lt

