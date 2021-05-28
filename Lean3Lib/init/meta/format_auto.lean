/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import PrePort
import Lean3Lib.init.meta.options
import Lean3Lib.init.function
import Lean3Lib.init.data.to_string
import PostPort

universes l 

namespace Mathlib

inductive format.color 
where
| red : format.color
| green : format.color
| orange : format.color
| blue : format.color
| pink : format.color
| cyan : format.color
| grey : format.color

def format.color.to_string : format.color → string :=
  sorry

