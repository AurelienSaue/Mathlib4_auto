/-
Copyright (c) 2020 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.meta.expr
import Mathlib.Lean3Lib.init.data.list.basic
import Mathlib.Lean3Lib.init.data.option.basic
import Mathlib.Lean3Lib.init.util
import Mathlib.PostPort

universes l 

namespace Mathlib

namespace expr


/-- An enum representing a recursive argument in an `expr` constructor.
Types of local and meta variables are not included because they are not consistently set and
depend on context. -/
inductive coord 
where
| app_fn : coord
| app_arg : coord
| lam_var_type : coord
| lam_body : coord
| pi_var_type : coord
| pi_body : coord
| elet_var_type : coord
| elet_assignment : coord
| elet_body : coord

namespace coord


/-- Convert the coord enum to its index number. -/
def code : coord → ℕ :=
  sorry

protected def repr : coord → string :=
  sorry

protected instance has_repr : has_repr coord :=
  has_repr.mk coord.repr

protected instance has_to_string : has_to_string coord :=
  has_to_string.mk coord.repr

protected instance has_lt : HasLess coord :=
  { Less := fun (x y : coord) => code x < code y }

/-- Use this to pick the subexpression of a given expression that cooresponds
to the given coordinate. -/
end coord


/-- An address is a list of coordinates used to reference subterms of an expression.
The first coordinate in the list corresponds to the root of the expression. -/
def address  :=
  List coord

namespace address


protected def to_string : address → string :=
  to_string ∘ list.map coord.repr

protected instance has_repr : has_repr address :=
  has_repr.mk address.to_string

protected instance has_to_string : has_to_string address :=
  has_to_string.mk address.to_string

protected instance has_append : Append address :=
  { append := list.append }

