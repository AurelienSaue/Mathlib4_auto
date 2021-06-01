/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.data.bool.lemmas
import Mathlib.Lean3Lib.init.data.string.basic
import Mathlib.Lean3Lib.init.meta.well_founded_tactics
 

namespace Mathlib

namespace string


namespace iterator


@[simp] theorem next_to_string_mk_iterator (s : string) : next_to_string (mk_iterator s) = s :=
  string_imp.rec (fun (s : List char) => Eq.refl (next_to_string (mk_iterator (string_imp.mk s)))) s

@[simp] theorem length_next_to_string_next (it : iterator) : length (next_to_string (next it)) = length (next_to_string it) - 1 := sorry

theorem zero_lt_length_next_to_string_of_has_next {it : iterator} : ↥(has_next it) → 0 < length (next_to_string it) := sorry

end iterator


-- TODO(Sebastian): generalize to something like https://doc.rust-lang.org/std/primitive.str.html#method.split

def split (p : char → Bool) (s : string) : List string :=
  split_core p (mk_iterator s) (mk_iterator s)

