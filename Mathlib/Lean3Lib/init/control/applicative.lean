/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.control.functor
 

universes u v l 

namespace Mathlib

not foundnot foundinfixl:60 " <*> " => Mathlib.has_seq.seq

not foundinfixl:60 " <* " => Mathlib.has_seq_left.seq_left

not foundinfixl:60 " *> " => Mathlib.has_seq_right.seq_right

not found