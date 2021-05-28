/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.char_p.basic
import Mathlib.algebra.ring.pi
import PostPort

universes u v 

namespace Mathlib

/-!
# Characteristic of semirings of functions
-/

namespace char_p


protected instance pi (ι : Type u) [hi : Nonempty ι] (R : Type v) [semiring R] (p : ℕ) [char_p R p] : char_p (ι → R) p :=
  mk fun (x : ℕ) => sorry

-- diamonds

protected instance pi' (ι : Type u) [hi : Nonempty ι] (R : Type v) [comm_ring R] (p : ℕ) [char_p R p] : char_p (ι → R) p :=
  char_p.pi ι R p

