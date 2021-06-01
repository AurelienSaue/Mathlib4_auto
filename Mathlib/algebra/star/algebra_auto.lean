/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.algebra.basic
import Mathlib.algebra.star.basic
import Mathlib.PostPort

universes u v l 

namespace Mathlib

/-!
# Star algebras

Introduces the notion of a star algebra over a star ring.
-/

/--
A star algebra `A` over a star ring `R` is an algebra which is a star ring,
and the two star structures are compatible in the sense
`star (r • a) = star r • star a`.
-/
-- Note that we take `star_ring A` as a typeclass argument, rather than extending it,

-- to avoid having multiple definitions of the star operation.

class star_algebra (R : Type u) (A : Type v) [comm_semiring R] [star_ring R] [semiring A]
    [star_ring A] [algebra R A]
    where
  star_smul : ∀ (r : R) (a : A), star (r • a) = has_star.star r • star a

@[simp] theorem star_smul (R : Type u) (A : Type v) [comm_semiring R] [star_ring R] [semiring A]
    [star_ring A] [algebra R A] [star_algebra R A] (r : R) (a : A) :
    star (r • a) = star r • star a :=
  star_algebra.star_smul r a

end Mathlib