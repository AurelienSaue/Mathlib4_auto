/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebraic_geometry.locally_ringed_space
import Mathlib.algebraic_geometry.structure_sheaf
import Mathlib.data.equiv.transfer_instance
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# $Spec R$ as a `LocallyRingedSpace`

We bundle the `structure_sheaf R` construction for `R : CommRing` as a `LocallyRingedSpace`.

## Future work

Make it a functor.

-/

namespace algebraic_geometry


/--
Spec of a commutative ring, as a `SheafedSpace`.
-/
def Spec.SheafedSpace (R : CommRing) : SheafedSpace CommRing :=
  SheafedSpace.mk
    (PresheafedSpace.mk (Top.of (prime_spectrum ↥R)) (Top.sheaf.presheaf (structure_sheaf ↥R)))
    (Top.sheaf.sheaf_condition (structure_sheaf ↥R))

/--
Spec of a commutative ring, as a `PresheafedSpace`.
-/
def Spec.PresheafedSpace (R : CommRing) : PresheafedSpace CommRing :=
  SheafedSpace.to_PresheafedSpace (Spec.SheafedSpace R)

/--
Spec of a commutative ring, as a `LocallyRingedSpace`.
-/
def Spec.LocallyRingedSpace (R : CommRing) : LocallyRingedSpace :=
  LocallyRingedSpace.mk
    (SheafedSpace.mk (SheafedSpace.to_PresheafedSpace (Spec.SheafedSpace R))
      (SheafedSpace.sheaf_condition (Spec.SheafedSpace R)))
    sorry

end Mathlib