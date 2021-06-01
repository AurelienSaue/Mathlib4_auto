/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.char_p.basic
import Mathlib.ring_theory.subring
import Mathlib.PostPort

universes u 

namespace Mathlib

/-!
# Characteristic of subrings
-/

namespace char_p


protected instance subsemiring (R : Type u) [semiring R] (p : ℕ) [char_p R p] (S : subsemiring R) :
    char_p (↥S) p :=
  mk
    fun (x : ℕ) =>
      iff.symm
        (iff.trans (iff.symm (cast_eq_zero_iff R p x))
          { mp :=
              fun (h : ↑x = 0) =>
                subtype.eq
                  ((fun (this : coe_fn (subsemiring.subtype S) ↑x = 0) => this)
                    (eq.mpr
                      (id
                        (Eq._oldrec (Eq.refl (coe_fn (subsemiring.subtype S) ↑x = 0))
                          (ring_hom.map_nat_cast (subsemiring.subtype S) x)))
                      (eq.mpr (id (Eq._oldrec (Eq.refl (↑x = 0)) h)) (Eq.refl 0)))),
            mpr :=
              fun (h : ↑x = 0) =>
                ring_hom.map_nat_cast (subsemiring.subtype S) x ▸
                  eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn (subsemiring.subtype S) ↑x = 0)) h))
                    (eq.mpr
                      (id
                        (Eq._oldrec (Eq.refl (coe_fn (subsemiring.subtype S) 0 = 0))
                          (ring_hom.map_zero (subsemiring.subtype S))))
                      (Eq.refl 0)) })

protected instance subring (R : Type u) [ring R] (p : ℕ) [char_p R p] (S : subring R) :
    char_p (↥S) p :=
  mk
    fun (x : ℕ) =>
      iff.symm
        (iff.trans (iff.symm (cast_eq_zero_iff R p x))
          { mp :=
              fun (h : ↑x = 0) =>
                subtype.eq
                  ((fun (this : coe_fn (subring.subtype S) ↑x = 0) => this)
                    (eq.mpr
                      (id
                        (Eq._oldrec (Eq.refl (coe_fn (subring.subtype S) ↑x = 0))
                          (ring_hom.map_nat_cast (subring.subtype S) x)))
                      (eq.mpr (id (Eq._oldrec (Eq.refl (↑x = 0)) h)) (Eq.refl 0)))),
            mpr :=
              fun (h : ↑x = 0) =>
                ring_hom.map_nat_cast (subring.subtype S) x ▸
                  eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn (subring.subtype S) ↑x = 0)) h))
                    (eq.mpr
                      (id
                        (Eq._oldrec (Eq.refl (coe_fn (subring.subtype S) 0 = 0))
                          (ring_hom.map_zero (subring.subtype S))))
                      (Eq.refl 0)) })

protected instance subring' (R : Type u) [comm_ring R] (p : ℕ) [char_p R p] (S : subring R) :
    char_p (↥S) p :=
  char_p.subring R p S

end Mathlib