/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.equiv.ring
import Mathlib.data.equiv.mul_add_aut
import PostPort

universes u_1 

namespace Mathlib

/-!
# Ring automorphisms

This file defines the automorphism group structure on `ring_aut R := ring_equiv R R`.

## Implementation notes

The definition of multiplication in the automorphism group agrees with function composition,
multiplication in `equiv.perm`, and multiplication in `category_theory.End`, but not with
`category_theory.comp`.

This file is kept separate from `data/equiv/ring` so that `group_theory.perm` is free to use
equivalences (and other files that use them) before the group structure is defined.

## Tags

ring_aut
-/

/-- The group of ring automorphisms. -/
def ring_aut (R : Type u_1) [Mul R] [Add R]  :=
  R ≃+* R

namespace ring_aut


/--
The group operation on automorphisms of a ring is defined by
`λ g h, ring_equiv.trans h g`.
This means that multiplication agrees with composition, `(g*h)(x) = g (h x)`.
-/
protected instance group (R : Type u_1) [Mul R] [Add R] : group (ring_aut R) :=
  group.mk (fun (g h : R ≃+* R) => ring_equiv.trans h g) sorry (ring_equiv.refl R) sorry sorry ring_equiv.symm
    (fun (a b : R ≃+* R) => a * ring_equiv.symm b) sorry

protected instance inhabited (R : Type u_1) [Mul R] [Add R] : Inhabited (ring_aut R) :=
  { default := 1 }

/-- Monoid homomorphism from ring automorphisms to additive automorphisms. -/
def to_add_aut (R : Type u_1) [Mul R] [Add R] : ring_aut R →* add_aut R :=
  monoid_hom.mk ring_equiv.to_add_equiv sorry sorry

/-- Monoid homomorphism from ring automorphisms to multiplicative automorphisms. -/
def to_mul_aut (R : Type u_1) [Mul R] [Add R] : ring_aut R →* mul_aut R :=
  monoid_hom.mk ring_equiv.to_mul_equiv sorry sorry

/-- Monoid homomorphism from ring automorphisms to permutations. -/
def to_perm (R : Type u_1) [Mul R] [Add R] : ring_aut R →* equiv.perm R :=
  monoid_hom.mk ring_equiv.to_equiv sorry sorry

