/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebraic_geometry.prime_spectrum
import Mathlib.algebra.category.CommRing.colimits
import Mathlib.algebra.category.CommRing.limits
import Mathlib.topology.sheaves.local_predicate
import Mathlib.topology.sheaves.forget
import Mathlib.ring_theory.localization
import Mathlib.ring_theory.subring
import Mathlib.PostPort

universes u 

namespace Mathlib

/-!
# The structure sheaf on `prime_spectrum R`.

We define the structure sheaf on `Top.of (prime_spectrum R)`, for a commutative ring `R`.
We define this as a subsheaf of the sheaf of dependent functions into the localizations,
cut out by the condition that the function must be locally equal to a ratio of elements of `R`.

Because the condition "is equal to a fraction" passes to smaller open subsets,
the subset of functions satisfying this condition is automatically a subpresheaf.
Because the condition "is locally equal to a fraction" is local,
it is also a subsheaf.

(It may be helpful to refer back to `topology.sheaves.sheaf_of_functions`,
where we show that dependent functions into any type family form a sheaf,
and also `topology.sheaves.local_predicate`, where we characterise the predicates
which pick out sub-presheaves and sub-sheaves of these sheaves.)

We also set up the ring structure, obtaining
`structure_sheaf R : sheaf CommRing (Top.of (prime_spectrum R))`.
-/

namespace algebraic_geometry


/--
$Spec R$, just as a topological space.
-/
def Spec.Top (R : Type u) [comm_ring R] : Top :=
  Top.of (prime_spectrum R)

namespace structure_sheaf


/--
The type family over `prime_spectrum R` consisting of the localization over each point.
-/
def localizations (R : Type u) [comm_ring R] (P : ↥(Spec.Top R))  :=
  localization.at_prime (prime_spectrum.as_ideal P)

protected instance localizations.inhabited (R : Type u) [comm_ring R] (P : ↥(Spec.Top R)) : Inhabited (localizations R P) :=
  { default := coe_fn (localization_map.to_map (localization.of (ideal.prime_compl (prime_spectrum.as_ideal P)))) 1 }

/--
The predicate saying that a dependent function on an open `U` is realised as a fixed fraction
`r / s` in each of the stalks (which are localizations at various prime ideals).
-/
def is_fraction {R : Type u} [comm_ring R] {U : topological_space.opens ↥(Spec.Top R)} (f : (x : ↥U) → localizations R ↑x)  :=
  ∃ (r : R),
    ∃ (s : R),
      ∀ (x : ↥U),
        ¬s ∈ prime_spectrum.as_ideal (subtype.val x) ∧
          f x * coe_fn (localization_map.to_map (localization.of (ideal.prime_compl (prime_spectrum.as_ideal ↑x)))) s =
            coe_fn (localization_map.to_map (localization.of (ideal.prime_compl (prime_spectrum.as_ideal ↑x)))) r

/--
The predicate `is_fraction` is "prelocal",
in the sense that if it holds on `U` it holds on any open subset `V` of `U`.
-/
def is_fraction_prelocal (R : Type u) [comm_ring R] : Top.prelocal_predicate (localizations R) :=
  Top.prelocal_predicate.mk
    (fun (U : topological_space.opens ↥(Spec.Top R)) (f : (x : ↥U) → localizations R ↑x) => is_fraction f) sorry

/--
We will define the structure sheaf as
the subsheaf of all dependent functions in `Π x : U, localizations R x`
consisting of those functions which can locally be expressed as a ratio of
(the images in the localization of) elements of `R`.

Quoting Hartshorne:

For an open set $$U ⊆ Spec A$$, we define $$𝒪(U)$$ to be the set of functions
$$s : U → ⨆_{𝔭 ∈ U} A_𝔭$$, such that $s(𝔭) ∈ A_𝔭$$ for each $$𝔭$$,
and such that $$s$$ is locally a quotient of elements of $$A$$:
to be precise, we require that for each $$𝔭 ∈ U$$, there is a neighborhood $$V$$ of $$𝔭$$,
contained in $$U$$, and elements $$a, f ∈ A$$, such that for each $$𝔮 ∈ V, f ∉ 𝔮$$,
and $$s(𝔮) = a/f$$ in $$A_𝔮$$.

Now Hartshorne had the disadvantage of not knowing about dependent functions,
so we replace his circumlocut