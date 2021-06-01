/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.opens
import Mathlib.ring_theory.ideal.prod
import Mathlib.linear_algebra.finsupp
import Mathlib.algebra.punit_instances
import Mathlib.PostPort

universes u u_1 v 

namespace Mathlib

/-!
# Prime spectrum of a commutative ring

The prime spectrum of a commutative ring is the type of all prime ideals.
It is naturally endowed with a topology: the Zariski topology.

(It is also naturally endowed with a sheaf of rings,
which is constructed in `algebraic_geometry.structure_sheaf`.)

## Main definitions

* `prime_spectrum R`: The prime spectrum of a commutative ring `R`,
  i.e., the set of all prime ideals of `R`.
* `zero_locus s`: The zero locus of a subset `s` of `R`
  is the subset of `prime_spectrum R` consisting of all prime ideals that contain `s`.
* `vanishing_ideal t`: The vanishing ideal of a subset `t` of `prime_spectrum R`
  is the intersection of points in `t` (viewed as prime ideals).

## Conventions

We denote subsets of rings with `s`, `s'`, etc...
whereas we denote subsets of prime spectra with `t`, `t'`, etc...

## Inspiration/contributors

The contents of this file draw inspiration from
<https://github.com/ramonfmir/lean-scheme>
which has contributions from Ramon Fernandez Mir, Kevin Buzzard, Kenny Lau,
and Chris Hughes (on an earlier repository).

-/

/-- The prime spectrum of a commutative ring `R`
is the type of all prime ideals of `R`.

It is naturally endowed with a topology (the Zariski topology),
and a sheaf of commutative rings (see `algebraic_geometry.structure_sheaf`).
It is a fundamental building block in algebraic geometry. -/
def prime_spectrum (R : Type u) [comm_ring R] :=
  Subtype fun (I : ideal R) => ideal.is_prime I

namespace prime_spectrum


/-- A method to view a point in the prime spectrum of a commutative ring
as an ideal of that ring. -/
def as_ideal {R : Type u} [comm_ring R] (x : prime_spectrum R) : ideal R :=
  subtype.val x

protected instance is_prime {R : Type u} [comm_ring R] (x : prime_spectrum R) : ideal.is_prime (as_ideal x) :=
  subtype.property x

/--
The prime spectrum of the zero ring is empty.
-/
theorem punit (x : prime_spectrum PUnit) : False :=
  iff.mp (ideal.ne_top_iff_one (subtype.val x)) (and.left (subtype.property x))
    (subsingleton.elim 0 1 ▸ ideal.zero_mem (subtype.val x))

/-- The prime spectrum of `R × S` is in bijection with the disjoint unions of the prime spectrum of
    `R` and the prime spectrum of `S`. -/
def prime_spectrum_prod (R : Type u) [comm_ring R] (S : Type v) [comm_ring S] : prime_spectrum (R × S) ≃ prime_spectrum R ⊕ prime_spectrum S :=
  ideal.prime_ideals_equiv R S

@[simp] theorem prime_spectrum_prod_symm_inl_as_ideal {R : Type u} [comm_ring R] {S : Type v} [comm_ring S] (x : prime_spectrum R) : as_ideal (coe_fn (equiv.symm (prime_spectrum_prod R S)) (sum.inl x)) = ideal.prod (as_ideal x) ⊤ := sorry

@[simp] theorem prime_spectrum_prod_symm_inr_as_ideal {R : Type u} [comm_ring R] {S : Type v} [comm_ring S] (x : prime_spectrum S) : as_ideal (coe_fn (equiv.symm (prime_spectrum_prod R S)) (sum.inr x)) = ideal.prod ⊤ (as_ideal x) := sorry

theorem ext {R : Type u} [comm_ring R] {x : prime_spectrum R} {y : prime_spectrum R} : x = y ↔ as_ideal x = as_ideal y :=
  subtype.ext_iff_val

/-- The zero locus of a set `s` of elements of a commutative ring `R`
is the set of all prime ideals of the ring that contain the set `s`.

An element `f` of `R` can be thought of as a dependent function
on the prime spectrum of `R`.
At a point `x` (a prime ideal)
the function (i.e., element) `f` takes values in the quotient ring `R` modulo the prime ideal `x`.
In this manner, `zero_locus s` is exactly the subset of `prime_spectrum R`
where all "functions" in `s` vanish simultaneously.
-/
def zero_locus {R : Type u} [comm_ring R] (s : set R) : set (prime_spectrum R) :=
  set_of fun (x : prime_spectrum R) => s ⊆ ↑(as_ideal x)

@[simp] theorem mem_zero_locus {R : Type u} [comm_ring R] (x : prime_spectrum R) (s : set R) : x ∈ zero_locus s ↔ s ⊆ ↑(as_ideal x) :=
  iff.rfl

@[simp] theorem zero_locus_span {R : Type u} [comm_ring R] (s : set R) : zero_locus ↑(ideal.span s) = zero_locus s :=
  set.ext fun (x : prime_spectrum R) => galois_insertion.gc (submodule.gi R R) s (as_ideal x)

/-- The vanishing ideal of a set `t` of points
of the prime spectrum of a commutative ring `R`
is the intersection of all the prime ideals in the set `t`.

An element `f` of `R` can be thought of as a dependent function
on the prime spectrum of `R`.
At a point `x` (a prime ideal)
the function (i.e., element) `f` takes values in the quotient ring `R` modulo the prime ideal `x`.
In this manner, `vanishing_ideal t` is exactly the ideal of `R`
consisting of all "functions" that vanish on all of `t`.
-/
def vanishing_ideal {R : Type u} [comm_ring R] (t : set (prime_spectrum R)) : ideal R :=
  infi fun (x : prime_spectrum R) => infi fun (h : x ∈ t) => as_ideal x

theorem coe_vanishing_ideal {R : Type u} [comm_ring R] (t : set (prime_spectrum R)) : ↑(vanishing_ideal t) = set_of fun (f : R) => ∀ (x : prime_spectrum R), x ∈ t → f ∈ as_ideal x := sorry

theorem mem_vanishing_ideal {R : Type u} [comm_ring R] (t : set (prime_spectrum R)) (f : R) : f ∈ vanishing_ideal t ↔ ∀ (x : prime_spectrum R), x ∈ t → f ∈ as_ideal x := sorry

theorem subset_zero_locus_iff_le_vanishing_ideal {R : Type u} [comm_ring R] (t : set (prime_spectrum R)) (I : ideal R) : t ⊆ zero_locus ↑I ↔ I ≤ vanishing_ideal t := sorry

/-- `zero_locus` and `vanishing_ideal` form a galois connection. -/
theorem gc (R : Type u) [comm_ring R] : galois_connection (fun (I : ideal R) => zero_locus ↑I)
  fun (t : order_dual (set (prime_spectrum R))) => vanishing_ideal t :=
  fun (I : ideal R) (t : order_dual (set (prime_spectrum R))) => subset_zero_locus_iff_le_vanishing_ideal t I

/-- `zero_locus` and `vanishing_ideal` form a galois connection. -/
theorem gc_set (R : Type u) [comm_ring R] : galois_connection (fun (s : set R) => zero_locus s)
  fun (t : order_dual (set (prime_spectrum R))) => ↑(vanishing_ideal t) := sorry

theorem subset_zero_locus_iff_subset_vanishing_ideal (R : Type u) [comm_ring R] (t : set (prime_spectrum R)) (s : set R) : t ⊆ zero_locus s ↔ s ⊆ ↑(vanishing_ideal t) :=
  gc_set R s t

-- TODO: we actually get the radical ideal,

-- but I think that isn't in mathlib yet.

theorem subset_vanishing_ideal_zero_locus {R : Type u} [comm_ring R] (s : set R) : s ⊆ ↑(vanishing_ideal (zero_locus s)) :=
  galois_connection.le_u_l (gc_set R) s

theorem le_vanishing_ideal_zero_locus {R : Type u} [comm_ring R] (I : ideal R) : I ≤ vanishing_ideal (zero_locus ↑I) :=
  galois_connection.le_u_l (gc R) I

theorem subset_zero_locus_vanishing_ideal {R : Type u} [comm_ring R] (t : set (prime_spectrum R)) : t ⊆ zero_locus ↑(vanishing_ideal t) :=
  galois_connection.l_u_le (gc R) t

theorem zero_locus_bot {R : Type u} [comm_ring R] : zero_locus ↑⊥ = set.univ :=
  galois_connection.l_bot (gc R)

@[simp] theorem zero_locus_singleton_zero {R : Type u} [comm_ring R] : zero_locus 0 = set.univ :=
  zero_locus_bot

@[simp] theorem zero_locus_empty {R : Type u} [comm_ring R] : zero_locus ∅ = set.univ :=
  galois_connection.l_bot (gc_set R)

@[simp] theorem vanishing_ideal_univ {R : Type u} [comm_ring R] : vanishing_ideal ∅ = ⊤ :=
  eq.mpr (id (Eq.refl (vanishing_ideal ∅ = ⊤))) (eq.mp (Eq.refl (vanishing_ideal ⊤ = ⊤)) (galois_connection.u_top (gc R)))

theorem zero_locus_empty_of_one_mem {R : Type u} [comm_ring R] {s : set R} (h : 1 ∈ s) : zero_locus s = ∅ := sorry

theorem zero_locus_empty_iff_eq_top {R : Type u} [comm_ring R] {I : ideal R} : zero_locus ↑I = ∅ ↔ I = ⊤ := sorry

@[simp] theorem zero_locus_univ {R : Type u} [comm_ring R] : zero_locus set.univ = ∅ :=
  zero_locus_empty_of_one_mem (set.mem_univ 1)

theorem zero_locus_sup {R : Type u} [comm_ring R] (I : ideal R) (J : ideal R) : zero_locus ↑(I ⊔ J) = zero_locus ↑I ∩ zero_locus ↑J :=
  galois_connection.l_sup (gc R)

theorem zero_locus_union {R : Type u} [comm_ring R] (s : set R) (s' : set R) : zero_locus (s ∪ s') = zero_locus s ∩ zero_locus s' :=
  galois_connection.l_sup (gc_set R)

theorem vanishing_ideal_union {R : Type u} [comm_ring R] (t : set (prime_spectrum R)) (t' : set (prime_spectrum R)) : vanishing_ideal (t ∪ t') = vanishing_ideal t ⊓ vanishing_ideal t' :=
  galois_connection.u_inf (gc R)

theorem zero_locus_supr {R : Type u} [comm_ring R] {ι : Sort u_1} (I : ι → ideal R) : zero_locus ↑(supr fun (i : ι) => I i) = set.Inter fun (i : ι) => zero_locus ↑(I i) :=
  galois_connection.l_supr (gc R)

theorem zero_locus_Union {R : Type u} [comm_ring R] {ι : Sort u_1} (s : ι → set R) : zero_locus (set.Union fun (i : ι) => s i) = set.Inter fun (i : ι) => zero_locus (s i) :=
  galois_connection.l_supr (gc_set R)

theorem zero_locus_bUnion {R : Type u} [comm_ring R] (s : set (set R)) : zero_locus (set.Union fun (s' : set R) => set.Union fun (H : s' ∈ s) => s') =
  set.Inter fun (s' : set R) => set.Inter fun (H : s' ∈ s) => zero_locus s' := sorry

theorem vanishing_ideal_Union {R : Type u} [comm_ring R] {ι : Sort u_1} (t : ι → set (prime_spectrum R)) : vanishing_ideal (set.Union fun (i : ι) => t i) = infi fun (i : ι) => vanishing_ideal (t i) :=
  galois_connection.u_infi (gc R)

theorem zero_locus_inf {R : Type u} [comm_ring R] (I : ideal R) (J : ideal R) : zero_locus ↑(I ⊓ J) = zero_locus ↑I ∪ zero_locus ↑J := sorry

theorem union_zero_locus {R : Type u} [comm_ring R] (s : set R) (s' : set R) : zero_locus s ∪ zero_locus s' = zero_locus ↑(ideal.span s ⊓ ideal.span s') := sorry

theorem sup_vanishing_ideal_le {R : Type u} [comm_ring R] (t : set (prime_spectrum R)) (t' : set (prime_spectrum R)) : vanishing_ideal t ⊔ vanishing_ideal t' ≤ vanishing_ideal (t ∩ t') := sorry

theorem mem_compl_zero_locus_iff_not_mem {R : Type u} [comm_ring R] {f : R} {I : prime_spectrum R} : I ∈ (zero_locus (singleton f)ᶜ) ↔ ¬f ∈ as_ideal I := sorry

/-- The Zariski topology on the prime spectrum of a commutative ring
is defined via the closed sets of the topology:
they are exactly those sets that are the zero locus of a subset of the ring. -/
protected instance zariski_topology {R : Type u} [comm_ring R] : topological_space (prime_spectrum R) :=
  topological_space.of_closed (set.range zero_locus) sorry sorry sorry

theorem is_open_iff {R : Type u} [comm_ring R] (U : set (prime_spectrum R)) : is_open U ↔ ∃ (s : set R), Uᶜ = zero_locus s := sorry

theorem is_closed_iff_zero_locus {R : Type u} [comm_ring R] (Z : set (prime_spectrum R)) : is_closed Z ↔ ∃ (s : set R), Z = zero_locus s := sorry

theorem is_closed_zero_locus {R : Type u} [comm_ring R] (s : set R) : is_closed (zero_locus s) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_closed (zero_locus s))) (propext (is_closed_iff_zero_locus (zero_locus s)))))
    (Exists.intro s rfl)

/-- The function between prime spectra of commutative rings induced by a ring homomorphism.
This function is continuous. -/
def comap {R : Type u} [comm_ring R] {S : Type v} [comm_ring S] (f : R →+* S) : prime_spectrum S → prime_spectrum R :=
  fun (y : prime_spectrum S) => { val := ideal.comap f (as_ideal y), property := sorry }

@[simp] theorem comap_as_ideal {R : Type u} [comm_ring R] {S : Type v} [comm_ring S] (f : R →+* S) (y : prime_spectrum S) : as_ideal (comap f y) = ideal.comap f (as_ideal y) :=
  rfl

@[simp] theorem comap_id {R : Type u} [comm_ring R] : comap (ring_hom.id R) = id :=
  funext fun (_x : prime_spectrum R) => subtype.ext (ideal.ext fun (_x_1 : R) => iff.rfl)

@[simp] theorem comap_comp {R : Type u} [comm_ring R] {S : Type v} [comm_ring S] {S' : Type u_1} [comm_ring S'] (f : R →+* S) (g : S →+* S') : comap (ring_hom.comp g f) = comap f ∘ comap g :=
  funext fun (_x : prime_spectrum S') => subtype.ext (ideal.ext fun (_x_1 : R) => iff.rfl)

@[simp] theorem preimage_comap_zero_locus {R : Type u} [comm_ring R] {S : Type v} [comm_ring S] (f : R →+* S) (s : set R) : comap f ⁻¹' zero_locus s = zero_locus (⇑f '' s) := sorry

theorem comap_continuous {R : Type u} [comm_ring R] {S : Type v} [comm_ring S] (f : R →+* S) : continuous (comap f) := sorry

theorem zero_locus_vanishing_ideal_eq_closure {R : Type u} [comm_ring R] (t : set (prime_spectrum R)) : zero_locus ↑(vanishing_ideal t) = closure t := sorry

/-- The prime spectrum of a commutative ring is a compact topological space. -/
protected instance compact_space {R : Type u} [comm_ring R] : compact_space (prime_spectrum R) := sorry

/-- `basic_open r` is the open subset containing all prime ideals not containing `r`. -/
def basic_open {R : Type u} [comm_ring R] (r : R) : topological_space.opens (prime_spectrum R) :=
  { val := set_of fun (x : prime_spectrum R) => ¬r ∈ as_ideal x, property := sorry }

theorem is_open_basic_open {R : Type u} [comm_ring R] {a : R} : is_open ↑(basic_open a) :=
  subtype.property (basic_open a)

