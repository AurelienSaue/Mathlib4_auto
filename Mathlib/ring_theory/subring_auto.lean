/-
Copyright (c) 2020 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors : Ashvni Narayanan
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.deprecated.subring
import Mathlib.group_theory.subgroup
import Mathlib.ring_theory.subsemiring
import Mathlib.PostPort

universes u l u_1 u_2 v w 

namespace Mathlib

/-!
# Subrings

Let `R` be a ring. This file defines the "bundled" subring type `subring R`, a type
whose terms correspond to subrings of `R`. This is the preferred way to talk
about subrings in mathlib. Unbundled subrings (`s : set R` and `is_subring s`)
are not in this file, and they will ultimately be deprecated.

We prove that subrings are a complete lattice, and that you can `map` (pushforward) and
`comap` (pull back) them along ring homomorphisms.

We define the `closure` construction from `set R` to `subring R`, sending a subset of `R`
to the subring it generates, and prove that it is a Galois insertion.

## Main definitions

Notation used here:

`(R : Type u) [ring R] (S : Type u) [ring S] (f g : R →+* S)`
`(A : subring R) (B : subring S) (s : set R)`

* `subring R` : the type of subrings of a ring `R`.

* `instance : complete_lattice (subring R)` : the complete lattice structure on the subrings.

* `subring.closure` : subring closure of a set, i.e., the smallest subring that includes the set.

* `subring.gi` : `closure : set M → subring M` and coercion `coe : subring M → set M`
  form a `galois_insertion`.

* `comap f B : subring A` : the preimage of a subring `B` along the ring homomorphism `f`

* `map f A : subring B` : the image of a subring `A` along the ring homomorphism `f`.

* `prod A B : subring (R × S)` : the product of subrings

* `f.range : subring B` : the range of the ring homomorphism `f`.

* `eq_locus f g : subring R` : given ring homomorphisms `f g : R →+* S`,
     the subring of `R` where `f x = g x`

## Implementation notes

A subring is implemented as a subsemiring which is also an additive subgroup.
The initial PR was as a submonoid which is also an additive subgroup.

Lattice inclusion (e.g. `≤` and `⊓`) is used rather than set notation (`⊆` and `∩`), although
`∈` is defined as membership of a subring's underlying set.

## Tags
subring, subrings
-/

/-- `subring R` is the type of subrings of `R`. A subring of `R` is a subset `s` that is a
  multiplicative submonoid and an additive subgroup. Note in particular that it shares the
  same 0 and 1 as R. -/
structure subring (R : Type u) [ring R] extends subsemiring R, add_subgroup R where

/-- Reinterpret a `subring` as a `subsemiring`. -/
/-- Reinterpret a `subring` as an `add_subgroup`. -/
namespace subring


/-- The underlying submonoid of a subring. -/
def to_submonoid {R : Type u} [ring R] (s : subring R) : submonoid R :=
  submonoid.mk (carrier s) sorry sorry

protected instance set.has_coe {R : Type u} [ring R] : has_coe (subring R) (set R) :=
  has_coe.mk carrier

protected instance has_mem {R : Type u} [ring R] : has_mem R (subring R) :=
  has_mem.mk fun (m : R) (S : subring R) => m ∈ ↑S

protected instance has_coe_to_sort {R : Type u} [ring R] : has_coe_to_sort (subring R) :=
  has_coe_to_sort.mk (Type u) fun (S : subring R) => Subtype fun (x : R) => x ∈ S

/-- Construct a `subring R` from a set `s`, a submonoid `sm`, and an additive
subgroup `sa` such that `x ∈ s ↔ x ∈ sm ↔ x ∈ sa`. -/
protected def mk' {R : Type u} [ring R] (s : set R) (sm : submonoid R) (sa : add_subgroup R)
    (hm : ↑sm = s) (ha : ↑sa = s) : subring R :=
  mk s sorry sorry sorry sorry sorry

@[simp] theorem coe_mk' {R : Type u} [ring R] {s : set R} {sm : submonoid R} (hm : ↑sm = s)
    {sa : add_subgroup R} (ha : ↑sa = s) : ↑(subring.mk' s sm sa hm ha) = s :=
  rfl

@[simp] theorem mem_mk' {R : Type u} [ring R] {s : set R} {sm : submonoid R} (hm : ↑sm = s)
    {sa : add_subgroup R} (ha : ↑sa = s) {x : R} : x ∈ subring.mk' s sm sa hm ha ↔ x ∈ s :=
  iff.rfl

@[simp] theorem mk'_to_submonoid {R : Type u} [ring R] {s : set R} {sm : submonoid R} (hm : ↑sm = s)
    {sa : add_subgroup R} (ha : ↑sa = s) : to_submonoid (subring.mk' s sm sa hm ha) = sm :=
  submonoid.ext' (Eq.symm hm)

@[simp] theorem mk'_to_add_subgroup {R : Type u} [ring R] {s : set R} {sm : submonoid R}
    (hm : ↑sm = s) {sa : add_subgroup R} (ha : ↑sa = s) :
    to_add_subgroup (subring.mk' s sm sa hm ha) = sa :=
  add_subgroup.ext' (Eq.symm ha)

end subring


/-- Construct a `subring` from a set satisfying `is_subring`. -/
def set.to_subring {R : Type u} [ring R] (S : set R) [is_subring S] : subring R :=
  subring.mk S sorry sorry sorry sorry sorry

protected theorem subring.exists {R : Type u} [ring R] {s : subring R} {p : ↥s → Prop} :
    (∃ (x : ↥s), p x) ↔ ∃ (x : R), ∃ (H : x ∈ s), p { val := x, property := H } :=
  set_coe.exists

protected theorem subring.forall {R : Type u} [ring R] {s : subring R} {p : ↥s → Prop} :
    (∀ (x : ↥s), p x) ↔ ∀ (x : R) (H : x ∈ s), p { val := x, property := H } :=
  set_coe.forall

/-- A `subsemiring` containing -1 is a `subring`. -/
def subsemiring.to_subring {R : Type u} [ring R] (s : subsemiring R) (hneg : -1 ∈ s) : subring R :=
  subring.mk (submonoid.carrier (subsemiring.to_submonoid s)) sorry sorry sorry sorry sorry

namespace subring


/-- Two subrings are equal if the underlying subsets are equal. -/
theorem ext' {R : Type u} [ring R] {s : subring R} {t : subring R} (h : ↑s = ↑t) : s = t := sorry

/-- Two subrings are equal if and only if the underlying subsets are equal. -/
protected theorem ext'_iff {R : Type u} [ring R] {s : subring R} {t : subring R} :
    s = t ↔ ↑s = ↑t :=
  { mp := fun (h : s = t) => h ▸ rfl, mpr := fun (h : ↑s = ↑t) => ext' h }

/-- Two subrings are equal if they have the same elements. -/
theorem ext {R : Type u} [ring R] {S : subring R} {T : subring R} (h : ∀ (x : R), x ∈ S ↔ x ∈ T) :
    S = T :=
  ext' (set.ext h)

/-- A subring contains the ring's 1. -/
theorem one_mem {R : Type u} [ring R] (s : subring R) : 1 ∈ s := one_mem' s

/-- A subring contains the ring's 0. -/
theorem zero_mem {R : Type u} [ring R] (s : subring R) : 0 ∈ s := zero_mem' s

/-- A subring is closed under multiplication. -/
theorem mul_mem {R : Type u} [ring R] (s : subring R) {x : R} {y : R} : x ∈ s → y ∈ s → x * y ∈ s :=
  mul_mem' s

/-- A subring is closed under addition. -/
theorem add_mem {R : Type u} [ring R] (s : subring R) {x : R} {y : R} : x ∈ s → y ∈ s → x + y ∈ s :=
  add_mem' s

/-- A subring is closed under negation. -/
theorem neg_mem {R : Type u} [ring R] (s : subring R) {x : R} : x ∈ s → -x ∈ s := neg_mem' s

/-- A subring is closed under subtraction -/
theorem sub_mem {R : Type u} [ring R] (s : subring R) {x : R} {y : R} (hx : x ∈ s) (hy : y ∈ s) :
    x - y ∈ s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (x - y ∈ s)) (sub_eq_add_neg x y))) (add_mem s hx (neg_mem s hy))

/-- Product of a list of elements in a subring is in the subring. -/
theorem list_prod_mem {R : Type u} [ring R] (s : subring R) {l : List R} :
    (∀ (x : R), x ∈ l → x ∈ s) → list.prod l ∈ s :=
  submonoid.list_prod_mem (to_submonoid s)

/-- Sum of a list of elements in a subring is in the subring. -/
theorem list_sum_mem {R : Type u} [ring R] (s : subring R) {l : List R} :
    (∀ (x : R), x ∈ l → x ∈ s) → list.sum l ∈ s :=
  add_subgroup.list_sum_mem (to_add_subgroup s)

/-- Product of a multiset of elements in a subring of a `comm_ring` is in the subring. -/
theorem multiset_prod_mem {R : Type u_1} [comm_ring R] (s : subring R) (m : multiset R) :
    (∀ (a : R), a ∈ m → a ∈ s) → multiset.prod m ∈ s :=
  submonoid.multiset_prod_mem (to_submonoid s) m

/-- Sum of a multiset of elements in an `subring` of a `ring` is
in the `subring`. -/
theorem multiset_sum_mem {R : Type u_1} [ring R] (s : subring R) (m : multiset R) :
    (∀ (a : R), a ∈ m → a ∈ s) → multiset.sum m ∈ s :=
  add_subgroup.multiset_sum_mem (to_add_subgroup s) m

/-- Product of elements of a subring of a `comm_ring` indexed by a `finset` is in the
    subring. -/
theorem prod_mem {R : Type u_1} [comm_ring R] (s : subring R) {ι : Type u_2} {t : finset ι}
    {f : ι → R} (h : ∀ (c : ι), c ∈ t → f c ∈ s) : (finset.prod t fun (i : ι) => f i) ∈ s :=
  submonoid.prod_mem (to_submonoid s) h

/-- Sum of elements in a `subring` of a `ring` indexed by a `finset`
is in the `subring`. -/
theorem sum_mem {R : Type u_1} [ring R] (s : subring R) {ι : Type u_2} {t : finset ι} {f : ι → R}
    (h : ∀ (c : ι), c ∈ t → f c ∈ s) : (finset.sum t fun (i : ι) => f i) ∈ s :=
  add_subgroup.sum_mem (to_add_subgroup s) h

theorem pow_mem {R : Type u} [ring R] (s : subring R) {x : R} (hx : x ∈ s) (n : ℕ) : x ^ n ∈ s :=
  submonoid.pow_mem (to_submonoid s) hx n

theorem gsmul_mem {R : Type u} [ring R] (s : subring R) {x : R} (hx : x ∈ s) (n : ℤ) : n •ℤ x ∈ s :=
  add_subgroup.gsmul_mem (to_add_subgroup s) hx n

theorem coe_int_mem {R : Type u} [ring R] (s : subring R) (n : ℤ) : ↑n ∈ s := sorry

/-- A subring of a ring inherits a ring structure -/
protected instance to_ring {R : Type u} [ring R] (s : subring R) : ring ↥s :=
  ring.mk add_comm_group.add sorry add_comm_group.zero sorry sorry add_comm_group.neg
    add_comm_group.sub sorry sorry monoid.mul sorry monoid.one sorry sorry sorry sorry

@[simp] theorem coe_add {R : Type u} [ring R] (s : subring R) (x : ↥s) (y : ↥s) :
    ↑(x + y) = ↑x + ↑y :=
  rfl

@[simp] theorem coe_neg {R : Type u} [ring R] (s : subring R) (x : ↥s) : ↑(-x) = -↑x := rfl

@[simp] theorem coe_mul {R : Type u} [ring R] (s : subring R) (x : ↥s) (y : ↥s) :
    ↑(x * y) = ↑x * ↑y :=
  rfl

@[simp] theorem coe_zero {R : Type u} [ring R] (s : subring R) : ↑0 = 0 := rfl

@[simp] theorem coe_one {R : Type u} [ring R] (s : subring R) : ↑1 = 1 := rfl

@[simp] theorem coe_eq_zero_iff {R : Type u} [ring R] (s : subring R) {x : ↥s} : ↑x = 0 ↔ x = 0 :=
  { mp := fun (h : ↑x = 0) => subtype.ext (trans h (Eq.symm (coe_zero s))),
    mpr := fun (h : x = 0) => Eq.symm h ▸ coe_zero s }

/-- A subring of a `comm_ring` is a `comm_ring`. -/
protected instance to_comm_ring {R : Type u_1} [comm_ring R] (s : subring R) : comm_ring ↥s :=
  comm_ring.mk ring.add sorry ring.zero sorry sorry ring.neg ring.sub sorry sorry ring.mul sorry
    ring.one sorry sorry sorry sorry sorry

/-- The natural ring hom from a subring of ring `R` to `R`. -/
def subtype {R : Type u} [ring R] (s : subring R) : ↥s →+* R :=
  ring_hom.mk coe sorry sorry sorry sorry

@[simp] theorem coe_subtype {R : Type u} [ring R] (s : subring R) : ⇑(subtype s) = coe := rfl

/-! # Partial order -/

protected instance partial_order {R : Type u} [ring R] : partial_order (subring R) :=
  partial_order.mk (fun (s t : subring R) => ∀ {x : R}, x ∈ s → x ∈ t) partial_order.lt sorry sorry
    sorry

theorem le_def {R : Type u} [ring R] {s : subring R} {t : subring R} :
    s ≤ t ↔ ∀ {x : R}, x ∈ s → x ∈ t :=
  iff.rfl

@[simp] theorem coe_subset_coe {R : Type u} [ring R] {s : subring R} {t : subring R} :
    ↑s ⊆ ↑t ↔ s ≤ t :=
  iff.rfl

@[simp] theorem coe_ssubset_coe {R : Type u} [ring R] {s : subring R} {t : subring R} :
    ↑s ⊂ ↑t ↔ s < t :=
  iff.rfl

@[simp] theorem mem_coe {R : Type u} [ring R] {S : subring R} {m : R} : m ∈ ↑S ↔ m ∈ S := iff.rfl

@[simp] theorem coe_coe {R : Type u} [ring R] (s : subring R) : ↥↑s = ↥s := rfl

@[simp] theorem mem_to_submonoid {R : Type u} [ring R] {s : subring R} {x : R} :
    x ∈ to_submonoid s ↔ x ∈ s :=
  iff.rfl

@[simp] theorem coe_to_submonoid {R : Type u} [ring R] (s : subring R) : ↑(to_submonoid s) = ↑s :=
  rfl

@[simp] theorem mem_to_add_subgroup {R : Type u} [ring R] {s : subring R} {x : R} :
    x ∈ to_add_subgroup s ↔ x ∈ s :=
  iff.rfl

@[simp] theorem coe_to_add_subgroup {R : Type u} [ring R] (s : subring R) :
    ↑(to_add_subgroup s) = ↑s :=
  rfl

/-! # top -/

/-- The subring `R` of the ring `R`. -/
protected instance has_top {R : Type u} [ring R] : has_top (subring R) :=
  has_top.mk (mk (submonoid.carrier ⊤) sorry sorry sorry sorry sorry)

@[simp] theorem mem_top {R : Type u} [ring R] (x : R) : x ∈ ⊤ := set.mem_univ x

@[simp] theorem coe_top {R : Type u} [ring R] : ↑⊤ = set.univ := rfl

/-! # comap -/

/-- The preimage of a subring along a ring homomorphism is a subring. -/
def comap {R : Type u} {S : Type v} [ring R] [ring S] (f : R →+* S) (s : subring S) : subring R :=
  mk (⇑f ⁻¹' carrier s) sorry sorry sorry sorry sorry

@[simp] theorem coe_comap {R : Type u} {S : Type v} [ring R] [ring S] (s : subring S)
    (f : R →+* S) : ↑(comap f s) = ⇑f ⁻¹' ↑s :=
  rfl

@[simp] theorem mem_comap {R : Type u} {S : Type v} [ring R] [ring S] {s : subring S} {f : R →+* S}
    {x : R} : x ∈ comap f s ↔ coe_fn f x ∈ s :=
  iff.rfl

theorem comap_comap {R : Type u} {S : Type v} {T : Type w} [ring R] [ring S] [ring T]
    (s : subring T) (g : S →+* T) (f : R →+* S) :
    comap f (comap g s) = comap (ring_hom.comp g f) s :=
  rfl

/-! # map -/

/-- The image of a subring along a ring homomorphism is a subring. -/
def map {R : Type u} {S : Type v} [ring R] [ring S] (f : R →+* S) (s : subring R) : subring S :=
  mk (⇑f '' carrier s) sorry sorry sorry sorry sorry

@[simp] theorem coe_map {R : Type u} {S : Type v} [ring R] [ring S] (f : R →+* S) (s : subring R) :
    ↑(map f s) = ⇑f '' ↑s :=
  rfl

@[simp] theorem mem_map {R : Type u} {S : Type v} [ring R] [ring S] {f : R →+* S} {s : subring R}
    {y : S} : y ∈ map f s ↔ ∃ (x : R), ∃ (H : x ∈ s), coe_fn f x = y :=
  set.mem_image_iff_bex

theorem map_map {R : Type u} {S : Type v} {T : Type w} [ring R] [ring S] [ring T] (s : subring R)
    (g : S →+* T) (f : R →+* S) : map g (map f s) = map (ring_hom.comp g f) s :=
  ext' (set.image_image (fun (a : S) => coe_fn g a) (fun (a : R) => coe_fn f a) (carrier s))

theorem map_le_iff_le_comap {R : Type u} {S : Type v} [ring R] [ring S] {f : R →+* S}
    {s : subring R} {t : subring S} : map f s ≤ t ↔ s ≤ comap f t :=
  set.image_subset_iff

theorem gc_map_comap {R : Type u} {S : Type v} [ring R] [ring S] (f : R →+* S) :
    galois_connection (map f) (comap f) :=
  fun (S_1 : subring R) (T : subring S) => map_le_iff_le_comap

end subring


namespace ring_hom


/-! # range -/

/-- The range of a ring homomorphism, as a subring of the target. -/
def range {R : Type u} {S : Type v} [ring R] [ring S] (f : R →+* S) : subring S := subring.map f ⊤

@[simp] theorem coe_range {R : Type u} {S : Type v} [ring R] [ring S] (f : R →+* S) :
    ↑(range f) = set.range ⇑f :=
  set.image_univ

@[simp] theorem mem_range {R : Type u} {S : Type v} [ring R] [ring S] {f : R →+* S} {y : S} :
    y ∈ range f ↔ ∃ (x : R), coe_fn f x = y :=
  sorry

theorem mem_range_self {R : Type u} {S : Type v} [ring R] [ring S] (f : R →+* S) (x : R) :
    coe_fn f x ∈ range f :=
  iff.mpr mem_range (Exists.intro x rfl)

theorem map_range {R : Type u} {S : Type v} {T : Type w} [ring R] [ring S] [ring T] (g : S →+* T)
    (f : R →+* S) : subring.map g (range f) = range (comp g f) :=
  subring.map_map ⊤ g f

-- TODO -- rename to `cod_restrict` when is_ring_hom is deprecated

/-- Restrict the codomain of a ring homomorphism to a subring that includes the range. -/
def cod_restrict' {R : Type u} {S : Type v} [ring R] [ring S] (f : R →+* S) (s : subring S)
    (h : ∀ (x : R), coe_fn f x ∈ s) : R →+* ↥s :=
  mk (fun (x : R) => { val := coe_fn f x, property := h x }) sorry sorry sorry sorry

theorem surjective_onto_range {R : Type u} {S : Type v} [ring R] [ring S] (f : R →+* S) :
    function.surjective ⇑(cod_restrict' f (range f) (mem_range_self f)) :=
  sorry

end ring_hom


namespace subring


/-- A subring of a commutative ring is a commutative ring. -/
def subset_comm_ring {cR : Type u} [comm_ring cR] (S : subring cR) : comm_ring ↥S :=
  comm_ring.mk ring.add sorry ring.zero sorry sorry ring.neg ring.sub sorry sorry ring.mul sorry
    ring.one sorry sorry sorry sorry sorry

/-- A subring of a non-trivial ring is non-trivial. -/
protected instance nontrivial {D : Type u_1} [ring D] [nontrivial D] (S : subring D) :
    nontrivial ↥S :=
  subsemiring.nontrivial (to_subsemiring S)

/-- A subring of a ring with no zero divisors has no zero divisors. -/
protected instance no_zero_divisors {D : Type u_1} [ring D] [no_zero_divisors D] (S : subring D) :
    no_zero_divisors ↥S :=
  subsemiring.no_zero_divisors (to_subsemiring S)

/-- A subring of an integral domain is an integral domain. -/
protected instance subring.domain {D : Type u_1} [integral_domain D] (S : subring D) :
    integral_domain ↥S :=
  integral_domain.mk comm_ring.add sorry comm_ring.zero sorry sorry comm_ring.neg comm_ring.sub
    sorry sorry comm_ring.mul sorry comm_ring.one sorry sorry sorry sorry sorry sorry sorry

/-! # bot -/

protected instance has_bot {R : Type u} [ring R] : has_bot (subring R) :=
  has_bot.mk (ring_hom.range (int.cast_ring_hom R))

protected instance inhabited {R : Type u} [ring R] : Inhabited (subring R) := { default := ⊥ }

theorem coe_bot {R : Type u} [ring R] : ↑⊥ = set.range coe :=
  ring_hom.coe_range (int.cast_ring_hom R)

theorem mem_bot {R : Type u} [ring R] {x : R} : x ∈ ⊥ ↔ ∃ (n : ℤ), ↑n = x := ring_hom.mem_range

/-! # inf -/

/-- The inf of two subrings is their intersection. -/
protected instance has_inf {R : Type u} [ring R] : has_inf (subring R) :=
  has_inf.mk fun (s t : subring R) => mk (↑s ∩ ↑t) sorry sorry sorry sorry sorry

@[simp] theorem coe_inf {R : Type u} [ring R] (p : subring R) (p' : subring R) :
    ↑(p ⊓ p') = ↑p ∩ ↑p' :=
  rfl

@[simp] theorem mem_inf {R : Type u} [ring R] {p : subring R} {p' : subring R} {x : R} :
    x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' :=
  iff.rfl

protected instance has_Inf {R : Type u} [ring R] : has_Inf (subring R) :=
  has_Inf.mk
    fun (s : set (subring R)) =>
      subring.mk' (set.Inter fun (t : subring R) => set.Inter fun (H : t ∈ s) => ↑t)
        (infi fun (t : subring R) => infi fun (H : t ∈ s) => to_submonoid t)
        (infi fun (t : subring R) => infi fun (H : t ∈ s) => to_add_subgroup t) sorry sorry

@[simp] theorem coe_Inf {R : Type u} [ring R] (S : set (subring R)) :
    ↑(Inf S) = set.Inter fun (s : subring R) => set.Inter fun (H : s ∈ S) => ↑s :=
  rfl

theorem mem_Inf {R : Type u} [ring R] {S : set (subring R)} {x : R} :
    x ∈ Inf S ↔ ∀ (p : subring R), p ∈ S → x ∈ p :=
  set.mem_bInter_iff

@[simp] theorem Inf_to_submonoid {R : Type u} [ring R] (s : set (subring R)) :
    to_submonoid (Inf s) = infi fun (t : subring R) => infi fun (H : t ∈ s) => to_submonoid t :=
  mk'_to_submonoid (has_Inf._proof_1 s) (has_Inf._proof_2 s)

@[simp] theorem Inf_to_add_subgroup {R : Type u} [ring R] (s : set (subring R)) :
    to_add_subgroup (Inf s) =
        infi fun (t : subring R) => infi fun (H : t ∈ s) => to_add_subgroup t :=
  mk'_to_add_subgroup (has_Inf._proof_1 s) (has_Inf._proof_2 s)

/-- Subrings of a ring form a complete lattice. -/
protected instance complete_lattice {R : Type u} [ring R] : complete_lattice (subring R) :=
  complete_lattice.mk complete_lattice.sup complete_lattice.le complete_lattice.lt sorry sorry sorry
    sorry sorry sorry has_inf.inf sorry sorry sorry ⊤ sorry ⊥ sorry complete_lattice.Sup
    complete_lattice.Inf sorry sorry sorry sorry

/-! # subring closure of a subset -/

/-- The `subring` generated by a set. -/
def closure {R : Type u} [ring R] (s : set R) : subring R :=
  Inf (set_of fun (S : subring R) => s ⊆ ↑S)

theorem mem_closure {R : Type u} [ring R] {x : R} {s : set R} :
    x ∈ closure s ↔ ∀ (S : subring R), s ⊆ ↑S → x ∈ S :=
  mem_Inf

/-- The subring generated by a set includes the set. -/
@[simp] theorem subset_closure {R : Type u} [ring R] {s : set R} : s ⊆ ↑(closure s) :=
  fun (x : R) (hx : x ∈ s) => iff.mpr mem_closure fun (S : subring R) (hS : s ⊆ ↑S) => hS hx

/-- A subring `t` includes `closure s` if and only if it includes `s`. -/
@[simp] theorem closure_le {R : Type u} [ring R] {s : set R} {t : subring R} :
    closure s ≤ t ↔ s ⊆ ↑t :=
  { mp := set.subset.trans subset_closure, mpr := fun (h : s ⊆ ↑t) => Inf_le h }

/-- Subring closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
theorem closure_mono {R : Type u} [ring R] {s : set R} {t : set R} (h : s ⊆ t) :
    closure s ≤ closure t :=
  iff.mpr closure_le (set.subset.trans h subset_closure)

theorem closure_eq_of_le {R : Type u} [ring R] {s : set R} {t : subring R} (h₁ : s ⊆ ↑t)
    (h₂ : t ≤ closure s) : closure s = t :=
  le_antisymm (iff.mpr closure_le h₁) h₂

/-- An induction principle for closure membership. If `p` holds for `0`, `1`, and all elements
of `s`, and is preserved under addition, negation, and multiplication, then `p` holds for all elements
of the closure of `s`. -/
theorem closure_induction {R : Type u} [ring R] {s : set R} {p : R → Prop} {x : R}
    (h : x ∈ closure s) (Hs : ∀ (x : R), x ∈ s → p x) (H0 : p 0) (H1 : p 1)
    (Hadd : ∀ (x y : R), p x → p y → p (x + y)) (Hneg : ∀ (x : R), p x → p (-x))
    (Hmul : ∀ (x y : R), p x → p y → p (x * y)) : p x :=
  iff.mpr closure_le Hs x h

theorem mem_closure_iff {R : Type u} [ring R] {s : set R} {x : R} :
    x ∈ closure s ↔ x ∈ add_subgroup.closure ↑(submonoid.closure s) :=
  sorry

theorem exists_list_of_mem_closure {R : Type u} [ring R] {s : set R} {x : R} (h : x ∈ closure s) :
    ∃ (L : List (List R)),
        (∀ (t : List R), t ∈ L → ∀ (y : R), y ∈ t → y ∈ s ∨ y = -1) ∧
          list.sum (list.map list.prod L) = x :=
  sorry

/-- `closure` forms a Galois insertion with the coercion to set. -/
protected def gi (R : Type u) [ring R] : galois_insertion closure coe :=
  galois_insertion.mk (fun (s : set R) (_x : ↑(closure s) ≤ s) => closure s) sorry sorry sorry

/-- Closure of a subring `S` equals `S`. -/
theorem closure_eq {R : Type u} [ring R] (s : subring R) : closure ↑s = s :=
  galois_insertion.l_u_eq (subring.gi R) s

@[simp] theorem closure_empty {R : Type u} [ring R] : closure ∅ = ⊥ :=
  galois_connection.l_bot (galois_insertion.gc (subring.gi R))

@[simp] theorem closure_univ {R : Type u} [ring R] : closure set.univ = ⊤ := coe_top ▸ closure_eq ⊤

theorem closure_union {R : Type u} [ring R] (s : set R) (t : set R) :
    closure (s ∪ t) = closure s ⊔ closure t :=
  galois_connection.l_sup (galois_insertion.gc (subring.gi R))

theorem closure_Union {R : Type u} [ring R] {ι : Sort u_1} (s : ι → set R) :
    closure (set.Union fun (i : ι) => s i) = supr fun (i : ι) => closure (s i) :=
  galois_connection.l_supr (galois_insertion.gc (subring.gi R))

theorem closure_sUnion {R : Type u} [ring R] (s : set (set R)) :
    closure (⋃₀s) = supr fun (t : set R) => supr fun (H : t ∈ s) => closure t :=
  galois_connection.l_Sup (galois_insertion.gc (subring.gi R))

theorem map_sup {R : Type u} {S : Type v} [ring R] [ring S] (s : subring R) (t : subring R)
    (f : R →+* S) : map f (s ⊔ t) = map f s ⊔ map f t :=
  galois_connection.l_sup (gc_map_comap f)

theorem map_supr {R : Type u} {S : Type v} [ring R] [ring S] {ι : Sort u_1} (f : R →+* S)
    (s : ι → subring R) : map f (supr s) = supr fun (i : ι) => map f (s i) :=
  galois_connection.l_supr (gc_map_comap f)

theorem comap_inf {R : Type u} {S : Type v} [ring R] [ring S] (s : subring S) (t : subring S)
    (f : R →+* S) : comap f (s ⊓ t) = comap f s ⊓ comap f t :=
  galois_connection.u_inf (gc_map_comap f)

theorem comap_infi {R : Type u} {S : Type v} [ring R] [ring S] {ι : Sort u_1} (f : R →+* S)
    (s : ι → subring S) : comap f (infi s) = infi fun (i : ι) => comap f (s i) :=
  galois_connection.u_infi (gc_map_comap f)

@[simp] theorem map_bot {R : Type u} {S : Type v} [ring R] [ring S] (f : R →+* S) : map f ⊥ = ⊥ :=
  galois_connection.l_bot (gc_map_comap f)

@[simp] theorem comap_top {R : Type u} {S : Type v} [ring R] [ring S] (f : R →+* S) :
    comap f ⊤ = ⊤ :=
  galois_connection.u_top (gc_map_comap f)

/-- Given `subring`s `s`, `t` of rings `R`, `S` respectively, `s.prod t` is `s × t`
as a subring of `R × S`. -/
def prod {R : Type u} {S : Type v} [ring R] [ring S] (s : subring R) (t : subring S) :
    subring (R × S) :=
  mk (set.prod ↑s ↑t) sorry sorry sorry sorry sorry

theorem coe_prod {R : Type u} {S : Type v} [ring R] [ring S] (s : subring R) (t : subring S) :
    ↑(prod s t) = set.prod ↑s ↑t :=
  rfl

theorem mem_prod {R : Type u} {S : Type v} [ring R] [ring S] {s : subring R} {t : subring S}
    {p : R × S} : p ∈ prod s t ↔ prod.fst p ∈ s ∧ prod.snd p ∈ t :=
  iff.rfl

theorem prod_mono {R : Type u} {S : Type v} [ring R] [ring S] {s₁ : subring R} {s₂ : subring R}
    (hs : s₁ ≤ s₂) {t₁ : subring S} {t₂ : subring S} (ht : t₁ ≤ t₂) : prod s₁ t₁ ≤ prod s₂ t₂ :=
  set.prod_mono hs ht

theorem prod_mono_right {R : Type u} {S : Type v} [ring R] [ring S] (s : subring R) :
    monotone fun (t : subring S) => prod s t :=
  prod_mono (le_refl s)

theorem prod_mono_left {R : Type u} {S : Type v} [ring R] [ring S] (t : subring S) :
    monotone fun (s : subring R) => prod s t :=
  fun (s₁ s₂ : subring R) (hs : s₁ ≤ s₂) => prod_mono hs (le_refl t)

theorem prod_top {R : Type u} {S : Type v} [ring R] [ring S] (s : subring R) :
    prod s ⊤ = comap (ring_hom.fst R S) s :=
  sorry

theorem top_prod {R : Type u} {S : Type v} [ring R] [ring S] (s : subring S) :
    prod ⊤ s = comap (ring_hom.snd R S) s :=
  sorry

@[simp] theorem top_prod_top {R : Type u} {S : Type v} [ring R] [ring S] : prod ⊤ ⊤ = ⊤ :=
  Eq.trans (top_prod ⊤) (comap_top (ring_hom.snd R S))

/-- Product of subrings is isomorphic to their product as rings. -/
def prod_equiv {R : Type u} {S : Type v} [ring R] [ring S] (s : subring R) (t : subring S) :
    ↥(prod s t) ≃+* ↥s × ↥t :=
  ring_equiv.mk (equiv.to_fun (equiv.set.prod ↑s ↑t)) (equiv.inv_fun (equiv.set.prod ↑s ↑t)) sorry
    sorry sorry sorry

/-- The underlying set of a non-empty directed Sup of subrings is just a union of the subrings.
  Note that this fails without the directedness assumption (the union of two subrings is
  typically not a subring) -/
theorem mem_supr_of_directed {R : Type u} [ring R] {ι : Sort u_1} [hι : Nonempty ι]
    {S : ι → subring R} (hS : directed LessEq S) {x : R} :
    (x ∈ supr fun (i : ι) => S i) ↔ ∃ (i : ι), x ∈ S i :=
  sorry

theorem coe_supr_of_directed {R : Type u} [ring R] {ι : Sort u_1} [hι : Nonempty ι]
    {S : ι → subring R} (hS : directed LessEq S) :
    ↑(supr fun (i : ι) => S i) = set.Union fun (i : ι) => ↑(S i) :=
  sorry

theorem mem_Sup_of_directed_on {R : Type u} [ring R] {S : set (subring R)} (Sne : set.nonempty S)
    (hS : directed_on LessEq S) {x : R} : x ∈ Sup S ↔ ∃ (s : subring R), ∃ (H : s ∈ S), x ∈ s :=
  sorry

theorem coe_Sup_of_directed_on {R : Type u} [ring R] {S : set (subring R)} (Sne : set.nonempty S)
    (hS : directed_on LessEq S) :
    ↑(Sup S) = set.Union fun (s : subring R) => set.Union fun (H : s ∈ S) => ↑s :=
  sorry

end subring


namespace ring_hom


/-- Restriction of a ring homomorphism to a subring of the domain. -/
def restrict {R : Type u} {S : Type v} [ring R] [ring S] (f : R →+* S) (s : subring R) : ↥s →+* S :=
  comp f (subring.subtype s)

@[simp] theorem restrict_apply {R : Type u} {S : Type v} [ring R] [ring S] {s : subring R}
    (f : R →+* S) (x : ↥s) : coe_fn (restrict f s) x = coe_fn f ↑x :=
  rfl

/-- Restriction of a ring homomorphism to its range interpreted as a subsemiring. -/
def range_restrict {R : Type u} {S : Type v} [ring R] [ring S] (f : R →+* S) : R →+* ↥(range f) :=
  cod_restrict' f (range f) sorry

@[simp] theorem coe_range_restrict {R : Type u} {S : Type v} [ring R] [ring S] (f : R →+* S)
    (x : R) : ↑(coe_fn (range_restrict f) x) = coe_fn f x :=
  rfl

theorem range_top_iff_surjective {R : Type u} {S : Type v} [ring R] [ring S] {f : R →+* S} :
    range f = ⊤ ↔ function.surjective ⇑f :=
  sorry

/-- The range of a surjective ring homomorphism is the whole of the codomain. -/
theorem range_top_of_surjective {R : Type u} {S : Type v} [ring R] [ring S] (f : R →+* S)
    (hf : function.surjective ⇑f) : range f = ⊤ :=
  iff.mpr range_top_iff_surjective hf

/-- The subring of elements `x : R` such that `f x = g x`, i.e.,
  the equalizer of f and g as a subring of R -/
def eq_locus {R : Type u} {S : Type v} [ring R] [ring S] (f : R →+* S) (g : R →+* S) : subring R :=
  subring.mk (set_of fun (x : R) => coe_fn f x = coe_fn g x) sorry sorry sorry sorry sorry

/-- If two ring homomorphisms are equal on a set, then they are equal on its subring closure. -/
theorem eq_on_set_closure {R : Type u} {S : Type v} [ring R] [ring S] {f : R →+* S} {g : R →+* S}
    {s : set R} (h : set.eq_on (⇑f) (⇑g) s) : set.eq_on ⇑f ⇑g ↑(subring.closure s) :=
  (fun (this : subring.closure s ≤ eq_locus f g) => this) (iff.mpr subring.closure_le h)

theorem eq_of_eq_on_set_top {R : Type u} {S : Type v} [ring R] [ring S] {f : R →+* S} {g : R →+* S}
    (h : set.eq_on ⇑f ⇑g ↑⊤) : f = g :=
  ext fun (x : R) => h trivial

theorem eq_of_eq_on_set_dense {R : Type u} {S : Type v} [ring R] [ring S] {s : set R}
    (hs : subring.closure s = ⊤) {f : R →+* S} {g : R →+* S} (h : set.eq_on (⇑f) (⇑g) s) : f = g :=
  eq_of_eq_on_set_top (hs ▸ eq_on_set_closure h)

theorem closure_preimage_le {R : Type u} {S : Type v} [ring R] [ring S] (f : R →+* S) (s : set S) :
    subring.closure (⇑f ⁻¹' s) ≤ subring.comap f (subring.closure s) :=
  iff.mpr subring.closure_le
    fun (x : R) (hx : x ∈ ⇑f ⁻¹' s) =>
      iff.mpr subring.mem_coe (iff.mpr subring.mem_comap (subring.subset_closure hx))

/-- The image under a ring homomorphism of the subring generated by a set equals
the subring generated by the image of the set. -/
theorem map_closure {R : Type u} {S : Type v} [ring R] [ring S] (f : R →+* S) (s : set R) :
    subring.map f (subring.closure s) = subring.closure (⇑f '' s) :=
  sorry

end ring_hom


namespace subring


/-- The ring homomorphism associated to an inclusion of subrings. -/
def inclusion {R : Type u} [ring R] {S : subring R} {T : subring R} (h : S ≤ T) : ↥S →* ↥T :=
  ↑(ring_hom.cod_restrict' (subtype S) T sorry)

@[simp] theorem range_subtype {R : Type u} [ring R] (s : subring R) :
    ring_hom.range (subtype s) = s :=
  ext' (Eq.trans (ring_hom.coe_srange (subtype s)) subtype.range_coe)

@[simp] theorem range_fst {R : Type u} {S : Type v} [ring R] [ring S] :
    ring_hom.srange (ring_hom.fst R S) = ⊤ :=
  ring_hom.srange_top_of_surjective (ring_hom.fst R S) prod.fst_surjective

@[simp] theorem range_snd {R : Type u} {S : Type v} [ring R] [ring S] :
    ring_hom.srange (ring_hom.snd R S) = ⊤ :=
  ring_hom.srange_top_of_surjective (ring_hom.snd R S) prod.snd_surjective

@[simp] theorem prod_bot_sup_bot_prod {R : Type u} {S : Type v} [ring R] [ring S] (s : subring R)
    (t : subring S) : prod s ⊥ ⊔ prod ⊥ t = prod s t :=
  sorry

end subring


namespace ring_equiv


/-- Makes the identity isomorphism from a proof two subrings of a multiplicative
    monoid are equal. -/
def subring_congr {R : Type u} [ring R] {s : subring R} {t : subring R} (h : s = t) : ↥s ≃+* ↥t :=
  mk (equiv.to_fun (equiv.set_congr sorry)) (equiv.inv_fun (equiv.set_congr sorry)) sorry sorry
    sorry sorry

end ring_equiv


namespace subring


protected theorem in_closure.rec_on {R : Type u} [ring R] {s : set R} {C : R → Prop} {x : R}
    (hx : x ∈ closure s) (h1 : C 1) (hneg1 : C (-1))
    (hs : ∀ (z : R), z ∈ s → ∀ (n : R), C n → C (z * n)) (ha : ∀ {x y : R}, C x → C y → C (x + y)) :
    C x :=
  sorry

theorem closure_preimage_le {R : Type u} {S : Type v} [ring R] [ring S] (f : R →+* S) (s : set S) :
    closure (⇑f ⁻¹' s) ≤ comap f (closure s) :=
  iff.mpr closure_le
    fun (x : R) (hx : x ∈ ⇑f ⁻¹' s) => iff.mpr mem_coe (iff.mpr mem_comap (subset_closure hx))

end subring


theorem add_subgroup.int_mul_mem {R : Type u} [ring R] {G : add_subgroup R} (k : ℤ) {g : R}
    (h : g ∈ G) : ↑k * g ∈ G :=
  sorry

end Mathlib