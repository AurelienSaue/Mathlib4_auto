/-
Copyright (c) 2020 Yury Kudryashov All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.ring.prod
import Mathlib.group_theory.submonoid.default
import Mathlib.data.equiv.ring
import PostPort

universes u l u_1 u_2 v w 

namespace Mathlib

/-!
# Bundled subsemirings

We define bundled subsemirings and some standard constructions: `complete_lattice` structure,
`subtype` and `inclusion` ring homomorphisms, subsemiring `map`, `comap` and range (`srange`) of
a `ring_hom` etc.
-/

/-- A subsemiring of a semiring `R` is a subset `s` that is both a multiplicative and an additive
submonoid. -/
structure subsemiring (R : Type u) [semiring R] 
extends add_submonoid R, submonoid R
where

/-- Reinterpret a `subsemiring` as a `submonoid`. -/
/-- Reinterpret a `subsemiring` as an `add_submonoid`. -/
namespace subsemiring


protected instance set.has_coe {R : Type u} [semiring R] : has_coe (subsemiring R) (set R) :=
  has_coe.mk carrier

protected instance has_mem {R : Type u} [semiring R] : has_mem R (subsemiring R) :=
  has_mem.mk fun (m : R) (S : subsemiring R) => m ∈ ↑S

protected instance has_coe_to_sort {R : Type u} [semiring R] : has_coe_to_sort (subsemiring R) :=
  has_coe_to_sort.mk (Type u) fun (S : subsemiring R) => Subtype fun (x : R) => x ∈ S

/-- Construct a `subsemiring R` from a set `s`, a submonoid `sm`, and an additive
submonoid `sa` such that `x ∈ s ↔ x ∈ sm ↔ x ∈ sa`. -/
protected def mk' {R : Type u} [semiring R] (s : set R) (sm : submonoid R) (hm : ↑sm = s) (sa : add_submonoid R) (ha : ↑sa = s) : subsemiring R :=
  mk s sorry sorry sorry sorry

@[simp] theorem coe_mk' {R : Type u} [semiring R] {s : set R} {sm : submonoid R} (hm : ↑sm = s) {sa : add_submonoid R} (ha : ↑sa = s) : ↑(subsemiring.mk' s sm hm sa ha) = s :=
  rfl

@[simp] theorem mem_mk' {R : Type u} [semiring R] {s : set R} {sm : submonoid R} (hm : ↑sm = s) {sa : add_submonoid R} (ha : ↑sa = s) {x : R} : x ∈ subsemiring.mk' s sm hm sa ha ↔ x ∈ s :=
  iff.rfl

@[simp] theorem mk'_to_submonoid {R : Type u} [semiring R] {s : set R} {sm : submonoid R} (hm : ↑sm = s) {sa : add_submonoid R} (ha : ↑sa = s) : to_submonoid (subsemiring.mk' s sm hm sa ha) = sm :=
  submonoid.ext' (Eq.symm hm)

@[simp] theorem mk'_to_add_submonoid {R : Type u} [semiring R] {s : set R} {sm : submonoid R} (hm : ↑sm = s) {sa : add_submonoid R} (ha : ↑sa = s) : to_add_submonoid (subsemiring.mk' s sm hm sa ha) = sa :=
  add_submonoid.ext' (Eq.symm ha)

end subsemiring


protected theorem subsemiring.exists {R : Type u} [semiring R] {s : subsemiring R} {p : ↥s → Prop} : (∃ (x : ↥s), p x) ↔ ∃ (x : R), ∃ (H : x ∈ s), p { val := x, property := H } :=
  set_coe.exists

protected theorem subsemiring.forall {R : Type u} [semiring R] {s : subsemiring R} {p : ↥s → Prop} : (∀ (x : ↥s), p x) ↔ ∀ (x : R) (H : x ∈ s), p { val := x, property := H } :=
  set_coe.forall

namespace subsemiring


/-- Two subsemirings are equal if the underlying subsets are equal. -/
theorem ext' {R : Type u} [semiring R] {s : subsemiring R} {t : subsemiring R} (h : ↑s = ↑t) : s = t := sorry

/-- Two subsemirings are equal if and only if the underlying subsets are equal. -/
protected theorem ext'_iff {R : Type u} [semiring R] {s : subsemiring R} {t : subsemiring R} : s = t ↔ ↑s = ↑t :=
  { mp := fun (h : s = t) => h ▸ rfl, mpr := fun (h : ↑s = ↑t) => ext' h }

/-- Two subsemirings are equal if they have the same elements. -/
theorem ext {R : Type u} [semiring R] {S : subsemiring R} {T : subsemiring R} (h : ∀ (x : R), x ∈ S ↔ x ∈ T) : S = T :=
  ext' (set.ext h)

/-- A subsemiring contains the semiring's 1. -/
theorem one_mem {R : Type u} [semiring R] (s : subsemiring R) : 1 ∈ s :=
  one_mem' s

/-- A subsemiring contains the semiring's 0. -/
theorem zero_mem {R : Type u} [semiring R] (s : subsemiring R) : 0 ∈ s :=
  zero_mem' s

/-- A subsemiring is closed under multiplication. -/
theorem mul_mem {R : Type u} [semiring R] (s : subsemiring R) {x : R} {y : R} : x ∈ s → y ∈ s → x * y ∈ s :=
  mul_mem' s

/-- A subsemiring is closed under addition. -/
theorem add_mem {R : Type u} [semiring R] (s : subsemiring R) {x : R} {y : R} : x ∈ s → y ∈ s → x + y ∈ s :=
  add_mem' s

/-- Product of a list of elements in a `subsemiring` is in the `subsemiring`. -/
theorem list_prod_mem {R : Type u} [semiring R] (s : subsemiring R) {l : List R} : (∀ (x : R), x ∈ l → x ∈ s) → list.prod l ∈ s :=
  submonoid.list_prod_mem (to_submonoid s)

/-- Sum of a list of elements in a `subsemiring` is in the `subsemiring`. -/
theorem list_sum_mem {R : Type u} [semiring R] (s : subsemiring R) {l : List R} : (∀ (x : R), x ∈ l → x ∈ s) → list.sum l ∈ s :=
  add_submonoid.list_sum_mem (to_add_submonoid s)

/-- Product of a multiset of elements in a `subsemiring` of a `comm_semiring`
    is in the `subsemiring`. -/
theorem multiset_prod_mem {R : Type u_1} [comm_semiring R] (s : subsemiring R) (m : multiset R) : (∀ (a : R), a ∈ m → a ∈ s) → multiset.prod m ∈ s :=
  submonoid.multiset_prod_mem (to_submonoid s) m

/-- Sum of a multiset of elements in a `subsemiring` of a `semiring` is
in the `add_subsemiring`. -/
theorem multiset_sum_mem {R : Type u_1} [semiring R] (s : subsemiring R) (m : multiset R) : (∀ (a : R), a ∈ m → a ∈ s) → multiset.sum m ∈ s :=
  add_submonoid.multiset_sum_mem (to_add_submonoid s) m

/-- Product of elements of a subsemiring of a `comm_semiring` indexed by a `finset` is in the
    subsemiring. -/
theorem prod_mem {R : Type u_1} [comm_semiring R] (s : subsemiring R) {ι : Type u_2} {t : finset ι} {f : ι → R} (h : ∀ (c : ι), c ∈ t → f c ∈ s) : (finset.prod t fun (i : ι) => f i) ∈ s :=
  submonoid.prod_mem (to_submonoid s) h

/-- Sum of elements in an `subsemiring` of an `semiring` indexed by a `finset`
is in the `add_subsemiring`. -/
theorem sum_mem {R : Type u_1} [semiring R] (s : subsemiring R) {ι : Type u_2} {t : finset ι} {f : ι → R} (h : ∀ (c : ι), c ∈ t → f c ∈ s) : (finset.sum t fun (i : ι) => f i) ∈ s :=
  add_submonoid.sum_mem (to_add_submonoid s) h

theorem pow_mem {R : Type u} [semiring R] (s : subsemiring R) {x : R} (hx : x ∈ s) (n : ℕ) : x ^ n ∈ s :=
  submonoid.pow_mem (to_submonoid s) hx n

theorem nsmul_mem {R : Type u} [semiring R] (s : subsemiring R) {x : R} (hx : x ∈ s) (n : ℕ) : n •ℕ x ∈ s :=
  add_submonoid.nsmul_mem (to_add_submonoid s) hx n

theorem coe_nat_mem {R : Type u} [semiring R] (s : subsemiring R) (n : ℕ) : ↑n ∈ s := sorry

/-- A subsemiring of a semiring inherits a semiring structure -/
protected instance to_semiring {R : Type u} [semiring R] (s : subsemiring R) : semiring ↥s :=
  semiring.mk add_comm_monoid.add sorry add_comm_monoid.zero sorry sorry sorry monoid.mul sorry monoid.one sorry sorry
    sorry sorry sorry sorry

protected instance nontrivial {R : Type u} [semiring R] (s : subsemiring R) [nontrivial R] : nontrivial ↥s :=
  nontrivial_of_ne 0 1 fun (H : 0 = 1) => zero_ne_one (congr_arg subtype.val H)

protected instance no_zero_divisors {R : Type u} [semiring R] (s : subsemiring R) [no_zero_divisors R] : no_zero_divisors ↥s :=
  no_zero_divisors.mk
    fun (x y : ↥s) (h : x * y = 0) =>
      or.cases_on (eq_zero_or_eq_zero_of_mul_eq_zero (iff.mp subtype.ext_iff h))
        (fun (h : subtype.val x = 0) => Or.inl (subtype.eq h)) fun (h : subtype.val y = 0) => Or.inr (subtype.eq h)

@[simp] theorem coe_mul {R : Type u} [semiring R] (s : subsemiring R) (x : ↥s) (y : ↥s) : ↑(x * y) = ↑x * ↑y :=
  rfl

@[simp] theorem coe_one {R : Type u} [semiring R] (s : subsemiring R) : ↑1 = 1 :=
  rfl

/-- A subsemiring of a `comm_semiring` is a `comm_semiring`. -/
protected instance to_comm_semiring {R : Type u_1} [comm_semiring R] (s : subsemiring R) : comm_semiring ↥s :=
  comm_semiring.mk semiring.add sorry semiring.zero sorry sorry sorry semiring.mul sorry semiring.one sorry sorry sorry
    sorry sorry sorry sorry

/-- The natural ring hom from a subsemiring of semiring `R` to `R`. -/
def subtype {R : Type u} [semiring R] (s : subsemiring R) : ↥s →+* R :=
  ring_hom.mk coe sorry sorry sorry sorry

@[simp] theorem coe_subtype {R : Type u} [semiring R] (s : subsemiring R) : ⇑(subtype s) = coe :=
  rfl

protected instance partial_order {R : Type u} [semiring R] : partial_order (subsemiring R) :=
  partial_order.mk (fun (s t : subsemiring R) => ∀ {x : R}, x ∈ s → x ∈ t) partial_order.lt sorry sorry sorry

theorem le_def {R : Type u} [semiring R] {s : subsemiring R} {t : subsemiring R} : s ≤ t ↔ ∀ {x : R}, x ∈ s → x ∈ t :=
  iff.rfl

@[simp] theorem coe_subset_coe {R : Type u} [semiring R] {s : subsemiring R} {t : subsemiring R} : ↑s ⊆ ↑t ↔ s ≤ t :=
  iff.rfl

@[simp] theorem coe_ssubset_coe {R : Type u} [semiring R] {s : subsemiring R} {t : subsemiring R} : ↑s ⊂ ↑t ↔ s < t :=
  iff.rfl

@[simp] theorem mem_coe {R : Type u} [semiring R] {S : subsemiring R} {m : R} : m ∈ ↑S ↔ m ∈ S :=
  iff.rfl

@[simp] theorem coe_coe {R : Type u} [semiring R] (s : subsemiring R) : ↥↑s = ↥s :=
  rfl

@[simp] theorem mem_to_submonoid {R : Type u} [semiring R] {s : subsemiring R} {x : R} : x ∈ to_submonoid s ↔ x ∈ s :=
  iff.rfl

@[simp] theorem coe_to_submonoid {R : Type u} [semiring R] (s : subsemiring R) : ↑(to_submonoid s) = ↑s :=
  rfl

@[simp] theorem mem_to_add_submonoid {R : Type u} [semiring R] {s : subsemiring R} {x : R} : x ∈ to_add_submonoid s ↔ x ∈ s :=
  iff.rfl

@[simp] theorem coe_to_add_submonoid {R : Type u} [semiring R] (s : subsemiring R) : ↑(to_add_submonoid s) = ↑s :=
  rfl

/-- The subsemiring `R` of the semiring `R`. -/
protected instance has_top {R : Type u} [semiring R] : has_top (subsemiring R) :=
  has_top.mk (mk (submonoid.carrier ⊤) sorry sorry sorry sorry)

@[simp] theorem mem_top {R : Type u} [semiring R] (x : R) : x ∈ ⊤ :=
  set.mem_univ x

@[simp] theorem coe_top {R : Type u} [semiring R] : ↑⊤ = set.univ :=
  rfl

/-- The preimage of a subsemiring along a ring homomorphism is a subsemiring. -/
def comap {R : Type u} {S : Type v} [semiring R] [semiring S] (f : R →+* S) (s : subsemiring S) : subsemiring R :=
  mk (⇑f ⁻¹' ↑s) sorry sorry sorry sorry

@[simp] theorem coe_comap {R : Type u} {S : Type v} [semiring R] [semiring S] (s : subsemiring S) (f : R →+* S) : ↑(comap f s) = ⇑f ⁻¹' ↑s :=
  rfl

@[simp] theorem mem_comap {R : Type u} {S : Type v} [semiring R] [semiring S] {s : subsemiring S} {f : R →+* S} {x : R} : x ∈ comap f s ↔ coe_fn f x ∈ s :=
  iff.rfl

theorem comap_comap {R : Type u} {S : Type v} {T : Type w} [semiring R] [semiring S] [semiring T] (s : subsemiring T) (g : S →+* T) (f : R →+* S) : comap f (comap g s) = comap (ring_hom.comp g f) s :=
  rfl

/-- The image of a subsemiring along a ring homomorphism is a subsemiring. -/
def map {R : Type u} {S : Type v} [semiring R] [semiring S] (f : R →+* S) (s : subsemiring R) : subsemiring S :=
  mk (⇑f '' ↑s) sorry sorry sorry sorry

@[simp] theorem coe_map {R : Type u} {S : Type v} [semiring R] [semiring S] (f : R →+* S) (s : subsemiring R) : ↑(map f s) = ⇑f '' ↑s :=
  rfl

@[simp] theorem mem_map {R : Type u} {S : Type v} [semiring R] [semiring S] {f : R →+* S} {s : subsemiring R} {y : S} : y ∈ map f s ↔ ∃ (x : R), ∃ (H : x ∈ s), coe_fn f x = y :=
  set.mem_image_iff_bex

theorem map_map {R : Type u} {S : Type v} {T : Type w} [semiring R] [semiring S] [semiring T] (s : subsemiring R) (g : S →+* T) (f : R →+* S) : map g (map f s) = map (ring_hom.comp g f) s :=
  ext' (set.image_image (fun (a : S) => coe_fn g a) (fun (a : R) => coe_fn f a) ↑s)

theorem map_le_iff_le_comap {R : Type u} {S : Type v} [semiring R] [semiring S] {f : R →+* S} {s : subsemiring R} {t : subsemiring S} : map f s ≤ t ↔ s ≤ comap f t :=
  set.image_subset_iff

theorem gc_map_comap {R : Type u} {S : Type v} [semiring R] [semiring S] (f : R →+* S) : galois_connection (map f) (comap f) :=
  fun (S_1 : subsemiring R) (T : subsemiring S) => map_le_iff_le_comap

end subsemiring


namespace ring_hom


/-- The range of a ring homomorphism is a subsemiring. -/
def srange {R : Type u} {S : Type v} [semiring R] [semiring S] (f : R →+* S) : subsemiring S :=
  subsemiring.map f ⊤

@[simp] theorem coe_srange {R : Type u} {S : Type v} [semiring R] [semiring S] (f : R →+* S) : ↑(srange f) = set.range ⇑f :=
  set.image_univ

@[simp] theorem mem_srange {R : Type u} {S : Type v} [semiring R] [semiring S] {f : R →+* S} {y : S} : y ∈ srange f ↔ ∃ (x : R), coe_fn f x = y := sorry

theorem map_srange {R : Type u} {S : Type v} {T : Type w} [semiring R] [semiring S] [semiring T] (g : S →+* T) (f : R →+* S) : subsemiring.map g (srange f) = srange (comp g f) :=
  subsemiring.map_map ⊤ g f

end ring_hom


namespace subsemiring


protected instance has_bot {R : Type u} [semiring R] : has_bot (subsemiring R) :=
  has_bot.mk (ring_hom.srange (nat.cast_ring_hom R))

protected instance inhabited {R : Type u} [semiring R] : Inhabited (subsemiring R) :=
  { default := ⊥ }

theorem coe_bot {R : Type u} [semiring R] : ↑⊥ = set.range coe :=
  ring_hom.coe_srange (nat.cast_ring_hom R)

theorem mem_bot {R : Type u} [semiring R] {x : R} : x ∈ ⊥ ↔ ∃ (n : ℕ), ↑n = x :=
  ring_hom.mem_srange

/-- The inf of two subsemirings is their intersection. -/
protected instance has_inf {R : Type u} [semiring R] : has_inf (subsemiring R) :=
  has_inf.mk fun (s t : subsemiring R) => mk (↑s ∩ ↑t) sorry sorry sorry sorry

@[simp] theorem coe_inf {R : Type u} [semiring R] (p : subsemiring R) (p' : subsemiring R) : ↑(p ⊓ p') = ↑p ∩ ↑p' :=
  rfl

@[simp] theorem mem_inf {R : Type u} [semiring R] {p : subsemiring R} {p' : subsemiring R} {x : R} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' :=
  iff.rfl

protected instance has_Inf {R : Type u} [semiring R] : has_Inf (subsemiring R) :=
  has_Inf.mk
    fun (s : set (subsemiring R)) =>
      subsemiring.mk' (set.Inter fun (t : subsemiring R) => set.Inter fun (H : t ∈ s) => ↑t)
        (infi fun (t : subsemiring R) => infi fun (H : t ∈ s) => to_submonoid t) sorry
        (infi fun (t : subsemiring R) => infi fun (H : t ∈ s) => to_add_submonoid t) sorry

@[simp] theorem coe_Inf {R : Type u} [semiring R] (S : set (subsemiring R)) : ↑(Inf S) = set.Inter fun (s : subsemiring R) => set.Inter fun (H : s ∈ S) => ↑s :=
  rfl

theorem mem_Inf {R : Type u} [semiring R] {S : set (subsemiring R)} {x : R} : x ∈ Inf S ↔ ∀ (p : subsemiring R), p ∈ S → x ∈ p :=
  set.mem_bInter_iff

@[simp] theorem Inf_to_submonoid {R : Type u} [semiring R] (s : set (subsemiring R)) : to_submonoid (Inf s) = infi fun (t : subsemiring R) => infi fun (H : t ∈ s) => to_submonoid t :=
  mk'_to_submonoid (has_Inf._proof_1 s) (has_Inf._proof_2 s)

@[simp] theorem Inf_to_add_submonoid {R : Type u} [semiring R] (s : set (subsemiring R)) : to_add_submonoid (Inf s) = infi fun (t : subsemiring R) => infi fun (H : t ∈ s) => to_add_submonoid t :=
  mk'_to_add_submonoid (has_Inf._proof_1 s) (has_Inf._proof_2 s)

/-- Subsemirings of a semiring form a complete lattice. -/
protected instance complete_lattice {R : Type u} [semiring R] : complete_lattice (subsemiring R) :=
  complete_lattice.mk complete_lattice.sup complete_lattice.le complete_lattice.lt sorry sorry sorry sorry sorry sorry
    has_inf.inf sorry sorry sorry ⊤ sorry ⊥ sorry complete_lattice.Sup complete_lattice.Inf sorry sorry sorry sorry

/-- The `subsemiring` generated by a set. -/
def closure {R : Type u} [semiring R] (s : set R) : subsemiring R :=
  Inf (set_of fun (S : subsemiring R) => s ⊆ ↑S)

theorem mem_closure {R : Type u} [semiring R] {x : R} {s : set R} : x ∈ closure s ↔ ∀ (S : subsemiring R), s ⊆ ↑S → x ∈ S :=
  mem_Inf

/-- The subsemiring generated by a set includes the set. -/
@[simp] theorem subset_closure {R : Type u} [semiring R] {s : set R} : s ⊆ ↑(closure s) :=
  fun (x : R) (hx : x ∈ s) => iff.mpr mem_closure fun (S : subsemiring R) (hS : s ⊆ ↑S) => hS hx

/-- A subsemiring `S` includes `closure s` if and only if it includes `s`. -/
@[simp] theorem closure_le {R : Type u} [semiring R] {s : set R} {t : subsemiring R} : closure s ≤ t ↔ s ⊆ ↑t :=
  { mp := set.subset.trans subset_closure, mpr := fun (h : s ⊆ ↑t) => Inf_le h }

/-- Subsemiring closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
theorem closure_mono {R : Type u} [semiring R] {s : set R} {t : set R} (h : s ⊆ t) : closure s ≤ closure t :=
  iff.mpr closure_le (set.subset.trans h subset_closure)

theorem closure_eq_of_le {R : Type u} [semiring R] {s : set R} {t : subsemiring R} (h₁ : s ⊆ ↑t) (h₂ : t ≤ closure s) : closure s = t :=
  le_antisymm (iff.mpr closure_le h₁) h₂

/-- An induction principle for closure membership. If `p` holds for `0`, `1`, and all elements
of `s`, and is preserved under addition and multiplication, then `p` holds for all elements
of the closure of `s`. -/
theorem closure_induction {R : Type u} [semiring R] {s : set R} {p : R → Prop} {x : R} (h : x ∈ closure s) (Hs : ∀ (x : R), x ∈ s → p x) (H0 : p 0) (H1 : p 1) (Hadd : ∀ (x y : R), p x → p y → p (x + y)) (Hmul : ∀ (x y : R), p x → p y → p (x * y)) : p x :=
  iff.mpr closure_le Hs x h

theorem mem_closure_iff {R : Type u} [semiring R] {s : set R} {x : R} : x ∈ closure s ↔ x ∈ add_submonoid.closure ↑(submonoid.closure s) := sorry

theorem mem_closure_iff_exists_list {R : Type u} [semiring R] {s : set R} {x : R} : x ∈ closure s ↔
  ∃ (L : List (List R)), (∀ (t : List R), t ∈ L → ∀ (y : R), y ∈ t → y ∈ s) ∧ list.sum (list.map list.prod L) = x := sorry

/-- `closure` forms a Galois insertion with the coercion to set. -/
protected def gi (R : Type u) [semiring R] : galois_insertion closure coe :=
  galois_insertion.mk (fun (s : set R) (_x : ↑(closure s) ≤ s) => closure s) sorry sorry sorry

/-- Closure of a subsemiring `S` equals `S`. -/
theorem closure_eq {R : Type u} [semiring R] (s : subsemiring R) : closure ↑s = s :=
  galois_insertion.l_u_eq (subsemiring.gi R) s

@[simp] theorem closure_empty {R : Type u} [semiring R] : closure ∅ = ⊥ :=
  galois_connection.l_bot (galois_insertion.gc (subsemiring.gi R))

@[simp] theorem closure_univ {R : Type u} [semiring R] : closure set.univ = ⊤ :=
  coe_top ▸ closure_eq ⊤

theorem closure_union {R : Type u} [semiring R] (s : set R) (t : set R) : closure (s ∪ t) = closure s ⊔ closure t :=
  galois_connection.l_sup (galois_insertion.gc (subsemiring.gi R))

theorem closure_Union {R : Type u} [semiring R] {ι : Sort u_1} (s : ι → set R) : closure (set.Union fun (i : ι) => s i) = supr fun (i : ι) => closure (s i) :=
  galois_connection.l_supr (galois_insertion.gc (subsemiring.gi R))

theorem closure_sUnion {R : Type u} [semiring R] (s : set (set R)) : closure (⋃₀s) = supr fun (t : set R) => supr fun (H : t ∈ s) => closure t :=
  galois_connection.l_Sup (galois_insertion.gc (subsemiring.gi R))

theorem map_sup {R : Type u} {S : Type v} [semiring R] [semiring S] (s : subsemiring R) (t : subsemiring R) (f : R →+* S) : map f (s ⊔ t) = map f s ⊔ map f t :=
  galois_connection.l_sup (gc_map_comap f)

theorem map_supr {R : Type u} {S : Type v} [semiring R] [semiring S] {ι : Sort u_1} (f : R →+* S) (s : ι → subsemiring R) : map f (supr s) = supr fun (i : ι) => map f (s i) :=
  galois_connection.l_supr (gc_map_comap f)

theorem comap_inf {R : Type u} {S : Type v} [semiring R] [semiring S] (s : subsemiring S) (t : subsemiring S) (f : R →+* S) : comap f (s ⊓ t) = comap f s ⊓ comap f t :=
  galois_connection.u_inf (gc_map_comap f)

theorem comap_infi {R : Type u} {S : Type v} [semiring R] [semiring S] {ι : Sort u_1} (f : R →+* S) (s : ι → subsemiring S) : comap f (infi s) = infi fun (i : ι) => comap f (s i) :=
  galois_connection.u_infi (gc_map_comap f)

@[simp] theorem map_bot {R : Type u} {S : Type v} [semiring R] [semiring S] (f : R →+* S) : map f ⊥ = ⊥ :=
  galois_connection.l_bot (gc_map_comap f)

@[simp] theorem comap_top {R : Type u} {S : Type v} [semiring R] [semiring S] (f : R →+* S) : comap f ⊤ = ⊤ :=
  galois_connection.u_top (gc_map_comap f)

/-- Given `subsemiring`s `s`, `t` of semirings `R`, `S` respectively, `s.prod t` is `s × t`
as a subsemiring of `R × S`. -/
def prod {R : Type u} {S : Type v} [semiring R] [semiring S] (s : subsemiring R) (t : subsemiring S) : subsemiring (R × S) :=
  mk (set.prod ↑s ↑t) sorry sorry sorry sorry

theorem coe_prod {R : Type u} {S : Type v} [semiring R] [semiring S] (s : subsemiring R) (t : subsemiring S) : ↑(prod s t) = set.prod ↑s ↑t :=
  rfl

theorem mem_prod {R : Type u} {S : Type v} [semiring R] [semiring S] {s : subsemiring R} {t : subsemiring S} {p : R × S} : p ∈ prod s t ↔ prod.fst p ∈ s ∧ prod.snd p ∈ t :=
  iff.rfl

theorem prod_mono {R : Type u} {S : Type v} [semiring R] [semiring S] {s₁ : subsemiring R} {s₂ : subsemiring R} (hs : s₁ ≤ s₂) {t₁ : subsemiring S} {t₂ : subsemiring S} (ht : t₁ ≤ t₂) : prod s₁ t₁ ≤ prod s₂ t₂ :=
  set.prod_mono hs ht

theorem prod_mono_right {R : Type u} {S : Type v} [semiring R] [semiring S] (s : subsemiring R) : monotone fun (t : subsemiring S) => prod s t :=
  prod_mono (le_refl s)

theorem prod_mono_left {R : Type u} {S : Type v} [semiring R] [semiring S] (t : subsemiring S) : monotone fun (s : subsemiring R) => prod s t :=
  fun (s₁ s₂ : subsemiring R) (hs : s₁ ≤ s₂) => prod_mono hs (le_refl t)

theorem prod_top {R : Type u} {S : Type v} [semiring R] [semiring S] (s : subsemiring R) : prod s ⊤ = comap (ring_hom.fst R S) s := sorry

theorem top_prod {R : Type u} {S : Type v} [semiring R] [semiring S] (s : subsemiring S) : prod ⊤ s = comap (ring_hom.snd R S) s := sorry

@[simp] theorem top_prod_top {R : Type u} {S : Type v} [semiring R] [semiring S] : prod ⊤ ⊤ = ⊤ :=
  Eq.trans (top_prod ⊤) (comap_top (ring_hom.snd R S))

/-- Product of subsemirings is isomorphic to their product as monoids. -/
def prod_equiv {R : Type u} {S : Type v} [semiring R] [semiring S] (s : subsemiring R) (t : subsemiring S) : ↥(prod s t) ≃+* ↥s × ↥t :=
  ring_equiv.mk (equiv.to_fun (equiv.set.prod ↑s ↑t)) (equiv.inv_fun (equiv.set.prod ↑s ↑t)) sorry sorry sorry sorry

theorem mem_supr_of_directed {R : Type u} [semiring R] {ι : Sort u_1} [hι : Nonempty ι] {S : ι → subsemiring R} (hS : directed LessEq S) {x : R} : (x ∈ supr fun (i : ι) => S i) ↔ ∃ (i : ι), x ∈ S i := sorry

theorem coe_supr_of_directed {R : Type u} [semiring R] {ι : Sort u_1} [hι : Nonempty ι] {S : ι → subsemiring R} (hS : directed LessEq S) : ↑(supr fun (i : ι) => S i) = set.Union fun (i : ι) => ↑(S i) := sorry

theorem mem_Sup_of_directed_on {R : Type u} [semiring R] {S : set (subsemiring R)} (Sne : set.nonempty S) (hS : directed_on LessEq S) {x : R} : x ∈ Sup S ↔ ∃ (s : subsemiring R), ∃ (H : s ∈ S), x ∈ s := sorry

theorem coe_Sup_of_directed_on {R : Type u} [semiring R] {S : set (subsemiring R)} (Sne : set.nonempty S) (hS : directed_on LessEq S) : ↑(Sup S) = set.Union fun (s : subsemiring R) => set.Union fun (H : s ∈ S) => ↑s := sorry

end subsemiring


namespace ring_hom


/-- Restriction of a ring homomorphism to a subsemiring of the domain. -/
def srestrict {R : Type u} {S : Type v} [semiring R] [semiring S] (f : R →+* S) (s : subsemiring R) : ↥s →+* S :=
  comp f (subsemiring.subtype s)

@[simp] theorem srestrict_apply {R : Type u} {S : Type v} [semiring R] [semiring S] {s : subsemiring R} (f : R →+* S) (x : ↥s) : coe_fn (srestrict f s) x = coe_fn f ↑x :=
  rfl

/-- Restriction of a ring homomorphism to a subsemiring of the codomain. -/
def cod_srestrict {R : Type u} {S : Type v} [semiring R] [semiring S] (f : R →+* S) (s : subsemiring S) (h : ∀ (x : R), coe_fn f x ∈ s) : R →+* ↥s :=
  mk (fun (n : R) => { val := coe_fn f n, property := h n }) sorry sorry sorry sorry

/-- Restriction of a ring homomorphism to its range iterpreted as a subsemiring. -/
def srange_restrict {R : Type u} {S : Type v} [semiring R] [semiring S] (f : R →+* S) : R →+* ↥(srange f) :=
  cod_srestrict f (srange f) sorry

@[simp] theorem coe_srange_restrict {R : Type u} {S : Type v} [semiring R] [semiring S] (f : R →+* S) (x : R) : ↑(coe_fn (srange_restrict f) x) = coe_fn f x :=
  rfl

theorem srange_top_iff_surjective {R : Type u} {S : Type v} [semiring R] [semiring S] {f : R →+* S} : srange f = ⊤ ↔ function.surjective ⇑f := sorry

/-- The range of a surjective ring homomorphism is the whole of the codomain. -/
theorem srange_top_of_surjective {R : Type u} {S : Type v} [semiring R] [semiring S] (f : R →+* S) (hf : function.surjective ⇑f) : srange f = ⊤ :=
  iff.mpr srange_top_iff_surjective hf

/-- The subsemiring of elements `x : R` such that `f x = g x` -/
def eq_slocus {R : Type u} {S : Type v} [semiring R] [semiring S] (f : R →+* S) (g : R →+* S) : subsemiring R :=
  subsemiring.mk (set_of fun (x : R) => coe_fn f x = coe_fn g x) sorry sorry sorry sorry

/-- If two ring homomorphisms are equal on a set, then they are equal on its subsemiring closure. -/
theorem eq_on_sclosure {R : Type u} {S : Type v} [semiring R] [semiring S] {f : R →+* S} {g : R →+* S} {s : set R} (h : set.eq_on (⇑f) (⇑g) s) : set.eq_on ⇑f ⇑g ↑(subsemiring.closure s) :=
  (fun (this : subsemiring.closure s ≤ eq_slocus f g) => this) (iff.mpr subsemiring.closure_le h)

theorem eq_of_eq_on_stop {R : Type u} {S : Type v} [semiring R] [semiring S] {f : R →+* S} {g : R →+* S} (h : set.eq_on ⇑f ⇑g ↑⊤) : f = g :=
  ext fun (x : R) => h trivial

theorem eq_of_eq_on_sdense {R : Type u} {S : Type v} [semiring R] [semiring S] {s : set R} (hs : subsemiring.closure s = ⊤) {f : R →+* S} {g : R →+* S} (h : set.eq_on (⇑f) (⇑g) s) : f = g :=
  eq_of_eq_on_stop (hs ▸ eq_on_sclosure h)

theorem sclosure_preimage_le {R : Type u} {S : Type v} [semiring R] [semiring S] (f : R →+* S) (s : set S) : subsemiring.closure (⇑f ⁻¹' s) ≤ subsemiring.comap f (subsemiring.closure s) :=
  iff.mpr subsemiring.closure_le
    fun (x : R) (hx : x ∈ ⇑f ⁻¹' s) =>
      iff.mpr subsemiring.mem_coe (iff.mpr subsemiring.mem_comap (subsemiring.subset_closure hx))

/-- The image under a ring homomorphism of the subsemiring generated by a set equals
the subsemiring generated by the image of the set. -/
theorem map_sclosure {R : Type u} {S : Type v} [semiring R] [semiring S] (f : R →+* S) (s : set R) : subsemiring.map f (subsemiring.closure s) = subsemiring.closure (⇑f '' s) := sorry

end ring_hom


namespace subsemiring


/-- The ring homomorphism associated to an inclusion of subsemirings. -/
def inclusion {R : Type u} [semiring R] {S : subsemiring R} {T : subsemiring R} (h : S ≤ T) : ↥S →* ↥T :=
  ↑(ring_hom.cod_srestrict (subtype S) T sorry)

@[simp] theorem srange_subtype {R : Type u} [semiring R] (s : subsemiring R) : ring_hom.srange (subtype s) = s :=
  ext' (Eq.trans (ring_hom.coe_srange (subtype s)) subtype.range_coe)

@[simp] theorem range_fst {R : Type u} {S : Type v} [semiring R] [semiring S] : ring_hom.srange (ring_hom.fst R S) = ⊤ :=
  ring_hom.srange_top_of_surjective (ring_hom.fst R S) prod.fst_surjective

@[simp] theorem range_snd {R : Type u} {S : Type v} [semiring R] [semiring S] : ring_hom.srange (ring_hom.snd R S) = ⊤ :=
  ring_hom.srange_top_of_surjective (ring_hom.snd R S) prod.snd_surjective

@[simp] theorem prod_bot_sup_bot_prod {R : Type u} {S : Type v} [semiring R] [semiring S] (s : subsemiring R) (t : subsemiring S) : prod s ⊥ ⊔ prod ⊥ t = prod s t := sorry

end subsemiring


namespace ring_equiv


/-- Makes the identity isomorphism from a proof two subsemirings of a multiplicative
    monoid are equal. -/
def subsemiring_congr {R : Type u} [semiring R] {s : subsemiring R} {t : subsemiring R} (h : s = t) : ↥s ≃+* ↥t :=
  mk (equiv.to_fun (equiv.set_congr sorry)) (equiv.inv_fun (equiv.set_congr sorry)) sorry sorry sorry sorry

