/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.algebra.operations
import Mathlib.PostPort

universes u v l w u_1 u_2 u_3 

namespace Mathlib

/-!
# Subalgebras over Commutative Semiring

In this file we define `subalgebra`s and the usual operations on them (`map`, `comap`).

More lemmas about `adjoin` can be found in `ring_theory.adjoin`.
-/

/-- A subalgebra is a sub(semi)ring that includes the range of `algebra_map`. -/
structure subalgebra (R : Type u) (A : Type v) [comm_semiring R] [semiring A] [algebra R A]
    extends subsemiring A where
  algebra_map_mem' : ∀ (r : R), coe_fn (algebra_map R A) r ∈ carrier

/-- Reinterpret a `subalgebra` as a `subsemiring`. -/
namespace subalgebra


protected instance subsemiring.has_coe {R : Type u} {A : Type v} [comm_semiring R] [semiring A]
    [algebra R A] : has_coe (subalgebra R A) (subsemiring A) :=
  has_coe.mk
    fun (S : subalgebra R A) =>
      subsemiring.mk (carrier S) (one_mem' S) (mul_mem' S) (zero_mem' S) (add_mem' S)

protected instance has_mem {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A] :
    has_mem A (subalgebra R A) :=
  has_mem.mk fun (x : A) (S : subalgebra R A) => x ∈ ↑S

theorem mem_coe {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A] {x : A}
    {s : subalgebra R A} : x ∈ ↑s ↔ x ∈ s :=
  iff.rfl

theorem ext {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    {S : subalgebra R A} {T : subalgebra R A} (h : ∀ (x : A), x ∈ S ↔ x ∈ T) : S = T :=
  sorry

theorem ext_iff {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    {S : subalgebra R A} {T : subalgebra R A} : S = T ↔ ∀ (x : A), x ∈ S ↔ x ∈ T :=
  { mp :=
      fun (h : S = T) (x : A) =>
        eq.mpr (id (Eq._oldrec (Eq.refl (x ∈ S ↔ x ∈ T)) h)) (iff.refl (x ∈ T)),
    mpr := ext }

theorem algebra_map_mem {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    (S : subalgebra R A) (r : R) : coe_fn (algebra_map R A) r ∈ S :=
  algebra_map_mem' S r

theorem srange_le {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    (S : subalgebra R A) : ring_hom.srange (algebra_map R A) ≤ ↑S :=
  sorry

theorem range_subset {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    (S : subalgebra R A) : set.range ⇑(algebra_map R A) ⊆ ↑S :=
  sorry

theorem range_le {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    (S : subalgebra R A) : set.range ⇑(algebra_map R A) ≤ ↑S :=
  range_subset S

theorem one_mem {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    (S : subalgebra R A) : 1 ∈ S :=
  subsemiring.one_mem ↑S

theorem mul_mem {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    (S : subalgebra R A) {x : A} {y : A} (hx : x ∈ S) (hy : y ∈ S) : x * y ∈ S :=
  subsemiring.mul_mem (↑S) hx hy

theorem smul_mem {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    (S : subalgebra R A) {x : A} (hx : x ∈ S) (r : R) : r • x ∈ S :=
  Eq.symm (algebra.smul_def r x) ▸ mul_mem S (algebra_map_mem S r) hx

theorem pow_mem {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    (S : subalgebra R A) {x : A} (hx : x ∈ S) (n : ℕ) : x ^ n ∈ S :=
  subsemiring.pow_mem (↑S) hx n

theorem zero_mem {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    (S : subalgebra R A) : 0 ∈ S :=
  subsemiring.zero_mem ↑S

theorem add_mem {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    (S : subalgebra R A) {x : A} {y : A} (hx : x ∈ S) (hy : y ∈ S) : x + y ∈ S :=
  subsemiring.add_mem (↑S) hx hy

theorem neg_mem {R : Type u} {A : Type v} [comm_ring R] [ring A] [algebra R A] (S : subalgebra R A)
    {x : A} (hx : x ∈ S) : -x ∈ S :=
  neg_one_smul R x ▸ smul_mem S hx (-1)

theorem sub_mem {R : Type u} {A : Type v} [comm_ring R] [ring A] [algebra R A] (S : subalgebra R A)
    {x : A} {y : A} (hx : x ∈ S) (hy : y ∈ S) : x - y ∈ S :=
  sorry

theorem nsmul_mem {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    (S : subalgebra R A) {x : A} (hx : x ∈ S) (n : ℕ) : n •ℕ x ∈ S :=
  subsemiring.nsmul_mem (↑S) hx n

theorem gsmul_mem {R : Type u} {A : Type v} [comm_ring R] [ring A] [algebra R A]
    (S : subalgebra R A) {x : A} (hx : x ∈ S) (n : ℤ) : n •ℤ x ∈ S :=
  int.cases_on n (fun (i : ℕ) => nsmul_mem S hx i)
    fun (i : ℕ) => neg_mem S (nsmul_mem S hx (Nat.succ i))

theorem coe_nat_mem {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    (S : subalgebra R A) (n : ℕ) : ↑n ∈ S :=
  subsemiring.coe_nat_mem (↑S) n

theorem coe_int_mem {R : Type u} {A : Type v} [comm_ring R] [ring A] [algebra R A]
    (S : subalgebra R A) (n : ℤ) : ↑n ∈ S :=
  int.cases_on n (fun (i : ℕ) => coe_nat_mem S i) fun (i : ℕ) => neg_mem S (coe_nat_mem S (i + 1))

theorem list_prod_mem {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    (S : subalgebra R A) {L : List A} (h : ∀ (x : A), x ∈ L → x ∈ S) : list.prod L ∈ S :=
  subsemiring.list_prod_mem (↑S) h

theorem list_sum_mem {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    (S : subalgebra R A) {L : List A} (h : ∀ (x : A), x ∈ L → x ∈ S) : list.sum L ∈ S :=
  subsemiring.list_sum_mem (↑S) h

theorem multiset_prod_mem {R : Type u} {A : Type v} [comm_semiring R] [comm_semiring A]
    [algebra R A] (S : subalgebra R A) {m : multiset A} (h : ∀ (x : A), x ∈ m → x ∈ S) :
    multiset.prod m ∈ S :=
  subsemiring.multiset_prod_mem (↑S) m h

theorem multiset_sum_mem {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    (S : subalgebra R A) {m : multiset A} (h : ∀ (x : A), x ∈ m → x ∈ S) : multiset.sum m ∈ S :=
  subsemiring.multiset_sum_mem (↑S) m h

theorem prod_mem {R : Type u} {A : Type v} [comm_semiring R] [comm_semiring A] [algebra R A]
    (S : subalgebra R A) {ι : Type w} {t : finset ι} {f : ι → A} (h : ∀ (x : ι), x ∈ t → f x ∈ S) :
    (finset.prod t fun (x : ι) => f x) ∈ S :=
  subsemiring.prod_mem (↑S) h

theorem sum_mem {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    (S : subalgebra R A) {ι : Type w} {t : finset ι} {f : ι → A} (h : ∀ (x : ι), x ∈ t → f x ∈ S) :
    (finset.sum t fun (x : ι) => f x) ∈ S :=
  subsemiring.sum_mem (↑S) h

protected instance is_add_submonoid {R : Type u} {A : Type v} [comm_semiring R] [semiring A]
    [algebra R A] (S : subalgebra R A) : is_add_submonoid ↑S :=
  is_add_submonoid.mk (zero_mem S) fun (_x _x_1 : A) => add_mem S

protected instance is_submonoid {R : Type u} {A : Type v} [comm_semiring R] [semiring A]
    [algebra R A] (S : subalgebra R A) : is_submonoid ↑S :=
  is_submonoid.mk (one_mem S) fun (_x _x_1 : A) => mul_mem S

/-- A subalgebra over a ring is also a `subring`. -/
def to_subring {R : Type u} {A : Type v} [comm_ring R] [ring A] [algebra R A] (S : subalgebra R A) :
    subring A :=
  subring.mk (subsemiring.carrier (to_subsemiring S)) sorry sorry sorry sorry sorry

protected instance is_subring {R : Type u} {A : Type v} [comm_ring R] [ring A] [algebra R A]
    (S : subalgebra R A) : is_subring ↑S :=
  is_subring.mk

protected instance inhabited {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    (S : subalgebra R A) : Inhabited ↥S :=
  { default := 0 }

protected instance semiring (R : Type u) (A : Type v) [comm_semiring R] [semiring A] [algebra R A]
    (S : subalgebra R A) : semiring ↥S :=
  subsemiring.to_semiring ↑S

protected instance comm_semiring (R : Type u) (A : Type v) [comm_semiring R] [comm_semiring A]
    [algebra R A] (S : subalgebra R A) : comm_semiring ↥S :=
  subsemiring.to_comm_semiring ↑S

protected instance ring (R : Type u) (A : Type v) [comm_ring R] [ring A] [algebra R A]
    (S : subalgebra R A) : ring ↥S :=
  subtype.ring

protected instance comm_ring (R : Type u) (A : Type v) [comm_ring R] [comm_ring A] [algebra R A]
    (S : subalgebra R A) : comm_ring ↥S :=
  subtype.comm_ring

protected instance algebra {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    (S : subalgebra R A) : algebra R ↥S :=
  algebra.mk
    (ring_hom.mk (ring_hom.to_fun (ring_hom.cod_srestrict (algebra_map R A) ↑S sorry)) sorry sorry
      sorry sorry)
    sorry sorry

protected instance to_algebra {R : Type u_1} {A : Type u_2} {B : Type u_3} [comm_semiring R]
    [comm_semiring A] [semiring B] [algebra R A] [algebra A B] (A₀ : subalgebra R A) :
    algebra (↥A₀) B :=
  algebra.of_subsemiring ↑A₀

protected instance nontrivial {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    (S : subalgebra R A) [nontrivial A] : nontrivial ↥S :=
  subsemiring.nontrivial ↑S

-- todo: standardize on the names these morphisms

-- compare with submodule.subtype

/-- Embedding of a subalgebra into the algebra. -/
def val {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    (S : subalgebra R A) : alg_hom R (↥S) A :=
  alg_hom.mk coe sorry sorry sorry sorry sorry

@[simp] theorem coe_val {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    (S : subalgebra R A) : ⇑(val S) = coe :=
  rfl

theorem val_apply {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    (S : subalgebra R A) (x : ↥S) : coe_fn (val S) x = ↑x :=
  rfl

/-- Convert a `subalgebra` to `submodule` -/
def to_submodule {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    (S : subalgebra R A) : submodule R A :=
  submodule.mk ↑S sorry sorry sorry

protected instance coe_to_submodule {R : Type u} {A : Type v} [comm_semiring R] [semiring A]
    [algebra R A] : has_coe (subalgebra R A) (submodule R A) :=
  has_coe.mk to_submodule

protected instance to_submodule.is_subring {R : Type u} {A : Type v} [comm_ring R] [ring A]
    [algebra R A] (S : subalgebra R A) : is_subring ↑↑S :=
  subalgebra.is_subring S

@[simp] theorem mem_to_submodule {R : Type u} {A : Type v} [comm_semiring R] [semiring A]
    [algebra R A] (S : subalgebra R A) {x : A} : x ∈ ↑S ↔ x ∈ S :=
  iff.rfl

theorem to_submodule_injective {R : Type u} {A : Type v} [comm_semiring R] [semiring A]
    [algebra R A] {S : subalgebra R A} {U : subalgebra R A} (h : ↑S = ↑U) : S = U :=
  sorry

theorem to_submodule_inj {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    {S : subalgebra R A} {U : subalgebra R A} : ↑S = ↑U ↔ S = U :=
  { mp := to_submodule_injective, mpr := congr_arg fun {S : subalgebra R A} => ↑S }

/-- As submodules, subalgebras are idempotent. -/
@[simp] theorem mul_self {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    (S : subalgebra R A) : ↑S * ↑S = ↑S :=
  sorry

/-- Linear equivalence between `S : submodule R A` and `S`. Though these types are equal,
we define it as a `linear_equiv` to avoid type equalities. -/
def to_submodule_equiv {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    (S : subalgebra R A) : linear_equiv R ↥↑S ↥S :=
  linear_equiv.of_eq (↑S) (has_coe_t_aux.coe S) sorry

protected instance partial_order {R : Type u} {A : Type v} [comm_semiring R] [semiring A]
    [algebra R A] : partial_order (subalgebra R A) :=
  partial_order.mk (fun (S T : subalgebra R A) => ↑S ⊆ ↑T)
    (preorder.lt._default fun (S T : subalgebra R A) => ↑S ⊆ ↑T) sorry sorry sorry

/-- Reinterpret an `S`-subalgebra as an `R`-subalgebra in `comap R S A`. -/
def comap {R : Type u} {S : Type v} {A : Type w} [comm_semiring R] [comm_semiring S] [semiring A]
    [algebra R S] [algebra S A] (iSB : subalgebra S A) : subalgebra R (algebra.comap R S A) :=
  mk (carrier iSB) (one_mem' iSB) (mul_mem' iSB) (zero_mem' iSB) (add_mem' iSB) sorry

/-- If `S` is an `R`-subalgebra of `A` and `T` is an `S`-subalgebra of `A`,
then `T` is an `R`-subalgebra of `A`. -/
def under {R : Type u} {A : Type v} [comm_semiring R] [comm_semiring A] {i : algebra R A}
    (S : subalgebra R A) (T : subalgebra (↥S) A) : subalgebra R A :=
  mk (carrier T) sorry sorry sorry sorry sorry

/-- Transport a subalgebra via an algebra homomorphism. -/
def map {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [algebra R A]
    [semiring B] [algebra R B] (S : subalgebra R A) (f : alg_hom R A B) : subalgebra R B :=
  mk (subsemiring.carrier (subsemiring.map ↑f ↑S)) sorry sorry sorry sorry sorry

/-- Preimage of a subalgebra under an algebra homomorphism. -/
def comap' {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [algebra R A]
    [semiring B] [algebra R B] (S : subalgebra R B) (f : alg_hom R A B) : subalgebra R A :=
  mk (subsemiring.carrier (subsemiring.comap ↑f ↑S)) sorry sorry sorry sorry sorry

theorem map_mono {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [algebra R A]
    [semiring B] [algebra R B] {S₁ : subalgebra R A} {S₂ : subalgebra R A} {f : alg_hom R A B} :
    S₁ ≤ S₂ → map S₁ f ≤ map S₂ f :=
  set.image_subset ⇑f

theorem map_le {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [algebra R A]
    [semiring B] [algebra R B] {S : subalgebra R A} {f : alg_hom R A B} {U : subalgebra R B} :
    map S f ≤ U ↔ S ≤ comap' U f :=
  set.image_subset_iff

theorem map_injective {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A]
    [algebra R A] [semiring B] [algebra R B] {S₁ : subalgebra R A} {S₂ : subalgebra R A}
    (f : alg_hom R A B) (hf : function.injective ⇑f) (ih : map S₁ f = map S₂ f) : S₁ = S₂ :=
  ext
    (iff.mp set.ext_iff
      (iff.mpr set.image_injective hf (fun (x : A) => x ∈ ↑S₁) (fun (x : A) => x ∈ ↑S₂)
        (set.ext (iff.mp ext_iff ih))))

theorem mem_map {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [algebra R A]
    [semiring B] [algebra R B] {S : subalgebra R A} {f : alg_hom R A B} {y : B} :
    y ∈ map S f ↔ ∃ (x : A), ∃ (H : x ∈ S), coe_fn f x = y :=
  subsemiring.mem_map

protected instance no_zero_divisors {R : Type u_1} {A : Type u_2} [comm_ring R] [semiring A]
    [no_zero_divisors A] [algebra R A] (S : subalgebra R A) : no_zero_divisors ↥S :=
  subsemiring.no_zero_divisors (to_subsemiring S)

protected instance integral_domain {R : Type u_1} {A : Type u_2} [comm_ring R] [integral_domain A]
    [algebra R A] (S : subalgebra R A) : integral_domain ↥S :=
  subring.domain ↑S

end subalgebra


namespace alg_hom


/-- Range of an `alg_hom` as a subalgebra. -/
protected def range {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A]
    [semiring B] [algebra R A] [algebra R B] (φ : alg_hom R A B) : subalgebra R B :=
  subalgebra.mk (subsemiring.carrier (ring_hom.srange (to_ring_hom φ))) sorry sorry sorry sorry
    sorry

@[simp] theorem mem_range {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A]
    [semiring B] [algebra R A] [algebra R B] (φ : alg_hom R A B) {y : B} :
    y ∈ alg_hom.range φ ↔ ∃ (x : A), coe_fn φ x = y :=
  ring_hom.mem_srange

@[simp] theorem coe_range {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A]
    [semiring B] [algebra R A] [algebra R B] (φ : alg_hom R A B) :
    ↑(alg_hom.range φ) = set.range ⇑φ :=
  sorry

/-- Restrict the codomain of an algebra homomorphism. -/
def cod_restrict {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [semiring B]
    [algebra R A] [algebra R B] (f : alg_hom R A B) (S : subalgebra R B)
    (hf : ∀ (x : A), coe_fn f x ∈ S) : alg_hom R A ↥S :=
  mk (ring_hom.to_fun (ring_hom.cod_srestrict (↑f) (↑S) hf)) sorry sorry sorry sorry sorry

theorem injective_cod_restrict {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A]
    [semiring B] [algebra R A] [algebra R B] (f : alg_hom R A B) (S : subalgebra R B)
    (hf : ∀ (x : A), coe_fn f x ∈ S) :
    function.injective ⇑(cod_restrict f S hf) ↔ function.injective ⇑f :=
  sorry

/-- Restrict an injective algebra homomorphism to an algebra isomorphism -/
def alg_equiv.of_injective {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A]
    [semiring B] [algebra R A] [algebra R B] (f : alg_hom R A B) (hf : function.injective ⇑f) :
    alg_equiv R A ↥(alg_hom.range f) :=
  alg_equiv.of_bijective (cod_restrict f (alg_hom.range f) sorry) sorry

@[simp] theorem alg_equiv.of_injective_apply {R : Type u} {A : Type v} {B : Type w}
    [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] (f : alg_hom R A B)
    (hf : function.injective ⇑f) (x : A) : ↑(coe_fn (alg_equiv.of_injective f hf) x) = coe_fn f x :=
  rfl

/-- Restrict an algebra homomorphism between fields to an algebra isomorphism -/
def alg_equiv.of_injective_field {R : Type u} [comm_semiring R] {E : Type u_1} {F : Type u_2}
    [division_ring E] [semiring F] [nontrivial F] [algebra R E] [algebra R F] (f : alg_hom R E F) :
    alg_equiv R E ↥(alg_hom.range f) :=
  alg_equiv.of_injective f sorry

/-- The equalizer of two R-algebra homomorphisms -/
def equalizer {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [semiring B]
    [algebra R A] [algebra R B] (ϕ : alg_hom R A B) (ψ : alg_hom R A B) : subalgebra R A :=
  subalgebra.mk (set_of fun (a : A) => coe_fn ϕ a = coe_fn ψ a) sorry sorry sorry sorry sorry

@[simp] theorem mem_equalizer {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A]
    [semiring B] [algebra R A] [algebra R B] (ϕ : alg_hom R A B) (ψ : alg_hom R A B) (x : A) :
    x ∈ equalizer ϕ ψ ↔ coe_fn ϕ x = coe_fn ψ x :=
  iff.rfl

end alg_hom


namespace algebra


/-- The minimal subalgebra that includes `s`. -/
def adjoin (R : Type u) {A : Type v} [comm_semiring R] [semiring A] [algebra R A] (s : set A) :
    subalgebra R A :=
  subalgebra.mk (subsemiring.carrier (subsemiring.closure (set.range ⇑(algebra_map R A) ∪ s))) sorry
    sorry sorry sorry sorry

protected theorem gc {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A] :
    galois_connection (adjoin R) coe :=
  sorry

/-- Galois insertion between `adjoin` and `coe`. -/
protected def gi {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A] :
    galois_insertion (adjoin R) coe :=
  galois_insertion.mk (fun (s : set A) (hs : ↑(adjoin R s) ≤ s) => adjoin R s) algebra.gc sorry
    sorry

protected instance subalgebra.complete_lattice {R : Type u} {A : Type v} [comm_semiring R]
    [semiring A] [algebra R A] : complete_lattice (subalgebra R A) :=
  galois_insertion.lift_complete_lattice algebra.gi

protected instance subalgebra.inhabited {R : Type u} {A : Type v} [comm_semiring R] [semiring A]
    [algebra R A] : Inhabited (subalgebra R A) :=
  { default := ⊥ }

theorem mem_bot {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A] {x : A} :
    x ∈ ⊥ ↔ x ∈ set.range ⇑(algebra_map R A) :=
  sorry

theorem to_submodule_bot {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A] :
    ↑⊥ = submodule.span R (singleton 1) :=
  sorry

@[simp] theorem mem_top {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    {x : A} : x ∈ ⊤ :=
  subsemiring.subset_closure (Or.inr trivial)

@[simp] theorem coe_top {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A] :
    ↑⊤ = ⊤ :=
  submodule.ext fun (x : A) => iff_of_true mem_top trivial

@[simp] theorem coe_bot {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A] :
    ↑⊥ = set.range ⇑(algebra_map R A) :=
  sorry

theorem eq_top_iff {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    {S : subalgebra R A} : S = ⊤ ↔ ∀ (x : A), x ∈ S :=
  sorry

@[simp] theorem map_top {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A]
    [algebra R A] [semiring B] [algebra R B] (f : alg_hom R A B) :
    subalgebra.map ⊤ f = alg_hom.range f :=
  sorry

@[simp] theorem map_bot {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A]
    [algebra R A] [semiring B] [algebra R B] (f : alg_hom R A B) : subalgebra.map ⊥ f = ⊥ :=
  sorry

@[simp] theorem comap_top {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A]
    [algebra R A] [semiring B] [algebra R B] (f : alg_hom R A B) : subalgebra.comap' ⊤ f = ⊤ :=
  iff.mpr eq_top_iff fun (x : A) => mem_top

/-- `alg_hom` to `⊤ : subalgebra R A`. -/
def to_top {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A] :
    alg_hom R A ↥⊤ :=
  alg_hom.mk (fun (x : A) => { val := x, property := mem_top }) sorry sorry sorry sorry sorry

theorem surjective_algebra_map_iff {R : Type u} {A : Type v} [comm_semiring R] [semiring A]
    [algebra R A] : function.surjective ⇑(algebra_map R A) ↔ ⊤ = ⊥ :=
  sorry

theorem bijective_algebra_map_iff {R : Type u_1} {A : Type u_2} [field R] [semiring A]
    [nontrivial A] [algebra R A] : function.bijective ⇑(algebra_map R A) ↔ ⊤ = ⊥ :=
  { mp :=
      fun (h : function.bijective ⇑(algebra_map R A)) =>
        iff.mp surjective_algebra_map_iff (and.right h),
    mpr :=
      fun (h : ⊤ = ⊥) =>
        { left := ring_hom.injective (algebra_map R A),
          right := iff.mpr surjective_algebra_map_iff h } }

/-- The bottom subalgebra is isomorphic to the base ring. -/
def bot_equiv_of_injective {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    (h : function.injective ⇑(algebra_map R A)) : alg_equiv R (↥⊥) R :=
  alg_equiv.symm (alg_equiv.of_bijective (of_id R ↥⊥) sorry)

/-- The bottom subalgebra is isomorphic to the field. -/
def bot_equiv (F : Type u_1) (R : Type u_2) [field F] [semiring R] [nontrivial R] [algebra F R] :
    alg_equiv F (↥⊥) F :=
  bot_equiv_of_injective sorry

/-- The top subalgebra is isomorphic to the field. -/
def top_equiv {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A] :
    alg_equiv R (↥⊤) A :=
  alg_equiv.symm (alg_equiv.of_bijective to_top sorry)

end algebra


namespace subalgebra


theorem range_val {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
    (S : subalgebra R A) : alg_hom.range (val S) = S :=
  ext (iff.mp set.ext_iff (Eq.trans (alg_hom.coe_range (val S)) subtype.range_val))

protected instance unique {R : Type u} [comm_semiring R] : unique (subalgebra R R) :=
  unique.mk { default := Inhabited.default } sorry

end subalgebra


/-- A subsemiring is a `ℕ`-subalgebra. -/
def subalgebra_of_subsemiring {R : Type u_1} [semiring R] (S : subsemiring R) : subalgebra ℕ R :=
  subalgebra.mk (subsemiring.carrier S) (subsemiring.one_mem' S) (subsemiring.mul_mem' S)
    (subsemiring.zero_mem' S) (subsemiring.add_mem' S) sorry

@[simp] theorem mem_subalgebra_of_subsemiring {R : Type u_1} [semiring R] {x : R}
    {S : subsemiring R} : x ∈ subalgebra_of_subsemiring S ↔ x ∈ S :=
  iff.rfl

/-- A subring is a `ℤ`-subalgebra. -/
def subalgebra_of_subring {R : Type u_1} [ring R] (S : subring R) : subalgebra ℤ R :=
  subalgebra.mk (subring.carrier S) (subring.one_mem' S) (subring.mul_mem' S) (subring.zero_mem' S)
    (subring.add_mem' S) sorry

/-- A subset closed under the ring operations is a `ℤ`-subalgebra. -/
def subalgebra_of_is_subring {R : Type u_1} [ring R] (S : set R) [is_subring S] : subalgebra ℤ R :=
  subalgebra_of_subring (set.to_subring S)

@[simp] theorem mem_subalgebra_of_subring {R : Type u_1} [ring R] {x : R} {S : subring R} :
    x ∈ subalgebra_of_subring S ↔ x ∈ S :=
  iff.rfl

@[simp] theorem mem_subalgebra_of_is_subring {R : Type u_1} [ring R] {x : R} {S : set R}
    [is_subring S] : x ∈ subalgebra_of_is_subring S ↔ x ∈ S :=
  iff.rfl

end Mathlib