/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.group_theory.submonoid.basic
import Mathlib.data.equiv.mul_add
import Mathlib.algebra.group.prod
import Mathlib.algebra.group.inj_surj
import Mathlib.PostPort

universes u_1 u_2 u_3 u_4 

namespace Mathlib

/-!
# Operations on `submonoid`s

In this file we define various operations on `submonoid`s and `monoid_hom`s.

## Main definitions

### Conversion between multiplicative and additive definitions

* `submonoid.to_add_submonoid`, `submonoid.of_add_submonoid`, `add_submonoid.to_submonoid`,
  `add_submonoid.of_submonoid`: convert between multiplicative and additive submonoids of `M`,
  `multiplicative M`, and `additive M`.
* `submonoid.add_submonoid_equiv`: equivalence between `submonoid M`
  and `add_submonoid (additive M)`.

### (Commutative) monoid structure on a submonoid

* `submonoid.to_monoid`, `submonoid.to_comm_monoid`: a submonoid inherits a (commutative) monoid
  structure.

### Operations on submonoids

* `submonoid.comap`: preimage of a submonoid under a monoid homomorphism as a submonoid of the
  domain;
* `submonoid.map`: image of a submonoid under a monoid homomorphism as a submonoid of the codomain;
* `submonoid.prod`: product of two submonoids `s : submonoid M` and `t : submonoid N` as a submonoid
  of `M × N`;

### Monoid homomorphisms between submonoid

* `submonoid.subtype`: embedding of a submonoid into the ambient monoid.
* `submonoid.inclusion`: given two submonoids `S`, `T` such that `S ≤ T`, `S.inclusion T` is the
  inclusion of `S` into `T` as a monoid homomorphism;
* `mul_equiv.submonoid_congr`: converts a proof of `S = T` into a monoid isomorphism between `S`
  and `T`.
* `submonoid.prod_equiv`: monoid isomorphism between `s.prod t` and `s × t`;

### Operations on `monoid_hom`s

* `monoid_hom.mrange`: range of a monoid homomorphism as a submonoid of the codomain;
* `monoid_hom.mrestrict`: restrict a monoid homomorphism to a submonoid;
* `monoid_hom.cod_mrestrict`: restrict the codomain of a monoid homomorphism to a submonoid;
* `monoid_hom.mrange_restrict`: restrict a monoid homomorphism to its range;

## Tags

submonoid, range, product, map, comap
-/

/-!
### Conversion to/from `additive`/`multiplicative`
-/

/-- Map from submonoids of monoid `M` to `add_submonoid`s of `additive M`. -/
def submonoid.to_add_submonoid {M : Type u_1} [monoid M] (S : submonoid M) : add_submonoid (additive M) :=
  add_submonoid.mk (submonoid.carrier S) (submonoid.one_mem' S) (submonoid.mul_mem' S)

/-- Map from `add_submonoid`s of `additive M` to submonoids of `M`. -/
def submonoid.of_add_submonoid {M : Type u_1} [monoid M] (S : add_submonoid (additive M)) : submonoid M :=
  submonoid.mk (add_submonoid.carrier S) sorry sorry

/-- Map from `add_submonoid`s of `add_monoid M` to submonoids of `multiplicative M`. -/
def add_submonoid.to_submonoid {M : Type u_1} [add_monoid M] (S : add_submonoid M) : submonoid (multiplicative M) :=
  submonoid.mk (add_submonoid.carrier S) (add_submonoid.zero_mem' S) (add_submonoid.add_mem' S)

/-- Map from submonoids of `multiplicative M` to `add_submonoid`s of `add_monoid M`. -/
def add_submonoid.of_submonoid {M : Type u_1} [add_monoid M] (S : submonoid (multiplicative M)) : add_submonoid M :=
  add_submonoid.mk (submonoid.carrier S) sorry sorry

/-- Submonoids of monoid `M` are isomorphic to additive submonoids of `additive M`. -/
def submonoid.add_submonoid_equiv (M : Type u_1) [monoid M] : submonoid M ≃ add_submonoid (additive M) :=
  equiv.mk submonoid.to_add_submonoid submonoid.of_add_submonoid sorry sorry

namespace submonoid


/-!
### `comap` and `map`
-/

/-- The preimage of a submonoid along a monoid homomorphism is a submonoid. -/
def comap {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] (f : M →* N) (S : submonoid N) : submonoid M :=
  mk (⇑f ⁻¹' ↑S) sorry sorry

@[simp] theorem coe_comap {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] (S : submonoid N) (f : M →* N) : ↑(comap f S) = ⇑f ⁻¹' ↑S :=
  rfl

@[simp] theorem mem_comap {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] {S : submonoid N} {f : M →* N} {x : M} : x ∈ comap f S ↔ coe_fn f x ∈ S :=
  iff.rfl

theorem Mathlib.add_submonoid.comap_comap {M : Type u_1} {N : Type u_2} {P : Type u_3} [add_monoid M] [add_monoid N] [add_monoid P] (S : add_submonoid P) (g : N →+ P) (f : M →+ N) : add_submonoid.comap f (add_submonoid.comap g S) = add_submonoid.comap (add_monoid_hom.comp g f) S :=
  rfl

@[simp] theorem Mathlib.add_submonoid.comap_id {P : Type u_3} [add_monoid P] (S : add_submonoid P) : add_submonoid.comap (add_monoid_hom.id P) S = S := sorry

/-- The image of a submonoid along a monoid homomorphism is a submonoid. -/
def map {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] (f : M →* N) (S : submonoid M) : submonoid N :=
  mk (⇑f '' ↑S) sorry sorry

@[simp] theorem coe_map {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] (f : M →* N) (S : submonoid M) : ↑(map f S) = ⇑f '' ↑S :=
  rfl

@[simp] theorem mem_map {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] {f : M →* N} {S : submonoid M} {y : N} : y ∈ map f S ↔ ∃ (x : M), ∃ (H : x ∈ S), coe_fn f x = y :=
  set.mem_image_iff_bex

theorem Mathlib.add_submonoid.mem_map_of_mem {M : Type u_1} {N : Type u_2} [add_monoid M] [add_monoid N] (S : add_submonoid M) (f : M →+ N) (x : ↥S) : coe_fn f ↑x ∈ add_submonoid.map f S :=
  set.mem_image_of_mem (⇑f) (subtype.property x)

theorem map_map {M : Type u_1} {N : Type u_2} {P : Type u_3} [monoid M] [monoid N] [monoid P] (S : submonoid M) (g : N →* P) (f : M →* N) : map g (map f S) = map (monoid_hom.comp g f) S :=
  ext' (set.image_image (fun (a : N) => coe_fn g a) (fun (a : M) => coe_fn f a) ↑S)

theorem map_le_iff_le_comap {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] {f : M →* N} {S : submonoid M} {T : submonoid N} : map f S ≤ T ↔ S ≤ comap f T :=
  set.image_subset_iff

theorem Mathlib.add_submonoid.gc_map_comap {M : Type u_1} {N : Type u_2} [add_monoid M] [add_monoid N] (f : M →+ N) : galois_connection (add_submonoid.map f) (add_submonoid.comap f) :=
  fun (S : add_submonoid M) (T : add_submonoid N) => add_submonoid.map_le_iff_le_comap

theorem map_le_of_le_comap {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] (S : submonoid M) {T : submonoid N} {f : M →* N} : S ≤ comap f T → map f S ≤ T :=
  galois_connection.l_le (gc_map_comap f)

theorem le_comap_of_map_le {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] (S : submonoid M) {T : submonoid N} {f : M →* N} : map f S ≤ T → S ≤ comap f T :=
  galois_connection.le_u (gc_map_comap f)

theorem le_comap_map {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] (S : submonoid M) {f : M →* N} : S ≤ comap f (map f S) :=
  galois_connection.le_u_l (gc_map_comap f) S

theorem map_comap_le {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] {S : submonoid N} {f : M →* N} : map f (comap f S) ≤ S :=
  galois_connection.l_u_le (gc_map_comap f) S

theorem monotone_map {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] {f : M →* N} : monotone (map f) :=
  galois_connection.monotone_l (gc_map_comap f)

theorem Mathlib.add_submonoid.monotone_comap {M : Type u_1} {N : Type u_2} [add_monoid M] [add_monoid N] {f : M →+ N} : monotone (add_submonoid.comap f) :=
  galois_connection.monotone_u (add_submonoid.gc_map_comap f)

@[simp] theorem map_comap_map {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] (S : submonoid M) {f : M →* N} : map f (comap f (map f S)) = map f S :=
  congr_fun (galois_connection.l_u_l_eq_l (gc_map_comap f)) S

@[simp] theorem comap_map_comap {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] {S : submonoid N} {f : M →* N} : comap f (map f (comap f S)) = comap f S :=
  congr_fun (galois_connection.u_l_u_eq_u (gc_map_comap f)) S

theorem map_sup {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] (S : submonoid M) (T : submonoid M) (f : M →* N) : map f (S ⊔ T) = map f S ⊔ map f T :=
  galois_connection.l_sup (gc_map_comap f)

theorem map_supr {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] {ι : Sort u_3} (f : M →* N) (s : ι → submonoid M) : map f (supr s) = supr fun (i : ι) => map f (s i) :=
  galois_connection.l_supr (gc_map_comap f)

theorem Mathlib.add_submonoid.comap_inf {M : Type u_1} {N : Type u_2} [add_monoid M] [add_monoid N] (S : add_submonoid N) (T : add_submonoid N) (f : M →+ N) : add_submonoid.comap f (S ⊓ T) = add_submonoid.comap f S ⊓ add_submonoid.comap f T :=
  galois_connection.u_inf (add_submonoid.gc_map_comap f)

theorem Mathlib.add_submonoid.comap_infi {M : Type u_1} {N : Type u_2} [add_monoid M] [add_monoid N] {ι : Sort u_3} (f : M →+ N) (s : ι → add_submonoid N) : add_submonoid.comap f (infi s) = infi fun (i : ι) => add_submonoid.comap f (s i) :=
  galois_connection.u_infi (add_submonoid.gc_map_comap f)

@[simp] theorem map_bot {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] (f : M →* N) : map f ⊥ = ⊥ :=
  galois_connection.l_bot (gc_map_comap f)

@[simp] theorem comap_top {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] (f : M →* N) : comap f ⊤ = ⊤ :=
  galois_connection.u_top (gc_map_comap f)

@[simp] theorem Mathlib.add_submonoid.map_id {M : Type u_1} [add_monoid M] (S : add_submonoid M) : add_submonoid.map (add_monoid_hom.id M) S = S := sorry

/-- `map f` and `comap f` form a `galois_coinsertion` when `f` is injective. -/
def gci_map_comap {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] {f : M →* N} (hf : function.injective ⇑f) : galois_coinsertion (map f) (comap f) :=
  galois_connection.to_galois_coinsertion (gc_map_comap f) sorry

theorem comap_map_eq_of_injective {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] {f : M →* N} (hf : function.injective ⇑f) (S : submonoid M) : comap f (map f S) = S :=
  galois_coinsertion.u_l_eq (gci_map_comap hf) S

theorem comap_surjective_of_injective {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] {f : M →* N} (hf : function.injective ⇑f) : function.surjective (comap f) :=
  galois_coinsertion.u_surjective (gci_map_comap hf)

theorem map_injective_of_injective {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] {f : M →* N} (hf : function.injective ⇑f) : function.injective (map f) :=
  galois_coinsertion.l_injective (gci_map_comap hf)

theorem comap_inf_map_of_injective {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] {f : M →* N} (hf : function.injective ⇑f) (S : submonoid M) (T : submonoid M) : comap f (map f S ⊓ map f T) = S ⊓ T :=
  galois_coinsertion.u_inf_l (gci_map_comap hf) S T

theorem comap_infi_map_of_injective {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] {ι : Type u_4} {f : M →* N} (hf : function.injective ⇑f) (S : ι → submonoid M) : comap f (infi fun (i : ι) => map f (S i)) = infi S :=
  galois_coinsertion.u_infi_l (gci_map_comap hf) fun (i : ι) => S i

theorem comap_sup_map_of_injective {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] {f : M →* N} (hf : function.injective ⇑f) (S : submonoid M) (T : submonoid M) : comap f (map f S ⊔ map f T) = S ⊔ T :=
  galois_coinsertion.u_sup_l (gci_map_comap hf) S T

theorem comap_supr_map_of_injective {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] {ι : Type u_4} {f : M →* N} (hf : function.injective ⇑f) (S : ι → submonoid M) : comap f (supr fun (i : ι) => map f (S i)) = supr S :=
  galois_coinsertion.u_supr_l (gci_map_comap hf) fun (i : ι) => S i

theorem map_le_map_iff_of_injective {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] {f : M →* N} (hf : function.injective ⇑f) {S : submonoid M} {T : submonoid M} : map f S ≤ map f T ↔ S ≤ T :=
  galois_coinsertion.l_le_l_iff (gci_map_comap hf)

theorem map_strict_mono_of_injective {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] {f : M →* N} (hf : function.injective ⇑f) : strict_mono (map f) :=
  galois_coinsertion.strict_mono_l (gci_map_comap hf)

/-- `map f` and `comap f` form a `galois_insertion` when `f` is surjective. -/
def gi_map_comap {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] {f : M →* N} (hf : function.surjective ⇑f) : galois_insertion (map f) (comap f) :=
  galois_connection.to_galois_insertion (gc_map_comap f) sorry

theorem map_comap_eq_of_surjective {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] {f : M →* N} (hf : function.surjective ⇑f) (S : submonoid N) : map f (comap f S) = S :=
  galois_insertion.l_u_eq (gi_map_comap hf) S

theorem map_surjective_of_surjective {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] {f : M →* N} (hf : function.surjective ⇑f) : function.surjective (map f) :=
  galois_insertion.l_surjective (gi_map_comap hf)

theorem comap_injective_of_surjective {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] {f : M →* N} (hf : function.surjective ⇑f) : function.injective (comap f) :=
  galois_insertion.u_injective (gi_map_comap hf)

theorem map_inf_comap_of_surjective {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] {f : M →* N} (hf : function.surjective ⇑f) (S : submonoid N) (T : submonoid N) : map f (comap f S ⊓ comap f T) = S ⊓ T :=
  galois_insertion.l_inf_u (gi_map_comap hf) S T

theorem map_infi_comap_of_surjective {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] {ι : Type u_4} {f : M →* N} (hf : function.surjective ⇑f) (S : ι → submonoid N) : map f (infi fun (i : ι) => comap f (S i)) = infi S :=
  galois_insertion.l_infi_u (gi_map_comap hf) fun (i : ι) => S i

theorem map_sup_comap_of_surjective {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] {f : M →* N} (hf : function.surjective ⇑f) (S : submonoid N) (T : submonoid N) : map f (comap f S ⊔ comap f T) = S ⊔ T :=
  galois_insertion.l_sup_u (gi_map_comap hf) S T

theorem map_supr_comap_of_surjective {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] {ι : Type u_4} {f : M →* N} (hf : function.surjective ⇑f) (S : ι → submonoid N) : map f (supr fun (i : ι) => comap f (S i)) = supr S :=
  galois_insertion.l_supr_u (gi_map_comap hf) fun (i : ι) => S i

theorem comap_le_comap_iff_of_surjective {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] {f : M →* N} (hf : function.surjective ⇑f) {S : submonoid N} {T : submonoid N} : comap f S ≤ comap f T ↔ S ≤ T :=
  galois_insertion.u_le_u_iff (gi_map_comap hf)

theorem comap_strict_mono_of_surjective {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] {f : M →* N} (hf : function.surjective ⇑f) : strict_mono (comap f) :=
  galois_insertion.strict_mono_u (gi_map_comap hf)

/-- A submonoid of a monoid inherits a multiplication. -/
protected instance Mathlib.add_submonoid.has_add {M : Type u_1} [add_monoid M] (S : add_submonoid M) : Add ↥S :=
  { add := fun (a b : ↥S) => { val := subtype.val a + subtype.val b, property := sorry } }

/-- A submonoid of a monoid inherits a 1. -/
protected instance has_one {M : Type u_1} [monoid M] (S : submonoid M) : HasOne ↥S :=
  { one := { val := 1, property := one_mem S } }

@[simp] theorem coe_mul {M : Type u_1} [monoid M] (S : submonoid M) (x : ↥S) (y : ↥S) : ↑(x * y) = ↑x * ↑y :=
  rfl

@[simp] theorem Mathlib.add_submonoid.coe_zero {M : Type u_1} [add_monoid M] (S : add_submonoid M) : ↑0 = 0 :=
  rfl

/-- A submonoid of a monoid inherits a monoid structure. -/
protected instance to_monoid {M : Type u_1} [monoid M] (S : submonoid M) : monoid ↥S :=
  function.injective.monoid coe (coe_injective S) sorry sorry

/-- A submonoid of a `comm_monoid` is a `comm_monoid`. -/
protected instance to_comm_monoid {M : Type u_1} [comm_monoid M] (S : submonoid M) : comm_monoid ↥S :=
  function.injective.comm_monoid coe sorry sorry sorry

/-- The natural monoid hom from a submonoid of monoid `M` to `M`. -/
def Mathlib.add_submonoid.subtype {M : Type u_1} [add_monoid M] (S : add_submonoid M) : ↥S →+ M :=
  add_monoid_hom.mk coe sorry sorry

@[simp] theorem Mathlib.add_submonoid.coe_subtype {M : Type u_1} [add_monoid M] (S : add_submonoid M) : ⇑(add_submonoid.subtype S) = coe :=
  rfl

/-- An induction principle on elements of the type `submonoid.closure s`.
If `p` holds for `1` and all elements of `s`, and is preserved under multiplication, then `p`
holds for all elements of the closure of `s`.

The difference with `submonoid.closure_induction` is that this acts on the subtype.
-/
theorem Mathlib.add_submonoid.closure_induction' {M : Type u_1} [add_monoid M] (s : set M) {p : ↥(add_submonoid.closure s) → Prop} (Hs : ∀ (x : M) (h : x ∈ s), p { val := x, property := add_submonoid.subset_closure h }) (H1 : p 0) (Hmul : ∀ (x y : ↥(add_submonoid.closure s)), p x → p y → p (x + y)) (x : ↥(add_submonoid.closure s)) : p x := sorry

/-- Given `submonoid`s `s`, `t` of monoids `M`, `N` respectively, `s × t` as a submonoid
of `M × N`. -/
def prod {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] (s : submonoid M) (t : submonoid N) : submonoid (M × N) :=
  mk (set.prod ↑s ↑t) sorry sorry

theorem coe_prod {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] (s : submonoid M) (t : submonoid N) : ↑(prod s t) = set.prod ↑s ↑t :=
  rfl

theorem Mathlib.add_submonoid.mem_prod {M : Type u_1} {N : Type u_2} [add_monoid M] [add_monoid N] {s : add_submonoid M} {t : add_submonoid N} {p : M × N} : p ∈ add_submonoid.prod s t ↔ prod.fst p ∈ s ∧ prod.snd p ∈ t :=
  iff.rfl

theorem prod_mono {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] {s₁ : submonoid M} {s₂ : submonoid M} {t₁ : submonoid N} {t₂ : submonoid N} (hs : s₁ ≤ s₂) (ht : t₁ ≤ t₂) : prod s₁ t₁ ≤ prod s₂ t₂ :=
  set.prod_mono hs ht

theorem prod_top {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] (s : submonoid M) : prod s ⊤ = comap (monoid_hom.fst M N) s := sorry

theorem top_prod {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] (s : submonoid N) : prod ⊤ s = comap (monoid_hom.snd M N) s := sorry

@[simp] theorem top_prod_top {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] : prod ⊤ ⊤ = ⊤ :=
  Eq.trans (top_prod ⊤) (comap_top (monoid_hom.snd M N))

theorem bot_prod_bot {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] : prod ⊥ ⊥ = ⊥ := sorry

/-- The product of submonoids is isomorphic to their product as monoids. -/
def prod_equiv {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] (s : submonoid M) (t : submonoid N) : ↥(prod s t) ≃* ↥s × ↥t :=
  mul_equiv.mk (equiv.to_fun (equiv.set.prod ↑s ↑t)) (equiv.inv_fun (equiv.set.prod ↑s ↑t)) sorry sorry sorry

theorem map_inl {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] (s : submonoid M) : map (monoid_hom.inl M N) s = prod s ⊥ := sorry

theorem map_inr {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] (s : submonoid N) : map (monoid_hom.inr M N) s = prod ⊥ s := sorry

@[simp] theorem prod_bot_sup_bot_prod {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] (s : submonoid M) (t : submonoid N) : prod s ⊥ ⊔ prod ⊥ t = prod s t := sorry

end submonoid


namespace monoid_hom


/-- The range of a monoid homomorphism is a submonoid. -/
def mrange {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] (f : M →* N) : submonoid N :=
  submonoid.map f ⊤

@[simp] theorem coe_mrange {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] (f : M →* N) : ↑(mrange f) = set.range ⇑f :=
  set.image_univ

@[simp] theorem mem_mrange {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] {f : M →* N} {y : N} : y ∈ mrange f ↔ ∃ (x : M), coe_fn f x = y := sorry

theorem map_mrange {M : Type u_1} {N : Type u_2} {P : Type u_3} [monoid M] [monoid N] [monoid P] (g : N →* P) (f : M →* N) : submonoid.map g (mrange f) = mrange (comp g f) :=
  submonoid.map_map ⊤ g f

theorem Mathlib.add_monoid_hom.mrange_top_iff_surjective {M : Type u_1} [add_monoid M] {N : Type u_2} [add_monoid N] {f : M →+ N} : add_monoid_hom.mrange f = ⊤ ↔ function.surjective ⇑f := sorry

/-- The range of a surjective monoid hom is the whole of the codomain. -/
theorem Mathlib.add_monoid_hom.mrange_top_of_surjective {M : Type u_1} [add_monoid M] {N : Type u_2} [add_monoid N] (f : M →+ N) (hf : function.surjective ⇑f) : add_monoid_hom.mrange f = ⊤ :=
  iff.mpr add_monoid_hom.mrange_top_iff_surjective hf

theorem Mathlib.add_monoid_hom.mrange_eq_map {M : Type u_1} {N : Type u_2} [add_monoid M] [add_monoid N] (f : M →+ N) : add_monoid_hom.mrange f = add_submonoid.map f ⊤ :=
  rfl

theorem mclosure_preimage_le {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] (f : M →* N) (s : set N) : submonoid.closure (⇑f ⁻¹' s) ≤ submonoid.comap f (submonoid.closure s) :=
  iff.mpr submonoid.closure_le
    fun (x : M) (hx : x ∈ ⇑f ⁻¹' s) =>
      iff.mpr submonoid.mem_coe (iff.mpr submonoid.mem_comap (submonoid.subset_closure hx))

/-- The image under a monoid hom of the submonoid generated by a set equals the submonoid generated
    by the image of the set. -/
theorem Mathlib.add_monoid_hom.map_mclosure {M : Type u_1} {N : Type u_2} [add_monoid M] [add_monoid N] (f : M →+ N) (s : set M) : add_submonoid.map f (add_submonoid.closure s) = add_submonoid.closure (⇑f '' s) := sorry

/-- Restriction of a monoid hom to a submonoid of the domain. -/
def mrestrict {M : Type u_1} [monoid M] {N : Type u_2} [monoid N] (f : M →* N) (S : submonoid M) : ↥S →* N :=
  comp f (submonoid.subtype S)

@[simp] theorem Mathlib.add_monoid_hom.mrestrict_apply {M : Type u_1} [add_monoid M] (S : add_submonoid M) {N : Type u_2} [add_monoid N] (f : M →+ N) (x : ↥S) : coe_fn (add_monoid_hom.mrestrict f S) x = coe_fn f ↑x :=
  rfl

/-- Restriction of a monoid hom to a submonoid of the codomain. -/
def cod_mrestrict {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] (f : M →* N) (S : submonoid N) (h : ∀ (x : M), coe_fn f x ∈ S) : M →* ↥S :=
  mk (fun (n : M) => { val := coe_fn f n, property := h n }) sorry sorry

/-- Restriction of a monoid hom to its range interpreted as a submonoid. -/
def mrange_restrict {M : Type u_1} [monoid M] {N : Type u_2} [monoid N] (f : M →* N) : M →* ↥(mrange f) :=
  cod_mrestrict f (mrange f) sorry

@[simp] theorem Mathlib.add_monoid_hom.coe_mrange_restrict {M : Type u_1} [add_monoid M] {N : Type u_2} [add_monoid N] (f : M →+ N) (x : M) : ↑(coe_fn (add_monoid_hom.mrange_restrict f) x) = coe_fn f x :=
  rfl

end monoid_hom


namespace submonoid


theorem Mathlib.add_submonoid.mrange_inl {M : Type u_1} {N : Type u_2} [add_monoid M] [add_monoid N] : add_monoid_hom.mrange (add_monoid_hom.inl M N) = add_submonoid.prod ⊤ ⊥ :=
  add_submonoid.map_inl ⊤

theorem mrange_inr {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] : monoid_hom.mrange (monoid_hom.inr M N) = prod ⊥ ⊤ :=
  map_inr ⊤

theorem mrange_inl' {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] : monoid_hom.mrange (monoid_hom.inl M N) = comap (monoid_hom.snd M N) ⊥ :=
  Eq.trans mrange_inl (top_prod ⊥)

theorem mrange_inr' {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] : monoid_hom.mrange (monoid_hom.inr M N) = comap (monoid_hom.fst M N) ⊥ :=
  Eq.trans mrange_inr (prod_top ⊥)

@[simp] theorem mrange_fst {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] : monoid_hom.mrange (monoid_hom.fst M N) = ⊤ :=
  monoid_hom.mrange_top_of_surjective (monoid_hom.fst M N) prod.fst_surjective

@[simp] theorem mrange_snd {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] : monoid_hom.mrange (monoid_hom.snd M N) = ⊤ :=
  monoid_hom.mrange_top_of_surjective (monoid_hom.snd M N) prod.snd_surjective

@[simp] theorem mrange_inl_sup_mrange_inr {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] : monoid_hom.mrange (monoid_hom.inl M N) ⊔ monoid_hom.mrange (monoid_hom.inr M N) = ⊤ := sorry

/-- The monoid hom associated to an inclusion of submonoids. -/
def inclusion {M : Type u_1} [monoid M] {S : submonoid M} {T : submonoid M} (h : S ≤ T) : ↥S →* ↥T :=
  monoid_hom.cod_mrestrict (subtype S) T sorry

@[simp] theorem range_subtype {M : Type u_1} [monoid M] (s : submonoid M) : monoid_hom.mrange (subtype s) = s :=
  ext' (Eq.trans (monoid_hom.coe_mrange (subtype s)) subtype.range_coe)

theorem eq_bot_iff_forall {M : Type u_1} [monoid M] (S : submonoid M) : S = ⊥ ↔ ∀ (x : M), x ∈ S → x = 1 := sorry

theorem Mathlib.add_submonoid.nontrivial_iff_exists_ne_zero {M : Type u_1} [add_monoid M] (S : add_submonoid M) : nontrivial ↥S ↔ ∃ (x : M), ∃ (H : x ∈ S), x ≠ 0 := sorry

/-- A submonoid is either the trivial submonoid or nontrivial. -/
theorem bot_or_nontrivial {M : Type u_1} [monoid M] (S : submonoid M) : S = ⊥ ∨ nontrivial ↥S := sorry

/-- A submonoid is either the trivial submonoid or contains a nonzero element. -/
theorem Mathlib.add_submonoid.bot_or_exists_ne_zero {M : Type u_1} [add_monoid M] (S : add_submonoid M) : S = ⊥ ∨ ∃ (x : M), ∃ (H : x ∈ S), x ≠ 0 := sorry

end submonoid


namespace mul_equiv


/-- Makes the identity isomorphism from a proof that two submonoids of a multiplicative
    monoid are equal. -/
def Mathlib.add_equiv.add_submonoid_congr {M : Type u_1} [add_monoid M] {S : add_submonoid M} {T : add_submonoid M} (h : S = T) : ↥S ≃+ ↥T :=
  add_equiv.mk (equiv.to_fun (equiv.set_congr sorry)) (equiv.inv_fun (equiv.set_congr sorry)) sorry sorry sorry

