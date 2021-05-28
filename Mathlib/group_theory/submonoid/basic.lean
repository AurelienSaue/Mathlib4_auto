/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.set.lattice
import Mathlib.PostPort

universes u_3 l u_1 u_2 

namespace Mathlib

/-!
# Submonoids: definition and `complete_lattice` structure

This file defines bundled multiplicative and additive submonoids. We also define
a `complete_lattice` structure on `submonoid`s, define the closure of a set as the minimal submonoid
that includes this set, and prove a few results about extending properties from a dense set (i.e.
a set with `closure s = ⊤`) to the whole monoid, see `submonoid.dense_induction` and
`monoid_hom.of_mdense`.

## Main definitions

* `submonoid M`: the type of bundled submonoids of a monoid `M`; the underlying set is given in
  the `carrier` field of the structure, and should be accessed through coercion as in `(S : set M)`.
* `add_submonoid M` : the type of bundled submonoids of an additive monoid `M`.

For each of the following definitions in the `submonoid` namespace, there is a corresponding
definition in the `add_submonoid` namespace.

* `submonoid.copy` : copy of a submonoid with `carrier` replaced by a set that is equal but possibly
  not definitionally equal to the carrier of the original `submonoid`.
* `submonoid.closure` :  monoid closure of a set, i.e., the least submonoid that includes the set.
* `submonoid.gi` : `closure : set M → submonoid M` and coercion `coe : submonoid M → set M`
  form a `galois_insertion`;
* `monoid_hom.eq_mlocus`: the submonoid of elements `x : M` such that `f x = g x`;
* `monoid_hom.of_mdense`:  if a map `f : M → N` between two monoids satisfies `f 1 = 1` and
  `f (x * y) = f x * f y` for `y` from some dense set `s`, then `f` is a monoid homomorphism.
  E.g., if `f : ℕ → M` satisfies `f 0 = 0` and `f (x + 1) = f x + f 1`, then `f` is an additive
  monoid homomorphism.

## Implementation notes

Submonoid inclusion is denoted `≤` rather than `⊆`, although `∈` is defined as
membership of a submonoid's underlying set.

This file is designed to have very few dependencies. In particular, it should not use natural
numbers.

## Tags
submonoid, submonoids
-/

/-- A submonoid of a monoid `M` is a subset containing 1 and closed under multiplication. -/
structure submonoid (M : Type u_3) [monoid M] 
where
  carrier : set M
  one_mem' : 1 ∈ carrier
  mul_mem' : ∀ {a b : M}, a ∈ carrier → b ∈ carrier → a * b ∈ carrier

/-- An additive submonoid of an additive monoid `M` is a subset containing 0 and
  closed under addition. -/
structure add_submonoid (M : Type u_3) [add_monoid M] 
where
  carrier : set M
  zero_mem' : 0 ∈ carrier
  add_mem' : ∀ {a b : M}, a ∈ carrier → b ∈ carrier → a + b ∈ carrier

namespace submonoid


protected instance Mathlib.add_submonoid.set.has_coe {M : Type u_1} [add_monoid M] : has_coe (add_submonoid M) (set M) :=
  has_coe.mk add_submonoid.carrier

protected instance has_mem {M : Type u_1} [monoid M] : has_mem M (submonoid M) :=
  has_mem.mk fun (m : M) (S : submonoid M) => m ∈ ↑S

protected instance has_coe_to_sort {M : Type u_1} [monoid M] : has_coe_to_sort (submonoid M) :=
  has_coe_to_sort.mk (Type u_1) fun (S : submonoid M) => Subtype fun (x : M) => x ∈ S

@[simp] theorem mem_carrier {M : Type u_1} [monoid M] {s : submonoid M} {x : M} : x ∈ carrier s ↔ x ∈ s :=
  iff.rfl

@[simp] theorem mem_coe {M : Type u_1} [monoid M] {S : submonoid M} {m : M} : m ∈ ↑S ↔ m ∈ S :=
  iff.rfl

@[simp] theorem coe_coe {M : Type u_1} [monoid M] (s : submonoid M) : ↥↑s = ↥s :=
  rfl

protected theorem Mathlib.add_submonoid.exists {M : Type u_1} [add_monoid M] {s : add_submonoid M} {p : ↥s → Prop} : (∃ (x : ↥s), p x) ↔ ∃ (x : M), ∃ (H : x ∈ s), p { val := x, property := H } :=
  set_coe.exists

protected theorem forall {M : Type u_1} [monoid M] {s : submonoid M} {p : ↥s → Prop} : (∀ (x : ↥s), p x) ↔ ∀ (x : M) (H : x ∈ s), p { val := x, property := H } :=
  set_coe.forall

/-- Two submonoids are equal if the underlying subsets are equal. -/
theorem ext' {M : Type u_1} [monoid M] {S : submonoid M} {T : submonoid M} (h : ↑S = ↑T) : S = T := sorry

/-- Two submonoids are equal if and only if the underlying subsets are equal. -/
protected theorem ext'_iff {M : Type u_1} [monoid M] {S : submonoid M} {T : submonoid M} : S = T ↔ ↑S = ↑T :=
  { mp := fun (h : S = T) => h ▸ rfl, mpr := fun (h : ↑S = ↑T) => ext' h }

/-- Two submonoids are equal if they have the same elements. -/
theorem Mathlib.add_submonoid.ext {M : Type u_1} [add_monoid M] {S : add_submonoid M} {T : add_submonoid M} (h : ∀ (x : M), x ∈ S ↔ x ∈ T) : S = T :=
  add_submonoid.ext' (set.ext h)

/-- Copy a submonoid replacing `carrier` with a set that is equal to it. -/
def copy {M : Type u_1} [monoid M] (S : submonoid M) (s : set M) (hs : s = ↑S) : submonoid M :=
  mk s sorry sorry

@[simp] theorem coe_copy {M : Type u_1} [monoid M] {S : submonoid M} {s : set M} (hs : s = ↑S) : ↑(copy S s hs) = s :=
  rfl

theorem copy_eq {M : Type u_1} [monoid M] {S : submonoid M} {s : set M} (hs : s = ↑S) : copy S s hs = S :=
  ext' hs

/-- A submonoid contains the monoid's 1. -/
theorem Mathlib.add_submonoid.zero_mem {M : Type u_1} [add_monoid M] (S : add_submonoid M) : 0 ∈ S :=
  add_submonoid.zero_mem' S

/-- A submonoid is closed under multiplication. -/
theorem mul_mem {M : Type u_1} [monoid M] (S : submonoid M) {x : M} {y : M} : x ∈ S → y ∈ S → x * y ∈ S :=
  mul_mem' S

theorem coe_injective {M : Type u_1} [monoid M] (S : submonoid M) : function.injective coe :=
  subtype.val_injective

@[simp] theorem coe_eq_coe {M : Type u_1} [monoid M] (S : submonoid M) (x : ↥S) (y : ↥S) : ↑x = ↑y ↔ x = y :=
  set_coe.ext_iff

protected instance has_le {M : Type u_1} [monoid M] : HasLessEq (submonoid M) :=
  { LessEq := fun (S T : submonoid M) => ∀ {x : M}, x ∈ S → x ∈ T }

theorem le_def {M : Type u_1} [monoid M] {S : submonoid M} {T : submonoid M} : S ≤ T ↔ ∀ {x : M}, x ∈ S → x ∈ T :=
  iff.rfl

@[simp] theorem Mathlib.add_submonoid.coe_subset_coe {M : Type u_1} [add_monoid M] {S : add_submonoid M} {T : add_submonoid M} : ↑S ⊆ ↑T ↔ S ≤ T :=
  iff.rfl

protected instance Mathlib.add_submonoid.partial_order {M : Type u_1} [add_monoid M] : partial_order (add_submonoid M) :=
  partial_order.mk (fun (S T : add_submonoid M) => ∀ {x : M}, x ∈ S → x ∈ T) partial_order.lt sorry sorry sorry

@[simp] theorem coe_ssubset_coe {M : Type u_1} [monoid M] {S : submonoid M} {T : submonoid M} : ↑S ⊂ ↑T ↔ S < T :=
  iff.rfl

/-- The submonoid `M` of the monoid `M`. -/
protected instance has_top {M : Type u_1} [monoid M] : has_top (submonoid M) :=
  has_top.mk (mk set.univ sorry sorry)

/-- The trivial submonoid `{1}` of an monoid `M`. -/
protected instance Mathlib.add_submonoid.has_bot {M : Type u_1} [add_monoid M] : has_bot (add_submonoid M) :=
  has_bot.mk (add_submonoid.mk (singleton 0) sorry sorry)

protected instance Mathlib.add_submonoid.inhabited {M : Type u_1} [add_monoid M] : Inhabited (add_submonoid M) :=
  { default := ⊥ }

@[simp] theorem mem_bot {M : Type u_1} [monoid M] {x : M} : x ∈ ⊥ ↔ x = 1 :=
  set.mem_singleton_iff

@[simp] theorem mem_top {M : Type u_1} [monoid M] (x : M) : x ∈ ⊤ :=
  set.mem_univ x

@[simp] theorem Mathlib.add_submonoid.coe_top {M : Type u_1} [add_monoid M] : ↑⊤ = set.univ :=
  rfl

@[simp] theorem coe_bot {M : Type u_1} [monoid M] : ↑⊥ = singleton 1 :=
  rfl

/-- The inf of two submonoids is their intersection. -/
protected instance has_inf {M : Type u_1} [monoid M] : has_inf (submonoid M) :=
  has_inf.mk fun (S₁ S₂ : submonoid M) => mk (↑S₁ ∩ ↑S₂) sorry sorry

@[simp] theorem coe_inf {M : Type u_1} [monoid M] (p : submonoid M) (p' : submonoid M) : ↑(p ⊓ p') = ↑p ∩ ↑p' :=
  rfl

@[simp] theorem mem_inf {M : Type u_1} [monoid M] {p : submonoid M} {p' : submonoid M} {x : M} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' :=
  iff.rfl

protected instance has_Inf {M : Type u_1} [monoid M] : has_Inf (submonoid M) :=
  has_Inf.mk
    fun (s : set (submonoid M)) => mk (set.Inter fun (t : submonoid M) => set.Inter fun (H : t ∈ s) => ↑t) sorry sorry

@[simp] theorem coe_Inf {M : Type u_1} [monoid M] (S : set (submonoid M)) : ↑(Inf S) = set.Inter fun (s : submonoid M) => set.Inter fun (H : s ∈ S) => ↑s :=
  rfl

theorem Mathlib.add_submonoid.mem_Inf {M : Type u_1} [add_monoid M] {S : set (add_submonoid M)} {x : M} : x ∈ Inf S ↔ ∀ (p : add_submonoid M), p ∈ S → x ∈ p :=
  set.mem_bInter_iff

theorem mem_infi {M : Type u_1} [monoid M] {ι : Sort u_2} {S : ι → submonoid M} {x : M} : (x ∈ infi fun (i : ι) => S i) ↔ ∀ (i : ι), x ∈ S i := sorry

@[simp] theorem Mathlib.add_submonoid.coe_infi {M : Type u_1} [add_monoid M] {ι : Sort u_2} {S : ι → add_submonoid M} : ↑(infi fun (i : ι) => S i) = set.Inter fun (i : ι) => ↑(S i) := sorry

/-- Submonoids of a monoid form a complete lattice. -/
protected instance complete_lattice {M : Type u_1} [monoid M] : complete_lattice (submonoid M) :=
  complete_lattice.mk complete_lattice.sup LessEq Less sorry sorry sorry sorry sorry sorry has_inf.inf sorry sorry sorry ⊤
    sorry ⊥ sorry complete_lattice.Sup Inf sorry sorry sorry sorry

theorem subsingleton_iff {M : Type u_1} [monoid M] : subsingleton M ↔ subsingleton (submonoid M) := sorry

theorem nontrivial_iff {M : Type u_1} [monoid M] : nontrivial M ↔ nontrivial (submonoid M) :=
  iff.mp not_iff_not
    (iff.trans (iff.trans not_nontrivial_iff_subsingleton subsingleton_iff) (iff.symm not_nontrivial_iff_subsingleton))

protected instance subsingleton {M : Type u_1} [monoid M] [subsingleton M] : subsingleton (submonoid M) :=
  iff.mp subsingleton_iff _inst_3

protected instance nontrivial {M : Type u_1} [monoid M] [nontrivial M] : nontrivial (submonoid M) :=
  iff.mp nontrivial_iff _inst_3

/-- The `submonoid` generated by a set. -/
def Mathlib.add_submonoid.closure {M : Type u_1} [add_monoid M] (s : set M) : add_submonoid M :=
  Inf (set_of fun (S : add_submonoid M) => s ⊆ ↑S)

theorem mem_closure {M : Type u_1} [monoid M] {s : set M} {x : M} : x ∈ closure s ↔ ∀ (S : submonoid M), s ⊆ ↑S → x ∈ S :=
  mem_Inf

/-- The submonoid generated by a set includes the set. -/
@[simp] theorem subset_closure {M : Type u_1} [monoid M] {s : set M} : s ⊆ ↑(closure s) :=
  fun (x : M) (hx : x ∈ s) => iff.mpr mem_closure fun (S : submonoid M) (hS : s ⊆ ↑S) => hS hx

/-- A submonoid `S` includes `closure s` if and only if it includes `s`. -/
@[simp] theorem closure_le {M : Type u_1} [monoid M] {s : set M} {S : submonoid M} : closure s ≤ S ↔ s ⊆ ↑S :=
  { mp := set.subset.trans subset_closure, mpr := fun (h : s ⊆ ↑S) => Inf_le h }

/-- Submonoid closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
theorem Mathlib.add_submonoid.closure_mono {M : Type u_1} [add_monoid M] {s : set M} {t : set M} (h : s ⊆ t) : add_submonoid.closure s ≤ add_submonoid.closure t :=
  iff.mpr add_submonoid.closure_le (set.subset.trans h add_submonoid.subset_closure)

theorem Mathlib.add_submonoid.closure_eq_of_le {M : Type u_1} [add_monoid M] {s : set M} {S : add_submonoid M} (h₁ : s ⊆ ↑S) (h₂ : S ≤ add_submonoid.closure s) : add_submonoid.closure s = S :=
  le_antisymm (iff.mpr add_submonoid.closure_le h₁) h₂

/-- An induction principle for closure membership. If `p` holds for `1` and all elements of `s`, and
is preserved under multiplication, then `p` holds for all elements of the closure of `s`. -/
theorem closure_induction {M : Type u_1} [monoid M] {s : set M} {p : M → Prop} {x : M} (h : x ∈ closure s) (Hs : ∀ (x : M), x ∈ s → p x) (H1 : p 1) (Hmul : ∀ (x y : M), p x → p y → p (x * y)) : p x :=
  iff.mpr closure_le Hs x h

/-- If `s` is a dense set in a monoid `M`, `submonoid.closure s = ⊤`, then in order to prove that
some predicate `p` holds for all `x : M` it suffices to verify `p x` for `x ∈ s`, verify `p 1`,
and verify that `p x` and `p y` imply `p (x * y)`. -/
theorem dense_induction {M : Type u_1} [monoid M] {p : M → Prop} (x : M) {s : set M} (hs : closure s = ⊤) (Hs : ∀ (x : M), x ∈ s → p x) (H1 : p 1) (Hmul : ∀ (x y : M), p x → p y → p (x * y)) : p x := sorry

/-- If `s` is a dense set in an additive monoid `M`, `add_submonoid.closure s = ⊤`, then in order
to prove that some predicate `p` holds for all `x : M` it suffices to verify `p x` for `x ∈ s`,
verify `p 0`, and verify that `p x` and `p y` imply `p (x + y)`. -/
/-- `closure` forms a Galois insertion with the coercion to set. -/
protected def gi (M : Type u_1) [monoid M] : galois_insertion closure coe :=
  galois_insertion.mk (fun (s : set M) (_x : ↑(closure s) ≤ s) => closure s) sorry sorry sorry

/-- Closure of a submonoid `S` equals `S`. -/
@[simp] theorem closure_eq {M : Type u_1} [monoid M] (S : submonoid M) : closure ↑S = S :=
  galois_insertion.l_u_eq (submonoid.gi M) S

@[simp] theorem closure_empty {M : Type u_1} [monoid M] : closure ∅ = ⊥ :=
  galois_connection.l_bot (galois_insertion.gc (submonoid.gi M))

@[simp] theorem closure_univ {M : Type u_1} [monoid M] : closure set.univ = ⊤ :=
  coe_top ▸ closure_eq ⊤

theorem Mathlib.add_submonoid.closure_union {M : Type u_1} [add_monoid M] (s : set M) (t : set M) : add_submonoid.closure (s ∪ t) = add_submonoid.closure s ⊔ add_submonoid.closure t :=
  galois_connection.l_sup (galois_insertion.gc (add_submonoid.gi M))

theorem closure_Union {M : Type u_1} [monoid M] {ι : Sort u_2} (s : ι → set M) : closure (set.Union fun (i : ι) => s i) = supr fun (i : ι) => closure (s i) :=
  galois_connection.l_supr (galois_insertion.gc (submonoid.gi M))

end submonoid


/-- The submonoid consisting of the units of a monoid -/
def is_unit.submonoid (M : Type u_1) [monoid M] : submonoid M :=
  submonoid.mk (set_of is_unit) sorry sorry

theorem is_unit.mem_submonoid_iff {M : Type u_1} [monoid M] (a : M) : a ∈ is_unit.submonoid M ↔ is_unit a :=
  id (eq.mpr (id (Eq._oldrec (Eq.refl (a ∈ set_of is_unit ↔ is_unit a)) set.mem_set_of_eq)) (iff.refl (is_unit a)))

namespace monoid_hom


/-- The submonoid of elements `x : M` such that `f x = g x` -/
def eq_mlocus {M : Type u_1} [monoid M] {N : Type u_3} [monoid N] (f : M →* N) (g : M →* N) : submonoid M :=
  submonoid.mk (set_of fun (x : M) => coe_fn f x = coe_fn g x) sorry sorry

/-- If two monoid homomorphisms are equal on a set, then they are equal on its submonoid closure. -/
theorem Mathlib.add_monoid_hom.eq_on_mclosure {M : Type u_1} [add_monoid M] {N : Type u_3} [add_monoid N] {f : M →+ N} {g : M →+ N} {s : set M} (h : set.eq_on (⇑f) (⇑g) s) : set.eq_on ⇑f ⇑g ↑(add_submonoid.closure s) :=
  (fun (this : add_submonoid.closure s ≤ add_monoid_hom.eq_mlocus f g) => this) (iff.mpr add_submonoid.closure_le h)

theorem Mathlib.add_monoid_hom.eq_of_eq_on_mtop {M : Type u_1} [add_monoid M] {N : Type u_3} [add_monoid N] {f : M →+ N} {g : M →+ N} (h : set.eq_on ⇑f ⇑g ↑⊤) : f = g :=
  add_monoid_hom.ext fun (x : M) => h trivial

theorem eq_of_eq_on_mdense {M : Type u_1} [monoid M] {N : Type u_3} [monoid N] {s : set M} (hs : submonoid.closure s = ⊤) {f : M →* N} {g : M →* N} (h : set.eq_on (⇑f) (⇑g) s) : f = g :=
  eq_of_eq_on_mtop (hs ▸ eq_on_mclosure h)

/-- Let `s` be a subset of a monoid `M` such that the closure of `s` is the whole monoid.
Then `monoid_hom.of_mdense` defines a monoid homomorphism from `M` asking for a proof
of `f (x * y) = f x * f y` only for `y ∈ s`. -/
def of_mdense {M : Type u_1} [monoid M] {s : set M} {N : Type u_3} [monoid N] (f : M → N) (hs : submonoid.closure s = ⊤) (h1 : f 1 = 1) (hmul : ∀ (x y : M), y ∈ s → f (x * y) = f x * f y) : M →* N :=
  mk f h1 sorry

/-- Let `s` be a subset of an additive monoid `M` such that the closure of `s` is the whole monoid.
Then `add_monoid_hom.of_mdense` defines an additive monoid homomorphism from `M` asking for a proof
of `f (x + y) = f x + f y` only for `y ∈ s`. -/
@[simp] theorem coe_of_mdense {M : Type u_1} [monoid M] {s : set M} {N : Type u_3} [monoid N] (f : M → N) (hs : submonoid.closure s = ⊤) (h1 : f 1 = 1) (hmul : ∀ (x y : M), y ∈ s → f (x * y) = f x * f y) : ⇑(of_mdense f hs h1 hmul) = f :=
  rfl

