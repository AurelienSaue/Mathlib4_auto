/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mitchell Rowett, Scott Morrison, Johan Commelin, Mario Carneiro,
  Michael Howes
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.group_theory.subgroup
import Mathlib.deprecated.submonoid
import PostPort

universes u_3 l u_1 u_2 u_4 

namespace Mathlib

/-- `s` is an additive subgroup: a set containing 0 and closed under addition and negation. -/
class is_add_subgroup {A : Type u_3} [add_group A] (s : set A) 
extends is_add_submonoid s
where
  neg_mem : ∀ {a : A}, a ∈ s → -a ∈ s

/-- `s` is a subgroup: a set containing 1 and closed under multiplication and inverse. -/
class is_subgroup {G : Type u_1} [group G] (s : set G) 
extends is_submonoid s
where
  inv_mem : ∀ {a : G}, a ∈ s → a⁻¹ ∈ s

theorem is_subgroup.div_mem {G : Type u_1} [group G] {s : set G} [is_subgroup s] {x : G} {y : G} (hx : x ∈ s) (hy : y ∈ s) : x / y ∈ s := sorry

theorem additive.is_add_subgroup {G : Type u_1} [group G] (s : set G) [is_subgroup s] : is_add_subgroup s :=
  is_add_subgroup.mk is_subgroup.inv_mem

theorem additive.is_add_subgroup_iff {G : Type u_1} [group G] {s : set G} : is_add_subgroup s ↔ is_subgroup s := sorry

theorem multiplicative.is_subgroup {A : Type u_3} [add_group A] (s : set A) [is_add_subgroup s] : is_subgroup s :=
  is_subgroup.mk is_add_subgroup.neg_mem

theorem multiplicative.is_subgroup_iff {A : Type u_3} [add_group A] {s : set A} : is_subgroup s ↔ is_add_subgroup s := sorry

/-- The group structure on a subgroup coerced to a type. -/
def subtype.group {G : Type u_1} [group G] {s : set G} [is_subgroup s] : group ↥s :=
  group.mk monoid.mul sorry monoid.one sorry sorry (fun (x : ↥s) => { val := ↑x⁻¹, property := sorry })
    (fun (x y : ↥s) => { val := ↑x / ↑y, property := sorry }) sorry

/-- The commutative group structure on a commutative subgroup coerced to a type. -/
def subtype.comm_group {G : Type u_1} [comm_group G] {s : set G} [is_subgroup s] : comm_group ↥s :=
  comm_group.mk group.mul sorry group.one sorry sorry group.inv group.div sorry sorry

@[simp] theorem is_subgroup.coe_inv {G : Type u_1} [group G] {s : set G} [is_subgroup s] (a : ↥s) : ↑(a⁻¹) = (↑a⁻¹) :=
  rfl

@[simp] theorem is_subgroup.coe_gpow {G : Type u_1} [group G] {s : set G} [is_subgroup s] (a : ↥s) (n : ℤ) : ↑(a ^ n) = ↑a ^ n := sorry

@[simp] theorem is_add_subgroup.gsmul_coe {A : Type u_3} [add_group A] {s : set A} [is_add_subgroup s] (a : ↥s) (n : ℤ) : ↑(n •ℤ a) = n •ℤ ↑a := sorry

theorem is_add_subgroup.of_add_neg {G : Type u_1} [add_group G] (s : set G) (one_mem : 0 ∈ s) (div_mem : ∀ {a b : G}, a ∈ s → b ∈ s → a + -b ∈ s) : is_add_subgroup s := sorry

theorem is_add_subgroup.of_sub {A : Type u_3} [add_group A] (s : set A) (zero_mem : 0 ∈ s) (sub_mem : ∀ {a b : A}, a ∈ s → b ∈ s → a - b ∈ s) : is_add_subgroup s := sorry

protected instance is_add_subgroup.inter {G : Type u_1} [add_group G] (s₁ : set G) (s₂ : set G) [is_add_subgroup s₁] [is_add_subgroup s₂] : is_add_subgroup (s₁ ∩ s₂) :=
  is_add_subgroup.mk
    fun (x : G) (hx : x ∈ s₁ ∩ s₂) =>
      { left := is_add_subgroup.neg_mem (and.left hx), right := is_add_subgroup.neg_mem (and.right hx) }

protected instance is_add_subgroup.Inter {G : Type u_1} [add_group G] {ι : Sort u_2} (s : ι → set G) [h : ∀ (y : ι), is_add_subgroup (s y)] : is_add_subgroup (set.Inter s) :=
  is_add_subgroup.mk
    fun (x : G) (h_1 : x ∈ set.Inter s) =>
      iff.mpr set.mem_Inter fun (y : ι) => is_add_subgroup.neg_mem (iff.mp set.mem_Inter h_1 y)

theorem is_add_subgroup_Union_of_directed {G : Type u_1} [add_group G] {ι : Type u_2} [hι : Nonempty ι] (s : ι → set G) [∀ (i : ι), is_add_subgroup (s i)] (directed : ∀ (i j : ι), ∃ (k : ι), s i ⊆ s k ∧ s j ⊆ s k) : is_add_subgroup (set.Union fun (i : ι) => s i) := sorry

def gpowers {G : Type u_1} [group G] (x : G) : set G :=
  set.range (pow x)

def gmultiples {A : Type u_3} [add_group A] (x : A) : set A :=
  set.range fun (i : ℤ) => i •ℤ x

protected instance gpowers.is_subgroup {G : Type u_1} [group G] (x : G) : is_subgroup (gpowers x) :=
  is_subgroup.mk fun (x₀ : G) (_x : x₀ ∈ gpowers x) => sorry

protected instance gmultiples.is_add_subgroup {A : Type u_3} [add_group A] (x : A) : is_add_subgroup (gmultiples x) :=
  iff.mp multiplicative.is_subgroup_iff (gpowers.is_subgroup x)

theorem is_subgroup.gpow_mem {G : Type u_1} [group G] {a : G} {s : set G} [is_subgroup s] (h : a ∈ s) {i : ℤ} : a ^ i ∈ s :=
  int.cases_on i (fun (i : ℕ) => idRhs (a ^ i ∈ s) (is_submonoid.pow_mem h))
    fun (i : ℕ) => idRhs (a ^ Nat.succ i⁻¹ ∈ s) (is_subgroup.inv_mem (is_submonoid.pow_mem h))

theorem is_add_subgroup.gsmul_mem {A : Type u_3} [add_group A] {a : A} {s : set A} [is_add_subgroup s] : a ∈ s → ∀ {i : ℤ}, i •ℤ a ∈ s :=
  is_subgroup.gpow_mem

theorem gpowers_subset {G : Type u_1} [group G] {a : G} {s : set G} [is_subgroup s] (h : a ∈ s) : gpowers a ⊆ s := sorry

theorem gmultiples_subset {A : Type u_3} [add_group A] {a : A} {s : set A} [is_add_subgroup s] (h : a ∈ s) : gmultiples a ⊆ s :=
  gpowers_subset h

theorem mem_gpowers {G : Type u_1} [group G] {a : G} : a ∈ gpowers a := sorry

theorem mem_gmultiples {A : Type u_3} [add_group A] {a : A} : a ∈ gmultiples a := sorry

namespace is_subgroup


theorem inv_mem_iff {G : Type u_1} {a : G} [group G] (s : set G) [is_subgroup s] : a⁻¹ ∈ s ↔ a ∈ s := sorry

theorem Mathlib.is_add_subgroup.add_mem_cancel_right {G : Type u_1} {a : G} {b : G} [add_group G] (s : set G) [is_add_subgroup s] (h : a ∈ s) : b + a ∈ s ↔ b ∈ s := sorry

theorem Mathlib.is_add_subgroup.add_mem_cancel_left {G : Type u_1} {a : G} {b : G} [add_group G] (s : set G) [is_add_subgroup s] (h : a ∈ s) : a + b ∈ s ↔ b ∈ s := sorry

end is_subgroup


class normal_add_subgroup {A : Type u_3} [add_group A] (s : set A) 
extends is_add_subgroup s
where
  normal : ∀ (n : A), n ∈ s → ∀ (g : A), g + n + -g ∈ s

class normal_subgroup {G : Type u_1} [group G] (s : set G) 
extends is_subgroup s
where
  normal : ∀ (n : G), n ∈ s → ∀ (g : G), g * n * (g⁻¹) ∈ s

theorem normal_add_subgroup_of_add_comm_group {G : Type u_1} [add_comm_group G] (s : set G) [hs : is_add_subgroup s] : normal_add_subgroup s := sorry

theorem additive.normal_add_subgroup {G : Type u_1} [group G] (s : set G) [normal_subgroup s] : normal_add_subgroup s :=
  normal_add_subgroup.mk normal_subgroup.normal

theorem additive.normal_add_subgroup_iff {G : Type u_1} [group G] {s : set G} : normal_add_subgroup s ↔ normal_subgroup s := sorry

theorem multiplicative.normal_subgroup {A : Type u_3} [add_group A] (s : set A) [normal_add_subgroup s] : normal_subgroup s :=
  normal_subgroup.mk normal_add_subgroup.normal

theorem multiplicative.normal_subgroup_iff {A : Type u_3} [add_group A] {s : set A} : normal_subgroup s ↔ normal_add_subgroup s := sorry

namespace is_subgroup


-- Normal subgroup properties

theorem mem_norm_comm {G : Type u_1} [group G] {s : set G} [normal_subgroup s] {a : G} {b : G} (hab : a * b ∈ s) : b * a ∈ s := sorry

theorem Mathlib.is_add_subgroup.mem_norm_comm_iff {G : Type u_1} [add_group G] {s : set G} [normal_add_subgroup s] {a : G} {b : G} : a + b ∈ s ↔ b + a ∈ s :=
  { mp := is_add_subgroup.mem_norm_comm, mpr := is_add_subgroup.mem_norm_comm }

/-- The trivial subgroup -/
def trivial (G : Type u_1) [group G] : set G :=
  singleton 1

@[simp] theorem Mathlib.is_add_subgroup.mem_trivial {G : Type u_1} [add_group G] {g : G} : g ∈ is_add_subgroup.trivial G ↔ g = 0 :=
  set.mem_singleton_iff

protected instance Mathlib.is_add_subgroup.trivial_normal {G : Type u_1} [add_group G] : normal_add_subgroup (is_add_subgroup.trivial G) := sorry

theorem Mathlib.is_add_subgroup.eq_trivial_iff {G : Type u_1} [add_group G] {s : set G} [is_add_subgroup s] : s = is_add_subgroup.trivial G ↔ ∀ (x : G), x ∈ s → x = 0 := sorry

protected instance univ_subgroup {G : Type u_1} [group G] : normal_subgroup set.univ :=
  normal_subgroup.mk
    (eq.mpr
      (id
        (Eq.trans
          (forall_congr_eq
            fun (n : G) =>
              Eq.trans
                (imp_congr_eq (propext ((fun {α : Type u_1} (x : α) => iff_true_intro (set.mem_univ x)) n))
                  (Eq.trans
                    (forall_congr_eq
                      fun (g : G) =>
                        propext ((fun {α : Type u_1} (x : α) => iff_true_intro (set.mem_univ x)) (g * n * (g⁻¹))))
                    (propext (forall_const G))))
                (propext (forall_prop_of_true True.intro)))
          (propext (forall_const G))))
      trivial)

def Mathlib.is_add_subgroup.add_center (G : Type u_1) [add_group G] : set G :=
  set_of fun (z : G) => ∀ (g : G), g + z = z + g

theorem mem_center {G : Type u_1} [group G] {a : G} : a ∈ center G ↔ ∀ (g : G), g * a = a * g :=
  iff.rfl

protected instance center_normal {G : Type u_1} [group G] : normal_subgroup (center G) := sorry

def Mathlib.is_add_subgroup.add_normalizer {G : Type u_1} [add_group G] (s : set G) : set G :=
  set_of fun (g : G) => ∀ (n : G), n ∈ s ↔ g + n + -g ∈ s

protected instance Mathlib.is_add_subgroup.normalizer_is_add_subgroup {G : Type u_1} [add_group G] (s : set G) : is_add_subgroup (is_add_subgroup.add_normalizer s) := sorry

theorem Mathlib.is_add_subgroup.subset_add_normalizer {G : Type u_1} [add_group G] (s : set G) [is_add_subgroup s] : s ⊆ is_add_subgroup.add_normalizer s := sorry

/-- Every subgroup is a normal subgroup of its normalizer -/
protected instance Mathlib.is_add_subgroup.add_normal_in_add_normalizer {G : Type u_1} [add_group G] (s : set G) [is_add_subgroup s] : normal_add_subgroup (subtype.val ⁻¹' s) :=
  normal_add_subgroup.mk
    fun (a : ↥(is_add_subgroup.add_normalizer s)) (ha : a ∈ subtype.val ⁻¹' s)
      (_x : ↥(is_add_subgroup.add_normalizer s)) => sorry

end is_subgroup


-- Homomorphism subgroups

namespace is_group_hom


def ker {G : Type u_1} {H : Type u_2} [group H] (f : G → H) : set G :=
  f ⁻¹' is_subgroup.trivial H

theorem Mathlib.is_add_group_hom.mem_ker {G : Type u_1} {H : Type u_2} [add_group H] (f : G → H) {x : G} : x ∈ is_add_group_hom.ker f ↔ f x = 0 :=
  is_add_subgroup.mem_trivial

theorem Mathlib.is_add_group_hom.zero_ker_neg {G : Type u_1} {H : Type u_2} [add_group G] [add_group H] (f : G → H) [is_add_group_hom f] {a : G} {b : G} (h : f (a + -b) = 0) : f a = f b := sorry

theorem one_ker_inv' {G : Type u_1} {H : Type u_2} [group G] [group H] (f : G → H) [is_group_hom f] {a : G} {b : G} (h : f (a⁻¹ * b) = 1) : f a = f b := sorry

theorem Mathlib.is_add_group_hom.neg_ker_zero {G : Type u_1} {H : Type u_2} [add_group G] [add_group H] (f : G → H) [is_add_group_hom f] {a : G} {b : G} (h : f a = f b) : f (a + -b) = 0 := sorry

theorem inv_ker_one' {G : Type u_1} {H : Type u_2} [group G] [group H] (f : G → H) [is_group_hom f] {a : G} {b : G} (h : f a = f b) : f (a⁻¹ * b) = 1 := sorry

theorem Mathlib.is_add_group_hom.zero_iff_ker_neg {G : Type u_1} {H : Type u_2} [add_group G] [add_group H] (f : G → H) [is_add_group_hom f] (a : G) (b : G) : f a = f b ↔ f (a + -b) = 0 :=
  { mp := is_add_group_hom.neg_ker_zero f, mpr := is_add_group_hom.zero_ker_neg f }

theorem one_iff_ker_inv' {G : Type u_1} {H : Type u_2} [group G] [group H] (f : G → H) [is_group_hom f] (a : G) (b : G) : f a = f b ↔ f (a⁻¹ * b) = 1 :=
  { mp := inv_ker_one' f, mpr := one_ker_inv' f }

theorem inv_iff_ker {G : Type u_1} {H : Type u_2} [group G] [group H] (f : G → H) [w : is_group_hom f] (a : G) (b : G) : f a = f b ↔ a * (b⁻¹) ∈ ker f :=
  eq.mpr (id (Eq._oldrec (Eq.refl (f a = f b ↔ a * (b⁻¹) ∈ ker f)) (propext (mem_ker f)))) (one_iff_ker_inv f a b)

theorem inv_iff_ker' {G : Type u_1} {H : Type u_2} [group G] [group H] (f : G → H) [w : is_group_hom f] (a : G) (b : G) : f a = f b ↔ a⁻¹ * b ∈ ker f :=
  eq.mpr (id (Eq._oldrec (Eq.refl (f a = f b ↔ a⁻¹ * b ∈ ker f)) (propext (mem_ker f)))) (one_iff_ker_inv' f a b)

protected instance Mathlib.is_add_group_hom.image_add_subgroup {G : Type u_1} {H : Type u_2} [add_group G] [add_group H] (f : G → H) [is_add_group_hom f] (s : set G) [is_add_subgroup s] : is_add_subgroup (f '' s) :=
  is_add_subgroup.mk fun (a : H) (_x : a ∈ f '' s) => sorry

protected instance range_subgroup {G : Type u_1} {H : Type u_2} [group G] [group H] (f : G → H) [is_group_hom f] : is_subgroup (set.range f) :=
  set.image_univ ▸ is_group_hom.image_subgroup f set.univ

protected instance preimage {G : Type u_1} {H : Type u_2} [group G] [group H] (f : G → H) [is_group_hom f] (s : set H) [is_subgroup s] : is_subgroup (f ⁻¹' s) :=
  is_subgroup.mk
    (eq.mpr
      (id
        (Eq.trans
          (forall_congr_eq
            fun (a : G) =>
              Eq.trans
                (imp_congr_ctx_eq (propext set.mem_preimage)
                  fun (_h : f a ∈ s) =>
                    Eq.trans
                      (Eq.trans (propext set.mem_preimage)
                        ((fun (ᾰ ᾰ_1 : H) (e_2 : ᾰ = ᾰ_1) (ᾰ_2 ᾰ_3 : set H) (e_3 : ᾰ_2 = ᾰ_3) =>
                            congr (congr_arg has_mem.mem e_2) e_3)
                          (f (a⁻¹)) (f a⁻¹) (map_inv f a) s s (Eq.refl s)))
                      (propext
                        ((fun [c : is_subgroup s] {a : H} (ᾰ : a ∈ s) => iff_true_intro (is_subgroup.inv_mem ᾰ))
                          (iff.mpr (iff_true_intro _h) True.intro))))
                (propext forall_true_iff))
          (propext (forall_const G))))
      trivial)

protected instance preimage_normal {G : Type u_1} {H : Type u_2} [group G] [group H] (f : G → H) [is_group_hom f] (s : set H) [normal_subgroup s] : normal_subgroup (f ⁻¹' s) := sorry

protected instance normal_subgroup_ker {G : Type u_1} {H : Type u_2} [group G] [group H] (f : G → H) [is_group_hom f] : normal_subgroup (ker f) :=
  is_group_hom.preimage_normal f (is_subgroup.trivial H)

theorem Mathlib.is_add_group_hom.injective_of_trivial_ker {G : Type u_1} {H : Type u_2} [add_group G] [add_group H] (f : G → H) [is_add_group_hom f] (h : is_add_group_hom.ker f = is_add_subgroup.trivial G) : function.injective f := sorry

theorem trivial_ker_of_injective {G : Type u_1} {H : Type u_2} [group G] [group H] (f : G → H) [is_group_hom f] (h : function.injective f) : ker f = is_subgroup.trivial G := sorry

theorem Mathlib.is_add_group_hom.injective_iff_trivial_ker {G : Type u_1} {H : Type u_2} [add_group G] [add_group H] (f : G → H) [is_add_group_hom f] : function.injective f ↔ is_add_group_hom.ker f = is_add_subgroup.trivial G :=
  { mp := is_add_group_hom.trivial_ker_of_injective f, mpr := is_add_group_hom.injective_of_trivial_ker f }

theorem Mathlib.is_add_group_hom.trivial_ker_iff_eq_zero {G : Type u_1} {H : Type u_2} [add_group G] [add_group H] (f : G → H) [is_add_group_hom f] : is_add_group_hom.ker f = is_add_subgroup.trivial G ↔ ∀ (x : G), f x = 0 → x = 0 := sorry

end is_group_hom


protected instance subtype_val.is_add_group_hom {G : Type u_1} [add_group G] {s : set G} [is_add_subgroup s] : is_add_group_hom subtype.val :=
  is_add_group_hom.mk

protected instance coe.is_add_group_hom {G : Type u_1} [add_group G] {s : set G} [is_add_subgroup s] : is_add_group_hom coe :=
  is_add_group_hom.mk

protected instance subtype_mk.is_group_hom {G : Type u_1} {H : Type u_2} [group G] [group H] {s : set G} [is_subgroup s] (f : H → G) [is_group_hom f] (h : ∀ (x : H), f x ∈ s) : is_group_hom fun (x : H) => { val := f x, property := h x } :=
  is_group_hom.mk

protected instance set_inclusion.is_group_hom {G : Type u_1} [group G] {s : set G} {t : set G} [is_subgroup s] [is_subgroup t] (h : s ⊆ t) : is_group_hom (set.inclusion h) :=
  subtype_mk.is_group_hom (fun (x : ↥s) => ↑x) fun (x : ↥s) => set.inclusion._proof_1 h x

/-- `subtype.val : set.range f → H` as a monoid homomorphism, when `f` is a monoid homomorphism. -/
def monoid_hom.range_subtype_val {G : Type u_1} {H : Type u_2} [monoid G] [monoid H] (f : G →* H) : ↥(set.range ⇑f) →* H :=
  monoid_hom.of subtype.val

/-- `set.range_factorization f : G → set.range f` as a monoid homomorphism, when `f` is a monoid
homomorphism. -/
def add_monoid_hom.range_factorization {G : Type u_1} {H : Type u_2} [add_monoid G] [add_monoid H] (f : G →+ H) : G →+ ↥(set.range ⇑f) :=
  add_monoid_hom.mk (set.range_factorization ⇑f) sorry sorry

namespace add_group


inductive in_closure {A : Type u_3} [add_group A] (s : set A) : A → Prop
where
| basic : ∀ {a : A}, a ∈ s → in_closure s a
| zero : in_closure s 0
| neg : ∀ {a : A}, in_closure s a → in_closure s (-a)
| add : ∀ {a b : A}, in_closure s a → in_closure s b → in_closure s (a + b)

end add_group


namespace group


inductive in_closure {G : Type u_1} [group G] (s : set G) : G → Prop
where
| basic : ∀ {a : G}, a ∈ s → in_closure s a
| one : in_closure s 1
| inv : ∀ {a : G}, in_closure s a → in_closure s (a⁻¹)
| mul : ∀ {a b : G}, in_closure s a → in_closure s b → in_closure s (a * b)

/-- `group.closure s` is the subgroup closed over `s`, i.e. the smallest subgroup containg s. -/
def Mathlib.add_group.closure {G : Type u_1} [add_group G] (s : set G) : set G :=
  set_of fun (a : G) => add_group.in_closure s a

theorem Mathlib.add_group.mem_closure {G : Type u_1} [add_group G] {s : set G} {a : G} : a ∈ s → a ∈ add_group.closure s :=
  add_group.in_closure.basic

protected instance closure.is_subgroup {G : Type u_1} [group G] (s : set G) : is_subgroup (closure s) :=
  is_subgroup.mk fun (a : G) => in_closure.inv

theorem Mathlib.add_group.subset_closure {G : Type u_1} [add_group G] {s : set G} : s ⊆ add_group.closure s :=
  fun (a : G) => add_group.mem_closure

theorem Mathlib.add_group.closure_subset {G : Type u_1} [add_group G] {s : set G} {t : set G} [is_add_subgroup t] (h : s ⊆ t) : add_group.closure s ⊆ t := sorry

theorem Mathlib.add_group.closure_subset_iff {G : Type u_1} [add_group G] (s : set G) (t : set G) [is_add_subgroup t] : add_group.closure s ⊆ t ↔ s ⊆ t :=
  { mp := fun (h : add_group.closure s ⊆ t) (b : G) (ha : b ∈ s) => h (add_group.mem_closure ha),
    mpr := fun (h : s ⊆ t) (b : G) (ha : b ∈ add_group.closure s) => add_group.closure_subset h ha }

theorem Mathlib.add_group.closure_mono {G : Type u_1} [add_group G] {s : set G} {t : set G} (h : s ⊆ t) : add_group.closure s ⊆ add_group.closure t :=
  add_group.closure_subset (set.subset.trans h add_group.subset_closure)

@[simp] theorem closure_subgroup {G : Type u_1} [group G] (s : set G) [is_subgroup s] : closure s = s :=
  set.subset.antisymm (closure_subset (set.subset.refl s)) subset_closure

theorem Mathlib.add_group.exists_list_of_mem_closure {G : Type u_1} [add_group G] {s : set G} {a : G} (h : a ∈ add_group.closure s) : ∃ (l : List G), (∀ (x : G), x ∈ l → x ∈ s ∨ -x ∈ s) ∧ list.sum l = a := sorry

theorem Mathlib.add_group.image_closure {G : Type u_1} {H : Type u_2} [add_group G] [add_group H] (f : G → H) [is_add_group_hom f] (s : set G) : f '' add_group.closure s = add_group.closure (f '' s) := sorry

theorem Mathlib.add_group.mclosure_subset {G : Type u_1} [add_group G] {s : set G} : add_monoid.closure s ⊆ add_group.closure s :=
  add_monoid.closure_subset add_group.subset_closure

theorem Mathlib.add_group.mclosure_neg_subset {G : Type u_1} [add_group G] {s : set G} : add_monoid.closure (Neg.neg ⁻¹' s) ⊆ add_group.closure s :=
  add_monoid.closure_subset
    fun (x : G) (hx : x ∈ Neg.neg ⁻¹' s) => neg_neg x ▸ is_add_subgroup.neg_mem (add_group.subset_closure hx)

theorem Mathlib.add_group.closure_eq_mclosure {G : Type u_1} [add_group G] {s : set G} : add_group.closure s = add_monoid.closure (s ∪ Neg.neg ⁻¹' s) := sorry

theorem Mathlib.add_group.mem_closure_union_iff {G : Type u_1} [add_comm_group G] {s : set G} {t : set G} {x : G} : x ∈ add_group.closure (s ∪ t) ↔
  ∃ (y : G), ∃ (H : y ∈ add_group.closure s), ∃ (z : G), ∃ (H : z ∈ add_group.closure t), y + z = x := sorry

theorem gpowers_eq_closure {G : Type u_1} [group G] {a : G} : gpowers a = closure (singleton a) := sorry

end group


namespace is_subgroup


theorem Mathlib.is_add_subgroup.trivial_eq_closure {G : Type u_1} [add_group G] : is_add_subgroup.trivial G = add_group.closure ∅ := sorry

end is_subgroup


/-The normal closure of a set s is the subgroup closure of all the conjugates of
elements of s. It is the smallest normal subgroup containing s. -/

namespace group


theorem conjugates_subset {G : Type u_1} [group G] {t : set G} [normal_subgroup t] {a : G} (h : a ∈ t) : conjugates a ⊆ t := sorry

theorem conjugates_of_set_subset' {G : Type u_1} [group G] {s : set G} {t : set G} [normal_subgroup t] (h : s ⊆ t) : conjugates_of_set s ⊆ t :=
  set.bUnion_subset fun (x : G) (H : x ∈ s) => conjugates_subset (h H)

/-- The normal closure of a set s is the subgroup closure of all the conjugates of
elements of s. It is the smallest normal subgroup containing s. -/
def normal_closure {G : Type u_1} [group G] (s : set G) : set G :=
  closure (conjugates_of_set s)

theorem conjugates_of_set_subset_normal_closure {G : Type u_1} {s : set G} [group G] : conjugates_of_set s ⊆ normal_closure s :=
  subset_closure

theorem subset_normal_closure {G : Type u_1} {s : set G} [group G] : s ⊆ normal_closure s :=
  set.subset.trans subset_conjugates_of_set conjugates_of_set_subset_normal_closure

/-- The normal closure of a set is a subgroup. -/
protected instance normal_closure.is_subgroup {G : Type u_1} [group G] (s : set G) : is_subgroup (normal_closure s) :=
  closure.is_subgroup (conjugates_of_set s)

/-- The normal closure of s is a normal subgroup. -/
protected instance normal_closure.is_normal {G : Type u_1} {s : set G} [group G] : normal_subgroup (normal_closure s) := sorry

/-- The normal closure of s is the smallest normal subgroup containing s. -/
theorem normal_closure_subset {G : Type u_1} [group G] {s : set G} {t : set G} [normal_subgroup t] (h : s ⊆ t) : normal_closure s ⊆ t := sorry

theorem normal_closure_subset_iff {G : Type u_1} [group G] {s : set G} {t : set G} [normal_subgroup t] : s ⊆ t ↔ normal_closure s ⊆ t :=
  { mp := normal_closure_subset, mpr := set.subset.trans subset_normal_closure }

theorem normal_closure_mono {G : Type u_1} [group G] {s : set G} {t : set G} : s ⊆ t → normal_closure s ⊆ normal_closure t :=
  fun (h : s ⊆ t) => normal_closure_subset (set.subset.trans h subset_normal_closure)

end group


class simple_group (G : Type u_4) [group G] 
where
  simple : ∀ (N : set G) [_inst_1_1 : normal_subgroup N], N = is_subgroup.trivial G ∨ N = set.univ

class simple_add_group (A : Type u_4) [add_group A] 
where
  simple : ∀ (N : set A) [_inst_1_1 : normal_add_subgroup N], N = is_add_subgroup.trivial A ∨ N = set.univ

theorem additive.simple_add_group_iff {G : Type u_1} [group G] : simple_add_group (additive G) ↔ simple_group G := sorry

protected instance additive.simple_add_group {G : Type u_1} [group G] [simple_group G] : simple_add_group (additive G) :=
  iff.mpr additive.simple_add_group_iff _inst_2

theorem multiplicative.simple_group_iff {A : Type u_3} [add_group A] : simple_group (multiplicative A) ↔ simple_add_group A := sorry

protected instance multiplicative.simple_group {A : Type u_3} [add_group A] [simple_add_group A] : simple_group (multiplicative A) :=
  iff.mpr multiplicative.simple_group_iff _inst_2

theorem simple_add_group_of_surjective {G : Type u_1} {H : Type u_2} [add_group G] [add_group H] [simple_add_group G] (f : G → H) [is_add_group_hom f] (hf : function.surjective f) : simple_add_group H := sorry

/-- Create a bundled subgroup from a set `s` and `[is_subroup s]`. -/
def subgroup.of {G : Type u_1} [group G] (s : set G) [h : is_subgroup s] : subgroup G :=
  subgroup.mk s sorry sorry is_subgroup.inv_mem

protected instance subgroup.is_subgroup {G : Type u_1} [group G] (K : subgroup G) : is_subgroup ↑K :=
  is_subgroup.mk (subgroup.inv_mem' K)

protected instance subgroup.of_normal {G : Type u_1} [group G] (s : set G) [h : is_subgroup s] [n : normal_subgroup s] : subgroup.normal (subgroup.of s) :=
  subgroup.normal.mk normal_subgroup.normal

