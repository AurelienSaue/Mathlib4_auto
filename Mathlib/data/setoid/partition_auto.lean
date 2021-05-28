/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Bryan Gin-ge Chen
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.setoid.basic
import Mathlib.data.set.lattice
import PostPort

universes u_1 

namespace Mathlib

/-!
# Equivalence relations: partitions

This file comprises properties of equivalence relations viewed as partitions.

## Tags

setoid, equivalence, iseqv, relation, equivalence relation, partition, equivalence class
-/

namespace setoid


/-- If x ∈ α is in 2 elements of a set of sets partitioning α, those 2 sets are equal. -/
theorem eq_of_mem_eqv_class {α : Type u_1} {c : set (set α)} (H : ∀ (a : α), exists_unique fun (b : set α) => exists_unique fun (H : b ∈ c) => a ∈ b) {x : α} {b : set α} {b' : set α} (hc : b ∈ c) (hb : x ∈ b) (hc' : b' ∈ c) (hb' : x ∈ b') : b = b' :=
  exists_unique.unique2 (H x) hc hb hc' hb'

/-- Makes an equivalence relation from a set of sets partitioning α. -/
def mk_classes {α : Type u_1} (c : set (set α)) (H : ∀ (a : α), exists_unique fun (b : set α) => exists_unique fun (H : b ∈ c) => a ∈ b) : setoid α :=
  mk (fun (x y : α) => ∀ (s : set α), s ∈ c → x ∈ s → y ∈ s) sorry

/-- Makes the equivalence classes of an equivalence relation. -/
def classes {α : Type u_1} (r : setoid α) : set (set α) :=
  set_of fun (s : set α) => ∃ (y : α), s = set_of fun (x : α) => rel r x y

theorem mem_classes {α : Type u_1} (r : setoid α) (y : α) : (set_of fun (x : α) => rel r x y) ∈ classes r :=
  Exists.intro y rfl

/-- Two equivalence relations are equal iff all their equivalence classes are equal. -/
theorem eq_iff_classes_eq {α : Type u_1} {r₁ : setoid α} {r₂ : setoid α} : r₁ = r₂ ↔ ∀ (x : α), (set_of fun (y : α) => rel r₁ x y) = set_of fun (y : α) => rel r₂ x y := sorry

theorem rel_iff_exists_classes {α : Type u_1} (r : setoid α) {x : α} {y : α} : rel r x y ↔ ∃ (c : set α), ∃ (H : c ∈ classes r), x ∈ c ∧ y ∈ c := sorry

/-- Two equivalence relations are equal iff their equivalence classes are equal. -/
theorem classes_inj {α : Type u_1} {r₁ : setoid α} {r₂ : setoid α} : r₁ = r₂ ↔ classes r₁ = classes r₂ := sorry

/-- The empty set is not an equivalence class. -/
theorem empty_not_mem_classes {α : Type u_1} {r : setoid α} : ¬∅ ∈ classes r := sorry

/-- Equivalence classes partition the type. -/
theorem classes_eqv_classes {α : Type u_1} {r : setoid α} (a : α) : exists_unique fun (b : set α) => exists_unique fun (H : b ∈ classes r) => a ∈ b := sorry

/-- If x ∈ α is in 2 equivalence classes, the equivalence classes are equal. -/
theorem eq_of_mem_classes {α : Type u_1} {r : setoid α} {x : α} {b : set α} (hc : b ∈ classes r) (hb : x ∈ b) {b' : set α} (hc' : b' ∈ classes r) (hb' : x ∈ b') : b = b' :=
  eq_of_mem_eqv_class classes_eqv_classes hc hb hc' hb'

/-- The elements of a set of sets partitioning α are the equivalence classes of the
    equivalence relation defined by the set of sets. -/
theorem eq_eqv_class_of_mem {α : Type u_1} {c : set (set α)} (H : ∀ (a : α), exists_unique fun (b : set α) => exists_unique fun (H : b ∈ c) => a ∈ b) {s : set α} {y : α} (hs : s ∈ c) (hy : y ∈ s) : s = set_of fun (x : α) => rel (mk_classes c H) x y := sorry

/-- The equivalence classes of the equivalence relation defined by a set of sets
    partitioning α are elements of the set of sets. -/
theorem eqv_class_mem {α : Type u_1} {c : set (set α)} (H : ∀ (a : α), exists_unique fun (b : set α) => exists_unique fun (H : b ∈ c) => a ∈ b) {y : α} : (set_of fun (x : α) => rel (mk_classes c H) x y) ∈ c :=
  exists_unique.elim2 (H y)
    fun (b : set α) (hc : b ∈ c) (hy : y ∈ b) (hb : ∀ (y_1 : set α), y_1 ∈ c → y ∈ y_1 → y_1 = b) =>
      eq_eqv_class_of_mem H hc hy ▸ hc

/-- Distinct elements of a set of sets partitioning α are disjoint. -/
theorem eqv_classes_disjoint {α : Type u_1} {c : set (set α)} (H : ∀ (a : α), exists_unique fun (b : set α) => exists_unique fun (H : b ∈ c) => a ∈ b) : set.pairwise_disjoint c := sorry

/-- A set of disjoint sets covering α partition α (classical). -/
theorem eqv_classes_of_disjoint_union {α : Type u_1} {c : set (set α)} (hu : ⋃₀c = set.univ) (H : set.pairwise_disjoint c) (a : α) : exists_unique fun (b : set α) => exists_unique fun (H : b ∈ c) => a ∈ b := sorry

/-- Makes an equivalence relation from a set of disjoints sets covering α. -/
def setoid_of_disjoint_union {α : Type u_1} {c : set (set α)} (hu : ⋃₀c = set.univ) (H : set.pairwise_disjoint c) : setoid α :=
  mk_classes c (eqv_classes_of_disjoint_union hu H)

/-- The equivalence relation made from the equivalence classes of an equivalence
    relation r equals r. -/
theorem mk_classes_classes {α : Type u_1} (r : setoid α) : mk_classes (classes r) classes_eqv_classes = r := sorry

@[simp] theorem sUnion_classes {α : Type u_1} (r : setoid α) : ⋃₀classes r = set.univ :=
  set.eq_univ_of_forall
    fun (x : α) =>
      iff.mpr set.mem_sUnion (Exists.intro (set_of fun (y : α) => rel r y x) (Exists.intro (Exists.intro x rfl) (refl x)))

/-- A collection `c : set (set α)` of sets is a partition of `α` into pairwise
disjoint sets if `∅ ∉ c` and each element `a : α` belongs to a unique set `b ∈ c`. -/
def is_partition {α : Type u_1} (c : set (set α))  :=
  ¬∅ ∈ c ∧ ∀ (a : α), exists_unique fun (b : set α) => exists_unique fun (H : b ∈ c) => a ∈ b

/-- A partition of `α` does not contain the empty set. -/
theorem nonempty_of_mem_partition {α : Type u_1} {c : set (set α)} (hc : is_partition c) {s : set α} (h : s ∈ c) : set.nonempty s :=
  iff.mp set.ne_empty_iff_nonempty fun (hs0 : s = ∅) => and.left hc (hs0 ▸ h)

theorem is_partition_classes {α : Type u_1} (r : setoid α) : is_partition (classes r) :=
  { left := empty_not_mem_classes, right := classes_eqv_classes }

theorem is_partition.pairwise_disjoint {α : Type u_1} {c : set (set α)} (hc : is_partition c) : set.pairwise_disjoint c :=
  eqv_classes_disjoint (and.right hc)

theorem is_partition.sUnion_eq_univ {α : Type u_1} {c : set (set α)} (hc : is_partition c) : ⋃₀c = set.univ := sorry

/-- All elements of a partition of α are the equivalence class of some y ∈ α. -/
theorem exists_of_mem_partition {α : Type u_1} {c : set (set α)} (hc : is_partition c) {s : set α} (hs : s ∈ c) : ∃ (y : α), s = set_of fun (x : α) => rel (mk_classes c (and.right hc)) x y := sorry

/-- The equivalence classes of the equivalence relation defined by a partition of α equal
    the original partition. -/
theorem classes_mk_classes {α : Type u_1} (c : set (set α)) (hc : is_partition c) : classes (mk_classes c (and.right hc)) = c := sorry

/-- Defining `≤` on partitions as the `≤` defined on their induced equivalence relations. -/
protected instance partition.le {α : Type u_1} : HasLessEq (Subtype is_partition) :=
  { LessEq := fun (x y : Subtype is_partition) => mk_classes (subtype.val x) sorry ≤ mk_classes (subtype.val y) sorry }

/-- Defining a partial order on partitions as the partial order on their induced
    equivalence relations. -/
protected instance partition.partial_order {α : Type u_1} : partial_order (Subtype is_partition) :=
  partial_order.mk LessEq (fun (x y : Subtype is_partition) => x ≤ y ∧ ¬y ≤ x) sorry sorry sorry

/-- The order-preserving bijection between equivalence relations and partitions of sets. -/
def partition.rel_iso (α : Type u_1) : setoid α ≃o Subtype is_partition :=
  rel_iso.mk
    (equiv.mk (fun (r : setoid α) => { val := classes r, property := sorry })
      (fun (x : Subtype is_partition) => mk_classes (subtype.val x) sorry) mk_classes_classes sorry)
    sorry

/-- A complete lattice instance for partitions; there is more infrastructure for the
    equivalent complete lattice on equivalence relations. -/
protected instance partition.complete_lattice {α : Type u_1} : complete_lattice (Subtype is_partition) :=
  galois_insertion.lift_complete_lattice (rel_iso.to_galois_insertion (partition.rel_iso α))

