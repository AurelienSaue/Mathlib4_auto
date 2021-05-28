/-
Copyright (c) 2018 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.module.pi
import Mathlib.algebra.big_operators.basic
import Mathlib.PostPort

universes u u_1 

namespace Mathlib

/-!
# Basic properties of holors

Holors are indexed collections of tensor coefficients. Confusingly,
they are often called tensors in physics and in the neural network
community.

A holor is simply a multidimensional array of values. The size of a
holor is specified by a `list ℕ`, whose length is called the dimension
of the holor.

The tensor product of `x₁ : holor α ds₁` and `x₂ : holor α ds₂` is the
holor given by `(x₁ ⊗ x₂) (i₁ ++ i₂) = x₁ i₁ * x₂ i₂`. A holor is "of
rank at most 1" if it is a tensor product of one-dimensional holors.
The CP rank of a holor `x` is the smallest N such that `x` is the sum
of N holors of rank at most 1.

Based on the tensor library found in <https://www.isa-afp.org/entries/Deep_Learning.html>

## References

* <https://en.wikipedia.org/wiki/Tensor_rank_decomposition>
-/

/-- `holor_index ds` is the type of valid index tuples to identify an entry of a holor of dimensions `ds` -/
def holor_index (ds : List ℕ)  :=
  Subtype fun (is : List ℕ) => list.forall₂ Less is ds

namespace holor_index


def take {ds₂ : List ℕ} {ds₁ : List ℕ} : holor_index (ds₁ ++ ds₂) → holor_index ds₁ :=
  sorry

def drop {ds₂ : List ℕ} {ds₁ : List ℕ} : holor_index (ds₁ ++ ds₂) → holor_index ds₂ :=
  sorry

theorem cast_type {ds₁ : List ℕ} {ds₂ : List ℕ} (is : List ℕ) (eq : ds₁ = ds₂) (h : list.forall₂ Less is ds₁) : subtype.val (cast (congr_arg holor_index eq) { val := is, property := h }) = is :=
  eq.drec (Eq.refl (subtype.val (cast (congr_arg holor_index (Eq.refl ds₁)) { val := is, property := h }))) eq

def assoc_right {ds₁ : List ℕ} {ds₂ : List ℕ} {ds₃ : List ℕ} : holor_index (ds₁ ++ ds₂ ++ ds₃) → holor_index (ds₁ ++ (ds₂ ++ ds₃)) :=
  cast sorry

def assoc_left {ds₁ : List ℕ} {ds₂ : List ℕ} {ds₃ : List ℕ} : holor_index (ds₁ ++ (ds₂ ++ ds₃)) → holor_index (ds₁ ++ ds₂ ++ ds₃) :=
  cast sorry

theorem take_take {ds₁ : List ℕ} {ds₂ : List ℕ} {ds₃ : List ℕ} (t : holor_index (ds₁ ++ ds₂ ++ ds₃)) : take (assoc_right t) = take (take t) := sorry

theorem drop_take {ds₁ : List ℕ} {ds₂ : List ℕ} {ds₃ : List ℕ} (t : holor_index (ds₁ ++ ds₂ ++ ds₃)) : take (drop (assoc_right t)) = drop (take t) := sorry

theorem drop_drop {ds₁ : List ℕ} {ds₂ : List ℕ} {ds₃ : List ℕ} (t : holor_index (ds₁ ++ ds₂ ++ ds₃)) : drop (drop (assoc_right t)) = drop t := sorry

end holor_index


/-- Holor (indexed collections of tensor coefficients) -/
def holor (α : Type u) (ds : List ℕ)  :=
  holor_index ds → α

namespace holor


protected instance inhabited {α : Type} {ds : List ℕ} [Inhabited α] : Inhabited (holor α ds) :=
  { default := fun (t : holor_index ds) => Inhabited.default }

protected instance has_zero {α : Type} {ds : List ℕ} [HasZero α] : HasZero (holor α ds) :=
  { zero := fun (t : holor_index ds) => 0 }

protected instance has_add {α : Type} {ds : List ℕ} [Add α] : Add (holor α ds) :=
  { add := fun (x y : holor α ds) (t : holor_index ds) => x t + y t }

protected instance has_neg {α : Type} {ds : List ℕ} [Neg α] : Neg (holor α ds) :=
  { neg := fun (a : holor α ds) (t : holor_index ds) => -a t }

protected instance add_semigroup {α : Type} {ds : List ℕ} [add_semigroup α] : add_semigroup (holor α ds) :=
  add_semigroup.mk (fun (ᾰ ᾰ_1 : holor α ds) => id fun (ᾰ_2 : holor_index ds) => add_semigroup.add (ᾰ ᾰ_2) (ᾰ_1 ᾰ_2))
    sorry

protected instance add_comm_semigroup {α : Type} {ds : List ℕ} [add_comm_semigroup α] : add_comm_semigroup (holor α ds) :=
  add_comm_semigroup.mk
    (fun (ᾰ ᾰ_1 : holor α ds) => id fun (ᾰ_2 : holor_index ds) => add_comm_semigroup.add (ᾰ ᾰ_2) (ᾰ_1 ᾰ_2)) sorry sorry

protected instance add_monoid {α : Type} {ds : List ℕ} [add_monoid α] : add_monoid (holor α ds) :=
  add_monoid.mk (fun (ᾰ ᾰ_1 : holor α ds) => id fun (ᾰ_2 : holor_index ds) => add_monoid.add (ᾰ ᾰ_2) (ᾰ_1 ᾰ_2)) sorry
    (id fun (ᾰ : holor_index ds) => add_monoid.zero) sorry sorry

protected instance add_comm_monoid {α : Type} {ds : List ℕ} [add_comm_monoid α] : add_comm_monoid (holor α ds) :=
  add_comm_monoid.mk (fun (ᾰ ᾰ_1 : holor α ds) => id fun (ᾰ_2 : holor_index ds) => add_comm_monoid.add (ᾰ ᾰ_2) (ᾰ_1 ᾰ_2))
    sorry (id fun (ᾰ : holor_index ds) => add_comm_monoid.zero) sorry sorry sorry

protected instance add_group {α : Type} {ds : List ℕ} [add_group α] : add_group (holor α ds) :=
  add_group.mk (fun (ᾰ ᾰ_1 : holor α ds) => id fun (ᾰ_2 : holor_index ds) => add_group.add (ᾰ ᾰ_2) (ᾰ_1 ᾰ_2)) sorry
    (id fun (ᾰ : holor_index ds) => add_group.zero) sorry sorry
    (fun (ᾰ : holor α ds) => id fun (ᾰ_1 : holor_index ds) => add_group.neg (ᾰ ᾰ_1))
    (fun (ᾰ ᾰ_1 : holor α ds) => id fun (ᾰ_2 : holor_index ds) => add_group.sub (ᾰ ᾰ_2) (ᾰ_1 ᾰ_2)) sorry

protected instance add_comm_group {α : Type} {ds : List ℕ} [add_comm_group α] : add_comm_group (holor α ds) :=
  add_comm_group.mk (fun (ᾰ ᾰ_1 : holor α ds) => id fun (ᾰ_2 : holor_index ds) => add_comm_group.add (ᾰ ᾰ_2) (ᾰ_1 ᾰ_2))
    sorry (id fun (ᾰ : holor_index ds) => add_comm_group.zero) sorry sorry
    (fun (ᾰ : holor α ds) => id fun (ᾰ_1 : holor_index ds) => add_comm_group.neg (ᾰ ᾰ_1))
    (fun (ᾰ ᾰ_1 : holor α ds) => id fun (ᾰ_2 : holor_index ds) => add_comm_group.sub (ᾰ ᾰ_2) (ᾰ_1 ᾰ_2)) sorry sorry

/- scalar product -/

protected instance has_scalar {α : Type} {ds : List ℕ} [Mul α] : has_scalar α (holor α ds) :=
  has_scalar.mk fun (a : α) (x : holor α ds) (t : holor_index ds) => a * x t

protected instance semimodule {α : Type} {ds : List ℕ} [semiring α] : semimodule α (holor α ds) :=
  pi.semimodule (holor_index ds) (fun (ᾰ : holor_index ds) => α) α

/-- The tensor product of two holors. -/
def mul {α : Type} {ds₁ : List ℕ} {ds₂ : List ℕ} [s : Mul α] (x : holor α ds₁) (y : holor α ds₂) : holor α (ds₁ ++ ds₂) :=
  fun (t : holor_index (ds₁ ++ ds₂)) => x (holor_index.take t) * y (holor_index.drop t)

theorem cast_type {α : Type} {ds₁ : List ℕ} {ds₂ : List ℕ} (eq : ds₁ = ds₂) (a : holor α ds₁) : cast (congr_arg (holor α) eq) a = fun (t : holor_index ds₂) => a (cast (congr_arg holor_index (Eq.symm eq)) t) :=
  eq.drec (Eq.refl (cast (congr_arg (holor α) (Eq.refl ds₁)) a)) eq

def assoc_right {α : Type} {ds₁ : List ℕ} {ds₂ : List ℕ} {ds₃ : List ℕ} : holor α (ds₁ ++ ds₂ ++ ds₃) → holor α (ds₁ ++ (ds₂ ++ ds₃)) :=
  cast sorry

def assoc_left {α : Type} {ds₁ : List ℕ} {ds₂ : List ℕ} {ds₃ : List ℕ} : holor α (ds₁ ++ (ds₂ ++ ds₃)) → holor α (ds₁ ++ ds₂ ++ ds₃) :=
  cast sorry

theorem mul_assoc0 {α : Type} {ds₁ : List ℕ} {ds₂ : List ℕ} {ds₃ : List ℕ} [semigroup α] (x : holor α ds₁) (y : holor α ds₂) (z : holor α ds₃) : mul (mul x y) z = assoc_left (mul x (mul y z)) := sorry

theorem mul_assoc {α : Type} {ds₁ : List ℕ} {ds₂ : List ℕ} {ds₃ : List ℕ} [semigroup α] (x : holor α ds₁) (y : holor α ds₂) (z : holor α ds₃) : mul (mul x y) z == mul x (mul y z) := sorry

theorem mul_left_distrib {α : Type} {ds₁ : List ℕ} {ds₂ : List ℕ} [distrib α] (x : holor α ds₁) (y : holor α ds₂) (z : holor α ds₂) : mul x (y + z) = mul x y + mul x z :=
  funext
    fun (t : holor_index (ds₁ ++ ds₂)) =>
      left_distrib (x (holor_index.take t)) (y (holor_index.drop t)) (z (holor_index.drop t))

theorem mul_right_distrib {α : Type} {ds₁ : List ℕ} {ds₂ : List ℕ} [distrib α] (x : holor α ds₁) (y : holor α ds₁) (z : holor α ds₂) : mul (x + y) z = mul x z + mul y z :=
  funext
    fun (t : holor_index (ds₁ ++ ds₂)) =>
      right_distrib (x (holor_index.take t)) (y (holor_index.take t)) (z (holor_index.drop t))

@[simp] theorem zero_mul {ds₁ : List ℕ} {ds₂ : List ℕ} {α : Type} [ring α] (x : holor α ds₂) : mul 0 x = 0 :=
  funext fun (t : holor_index (ds₁ ++ ds₂)) => zero_mul (x (holor_index.drop t))

@[simp] theorem mul_zero {ds₁ : List ℕ} {ds₂ : List ℕ} {α : Type} [ring α] (x : holor α ds₁) : mul x 0 = 0 :=
  funext fun (t : holor_index (ds₁ ++ ds₂)) => mul_zero (x (holor_index.take t))

theorem mul_scalar_mul {α : Type} {ds : List ℕ} [monoid α] (x : holor α []) (y : holor α ds) : mul x y = x { val := [], property := list.forall₂.nil } • y := sorry

/- holor slices -/

/-- A slice is a subholor consisting of all entries with initial index i. -/
def slice {α : Type} {d : ℕ} {ds : List ℕ} (x : holor α (d :: ds)) (i : ℕ) (h : i < d) : holor α ds :=
  fun (is : holor_index ds) => x { val := i :: subtype.val is, property := sorry }

/-- The 1-dimensional "unit" holor with 1 in the `j`th position. -/
def unit_vec {α : Type} [monoid α] [add_monoid α] (d : ℕ) (j : ℕ) : holor α [d] :=
  fun (ti : holor_index [d]) => ite (subtype.val ti = [j]) 1 0

theorem holor_index_cons_decomp {d : ℕ} {ds : List ℕ} (p : holor_index (d :: ds) → Prop) (t : holor_index (d :: ds)) : (∀ (i : ℕ) (is : List ℕ) (h : subtype.val t = i :: is),
    p
      { val := i :: is,
        property :=
          eq.mpr (id (Eq._oldrec (Eq.refl (list.forall₂ Less (i :: is) (d :: ds))) (Eq.symm h)))
            (subtype.property t) }) →
  p t := sorry

/-- Two holors are equal if all their slices are equal. -/
theorem slice_eq {α : Type} {d : ℕ} {ds : List ℕ} (x : holor α (d :: ds)) (y : holor α (d :: ds)) (h : slice x = slice y) : x = y := sorry

theorem slice_unit_vec_mul {α : Type} {d : ℕ} {ds : List ℕ} [ring α] {i : ℕ} {j : ℕ} (hid : i < d) (x : holor α ds) : slice (mul (unit_vec d j) x) i hid = ite (i = j) x 0 := sorry

theorem slice_add {α : Type} {d : ℕ} {ds : List ℕ} [Add α] (i : ℕ) (hid : i < d) (x : holor α (d :: ds)) (y : holor α (d :: ds)) : slice x i hid + slice y i hid = slice (x + y) i hid := sorry

theorem slice_zero {α : Type} {d : ℕ} {ds : List ℕ} [HasZero α] (i : ℕ) (hid : i < d) : slice 0 i hid = 0 :=
  rfl

theorem slice_sum {α : Type} {d : ℕ} {ds : List ℕ} [add_comm_monoid α] {β : Type} (i : ℕ) (hid : i < d) (s : finset β) (f : β → holor α (d :: ds)) : (finset.sum s fun (x : β) => slice (f x) i hid) = slice (finset.sum s fun (x : β) => f x) i hid := sorry

/-- The original holor can be recovered from its slices by multiplying with unit vectors and summing up. -/
@[simp] theorem sum_unit_vec_mul_slice {α : Type} {d : ℕ} {ds : List ℕ} [ring α] (x : holor α (d :: ds)) : (finset.sum (finset.attach (finset.range d))
    fun (i : Subtype fun (x : ℕ) => x ∈ finset.range d) =>
      mul (unit_vec d ↑i) (slice x (↑i) (nat.succ_le_of_lt (iff.mp finset.mem_range (subtype.prop i))))) =
  x := sorry

/- CP rank -/

/-- `cprank_max1 x` means `x` has CP rank at most 1, that is,
  it is the tensor product of 1-dimensional holors. -/
inductive cprank_max1 {α : Type} [Mul α] : {ds : List ℕ} → holor α ds → Prop
where
| nil : ∀ (x : holor α []), cprank_max1 x
| cons : ∀ {d : ℕ} {ds : List ℕ} (x : holor α [d]) (y : holor α ds), cprank_max1 y → cprank_max1 (mul x y)

/-- `cprank_max N x` means `x` has CP rank at most `N`, that is,
  it can be written as the sum of N holors of rank at most 1. -/
inductive cprank_max {α : Type} [Mul α] [add_monoid α] : ℕ → {ds : List ℕ} → holor α ds → Prop
where
| zero : ∀ {ds : List ℕ}, cprank_max 0 0
| succ : ∀ (n : ℕ) {ds : List ℕ} (x y : holor α ds), cprank_max1 x → cprank_max n y → cprank_max (n + 1) (x + y)

theorem cprank_max_nil {α : Type} [monoid α] [add_monoid α] (x : holor α []) : cprank_max 1 x := sorry

theorem cprank_max_1 {α : Type} {ds : List ℕ} [monoid α] [add_monoid α] {x : holor α ds} (h : cprank_max1 x) : cprank_max 1 x := sorry

theorem cprank_max_add {α : Type} {ds : List ℕ} [monoid α] [add_monoid α] {m : ℕ} {n : ℕ} {x : holor α ds} {y : holor α ds} : cprank_max m x → cprank_max n y → cprank_max (m + n) (x + y) := sorry

theorem cprank_max_mul {α : Type} {d : ℕ} {ds : List ℕ} [ring α] (n : ℕ) (x : holor α [d]) (y : holor α ds) : cprank_max n y → cprank_max n (mul x y) := sorry

theorem cprank_max_sum {α : Type} {ds : List ℕ} [ring α] {β : Type u_1} {n : ℕ} (s : finset β) (f : β → holor α ds) : (∀ (x : β), x ∈ s → cprank_max n (f x)) → cprank_max (finset.card s * n) (finset.sum s fun (x : β) => f x) := sorry

theorem cprank_max_upper_bound {α : Type} [ring α] {ds : List ℕ} (x : holor α ds) : cprank_max (list.prod ds) x := sorry

/-- The CP rank of a holor `x`: the smallest N such that
  `x` can be written as the sum of N holors of rank at most 1. -/
def cprank {α : Type} {ds : List ℕ} [ring α] (x : holor α ds) : ℕ :=
  nat.find sorry

theorem cprank_upper_bound {α : Type} [ring α] {ds : List ℕ} (x : holor α ds) : cprank x ≤ list.prod ds :=
  nat.find_min'
    (Exists.intro (list.prod ds) ((fun (this : cprank_max (list.prod ds) x) => this) (cprank_max_upper_bound x)))
    (cprank_max_upper_bound x)

