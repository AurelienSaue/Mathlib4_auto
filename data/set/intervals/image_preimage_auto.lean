/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Patrick Massot
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.set.intervals.basic
import Mathlib.data.equiv.mul_add
import Mathlib.algebra.pointwise
import PostPort

universes u 

namespace Mathlib

/-!
# (Pre)images of intervals

In this file we prove a bunch of trivial lemmas like “if we add `a` to all points of `[b, c]`,
then we get `[a + b, a + c]`”. For the functions `x ↦ x ± a`, `x ↦ a ± x`, and `x ↦ -x` we prove
lemmas about preimages and images of all intervals. We also prove a few lemmas about images under
`x ↦ a * x`, `x ↦ x * a` and `x ↦ x⁻¹`.

-/

namespace set


/-!
### Preimages under `x ↦ a + x`
-/

@[simp] theorem preimage_const_add_Ici {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) : (fun (x : G) => a + x) ⁻¹' Ici b = Ici (b - a) :=
  ext fun (x : G) => iff.symm sub_le_iff_le_add'

@[simp] theorem preimage_const_add_Ioi {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) : (fun (x : G) => a + x) ⁻¹' Ioi b = Ioi (b - a) :=
  ext fun (x : G) => iff.symm sub_lt_iff_lt_add'

@[simp] theorem preimage_const_add_Iic {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) : (fun (x : G) => a + x) ⁻¹' Iic b = Iic (b - a) :=
  ext fun (x : G) => iff.symm le_sub_iff_add_le'

@[simp] theorem preimage_const_add_Iio {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) : (fun (x : G) => a + x) ⁻¹' Iio b = Iio (b - a) :=
  ext fun (x : G) => iff.symm lt_sub_iff_add_lt'

@[simp] theorem preimage_const_add_Icc {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) (c : G) : (fun (x : G) => a + x) ⁻¹' Icc b c = Icc (b - a) (c - a) := sorry

@[simp] theorem preimage_const_add_Ico {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) (c : G) : (fun (x : G) => a + x) ⁻¹' Ico b c = Ico (b - a) (c - a) := sorry

@[simp] theorem preimage_const_add_Ioc {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) (c : G) : (fun (x : G) => a + x) ⁻¹' Ioc b c = Ioc (b - a) (c - a) := sorry

@[simp] theorem preimage_const_add_Ioo {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) (c : G) : (fun (x : G) => a + x) ⁻¹' Ioo b c = Ioo (b - a) (c - a) := sorry

/-!
### Preimages under `x ↦ x + a`
-/

@[simp] theorem preimage_add_const_Ici {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) : (fun (x : G) => x + a) ⁻¹' Ici b = Ici (b - a) :=
  ext fun (x : G) => iff.symm sub_le_iff_le_add

@[simp] theorem preimage_add_const_Ioi {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) : (fun (x : G) => x + a) ⁻¹' Ioi b = Ioi (b - a) :=
  ext fun (x : G) => iff.symm sub_lt_iff_lt_add

@[simp] theorem preimage_add_const_Iic {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) : (fun (x : G) => x + a) ⁻¹' Iic b = Iic (b - a) :=
  ext fun (x : G) => iff.symm le_sub_iff_add_le

@[simp] theorem preimage_add_const_Iio {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) : (fun (x : G) => x + a) ⁻¹' Iio b = Iio (b - a) :=
  ext fun (x : G) => iff.symm lt_sub_iff_add_lt

@[simp] theorem preimage_add_const_Icc {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) (c : G) : (fun (x : G) => x + a) ⁻¹' Icc b c = Icc (b - a) (c - a) := sorry

@[simp] theorem preimage_add_const_Ico {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) (c : G) : (fun (x : G) => x + a) ⁻¹' Ico b c = Ico (b - a) (c - a) := sorry

@[simp] theorem preimage_add_const_Ioc {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) (c : G) : (fun (x : G) => x + a) ⁻¹' Ioc b c = Ioc (b - a) (c - a) := sorry

@[simp] theorem preimage_add_const_Ioo {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) (c : G) : (fun (x : G) => x + a) ⁻¹' Ioo b c = Ioo (b - a) (c - a) := sorry

/-!
### Preimages under `x ↦ -x`
-/

@[simp] theorem preimage_neg_Ici {G : Type u} [ordered_add_comm_group G] (a : G) : -Ici a = Iic (-a) :=
  ext fun (x : G) => le_neg

@[simp] theorem preimage_neg_Iic {G : Type u} [ordered_add_comm_group G] (a : G) : -Iic a = Ici (-a) :=
  ext fun (x : G) => neg_le

@[simp] theorem preimage_neg_Ioi {G : Type u} [ordered_add_comm_group G] (a : G) : -Ioi a = Iio (-a) :=
  ext fun (x : G) => lt_neg

@[simp] theorem preimage_neg_Iio {G : Type u} [ordered_add_comm_group G] (a : G) : -Iio a = Ioi (-a) :=
  ext fun (x : G) => neg_lt

@[simp] theorem preimage_neg_Icc {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) : -Icc a b = Icc (-b) (-a) := sorry

@[simp] theorem preimage_neg_Ico {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) : -Ico a b = Ioc (-b) (-a) := sorry

@[simp] theorem preimage_neg_Ioc {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) : -Ioc a b = Ico (-b) (-a) := sorry

@[simp] theorem preimage_neg_Ioo {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) : -Ioo a b = Ioo (-b) (-a) := sorry

/-!
### Preimages under `x ↦ x - a`
-/

@[simp] theorem preimage_sub_const_Ici {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) : (fun (x : G) => x - a) ⁻¹' Ici b = Ici (b + a) := sorry

@[simp] theorem preimage_sub_const_Ioi {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) : (fun (x : G) => x - a) ⁻¹' Ioi b = Ioi (b + a) := sorry

@[simp] theorem preimage_sub_const_Iic {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) : (fun (x : G) => x - a) ⁻¹' Iic b = Iic (b + a) := sorry

@[simp] theorem preimage_sub_const_Iio {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) : (fun (x : G) => x - a) ⁻¹' Iio b = Iio (b + a) := sorry

@[simp] theorem preimage_sub_const_Icc {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) (c : G) : (fun (x : G) => x - a) ⁻¹' Icc b c = Icc (b + a) (c + a) := sorry

@[simp] theorem preimage_sub_const_Ico {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) (c : G) : (fun (x : G) => x - a) ⁻¹' Ico b c = Ico (b + a) (c + a) := sorry

@[simp] theorem preimage_sub_const_Ioc {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) (c : G) : (fun (x : G) => x - a) ⁻¹' Ioc b c = Ioc (b + a) (c + a) := sorry

@[simp] theorem preimage_sub_const_Ioo {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) (c : G) : (fun (x : G) => x - a) ⁻¹' Ioo b c = Ioo (b + a) (c + a) := sorry

/-!
### Preimages under `x ↦ a - x`
-/

@[simp] theorem preimage_const_sub_Ici {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) : (fun (x : G) => a - x) ⁻¹' Ici b = Iic (a - b) :=
  ext fun (x : G) => le_sub

@[simp] theorem preimage_const_sub_Iic {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) : (fun (x : G) => a - x) ⁻¹' Iic b = Ici (a - b) :=
  ext fun (x : G) => sub_le

@[simp] theorem preimage_const_sub_Ioi {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) : (fun (x : G) => a - x) ⁻¹' Ioi b = Iio (a - b) :=
  ext fun (x : G) => lt_sub

@[simp] theorem preimage_const_sub_Iio {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) : (fun (x : G) => a - x) ⁻¹' Iio b = Ioi (a - b) :=
  ext fun (x : G) => sub_lt

@[simp] theorem preimage_const_sub_Icc {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) (c : G) : (fun (x : G) => a - x) ⁻¹' Icc b c = Icc (a - c) (a - b) := sorry

@[simp] theorem preimage_const_sub_Ico {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) (c : G) : (fun (x : G) => a - x) ⁻¹' Ico b c = Ioc (a - c) (a - b) := sorry

@[simp] theorem preimage_const_sub_Ioc {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) (c : G) : (fun (x : G) => a - x) ⁻¹' Ioc b c = Ico (a - c) (a - b) := sorry

@[simp] theorem preimage_const_sub_Ioo {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) (c : G) : (fun (x : G) => a - x) ⁻¹' Ioo b c = Ioo (a - c) (a - b) := sorry

/-!
### Images under `x ↦ a + x`
-/

@[simp] theorem image_const_add_Ici {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) : (fun (x : G) => a + x) '' Ici b = Ici (a + b) := sorry

@[simp] theorem image_const_add_Iic {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) : (fun (x : G) => a + x) '' Iic b = Iic (a + b) := sorry

@[simp] theorem image_const_add_Iio {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) : (fun (x : G) => a + x) '' Iio b = Iio (a + b) := sorry

@[simp] theorem image_const_add_Ioi {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) : (fun (x : G) => a + x) '' Ioi b = Ioi (a + b) := sorry

@[simp] theorem image_const_add_Icc {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) (c : G) : (fun (x : G) => a + x) '' Icc b c = Icc (a + b) (a + c) := sorry

@[simp] theorem image_const_add_Ico {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) (c : G) : (fun (x : G) => a + x) '' Ico b c = Ico (a + b) (a + c) := sorry

@[simp] theorem image_const_add_Ioc {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) (c : G) : (fun (x : G) => a + x) '' Ioc b c = Ioc (a + b) (a + c) := sorry

@[simp] theorem image_const_add_Ioo {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) (c : G) : (fun (x : G) => a + x) '' Ioo b c = Ioo (a + b) (a + c) := sorry

/-!
### Images under `x ↦ x + a`
-/

@[simp] theorem image_add_const_Ici {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) : (fun (x : G) => x + a) '' Ici b = Ici (a + b) := sorry

@[simp] theorem image_add_const_Iic {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) : (fun (x : G) => x + a) '' Iic b = Iic (a + b) := sorry

@[simp] theorem image_add_const_Iio {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) : (fun (x : G) => x + a) '' Iio b = Iio (a + b) := sorry

@[simp] theorem image_add_const_Ioi {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) : (fun (x : G) => x + a) '' Ioi b = Ioi (a + b) := sorry

@[simp] theorem image_add_const_Icc {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) (c : G) : (fun (x : G) => x + a) '' Icc b c = Icc (a + b) (a + c) := sorry

@[simp] theorem image_add_const_Ico {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) (c : G) : (fun (x : G) => x + a) '' Ico b c = Ico (a + b) (a + c) := sorry

@[simp] theorem image_add_const_Ioc {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) (c : G) : (fun (x : G) => x + a) '' Ioc b c = Ioc (a + b) (a + c) := sorry

@[simp] theorem image_add_const_Ioo {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) (c : G) : (fun (x : G) => x + a) '' Ioo b c = Ioo (a + b) (a + c) := sorry

/-!
### Images under `x ↦ -x`
-/

theorem image_neg_Ici {G : Type u} [ordered_add_comm_group G] (a : G) : Neg.neg '' Ici a = Iic (-a) := sorry

theorem image_neg_Iic {G : Type u} [ordered_add_comm_group G] (a : G) : Neg.neg '' Iic a = Ici (-a) := sorry

theorem image_neg_Ioi {G : Type u} [ordered_add_comm_group G] (a : G) : Neg.neg '' Ioi a = Iio (-a) := sorry

theorem image_neg_Iio {G : Type u} [ordered_add_comm_group G] (a : G) : Neg.neg '' Iio a = Ioi (-a) := sorry

theorem image_neg_Icc {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) : Neg.neg '' Icc a b = Icc (-b) (-a) := sorry

theorem image_neg_Ico {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) : Neg.neg '' Ico a b = Ioc (-b) (-a) := sorry

theorem image_neg_Ioc {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) : Neg.neg '' Ioc a b = Ico (-b) (-a) := sorry

theorem image_neg_Ioo {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) : Neg.neg '' Ioo a b = Ioo (-b) (-a) := sorry

/-!
### Images under `x ↦ a - x`
-/

@[simp] theorem image_const_sub_Ici {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) : (fun (x : G) => a - x) '' Ici b = Iic (a - b) := sorry

@[simp] theorem image_const_sub_Iic {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) : (fun (x : G) => a - x) '' Iic b = Ici (a - b) := sorry

@[simp] theorem image_const_sub_Ioi {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) : (fun (x : G) => a - x) '' Ioi b = Iio (a - b) := sorry

@[simp] theorem image_const_sub_Iio {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) : (fun (x : G) => a - x) '' Iio b = Ioi (a - b) := sorry

@[simp] theorem image_const_sub_Icc {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) (c : G) : (fun (x : G) => a - x) '' Icc b c = Icc (a - c) (a - b) := sorry

@[simp] theorem image_const_sub_Ico {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) (c : G) : (fun (x : G) => a - x) '' Ico b c = Ioc (a - c) (a - b) := sorry

@[simp] theorem image_const_sub_Ioc {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) (c : G) : (fun (x : G) => a - x) '' Ioc b c = Ico (a - c) (a - b) := sorry

@[simp] theorem image_const_sub_Ioo {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) (c : G) : (fun (x : G) => a - x) '' Ioo b c = Ioo (a - c) (a - b) := sorry

/-!
### Images under `x ↦ x - a`
-/

@[simp] theorem image_sub_const_Ici {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) : (fun (x : G) => x - a) '' Ici b = Ici (b - a) := sorry

@[simp] theorem image_sub_const_Iic {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) : (fun (x : G) => x - a) '' Iic b = Iic (b - a) := sorry

@[simp] theorem image_sub_const_Ioi {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) : (fun (x : G) => x - a) '' Ioi b = Ioi (b - a) := sorry

@[simp] theorem image_sub_const_Iio {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) : (fun (x : G) => x - a) '' Iio b = Iio (b - a) := sorry

@[simp] theorem image_sub_const_Icc {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) (c : G) : (fun (x : G) => x - a) '' Icc b c = Icc (b - a) (c - a) := sorry

@[simp] theorem image_sub_const_Ico {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) (c : G) : (fun (x : G) => x - a) '' Ico b c = Ico (b - a) (c - a) := sorry

@[simp] theorem image_sub_const_Ioc {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) (c : G) : (fun (x : G) => x - a) '' Ioc b c = Ioc (b - a) (c - a) := sorry

@[simp] theorem image_sub_const_Ioo {G : Type u} [ordered_add_comm_group G] (a : G) (b : G) (c : G) : (fun (x : G) => x - a) '' Ioo b c = Ioo (b - a) (c - a) := sorry

/-!
### Multiplication and inverse in a field
-/

@[simp] theorem preimage_mul_const_Iio {k : Type u} [linear_ordered_field k] (a : k) {c : k} (h : 0 < c) : (fun (x : k) => x * c) ⁻¹' Iio a = Iio (a / c) :=
  ext fun (x : k) => iff.symm (lt_div_iff h)

@[simp] theorem preimage_mul_const_Ioi {k : Type u} [linear_ordered_field k] (a : k) {c : k} (h : 0 < c) : (fun (x : k) => x * c) ⁻¹' Ioi a = Ioi (a / c) :=
  ext fun (x : k) => iff.symm (div_lt_iff h)

@[simp] theorem preimage_mul_const_Iic {k : Type u} [linear_ordered_field k] (a : k) {c : k} (h : 0 < c) : (fun (x : k) => x * c) ⁻¹' Iic a = Iic (a / c) :=
  ext fun (x : k) => iff.symm (le_div_iff h)

@[simp] theorem preimage_mul_const_Ici {k : Type u} [linear_ordered_field k] (a : k) {c : k} (h : 0 < c) : (fun (x : k) => x * c) ⁻¹' Ici a = Ici (a / c) :=
  ext fun (x : k) => iff.symm (div_le_iff h)

@[simp] theorem preimage_mul_const_Ioo {k : Type u} [linear_ordered_field k] (a : k) (b : k) {c : k} (h : 0 < c) : (fun (x : k) => x * c) ⁻¹' Ioo a b = Ioo (a / c) (b / c) := sorry

@[simp] theorem preimage_mul_const_Ioc {k : Type u} [linear_ordered_field k] (a : k) (b : k) {c : k} (h : 0 < c) : (fun (x : k) => x * c) ⁻¹' Ioc a b = Ioc (a / c) (b / c) := sorry

@[simp] theorem preimage_mul_const_Ico {k : Type u} [linear_ordered_field k] (a : k) (b : k) {c : k} (h : 0 < c) : (fun (x : k) => x * c) ⁻¹' Ico a b = Ico (a / c) (b / c) := sorry

@[simp] theorem preimage_mul_const_Icc {k : Type u} [linear_ordered_field k] (a : k) (b : k) {c : k} (h : 0 < c) : (fun (x : k) => x * c) ⁻¹' Icc a b = Icc (a / c) (b / c) := sorry

@[simp] theorem preimage_mul_const_Iio_of_neg {k : Type u} [linear_ordered_field k] (a : k) {c : k} (h : c < 0) : (fun (x : k) => x * c) ⁻¹' Iio a = Ioi (a / c) :=
  ext fun (x : k) => iff.symm (div_lt_iff_of_neg h)

@[simp] theorem preimage_mul_const_Ioi_of_neg {k : Type u} [linear_ordered_field k] (a : k) {c : k} (h : c < 0) : (fun (x : k) => x * c) ⁻¹' Ioi a = Iio (a / c) :=
  ext fun (x : k) => iff.symm (lt_div_iff_of_neg h)

@[simp] theorem preimage_mul_const_Iic_of_neg {k : Type u} [linear_ordered_field k] (a : k) {c : k} (h : c < 0) : (fun (x : k) => x * c) ⁻¹' Iic a = Ici (a / c) :=
  ext fun (x : k) => iff.symm (div_le_iff_of_neg h)

@[simp] theorem preimage_mul_const_Ici_of_neg {k : Type u} [linear_ordered_field k] (a : k) {c : k} (h : c < 0) : (fun (x : k) => x * c) ⁻¹' Ici a = Iic (a / c) :=
  ext fun (x : k) => iff.symm (le_div_iff_of_neg h)

@[simp] theorem preimage_mul_const_Ioo_of_neg {k : Type u} [linear_ordered_field k] (a : k) (b : k) {c : k} (h : c < 0) : (fun (x : k) => x * c) ⁻¹' Ioo a b = Ioo (b / c) (a / c) := sorry

@[simp] theorem preimage_mul_const_Ioc_of_neg {k : Type u} [linear_ordered_field k] (a : k) (b : k) {c : k} (h : c < 0) : (fun (x : k) => x * c) ⁻¹' Ioc a b = Ico (b / c) (a / c) := sorry

@[simp] theorem preimage_mul_const_Ico_of_neg {k : Type u} [linear_ordered_field k] (a : k) (b : k) {c : k} (h : c < 0) : (fun (x : k) => x * c) ⁻¹' Ico a b = Ioc (b / c) (a / c) := sorry

@[simp] theorem preimage_mul_const_Icc_of_neg {k : Type u} [linear_ordered_field k] (a : k) (b : k) {c : k} (h : c < 0) : (fun (x : k) => x * c) ⁻¹' Icc a b = Icc (b / c) (a / c) := sorry

@[simp] theorem preimage_const_mul_Iio {k : Type u} [linear_ordered_field k] (a : k) {c : k} (h : 0 < c) : Mul.mul c ⁻¹' Iio a = Iio (a / c) :=
  ext fun (x : k) => iff.symm (lt_div_iff' h)

@[simp] theorem preimage_const_mul_Ioi {k : Type u} [linear_ordered_field k] (a : k) {c : k} (h : 0 < c) : Mul.mul c ⁻¹' Ioi a = Ioi (a / c) :=
  ext fun (x : k) => iff.symm (div_lt_iff' h)

@[simp] theorem preimage_const_mul_Iic {k : Type u} [linear_ordered_field k] (a : k) {c : k} (h : 0 < c) : Mul.mul c ⁻¹' Iic a = Iic (a / c) :=
  ext fun (x : k) => iff.symm (le_div_iff' h)

@[simp] theorem preimage_const_mul_Ici {k : Type u} [linear_ordered_field k] (a : k) {c : k} (h : 0 < c) : Mul.mul c ⁻¹' Ici a = Ici (a / c) :=
  ext fun (x : k) => iff.symm (div_le_iff' h)

@[simp] theorem preimage_const_mul_Ioo {k : Type u} [linear_ordered_field k] (a : k) (b : k) {c : k} (h : 0 < c) : Mul.mul c ⁻¹' Ioo a b = Ioo (a / c) (b / c) := sorry

@[simp] theorem preimage_const_mul_Ioc {k : Type u} [linear_ordered_field k] (a : k) (b : k) {c : k} (h : 0 < c) : Mul.mul c ⁻¹' Ioc a b = Ioc (a / c) (b / c) := sorry

@[simp] theorem preimage_const_mul_Ico {k : Type u} [linear_ordered_field k] (a : k) (b : k) {c : k} (h : 0 < c) : Mul.mul c ⁻¹' Ico a b = Ico (a / c) (b / c) := sorry

@[simp] theorem preimage_const_mul_Icc {k : Type u} [linear_ordered_field k] (a : k) (b : k) {c : k} (h : 0 < c) : Mul.mul c ⁻¹' Icc a b = Icc (a / c) (b / c) := sorry

@[simp] theorem preimage_const_mul_Iio_of_neg {k : Type u} [linear_ordered_field k] (a : k) {c : k} (h : c < 0) : Mul.mul c ⁻¹' Iio a = Ioi (a / c) := sorry

@[simp] theorem preimage_const_mul_Ioi_of_neg {k : Type u} [linear_ordered_field k] (a : k) {c : k} (h : c < 0) : Mul.mul c ⁻¹' Ioi a = Iio (a / c) := sorry

@[simp] theorem preimage_const_mul_Iic_of_neg {k : Type u} [linear_ordered_field k] (a : k) {c : k} (h : c < 0) : Mul.mul c ⁻¹' Iic a = Ici (a / c) := sorry

@[simp] theorem preimage_const_mul_Ici_of_neg {k : Type u} [linear_ordered_field k] (a : k) {c : k} (h : c < 0) : Mul.mul c ⁻¹' Ici a = Iic (a / c) := sorry

@[simp] theorem preimage_const_mul_Ioo_of_neg {k : Type u} [linear_ordered_field k] (a : k) (b : k) {c : k} (h : c < 0) : Mul.mul c ⁻¹' Ioo a b = Ioo (b / c) (a / c) := sorry

@[simp] theorem preimage_const_mul_Ioc_of_neg {k : Type u} [linear_ordered_field k] (a : k) (b : k) {c : k} (h : c < 0) : Mul.mul c ⁻¹' Ioc a b = Ico (b / c) (a / c) := sorry

@[simp] theorem preimage_const_mul_Ico_of_neg {k : Type u} [linear_ordered_field k] (a : k) (b : k) {c : k} (h : c < 0) : Mul.mul c ⁻¹' Ico a b = Ioc (b / c) (a / c) := sorry

@[simp] theorem preimage_const_mul_Icc_of_neg {k : Type u} [linear_ordered_field k] (a : k) (b : k) {c : k} (h : c < 0) : Mul.mul c ⁻¹' Icc a b = Icc (b / c) (a / c) := sorry

theorem image_mul_right_Icc' {k : Type u} [linear_ordered_field k] (a : k) (b : k) {c : k} (h : 0 < c) : (fun (x : k) => x * c) '' Icc a b = Icc (a * c) (b * c) := sorry

theorem image_mul_right_Icc {k : Type u} [linear_ordered_field k] {a : k} {b : k} {c : k} (hab : a ≤ b) (hc : 0 ≤ c) : (fun (x : k) => x * c) '' Icc a b = Icc (a * c) (b * c) := sorry

theorem image_mul_left_Icc' {k : Type u} [linear_ordered_field k] {a : k} (h : 0 < a) (b : k) (c : k) : Mul.mul a '' Icc b c = Icc (a * b) (a * c) := sorry

theorem image_mul_left_Icc {k : Type u} [linear_ordered_field k] {a : k} {b : k} {c : k} (ha : 0 ≤ a) (hbc : b ≤ c) : Mul.mul a '' Icc b c = Icc (a * b) (a * c) := sorry

/-- The image under `inv` of `Ioo 0 a` is `Ioi a⁻¹`. -/
theorem image_inv_Ioo_0_left {k : Type u} [linear_ordered_field k] {a : k} (ha : 0 < a) : has_inv.inv '' Ioo 0 a = Ioi (a⁻¹) := sorry

