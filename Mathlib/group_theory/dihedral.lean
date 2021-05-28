/-
Copyright (c) 2020 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.zmod.basic
import Mathlib.group_theory.order_of_element
import Mathlib.PostPort

universes l 

namespace Mathlib

/-!
# Dihedral Groups

We define the dihedral groups `dihedral n`, with elements `r i` and `sr i` for `i : zmod n`.

For `n ≠ 0`, `dihedral n` represents the symmetry group of the regular `n`-gon. `r i` represents
the rotations of the `n`-gon by `2πi/n`, and `sr i` represents the reflections of the `n`-gon.
`dihedral 0` corresponds to the infinite dihedral group.
-/

/--
For `n ≠ 0`, `dihedral n` represents the symmetry group of the regular `n`-gon. `r i` represents
the rotations of the `n`-gon by `2πi/n`, and `sr i` represents the reflections of the `n`-gon.
`dihedral 0` corresponds to the infinite dihedral group.
-/
inductive dihedral (n : ℕ) 
where
| r : zmod n → dihedral n
| sr : zmod n → dihedral n

namespace dihedral


/--
Multiplication of the dihedral group.
-/
/--
The identity `1` is the rotation by `0`.
-/
protected instance inhabited {n : ℕ} : Inhabited (dihedral n) :=
  { default := one }

/--
The inverse of a an element of the dihedral group.
-/
/--
The group structure on `dihedral n`.
-/
protected instance group {n : ℕ} : group (dihedral n) :=
  group.mk mul sorry one sorry sorry inv (div_inv_monoid.div._default mul sorry one sorry sorry inv) sorry

@[simp] theorem r_mul_r {n : ℕ} (i : zmod n) (j : zmod n) : r i * r j = r (i + j) :=
  rfl

@[simp] theorem r_mul_sr {n : ℕ} (i : zmod n) (j : zmod n) : r i * sr j = sr (j - i) :=
  rfl

@[simp] theorem sr_mul_r {n : ℕ} (i : zmod n) (j : zmod n) : sr i * r j = sr (i + j) :=
  rfl

@[simp] theorem sr_mul_sr {n : ℕ} (i : zmod n) (j : zmod n) : sr i * sr j = r (j - i) :=
  rfl

theorem one_def {n : ℕ} : 1 = r 0 :=
  rfl

/--
If `0 < n`, then `dihedral n` is a finite group.
-/
protected instance fintype {n : ℕ} [fact (0 < n)] : fintype (dihedral n) :=
  fintype.of_equiv (zmod n ⊕ zmod n) fintype_helper

protected instance nontrivial {n : ℕ} : nontrivial (dihedral n) :=
  nontrivial.mk (Exists.intro (r 0) (Exists.intro (sr 0) (of_as_true trivial)))

/--
If `0 < n`, then `dihedral n` has `2n` elements.
-/
theorem card {n : ℕ} [fact (0 < n)] : fintype.card (dihedral n) = bit0 1 * n := sorry

@[simp] theorem r_one_pow {n : ℕ} (k : ℕ) : r 1 ^ k = r ↑k := sorry

@[simp] theorem r_one_pow_n {n : ℕ} : r 1 ^ n = 1 := sorry

@[simp] theorem sr_mul_self {n : ℕ} (i : zmod n) : sr i * sr i = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (sr i * sr i = 1)) (sr_mul_sr i i)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (r (i - i) = 1)) (sub_self i)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (r 0 = 1)) one_def)) (Eq.refl (r 0))))

/--
If `0 < n`, then `sr i` has order 2.
-/
@[simp] theorem order_of_sr {n : ℕ} [fact (0 < n)] (i : zmod n) : order_of (sr i) = bit0 1 := sorry

/--
If `0 < n`, then `r 1` has order `n`.
-/
@[simp] theorem order_of_r_one {n : ℕ} [hnpos : fact (0 < n)] : order_of (r 1) = n := sorry

/--
If `0 < n`, then `i : zmod n` has order `n / gcd n i`
-/
theorem order_of_r {n : ℕ} [fact (0 < n)] (i : zmod n) : order_of (r i) = n / nat.gcd n (zmod.val i) := sorry

