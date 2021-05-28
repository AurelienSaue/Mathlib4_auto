/-
Copyright (c) 2019 Neil Strickland.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Neil Strickland

This file sets up a version of the Euclidean algorithm that works
only with natural numbers.  Given a, b > 0, it computes the unique
system (w, x, y, z, d) such that the following identities hold:

 w * z = x * y + 1
 a = (w + x) d
 b = (y + z) d

These equations force w, z, d > 0.  They also imply that
the integers a' = w + x = a / d and b' = y + z = b / d are coprime,
and that d is the gcd of a and b.

This story is closely related to the structure of SL₂(ℕ) (as a
free monoid on two generators) and the theory of continued fractions.
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.tactic.ring
import Mathlib.tactic.abel
import Mathlib.data.pnat.prime
import PostPort

universes l 

namespace Mathlib

namespace pnat


/-- A term of xgcd_type is a system of six naturals.  They should
 be thought of as representing the matrix
 [[w, x], [y, z]] = [[wp + 1, x], [y, zp + 1]]
 together with the vector [a, b] = [ap + 1, bp + 1].
-/
structure xgcd_type 
where
  wp : ℕ
  x : ℕ
  y : ℕ
  zp : ℕ
  ap : ℕ
  bp : ℕ

namespace xgcd_type


protected instance has_sizeof : SizeOf xgcd_type :=
  { sizeOf := fun (u : xgcd_type) => bp u }

/-- The has_repr instance converts terms to strings in a way that
 reflects the matrix/vector interpretation as above. -/
protected instance has_repr : has_repr xgcd_type := sorry

def mk' (w : ℕ+) (x : ℕ) (y : ℕ) (z : ℕ+) (a : ℕ+) (b : ℕ+) : xgcd_type :=
  mk (Nat.pred (subtype.val w)) x y (Nat.pred (subtype.val z)) (Nat.pred (subtype.val a)) (Nat.pred (subtype.val b))

def w (u : xgcd_type) : ℕ+ :=
  nat.succ_pnat (wp u)

def z (u : xgcd_type) : ℕ+ :=
  nat.succ_pnat (zp u)

def a (u : xgcd_type) : ℕ+ :=
  nat.succ_pnat (ap u)

def b (u : xgcd_type) : ℕ+ :=
  nat.succ_pnat (bp u)

def r (u : xgcd_type) : ℕ :=
  (ap u + 1) % (bp u + 1)

def q (u : xgcd_type) : ℕ :=
  (ap u + 1) / (bp u + 1)

def qp (u : xgcd_type) : ℕ :=
  q u - 1

/-- The map v gives the product of the matrix
 [[w, x], [y, z]] = [[wp + 1, x], [y, zp + 1]]
 and the vector [a, b] = [ap + 1, bp + 1].  The map
 vp gives [sp, tp] such that v = [sp + 1, tp + 1].
-/
def vp (u : xgcd_type) : ℕ × ℕ :=
  (wp u + x u + ap u + wp u * ap u + x u * bp u, y u + zp u + bp u + y u * ap u + zp u * bp u)

def v (u : xgcd_type) : ℕ × ℕ :=
  (↑(w u) * ↑(a u) + x u * ↑(b u), y u * ↑(a u) + ↑(z u) * ↑(b u))

def succ₂ (t : ℕ × ℕ) : ℕ × ℕ :=
  (Nat.succ (prod.fst t), Nat.succ (prod.snd t))

theorem v_eq_succ_vp (u : xgcd_type) : v u = succ₂ (vp u) := sorry

/-- is_special holds if the matrix has determinant one. -/
def is_special (u : xgcd_type)  :=
  wp u + zp u + wp u * zp u = x u * y u

def is_special' (u : xgcd_type)  :=
  w u * z u = nat.succ_pnat (x u * y u)

theorem is_special_iff (u : xgcd_type) : is_special u ↔ is_special' u := sorry

/-- is_reduced holds if the two entries in the vector are the
 same.  The reduction algorithm will produce a system with this
 property, whose product vector is the same as for the original
 system. -/
def is_reduced (u : xgcd_type)  :=
  ap u = bp u

def is_reduced' (u : xgcd_type)  :=
  a u = b u

theorem is_reduced_iff (u : xgcd_type) : is_reduced u ↔ is_reduced' u :=
  { mp := congr_arg nat.succ_pnat, mpr := nat.succ_pnat_inj }

def flip (u : xgcd_type) : xgcd_type :=
  mk (zp u) (y u) (x u) (wp u) (bp u) (ap u)

@[simp] theorem flip_w (u : xgcd_type) : w (flip u) = z u :=
  rfl

@[simp] theorem flip_x (u : xgcd_type) : x (flip u) = y u :=
  rfl

@[simp] theorem flip_y (u : xgcd_type) : y (flip u) = x u :=
  rfl

@[simp] theorem flip_z (u : xgcd_type) : z (flip u) = w u :=
  rfl

@[simp] theorem flip_a (u : xgcd_type) : a (flip u) = b u :=
  rfl

@[simp] theorem flip_b (u : xgcd_type) : b (flip u) = a u :=
  rfl

theorem flip_is_reduced (u : xgcd_type) : is_reduced (flip u) ↔ is_reduced u :=
  id { mp := fun (h : bp u = ap u) => Eq.symm h, mpr := fun (h : ap u = bp u) => Eq.symm h }

theorem flip_is_special (u : xgcd_type) : is_special (flip u) ↔ is_special u := sorry

theorem flip_v (u : xgcd_type) : v (flip u) = prod.swap (v u) := sorry

/-- Properties of division with remainder for a / b.  -/
theorem rq_eq (u : xgcd_type) : r u + (bp u + 1) * q u = ap u + 1 :=
  nat.mod_add_div (ap u + 1) (bp u + 1)

theorem qp_eq (u : xgcd_type) (hr : r u = 0) : q u = qp u + 1 := sorry

/-- The following function provides the starting point for
 our algorithm.  We will apply an iterative reduction process
 to it, which will produce a system satisfying is_reduced.
 The gcd can be read off from this final system.
-/
def start (a : ℕ+) (b : ℕ+) : xgcd_type :=
  mk 0 0 0 0 (↑a - 1) (↑b - 1)

theorem start_is_special (a : ℕ+) (b : ℕ+) : is_special (start a b) :=
  id (Eq.refl (0 + 0 + 0 * 0))

theorem start_v (a : ℕ+) (b : ℕ+) : v (start a b) = (↑a, ↑b) := sorry

def finish (u : xgcd_type) : xgcd_type :=
  mk (wp u) ((wp u + 1) * qp u + x u) (y u) (y u * qp u + zp u) (bp u) (bp u)

theorem finish_is_reduced (u : xgcd_type) : is_reduced (finish u) :=
  id (Eq.refl (ap (finish u)))

theorem finish_is_special (u : xgcd_type) (hs : is_special u) : is_special (finish u) := sorry

theorem finish_v (u : xgcd_type) (hr : r u = 0) : v (finish u) = v u := sorry

/-- This is the main reduction step, which is used when u.r ≠ 0, or
 equivalently b does not divide a. -/
def step (u : xgcd_type) : xgcd_type :=
  mk (y u * q u + zp u) (y u) ((wp u + 1) * q u + x u) (wp u) (bp u) (r u - 1)

/-- We will apply the above step recursively.  The following result
 is used to ensure that the process terminates. -/
theorem step_wf (u : xgcd_type) (hr : r u ≠ 0) : sizeof (step u) < sizeof u := sorry

theorem step_is_special (u : xgcd_type) (hs : is_special u) : is_special (step u) := sorry

/-- The reduction step does not change the product vector. -/
theorem step_v (u : xgcd_type) (hr : r u ≠ 0) : v (step u) = prod.swap (v u) := sorry

/-- We can now define the full reduction function, which applies
 step as long as possible, and then applies finish. Note that the
 "have" statement puts a fact in the local context, and the
 equation compiler uses this fact to help construct the full
 definition in terms of well-founded recursion.  The same fact
 needs to be introduced in all the inductive proofs of properties
 given below. -/
def reduce : xgcd_type → xgcd_type :=
  sorry

theorem reduce_a {u : xgcd_type} (h : r u = 0) : reduce u = finish u := sorry

theorem reduce_b {u : xgcd_type} (h : r u ≠ 0) : reduce u = flip (reduce (step u)) := sorry

theorem reduce_reduced (u : xgcd_type) : is_reduced (reduce u) := sorry

theorem reduce_reduced' (u : xgcd_type) : is_reduced' (reduce u) :=
  iff.mp (is_reduced_iff (reduce u)) (reduce_reduced u)

theorem reduce_special (u : xgcd_type) : is_special u → is_special (reduce u) := sorry

theorem reduce_special' (u : xgcd_type) (hs : is_special u) : is_special' (reduce u) :=
  iff.mp (is_special_iff (reduce u)) (reduce_special u hs)

theorem reduce_v (u : xgcd_type) : v (reduce u) = v u := sorry

end xgcd_type


def xgcd (a : ℕ+) (b : ℕ+) : xgcd_type :=
  xgcd_type.reduce (xgcd_type.start a b)

def gcd_d (a : ℕ+) (b : ℕ+) : ℕ+ :=
  xgcd_type.a (xgcd a b)

def gcd_w (a : ℕ+) (b : ℕ+) : ℕ+ :=
  xgcd_type.w (xgcd a b)

def gcd_x (a : ℕ+) (b : ℕ+) : ℕ :=
  xgcd_type.x (xgcd a b)

def gcd_y (a : ℕ+) (b : ℕ+) : ℕ :=
  xgcd_type.y (xgcd a b)

def gcd_z (a : ℕ+) (b : ℕ+) : ℕ+ :=
  xgcd_type.z (xgcd a b)

def gcd_a' (a : ℕ+) (b : ℕ+) : ℕ+ :=
  nat.succ_pnat (xgcd_type.wp (xgcd a b) + xgcd_type.x (xgcd a b))

def gcd_b' (a : ℕ+) (b : ℕ+) : ℕ+ :=
  nat.succ_pnat (xgcd_type.y (xgcd a b) + xgcd_type.zp (xgcd a b))

theorem gcd_a'_coe (a : ℕ+) (b : ℕ+) : ↑(gcd_a' a b) = ↑(gcd_w a b) + gcd_x a b := sorry

theorem gcd_b'_coe (a : ℕ+) (b : ℕ+) : ↑(gcd_b' a b) = gcd_y a b + ↑(gcd_z a b) := sorry

theorem gcd_props (a : ℕ+) (b : ℕ+) : let d : ℕ+ := gcd_d a b;
let w : ℕ+ := gcd_w a b;
let x : ℕ := gcd_x a b;
let y : ℕ := gcd_y a b;
let z : ℕ+ := gcd_z a b;
let a' : ℕ+ := gcd_a' a b;
let b' : ℕ+ := gcd_b' a b;
w * z = nat.succ_pnat (x * y) ∧
  a = a' * d ∧
    b = b' * d ∧
      z * a' = nat.succ_pnat (x * ↑b') ∧
        w * b' = nat.succ_pnat (y * ↑a') ∧ ↑z * ↑a = x * ↑b + ↑d ∧ ↑w * ↑b = y * ↑a + ↑d := sorry

theorem gcd_eq (a : ℕ+) (b : ℕ+) : gcd_d a b = gcd a b := sorry

theorem gcd_det_eq (a : ℕ+) (b : ℕ+) : gcd_w a b * gcd_z a b = nat.succ_pnat (gcd_x a b * gcd_y a b) :=
  and.left (gcd_props a b)

theorem gcd_a_eq (a : ℕ+) (b : ℕ+) : a = gcd_a' a b * gcd a b :=
  gcd_eq a b ▸ and.left (and.right (gcd_props a b))

theorem gcd_b_eq (a : ℕ+) (b : ℕ+) : b = gcd_b' a b * gcd a b :=
  gcd_eq a b ▸ and.left (and.right (and.right (gcd_props a b)))

theorem gcd_rel_left' (a : ℕ+) (b : ℕ+) : gcd_z a b * gcd_a' a b = nat.succ_pnat (gcd_x a b * ↑(gcd_b' a b)) :=
  and.left (and.right (and.right (and.right (gcd_props a b))))

theorem gcd_rel_right' (a : ℕ+) (b : ℕ+) : gcd_w a b * gcd_b' a b = nat.succ_pnat (gcd_y a b * ↑(gcd_a' a b)) :=
  and.left (and.right (and.right (and.right (and.right (gcd_props a b)))))

theorem gcd_rel_left (a : ℕ+) (b : ℕ+) : ↑(gcd_z a b) * ↑a = gcd_x a b * ↑b + ↑(gcd a b) :=
  gcd_eq a b ▸ and.left (and.right (and.right (and.right (and.right (and.right (gcd_props a b))))))

theorem gcd_rel_right (a : ℕ+) (b : ℕ+) : ↑(gcd_w a b) * ↑b = gcd_y a b * ↑a + ↑(gcd a b) :=
  gcd_eq a b ▸ and.right (and.right (and.right (and.right (and.right (and.right (gcd_props a b))))))

