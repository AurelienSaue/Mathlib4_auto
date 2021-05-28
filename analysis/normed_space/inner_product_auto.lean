/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Sébastien Gouëzel, Frédéric Dupuis, Heather Macbeth
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.linear_algebra.bilinear_form
import Mathlib.linear_algebra.sesquilinear_form
import Mathlib.topology.metric_space.pi_Lp
import Mathlib.data.complex.is_R_or_C
import PostPort

universes u_4 u_5 l u_1 u_3 u_2 

namespace Mathlib

/-!
# Inner Product Space

This file defines inner product spaces and proves its basic properties.

An inner product space is a vector space endowed with an inner product. It generalizes the notion of
dot product in `ℝ^n` and provides the means of defining the length of a vector and the angle between
two vectors. In particular vectors `x` and `y` are orthogonal if their inner product equals zero.
We define both the real and complex cases at the same time using the `is_R_or_C` typeclass.

## Main results

- We define the class `inner_product_space 𝕜 E` extending `normed_space 𝕜 E` with a number of basic
  properties, most notably the Cauchy-Schwarz inequality. Here `𝕜` is understood to be either `ℝ`
  or `ℂ`, through the `is_R_or_C` typeclass.
- We show that if `f i` is an inner product space for each `i`, then so is `Π i, f i`
- We define `euclidean_space 𝕜 n` to be `n → 𝕜` for any `fintype n`, and show that
  this an inner product space.
- Existence of orthogonal projection onto nonempty complete subspace:
  Let `u` be a point in an inner product space, and let `K` be a nonempty complete subspace.
  Then there exists a unique `v` in `K` that minimizes the distance `∥u - v∥` to `u`.
  The point `v` is usually called the orthogonal projection of `u` onto `K`.
- We define `orthonormal`, a predicate on a function `v : ι → E`.  We prove the existence of a
  maximal orthonormal set, `exists_maximal_orthonormal`, and also prove that a maximal orthonormal
  set is a basis (`maximal_orthonormal_iff_is_basis_of_finite_dimensional`), if `E` is finite-
  dimensional, or in general (`maximal_orthonormal_iff_dense_span`) a set whose span is dense
  (i.e., a Hilbert basis, although we do not make that definition).

## Notation

We globally denote the real and complex inner products by `⟪·, ·⟫_ℝ` and `⟪·, ·⟫_ℂ` respectively.
We also provide two notation namespaces: `real_inner_product_space`, `complex_inner_product_space`,
which respectively introduce the plain notation `⟪·, ·⟫` for the the real and complex inner product.

The orthogonal complement of a submodule `K` is denoted by `Kᗮ`.

## Implementation notes

We choose the convention that inner products are conjugate linear in the first argument and linear
in the second.

## TODO

- Fix the section on the existence of minimizers and orthogonal projections to make sure that it
  also applies in the complex case.

## Tags

inner product space, norm

## References
*  [Clément & Martin, *The Lax-Milgram Theorem. A detailed proof to be formalized in Coq*]
*  [Clément & Martin, *A Coq formal proof of the Lax–Milgram theorem*]

The Coq code is available at the following address: <http://www.lri.fr/~sboldo/elfic/index.html>
-/

/-- Syntactic typeclass for types endowed with an inner product -/
class has_inner (𝕜 : Type u_4) (E : Type u_5) 
where
  inner : E → E → 𝕜

/--
An inner product space is a vector space with an additional operation called inner product.
The norm could be derived from the inner product, instead we require the existence of a norm and
the fact that `∥x∥^2 = re ⟪x, x⟫` to be able to put instances on `𝕂` or product
spaces.

To construct a norm from an inner product, see `inner_product_space.of_core`.
-/
class inner_product_space (𝕜 : Type u_4) (E : Type u_5) [is_R_or_C 𝕜] 
extends normed_space 𝕜 E, has_inner 𝕜 E, normed_group E
where
  norm_sq_eq_inner : ∀ (x : E), norm x ^ bit0 1 = coe_fn is_R_or_C.re (inner x x)
  conj_sym : ∀ (x y : E), coe_fn is_R_or_C.conj (inner y x) = inner x y
  nonneg_im : ∀ (x : E), coe_fn is_R_or_C.im (inner x x) = 0
  add_left : ∀ (x y z : E), inner (x + y) z = inner x z + inner y z
  smul_left : ∀ (x y : E) (r : 𝕜), inner (r • x) y = coe_fn is_R_or_C.conj r * inner x y

-- note [is_R_or_C instance]

/-!
### Constructing a normed space structure from an inner product

In the definition of an inner product space, we require the existence of a norm, which is equal
(but maybe not defeq) to the square root of the scalar product. This makes it possible to put
an inner product space structure on spaces with a preexisting norm (for instance `ℝ`), with good
properties. However, sometimes, one would like to define the norm starting only from a well-behaved
scalar product. This is what we implement in this paragraph, starting from a structure
`inner_product_space.core` stating that we have a nice scalar product.

Our goal here is not to develop a whole theory with all the supporting API, as this will be done
below for `inner_product_space`. Instead, we implement the bare minimum to go as directly as
possible to the construction of the norm and the proof of the triangular inequality.

Warning: Do not use this `core` structure if the space you are interested in already has a norm
instance defined on it, otherwise this will create a second non-defeq norm instance!
-/

/-- A structure requiring that a scalar product is positive definite and symmetric, from which one
can construct an `inner_product_space` instance in `inner_product_space.of_core`. -/
class inner_product_space.core (𝕜 : Type u_4) (F : Type u_5) [is_R_or_C 𝕜] [add_comm_group F] [semimodule 𝕜 F] 
where
  inner : F → F → 𝕜
  conj_sym : ∀ (x y : F), coe_fn is_R_or_C.conj (inner y x) = inner x y
  nonneg_im : ∀ (x : F), coe_fn is_R_or_C.im (inner x x) = 0
  nonneg_re : ∀ (x : F), 0 ≤ coe_fn is_R_or_C.re (inner x x)
  definite : ∀ (x : F), inner x x = 0 → x = 0
  add_left : ∀ (x y z : F), inner (x + y) z = inner x z + inner y z
  smul_left : ∀ (x y : F) (r : 𝕜), inner (r • x) y = coe_fn is_R_or_C.conj r * inner x y

/- We set `inner_product_space.core` to be a class as we will use it as such in the construction
of the normed space structure that it produces. However, all the instances we will use will be
local to this proof. -/

namespace inner_product_space.of_core


/-- Inner product defined by the `inner_product_space.core` structure. -/
def to_has_inner {𝕜 : Type u_1} {F : Type u_3} [is_R_or_C 𝕜] [add_comm_group F] [semimodule 𝕜 F] [c : core 𝕜 F] : has_inner 𝕜 F :=
  has_inner.mk (core.inner c)

/-- The norm squared function for `inner_product_space.core` structure. -/
def norm_sq {𝕜 : Type u_1} {F : Type u_3} [is_R_or_C 𝕜] [add_comm_group F] [semimodule 𝕜 F] [c : core 𝕜 F] (x : F) : ℝ :=
  coe_fn is_R_or_C.re (inner x x)

theorem inner_conj_sym {𝕜 : Type u_1} {F : Type u_3} [is_R_or_C 𝕜] [add_comm_group F] [semimodule 𝕜 F] [c : core 𝕜 F] (x : F) (y : F) : coe_fn is_R_or_C.conj (inner y x) = inner x y :=
  core.conj_sym c x y

theorem inner_self_nonneg {𝕜 : Type u_1} {F : Type u_3} [is_R_or_C 𝕜] [add_comm_group F] [semimodule 𝕜 F] [c : core 𝕜 F] {x : F} : 0 ≤ coe_fn is_R_or_C.re (inner x x) :=
  core.nonneg_re c x

theorem inner_self_nonneg_im {𝕜 : Type u_1} {F : Type u_3} [is_R_or_C 𝕜] [add_comm_group F] [semimodule 𝕜 F] [c : core 𝕜 F] {x : F} : coe_fn is_R_or_C.im (inner x x) = 0 :=
  core.nonneg_im c x

theorem inner_self_im_zero {𝕜 : Type u_1} {F : Type u_3} [is_R_or_C 𝕜] [add_comm_group F] [semimodule 𝕜 F] [c : core 𝕜 F] {x : F} : coe_fn is_R_or_C.im (inner x x) = 0 :=
  core.nonneg_im c x

theorem inner_add_left {𝕜 : Type u_1} {F : Type u_3} [is_R_or_C 𝕜] [add_comm_group F] [semimodule 𝕜 F] [c : core 𝕜 F] {x : F} {y : F} {z : F} : inner (x + y) z = inner x z + inner y z :=
  core.add_left c x y z

theorem inner_add_right {𝕜 : Type u_1} {F : Type u_3} [is_R_or_C 𝕜] [add_comm_group F] [semimodule 𝕜 F] [c : core 𝕜 F] {x : F} {y : F} {z : F} : inner x (y + z) = inner x y + inner x z := sorry

theorem inner_norm_sq_eq_inner_self {𝕜 : Type u_1} {F : Type u_3} [is_R_or_C 𝕜] [add_comm_group F] [semimodule 𝕜 F] [c : core 𝕜 F] (x : F) : ↑(norm_sq x) = inner x x := sorry

theorem inner_re_symm {𝕜 : Type u_1} {F : Type u_3} [is_R_or_C 𝕜] [add_comm_group F] [semimodule 𝕜 F] [c : core 𝕜 F] {x : F} {y : F} : coe_fn is_R_or_C.re (inner x y) = coe_fn is_R_or_C.re (inner y x) := sorry

theorem inner_im_symm {𝕜 : Type u_1} {F : Type u_3} [is_R_or_C 𝕜] [add_comm_group F] [semimodule 𝕜 F] [c : core 𝕜 F] {x : F} {y : F} : coe_fn is_R_or_C.im (inner x y) = -coe_fn is_R_or_C.im (inner y x) := sorry

theorem inner_smul_left {𝕜 : Type u_1} {F : Type u_3} [is_R_or_C 𝕜] [add_comm_group F] [semimodule 𝕜 F] [c : core 𝕜 F] {x : F} {y : F} {r : 𝕜} : inner (r • x) y = coe_fn is_R_or_C.conj r * inner x y :=
  core.smul_left c x y r

theorem inner_smul_right {𝕜 : Type u_1} {F : Type u_3} [is_R_or_C 𝕜] [add_comm_group F] [semimodule 𝕜 F] [c : core 𝕜 F] {x : F} {y : F} {r : 𝕜} : inner x (r • y) = r * inner x y := sorry

theorem inner_zero_left {𝕜 : Type u_1} {F : Type u_3} [is_R_or_C 𝕜] [add_comm_group F] [semimodule 𝕜 F] [c : core 𝕜 F] {x : F} : inner 0 x = 0 := sorry

theorem inner_zero_right {𝕜 : Type u_1} {F : Type u_3} [is_R_or_C 𝕜] [add_comm_group F] [semimodule 𝕜 F] [c : core 𝕜 F] {x : F} : inner x 0 = 0 := sorry

theorem inner_self_eq_zero {𝕜 : Type u_1} {F : Type u_3} [is_R_or_C 𝕜] [add_comm_group F] [semimodule 𝕜 F] [c : core 𝕜 F] {x : F} : inner x x = 0 ↔ x = 0 :=
  { mp := core.definite c x, mpr := fun (ᾰ : x = 0) => Eq._oldrec inner_zero_left (Eq.symm ᾰ) }

theorem inner_self_re_to_K {𝕜 : Type u_1} {F : Type u_3} [is_R_or_C 𝕜] [add_comm_group F] [semimodule 𝕜 F] [c : core 𝕜 F] {x : F} : ↑(coe_fn is_R_or_C.re (inner x x)) = inner x x := sorry

theorem inner_abs_conj_sym {𝕜 : Type u_1} {F : Type u_3} [is_R_or_C 𝕜] [add_comm_group F] [semimodule 𝕜 F] [c : core 𝕜 F] {x : F} {y : F} : is_R_or_C.abs (inner x y) = is_R_or_C.abs (inner y x) := sorry

theorem inner_neg_left {𝕜 : Type u_1} {F : Type u_3} [is_R_or_C 𝕜] [add_comm_group F] [semimodule 𝕜 F] [c : core 𝕜 F] {x : F} {y : F} : inner (-x) y = -inner x y := sorry

theorem inner_neg_right {𝕜 : Type u_1} {F : Type u_3} [is_R_or_C 𝕜] [add_comm_group F] [semimodule 𝕜 F] [c : core 𝕜 F] {x : F} {y : F} : inner x (-y) = -inner x y := sorry

theorem inner_sub_left {𝕜 : Type u_1} {F : Type u_3} [is_R_or_C 𝕜] [add_comm_group F] [semimodule 𝕜 F] [c : core 𝕜 F] {x : F} {y : F} {z : F} : inner (x - y) z = inner x z - inner y z := sorry

theorem inner_sub_right {𝕜 : Type u_1} {F : Type u_3} [is_R_or_C 𝕜] [add_comm_group F] [semimodule 𝕜 F] [c : core 𝕜 F] {x : F} {y : F} {z : F} : inner x (y - z) = inner x y - inner x z := sorry

theorem inner_mul_conj_re_abs {𝕜 : Type u_1} {F : Type u_3} [is_R_or_C 𝕜] [add_comm_group F] [semimodule 𝕜 F] [c : core 𝕜 F] {x : F} {y : F} : coe_fn is_R_or_C.re (inner x y * inner y x) = is_R_or_C.abs (inner x y * inner y x) := sorry

/-- Expand `inner (x + y) (x + y)` -/
theorem inner_add_add_self {𝕜 : Type u_1} {F : Type u_3} [is_R_or_C 𝕜] [add_comm_group F] [semimodule 𝕜 F] [c : core 𝕜 F] {x : F} {y : F} : inner (x + y) (x + y) = inner x x + inner x y + inner y x + inner y y := sorry

/- Expand `inner (x - y) (x - y)` -/

theorem inner_sub_sub_self {𝕜 : Type u_1} {F : Type u_3} [is_R_or_C 𝕜] [add_comm_group F] [semimodule 𝕜 F] [c : core 𝕜 F] {x : F} {y : F} : inner (x - y) (x - y) = inner x x - inner x y - inner y x + inner y y := sorry

/--
Cauchy–Schwarz inequality. This proof follows "Proof 2" on Wikipedia.
We need this for the `core` structure to prove the triangle inequality below when
showing the core is a normed group.
-/
theorem inner_mul_inner_self_le {𝕜 : Type u_1} {F : Type u_3} [is_R_or_C 𝕜] [add_comm_group F] [semimodule 𝕜 F] [c : core 𝕜 F] (x : F) (y : F) : is_R_or_C.abs (inner x y) * is_R_or_C.abs (inner y x) ≤
  coe_fn is_R_or_C.re (inner x x) * coe_fn is_R_or_C.re (inner y y) := sorry

/-- Norm constructed from a `inner_product_space.core` structure, defined to be the square root
of the scalar product. -/
def to_has_norm {𝕜 : Type u_1} {F : Type u_3} [is_R_or_C 𝕜] [add_comm_group F] [semimodule 𝕜 F] [c : core 𝕜 F] : has_norm F :=
  has_norm.mk fun (x : F) => real.sqrt (coe_fn is_R_or_C.re (inner x x))

theorem norm_eq_sqrt_inner {𝕜 : Type u_1} {F : Type u_3} [is_R_or_C 𝕜] [add_comm_group F] [semimodule 𝕜 F] [c : core 𝕜 F] (x : F) : norm x = real.sqrt (coe_fn is_R_or_C.re (inner x x)) :=
  rfl

theorem inner_self_eq_norm_square {𝕜 : Type u_1} {F : Type u_3} [is_R_or_C 𝕜] [add_comm_group F] [semimodule 𝕜 F] [c : core 𝕜 F] (x : F) : coe_fn is_R_or_C.re (inner x x) = norm x * norm x := sorry

theorem sqrt_norm_sq_eq_norm {𝕜 : Type u_1} {F : Type u_3} [is_R_or_C 𝕜] [add_comm_group F] [semimodule 𝕜 F] [c : core 𝕜 F] {x : F} : real.sqrt (norm_sq x) = norm x :=
  rfl

/-- Cauchy–Schwarz inequality with norm -/
theorem abs_inner_le_norm {𝕜 : Type u_1} {F : Type u_3} [is_R_or_C 𝕜] [add_comm_group F] [semimodule 𝕜 F] [c : core 𝕜 F] (x : F) (y : F) : is_R_or_C.abs (inner x y) ≤ norm x * norm y := sorry

/-- Normed group structure constructed from an `inner_product_space.core` structure -/
def to_normed_group {𝕜 : Type u_1} {F : Type u_3} [is_R_or_C 𝕜] [add_comm_group F] [semimodule 𝕜 F] [c : core 𝕜 F] : normed_group F :=
  normed_group.of_core F sorry

/-- Normed space structure constructed from a `inner_product_space.core` structure -/
def to_normed_space {𝕜 : Type u_1} {F : Type u_3} [is_R_or_C 𝕜] [add_comm_group F] [semimodule 𝕜 F] [c : core 𝕜 F] : normed_space 𝕜 F :=
  normed_space.mk sorry

end inner_product_space.of_core


/-- Given a `inner_product_space.core` structure on a space, one can use it to turn
the space into an inner product space, constructing the norm out of the inner product -/
def inner_product_space.of_core {𝕜 : Type u_1} {F : Type u_3} [is_R_or_C 𝕜] [add_comm_group F] [semimodule 𝕜 F] (c : inner_product_space.core 𝕜 F) : inner_product_space 𝕜 F :=
  let _inst : normed_group F := sorry;
  let _inst_4 : normed_space 𝕜 F := sorry;
  inner_product_space.mk sorry (inner_product_space.core.conj_sym c) (inner_product_space.core.nonneg_im c)
    (inner_product_space.core.add_left c) (inner_product_space.core.smul_left c)

/-! ### Properties of inner product spaces -/

theorem inner_conj_sym {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (x : E) (y : E) : coe_fn is_R_or_C.conj (inner y x) = inner x y :=
  inner_product_space.conj_sym x y

theorem real_inner_comm {F : Type u_3} [inner_product_space ℝ F] (x : F) (y : F) : inner y x = inner x y :=
  inner_conj_sym x y

theorem inner_eq_zero_sym {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {x : E} {y : E} : inner x y = 0 ↔ inner y x = 0 := sorry

theorem inner_self_nonneg_im {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {x : E} : coe_fn is_R_or_C.im (inner x x) = 0 :=
  inner_product_space.nonneg_im x

theorem inner_self_im_zero {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {x : E} : coe_fn is_R_or_C.im (inner x x) = 0 :=
  inner_product_space.nonneg_im x

theorem inner_add_left {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {x : E} {y : E} {z : E} : inner (x + y) z = inner x z + inner y z :=
  inner_product_space.add_left x y z

theorem inner_add_right {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {x : E} {y : E} {z : E} : inner x (y + z) = inner x y + inner x z := sorry

theorem inner_re_symm {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {x : E} {y : E} : coe_fn is_R_or_C.re (inner x y) = coe_fn is_R_or_C.re (inner y x) := sorry

theorem inner_im_symm {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {x : E} {y : E} : coe_fn is_R_or_C.im (inner x y) = -coe_fn is_R_or_C.im (inner y x) := sorry

theorem inner_smul_left {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {x : E} {y : E} {r : 𝕜} : inner (r • x) y = coe_fn is_R_or_C.conj r * inner x y :=
  inner_product_space.smul_left x y r

theorem real_inner_smul_left {F : Type u_3} [inner_product_space ℝ F] {x : F} {y : F} {r : ℝ} : inner (r • x) y = r * inner x y :=
  inner_smul_left

theorem inner_smul_real_left {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {x : E} {y : E} {r : ℝ} : inner (↑r • x) y = r • inner x y := sorry

theorem inner_smul_right {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {x : E} {y : E} {r : 𝕜} : inner x (r • y) = r * inner x y := sorry

theorem real_inner_smul_right {F : Type u_3} [inner_product_space ℝ F] {x : F} {y : F} {r : ℝ} : inner x (r • y) = r * inner x y :=
  inner_smul_right

theorem inner_smul_real_right {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {x : E} {y : E} {r : ℝ} : inner x (↑r • y) = r • inner x y :=
  eq.mpr (id (Eq._oldrec (Eq.refl (inner x (↑r • y) = r • inner x y)) inner_smul_right))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑r * inner x y = r • inner x y)) (algebra.smul_def r (inner x y))))
      (Eq.refl (↑r * inner x y)))

/-- The inner product as a sesquilinear form. -/
def sesq_form_of_inner {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] : sesq_form 𝕜 E (is_R_or_C.conj_to_ring_equiv 𝕜) :=
  sesq_form.mk (fun (x y : E) => inner y x) sorry sorry sorry sorry

/-- The real inner product as a bilinear form. -/
def bilin_form_of_real_inner {F : Type u_3} [inner_product_space ℝ F] : bilin_form ℝ F :=
  bilin_form.mk inner sorry sorry sorry sorry

/-- An inner product with a sum on the left. -/
theorem sum_inner {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {ι : Type u_3} (s : finset ι) (f : ι → E) (x : E) : inner (finset.sum s fun (i : ι) => f i) x = finset.sum s fun (i : ι) => inner (f i) x :=
  sesq_form.map_sum_right sesq_form_of_inner s (fun (i : ι) => f i) x

/-- An inner product with a sum on the right. -/
theorem inner_sum {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {ι : Type u_3} (s : finset ι) (f : ι → E) (x : E) : inner x (finset.sum s fun (i : ι) => f i) = finset.sum s fun (i : ι) => inner x (f i) :=
  sesq_form.map_sum_left sesq_form_of_inner s (fun (i : ι) => f i) x

/-- An inner product with a sum on the left, `finsupp` version. -/
theorem finsupp.sum_inner {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {ι : Type u_3} (l : ι →₀ 𝕜) (v : ι → E) (x : E) : inner (finsupp.sum l fun (i : ι) (a : 𝕜) => a • v i) x =
  finsupp.sum l fun (i : ι) (a : 𝕜) => coe_fn is_R_or_C.conj a • inner (v i) x := sorry

/-- An inner product with a sum on the right, `finsupp` version. -/
theorem finsupp.inner_sum {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {ι : Type u_3} (l : ι →₀ 𝕜) (v : ι → E) (x : E) : inner x (finsupp.sum l fun (i : ι) (a : 𝕜) => a • v i) = finsupp.sum l fun (i : ι) (a : 𝕜) => a • inner x (v i) := sorry

@[simp] theorem inner_zero_left {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {x : E} : inner 0 x = 0 := sorry

theorem inner_re_zero_left {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {x : E} : coe_fn is_R_or_C.re (inner 0 x) = 0 := sorry

@[simp] theorem inner_zero_right {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {x : E} : inner x 0 = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (inner x 0 = 0)) (Eq.symm (inner_conj_sym x 0))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn is_R_or_C.conj (inner 0 x) = 0)) inner_zero_left))
      (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn is_R_or_C.conj 0 = 0)) (ring_hom.map_zero is_R_or_C.conj))) (Eq.refl 0)))

theorem inner_re_zero_right {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {x : E} : coe_fn is_R_or_C.re (inner x 0) = 0 := sorry

theorem inner_self_nonneg {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {x : E} : 0 ≤ coe_fn is_R_or_C.re (inner x x) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (0 ≤ coe_fn is_R_or_C.re (inner x x))) (Eq.symm (norm_sq_eq_inner x))))
    (pow_nonneg (norm_nonneg x) (bit0 1))

theorem real_inner_self_nonneg {F : Type u_3} [inner_product_space ℝ F] {x : F} : 0 ≤ inner x x :=
  inner_self_nonneg

@[simp] theorem inner_self_eq_zero {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {x : E} : inner x x = 0 ↔ x = 0 := sorry

@[simp] theorem inner_self_nonpos {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {x : E} : coe_fn is_R_or_C.re (inner x x) ≤ 0 ↔ x = 0 := sorry

theorem real_inner_self_nonpos {F : Type u_3} [inner_product_space ℝ F] {x : F} : inner x x ≤ 0 ↔ x = 0 := sorry

@[simp] theorem inner_self_re_to_K {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {x : E} : ↑(coe_fn is_R_or_C.re (inner x x)) = inner x x := sorry

theorem inner_self_eq_norm_sq_to_K {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (x : E) : inner x x = ↑(norm x) ^ bit0 1 := sorry

theorem inner_self_re_abs {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {x : E} : coe_fn is_R_or_C.re (inner x x) = is_R_or_C.abs (inner x x) := sorry

theorem inner_self_abs_to_K {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {x : E} : ↑(is_R_or_C.abs (inner x x)) = inner x x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑(is_R_or_C.abs (inner x x)) = inner x x)) (Eq.symm inner_self_re_abs)))
    inner_self_re_to_K

theorem real_inner_self_abs {F : Type u_3} [inner_product_space ℝ F] {x : F} : abs (inner x x) = inner x x := sorry

theorem inner_abs_conj_sym {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {x : E} {y : E} : is_R_or_C.abs (inner x y) = is_R_or_C.abs (inner y x) := sorry

@[simp] theorem inner_neg_left {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {x : E} {y : E} : inner (-x) y = -inner x y := sorry

@[simp] theorem inner_neg_right {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {x : E} {y : E} : inner x (-y) = -inner x y := sorry

theorem inner_neg_neg {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {x : E} {y : E} : inner (-x) (-y) = inner x y := sorry

@[simp] theorem inner_self_conj {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {x : E} : coe_fn is_R_or_C.conj (inner x x) = inner x x := sorry

theorem inner_sub_left {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {x : E} {y : E} {z : E} : inner (x - y) z = inner x z - inner y z := sorry

theorem inner_sub_right {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {x : E} {y : E} {z : E} : inner x (y - z) = inner x y - inner x z := sorry

theorem inner_mul_conj_re_abs {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {x : E} {y : E} : coe_fn is_R_or_C.re (inner x y * inner y x) = is_R_or_C.abs (inner x y * inner y x) := sorry

/-- Expand `⟪x + y, x + y⟫` -/
theorem inner_add_add_self {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {x : E} {y : E} : inner (x + y) (x + y) = inner x x + inner x y + inner y x + inner y y := sorry

/-- Expand `⟪x + y, x + y⟫_ℝ` -/
theorem real_inner_add_add_self {F : Type u_3} [inner_product_space ℝ F] {x : F} {y : F} : inner (x + y) (x + y) = inner x x + bit0 1 * inner x y + inner y y := sorry

/- Expand `⟪x - y, x - y⟫` -/

theorem inner_sub_sub_self {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {x : E} {y : E} : inner (x - y) (x - y) = inner x x - inner x y - inner y x + inner y y := sorry

/-- Expand `⟪x - y, x - y⟫_ℝ` -/
theorem real_inner_sub_sub_self {F : Type u_3} [inner_product_space ℝ F] {x : F} {y : F} : inner (x - y) (x - y) = inner x x - bit0 1 * inner x y + inner y y := sorry

/-- Parallelogram law -/
theorem parallelogram_law {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {x : E} {y : E} : inner (x + y) (x + y) + inner (x - y) (x - y) = bit0 1 * (inner x x + inner y y) := sorry

/-- Cauchy–Schwarz inequality. This proof follows "Proof 2" on Wikipedia. -/
theorem inner_mul_inner_self_le {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (x : E) (y : E) : is_R_or_C.abs (inner x y) * is_R_or_C.abs (inner y x) ≤
  coe_fn is_R_or_C.re (inner x x) * coe_fn is_R_or_C.re (inner y y) := sorry

/-- Cauchy–Schwarz inequality for real inner products. -/
theorem real_inner_mul_inner_self_le {F : Type u_3} [inner_product_space ℝ F] (x : F) (y : F) : inner x y * inner x y ≤ inner x x * inner y y := sorry

/-- A family of vectors is linearly independent if they are nonzero
and orthogonal. -/
theorem linear_independent_of_ne_zero_of_inner_eq_zero {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {ι : Type u_3} {v : ι → E} (hz : ∀ (i : ι), v i ≠ 0) (ho : ∀ (i j : ι), i ≠ j → inner (v i) (v j) = 0) : linear_independent 𝕜 v := sorry

/-- An orthonormal set of vectors in an `inner_product_space` -/
def orthonormal (𝕜 : Type u_1) {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {ι : Type u_4} (v : ι → E)  :=
  (∀ (i : ι), norm (v i) = 1) ∧ ∀ {i j : ι}, i ≠ j → inner (v i) (v j) = 0

/-- `if ... then ... else` characterization of an indexed set of vectors being orthonormal.  (Inner
product equals Kronecker delta.) -/
theorem orthonormal_iff_ite {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {ι : Type u_4} {v : ι → E} : orthonormal 𝕜 v ↔ ∀ (i j : ι), inner (v i) (v j) = ite (i = j) 1 0 := sorry

/-- `if ... then ... else` characterization of a set of vectors being orthonormal.  (Inner product
equals Kronecker delta.) -/
theorem orthonormal_subtype_iff_ite {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {s : set E} : orthonormal 𝕜 coe ↔ ∀ (v : E), v ∈ s → ∀ (w : E), w ∈ s → inner v w = ite (v = w) 1 0 := sorry

/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
theorem orthonormal.inner_right_finsupp {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {ι : Type u_4} {v : ι → E} (hv : orthonormal 𝕜 v) (l : ι →₀ 𝕜) (i : ι) : inner (v i) (coe_fn (finsupp.total ι E 𝕜 v) l) = coe_fn l i := sorry

/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
theorem orthonormal.inner_left_finsupp {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {ι : Type u_4} {v : ι → E} (hv : orthonormal 𝕜 v) (l : ι →₀ 𝕜) (i : ι) : inner (coe_fn (finsupp.total ι E 𝕜 v) l) (v i) = coe_fn is_R_or_C.conj (coe_fn l i) := sorry

/-- An orthonormal set is linearly independent. -/
theorem orthonormal.linear_independent {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {ι : Type u_4} {v : ι → E} (hv : orthonormal 𝕜 v) : linear_independent 𝕜 v := sorry

/-- A linear combination of some subset of an orthonormal set is orthogonal to other members of the
set. -/
theorem orthonormal.inner_finsupp_eq_zero {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {ι : Type u_4} {v : ι → E} (hv : orthonormal 𝕜 v) {s : set ι} {i : ι} (hi : ¬i ∈ s) {l : ι →₀ 𝕜} (hl : l ∈ finsupp.supported 𝕜 𝕜 s) : inner (coe_fn (finsupp.total ι E 𝕜 v) l) (v i) = 0 := sorry

/- The material that follows, culminating in the existence of a maximal orthonormal subset, is
adapted from the corresponding development of the theory of linearly independents sets.  See
`exists_linear_independent` in particular. -/

theorem orthonormal_empty (𝕜 : Type u_1) (E : Type u_2) [is_R_or_C 𝕜] [inner_product_space 𝕜 E] : orthonormal 𝕜 fun (x : ↥∅) => ↑x := sorry

theorem orthonormal_Union_of_directed {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {η : Type u_3} {s : η → set E} (hs : directed has_subset.subset s) (h : ∀ (i : η), orthonormal 𝕜 fun (x : ↥(s i)) => ↑x) : orthonormal 𝕜 fun (x : ↥(set.Union fun (i : η) => s i)) => ↑x := sorry

theorem orthonormal_sUnion_of_directed {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {s : set (set E)} (hs : directed_on has_subset.subset s) (h : ∀ (a : set E), a ∈ s → orthonormal 𝕜 fun (x : ↥a) => ↑x) : orthonormal 𝕜 fun (x : ↥(⋃₀s)) => ↑x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (orthonormal 𝕜 fun (x : ↥(⋃₀s)) => ↑x)) set.sUnion_eq_Union))
    (orthonormal_Union_of_directed (directed_on.directed_coe hs)
      (eq.mpr (id (propext set_coe.forall)) (eq.mp (Eq.refl (∀ (a : set E), a ∈ s → orthonormal 𝕜 coe)) h)))

/-- Given an orthonormal set `v` of vectors in `E`, there exists a maximal orthonormal set
containing it. -/
theorem exists_maximal_orthonormal {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {s : set E} (hs : orthonormal 𝕜 coe) : ∃ (w : set E), ∃ (H : w ⊇ s), orthonormal 𝕜 coe ∧ ∀ (u : set E), u ⊇ w → orthonormal 𝕜 coe → u = w := sorry

theorem orthonormal.ne_zero {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {ι : Type u_4} {v : ι → E} (hv : orthonormal 𝕜 v) (i : ι) : v i ≠ 0 := sorry

theorem is_basis_of_orthonormal_of_card_eq_findim {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {ι : Type u_4} [fintype ι] [Nonempty ι] {v : ι → E} (hv : orthonormal 𝕜 v) (card_eq : fintype.card ι = finite_dimensional.findim 𝕜 E) : is_basis 𝕜 v :=
  is_basis_of_linear_independent_of_card_eq_findim (orthonormal.linear_independent hv) card_eq

theorem norm_eq_sqrt_inner {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (x : E) : norm x = real.sqrt (coe_fn is_R_or_C.re (inner x x)) := sorry

theorem norm_eq_sqrt_real_inner {F : Type u_3} [inner_product_space ℝ F] (x : F) : norm x = real.sqrt (inner x x) := sorry

theorem inner_self_eq_norm_square {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (x : E) : coe_fn is_R_or_C.re (inner x x) = norm x * norm x := sorry

theorem real_inner_self_eq_norm_square {F : Type u_3} [inner_product_space ℝ F] (x : F) : inner x x = norm x * norm x := sorry

/-- Expand the square -/
theorem norm_add_pow_two {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {x : E} {y : E} : norm (x + y) ^ bit0 1 = norm x ^ bit0 1 + bit0 1 * coe_fn is_R_or_C.re (inner x y) + norm y ^ bit0 1 := sorry

/-- Expand the square -/
theorem norm_add_pow_two_real {F : Type u_3} [inner_product_space ℝ F] {x : F} {y : F} : norm (x + y) ^ bit0 1 = norm x ^ bit0 1 + bit0 1 * inner x y + norm y ^ bit0 1 := sorry

/-- Expand the square -/
theorem norm_add_mul_self {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {x : E} {y : E} : norm (x + y) * norm (x + y) = norm x * norm x + bit0 1 * coe_fn is_R_or_C.re (inner x y) + norm y * norm y := sorry

/-- Expand the square -/
theorem norm_add_mul_self_real {F : Type u_3} [inner_product_space ℝ F] {x : F} {y : F} : norm (x + y) * norm (x + y) = norm x * norm x + bit0 1 * inner x y + norm y * norm y := sorry

/-- Expand the square -/
theorem norm_sub_pow_two {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {x : E} {y : E} : norm (x - y) ^ bit0 1 = norm x ^ bit0 1 - bit0 1 * coe_fn is_R_or_C.re (inner x y) + norm y ^ bit0 1 := sorry

/-- Expand the square -/
theorem norm_sub_pow_two_real {F : Type u_3} [inner_product_space ℝ F] {x : F} {y : F} : norm (x - y) ^ bit0 1 = norm x ^ bit0 1 - bit0 1 * inner x y + norm y ^ bit0 1 := sorry

/-- Expand the square -/
theorem norm_sub_mul_self {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {x : E} {y : E} : norm (x - y) * norm (x - y) = norm x * norm x - bit0 1 * coe_fn is_R_or_C.re (inner x y) + norm y * norm y := sorry

/-- Expand the square -/
theorem norm_sub_mul_self_real {F : Type u_3} [inner_product_space ℝ F] {x : F} {y : F} : norm (x - y) * norm (x - y) = norm x * norm x - bit0 1 * inner x y + norm y * norm y := sorry

/-- Cauchy–Schwarz inequality with norm -/
theorem abs_inner_le_norm {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (x : E) (y : E) : is_R_or_C.abs (inner x y) ≤ norm x * norm y := sorry

/-- Cauchy–Schwarz inequality with norm -/
theorem abs_real_inner_le_norm {F : Type u_3} [inner_product_space ℝ F] (x : F) (y : F) : abs (inner x y) ≤ norm x * norm y := sorry

/-- Cauchy–Schwarz inequality with norm -/
theorem real_inner_le_norm {F : Type u_3} [inner_product_space ℝ F] (x : F) (y : F) : inner x y ≤ norm x * norm y :=
  le_trans (le_abs_self (inner x y)) (abs_real_inner_le_norm x y)

theorem parallelogram_law_with_norm {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {x : E} {y : E} : norm (x + y) * norm (x + y) + norm (x - y) * norm (x - y) = bit0 1 * (norm x * norm x + norm y * norm y) := sorry

theorem parallelogram_law_with_norm_real {F : Type u_3} [inner_product_space ℝ F] {x : F} {y : F} : norm (x + y) * norm (x + y) + norm (x - y) * norm (x - y) = bit0 1 * (norm x * norm x + norm y * norm y) := sorry

/-- Polarization identity: The real part of the  inner product, in terms of the norm. -/
theorem re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (x : E) (y : E) : coe_fn is_R_or_C.re (inner x y) = (norm (x + y) * norm (x + y) - norm x * norm x - norm y * norm y) / bit0 1 := sorry

/-- Polarization identity: The real part of the  inner product, in terms of the norm. -/
theorem re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (x : E) (y : E) : coe_fn is_R_or_C.re (inner x y) = (norm x * norm x + norm y * norm y - norm (x - y) * norm (x - y)) / bit0 1 := sorry

/-- Polarization identity: The real part of the  inner product, in terms of the norm. -/
theorem re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (x : E) (y : E) : coe_fn is_R_or_C.re (inner x y) = (norm (x + y) * norm (x + y) - norm (x - y) * norm (x - y)) / bit0 (bit0 1) := sorry

/-- Polarization identity: The imaginary part of the inner product, in terms of the norm. -/
theorem im_inner_eq_norm_sub_I_smul_mul_self_sub_norm_add_I_smul_mul_self_div_four {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (x : E) (y : E) : coe_fn is_R_or_C.im (inner x y) =
  (norm (x - is_R_or_C.I • y) * norm (x - is_R_or_C.I • y) - norm (x + is_R_or_C.I • y) * norm (x + is_R_or_C.I • y)) /
    bit0 (bit0 1) := sorry

/-- Polarization identity: The inner product, in terms of the norm. -/
theorem inner_eq_sum_norm_sq_div_four {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (x : E) (y : E) : inner x y =
  (↑(norm (x + y)) ^ bit0 1 - ↑(norm (x - y)) ^ bit0 1 +
      (↑(norm (x - is_R_or_C.I • y)) ^ bit0 1 - ↑(norm (x + is_R_or_C.I • y)) ^ bit0 1) * is_R_or_C.I) /
    bit0 (bit0 1) := sorry

/-- A linear isometry preserves the inner product. -/
@[simp] theorem linear_isometry.inner_map_map {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {E' : Type u_4} [inner_product_space 𝕜 E'] (f : linear_isometry 𝕜 E E') (x : E) (y : E) : inner (coe_fn f x) (coe_fn f y) = inner x y := sorry

/-- A linear isometric equivalence preserves the inner product. -/
@[simp] theorem linear_isometry_equiv.inner_map_map {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {E' : Type u_4} [inner_product_space 𝕜 E'] (f : linear_isometry_equiv 𝕜 E E') (x : E) (y : E) : inner (coe_fn f x) (coe_fn f y) = inner x y :=
  linear_isometry.inner_map_map (linear_isometry_equiv.to_linear_isometry f) x y

/-- A linear map that preserves the inner product is a linear isometry. -/
def linear_map.isometry_of_inner {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {E' : Type u_4} [inner_product_space 𝕜 E'] (f : linear_map 𝕜 E E') (h : ∀ (x y : E), inner (coe_fn f x) (coe_fn f y) = inner x y) : linear_isometry 𝕜 E E' :=
  linear_isometry.mk f sorry

@[simp] theorem linear_map.coe_isometry_of_inner {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {E' : Type u_4} [inner_product_space 𝕜 E'] (f : linear_map 𝕜 E E') (h : ∀ (x y : E), inner (coe_fn f x) (coe_fn f y) = inner x y) : ⇑(linear_map.isometry_of_inner f h) = ⇑f :=
  rfl

@[simp] theorem linear_map.isometry_of_inner_to_linear_map {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {E' : Type u_4} [inner_product_space 𝕜 E'] (f : linear_map 𝕜 E E') (h : ∀ (x y : E), inner (coe_fn f x) (coe_fn f y) = inner x y) : linear_isometry.to_linear_map (linear_map.isometry_of_inner f h) = f :=
  rfl

/-- A linear equivalence that preserves the inner product is a linear isometric equivalence. -/
def linear_equiv.isometry_of_inner {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {E' : Type u_4} [inner_product_space 𝕜 E'] (f : linear_equiv 𝕜 E E') (h : ∀ (x y : E), inner (coe_fn f x) (coe_fn f y) = inner x y) : linear_isometry_equiv 𝕜 E E' :=
  linear_isometry_equiv.mk f sorry

@[simp] theorem linear_equiv.coe_isometry_of_inner {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {E' : Type u_4} [inner_product_space 𝕜 E'] (f : linear_equiv 𝕜 E E') (h : ∀ (x y : E), inner (coe_fn f x) (coe_fn f y) = inner x y) : ⇑(linear_equiv.isometry_of_inner f h) = ⇑f :=
  rfl

@[simp] theorem linear_equiv.isometry_of_inner_to_linear_equiv {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {E' : Type u_4} [inner_product_space 𝕜 E'] (f : linear_equiv 𝕜 E E') (h : ∀ (x y : E), inner (coe_fn f x) (coe_fn f y) = inner x y) : linear_isometry_equiv.to_linear_equiv (linear_equiv.isometry_of_inner f h) = f :=
  rfl

/-- Polarization identity: The real inner product, in terms of the norm. -/
theorem real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two {F : Type u_3} [inner_product_space ℝ F] (x : F) (y : F) : inner x y = (norm (x + y) * norm (x + y) - norm x * norm x - norm y * norm y) / bit0 1 :=
  Eq.trans (Eq.symm is_R_or_C.re_to_real) (re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two x y)

/-- Polarization identity: The real inner product, in terms of the norm. -/
theorem real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two {F : Type u_3} [inner_product_space ℝ F] (x : F) (y : F) : inner x y = (norm x * norm x + norm y * norm y - norm (x - y) * norm (x - y)) / bit0 1 :=
  Eq.trans (Eq.symm is_R_or_C.re_to_real) (re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two x y)

/-- Pythagorean theorem, if-and-only-if vector inner product form. -/
theorem norm_add_square_eq_norm_square_add_norm_square_iff_real_inner_eq_zero {F : Type u_3} [inner_product_space ℝ F] (x : F) (y : F) : norm (x + y) * norm (x + y) = norm x * norm x + norm y * norm y ↔ inner x y = 0 := sorry

/-- Pythagorean theorem, vector inner product form. -/
theorem norm_add_square_eq_norm_square_add_norm_square_of_inner_eq_zero {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (x : E) (y : E) (h : inner x y = 0) : norm (x + y) * norm (x + y) = norm x * norm x + norm y * norm y := sorry

/-- Pythagorean theorem, vector inner product form. -/
theorem norm_add_square_eq_norm_square_add_norm_square_real {F : Type u_3} [inner_product_space ℝ F] {x : F} {y : F} (h : inner x y = 0) : norm (x + y) * norm (x + y) = norm x * norm x + norm y * norm y :=
  iff.mpr (norm_add_square_eq_norm_square_add_norm_square_iff_real_inner_eq_zero x y) h

/-- Pythagorean theorem, subtracting vectors, if-and-only-if vector
inner product form. -/
theorem norm_sub_square_eq_norm_square_add_norm_square_iff_real_inner_eq_zero {F : Type u_3} [inner_product_space ℝ F] (x : F) (y : F) : norm (x - y) * norm (x - y) = norm x * norm x + norm y * norm y ↔ inner x y = 0 := sorry

/-- Pythagorean theorem, subtracting vectors, vector inner product
form. -/
theorem norm_sub_square_eq_norm_square_add_norm_square_real {F : Type u_3} [inner_product_space ℝ F] {x : F} {y : F} (h : inner x y = 0) : norm (x - y) * norm (x - y) = norm x * norm x + norm y * norm y :=
  iff.mpr (norm_sub_square_eq_norm_square_add_norm_square_iff_real_inner_eq_zero x y) h

/-- The sum and difference of two vectors are orthogonal if and only
if they have the same norm. -/
theorem real_inner_add_sub_eq_zero_iff {F : Type u_3} [inner_product_space ℝ F] (x : F) (y : F) : inner (x + y) (x - y) = 0 ↔ norm x = norm y := sorry

/-- The real inner product of two vectors, divided by the product of their
norms, has absolute value at most 1. -/
theorem abs_real_inner_div_norm_mul_norm_le_one {F : Type u_3} [inner_product_space ℝ F] (x : F) (y : F) : abs (inner x y / (norm x * norm y)) ≤ 1 := sorry

/-- The inner product of a vector with a multiple of itself. -/
theorem real_inner_smul_self_left {F : Type u_3} [inner_product_space ℝ F] (x : F) (r : ℝ) : inner (r • x) x = r * (norm x * norm x) := sorry

/-- The inner product of a vector with a multiple of itself. -/
theorem real_inner_smul_self_right {F : Type u_3} [inner_product_space ℝ F] (x : F) (r : ℝ) : inner x (r • x) = r * (norm x * norm x) := sorry

/-- The inner product of a nonzero vector with a nonzero multiple of
itself, divided by the product of their norms, has absolute value
1. -/
theorem abs_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {x : E} {r : 𝕜} (hx : x ≠ 0) (hr : r ≠ 0) : is_R_or_C.abs (inner x (r • x)) / (norm x * norm (r • x)) = 1 := sorry

/-- The inner product of a nonzero vector with a nonzero multiple of
itself, divided by the product of their norms, has absolute value
1. -/
theorem abs_real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul {F : Type u_3} [inner_product_space ℝ F] {x : F} {r : ℝ} (hx : x ≠ 0) (hr : r ≠ 0) : abs (inner x (r • x)) / (norm x * norm (r • x)) = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (abs (inner x (r • x)) / (norm x * norm (r • x)) = 1)) (Eq.symm is_R_or_C.abs_to_real)))
    (abs_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul hx hr)

/-- The inner product of a nonzero vector with a positive multiple of
itself, divided by the product of their norms, has value 1. -/
theorem real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul {F : Type u_3} [inner_product_space ℝ F] {x : F} {r : ℝ} (hx : x ≠ 0) (hr : 0 < r) : inner x (r • x) / (norm x * norm (r • x)) = 1 := sorry

/-- The inner product of a nonzero vector with a negative multiple of
itself, divided by the product of their norms, has value -1. -/
theorem real_inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul {F : Type u_3} [inner_product_space ℝ F] {x : F} {r : ℝ} (hx : x ≠ 0) (hr : r < 0) : inner x (r • x) / (norm x * norm (r • x)) = -1 := sorry

/-- The inner product of two vectors, divided by the product of their
norms, has absolute value 1 if and only if they are nonzero and one is
a multiple of the other. One form of equality case for Cauchy-Schwarz. -/
theorem abs_inner_div_norm_mul_norm_eq_one_iff {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (x : E) (y : E) : is_R_or_C.abs (inner x y / (↑(norm x) * ↑(norm y))) = 1 ↔ x ≠ 0 ∧ ∃ (r : 𝕜), r ≠ 0 ∧ y = r • x := sorry

/-- The inner product of two vectors, divided by the product of their
norms, has absolute value 1 if and only if they are nonzero and one is
a multiple of the other. One form of equality case for Cauchy-Schwarz. -/
theorem abs_real_inner_div_norm_mul_norm_eq_one_iff {F : Type u_3} [inner_product_space ℝ F] (x : F) (y : F) : abs (inner x y / (norm x * norm y)) = 1 ↔ x ≠ 0 ∧ ∃ (r : ℝ), r ≠ 0 ∧ y = r • x := sorry

/--
If the inner product of two vectors is equal to the product of their norms, then the two vectors
are multiples of each other. One form of the equality case for Cauchy-Schwarz.
Compare `inner_eq_norm_mul_iff`, which takes the stronger hypothesis `⟪x, y⟫ = ∥x∥ * ∥y∥`. -/
theorem abs_inner_eq_norm_iff {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (x : E) (y : E) (hx0 : x ≠ 0) (hy0 : y ≠ 0) : is_R_or_C.abs (inner x y) = norm x * norm y ↔ ∃ (r : 𝕜), r ≠ 0 ∧ y = r • x := sorry

/-- The inner product of two vectors, divided by the product of their
norms, has value 1 if and only if they are nonzero and one is
a positive multiple of the other. -/
theorem real_inner_div_norm_mul_norm_eq_one_iff {F : Type u_3} [inner_product_space ℝ F] (x : F) (y : F) : inner x y / (norm x * norm y) = 1 ↔ x ≠ 0 ∧ ∃ (r : ℝ), 0 < r ∧ y = r • x := sorry

/-- The inner product of two vectors, divided by the product of their
norms, has value -1 if and only if they are nonzero and one is
a negative multiple of the other. -/
theorem real_inner_div_norm_mul_norm_eq_neg_one_iff {F : Type u_3} [inner_product_space ℝ F] (x : F) (y : F) : inner x y / (norm x * norm y) = -1 ↔ x ≠ 0 ∧ ∃ (r : ℝ), r < 0 ∧ y = r • x := sorry

/-- If the inner product of two vectors is equal to the product of their norms (i.e.,
`⟪x, y⟫ = ∥x∥ * ∥y∥`), then the two vectors are nonnegative real multiples of each other. One form
of the equality case for Cauchy-Schwarz.
Compare `abs_inner_eq_norm_iff`, which takes the weaker hypothesis `abs ⟪x, y⟫ = ∥x∥ * ∥y∥`. -/
theorem inner_eq_norm_mul_iff {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {x : E} {y : E} : inner x y = ↑(norm x) * ↑(norm y) ↔ ↑(norm y) • x = ↑(norm x) • y := sorry

/-- If the inner product of two vectors is equal to the product of their norms (i.e.,
`⟪x, y⟫ = ∥x∥ * ∥y∥`), then the two vectors are nonnegative real multiples of each other. One form
of the equality case for Cauchy-Schwarz.
Compare `abs_inner_eq_norm_iff`, which takes the weaker hypothesis `abs ⟪x, y⟫ = ∥x∥ * ∥y∥`. -/
theorem inner_eq_norm_mul_iff_real {F : Type u_3} [inner_product_space ℝ F] {x : F} {y : F} : inner x y = norm x * norm y ↔ norm y • x = norm x • y :=
  inner_eq_norm_mul_iff

/-- If the inner product of two unit vectors is `1`, then the two vectors are equal. One form of
the equality case for Cauchy-Schwarz. -/
theorem inner_eq_norm_mul_iff_of_norm_one {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {x : E} {y : E} (hx : norm x = 1) (hy : norm y = 1) : inner x y = 1 ↔ x = y := sorry

theorem inner_lt_norm_mul_iff_real {F : Type u_3} [inner_product_space ℝ F] {x : F} {y : F} : inner x y < norm x * norm y ↔ norm y • x ≠ norm x • y :=
  iff.trans { mp := ne_of_lt, mpr := lt_of_le_of_ne (real_inner_le_norm x y) } (not_congr inner_eq_norm_mul_iff_real)

/-- If the inner product of two unit vectors is strictly less than `1`, then the two vectors are
distinct. One form of the equality case for Cauchy-Schwarz. -/
theorem inner_lt_one_iff_real_of_norm_one {F : Type u_3} [inner_product_space ℝ F] {x : F} {y : F} (hx : norm x = 1) (hy : norm y = 1) : inner x y < 1 ↔ x ≠ y := sorry

/-- The inner product of two weighted sums, where the weights in each
sum add to 0, in terms of the norms of pairwise differences. -/
theorem inner_sum_smul_sum_smul_of_sum_eq_zero {F : Type u_3} [inner_product_space ℝ F] {ι₁ : Type u_1} {s₁ : finset ι₁} {w₁ : ι₁ → ℝ} (v₁ : ι₁ → F) (h₁ : (finset.sum s₁ fun (i : ι₁) => w₁ i) = 0) {ι₂ : Type u_2} {s₂ : finset ι₂} {w₂ : ι₂ → ℝ} (v₂ : ι₂ → F) (h₂ : (finset.sum s₂ fun (i : ι₂) => w₂ i) = 0) : inner (finset.sum s₁ fun (i₁ : ι₁) => w₁ i₁ • v₁ i₁) (finset.sum s₂ fun (i₂ : ι₂) => w₂ i₂ • v₂ i₂) =
  (-finset.sum s₁
        fun (i₁ : ι₁) => finset.sum s₂ fun (i₂ : ι₂) => w₁ i₁ * w₂ i₂ * (norm (v₁ i₁ - v₂ i₂) * norm (v₁ i₁ - v₂ i₂))) /
    bit0 1 := sorry

/-- The inner product with a fixed left element, as a continuous linear map.  This can be upgraded
to a continuous map which is jointly conjugate-linear in the left argument and linear in the right
argument, once (TODO) conjugate-linear maps have been defined. -/
def inner_right {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (v : E) : continuous_linear_map 𝕜 E 𝕜 :=
  linear_map.mk_continuous (linear_map.mk (fun (w : E) => inner v w) sorry sorry) (norm v) sorry

@[simp] theorem inner_right_coe {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (v : E) : ⇑(inner_right v) = fun (w : E) => inner v w :=
  rfl

@[simp] theorem inner_right_apply {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (v : E) (w : E) : coe_fn (inner_right v) w = inner v w :=
  rfl

/-! ### Inner product space structure on product spaces -/

/-
 If `ι` is a finite type and each space `f i`, `i : ι`, is an inner product space,
then `Π i, f i` is an inner product space as well. Since `Π i, f i` is endowed with the sup norm,
we use instead `pi_Lp 2 one_le_two f` for the product space, which is endowed with the `L^2` norm.
-/

protected instance pi_Lp.inner_product_space {𝕜 : Type u_1} [is_R_or_C 𝕜] {ι : Type u_2} [fintype ι] (f : ι → Type u_3) [(i : ι) → inner_product_space 𝕜 (f i)] : inner_product_space 𝕜 (pi_Lp (bit0 1) one_le_two f) :=
  inner_product_space.mk sorry sorry sorry sorry sorry

/-- A field `𝕜` satisfying `is_R_or_C` is itself a `𝕜`-inner product space. -/
protected instance is_R_or_C.inner_product_space {𝕜 : Type u_1} [is_R_or_C 𝕜] : inner_product_space 𝕜 𝕜 :=
  inner_product_space.mk sorry sorry sorry sorry sorry

/-- The standard real/complex Euclidean space, functions on a finite type. For an `n`-dimensional
space use `euclidean_space 𝕜 (fin n)`. -/
def euclidean_space (𝕜 : Type u_1) [is_R_or_C 𝕜] (n : Type u_2) [fintype n]  :=
  pi_Lp (bit0 1) one_le_two fun (i : n) => 𝕜

/-! ### Inner product space structure on subspaces -/

/-- Induced inner product on a submodule. -/
protected instance submodule.inner_product_space {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (W : submodule 𝕜 E) : inner_product_space 𝕜 ↥W :=
  inner_product_space.mk sorry sorry sorry sorry sorry

/-- The inner product on submodules is the same as on the ambient space. -/
@[simp] theorem submodule.coe_inner {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (W : submodule 𝕜 E) (x : ↥W) (y : ↥W) : inner x y = inner ↑x ↑y :=
  rfl

/-- A general inner product implies a real inner product. This is not registered as an instance
since it creates problems with the case `𝕜 = ℝ`. -/
def has_inner.is_R_or_C_to_real (𝕜 : Type u_1) (E : Type u_2) [is_R_or_C 𝕜] [inner_product_space 𝕜 E] : has_inner ℝ E :=
  has_inner.mk fun (x y : E) => coe_fn is_R_or_C.re (inner x y)

/-- A general inner product space structure implies a real inner product structure. This is not
registered as an instance since it creates problems with the case `𝕜 = ℝ`, but in can be used in a
proof to obtain a real inner product space structure from a given `𝕜`-inner product space
structure. -/
def inner_product_space.is_R_or_C_to_real (𝕜 : Type u_1) (E : Type u_2) [is_R_or_C 𝕜] [inner_product_space 𝕜 E] : inner_product_space ℝ E :=
  inner_product_space.mk norm_sq_eq_inner sorry sorry sorry sorry

theorem real_inner_eq_re_inner (𝕜 : Type u_1) {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (x : E) (y : E) : inner x y = coe_fn is_R_or_C.re (inner x y) :=
  rfl

/-- A complex inner product implies a real inner product -/
protected instance inner_product_space.complex_to_real {G : Type u_4} [inner_product_space ℂ G] : inner_product_space ℝ G :=
  inner_product_space.is_R_or_C_to_real ℂ G

/-!
### Derivative of the inner product

In this section we prove that the inner product and square of the norm in an inner space are
infinitely `ℝ`-smooth. In order to state these results, we need a `normed_space ℝ E`
instance. Though we can deduce this structure from `inner_product_space 𝕜 E`, this instance may be
not definitionally equal to some other “natural” instance. So, we assume `[normed_space ℝ E]` and
`[is_scalar_tower ℝ 𝕜 E]`. In both interesting cases `𝕜 = ℝ` and `𝕜 = ℂ` we have these instances.

-/

theorem is_bounded_bilinear_map_inner {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [normed_space ℝ E] [is_scalar_tower ℝ 𝕜 E] : is_bounded_bilinear_map ℝ fun (p : E × E) => inner (prod.fst p) (prod.snd p) := sorry

/-- Derivative of the inner product. -/
def fderiv_inner_clm {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [normed_space ℝ E] [is_scalar_tower ℝ 𝕜 E] (p : E × E) : continuous_linear_map ℝ (E × E) 𝕜 :=
  is_bounded_bilinear_map.deriv is_bounded_bilinear_map_inner p

@[simp] theorem fderiv_inner_clm_apply {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [normed_space ℝ E] [is_scalar_tower ℝ 𝕜 E] (p : E × E) (x : E × E) : coe_fn (fderiv_inner_clm p) x = inner (prod.fst p) (prod.snd x) + inner (prod.fst x) (prod.snd p) :=
  rfl

theorem times_cont_diff_inner {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [normed_space ℝ E] [is_scalar_tower ℝ 𝕜 E] {n : with_top ℕ} : times_cont_diff ℝ n fun (p : E × E) => inner (prod.fst p) (prod.snd p) :=
  is_bounded_bilinear_map.times_cont_diff is_bounded_bilinear_map_inner

theorem times_cont_diff_at_inner {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [normed_space ℝ E] [is_scalar_tower ℝ 𝕜 E] {p : E × E} {n : with_top ℕ} : times_cont_diff_at ℝ n (fun (p : E × E) => inner (prod.fst p) (prod.snd p)) p :=
  times_cont_diff.times_cont_diff_at times_cont_diff_inner

theorem differentiable_inner {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [normed_space ℝ E] [is_scalar_tower ℝ 𝕜 E] : differentiable ℝ fun (p : E × E) => inner (prod.fst p) (prod.snd p) :=
  is_bounded_bilinear_map.differentiable_at is_bounded_bilinear_map_inner

theorem times_cont_diff_within_at.inner {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [normed_space ℝ E] [is_scalar_tower ℝ 𝕜 E] {G : Type u_4} [normed_group G] [normed_space ℝ G] {f : G → E} {g : G → E} {s : set G} {x : G} {n : with_top ℕ} (hf : times_cont_diff_within_at ℝ n f s x) (hg : times_cont_diff_within_at ℝ n g s x) : times_cont_diff_within_at ℝ n (fun (x : G) => inner (f x) (g x)) s x :=
  times_cont_diff_at.comp_times_cont_diff_within_at x times_cont_diff_at_inner (times_cont_diff_within_at.prod hf hg)

theorem times_cont_diff_at.inner {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [normed_space ℝ E] [is_scalar_tower ℝ 𝕜 E] {G : Type u_4} [normed_group G] [normed_space ℝ G] {f : G → E} {g : G → E} {x : G} {n : with_top ℕ} (hf : times_cont_diff_at ℝ n f x) (hg : times_cont_diff_at ℝ n g x) : times_cont_diff_at ℝ n (fun (x : G) => inner (f x) (g x)) x :=
  times_cont_diff_within_at.inner hf hg

theorem times_cont_diff_on.inner {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [normed_space ℝ E] [is_scalar_tower ℝ 𝕜 E] {G : Type u_4} [normed_group G] [normed_space ℝ G] {f : G → E} {g : G → E} {s : set G} {n : with_top ℕ} (hf : times_cont_diff_on ℝ n f s) (hg : times_cont_diff_on ℝ n g s) : times_cont_diff_on ℝ n (fun (x : G) => inner (f x) (g x)) s :=
  fun (x : G) (hx : x ∈ s) => times_cont_diff_within_at.inner (hf x hx) (hg x hx)

theorem times_cont_diff.inner {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [normed_space ℝ E] [is_scalar_tower ℝ 𝕜 E] {G : Type u_4} [normed_group G] [normed_space ℝ G] {f : G → E} {g : G → E} {n : with_top ℕ} (hf : times_cont_diff ℝ n f) (hg : times_cont_diff ℝ n g) : times_cont_diff ℝ n fun (x : G) => inner (f x) (g x) :=
  times_cont_diff.comp times_cont_diff_inner (times_cont_diff.prod hf hg)

theorem has_fderiv_within_at.inner {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [normed_space ℝ E] [is_scalar_tower ℝ 𝕜 E] {G : Type u_4} [normed_group G] [normed_space ℝ G] {f : G → E} {g : G → E} {f' : continuous_linear_map ℝ G E} {g' : continuous_linear_map ℝ G E} {s : set G} {x : G} (hf : has_fderiv_within_at f f' s x) (hg : has_fderiv_within_at g g' s x) : has_fderiv_within_at (fun (t : G) => inner (f t) (g t))
  (continuous_linear_map.comp (fderiv_inner_clm (f x, g x)) (continuous_linear_map.prod f' g')) s x :=
  has_fderiv_at.comp_has_fderiv_within_at x
    (is_bounded_bilinear_map.has_fderiv_at is_bounded_bilinear_map_inner (f x, g x)) (has_fderiv_within_at.prod hf hg)

theorem has_fderiv_at.inner {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [normed_space ℝ E] [is_scalar_tower ℝ 𝕜 E] {G : Type u_4} [normed_group G] [normed_space ℝ G] {f : G → E} {g : G → E} {f' : continuous_linear_map ℝ G E} {g' : continuous_linear_map ℝ G E} {x : G} (hf : has_fderiv_at f f' x) (hg : has_fderiv_at g g' x) : has_fderiv_at (fun (t : G) => inner (f t) (g t))
  (continuous_linear_map.comp (fderiv_inner_clm (f x, g x)) (continuous_linear_map.prod f' g')) x :=
  has_fderiv_at.comp x (is_bounded_bilinear_map.has_fderiv_at is_bounded_bilinear_map_inner (f x, g x))
    (has_fderiv_at.prod hf hg)

theorem has_deriv_within_at.inner {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [normed_space ℝ E] [is_scalar_tower ℝ 𝕜 E] {f : ℝ → E} {g : ℝ → E} {f' : E} {g' : E} {s : set ℝ} {x : ℝ} (hf : has_deriv_within_at f f' s x) (hg : has_deriv_within_at g g' s x) : has_deriv_within_at (fun (t : ℝ) => inner (f t) (g t)) (inner (f x) g' + inner f' (g x)) s x := sorry

theorem has_deriv_at.inner {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [normed_space ℝ E] [is_scalar_tower ℝ 𝕜 E] {f : ℝ → E} {g : ℝ → E} {f' : E} {g' : E} {x : ℝ} : has_deriv_at f f' x →
  has_deriv_at g g' x → has_deriv_at (fun (t : ℝ) => inner (f t) (g t)) (inner (f x) g' + inner f' (g x)) x := sorry

theorem differentiable_within_at.inner {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [normed_space ℝ E] [is_scalar_tower ℝ 𝕜 E] {G : Type u_4} [normed_group G] [normed_space ℝ G] {f : G → E} {g : G → E} {s : set G} {x : G} (hf : differentiable_within_at ℝ f s x) (hg : differentiable_within_at ℝ g s x) : differentiable_within_at ℝ (fun (x : G) => inner (f x) (g x)) s x :=
  has_fderiv_within_at.differentiable_within_at
    (has_fderiv_at.comp_has_fderiv_within_at x (differentiable_at.has_fderiv_at (differentiable_inner (f x, g x)))
      (differentiable_within_at.has_fderiv_within_at (differentiable_within_at.prod hf hg)))

theorem differentiable_at.inner {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [normed_space ℝ E] [is_scalar_tower ℝ 𝕜 E] {G : Type u_4} [normed_group G] [normed_space ℝ G] {f : G → E} {g : G → E} {x : G} (hf : differentiable_at ℝ f x) (hg : differentiable_at ℝ g x) : differentiable_at ℝ (fun (x : G) => inner (f x) (g x)) x :=
  differentiable_at.comp x (differentiable_inner (f x, g x)) (differentiable_at.prod hf hg)

theorem differentiable_on.inner {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [normed_space ℝ E] [is_scalar_tower ℝ 𝕜 E] {G : Type u_4} [normed_group G] [normed_space ℝ G] {f : G → E} {g : G → E} {s : set G} (hf : differentiable_on ℝ f s) (hg : differentiable_on ℝ g s) : differentiable_on ℝ (fun (x : G) => inner (f x) (g x)) s :=
  fun (x : G) (hx : x ∈ s) => differentiable_within_at.inner (hf x hx) (hg x hx)

theorem differentiable.inner {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [normed_space ℝ E] [is_scalar_tower ℝ 𝕜 E] {G : Type u_4} [normed_group G] [normed_space ℝ G] {f : G → E} {g : G → E} (hf : differentiable ℝ f) (hg : differentiable ℝ g) : differentiable ℝ fun (x : G) => inner (f x) (g x) :=
  fun (x : G) => differentiable_at.inner (hf x) (hg x)

theorem fderiv_inner_apply {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [normed_space ℝ E] [is_scalar_tower ℝ 𝕜 E] {G : Type u_4} [normed_group G] [normed_space ℝ G] {f : G → E} {g : G → E} {x : G} (hf : differentiable_at ℝ f x) (hg : differentiable_at ℝ g x) (y : G) : coe_fn (fderiv ℝ (fun (t : G) => inner (f t) (g t)) x) y =
  inner (f x) (coe_fn (fderiv ℝ g x) y) + inner (coe_fn (fderiv ℝ f x) y) (g x) := sorry

theorem deriv_inner_apply {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [normed_space ℝ E] [is_scalar_tower ℝ 𝕜 E] {f : ℝ → E} {g : ℝ → E} {x : ℝ} (hf : differentiable_at ℝ f x) (hg : differentiable_at ℝ g x) : deriv (fun (t : ℝ) => inner (f t) (g t)) x = inner (f x) (deriv g x) + inner (deriv f x) (g x) :=
  has_deriv_at.deriv (has_deriv_at.inner (differentiable_at.has_deriv_at hf) (differentiable_at.has_deriv_at hg))

theorem times_cont_diff_norm_square {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [normed_space ℝ E] [is_scalar_tower ℝ 𝕜 E] {n : with_top ℕ} : times_cont_diff ℝ n fun (x : E) => norm x ^ bit0 1 := sorry

theorem times_cont_diff.norm_square {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [normed_space ℝ E] [is_scalar_tower ℝ 𝕜 E] {G : Type u_4} [normed_group G] [normed_space ℝ G] {f : G → E} {n : with_top ℕ} (hf : times_cont_diff ℝ n f) : times_cont_diff ℝ n fun (x : G) => norm (f x) ^ bit0 1 :=
  times_cont_diff.comp times_cont_diff_norm_square hf

theorem times_cont_diff_within_at.norm_square {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [normed_space ℝ E] [is_scalar_tower ℝ 𝕜 E] {G : Type u_4} [normed_group G] [normed_space ℝ G] {f : G → E} {s : set G} {x : G} {n : with_top ℕ} (hf : times_cont_diff_within_at ℝ n f s x) : times_cont_diff_within_at ℝ n (fun (y : G) => norm (f y) ^ bit0 1) s x :=
  times_cont_diff_at.comp_times_cont_diff_within_at x (times_cont_diff.times_cont_diff_at times_cont_diff_norm_square) hf

theorem times_cont_diff_at.norm_square {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [normed_space ℝ E] [is_scalar_tower ℝ 𝕜 E] {G : Type u_4} [normed_group G] [normed_space ℝ G] {f : G → E} {x : G} {n : with_top ℕ} (hf : times_cont_diff_at ℝ n f x) : times_cont_diff_at ℝ n (fun (y : G) => norm (f y) ^ bit0 1) x :=
  times_cont_diff_within_at.norm_square hf

theorem times_cont_diff_on.norm_square {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [normed_space ℝ E] [is_scalar_tower ℝ 𝕜 E] {G : Type u_4} [normed_group G] [normed_space ℝ G] {f : G → E} {s : set G} {n : with_top ℕ} (hf : times_cont_diff_on ℝ n f s) : times_cont_diff_on ℝ n (fun (y : G) => norm (f y) ^ bit0 1) s :=
  fun (x : G) (hx : x ∈ s) => times_cont_diff_within_at.norm_square (hf x hx)

theorem differentiable_at.norm_square {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [normed_space ℝ E] [is_scalar_tower ℝ 𝕜 E] {G : Type u_4} [normed_group G] [normed_space ℝ G] {f : G → E} {x : G} (hf : differentiable_at ℝ f x) : differentiable_at ℝ (fun (y : G) => norm (f y) ^ bit0 1) x :=
  differentiable_at.comp x
    (differentiable.differentiable_at (times_cont_diff.differentiable times_cont_diff_norm_square le_rfl)) hf

theorem differentiable.norm_square {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [normed_space ℝ E] [is_scalar_tower ℝ 𝕜 E] {G : Type u_4} [normed_group G] [normed_space ℝ G] {f : G → E} (hf : differentiable ℝ f) : differentiable ℝ fun (y : G) => norm (f y) ^ bit0 1 :=
  fun (x : G) => differentiable_at.norm_square (hf x)

theorem differentiable_within_at.norm_square {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [normed_space ℝ E] [is_scalar_tower ℝ 𝕜 E] {G : Type u_4} [normed_group G] [normed_space ℝ G] {f : G → E} {s : set G} {x : G} (hf : differentiable_within_at ℝ f s x) : differentiable_within_at ℝ (fun (y : G) => norm (f y) ^ bit0 1) s x :=
  differentiable_at.comp_differentiable_within_at x
    (differentiable.differentiable_at (times_cont_diff.differentiable times_cont_diff_norm_square le_rfl)) hf

theorem differentiable_on.norm_square {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [normed_space ℝ E] [is_scalar_tower ℝ 𝕜 E] {G : Type u_4} [normed_group G] [normed_space ℝ G] {f : G → E} {s : set G} (hf : differentiable_on ℝ f s) : differentiable_on ℝ (fun (y : G) => norm (f y) ^ bit0 1) s :=
  fun (x : G) (hx : x ∈ s) => differentiable_within_at.norm_square (hf x hx)

/-!
### Continuity and measurability of the inner product

Since the inner product is `ℝ`-smooth, it is continuous. We do not need a `[normed_space ℝ E]`
structure to *state* this fact and its corollaries, so we introduce them in the proof instead.
-/

theorem continuous_inner {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] : continuous fun (p : E × E) => inner (prod.fst p) (prod.snd p) :=
  let _inst : inner_product_space ℝ E := inner_product_space.is_R_or_C_to_real 𝕜 E;
  let _inst_3 : is_scalar_tower ℝ 𝕜 E := restrict_scalars.is_scalar_tower ℝ 𝕜 E;
  differentiable.continuous differentiable_inner

theorem filter.tendsto.inner {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {α : Type u_4} {f : α → E} {g : α → E} {l : filter α} {x : E} {y : E} (hf : filter.tendsto f l (nhds x)) (hg : filter.tendsto g l (nhds y)) : filter.tendsto (fun (t : α) => inner (f t) (g t)) l (nhds (inner x y)) :=
  filter.tendsto.comp (continuous.tendsto continuous_inner (x, y)) (filter.tendsto.prod_mk_nhds hf hg)

theorem measurable.inner {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {α : Type u_4} [measurable_space α] [measurable_space E] [opens_measurable_space E] [topological_space.second_countable_topology E] [measurable_space 𝕜] [borel_space 𝕜] {f : α → E} {g : α → E} (hf : measurable f) (hg : measurable g) : measurable fun (t : α) => inner (f t) (g t) :=
  continuous.measurable2 continuous_inner hf hg

theorem continuous_within_at.inner {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {α : Type u_4} [topological_space α] {f : α → E} {g : α → E} {x : α} {s : set α} (hf : continuous_within_at f s x) (hg : continuous_within_at g s x) : continuous_within_at (fun (t : α) => inner (f t) (g t)) s x :=
  filter.tendsto.inner hf hg

theorem continuous_at.inner {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {α : Type u_4} [topological_space α] {f : α → E} {g : α → E} {x : α} (hf : continuous_at f x) (hg : continuous_at g x) : continuous_at (fun (t : α) => inner (f t) (g t)) x :=
  filter.tendsto.inner hf hg

theorem continuous_on.inner {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {α : Type u_4} [topological_space α] {f : α → E} {g : α → E} {s : set α} (hf : continuous_on f s) (hg : continuous_on g s) : continuous_on (fun (t : α) => inner (f t) (g t)) s :=
  fun (x : α) (hx : x ∈ s) => continuous_within_at.inner (hf x hx) (hg x hx)

theorem continuous.inner {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {α : Type u_4} [topological_space α] {f : α → E} {g : α → E} (hf : continuous f) (hg : continuous g) : continuous fun (t : α) => inner (f t) (g t) :=
  iff.mpr continuous_iff_continuous_at
    fun (x : α) => continuous_at.inner (continuous.continuous_at hf) (continuous.continuous_at hg)

protected instance euclidean_space.finite_dimensional {𝕜 : Type u_1} [is_R_or_C 𝕜] {ι : Type u_4} [fintype ι] : finite_dimensional 𝕜 (euclidean_space 𝕜 ι) :=
  finite_dimensional.finite_dimensional_fintype_fun 𝕜

@[simp] theorem findim_euclidean_space {𝕜 : Type u_1} [is_R_or_C 𝕜] {ι : Type u_4} [fintype ι] : finite_dimensional.findim 𝕜 (euclidean_space 𝕜 ι) = fintype.card ι := sorry

theorem findim_euclidean_space_fin {𝕜 : Type u_1} [is_R_or_C 𝕜] {n : ℕ} : finite_dimensional.findim 𝕜 (euclidean_space 𝕜 (fin n)) = n := sorry

/-- A basis on `ι` for a finite-dimensional space induces a continuous linear equivalence
with `euclidean_space 𝕜 ι`.  If the basis is orthonormal in an inner product space, this continuous
linear equivalence is an isometry, but we don't prove that here. -/
def is_basis.equiv_fun_euclidean {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {ι : Type u_4} [fintype ι] [finite_dimensional 𝕜 E] {v : ι → E} (h : is_basis 𝕜 v) : continuous_linear_equiv 𝕜 E (euclidean_space 𝕜 ι) :=
  linear_equiv.to_continuous_linear_equiv (is_basis.equiv_fun h)

/-! ### Orthogonal projection in inner product spaces -/

/--
Existence of minimizers
Let `u` be a point in a real inner product space, and let `K` be a nonempty complete convex subset.
Then there exists a (unique) `v` in `K` that minimizes the distance `∥u - v∥` to `u`.
 -/
-- FIXME this monolithic proof causes a deterministic timeout with `-T50000`

-- It should be broken in a sequence of more manageable pieces,

-- perhaps with individual statements for the three steps below.

theorem exists_norm_eq_infi_of_complete_convex {F : Type u_3} [inner_product_space ℝ F] {K : set F} (ne : set.nonempty K) (h₁ : is_complete K) (h₂ : convex K) (u : F) : ∃ (v : F), ∃ (H : v ∈ K), norm (u - v) = infi fun (w : ↥K) => norm (u - ↑w) := sorry

/-- Characterization of minimizers for the projection on a convex set in a real inner product
space. -/
theorem norm_eq_infi_iff_real_inner_le_zero {F : Type u_3} [inner_product_space ℝ F] {K : set F} (h : convex K) {u : F} {v : F} (hv : v ∈ K) : (norm (u - v) = infi fun (w : ↥K) => norm (u - ↑w)) ↔ ∀ (w : F), w ∈ K → inner (u - v) (w - v) ≤ 0 := sorry

/--
Existence of projections on complete subspaces.
Let `u` be a point in an inner product space, and let `K` be a nonempty complete subspace.
Then there exists a (unique) `v` in `K` that minimizes the distance `∥u - v∥` to `u`.
This point `v` is usually called the orthogonal projection of `u` onto `K`.
-/
theorem exists_norm_eq_infi_of_complete_subspace {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (K : submodule 𝕜 E) (h : is_complete ↑K) (u : E) : ∃ (v : E), ∃ (H : v ∈ K), norm (u - v) = infi fun (w : ↥↑K) => norm (u - ↑w) := sorry

/--
Characterization of minimizers in the projection on a subspace, in the real case.
Let `u` be a point in a real inner product space, and let `K` be a nonempty subspace.
Then point `v` minimizes the distance `∥u - v∥` over points in `K` if and only if
for all `w ∈ K`, `⟪u - v, w⟫ = 0` (i.e., `u - v` is orthogonal to the subspace `K`).
This is superceded by `norm_eq_infi_iff_inner_eq_zero` that gives the same conclusion over
any `is_R_or_C` field.
-/
theorem norm_eq_infi_iff_real_inner_eq_zero {F : Type u_3} [inner_product_space ℝ F] (K : submodule ℝ F) {u : F} {v : F} (hv : v ∈ K) : (norm (u - v) = infi fun (w : ↥↑K) => norm (u - ↑w)) ↔ ∀ (w : F), w ∈ K → inner (u - v) w = 0 := sorry

/--
Characterization of minimizers in the projection on a subspace.
Let `u` be a point in an inner product space, and let `K` be a nonempty subspace.
Then point `v` minimizes the distance `∥u - v∥` over points in `K` if and only if
for all `w ∈ K`, `⟪u - v, w⟫ = 0` (i.e., `u - v` is orthogonal to the subspace `K`)
-/
theorem norm_eq_infi_iff_inner_eq_zero {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (K : submodule 𝕜 E) {u : E} {v : E} (hv : v ∈ K) : (norm (u - v) = infi fun (w : ↥↑K) => norm (u - ↑w)) ↔ ∀ (w : E), w ∈ K → inner (u - v) w = 0 := sorry

/-- The orthogonal projection onto a complete subspace, as an
unbundled function.  This definition is only intended for use in
setting up the bundled version `orthogonal_projection` and should not
be used once that is defined. -/
def orthogonal_projection_fn {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (K : submodule 𝕜 E) [complete_space ↥K] (v : E) : E :=
  Exists.some sorry

/-- The unbundled orthogonal projection is in the given subspace.
This lemma is only intended for use in setting up the bundled version
and should not be used once that is defined. -/
theorem orthogonal_projection_fn_mem {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {K : submodule 𝕜 E} [complete_space ↥K] (v : E) : orthogonal_projection_fn K v ∈ K :=
  Exists.some
    (Exists.some_spec (exists_norm_eq_infi_of_complete_subspace K (iff.mp complete_space_coe_iff_is_complete _inst_4) v))

/-- The characterization of the unbundled orthogonal projection.  This
lemma is only intended for use in setting up the bundled version
and should not be used once that is defined. -/
theorem orthogonal_projection_fn_inner_eq_zero {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {K : submodule 𝕜 E} [complete_space ↥K] (v : E) (w : E) (H : w ∈ K) : inner (v - orthogonal_projection_fn K v) w = 0 := sorry

/-- The unbundled orthogonal projection is the unique point in `K`
with the orthogonality property.  This lemma is only intended for use
in setting up the bundled version and should not be used once that is
defined. -/
theorem eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {K : submodule 𝕜 E} [complete_space ↥K] {u : E} {v : E} (hvm : v ∈ K) (hvo : ∀ (w : E), w ∈ K → inner (u - v) w = 0) : orthogonal_projection_fn K u = v := sorry

theorem orthogonal_projection_fn_norm_sq {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (K : submodule 𝕜 E) [complete_space ↥K] (v : E) : norm v * norm v =
  norm (v - orthogonal_projection_fn K v) * norm (v - orthogonal_projection_fn K v) +
    norm (orthogonal_projection_fn K v) * norm (orthogonal_projection_fn K v) := sorry

/-- The orthogonal projection onto a complete subspace. -/
def orthogonal_projection {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (K : submodule 𝕜 E) [complete_space ↥K] : continuous_linear_map 𝕜 E ↥K :=
  linear_map.mk_continuous
    (linear_map.mk (fun (v : E) => { val := orthogonal_projection_fn K v, property := orthogonal_projection_fn_mem v })
      sorry sorry)
    1 sorry

@[simp] theorem orthogonal_projection_fn_eq {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {K : submodule 𝕜 E} [complete_space ↥K] (v : E) : orthogonal_projection_fn K v = ↑(coe_fn (orthogonal_projection K) v) :=
  rfl

/-- The characterization of the orthogonal projection.  -/
@[simp] theorem orthogonal_projection_inner_eq_zero {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {K : submodule 𝕜 E} [complete_space ↥K] (v : E) (w : E) (H : w ∈ K) : inner (v - ↑(coe_fn (orthogonal_projection K) v)) w = 0 :=
  orthogonal_projection_fn_inner_eq_zero v

/-- The orthogonal projection is the unique point in `K` with the
orthogonality property. -/
theorem eq_orthogonal_projection_of_mem_of_inner_eq_zero {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {K : submodule 𝕜 E} [complete_space ↥K] {u : E} {v : E} (hvm : v ∈ K) (hvo : ∀ (w : E), w ∈ K → inner (u - v) w = 0) : ↑(coe_fn (orthogonal_projection K) u) = v :=
  eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero hvm hvo

/-- The orthogonal projections onto equal subspaces are coerced back to the same point in `E`. -/
theorem eq_orthogonal_projection_of_eq_submodule {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {K : submodule 𝕜 E} [complete_space ↥K] {K' : submodule 𝕜 E} [complete_space ↥K'] (h : K = K') (u : E) : ↑(coe_fn (orthogonal_projection K) u) = ↑(coe_fn (orthogonal_projection K') u) := sorry

/-- The orthogonal projection sends elements of `K` to themselves. -/
@[simp] theorem orthogonal_projection_mem_subspace_eq_self {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {K : submodule 𝕜 E} [complete_space ↥K] (v : ↥K) : coe_fn (orthogonal_projection K) ↑v = v := sorry

/-- The orthogonal projection onto the trivial submodule is the zero map. -/
@[simp] theorem orthogonal_projection_bot {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] : orthogonal_projection ⊥ = 0 := sorry

/-- The orthogonal projection has norm `≤ 1`. -/
theorem orthogonal_projection_norm_le {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (K : submodule 𝕜 E) [complete_space ↥K] : norm (orthogonal_projection K) ≤ 1 := sorry

theorem smul_orthogonal_projection_singleton (𝕜 : Type u_1) {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {v : E} (w : E) : ↑(norm v) ^ bit0 1 • ↑(coe_fn (orthogonal_projection (submodule.span 𝕜 (singleton v))) w) = inner v w • v := sorry

/-- Formula for orthogonal projection onto a single vector. -/
theorem orthogonal_projection_singleton (𝕜 : Type u_1) {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {v : E} (w : E) : ↑(coe_fn (orthogonal_projection (submodule.span 𝕜 (singleton v))) w) = (inner v w / ↑(norm v) ^ bit0 1) • v := sorry

/-- Formula for orthogonal projection onto a single unit vector. -/
theorem orthogonal_projection_unit_singleton (𝕜 : Type u_1) {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {v : E} (hv : norm v = 1) (w : E) : ↑(coe_fn (orthogonal_projection (submodule.span 𝕜 (singleton v))) w) = inner v w • v := sorry

/-- The subspace of vectors orthogonal to a given subspace. -/
def submodule.orthogonal {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (K : submodule 𝕜 E) : submodule 𝕜 E :=
  submodule.mk (set_of fun (v : E) => ∀ (u : E), u ∈ K → inner u v = 0) sorry sorry sorry

postfix:0 "ᗮ" => Mathlib.submodule.orthogonal

/-- When a vector is in `Kᗮ`. -/
theorem submodule.mem_orthogonal {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (K : submodule 𝕜 E) (v : E) : v ∈ (Kᗮ) ↔ ∀ (u : E), u ∈ K → inner u v = 0 :=
  iff.rfl

/-- When a vector is in `Kᗮ`, with the inner product the
other way round. -/
theorem submodule.mem_orthogonal' {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (K : submodule 𝕜 E) (v : E) : v ∈ (Kᗮ) ↔ ∀ (u : E), u ∈ K → inner v u = 0 := sorry

/-- A vector in `K` is orthogonal to one in `Kᗮ`. -/
theorem submodule.inner_right_of_mem_orthogonal {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {K : submodule 𝕜 E} {u : E} {v : E} (hu : u ∈ K) (hv : v ∈ (Kᗮ)) : inner u v = 0 :=
  iff.mp (submodule.mem_orthogonal K v) hv u hu

/-- A vector in `Kᗮ` is orthogonal to one in `K`. -/
theorem submodule.inner_left_of_mem_orthogonal {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {K : submodule 𝕜 E} {u : E} {v : E} (hu : u ∈ K) (hv : v ∈ (Kᗮ)) : inner v u = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (inner v u = 0)) (propext inner_eq_zero_sym)))
    (submodule.inner_right_of_mem_orthogonal hu hv)

/-- A vector in `(𝕜 ∙ u)ᗮ` is orthogonal to `u`. -/
theorem inner_right_of_mem_orthogonal_singleton {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (u : E) {v : E} (hv : v ∈ (submodule.span 𝕜 (singleton u)ᗮ)) : inner u v = 0 :=
  submodule.inner_right_of_mem_orthogonal (submodule.mem_span_singleton_self u) hv

/-- A vector in `(𝕜 ∙ u)ᗮ` is orthogonal to `u`. -/
theorem inner_left_of_mem_orthogonal_singleton {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (u : E) {v : E} (hv : v ∈ (submodule.span 𝕜 (singleton u)ᗮ)) : inner v u = 0 :=
  submodule.inner_left_of_mem_orthogonal (submodule.mem_span_singleton_self u) hv

/-- `K` and `Kᗮ` have trivial intersection. -/
theorem submodule.inf_orthogonal_eq_bot {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (K : submodule 𝕜 E) : K ⊓ (Kᗮ) = ⊥ := sorry

/-- `K` and `Kᗮ` have trivial intersection. -/
theorem submodule.orthogonal_disjoint {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (K : submodule 𝕜 E) : disjoint K (Kᗮ) := sorry

/-- `Kᗮ` can be characterized as the intersection of the kernels of the operations of
inner product with each of the elements of `K`. -/
theorem orthogonal_eq_inter {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (K : submodule 𝕜 E) : Kᗮ = infi fun (v : ↥K) => continuous_linear_map.ker (inner_right ↑v) := sorry

/-- The orthogonal complement of any submodule `K` is closed. -/
theorem submodule.is_closed_orthogonal {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (K : submodule 𝕜 E) : is_closed ↑(Kᗮ) := sorry

/-- In a complete space, the orthogonal complement of any submodule `K` is complete. -/
protected instance submodule.orthogonal.complete_space {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (K : submodule 𝕜 E) [complete_space E] : complete_space ↥(Kᗮ) :=
  is_closed.complete_space_coe (submodule.is_closed_orthogonal K)

/-- `submodule.orthogonal` gives a `galois_connection` between
`submodule 𝕜 E` and its `order_dual`. -/
theorem submodule.orthogonal_gc (𝕜 : Type u_1) (E : Type u_2) [is_R_or_C 𝕜] [inner_product_space 𝕜 E] : galois_connection submodule.orthogonal submodule.orthogonal := sorry

/-- `submodule.orthogonal` reverses the `≤` ordering of two
subspaces. -/
theorem submodule.orthogonal_le {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {K₁ : submodule 𝕜 E} {K₂ : submodule 𝕜 E} (h : K₁ ≤ K₂) : K₂ᗮ ≤ (K₁ᗮ) :=
  galois_connection.monotone_l (submodule.orthogonal_gc 𝕜 E) h

/-- `submodule.orthogonal.orthogonal` preserves the `≤` ordering of two
subspaces. -/
theorem submodule.orthogonal_orthogonal_monotone {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {K₁ : submodule 𝕜 E} {K₂ : submodule 𝕜 E} (h : K₁ ≤ K₂) : K₁ᗮᗮ ≤ (K₂ᗮᗮ) :=
  submodule.orthogonal_le (submodule.orthogonal_le h)

/-- `K` is contained in `Kᗮᗮ`. -/
theorem submodule.le_orthogonal_orthogonal {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (K : submodule 𝕜 E) : K ≤ (Kᗮᗮ) :=
  galois_connection.le_u_l (submodule.orthogonal_gc 𝕜 E) K

/-- The inf of two orthogonal subspaces equals the subspace orthogonal
to the sup. -/
theorem submodule.inf_orthogonal {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (K₁ : submodule 𝕜 E) (K₂ : submodule 𝕜 E) : K₁ᗮ ⊓ (K₂ᗮ) = (K₁ ⊔ K₂ᗮ) :=
  Eq.symm (galois_connection.l_sup (submodule.orthogonal_gc 𝕜 E))

/-- The inf of an indexed family of orthogonal subspaces equals the
subspace orthogonal to the sup. -/
theorem submodule.infi_orthogonal {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {ι : Type u_3} (K : ι → submodule 𝕜 E) : (infi fun (i : ι) => K iᗮ) = (supr Kᗮ) :=
  Eq.symm (galois_connection.l_supr (submodule.orthogonal_gc 𝕜 E))

/-- The inf of a set of orthogonal subspaces equals the subspace orthogonal to the sup. -/
theorem submodule.Inf_orthogonal {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (s : set (submodule 𝕜 E)) : (infi fun (K : submodule 𝕜 E) => infi fun (H : K ∈ s) => Kᗮ) = (Sup sᗮ) :=
  Eq.symm (galois_connection.l_Sup (submodule.orthogonal_gc 𝕜 E))

/-- If `K₁` is complete and contained in `K₂`, `K₁` and `K₁ᗮ ⊓ K₂` span `K₂`. -/
theorem submodule.sup_orthogonal_inf_of_is_complete {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {K₁ : submodule 𝕜 E} {K₂ : submodule 𝕜 E} (h : K₁ ≤ K₂) (hc : is_complete ↑K₁) : K₁ ⊔ K₁ᗮ ⊓ K₂ = K₂ := sorry

/-- If `K` is complete, `K` and `Kᗮ` span the whole space. -/
theorem submodule.sup_orthogonal_of_is_complete {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {K : submodule 𝕜 E} (h : is_complete ↑K) : K ⊔ (Kᗮ) = ⊤ := sorry

/-- If `K` is complete, `K` and `Kᗮ` span the whole space. Version using `complete_space`. -/
theorem submodule.sup_orthogonal_of_complete_space {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {K : submodule 𝕜 E} [complete_space ↥K] : K ⊔ (Kᗮ) = ⊤ :=
  submodule.sup_orthogonal_of_is_complete (iff.mp complete_space_coe_iff_is_complete _inst_4)

/-- If `K` is complete, any `v` in `E` can be expressed as a sum of elements of `K` and `Kᗮ`. -/
theorem submodule.exists_sum_mem_mem_orthogonal {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (K : submodule 𝕜 E) [complete_space ↥K] (v : E) : ∃ (y : E), ∃ (H : y ∈ K), ∃ (z : E), ∃ (H : z ∈ (Kᗮ)), v = y + z := sorry

/-- If `K` is complete, then the orthogonal complement of its orthogonal complement is itself. -/
@[simp] theorem submodule.orthogonal_orthogonal {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (K : submodule 𝕜 E) [complete_space ↥K] : Kᗮᗮ = K := sorry

theorem submodule.orthogonal_orthogonal_eq_closure {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (K : submodule 𝕜 E) [complete_space E] : Kᗮᗮ = submodule.topological_closure K := sorry

/-- If `K` is complete, `K` and `Kᗮ` are complements of each other. -/
theorem submodule.is_compl_orthogonal_of_is_complete {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {K : submodule 𝕜 E} (h : is_complete ↑K) : is_compl K (Kᗮ) :=
  is_compl.mk (submodule.orthogonal_disjoint K) (le_of_eq (Eq.symm (submodule.sup_orthogonal_of_is_complete h)))

@[simp] theorem submodule.top_orthogonal_eq_bot {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] : ⊤ᗮ = ⊥ := sorry

@[simp] theorem submodule.bot_orthogonal_eq_top {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] : ⊥ᗮ = ⊤ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (⊥ᗮ = ⊤)) (Eq.symm submodule.top_orthogonal_eq_bot)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (⊤ᗮᗮ = ⊤)) (propext eq_top_iff))) (submodule.le_orthogonal_orthogonal ⊤))

@[simp] theorem submodule.orthogonal_eq_bot_iff {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {K : submodule 𝕜 E} (hK : is_complete ↑K) : Kᗮ = ⊥ ↔ K = ⊤ := sorry

@[simp] theorem submodule.orthogonal_eq_top_iff {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {K : submodule 𝕜 E} : Kᗮ = ⊤ ↔ K = ⊥ := sorry

/-- A point in `K` with the orthogonality property (here characterized in terms of `Kᗮ`) must be the
orthogonal projection. -/
theorem eq_orthogonal_projection_of_mem_orthogonal {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {K : submodule 𝕜 E} [complete_space ↥K] {u : E} {v : E} (hv : v ∈ K) (hvo : u - v ∈ (Kᗮ)) : ↑(coe_fn (orthogonal_projection K) u) = v :=
  eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero hv fun (w : E) => iff.mp inner_eq_zero_sym ∘ hvo w

/-- A point in `K` with the orthogonality property (here characterized in terms of `Kᗮ`) must be the
orthogonal projection. -/
theorem eq_orthogonal_projection_of_mem_orthogonal' {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {K : submodule 𝕜 E} [complete_space ↥K] {u : E} {v : E} {z : E} (hv : v ∈ K) (hz : z ∈ (Kᗮ)) (hu : u = v + z) : ↑(coe_fn (orthogonal_projection K) u) = v := sorry

/-- The orthogonal projection onto `K` of an element of `Kᗮ` is zero. -/
theorem orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {K : submodule 𝕜 E} [complete_space ↥K] {v : E} (hv : v ∈ (Kᗮ)) : coe_fn (orthogonal_projection K) v = 0 := sorry

/-- The orthogonal projection onto `Kᗮ` of an element of `K` is zero. -/
theorem orthogonal_projection_mem_subspace_orthogonal_precomplement_eq_zero {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {K : submodule 𝕜 E} [complete_space E] {v : E} (hv : v ∈ K) : coe_fn (orthogonal_projection (Kᗮ)) v = 0 :=
  orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero (submodule.le_orthogonal_orthogonal K hv)

/-- The orthogonal projection onto `(𝕜 ∙ v)ᗮ` of `v` is zero. -/
theorem orthogonal_projection_orthogonal_complement_singleton_eq_zero {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [complete_space E] (v : E) : coe_fn (orthogonal_projection (submodule.span 𝕜 (singleton v)ᗮ)) v = 0 :=
  orthogonal_projection_mem_subspace_orthogonal_precomplement_eq_zero (submodule.mem_span_singleton_self v)

/-- In a complete space `E`, a vector splits as the sum of its orthogonal projections onto a
complete submodule `K` and onto the orthogonal complement of `K`.-/
theorem eq_sum_orthogonal_projection_self_orthogonal_complement {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (K : submodule 𝕜 E) [complete_space E] [complete_space ↥K] (w : E) : w = ↑(coe_fn (orthogonal_projection K) w) + ↑(coe_fn (orthogonal_projection (Kᗮ)) w) := sorry

/-- In a complete space `E`, the projection maps onto a complete subspace `K` and its orthogonal
complement sum to the identity. -/
theorem id_eq_sum_orthogonal_projection_self_orthogonal_complement {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (K : submodule 𝕜 E) [complete_space E] [complete_space ↥K] : continuous_linear_map.id 𝕜 E =
  continuous_linear_map.comp (submodule.subtype_continuous K) (orthogonal_projection K) +
    continuous_linear_map.comp (submodule.subtype_continuous (Kᗮ)) (orthogonal_projection (Kᗮ)) :=
  continuous_linear_map.ext fun (w : E) => eq_sum_orthogonal_projection_self_orthogonal_complement K w

/-- Given a finite-dimensional subspace `K₂`, and a subspace `K₁`
containined in it, the dimensions of `K₁` and the intersection of its
orthogonal subspace with `K₂` add to that of `K₂`. -/
theorem submodule.findim_add_inf_findim_orthogonal {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {K₁ : submodule 𝕜 E} {K₂ : submodule 𝕜 E} [finite_dimensional 𝕜 ↥K₂] (h : K₁ ≤ K₂) : finite_dimensional.findim 𝕜 ↥K₁ + finite_dimensional.findim 𝕜 ↥(K₁ᗮ ⊓ K₂) = finite_dimensional.findim 𝕜 ↥K₂ := sorry

/-- Given a finite-dimensional subspace `K₂`, and a subspace `K₁`
containined in it, the dimensions of `K₁` and the intersection of its
orthogonal subspace with `K₂` add to that of `K₂`. -/
theorem submodule.findim_add_inf_findim_orthogonal' {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {K₁ : submodule 𝕜 E} {K₂ : submodule 𝕜 E} [finite_dimensional 𝕜 ↥K₂] (h : K₁ ≤ K₂) {n : ℕ} (h_dim : finite_dimensional.findim 𝕜 ↥K₁ + n = finite_dimensional.findim 𝕜 ↥K₂) : finite_dimensional.findim 𝕜 ↥(K₁ᗮ ⊓ K₂) = n := sorry

/-- Given a finite-dimensional space `E` and subspace `K`, the dimensions of `K` and `Kᗮ` add to
that of `E`. -/
theorem submodule.findim_add_findim_orthogonal {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [finite_dimensional 𝕜 E] {K : submodule 𝕜 E} : finite_dimensional.findim 𝕜 ↥K + finite_dimensional.findim 𝕜 ↥(Kᗮ) = finite_dimensional.findim 𝕜 E := sorry

/-- Given a finite-dimensional space `E` and subspace `K`, the dimensions of `K` and `Kᗮ` add to
that of `E`. -/
theorem submodule.findim_add_findim_orthogonal' {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [finite_dimensional 𝕜 E] {K : submodule 𝕜 E} {n : ℕ} (h_dim : finite_dimensional.findim 𝕜 ↥K + n = finite_dimensional.findim 𝕜 E) : finite_dimensional.findim 𝕜 ↥(Kᗮ) = n := sorry

/-- In a finite-dimensional inner product space, the dimension of the orthogonal complement of the
span of a nonzero vector is one less than the dimension of the space. -/
theorem findim_orthogonal_span_singleton {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [finite_dimensional 𝕜 E] {v : E} (hv : v ≠ 0) : finite_dimensional.findim 𝕜 ↥(submodule.span 𝕜 (singleton v)ᗮ) = finite_dimensional.findim 𝕜 E - 1 := sorry

/-! ### Existence of Hilbert basis, orthonormal basis, etc. -/

/-- An orthonormal set in an `inner_product_space` is maximal, if and only if the orthogonal
complement of its span is empty. -/
theorem maximal_orthonormal_iff_orthogonal_complement_eq_bot {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {v : set E} (hv : orthonormal 𝕜 coe) : (∀ (u : set E), u ⊇ v → orthonormal 𝕜 coe → u = v) ↔ submodule.span 𝕜 vᗮ = ⊥ := sorry

/-- An orthonormal set in an `inner_product_space` is maximal, if and only if the closure of its
span is the whole space. -/
theorem maximal_orthonormal_iff_dense_span {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {v : set E} [complete_space E] (hv : orthonormal 𝕜 coe) : (∀ (u : set E), u ⊇ v → orthonormal 𝕜 coe → u = v) ↔ submodule.topological_closure (submodule.span 𝕜 v) = ⊤ := sorry

/-- Any orthonormal subset can be extended to an orthonormal set whose span is dense. -/
theorem exists_subset_is_orthonormal_dense_span {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {v : set E} [complete_space E] (hv : orthonormal 𝕜 coe) : ∃ (u : set E), ∃ (H : u ⊇ v), orthonormal 𝕜 coe ∧ submodule.topological_closure (submodule.span 𝕜 u) = ⊤ := sorry

/-- An inner product space admits an orthonormal set whose span is dense. -/
theorem exists_is_orthonormal_dense_span (𝕜 : Type u_1) (E : Type u_2) [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [complete_space E] : ∃ (u : set E), orthonormal 𝕜 coe ∧ submodule.topological_closure (submodule.span 𝕜 u) = ⊤ := sorry

/-- An orthonormal set in a finite-dimensional `inner_product_space` is maximal, if and only if it
is a basis. -/
theorem maximal_orthonormal_iff_is_basis_of_finite_dimensional {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {v : set E} [finite_dimensional 𝕜 E] (hv : orthonormal 𝕜 coe) : (∀ (u : set E), u ⊇ v → orthonormal 𝕜 coe → u = v) ↔ is_basis 𝕜 coe := sorry

/-- In a finite-dimensional `inner_product_space`, any orthonormal subset can be extended to an
orthonormal basis. -/
theorem exists_subset_is_orthonormal_basis {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {v : set E} [finite_dimensional 𝕜 E] (hv : orthonormal 𝕜 coe) : ∃ (u : set E), ∃ (H : u ⊇ v), orthonormal 𝕜 coe ∧ is_basis 𝕜 coe := sorry

/-- A finite-dimensional `inner_product_space` has an orthonormal basis. -/
theorem exists_is_orthonormal_basis (𝕜 : Type u_1) (E : Type u_2) [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [finite_dimensional 𝕜 E] : ∃ (u : set E), orthonormal 𝕜 coe ∧ is_basis 𝕜 coe := sorry

