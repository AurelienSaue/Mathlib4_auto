/-
Copyright (c) 2020 Alexander Bentkamp, Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Sébastien Gouëzel
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.complex.basic
import Mathlib.data.matrix.notation
import Mathlib.field_theory.tower
import Mathlib.linear_algebra.finite_dimensional
import PostPort

universes u u_1 

namespace Mathlib

/-!
# Complex number as a vector space over `ℝ`

This file contains three instances:
* `ℂ` is an `ℝ` algebra;
* any complex vector space is a real vector space;
* any finite dimensional complex vector space is a finite dimesional real vector space;
* the space of `ℝ`-linear maps from a real vector space to a complex vector space is a complex
  vector space.

It also defines three linear maps:

* `complex.linear_map.re`;
* `complex.linear_map.im`;
* `complex.linear_map.of_real`.

They are bundled versions of the real part, the imaginary part, and the embedding of `ℝ` in `ℂ`,
as `ℝ`-linear maps.
-/

namespace complex


protected instance algebra_over_reals : algebra ℝ ℂ :=
  ring_hom.to_algebra of_real

@[simp] theorem coe_algebra_map : ⇑(algebra_map ℝ ℂ) = ⇑of_real :=
  rfl

@[simp] theorem re_smul (a : ℝ) (z : ℂ) : re (a • z) = a * re z := sorry

@[simp] theorem im_smul (a : ℝ) (z : ℂ) : im (a • z) = a * im z := sorry

theorem is_basis_one_I : is_basis ℝ (matrix.vec_cons 1 (matrix.vec_cons I matrix.vec_empty)) := sorry

protected instance finite_dimensional : finite_dimensional ℝ ℂ :=
  finite_dimensional.of_fintype_basis is_basis_one_I

@[simp] theorem findim_real_complex : finite_dimensional.findim ℝ ℂ = bit0 1 := sorry

@[simp] theorem dim_real_complex : vector_space.dim ℝ ℂ = bit0 1 := sorry

theorem dim_real_complex' : cardinal.lift (vector_space.dim ℝ ℂ) = bit0 1 := sorry

end complex


/- Register as an instance (with low priority) the fact that a complex vector space is also a real
vector space. -/

protected instance module.complex_to_real (E : Type u_1) [add_comm_group E] [module ℂ E] : module ℝ E :=
  restrict_scalars.semimodule ℝ ℂ E

protected instance module.real_complex_tower (E : Type u_1) [add_comm_group E] [module ℂ E] : is_scalar_tower ℝ ℂ E :=
  restrict_scalars.is_scalar_tower ℝ ℂ E

protected instance finite_dimensional.complex_to_real (E : Type u_1) [add_comm_group E] [module ℂ E] [finite_dimensional ℂ E] : finite_dimensional ℝ E :=
  finite_dimensional.trans ℝ ℂ E

theorem dim_real_of_complex (E : Type u_1) [add_comm_group E] [module ℂ E] : vector_space.dim ℝ E = bit0 1 * vector_space.dim ℂ E := sorry

theorem findim_real_of_complex (E : Type u_1) [add_comm_group E] [module ℂ E] : finite_dimensional.findim ℝ E = bit0 1 * finite_dimensional.findim ℂ E := sorry

namespace complex


/-- Linear map version of the real part function, from `ℂ` to `ℝ`. -/
def linear_map.re : linear_map ℝ ℂ ℝ :=
  linear_map.mk (fun (x : ℂ) => re x) add_re re_smul

@[simp] theorem linear_map.coe_re : ⇑linear_map.re = re :=
  rfl

/-- Linear map version of the imaginary part function, from `ℂ` to `ℝ`. -/
def linear_map.im : linear_map ℝ ℂ ℝ :=
  linear_map.mk (fun (x : ℂ) => im x) add_im im_smul

@[simp] theorem linear_map.coe_im : ⇑linear_map.im = im :=
  rfl

/-- Linear map version of the canonical embedding of `ℝ` in `ℂ`. -/
def linear_map.of_real : linear_map ℝ ℝ ℂ :=
  linear_map.mk coe of_real_add sorry

@[simp] theorem linear_map.coe_of_real : ⇑linear_map.of_real = coe :=
  rfl

