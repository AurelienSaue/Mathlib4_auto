/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.category.Module.basic
import Mathlib.PostPort

universes u v u_1 

namespace Mathlib

/-!
# The concrete (co)kernels in the category of modules are (co)kernels in the categorical sense.
-/

namespace Module


/-- The kernel cone induced by the concrete kernel. -/
def kernel_cone {R : Type u} [ring R] {M : Module R} {N : Module R} (f : M ⟶ N) :
    category_theory.limits.kernel_fork f :=
  category_theory.limits.kernel_fork.of_ι (as_hom (submodule.subtype (linear_map.ker f))) sorry

/-- The kernel of a linear map is a kernel in the categorical sense. -/
def kernel_is_limit {R : Type u} [ring R] {M : Module R} {N : Module R} (f : M ⟶ N) :
    category_theory.limits.is_limit (kernel_cone f) :=
  category_theory.limits.fork.is_limit.mk (kernel_cone f)
    (fun (s : category_theory.limits.fork f 0) =>
      linear_map.cod_restrict (linear_map.ker f) (category_theory.limits.fork.ι s) sorry)
    sorry sorry

/-- The cokernel cocone induced by the projection onto the quotient. -/
def cokernel_cocone {R : Type u} [ring R] {M : Module R} {N : Module R} (f : M ⟶ N) :
    category_theory.limits.cokernel_cofork f :=
  category_theory.limits.cokernel_cofork.of_π (as_hom (submodule.mkq (linear_map.range f))) sorry

/-- The projection onto the quotient is a cokernel in the categorical sense. -/
def cokernel_is_colimit {R : Type u} [ring R] {M : Module R} {N : Module R} (f : M ⟶ N) :
    category_theory.limits.is_colimit (cokernel_cocone f) :=
  category_theory.limits.cofork.is_colimit.mk (cokernel_cocone f)
    (fun (s : category_theory.limits.cofork f 0) =>
      submodule.liftq (linear_map.range f) (category_theory.limits.cofork.π s) sorry)
    sorry sorry

/-- The category of R-modules has kernels, given by the inclusion of the kernel submodule. -/
theorem has_kernels_Module {R : Type u} [ring R] : category_theory.limits.has_kernels (Module R) :=
  category_theory.limits.has_kernels.mk
    fun (X Y : Module R) (f : X ⟶ Y) =>
      category_theory.limits.has_limit.mk
        (category_theory.limits.limit_cone.mk (kernel_cone f) (kernel_is_limit f))

/-- The category or R-modules has cokernels, given by the projection onto the quotient. -/
theorem has_cokernels_Module {R : Type u} [ring R] :
    category_theory.limits.has_cokernels (Module R) :=
  sorry

end Mathlib