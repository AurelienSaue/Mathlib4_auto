/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.category.Module.kernels
import Mathlib.algebra.category.Module.limits
import Mathlib.category_theory.abelian.exact
import Mathlib.PostPort

universes u v u_1 

namespace Mathlib

/-!
# The category of left R-modules is abelian.

Additionally, two linear maps are exact in the categorical sense iff `range f = ker g`.
-/

namespace Module


/-- In the category of modules, every monomorphism is normal. -/
def normal_mono {R : Type u} [ring R] {M : Module R} {N : Module R} (f : M ⟶ N)
    (hf : category_theory.mono f) : category_theory.normal_mono f :=
  category_theory.normal_mono.mk (of R (submodule.quotient (linear_map.range f)))
    (submodule.mkq (linear_map.range f)) sorry
    (category_theory.limits.is_kernel.iso_kernel (submodule.mkq (linear_map.range f)) f
      (kernel_is_limit (submodule.mkq (linear_map.range f)))
      (linear_equiv.to_Module_iso'
        (linear_equiv.trans
          (linear_equiv.symm
            (submodule.quot_equiv_of_eq_bot (linear_map.ker f) (ker_eq_bot_of_mono f)))
          (linear_equiv.trans (linear_map.quot_ker_equiv_range f)
            (linear_equiv.of_eq (linear_map.range f)
              (linear_map.ker (submodule.mkq (linear_map.range f))) sorry))))
      sorry)

/-- In the category of modules, every epimorphism is normal. -/
def normal_epi {R : Type u} [ring R] {M : Module R} {N : Module R} (f : M ⟶ N)
    (hf : category_theory.epi f) : category_theory.normal_epi f :=
  category_theory.normal_epi.mk (of R ↥(linear_map.ker f)) (submodule.subtype (linear_map.ker f))
    sorry
    (category_theory.limits.is_cokernel.cokernel_iso (submodule.subtype (linear_map.ker f)) f
      (cokernel_is_colimit (submodule.subtype (linear_map.ker f)))
      (linear_equiv.to_Module_iso'
        (linear_equiv.trans
          (linear_equiv.trans
            (submodule.quot_equiv_of_eq (linear_map.range (submodule.subtype (linear_map.ker f)))
              (linear_map.ker f) sorry)
            (linear_map.quot_ker_equiv_range f))
          (linear_equiv.of_top (linear_map.range f) (range_eq_top_of_epi f))))
      sorry)

/-- The category of R-modules is abelian. -/
protected instance category_theory.abelian {R : Type u} [ring R] :
    category_theory.abelian (Module R) :=
  category_theory.abelian.mk (fun (X Y : Module R) => normal_mono)
    fun (X Y : Module R) => normal_epi

theorem exact_iff {R : Type u} [ring R] {M : Module R} {N : Module R} (f : M ⟶ N) {O : Module R}
    (g : N ⟶ O) : category_theory.exact f g ↔ linear_map.range f = linear_map.ker g :=
  sorry

end Mathlib