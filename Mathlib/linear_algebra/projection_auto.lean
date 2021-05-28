/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury Kudryashov
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.linear_algebra.basic
import PostPort

universes u_1 u_2 u_3 u_4 

namespace Mathlib

/-!
# Projection to a subspace

In this file we define
* `linear_proj_of_is_compl (p q : submodule R E) (h : is_compl p q)`: the projection of a module `E`
  to a submodule `p` along its complement `q`; it is the unique linear map `f : E → p` such that
  `f x = x` for `x ∈ p` and `f x = 0` for `x ∈ q`.
* `is_compl_equiv_proj p`: equivalence between submodules `q` such that `is_compl p q` and
  projections `f : E → p`, `∀ x ∈ p, f x = x`.

We also provide some lemmas justifying correctness of our definitions.

## Tags

projection, complement subspace
-/

namespace linear_map


theorem ker_id_sub_eq_of_proj {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {p : submodule R E} {f : linear_map R E ↥p} (hf : ∀ (x : ↥p), coe_fn f ↑x = x) : ker (id - comp (submodule.subtype p) f) = p := sorry

theorem range_eq_of_proj {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {p : submodule R E} {f : linear_map R E ↥p} (hf : ∀ (x : ↥p), coe_fn f ↑x = x) : range f = ⊤ :=
  iff.mpr range_eq_top fun (x : ↥p) => Exists.intro (↑x) (hf x)

theorem is_compl_of_proj {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {p : submodule R E} {f : linear_map R E ↥p} (hf : ∀ (x : ↥p), coe_fn f ↑x = x) : is_compl p (ker f) := sorry

end linear_map


namespace submodule


/-- If `q` is a complement of `p`, then `M/p ≃ q`. -/
def quotient_equiv_of_is_compl {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] (p : submodule R E) (q : submodule R E) (h : is_compl p q) : linear_equiv R (quotient p) ↥q :=
  linear_equiv.symm (linear_equiv.of_bijective (linear_map.comp (mkq p) (submodule.subtype q)) sorry sorry)

@[simp] theorem quotient_equiv_of_is_compl_symm_apply {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] (p : submodule R E) (q : submodule R E) (h : is_compl p q) (x : ↥q) : coe_fn (linear_equiv.symm (quotient_equiv_of_is_compl p q h)) x = quotient.mk ↑x :=
  rfl

@[simp] theorem quotient_equiv_of_is_compl_apply_mk_coe {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] (p : submodule R E) (q : submodule R E) (h : is_compl p q) (x : ↥q) : coe_fn (quotient_equiv_of_is_compl p q h) (quotient.mk ↑x) = x :=
  linear_equiv.apply_symm_apply (quotient_equiv_of_is_compl p q h) x

@[simp] theorem mk_quotient_equiv_of_is_compl_apply {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] (p : submodule R E) (q : submodule R E) (h : is_compl p q) (x : quotient p) : quotient.mk ↑(coe_fn (quotient_equiv_of_is_compl p q h) x) = x :=
  linear_equiv.symm_apply_apply (quotient_equiv_of_is_compl p q h) x

/-- If `q` is a complement of `p`, then `p × q` is isomorphic to `E`. It is the unique
linear map `f : E → p` such that `f x = x` for `x ∈ p` and `f x = 0` for `x ∈ q`. -/
def prod_equiv_of_is_compl {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] (p : submodule R E) (q : submodule R E) (h : is_compl p q) : linear_equiv R (↥p × ↥q) E :=
  linear_equiv.of_bijective (linear_map.coprod (submodule.subtype p) (submodule.subtype q)) sorry sorry

@[simp] theorem coe_prod_equiv_of_is_compl {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] (p : submodule R E) (q : submodule R E) (h : is_compl p q) : ↑(prod_equiv_of_is_compl p q h) = linear_map.coprod (submodule.subtype p) (submodule.subtype q) :=
  rfl

@[simp] theorem coe_prod_equiv_of_is_compl' {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] (p : submodule R E) (q : submodule R E) (h : is_compl p q) (x : ↥p × ↥q) : coe_fn (prod_equiv_of_is_compl p q h) x = ↑(prod.fst x) + ↑(prod.snd x) :=
  rfl

@[simp] theorem prod_equiv_of_is_compl_symm_apply_left {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] (p : submodule R E) (q : submodule R E) (h : is_compl p q) (x : ↥p) : coe_fn (linear_equiv.symm (prod_equiv_of_is_compl p q h)) ↑x = (x, 0) := sorry

@[simp] theorem prod_equiv_of_is_compl_symm_apply_right {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] (p : submodule R E) (q : submodule R E) (h : is_compl p q) (x : ↥q) : coe_fn (linear_equiv.symm (prod_equiv_of_is_compl p q h)) ↑x = (0, x) := sorry

@[simp] theorem prod_equiv_of_is_compl_symm_apply_fst_eq_zero {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] (p : submodule R E) (q : submodule R E) (h : is_compl p q) {x : E} : prod.fst (coe_fn (linear_equiv.symm (prod_equiv_of_is_compl p q h)) x) = 0 ↔ x ∈ q := sorry

@[simp] theorem prod_equiv_of_is_compl_symm_apply_snd_eq_zero {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] (p : submodule R E) (q : submodule R E) (h : is_compl p q) {x : E} : prod.snd (coe_fn (linear_equiv.symm (prod_equiv_of_is_compl p q h)) x) = 0 ↔ x ∈ p := sorry

/-- Projection to a submodule along its complement. -/
def linear_proj_of_is_compl {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] (p : submodule R E) (q : submodule R E) (h : is_compl p q) : linear_map R E ↥p :=
  linear_map.comp (linear_map.fst R ↥p ↥q) ↑(linear_equiv.symm (prod_equiv_of_is_compl p q h))

@[simp] theorem linear_proj_of_is_compl_apply_left {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {p : submodule R E} {q : submodule R E} (h : is_compl p q) (x : ↥p) : coe_fn (linear_proj_of_is_compl p q h) ↑x = x := sorry

@[simp] theorem linear_proj_of_is_compl_range {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {p : submodule R E} {q : submodule R E} (h : is_compl p q) : linear_map.range (linear_proj_of_is_compl p q h) = ⊤ :=
  linear_map.range_eq_of_proj (linear_proj_of_is_compl_apply_left h)

@[simp] theorem linear_proj_of_is_compl_apply_eq_zero_iff {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {p : submodule R E} {q : submodule R E} (h : is_compl p q) {x : E} : coe_fn (linear_proj_of_is_compl p q h) x = 0 ↔ x ∈ q := sorry

theorem linear_proj_of_is_compl_apply_right' {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {p : submodule R E} {q : submodule R E} (h : is_compl p q) (x : E) (hx : x ∈ q) : coe_fn (linear_proj_of_is_compl p q h) x = 0 :=
  iff.mpr (linear_proj_of_is_compl_apply_eq_zero_iff h) hx

@[simp] theorem linear_proj_of_is_compl_apply_right {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {p : submodule R E} {q : submodule R E} (h : is_compl p q) (x : ↥q) : coe_fn (linear_proj_of_is_compl p q h) ↑x = 0 :=
  linear_proj_of_is_compl_apply_right' h (↑x) (subtype.property x)

@[simp] theorem linear_proj_of_is_compl_ker {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {p : submodule R E} {q : submodule R E} (h : is_compl p q) : linear_map.ker (linear_proj_of_is_compl p q h) = q :=
  ext fun (x : E) => iff.trans linear_map.mem_ker (linear_proj_of_is_compl_apply_eq_zero_iff h)

theorem linear_proj_of_is_compl_comp_subtype {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {p : submodule R E} {q : submodule R E} (h : is_compl p q) : linear_map.comp (linear_proj_of_is_compl p q h) (submodule.subtype p) = linear_map.id :=
  linear_map.ext (linear_proj_of_is_compl_apply_left h)

theorem linear_proj_of_is_compl_idempotent {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {p : submodule R E} {q : submodule R E} (h : is_compl p q) (x : E) : coe_fn (linear_proj_of_is_compl p q h) ↑(coe_fn (linear_proj_of_is_compl p q h) x) =
  coe_fn (linear_proj_of_is_compl p q h) x :=
  linear_proj_of_is_compl_apply_left h (coe_fn (linear_proj_of_is_compl p q h) x)

end submodule


namespace linear_map


@[simp] theorem linear_proj_of_is_compl_of_proj {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {p : submodule R E} (f : linear_map R E ↥p) (hf : ∀ (x : ↥p), coe_fn f ↑x = x) : submodule.linear_proj_of_is_compl p (ker f) (is_compl_of_proj hf) = f := sorry

/-- If `f : E →ₗ[R] F` and `g : E →ₗ[R] G` are two surjective linear maps and
their kernels are complement of each other, then `x ↦ (f x, g x)` defines
a linear equivalence `E ≃ₗ[R] F × G`. -/
def equiv_prod_of_surjective_of_is_compl {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] {G : Type u_4} [add_comm_group G] [module R G] (f : linear_map R E F) (g : linear_map R E G) (hf : range f = ⊤) (hg : range g = ⊤) (hfg : is_compl (ker f) (ker g)) : linear_equiv R E (F × G) :=
  linear_equiv.of_bijective (prod f g) sorry sorry

@[simp] theorem coe_equiv_prod_of_surjective_of_is_compl {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] {G : Type u_4} [add_comm_group G] [module R G] {f : linear_map R E F} {g : linear_map R E G} (hf : range f = ⊤) (hg : range g = ⊤) (hfg : is_compl (ker f) (ker g)) : ↑(equiv_prod_of_surjective_of_is_compl f g hf hg hfg) = prod f g :=
  rfl

@[simp] theorem equiv_prod_of_surjective_of_is_compl_apply {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] {G : Type u_4} [add_comm_group G] [module R G] {f : linear_map R E F} {g : linear_map R E G} (hf : range f = ⊤) (hg : range g = ⊤) (hfg : is_compl (ker f) (ker g)) (x : E) : coe_fn (equiv_prod_of_surjective_of_is_compl f g hf hg hfg) x = (coe_fn f x, coe_fn g x) :=
  rfl

end linear_map


namespace submodule


/-- Equivalence between submodules `q` such that `is_compl p q` and linear maps `f : E →ₗ[R] p`
such that `∀ x : p, f x = x`. -/
def is_compl_equiv_proj {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] (p : submodule R E) : (Subtype fun (q : submodule R E) => is_compl p q) ≃ Subtype fun (f : linear_map R E ↥p) => ∀ (x : ↥p), coe_fn f ↑x = x :=
  equiv.mk
    (fun (q : Subtype fun (q : submodule R E) => is_compl p q) =>
      { val := linear_proj_of_is_compl p ↑q sorry, property := sorry })
    (fun (f : Subtype fun (f : linear_map R E ↥p) => ∀ (x : ↥p), coe_fn f ↑x = x) =>
      { val := linear_map.ker ↑f, property := sorry })
    sorry sorry

@[simp] theorem coe_is_compl_equiv_proj_apply {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] (p : submodule R E) (q : Subtype fun (q : submodule R E) => is_compl p q) : ↑(coe_fn (is_compl_equiv_proj p) q) = linear_proj_of_is_compl p (↑q) (subtype.property q) :=
  rfl

@[simp] theorem coe_is_compl_equiv_proj_symm_apply {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] (p : submodule R E) (f : Subtype fun (f : linear_map R E ↥p) => ∀ (x : ↥p), coe_fn f ↑x = x) : ↑(coe_fn (equiv.symm (is_compl_equiv_proj p)) f) = linear_map.ker ↑f :=
  rfl

