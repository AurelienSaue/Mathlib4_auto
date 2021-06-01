/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.analysis.normed_space.banach
import Mathlib.analysis.normed_space.finite_dimension
import Mathlib.PostPort

universes u_1 u_2 u_3 u_4 

namespace Mathlib

/-!
# Complemented subspaces of normed vector spaces

A submodule `p` of a topological module `E` over `R` is called *complemented* if there exists
a continuous linear projection `f : E →ₗ[R] p`, `∀ x : p, f x = x`. We prove that for
a closed subspace of a normed space this condition is equivalent to existence of a closed
subspace `q` such that `p ⊓ q = ⊥`, `p ⊔ q = ⊤`. We also prove that a subspace of finite codimension
is always a complemented subspace.

## Tags

complemented subspace, normed vector space
-/

namespace continuous_linear_map


theorem ker_closed_complemented_of_finite_dimensional_range {𝕜 : Type u_1}
    [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3}
    [normed_group F] [normed_space 𝕜 F] [complete_space 𝕜] (f : continuous_linear_map 𝕜 E F)
    [finite_dimensional 𝕜 ↥(range f)] : submodule.closed_complemented (ker f) :=
  sorry

/-- If `f : E →L[R] F` and `g : E →L[R] G` are two surjective linear maps and
their kernels are complement of each other, then `x ↦ (f x, g x)` defines
a linear equivalence `E ≃L[R] F × G`. -/
def equiv_prod_of_surjective_of_is_compl {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {G : Type u_4} [normed_group G] [normed_space 𝕜 G] [complete_space E] [complete_space (F × G)]
    (f : continuous_linear_map 𝕜 E F) (g : continuous_linear_map 𝕜 E G) (hf : range f = ⊤)
    (hg : range g = ⊤) (hfg : is_compl (ker f) (ker g)) : continuous_linear_equiv 𝕜 E (F × G) :=
  linear_equiv.to_continuous_linear_equiv_of_continuous
    (linear_map.equiv_prod_of_surjective_of_is_compl (↑f) (↑g) hf hg hfg) sorry

@[simp] theorem coe_equiv_prod_of_surjective_of_is_compl {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] [complete_space E]
    [complete_space (F × G)] {f : continuous_linear_map 𝕜 E F} {g : continuous_linear_map 𝕜 E G}
    (hf : range f = ⊤) (hg : range g = ⊤) (hfg : is_compl (ker f) (ker g)) :
    ↑(equiv_prod_of_surjective_of_is_compl f g hf hg hfg) = ↑(continuous_linear_map.prod f g) :=
  rfl

@[simp] theorem equiv_prod_of_surjective_of_is_compl_to_linear_equiv {𝕜 : Type u_1}
    [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3}
    [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G]
    [complete_space E] [complete_space (F × G)] {f : continuous_linear_map 𝕜 E F}
    {g : continuous_linear_map 𝕜 E G} (hf : range f = ⊤) (hg : range g = ⊤)
    (hfg : is_compl (ker f) (ker g)) :
    continuous_linear_equiv.to_linear_equiv (equiv_prod_of_surjective_of_is_compl f g hf hg hfg) =
        linear_map.equiv_prod_of_surjective_of_is_compl (↑f) (↑g) hf hg hfg :=
  rfl

@[simp] theorem equiv_prod_of_surjective_of_is_compl_apply {𝕜 : Type u_1}
    [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3}
    [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G]
    [complete_space E] [complete_space (F × G)] {f : continuous_linear_map 𝕜 E F}
    {g : continuous_linear_map 𝕜 E G} (hf : range f = ⊤) (hg : range g = ⊤)
    (hfg : is_compl (ker f) (ker g)) (x : E) :
    coe_fn (equiv_prod_of_surjective_of_is_compl f g hf hg hfg) x = (coe_fn f x, coe_fn g x) :=
  rfl

end continuous_linear_map


namespace subspace


/-- If `q` is a closed complement of a closed subspace `p`, then `p × q` is continuously
isomorphic to `E`. -/
def prod_equiv_of_closed_compl {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] [complete_space E] (p : subspace 𝕜 E) (q : subspace 𝕜 E)
    (h : is_compl p q) (hp : is_closed ↑p) (hq : is_closed ↑q) :
    continuous_linear_equiv 𝕜 (↥p × ↥q) E :=
  linear_equiv.to_continuous_linear_equiv_of_continuous (submodule.prod_equiv_of_is_compl p q h)
    sorry

/-- Projection to a closed submodule along a closed complement. -/
def linear_proj_of_closed_compl {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] [complete_space E] (p : subspace 𝕜 E) (q : subspace 𝕜 E)
    (h : is_compl p q) (hp : is_closed ↑p) (hq : is_closed ↑q) : continuous_linear_map 𝕜 E ↥p :=
  continuous_linear_map.comp (continuous_linear_map.fst 𝕜 ↥p ↥q)
    ↑(continuous_linear_equiv.symm (prod_equiv_of_closed_compl p q h hp hq))

@[simp] theorem coe_prod_equiv_of_closed_compl {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] [complete_space E] {p : subspace 𝕜 E}
    {q : subspace 𝕜 E} (h : is_compl p q) (hp : is_closed ↑p) (hq : is_closed ↑q) :
    ⇑(prod_equiv_of_closed_compl p q h hp hq) = ⇑(submodule.prod_equiv_of_is_compl p q h) :=
  rfl

@[simp] theorem coe_prod_equiv_of_closed_compl_symm {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] [complete_space E] {p : subspace 𝕜 E}
    {q : subspace 𝕜 E} (h : is_compl p q) (hp : is_closed ↑p) (hq : is_closed ↑q) :
    ⇑(continuous_linear_equiv.symm (prod_equiv_of_closed_compl p q h hp hq)) =
        ⇑(linear_equiv.symm (submodule.prod_equiv_of_is_compl p q h)) :=
  rfl

@[simp] theorem coe_continuous_linear_proj_of_closed_compl {𝕜 : Type u_1}
    [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E]
    [complete_space E] {p : subspace 𝕜 E} {q : subspace 𝕜 E} (h : is_compl p q) (hp : is_closed ↑p)
    (hq : is_closed ↑q) :
    ↑(linear_proj_of_closed_compl p q h hp hq) = submodule.linear_proj_of_is_compl p q h :=
  rfl

@[simp] theorem coe_continuous_linear_proj_of_closed_compl' {𝕜 : Type u_1}
    [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E]
    [complete_space E] {p : subspace 𝕜 E} {q : subspace 𝕜 E} (h : is_compl p q) (hp : is_closed ↑p)
    (hq : is_closed ↑q) :
    ⇑(linear_proj_of_closed_compl p q h hp hq) = ⇑(submodule.linear_proj_of_is_compl p q h) :=
  rfl

theorem closed_complemented_of_closed_compl {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] [complete_space E] {p : subspace 𝕜 E}
    {q : subspace 𝕜 E} (h : is_compl p q) (hp : is_closed ↑p) (hq : is_closed ↑q) :
    submodule.closed_complemented p :=
  Exists.intro (linear_proj_of_closed_compl p q h hp hq)
    (submodule.linear_proj_of_is_compl_apply_left h)

theorem closed_complemented_iff_has_closed_compl {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] [complete_space E] {p : subspace 𝕜 E} :
    submodule.closed_complemented p ↔
        is_closed ↑p ∧ ∃ (q : subspace 𝕜 E), ∃ (hq : is_closed ↑q), is_compl p q :=
  sorry

theorem closed_complemented_of_quotient_finite_dimensional {𝕜 : Type u_1}
    [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E]
    [complete_space E] {p : subspace 𝕜 E} [complete_space 𝕜]
    [finite_dimensional 𝕜 (submodule.quotient p)] (hp : is_closed ↑p) :
    submodule.closed_complemented p :=
  sorry

end Mathlib