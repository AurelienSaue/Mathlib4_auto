/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.analysis.calculus.inverse
import Mathlib.analysis.normed_space.complemented
import Mathlib.PostPort

universes u_1 u_2 u_3 u_4 l 

namespace Mathlib

/-!
# Implicit function theorem

We prove three versions of the implicit function theorem. First we define a structure
`implicit_function_data` that holds arguments for the most general version of the implicit function
theorem, see `implicit_function_data.implicit_function`
and `implicit_function_data.to_implicit_function`. This version allows a user to choose
a specific implicit function but provides only a little convenience over the inverse function
theorem.

Then we define `implicit_function_of_complemented`: implicit function defined by `f (g z y) = z`,
where `f : E → F` is a function strictly differentiable at `a` such that its derivative `f'`
is surjective and has a `complemented` kernel.

Finally, if the codomain of `f` is a finite dimensional space, then we can automatically prove
that the kernel of `f'` is complemented, hence the only assumptions are `has_strict_fderiv_at`
and `f'.range = ⊤`. This version is named `implicit_function`.

## TODO

* Add a version for a function `f : E × F → G` such that $$\frac{\partial f}{\partial y}$$ is
  invertible.
* Add a version for `f : 𝕜 × 𝕜 → 𝕜` proving `has_strict_deriv_at` and `deriv φ = ...`.
* Prove that in a real vector space the implicit function has the same smoothness as the original
  one.
* If the original function is differentiable in a neighborhood, then the implicit function is
  differentiable in a neighborhood as well. Current setup only proves differentiability at one
  point for the implicit function constructed in this file (as opposed to an unspecified implicit
  function). One of the ways to overcome this difficulty is to use uniqueness of the implicit
  function in the general version of the theorem. Another way is to prove that *any* implicit
  function satisfying some predicate is strictly differentiable.

## Tags

implicit function, inverse function
-/

/-!
### General version

Consider two functions `f : E → F` and `g : E → G` and a point `a` such that

* both functions are strictly differentiable at `a`;
* the derivatives are surjective;
* the kernels of the derivatives are complementary subspaces of `E`.

Note that the map `x ↦ (f x, g x)` has a bijective derivative, hence it is a local homeomorphism
between `E` and `F × G`. We use this fact to define a function `φ : F → G → E`
(see `implicit_function_data.implicit_function`) such that for `(y, z)` close enough to `(f a, g a)`
we have `f (φ y z) = y` and `g (φ y z) = z`.

We also prove a formula for $$\frac{\partial\varphi}{\partial z}.$$

Though this statement is almost symmetric with respect to `F`, `G`, we interpret it in the following
way. Consider a family of surfaces `{x | f x = y}`, `y ∈ 𝓝 (f a)`. Each of these surfaces is
parametrized by `φ y`.

There are many ways to choose a (differentiable) function `φ` such that `f (φ y z) = y` but the
extra condition `g (φ y z) = z` allows a user to select one of these functions. If we imagine
that the level surfaces `f = const` form a local horizontal foliation, then the choice of
`g` fixes a transverse foliation `g = const`, and `φ` is the inverse function of the projection
of `{x | f x = y}` along this transverse foliation.

This version of the theorem is used to prove the other versions and can be used if a user
needs to have a complete control over the choice of the implicit function.
-/

/-- Data for the general version of the implicit function theorem. It holds two functions
`f : E → F` and `g : E → G` (named `left_fun` and `right_fun`) and a point `a` (named `pt`)
such that

* both functions are strictly differentiable at `a`;
* the derivatives are surjective;
* the kernels of the derivatives are complementary subspaces of `E`. -/
structure implicit_function_data (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] (E : Type u_2)
    [normed_group E] [normed_space 𝕜 E] [complete_space E] (F : Type u_3) [normed_group F]
    [normed_space 𝕜 F] [complete_space F] (G : Type u_4) [normed_group G] [normed_space 𝕜 G]
    [complete_space G]
    where
  left_fun : E → F
  left_deriv : continuous_linear_map 𝕜 E F
  right_fun : E → G
  right_deriv : continuous_linear_map 𝕜 E G
  pt : E
  left_has_deriv : has_strict_fderiv_at left_fun left_deriv pt
  right_has_deriv : has_strict_fderiv_at right_fun right_deriv pt
  left_range : continuous_linear_map.range left_deriv = ⊤
  right_range : continuous_linear_map.range right_deriv = ⊤
  is_compl_ker :
    is_compl (continuous_linear_map.ker left_deriv) (continuous_linear_map.ker right_deriv)

namespace implicit_function_data


/-- The function given by `x ↦ (left_fun x, right_fun x)`. -/
def prod_fun {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] [complete_space E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    [complete_space F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] [complete_space G]
    (φ : implicit_function_data 𝕜 E F G) (x : E) : F × G :=
  (left_fun φ x, right_fun φ x)

@[simp] theorem prod_fun_apply {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] [complete_space E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] [complete_space F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G]
    [complete_space G] (φ : implicit_function_data 𝕜 E F G) (x : E) :
    prod_fun φ x = (left_fun φ x, right_fun φ x) :=
  rfl

protected theorem has_strict_fderiv_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] [complete_space E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] [complete_space F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G]
    [complete_space G] (φ : implicit_function_data 𝕜 E F G) :
    has_strict_fderiv_at (prod_fun φ)
        (↑(continuous_linear_map.equiv_prod_of_surjective_of_is_compl (left_deriv φ) (right_deriv φ)
            (left_range φ) (right_range φ) (is_compl_ker φ)))
        (pt φ) :=
  has_strict_fderiv_at.prod (left_has_deriv φ) (right_has_deriv φ)

/-- Implicit function theorem. If `f : E → F` and `g : E → G` are two maps strictly differentiable
at `a`, their derivatives `f'`, `g'` are surjective, and the kernels of these derivatives are
complementary subspaces of `E`, then `x ↦ (f x, g x)` defines a local homeomorphism between
`E` and `F × G`. In particular, `{x | f x = f a}` is locally homeomorphic to `G`. -/
def to_local_homeomorph {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] [complete_space E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    [complete_space F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] [complete_space G]
    (φ : implicit_function_data 𝕜 E F G) : local_homeomorph E (F × G) :=
  has_strict_fderiv_at.to_local_homeomorph (prod_fun φ)
    (implicit_function_data.has_strict_fderiv_at φ)

/-- Implicit function theorem. If `f : E → F` and `g : E → G` are two maps strictly differentiable
at `a`, their derivatives `f'`, `g'` are surjective, and the kernels of these derivatives are
complementary subspaces of `E`, then `implicit_function_of_is_compl_ker` is the unique (germ of a)
map `φ : F → G → E` such that `f (φ y z) = y` and `g (φ y z) = z`. -/
def implicit_function {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] [complete_space E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    [complete_space F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] [complete_space G]
    (φ : implicit_function_data 𝕜 E F G) : F → G → E :=
  function.curry ⇑(local_homeomorph.symm (to_local_homeomorph φ))

@[simp] theorem to_local_homeomorph_coe {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] [complete_space E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] [complete_space F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G]
    [complete_space G] (φ : implicit_function_data 𝕜 E F G) :
    ⇑(to_local_homeomorph φ) = prod_fun φ :=
  rfl

theorem to_local_homeomorph_apply {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] [complete_space E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] [complete_space F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G]
    [complete_space G] (φ : implicit_function_data 𝕜 E F G) (x : E) :
    coe_fn (to_local_homeomorph φ) x = (left_fun φ x, right_fun φ x) :=
  rfl

theorem pt_mem_to_local_homeomorph_source {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] [complete_space E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] [complete_space F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G]
    [complete_space G] (φ : implicit_function_data 𝕜 E F G) :
    pt φ ∈ local_equiv.source (local_homeomorph.to_local_equiv (to_local_homeomorph φ)) :=
  has_strict_fderiv_at.mem_to_local_homeomorph_source
    (implicit_function_data.has_strict_fderiv_at φ)

theorem map_pt_mem_to_local_homeomorph_target {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] [complete_space E] {F : Type u_3}
    [normed_group F] [normed_space 𝕜 F] [complete_space F] {G : Type u_4} [normed_group G]
    [normed_space 𝕜 G] [complete_space G] (φ : implicit_function_data 𝕜 E F G) :
    (left_fun φ (pt φ), right_fun φ (pt φ)) ∈
        local_equiv.target (local_homeomorph.to_local_equiv (to_local_homeomorph φ)) :=
  local_homeomorph.map_source (to_local_homeomorph φ) (pt_mem_to_local_homeomorph_source φ)

theorem prod_map_implicit_function {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] [complete_space E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] [complete_space F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G]
    [complete_space G] (φ : implicit_function_data 𝕜 E F G) :
    filter.eventually
        (fun (p : F × G) => prod_fun φ (implicit_function φ (prod.fst p) (prod.snd p)) = p)
        (nhds (prod_fun φ (pt φ))) :=
  sorry

theorem left_map_implicit_function {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] [complete_space E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] [complete_space F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G]
    [complete_space G] (φ : implicit_function_data 𝕜 E F G) :
    filter.eventually
        (fun (p : F × G) => left_fun φ (implicit_function φ (prod.fst p) (prod.snd p)) = prod.fst p)
        (nhds (prod_fun φ (pt φ))) :=
  filter.eventually.mono (prod_map_implicit_function φ) fun (z : F × G) => congr_arg prod.fst

theorem right_map_implicit_function {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] [complete_space E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] [complete_space F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G]
    [complete_space G] (φ : implicit_function_data 𝕜 E F G) :
    filter.eventually
        (fun (p : F × G) =>
          right_fun φ (implicit_function φ (prod.fst p) (prod.snd p)) = prod.snd p)
        (nhds (prod_fun φ (pt φ))) :=
  filter.eventually.mono (prod_map_implicit_function φ) fun (z : F × G) => congr_arg prod.snd

theorem implicit_function_apply_image {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] [complete_space E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] [complete_space F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G]
    [complete_space G] (φ : implicit_function_data 𝕜 E F G) :
    filter.eventually (fun (x : E) => implicit_function φ (left_fun φ x) (right_fun φ x) = x)
        (nhds (pt φ)) :=
  has_strict_fderiv_at.eventually_left_inverse (implicit_function_data.has_strict_fderiv_at φ)

theorem implicit_function_has_strict_fderiv_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] [complete_space E] {F : Type u_3}
    [normed_group F] [normed_space 𝕜 F] [complete_space F] {G : Type u_4} [normed_group G]
    [normed_space 𝕜 G] [complete_space G] (φ : implicit_function_data 𝕜 E F G)
    (g'inv : continuous_linear_map 𝕜 G E)
    (hg'inv : continuous_linear_map.comp (right_deriv φ) g'inv = continuous_linear_map.id 𝕜 G)
    (hg'invf : continuous_linear_map.comp (left_deriv φ) g'inv = 0) :
    has_strict_fderiv_at (implicit_function φ (left_fun φ (pt φ))) g'inv (right_fun φ (pt φ)) :=
  sorry

end implicit_function_data


namespace has_strict_fderiv_at


/-!
### Case of a complemented kernel

In this section we prove the following version of the implicit function theorem. Consider a map
`f : E → F` and a point `a : E` such that `f` is strictly differentiable at `a`, its derivative `f'`
is surjective and the kernel of `f'` is a complemented subspace of `E` (i.e., it has a closed
complementary subspace). Then there exists a function `φ : F → ker f' → E` such that for `(y, z)`
close to `(f a, 0)` we have `f (φ y z) = y` and the derivative of `φ (f a)` at zero is the
embedding `ker f' → E`.

Note that a map with these properties is not unique. E.g., different choices of a subspace
complementary to `ker f'` lead to different maps `φ`.
-/

/-- Data used to apply the generic implicit function theorem to the case of a strictly
differentiable map such that its derivative is surjective and has a complemented kernel. -/
@[simp] def implicit_function_data_of_complemented {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] [complete_space E] {F : Type u_3}
    [normed_group F] [normed_space 𝕜 F] [complete_space F] (f : E → F)
    (f' : continuous_linear_map 𝕜 E F) {a : E} (hf : has_strict_fderiv_at f f' a)
    (hf' : continuous_linear_map.range f' = ⊤)
    (hker : submodule.closed_complemented (continuous_linear_map.ker f')) :
    implicit_function_data 𝕜 E F ↥(continuous_linear_map.ker f') :=
  implicit_function_data.mk f f' (fun (x : E) => coe_fn (classical.some hker) (x - a))
    (classical.some hker) a hf sorry hf' sorry sorry

/-- A local homeomorphism between `E` and `F × f'.ker` sending level surfaces of `f`
to vertical subspaces. -/
def implicit_to_local_homeomorph_of_complemented {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] [complete_space E] {F : Type u_3}
    [normed_group F] [normed_space 𝕜 F] [complete_space F] (f : E → F)
    (f' : continuous_linear_map 𝕜 E F) {a : E} (hf : has_strict_fderiv_at f f' a)
    (hf' : continuous_linear_map.range f' = ⊤)
    (hker : submodule.closed_complemented (continuous_linear_map.ker f')) :
    local_homeomorph E (F × ↥(continuous_linear_map.ker f')) :=
  implicit_function_data.to_local_homeomorph
    (implicit_function_data_of_complemented f f' hf hf' hker)

/-- Implicit function `g` defined by `f (g z y) = z`. -/
def implicit_function_of_complemented {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] [complete_space E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] [complete_space F] (f : E → F) (f' : continuous_linear_map 𝕜 E F) {a : E}
    (hf : has_strict_fderiv_at f f' a) (hf' : continuous_linear_map.range f' = ⊤)
    (hker : submodule.closed_complemented (continuous_linear_map.ker f')) :
    F → ↥(continuous_linear_map.ker f') → E :=
  implicit_function_data.implicit_function (implicit_function_data_of_complemented f f' hf hf' hker)

@[simp] theorem implicit_to_local_homeomorph_of_complemented_fst {𝕜 : Type u_1}
    [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E]
    [complete_space E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] [complete_space F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {a : E} (hf : has_strict_fderiv_at f f' a)
    (hf' : continuous_linear_map.range f' = ⊤)
    (hker : submodule.closed_complemented (continuous_linear_map.ker f')) (x : E) :
    prod.fst (coe_fn (implicit_to_local_homeomorph_of_complemented f f' hf hf' hker) x) = f x :=
  rfl

theorem implicit_to_local_homeomorph_of_complemented_apply {𝕜 : Type u_1}
    [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E]
    [complete_space E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] [complete_space F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {a : E} (hf : has_strict_fderiv_at f f' a)
    (hf' : continuous_linear_map.range f' = ⊤)
    (hker : submodule.closed_complemented (continuous_linear_map.ker f')) (y : E) :
    coe_fn (implicit_to_local_homeomorph_of_complemented f f' hf hf' hker) y =
        (f y, coe_fn (classical.some hker) (y - a)) :=
  rfl

@[simp] theorem implicit_to_local_homeomorph_of_complemented_apply_ker {𝕜 : Type u_1}
    [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E]
    [complete_space E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] [complete_space F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {a : E} (hf : has_strict_fderiv_at f f' a)
    (hf' : continuous_linear_map.range f' = ⊤)
    (hker : submodule.closed_complemented (continuous_linear_map.ker f'))
    (y : ↥(continuous_linear_map.ker f')) :
    coe_fn (implicit_to_local_homeomorph_of_complemented f f' hf hf' hker) (↑y + a) =
        (f (↑y + a), y) :=
  sorry

@[simp] theorem implicit_to_local_homeomorph_of_complemented_self {𝕜 : Type u_1}
    [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E]
    [complete_space E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] [complete_space F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {a : E} (hf : has_strict_fderiv_at f f' a)
    (hf' : continuous_linear_map.range f' = ⊤)
    (hker : submodule.closed_complemented (continuous_linear_map.ker f')) :
    coe_fn (implicit_to_local_homeomorph_of_complemented f f' hf hf' hker) a = (f a, 0) :=
  sorry

theorem mem_implicit_to_local_homeomorph_of_complemented_source {𝕜 : Type u_1}
    [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E]
    [complete_space E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] [complete_space F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {a : E} (hf : has_strict_fderiv_at f f' a)
    (hf' : continuous_linear_map.range f' = ⊤)
    (hker : submodule.closed_complemented (continuous_linear_map.ker f')) :
    a ∈
        local_equiv.source
          (local_homeomorph.to_local_equiv
            (implicit_to_local_homeomorph_of_complemented f f' hf hf' hker)) :=
  mem_to_local_homeomorph_source
    (implicit_function_data.has_strict_fderiv_at
      (implicit_function_data_of_complemented f f' hf hf' hker))

theorem mem_implicit_to_local_homeomorph_of_complemented_target {𝕜 : Type u_1}
    [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E]
    [complete_space E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] [complete_space F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {a : E} (hf : has_strict_fderiv_at f f' a)
    (hf' : continuous_linear_map.range f' = ⊤)
    (hker : submodule.closed_complemented (continuous_linear_map.ker f')) :
    (f a, 0) ∈
        local_equiv.target
          (local_homeomorph.to_local_equiv
            (implicit_to_local_homeomorph_of_complemented f f' hf hf' hker)) :=
  sorry

/-- `implicit_function_of_complemented` sends `(z, y)` to a point in `f ⁻¹' z`. -/
theorem map_implicit_function_of_complemented_eq {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] [complete_space E] {F : Type u_3}
    [normed_group F] [normed_space 𝕜 F] [complete_space F] {f : E → F}
    {f' : continuous_linear_map 𝕜 E F} {a : E} (hf : has_strict_fderiv_at f f' a)
    (hf' : continuous_linear_map.range f' = ⊤)
    (hker : submodule.closed_complemented (continuous_linear_map.ker f')) :
    filter.eventually
        (fun (p : F × ↥(continuous_linear_map.ker f')) =>
          f (implicit_function_of_complemented f f' hf hf' hker (prod.fst p) (prod.snd p)) =
            prod.fst p)
        (nhds (f a, 0)) :=
  sorry

/-- Any point in some neighborhood of `a` can be represented as `implicit_function`
of some point. -/
theorem eq_implicit_function_of_complemented {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] [complete_space E] {F : Type u_3}
    [normed_group F] [normed_space 𝕜 F] [complete_space F] {f : E → F}
    {f' : continuous_linear_map 𝕜 E F} {a : E} (hf : has_strict_fderiv_at f f' a)
    (hf' : continuous_linear_map.range f' = ⊤)
    (hker : submodule.closed_complemented (continuous_linear_map.ker f')) :
    filter.eventually
        (fun (x : E) =>
          implicit_function_of_complemented f f' hf hf' hker (f x)
              (prod.snd
                (coe_fn (implicit_to_local_homeomorph_of_complemented f f' hf hf' hker) x)) =
            x)
        (nhds a) :=
  implicit_function_data.implicit_function_apply_image
    (implicit_function_data_of_complemented f f' hf hf' hker)

theorem to_implicit_function_of_complemented {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] [complete_space E] {F : Type u_3}
    [normed_group F] [normed_space 𝕜 F] [complete_space F] {f : E → F}
    {f' : continuous_linear_map 𝕜 E F} {a : E} (hf : has_strict_fderiv_at f f' a)
    (hf' : continuous_linear_map.range f' = ⊤)
    (hker : submodule.closed_complemented (continuous_linear_map.ker f')) :
    has_strict_fderiv_at (implicit_function_of_complemented f f' hf hf' hker (f a))
        (continuous_linear_map.subtype_val (continuous_linear_map.ker f')) 0 :=
  sorry

/-!
### Finite dimensional case

In this section we prove the following version of the implicit function theorem. Consider a map
`f : E → F` from a Banach normed space to a finite dimensional space.
Take a point `a : E` such that `f` is strictly differentiable at `a` and its derivative `f'`
is surjective. Then there exists a function `φ : F → ker f' → E` such that for `(y, z)`
close to `(f a, 0)` we have `f (φ y z) = y` and the derivative of `φ (f a)` at zero is the
embedding `ker f' → E`.

This version deduces that `ker f'` is a complemented subspace from the fact that `F` is a finite
dimensional space, then applies the previous version.

Note that a map with these properties is not unique. E.g., different choices of a subspace
complementary to `ker f'` lead to different maps `φ`.
-/

/-- Given a map `f : E → F` to a finite dimensional space with a surjective derivative `f'`,
returns a local homeomorphism between `E` and `F × ker f'`. -/
def implicit_to_local_homeomorph {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] [complete_space 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] [complete_space E] {F : Type u_3}
    [normed_group F] [normed_space 𝕜 F] [finite_dimensional 𝕜 F] (f : E → F)
    (f' : continuous_linear_map 𝕜 E F) {a : E} (hf : has_strict_fderiv_at f f' a)
    (hf' : continuous_linear_map.range f' = ⊤) :
    local_homeomorph E (F × ↥(continuous_linear_map.ker f')) :=
  implicit_to_local_homeomorph_of_complemented f f' hf hf' sorry

/-- Implicit function `g` defined by `f (g z y) = z`. -/
def implicit_function {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] [complete_space 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] [complete_space E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] [finite_dimensional 𝕜 F] (f : E → F) (f' : continuous_linear_map 𝕜 E F)
    {a : E} (hf : has_strict_fderiv_at f f' a) (hf' : continuous_linear_map.range f' = ⊤) :
    F → ↥(continuous_linear_map.ker f') → E :=
  function.curry ⇑(local_homeomorph.symm (implicit_to_local_homeomorph f f' hf hf'))

@[simp] theorem implicit_to_local_homeomorph_fst {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    [complete_space 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] [complete_space E]
    {F : Type u_3} [normed_group F] [normed_space 𝕜 F] [finite_dimensional 𝕜 F] {f : E → F}
    {f' : continuous_linear_map 𝕜 E F} {a : E} (hf : has_strict_fderiv_at f f' a)
    (hf' : continuous_linear_map.range f' = ⊤) (x : E) :
    prod.fst (coe_fn (implicit_to_local_homeomorph f f' hf hf') x) = f x :=
  rfl

@[simp] theorem implicit_to_local_homeomorph_apply_ker {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    [complete_space 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] [complete_space E]
    {F : Type u_3} [normed_group F] [normed_space 𝕜 F] [finite_dimensional 𝕜 F] {f : E → F}
    {f' : continuous_linear_map 𝕜 E F} {a : E} (hf : has_strict_fderiv_at f f' a)
    (hf' : continuous_linear_map.range f' = ⊤) (y : ↥(continuous_linear_map.ker f')) :
    coe_fn (implicit_to_local_homeomorph f f' hf hf') (↑y + a) = (f (↑y + a), y) :=
  implicit_to_local_homeomorph_of_complemented_apply_ker hf hf'
    (implicit_to_local_homeomorph._proof_1 f') y

@[simp] theorem implicit_to_local_homeomorph_self {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    [complete_space 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] [complete_space E]
    {F : Type u_3} [normed_group F] [normed_space 𝕜 F] [finite_dimensional 𝕜 F] {f : E → F}
    {f' : continuous_linear_map 𝕜 E F} {a : E} (hf : has_strict_fderiv_at f f' a)
    (hf' : continuous_linear_map.range f' = ⊤) :
    coe_fn (implicit_to_local_homeomorph f f' hf hf') a = (f a, 0) :=
  implicit_to_local_homeomorph_of_complemented_self hf hf'
    (implicit_to_local_homeomorph._proof_1 f')

theorem mem_implicit_to_local_homeomorph_source {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    [complete_space 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] [complete_space E]
    {F : Type u_3} [normed_group F] [normed_space 𝕜 F] [finite_dimensional 𝕜 F] {f : E → F}
    {f' : continuous_linear_map 𝕜 E F} {a : E} (hf : has_strict_fderiv_at f f' a)
    (hf' : continuous_linear_map.range f' = ⊤) :
    a ∈
        local_equiv.source
          (local_homeomorph.to_local_equiv (implicit_to_local_homeomorph f f' hf hf')) :=
  mem_to_local_homeomorph_source
    (implicit_function_data.has_strict_fderiv_at
      (implicit_function_data_of_complemented f f' hf hf'
        (implicit_to_local_homeomorph._proof_1 f')))

theorem mem_implicit_to_local_homeomorph_target {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    [complete_space 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] [complete_space E]
    {F : Type u_3} [normed_group F] [normed_space 𝕜 F] [finite_dimensional 𝕜 F] {f : E → F}
    {f' : continuous_linear_map 𝕜 E F} {a : E} (hf : has_strict_fderiv_at f f' a)
    (hf' : continuous_linear_map.range f' = ⊤) :
    (f a, 0) ∈
        local_equiv.target
          (local_homeomorph.to_local_equiv (implicit_to_local_homeomorph f f' hf hf')) :=
  mem_implicit_to_local_homeomorph_of_complemented_target hf hf'
    (implicit_to_local_homeomorph._proof_1 f')

/-- `implicit_function` sends `(z, y)` to a point in `f ⁻¹' z`. -/
theorem map_implicit_function_eq {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] [complete_space 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] [complete_space E] {F : Type u_3}
    [normed_group F] [normed_space 𝕜 F] [finite_dimensional 𝕜 F] {f : E → F}
    {f' : continuous_linear_map 𝕜 E F} {a : E} (hf : has_strict_fderiv_at f f' a)
    (hf' : continuous_linear_map.range f' = ⊤) :
    filter.eventually
        (fun (p : F × ↥(continuous_linear_map.ker f')) =>
          f (implicit_function f f' hf hf' (prod.fst p) (prod.snd p)) = prod.fst p)
        (nhds (f a, 0)) :=
  map_implicit_function_of_complemented_eq hf hf' (implicit_to_local_homeomorph._proof_1 f')

/-- Any point in some neighborhood of `a` can be represented as `implicit_function`
of some point. -/
theorem eq_implicit_function {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] [complete_space 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] [complete_space E] {F : Type u_3}
    [normed_group F] [normed_space 𝕜 F] [finite_dimensional 𝕜 F] {f : E → F}
    {f' : continuous_linear_map 𝕜 E F} {a : E} (hf : has_strict_fderiv_at f f' a)
    (hf' : continuous_linear_map.range f' = ⊤) :
    filter.eventually
        (fun (x : E) =>
          implicit_function f f' hf hf' (f x)
              (prod.snd (coe_fn (implicit_to_local_homeomorph f f' hf hf') x)) =
            x)
        (nhds a) :=
  eq_implicit_function_of_complemented hf hf' (implicit_to_local_homeomorph._proof_1 f')

theorem to_implicit_function {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] [complete_space 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] [complete_space E] {F : Type u_3}
    [normed_group F] [normed_space 𝕜 F] [finite_dimensional 𝕜 F] {f : E → F}
    {f' : continuous_linear_map 𝕜 E F} {a : E} (hf : has_strict_fderiv_at f f' a)
    (hf' : continuous_linear_map.range f' = ⊤) :
    has_strict_fderiv_at (implicit_function f f' hf hf' (f a))
        (continuous_linear_map.subtype_val (continuous_linear_map.ker f')) 0 :=
  to_implicit_function_of_complemented hf hf' (implicit_to_local_homeomorph._proof_1 f')

end Mathlib