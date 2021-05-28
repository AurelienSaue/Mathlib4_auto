/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.big_operators.pi
import Mathlib.algebra.module.pi
import Mathlib.algebra.module.prod
import Mathlib.algebra.module.submodule
import Mathlib.algebra.group.prod
import Mathlib.data.finsupp.basic
import Mathlib.data.dfinsupp
import Mathlib.algebra.pointwise
import PostPort

universes u v w y z x u_1 u_2 u' v' w' u_4 u_5 u_3 u_6 i 

namespace Mathlib

/-!
# Linear algebra

This file defines the basics of linear algebra. It sets up the "categorical/lattice structure" of
modules over a ring, submodules, and linear maps. If `p` and `q` are submodules of a module, `p ≤ q`
means that `p ⊆ q`.

Many of the relevant definitions, including `module`, `submodule`, and `linear_map`, are found in
`src/algebra/module`.

## Main definitions

* Many constructors for linear maps, including `prod` and `coprod`
* `submodule.span s` is defined to be the smallest submodule containing the set `s`.
* If `p` is a submodule of `M`, `submodule.quotient p` is the quotient of `M` with respect to `p`:
  that is, elements of `M` are identified if their difference is in `p`. This is itself a module.
* The kernel `ker` and range `range` of a linear map are submodules of the domain and codomain
  respectively.
* The general linear group is defined to be the group of invertible linear maps from `M` to itself.

## Main statements

* The first and second isomorphism laws for modules are proved as `quot_ker_equiv_range` and
  `quotient_inf_equiv_sup_quotient`.

## Notations

* We continue to use the notation `M →ₗ[R] M₂` for the type of linear maps from `M` to `M₂` over the
  ring `R`.
* We introduce the notations `M ≃ₗ M₂` and `M ≃ₗ[R] M₂` for `linear_equiv M M₂`. In the first, the
  ring `R` is implicit.
* We introduce the notation `R ∙ v` for the span of a singleton, `submodule.span R {v}`.  This is
  `\.`, not the same as the scalar multiplication `•`/`\bub`.

## Implementation notes

We note that, when constructing linear maps, it is convenient to use operations defined on bundled
maps (`prod`, `coprod`, arithmetic operations like `+`) instead of defining a function and proving
it is linear.

## Tags
linear algebra, vector space, module

-/

namespace finsupp


theorem smul_sum {α : Type u} {β : Type v} {R : Type w} {M : Type y} [HasZero β] [semiring R] [add_comm_monoid M] [semimodule R M] {v : α →₀ β} {c : R} {h : α → β → M} : c • sum v h = sum v fun (a : α) (b : β) => c • h a b :=
  finset.smul_sum

end finsupp


/-- decomposing `x : ι → R` as a sum along the canonical basis -/
theorem pi_eq_sum_univ {ι : Type u} [fintype ι] {R : Type v} [semiring R] (x : ι → R) : x = finset.sum finset.univ fun (i : ι) => x i • fun (j : ι) => ite (i = j) 1 0 := sorry

/-! ### Properties of linear maps -/

namespace linear_map


@[simp] theorem comp_id {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M M₂) : comp f id = f :=
  ext fun (x : M) => rfl

@[simp] theorem id_comp {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M M₂) : comp id f = f :=
  ext fun (x : M) => rfl

theorem comp_assoc {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} {M₄ : Type z} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [add_comm_monoid M₄] [semimodule R M] [semimodule R M₂] [semimodule R M₃] [semimodule R M₄] (f : linear_map R M M₂) (g : linear_map R M₂ M₃) (h : linear_map R M₃ M₄) : comp (comp h g) f = comp h (comp g f) :=
  rfl

/-- The restriction of a linear map `f : M → M₂` to a submodule `p ⊆ M` gives a linear map
`p → M₂`. -/
def dom_restrict {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M M₂) (p : submodule R M) : linear_map R (↥p) M₂ :=
  comp f (submodule.subtype p)

@[simp] theorem dom_restrict_apply {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M M₂) (p : submodule R M) (x : ↥p) : coe_fn (dom_restrict f p) x = coe_fn f ↑x :=
  rfl

/-- A linear map `f : M₂ → M` whose values lie in a submodule `p ⊆ M` can be restricted to a
linear map M₂ → p. -/
def cod_restrict {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (p : submodule R M) (f : linear_map R M₂ M) (h : ∀ (c : M₂), coe_fn f c ∈ p) : linear_map R M₂ ↥p :=
  mk (fun (c : M₂) => { val := coe_fn f c, property := h c }) sorry sorry

@[simp] theorem cod_restrict_apply {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (p : submodule R M) (f : linear_map R M₂ M) {h : ∀ (c : M₂), coe_fn f c ∈ p} (x : M₂) : ↑(coe_fn (cod_restrict p f h) x) = coe_fn f x :=
  rfl

@[simp] theorem comp_cod_restrict {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (f : linear_map R M M₂) (p : submodule R M₂) (h : ∀ (b : M), coe_fn f b ∈ p) (g : linear_map R M₃ M) : comp (cod_restrict p f h) g = cod_restrict p (comp f g) fun (b : M₃) => h (coe_fn g b) :=
  ext fun (b : M₃) => rfl

@[simp] theorem subtype_comp_cod_restrict {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M M₂) (p : submodule R M₂) (h : ∀ (b : M), coe_fn f b ∈ p) : comp (submodule.subtype p) (cod_restrict p f h) = f :=
  ext fun (b : M) => rfl

/-- Restrict domain and codomain of an endomorphism. -/
def restrict {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (f : linear_map R M M) {p : submodule R M} (hf : ∀ (x : M), x ∈ p → coe_fn f x ∈ p) : linear_map R ↥p ↥p :=
  cod_restrict p (dom_restrict f p) sorry

theorem restrict_apply {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {f : linear_map R M M} {p : submodule R M} (hf : ∀ (x : M), x ∈ p → coe_fn f x ∈ p) (x : ↥p) : coe_fn (restrict f hf) x = { val := coe_fn f ↑x, property := hf (subtype.val x) (subtype.property x) } :=
  rfl

theorem subtype_comp_restrict {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {f : linear_map R M M} {p : submodule R M} (hf : ∀ (x : M), x ∈ p → coe_fn f x ∈ p) : comp (submodule.subtype p) (restrict f hf) = dom_restrict f p :=
  rfl

theorem restrict_eq_cod_restrict_dom_restrict {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {f : linear_map R M M} {p : submodule R M} (hf : ∀ (x : M), x ∈ p → coe_fn f x ∈ p) : restrict f hf = cod_restrict p (dom_restrict f p) fun (x : ↥p) => hf (subtype.val x) (subtype.property x) :=
  rfl

theorem restrict_eq_dom_restrict_cod_restrict {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {f : linear_map R M M} {p : submodule R M} (hf : ∀ (x : M), coe_fn f x ∈ p) : (restrict f fun (x : M) (_x : x ∈ p) => hf x) = dom_restrict (cod_restrict p f hf) p :=
  rfl

/-- The constant 0 map is linear. -/
protected instance has_zero {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : HasZero (linear_map R M M₂) :=
  { zero := mk (fun (_x : M) => 0) sorry sorry }

protected instance inhabited {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : Inhabited (linear_map R M M₂) :=
  { default := 0 }

@[simp] theorem zero_apply {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (x : M) : coe_fn 0 x = 0 :=
  rfl

@[simp] theorem default_def {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : Inhabited.default = 0 :=
  rfl

protected instance unique_of_left {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] [subsingleton M] : unique (linear_map R M M₂) :=
  unique.mk { default := Inhabited.default } sorry

protected instance unique_of_right {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] [subsingleton M₂] : unique (linear_map R M M₂) :=
  function.injective.unique coe_injective

/-- The sum of two linear maps is linear. -/
protected instance has_add {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : Add (linear_map R M M₂) :=
  { add := fun (f g : linear_map R M M₂) => mk (fun (b : M) => coe_fn f b + coe_fn g b) sorry sorry }

@[simp] theorem add_apply {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M M₂) (g : linear_map R M M₂) (x : M) : coe_fn (f + g) x = coe_fn f x + coe_fn g x :=
  rfl

/-- The type of linear maps is an additive monoid. -/
protected instance add_comm_monoid {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : add_comm_monoid (linear_map R M M₂) :=
  add_comm_monoid.mk Add.add sorry 0 sorry sorry sorry

protected instance linear_map_apply_is_add_monoid_hom {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (a : M) : is_add_monoid_hom fun (f : linear_map R M M₂) => coe_fn f a :=
  is_add_monoid_hom.mk rfl

theorem add_comp {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (f : linear_map R M M₂) (g : linear_map R M₂ M₃) (h : linear_map R M₂ M₃) : comp (h + g) f = comp h f + comp g f :=
  rfl

theorem comp_add {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (f : linear_map R M M₂) (g : linear_map R M M₂) (h : linear_map R M₂ M₃) : comp h (f + g) = comp h f + comp h g := sorry

theorem sum_apply {R : Type u} {M : Type v} {M₂ : Type w} {ι : Type x} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (t : finset ι) (f : ι → linear_map R M M₂) (b : M) : coe_fn (finset.sum t fun (d : ι) => f d) b = finset.sum t fun (d : ι) => coe_fn (f d) b :=
  Eq.symm (finset.sum_hom t fun (g : linear_map R M M₂) => coe_fn g b)

/-- `λb, f b • x` is a linear map. -/
def smul_right {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M₂ R) (x : M) : linear_map R M₂ M :=
  mk (fun (b : M₂) => coe_fn f b • x) sorry sorry

@[simp] theorem smul_right_apply {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M₂ R) (x : M) (c : M₂) : coe_fn (smul_right f x) c = coe_fn f c • x :=
  rfl

protected instance has_one {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] : HasOne (linear_map R M M) :=
  { one := id }

protected instance has_mul {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] : Mul (linear_map R M M) :=
  { mul := comp }

theorem mul_eq_comp {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (f : linear_map R M M) (g : linear_map R M M) : f * g = comp f g :=
  rfl

@[simp] theorem one_app {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (x : M) : coe_fn 1 x = x :=
  rfl

@[simp] theorem mul_app {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (A : linear_map R M M) (B : linear_map R M M) (x : M) : coe_fn (A * B) x = coe_fn A (coe_fn B x) :=
  rfl

@[simp] theorem comp_zero {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (f : linear_map R M M₂) : comp f 0 = 0 := sorry

@[simp] theorem zero_comp {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (f : linear_map R M M₂) : comp 0 f = 0 :=
  rfl

theorem coe_fn_sum {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {ι : Type u_1} (t : finset ι) (f : ι → linear_map R M M₂) : ⇑(finset.sum t fun (i : ι) => f i) = finset.sum t fun (i : ι) => ⇑(f i) :=
  add_monoid_hom.map_sum (add_monoid_hom.mk to_fun rfl fun (x y : linear_map R M M₂) => rfl) (fun (x : ι) => f x) t

protected instance monoid {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] : monoid (linear_map R M M) :=
  monoid.mk Mul.mul sorry 1 sorry sorry

/-- A linear map `f` applied to `x : ι → R` can be computed using the image under `f` of elements
of the canonical basis. -/
theorem pi_apply_eq_sum_univ {R : Type u} {M : Type v} {ι : Type x} [semiring R] [add_comm_monoid M] [semimodule R M] [fintype ι] (f : linear_map R (ι → R) M) (x : ι → R) : coe_fn f x = finset.sum finset.univ fun (i : ι) => x i • coe_fn f fun (j : ι) => ite (i = j) 1 0 := sorry

/-- The first projection of a product is a linear map. -/
def fst (R : Type u) (M : Type v) (M₂ : Type w) [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : linear_map R (M × M₂) M :=
  mk prod.fst sorry sorry

/-- The second projection of a product is a linear map. -/
def snd (R : Type u) (M : Type v) (M₂ : Type w) [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : linear_map R (M × M₂) M₂ :=
  mk prod.snd sorry sorry

@[simp] theorem fst_apply {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (x : M × M₂) : coe_fn (fst R M M₂) x = prod.fst x :=
  rfl

@[simp] theorem snd_apply {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (x : M × M₂) : coe_fn (snd R M M₂) x = prod.snd x :=
  rfl

/-- The prod of two linear maps is a linear map. -/
def prod {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (f : linear_map R M M₂) (g : linear_map R M M₃) : linear_map R M (M₂ × M₃) :=
  mk (fun (x : M) => (coe_fn f x, coe_fn g x)) sorry sorry

@[simp] theorem prod_apply {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (f : linear_map R M M₂) (g : linear_map R M M₃) (x : M) : coe_fn (prod f g) x = (coe_fn f x, coe_fn g x) :=
  rfl

@[simp] theorem fst_prod {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (f : linear_map R M M₂) (g : linear_map R M M₃) : comp (fst R M₂ M₃) (prod f g) = f :=
  ext fun (x : M) => Eq.refl (coe_fn (comp (fst R M₂ M₃) (prod f g)) x)

@[simp] theorem snd_prod {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (f : linear_map R M M₂) (g : linear_map R M M₃) : comp (snd R M₂ M₃) (prod f g) = g :=
  ext fun (x : M) => Eq.refl (coe_fn (comp (snd R M₂ M₃) (prod f g)) x)

@[simp] theorem pair_fst_snd {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : prod (fst R M M₂) (snd R M M₂) = id := sorry

/-- The left injection into a product is a linear map. -/
def inl (R : Type u) (M : Type v) (M₂ : Type w) [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : linear_map R M (M × M₂) :=
  mk ⇑(add_monoid_hom.inl M M₂) sorry sorry

/-- The right injection into a product is a linear map. -/
def inr (R : Type u) (M : Type v) (M₂ : Type w) [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : linear_map R M₂ (M × M₂) :=
  mk ⇑(add_monoid_hom.inr M M₂) sorry sorry

@[simp] theorem inl_apply {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (x : M) : coe_fn (inl R M M₂) x = (x, 0) :=
  rfl

@[simp] theorem inr_apply {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (x : M₂) : coe_fn (inr R M M₂) x = (0, x) :=
  rfl

theorem inl_injective {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : function.injective ⇑(inl R M M₂) := sorry

theorem inr_injective {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : function.injective ⇑(inr R M M₂) := sorry

/-- The coprod function `λ x : M × M₂, f x.1 + g x.2` is a linear map. -/
def coprod {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (f : linear_map R M M₃) (g : linear_map R M₂ M₃) : linear_map R (M × M₂) M₃ :=
  mk (fun (x : M × M₂) => coe_fn f (prod.fst x) + coe_fn g (prod.snd x)) sorry sorry

@[simp] theorem coprod_apply {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (f : linear_map R M M₃) (g : linear_map R M₂ M₃) (x : M) (y : M₂) : coe_fn (coprod f g) (x, y) = coe_fn f x + coe_fn g y :=
  rfl

@[simp] theorem coprod_inl {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (f : linear_map R M M₃) (g : linear_map R M₂ M₃) : comp (coprod f g) (inl R M M₂) = f := sorry

@[simp] theorem coprod_inr {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (f : linear_map R M M₃) (g : linear_map R M₂ M₃) : comp (coprod f g) (inr R M M₂) = g := sorry

@[simp] theorem coprod_inl_inr {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : coprod (inl R M M₂) (inr R M M₂) = id := sorry

theorem fst_eq_coprod {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : fst R M M₂ = coprod id 0 := sorry

theorem snd_eq_coprod {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : snd R M M₂ = coprod 0 id := sorry

theorem inl_eq_prod {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : inl R M M₂ = prod id 0 :=
  rfl

theorem inr_eq_prod {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : inr R M M₂ = prod 0 id :=
  rfl

/-- `prod.map` of two linear maps. -/
def prod_map {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} {M₄ : Type z} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [add_comm_monoid M₄] [semimodule R M] [semimodule R M₂] [semimodule R M₃] [semimodule R M₄] (f : linear_map R M M₃) (g : linear_map R M₂ M₄) : linear_map R (M × M₂) (M₃ × M₄) :=
  prod (comp f (fst R M M₂)) (comp g (snd R M M₂))

@[simp] theorem prod_map_apply {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} {M₄ : Type z} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [add_comm_monoid M₄] [semimodule R M] [semimodule R M₂] [semimodule R M₃] [semimodule R M₄] (f : linear_map R M M₃) (g : linear_map R M₂ M₄) (x : M × M₂) : coe_fn (prod_map f g) x = (coe_fn f (prod.fst x), coe_fn g (prod.snd x)) :=
  rfl

/-- The negation of a linear map is linear. -/
protected instance has_neg {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] : Neg (linear_map R M M₂) :=
  { neg := fun (f : linear_map R M M₂) => mk (fun (b : M) => -coe_fn f b) sorry sorry }

@[simp] theorem neg_apply {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M M₂) (x : M) : coe_fn (-f) x = -coe_fn f x :=
  rfl

@[simp] theorem comp_neg {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} [semiring R] [add_comm_monoid M] [add_comm_group M₂] [add_comm_group M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (f : linear_map R M M₂) (g : linear_map R M₂ M₃) : comp g (-f) = -comp g f := sorry

/-- The negation of a linear map is linear. -/
protected instance has_sub {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] : Sub (linear_map R M M₂) :=
  { sub := fun (f g : linear_map R M M₂) => mk (fun (b : M) => coe_fn f b - coe_fn g b) sorry sorry }

@[simp] theorem sub_apply {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M M₂) (g : linear_map R M M₂) (x : M) : coe_fn (f - g) x = coe_fn f x - coe_fn g x :=
  rfl

theorem sub_comp {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} [semiring R] [add_comm_monoid M] [add_comm_group M₂] [add_comm_group M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (f : linear_map R M M₂) (g : linear_map R M₂ M₃) (h : linear_map R M₂ M₃) : comp (g - h) f = comp g f - comp h f :=
  rfl

theorem comp_sub {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} [semiring R] [add_comm_monoid M] [add_comm_group M₂] [add_comm_group M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (f : linear_map R M M₂) (g : linear_map R M M₂) (h : linear_map R M₂ M₃) : comp h (g - f) = comp h g - comp h f := sorry

/-- The type of linear maps is an additive group. -/
protected instance add_comm_group {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] : add_comm_group (linear_map R M M₂) :=
  add_comm_group.mk Add.add sorry 0 sorry sorry Neg.neg Sub.sub sorry sorry

protected instance linear_map_apply_is_add_group_hom {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] (a : M) : is_add_group_hom fun (f : linear_map R M M₂) => coe_fn f a :=
  is_add_group_hom.mk

protected instance has_scalar {R : Type u} {M : Type v} {M₂ : Type w} {S : Type u_1} [semiring R] [monoid S] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] [distrib_mul_action S M₂] [smul_comm_class R S M₂] : has_scalar S (linear_map R M M₂) :=
  has_scalar.mk fun (a : S) (f : linear_map R M M₂) => mk (fun (b : M) => a • coe_fn f b) sorry sorry

@[simp] theorem smul_apply {R : Type u} {M : Type v} {M₂ : Type w} {S : Type u_1} [semiring R] [monoid S] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] [distrib_mul_action S M₂] [smul_comm_class R S M₂] (f : linear_map R M M₂) (a : S) (x : M) : coe_fn (a • f) x = a • coe_fn f x :=
  rfl

protected instance distrib_mul_action {R : Type u} {M : Type v} {M₂ : Type w} {S : Type u_1} [semiring R] [monoid S] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] [distrib_mul_action S M₂] [smul_comm_class R S M₂] : distrib_mul_action S (linear_map R M M₂) :=
  distrib_mul_action.mk sorry sorry

theorem smul_comp {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} {S : Type u_1} [semiring R] [monoid S] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] [distrib_mul_action S M₂] [smul_comm_class R S M₂] (a : S) (g : linear_map R M₃ M₂) (f : linear_map R M M₃) : comp (a • g) f = a • comp g f :=
  rfl

protected instance semimodule {R : Type u} {M : Type v} {M₂ : Type w} {S : Type u_1} [semiring R] [semiring S] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] [semimodule S M₂] [smul_comm_class R S M₂] : semimodule S (linear_map R M M₂) :=
  semimodule.mk sorry sorry

/-- Applying a linear map at `v : M`, seen as `S`-linear map from `M →ₗ[R] M₂` to `M₂`.

 See `applyₗ` for a version where `S = R` -/
def applyₗ' {R : Type u} {M : Type v} {M₂ : Type w} (S : Type u_1) [semiring R] [semiring S] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] [semimodule S M₂] [smul_comm_class R S M₂] (v : M) : linear_map S (linear_map R M M₂) M₂ :=
  mk (fun (f : linear_map R M M₂) => coe_fn f v) sorry sorry

theorem comp_smul {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} [comm_semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (f : linear_map R M M₂) (g : linear_map R M₂ M₃) (a : R) : comp g (a • f) = a • comp g f := sorry

/-- Composition by `f : M₂ → M₃` is a linear map from the space of linear maps `M → M₂`
to the space of linear maps `M₂ → M₃`. -/
def comp_right {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} [comm_semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (f : linear_map R M₂ M₃) : linear_map R (linear_map R M M₂) (linear_map R M M₃) :=
  mk (comp f) sorry sorry

/-- Applying a linear map at `v : M`, seen as a linear map from `M →ₗ[R] M₂` to `M₂`.
See also `linear_map.applyₗ'` for a version that works with two different semirings. -/
def applyₗ {R : Type u} {M : Type v} {M₂ : Type w} [comm_semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (v : M) : linear_map R (linear_map R M M₂) M₂ :=
  applyₗ' R v

protected instance endomorphism_semiring {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] : semiring (linear_map R M M) :=
  semiring.mk add_comm_monoid.add sorry add_comm_monoid.zero sorry sorry sorry Mul.mul sorry 1 sorry sorry sorry sorry
    sorry sorry

theorem mul_apply {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (f : linear_map R M M) (g : linear_map R M M) (x : M) : coe_fn (f * g) x = coe_fn f (coe_fn g x) :=
  rfl

protected instance endomorphism_ring {R : Type u} {M : Type v} [ring R] [add_comm_group M] [semimodule R M] : ring (linear_map R M M) :=
  ring.mk semiring.add sorry semiring.zero sorry sorry add_comm_group.neg add_comm_group.sub sorry sorry semiring.mul
    sorry semiring.one sorry sorry sorry sorry

/--
The family of linear maps `M₂ → M` parameterised by `f ∈ M₂ → R`, `x ∈ M`, is linear in `f`, `x`.
-/
def smul_rightₗ {R : Type u} {M : Type v} {M₂ : Type w} [comm_ring R] [add_comm_group M] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] : linear_map R (linear_map R M₂ R) (linear_map R M (linear_map R M₂ M)) :=
  mk (fun (f : linear_map R M₂ R) => mk (smul_right f) sorry sorry) sorry sorry

@[simp] theorem smul_rightₗ_apply {R : Type u} {M : Type v} {M₂ : Type w} [comm_ring R] [add_comm_group M] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M₂ R) (x : M) (c : M₂) : coe_fn (coe_fn (coe_fn smul_rightₗ f) x) c = coe_fn f c • x :=
  rfl

end linear_map


/-! ### Properties of submodules -/

namespace submodule


protected instance partial_order {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] : partial_order (submodule R M) :=
  partial_order.mk (fun (p p' : submodule R M) => ∀ {x : M}, x ∈ p → x ∈ p') partial_order.lt sorry sorry sorry

theorem le_def {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {p : submodule R M} {p' : submodule R M} : p ≤ p' ↔ ↑p ⊆ ↑p' :=
  iff.rfl

theorem le_def' {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {p : submodule R M} {p' : submodule R M} : p ≤ p' ↔ ∀ (x : M), x ∈ p → x ∈ p' :=
  iff.rfl

theorem lt_def {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {p : submodule R M} {p' : submodule R M} : p < p' ↔ ↑p ⊂ ↑p' :=
  iff.rfl

theorem not_le_iff_exists {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {p : submodule R M} {p' : submodule R M} : ¬p ≤ p' ↔ ∃ (x : M), ∃ (H : x ∈ p), ¬x ∈ p' :=
  set.not_subset

theorem exists_of_lt {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {p : submodule R M} {p' : submodule R M} : p < p' → ∃ (x : M), ∃ (H : x ∈ p'), ¬x ∈ p :=
  set.exists_of_ssubset

theorem lt_iff_le_and_exists {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {p : submodule R M} {p' : submodule R M} : p < p' ↔ p ≤ p' ∧ ∃ (x : M), ∃ (H : x ∈ p'), ¬x ∈ p := sorry

/-- If two submodules `p` and `p'` satisfy `p ⊆ p'`, then `of_le p p'` is the linear map version of
this inclusion. -/
def of_le {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {p : submodule R M} {p' : submodule R M} (h : p ≤ p') : linear_map R ↥p ↥p' :=
  linear_map.cod_restrict p' (submodule.subtype p) sorry

@[simp] theorem coe_of_le {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {p : submodule R M} {p' : submodule R M} (h : p ≤ p') (x : ↥p) : ↑(coe_fn (of_le h) x) = ↑x :=
  rfl

theorem of_le_apply {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {p : submodule R M} {p' : submodule R M} (h : p ≤ p') (x : ↥p) : coe_fn (of_le h) x = { val := ↑x, property := h (subtype.property x) } :=
  rfl

theorem subtype_comp_of_le {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (p : submodule R M) (q : submodule R M) (h : p ≤ q) : linear_map.comp (submodule.subtype q) (of_le h) = submodule.subtype p := sorry

/-- The set `{0}` is the bottom element of the lattice of submodules. -/
protected instance has_bot {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] : has_bot (submodule R M) :=
  has_bot.mk (mk (singleton 0) sorry sorry sorry)

protected instance inhabited' {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] : Inhabited (submodule R M) :=
  { default := ⊥ }

@[simp] theorem bot_coe {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] : ↑⊥ = singleton 0 :=
  rfl

@[simp] theorem mem_bot (R : Type u) {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {x : M} : x ∈ ⊥ ↔ x = 0 :=
  set.mem_singleton_iff

theorem nonzero_mem_of_bot_lt {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {I : submodule R M} (bot_lt : ⊥ < I) : ∃ (a : ↥I), a ≠ 0 := sorry

protected instance order_bot {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] : order_bot (submodule R M) :=
  order_bot.mk ⊥ partial_order.le partial_order.lt sorry sorry sorry sorry

protected theorem eq_bot_iff {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (p : submodule R M) : p = ⊥ ↔ ∀ (x : M), x ∈ p → x = 0 :=
  { mp := fun (h : p = ⊥) => Eq.symm h ▸ fun (x : M) (hx : x ∈ ⊥) => iff.mp (mem_bot R) hx,
    mpr :=
      fun (h : ∀ (x : M), x ∈ p → x = 0) => iff.mpr eq_bot_iff fun (x : M) (hx : x ∈ p) => iff.mpr (mem_bot R) (h x hx) }

protected theorem ne_bot_iff {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (p : submodule R M) : p ≠ ⊥ ↔ ∃ (x : M), ∃ (H : x ∈ p), x ≠ 0 := sorry

/-- The universal set is the top element of the lattice of submodules. -/
protected instance has_top {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] : has_top (submodule R M) :=
  has_top.mk (mk set.univ sorry sorry sorry)

@[simp] theorem top_coe {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] : ↑⊤ = set.univ :=
  rfl

@[simp] theorem mem_top {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {x : M} : x ∈ ⊤ :=
  trivial

theorem eq_bot_of_zero_eq_one {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (p : submodule R M) (zero_eq_one : 0 = 1) : p = ⊥ := sorry

protected instance order_top {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] : order_top (submodule R M) :=
  order_top.mk ⊤ partial_order.le partial_order.lt sorry sorry sorry sorry

protected instance has_Inf {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] : has_Inf (submodule R M) :=
  has_Inf.mk
    fun (S : set (submodule R M)) =>
      mk (set.Inter fun (s : submodule R M) => set.Inter fun (H : s ∈ S) => ↑s) sorry sorry sorry

protected instance has_inf {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] : has_inf (submodule R M) :=
  has_inf.mk fun (p p' : submodule R M) => mk (↑p ∩ ↑p') sorry sorry sorry

protected instance complete_lattice {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] : complete_lattice (submodule R M) :=
  complete_lattice.mk (fun (a b : submodule R M) => Inf (set_of fun (x : submodule R M) => a ≤ x ∧ b ≤ x)) order_top.le
    order_top.lt sorry sorry sorry sorry sorry sorry has_inf.inf sorry sorry sorry order_top.top sorry order_bot.bot sorry
    (fun (tt : set (submodule R M)) => Inf (set_of fun (t : submodule R M) => ∀ (t' : submodule R M), t' ∈ tt → t' ≤ t))
    Inf sorry sorry sorry sorry

protected instance add_comm_monoid_submodule {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] : add_comm_monoid (submodule R M) :=
  add_comm_monoid.mk has_sup.sup sorry ⊥ sorry sorry sorry

@[simp] theorem add_eq_sup {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (p : submodule R M) (q : submodule R M) : p + q = p ⊔ q :=
  rfl

@[simp] theorem zero_eq_bot {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] : 0 = ⊥ :=
  rfl

theorem eq_top_iff' {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {p : submodule R M} : p = ⊤ ↔ ∀ (x : M), x ∈ p :=
  iff.trans eq_top_iff
    { mp := fun (h : ⊤ ≤ p) (x : M) => h trivial, mpr := fun (h : ∀ (x : M), x ∈ p) (x : M) (_x : x ∈ ⊤) => h x }

theorem bot_ne_top {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] [nontrivial M] : ⊥ ≠ ⊤ := sorry

@[simp] theorem inf_coe {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (p : submodule R M) (p' : submodule R M) : ↑p ⊓ ↑p' = ↑p ∩ ↑p' :=
  rfl

@[simp] theorem mem_inf {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {x : M} {p : submodule R M} {p' : submodule R M} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' :=
  iff.rfl

@[simp] theorem Inf_coe {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (P : set (submodule R M)) : ↑(Inf P) = set.Inter fun (p : submodule R M) => set.Inter fun (H : p ∈ P) => ↑p :=
  rfl

@[simp] theorem infi_coe {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {ι : Sort u_1} (p : ι → submodule R M) : ↑(infi fun (i : ι) => p i) = set.Inter fun (i : ι) => ↑(p i) := sorry

@[simp] theorem mem_Inf {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {S : set (submodule R M)} {x : M} : x ∈ Inf S ↔ ∀ (p : submodule R M), p ∈ S → x ∈ p :=
  set.mem_bInter_iff

@[simp] theorem mem_infi {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {x : M} {ι : Sort u_1} (p : ι → submodule R M) : (x ∈ infi fun (i : ι) => p i) ↔ ∀ (i : ι), x ∈ p i := sorry

theorem disjoint_def {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {p : submodule R M} {p' : submodule R M} : disjoint p p' ↔ ∀ (x : M), x ∈ p → x ∈ p' → x = 0 := sorry

theorem disjoint_def' {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {p : submodule R M} {p' : submodule R M} : disjoint p p' ↔ ∀ (x : M), x ∈ p → ∀ (y : M), y ∈ p' → x = y → x = 0 := sorry

theorem mem_right_iff_eq_zero_of_disjoint {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {p : submodule R M} {p' : submodule R M} (h : disjoint p p') {x : ↥p} : ↑x ∈ p' ↔ x = 0 :=
  { mp := fun (hx : ↑x ∈ p') => iff.mp coe_eq_zero (iff.mp disjoint_def h (↑x) (subtype.property x) hx),
    mpr := fun (h : x = 0) => Eq.symm h ▸ zero_mem p' }

theorem mem_left_iff_eq_zero_of_disjoint {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {p : submodule R M} {p' : submodule R M} (h : disjoint p p') {x : ↥p'} : ↑x ∈ p ↔ x = 0 :=
  { mp := fun (hx : ↑x ∈ p) => iff.mp coe_eq_zero (iff.mp disjoint_def h (↑x) hx (subtype.property x)),
    mpr := fun (h : x = 0) => Eq.symm h ▸ zero_mem p }

/-- The pushforward of a submodule `p ⊆ M` by `f : M → M₂` -/
def map {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M M₂) (p : submodule R M) : submodule R M₂ :=
  mk (⇑f '' ↑p) sorry sorry sorry

@[simp] theorem map_coe {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M M₂) (p : submodule R M) : ↑(map f p) = ⇑f '' ↑p :=
  rfl

@[simp] theorem mem_map {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {f : linear_map R M M₂} {p : submodule R M} {x : M₂} : x ∈ map f p ↔ ∃ (y : M), y ∈ p ∧ coe_fn f y = x :=
  iff.rfl

theorem mem_map_of_mem {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {f : linear_map R M M₂} {p : submodule R M} {r : M} (h : r ∈ p) : coe_fn f r ∈ map f p :=
  set.mem_image_of_mem (fun (a : M) => coe_fn f a) h

@[simp] theorem map_id {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (p : submodule R M) : map linear_map.id p = p := sorry

theorem map_comp {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (f : linear_map R M M₂) (g : linear_map R M₂ M₃) (p : submodule R M) : map (linear_map.comp g f) p = map g (map f p) := sorry

theorem map_mono {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {f : linear_map R M M₂} {p : submodule R M} {p' : submodule R M} : p ≤ p' → map f p ≤ map f p' :=
  set.image_subset fun (a : M) => coe_fn f a

@[simp] theorem map_zero {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (p : submodule R M) : map 0 p = ⊥ := sorry

/-- The pullback of a submodule `p ⊆ M₂` along `f : M → M₂` -/
def comap {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M M₂) (p : submodule R M₂) : submodule R M :=
  mk (⇑f ⁻¹' ↑p) sorry sorry sorry

@[simp] theorem comap_coe {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M M₂) (p : submodule R M₂) : ↑(comap f p) = ⇑f ⁻¹' ↑p :=
  rfl

@[simp] theorem mem_comap {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {x : M} {f : linear_map R M M₂} {p : submodule R M₂} : x ∈ comap f p ↔ coe_fn f x ∈ p :=
  iff.rfl

theorem comap_id {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (p : submodule R M) : comap linear_map.id p = p :=
  coe_injective rfl

theorem comap_comp {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (f : linear_map R M M₂) (g : linear_map R M₂ M₃) (p : submodule R M₃) : comap (linear_map.comp g f) p = comap f (comap g p) :=
  rfl

theorem comap_mono {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {f : linear_map R M M₂} {q : submodule R M₂} {q' : submodule R M₂} : q ≤ q' → comap f q ≤ comap f q' :=
  set.preimage_mono

theorem map_le_iff_le_comap {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {f : linear_map R M M₂} {p : submodule R M} {q : submodule R M₂} : map f p ≤ q ↔ p ≤ comap f q :=
  set.image_subset_iff

theorem gc_map_comap {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M M₂) : galois_connection (map f) (comap f) :=
  fun (a : submodule R M) (b : submodule R M₂) => idRhs (map f a ≤ b ↔ a ≤ comap f b) map_le_iff_le_comap

@[simp] theorem map_bot {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M M₂) : map f ⊥ = ⊥ :=
  galois_connection.l_bot (gc_map_comap f)

@[simp] theorem map_sup {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (p : submodule R M) (p' : submodule R M) (f : linear_map R M M₂) : map f (p ⊔ p') = map f p ⊔ map f p' :=
  galois_connection.l_sup (gc_map_comap f)

@[simp] theorem map_supr {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {ι : Sort u_1} (f : linear_map R M M₂) (p : ι → submodule R M) : map f (supr fun (i : ι) => p i) = supr fun (i : ι) => map f (p i) :=
  galois_connection.l_supr (gc_map_comap f)

@[simp] theorem comap_top {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M M₂) : comap f ⊤ = ⊤ :=
  rfl

@[simp] theorem comap_inf {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (q : submodule R M₂) (q' : submodule R M₂) (f : linear_map R M M₂) : comap f (q ⊓ q') = comap f q ⊓ comap f q' :=
  rfl

@[simp] theorem comap_infi {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {ι : Sort u_1} (f : linear_map R M M₂) (p : ι → submodule R M₂) : comap f (infi fun (i : ι) => p i) = infi fun (i : ι) => comap f (p i) :=
  galois_connection.u_infi (gc_map_comap f)

@[simp] theorem comap_zero {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (q : submodule R M₂) : comap 0 q = ⊤ := sorry

theorem map_comap_le {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M M₂) (q : submodule R M₂) : map f (comap f q) ≤ q :=
  galois_connection.l_u_le (gc_map_comap f) q

theorem le_comap_map {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M M₂) (p : submodule R M) : p ≤ comap f (map f p) :=
  galois_connection.le_u_l (gc_map_comap f) p

--TODO(Mario): is there a way to prove this from order properties?

theorem map_inf_eq_map_inf_comap {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {f : linear_map R M M₂} {p : submodule R M} {p' : submodule R M₂} : map f p ⊓ p' = map f (p ⊓ comap f p') := sorry

theorem map_comap_subtype {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (p : submodule R M) (p' : submodule R M) : map (submodule.subtype p) (comap (submodule.subtype p) p') = p ⊓ p' := sorry

theorem eq_zero_of_bot_submodule {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (b : ↥⊥) : b = 0 := sorry

/-- The span of a set `s ⊆ M` is the smallest submodule of M that contains `s`. -/
def span (R : Type u) {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (s : set M) : submodule R M :=
  Inf (set_of fun (p : submodule R M) => s ⊆ ↑p)

theorem mem_span {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {x : M} {s : set M} : x ∈ span R s ↔ ∀ (p : submodule R M), s ⊆ ↑p → x ∈ p :=
  set.mem_bInter_iff

theorem subset_span {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {s : set M} : s ⊆ ↑(span R s) :=
  fun (x : M) (h : x ∈ s) => iff.mpr mem_span fun (p : submodule R M) (hp : s ⊆ ↑p) => hp h

theorem span_le {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {s : set M} {p : submodule R M} : span R s ≤ p ↔ s ⊆ ↑p :=
  { mp := set.subset.trans subset_span, mpr := fun (ss : s ⊆ ↑p) (x : M) (h : x ∈ span R s) => iff.mp mem_span h p ss }

theorem span_mono {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {s : set M} {t : set M} (h : s ⊆ t) : span R s ≤ span R t :=
  iff.mpr span_le (set.subset.trans h subset_span)

theorem span_eq_of_le {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (p : submodule R M) {s : set M} (h₁ : s ⊆ ↑p) (h₂ : p ≤ span R s) : span R s = p :=
  le_antisymm (iff.mpr span_le h₁) h₂

@[simp] theorem span_eq {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (p : submodule R M) : span R ↑p = p :=
  span_eq_of_le p (set.subset.refl ↑p) subset_span

theorem map_span {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M M₂) (s : set M) : map f (span R s) = span R (⇑f '' s) := sorry

/- See also `span_preimage_eq` below. -/

theorem span_preimage_le {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M M₂) (s : set M₂) : span R (⇑f ⁻¹' s) ≤ comap f (span R s) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (span R (⇑f ⁻¹' s) ≤ comap f (span R s))) (propext span_le)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (⇑f ⁻¹' s ⊆ ↑(comap f (span R s)))) (comap_coe f (span R s))))
      (set.preimage_mono subset_span))

/-- An induction principle for span membership. If `p` holds for 0 and all elements of `s`, and is
preserved under addition and scalar multiplication, then `p` holds for all elements of the span of
`s`. -/
theorem span_induction {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {x : M} {s : set M} {p : M → Prop} (h : x ∈ span R s) (Hs : ∀ (x : M), x ∈ s → p x) (H0 : p 0) (H1 : ∀ (x y : M), p x → p y → p (x + y)) (H2 : ∀ (a : R) (x : M), p x → p (a • x)) : p x :=
  iff.mpr span_le Hs x h

/-- `span` forms a Galois insertion with the coercion from submodule to set. -/
protected def gi (R : Type u) (M : Type v) [semiring R] [add_comm_monoid M] [semimodule R M] : galois_insertion (span R) coe :=
  galois_insertion.mk (fun (s : set M) (_x : ↑(span R s) ≤ s) => span R s) sorry sorry sorry

@[simp] theorem span_empty {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] : span R ∅ = ⊥ :=
  galois_connection.l_bot (galois_insertion.gc (submodule.gi R M))

@[simp] theorem span_univ {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] : span R set.univ = ⊤ :=
  iff.mpr eq_top_iff (iff.mpr le_def subset_span)

theorem span_union {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (s : set M) (t : set M) : span R (s ∪ t) = span R s ⊔ span R t :=
  galois_connection.l_sup (galois_insertion.gc (submodule.gi R M))

theorem span_Union {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {ι : Sort u_1} (s : ι → set M) : span R (set.Union fun (i : ι) => s i) = supr fun (i : ι) => span R (s i) :=
  galois_connection.l_supr (galois_insertion.gc (submodule.gi R M))

theorem span_eq_supr_of_singleton_spans {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (s : set M) : span R s = supr fun (x : M) => supr fun (H : x ∈ s) => span R (singleton x) := sorry

@[simp] theorem coe_supr_of_directed {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {ι : Sort u_1} [hι : Nonempty ι] (S : ι → submodule R M) (H : directed LessEq S) : ↑(supr S) = set.Union fun (i : ι) => ↑(S i) := sorry

theorem mem_sup_left {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {S : submodule R M} {T : submodule R M} {x : M} : x ∈ S → x ∈ S ⊔ T :=
  (fun (this : S ≤ S ⊔ T) => this) le_sup_left

theorem mem_sup_right {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {S : submodule R M} {T : submodule R M} {x : M} : x ∈ T → x ∈ S ⊔ T :=
  (fun (this : T ≤ S ⊔ T) => this) le_sup_right

theorem mem_supr_of_mem {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {ι : Sort u_1} {b : M} {p : ι → submodule R M} (i : ι) (h : b ∈ p i) : b ∈ supr fun (i : ι) => p i :=
  (fun (this : p i ≤ supr fun (i : ι) => p i) => this h) (le_supr p i)

theorem mem_Sup_of_mem {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {S : set (submodule R M)} {s : submodule R M} (hs : s ∈ S) {x : M} : x ∈ s → x ∈ Sup S :=
  (fun (this : s ≤ Sup S) => this) (le_Sup hs)

@[simp] theorem mem_supr_of_directed {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {ι : Sort u_1} [Nonempty ι] (S : ι → submodule R M) (H : directed LessEq S) {x : M} : x ∈ supr S ↔ ∃ (i : ι), x ∈ S i := sorry

theorem mem_Sup_of_directed {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {s : set (submodule R M)} {z : M} (hs : set.nonempty s) (hdir : directed_on LessEq s) : z ∈ Sup s ↔ ∃ (y : submodule R M), ∃ (H : y ∈ s), z ∈ y := sorry

theorem mem_sup {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {p : submodule R M} {p' : submodule R M} {x : M} : x ∈ p ⊔ p' ↔ ∃ (y : M), ∃ (H : y ∈ p), ∃ (z : M), ∃ (H : z ∈ p'), y + z = x := sorry

theorem mem_sup' {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {p : submodule R M} {p' : submodule R M} {x : M} : x ∈ p ⊔ p' ↔ ∃ (y : ↥p), ∃ (z : ↥p'), ↑y + ↑z = x := sorry

theorem mem_span_singleton_self {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (x : M) : x ∈ span R (singleton x) :=
  subset_span rfl

theorem nontrivial_span_singleton {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {x : M} (h : x ≠ 0) : nontrivial ↥(span R (singleton x)) := sorry

theorem mem_span_singleton {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {x : M} {y : M} : x ∈ span R (singleton y) ↔ ∃ (a : R), a • y = x := sorry

theorem le_span_singleton_iff {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {s : submodule R M} {v₀ : M} : s ≤ span R (singleton v₀) ↔ ∀ (v : M), v ∈ s → ∃ (r : R), r • v₀ = v := sorry

@[simp] theorem span_zero_singleton {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] : span R (singleton 0) = ⊥ := sorry

theorem span_singleton_eq_range {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (y : M) : ↑(span R (singleton y)) = set.range fun (_x : R) => _x • y :=
  set.ext fun (x : M) => mem_span_singleton

theorem span_singleton_smul_le {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (r : R) (x : M) : span R (singleton (r • x)) ≤ span R (singleton x) := sorry

theorem span_singleton_smul_eq {K : Type u_1} {E : Type u_2} [division_ring K] [add_comm_group E] [module K E] {r : K} (x : E) (hr : r ≠ 0) : span K (singleton (r • x)) = span K (singleton x) := sorry

theorem disjoint_span_singleton {K : Type u_1} {E : Type u_2} [division_ring K] [add_comm_group E] [module K E] {s : submodule K E} {x : E} : disjoint s (span K (singleton x)) ↔ x ∈ s → x = 0 := sorry

theorem disjoint_span_singleton' {K : Type u_1} {E : Type u_2} [division_ring K] [add_comm_group E] [module K E] {p : submodule K E} {x : E} (x0 : x ≠ 0) : disjoint p (span K (singleton x)) ↔ ¬x ∈ p :=
  iff.trans disjoint_span_singleton
    { mp := fun (h₁ : x ∈ p → x = 0) (h₂ : x ∈ p) => x0 (h₁ h₂),
      mpr := fun (h₁ : ¬x ∈ p) (h₂ : x ∈ p) => false.elim (h₁ h₂) }

theorem mem_span_insert {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {x : M} {s : set M} {y : M} : x ∈ span R (insert y s) ↔ ∃ (a : R), ∃ (z : M), ∃ (H : z ∈ span R s), x = a • y + z := sorry

theorem span_insert_eq_span {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {x : M} {s : set M} (h : x ∈ span R s) : span R (insert x s) = span R s :=
  span_eq_of_le (span R s) (iff.mpr set.insert_subset { left := h, right := subset_span })
    (span_mono (set.subset_insert x s))

theorem span_span {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {s : set M} : span R ↑(span R s) = span R s :=
  span_eq (span R s)

theorem span_eq_bot {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {s : set M} : span R s = ⊥ ↔ ∀ (x : M), x ∈ s → x = 0 := sorry

@[simp] theorem span_singleton_eq_bot {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {x : M} : span R (singleton x) = ⊥ ↔ x = 0 := sorry

@[simp] theorem span_zero {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] : span R 0 = ⊥ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (span R 0 = ⊥)) (Eq.symm set.singleton_zero)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (span R (singleton 0) = ⊥)) (propext span_singleton_eq_bot))) (Eq.refl 0))

@[simp] theorem span_image {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {s : set M} (f : linear_map R M M₂) : span R (⇑f '' s) = map f (span R s) :=
  span_eq_of_le (map f (span R s)) (set.image_subset (⇑f) subset_span)
    (iff.mpr map_le_iff_le_comap (iff.mpr span_le (iff.mp set.image_subset_iff subset_span)))

theorem supr_eq_span {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {ι : Sort w} (p : ι → submodule R M) : (supr fun (i : ι) => p i) = span R (set.Union fun (i : ι) => ↑(p i)) := sorry

theorem span_singleton_le_iff_mem {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (m : M) (p : submodule R M) : span R (singleton m) ≤ p ↔ m ∈ p :=
  eq.mpr (id (Eq._oldrec (Eq.refl (span R (singleton m) ≤ p ↔ m ∈ p)) (propext span_le)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (singleton m ⊆ ↑p ↔ m ∈ p)) (propext set.singleton_subset_iff)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (m ∈ ↑p ↔ m ∈ p)) (propext (mem_coe p)))) (iff.refl (m ∈ p))))

theorem lt_add_iff_not_mem {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {I : submodule R M} {a : M} : I < I + span R (singleton a) ↔ ¬a ∈ I := sorry

theorem mem_supr {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {ι : Sort w} (p : ι → submodule R M) {m : M} : (m ∈ supr fun (i : ι) => p i) ↔ ∀ (N : submodule R M), (∀ (i : ι), p i ≤ N) → m ∈ N := sorry

/-- For every element in the span of a set, there exists a finite subset of the set
such that the element is contained in the span of the subset. -/
theorem mem_span_finite_of_mem_span {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {S : set M} {x : M} (hx : x ∈ span R S) : ∃ (T : finset M), ↑T ⊆ S ∧ x ∈ span R ↑T := sorry

/-- The product of two submodules is a submodule. -/
def prod {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (p : submodule R M) (q : submodule R M₂) : submodule R (M × M₂) :=
  mk (set.prod ↑p ↑q) sorry sorry sorry

@[simp] theorem prod_coe {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (p : submodule R M) (q : submodule R M₂) : ↑(prod p q) = set.prod ↑p ↑q :=
  rfl

@[simp] theorem mem_prod {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {p : submodule R M} {q : submodule R M₂} {x : M × M₂} : x ∈ prod p q ↔ prod.fst x ∈ p ∧ prod.snd x ∈ q :=
  set.mem_prod

theorem span_prod_le {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (s : set M) (t : set M₂) : span R (set.prod s t) ≤ prod (span R s) (span R t) :=
  iff.mpr span_le (set.prod_mono subset_span subset_span)

@[simp] theorem prod_top {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : prod ⊤ ⊤ = ⊤ := sorry

@[simp] theorem prod_bot {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : prod ⊥ ⊥ = ⊥ := sorry

theorem prod_mono {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {p : submodule R M} {p' : submodule R M} {q : submodule R M₂} {q' : submodule R M₂} : p ≤ p' → q ≤ q' → prod p q ≤ prod p' q' :=
  set.prod_mono

@[simp] theorem prod_inf_prod {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (p : submodule R M) (p' : submodule R M) (q : submodule R M₂) (q' : submodule R M₂) : prod p q ⊓ prod p' q' = prod (p ⊓ p') (q ⊓ q') :=
  coe_injective set.prod_inter_prod

@[simp] theorem prod_sup_prod {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (p : submodule R M) (p' : submodule R M) (q : submodule R M₂) (q' : submodule R M₂) : prod p q ⊔ prod p' q' = prod (p ⊔ p') (q ⊔ q') := sorry

@[simp] theorem neg_coe {R : Type u} {M : Type v} [ring R] [add_comm_group M] [semimodule R M] (p : submodule R M) : -↑p = ↑p :=
  set.ext fun (x : M) => neg_mem_iff p

@[simp] protected theorem map_neg {R : Type u} {M : Type v} {M₂ : Type w} [ring R] [add_comm_group M] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] (p : submodule R M) (f : linear_map R M M₂) : map (-f) p = map f p := sorry

@[simp] theorem span_neg {R : Type u} {M : Type v} [ring R] [add_comm_group M] [semimodule R M] (s : set M) : span R (-s) = span R s := sorry

theorem mem_span_insert' {R : Type u} {M : Type v} [ring R] [add_comm_group M] [semimodule R M] {x : M} {y : M} {s : set M} : x ∈ span R (insert y s) ↔ ∃ (a : R), x + a • y ∈ span R s := sorry

-- TODO(Mario): Factor through add_subgroup

/-- The equivalence relation associated to a submodule `p`, defined by `x ≈ y` iff `y - x ∈ p`. -/
def quotient_rel {R : Type u} {M : Type v} [ring R] [add_comm_group M] [semimodule R M] (p : submodule R M) : setoid M :=
  setoid.mk (fun (x y : M) => x - y ∈ p) sorry

/-- The quotient of a module `M` by a submodule `p ⊆ M`. -/
def quotient {R : Type u} {M : Type v} [ring R] [add_comm_group M] [semimodule R M] (p : submodule R M)  :=
  quotient (quotient_rel p)

namespace quotient


/-- Map associating to an element of `M` the corresponding element of `M/p`,
when `p` is a submodule of `M`. -/
def mk {R : Type u} {M : Type v} [ring R] [add_comm_group M] [semimodule R M] {p : submodule R M} : M → quotient p :=
  quotient.mk'

@[simp] theorem mk_eq_mk {R : Type u} {M : Type v} [ring R] [add_comm_group M] [semimodule R M] {p : submodule R M} (x : M) : mk x = mk x :=
  rfl

@[simp] theorem mk'_eq_mk {R : Type u} {M : Type v} [ring R] [add_comm_group M] [semimodule R M] {p : submodule R M} (x : M) : quotient.mk' x = mk x :=
  rfl

@[simp] theorem quot_mk_eq_mk {R : Type u} {M : Type v} [ring R] [add_comm_group M] [semimodule R M] {p : submodule R M} (x : M) : Quot.mk setoid.r x = mk x :=
  rfl

protected theorem eq {R : Type u} {M : Type v} [ring R] [add_comm_group M] [semimodule R M] (p : submodule R M) {x : M} {y : M} : mk x = mk y ↔ x - y ∈ p :=
  quotient.eq'

protected instance has_zero {R : Type u} {M : Type v} [ring R] [add_comm_group M] [semimodule R M] (p : submodule R M) : HasZero (quotient p) :=
  { zero := mk 0 }

protected instance inhabited {R : Type u} {M : Type v} [ring R] [add_comm_group M] [semimodule R M] (p : submodule R M) : Inhabited (quotient p) :=
  { default := 0 }

@[simp] theorem mk_zero {R : Type u} {M : Type v} [ring R] [add_comm_group M] [semimodule R M] (p : submodule R M) : mk 0 = 0 :=
  rfl

@[simp] theorem mk_eq_zero {R : Type u} {M : Type v} [ring R] [add_comm_group M] [semimodule R M] (p : submodule R M) {x : M} : mk x = 0 ↔ x ∈ p := sorry

protected instance has_add {R : Type u} {M : Type v} [ring R] [add_comm_group M] [semimodule R M] (p : submodule R M) : Add (quotient p) :=
  { add := fun (a b : quotient p) => quotient.lift_on₂' a b (fun (a b : M) => mk (a + b)) sorry }

@[simp] theorem mk_add {R : Type u} {M : Type v} [ring R] [add_comm_group M] [semimodule R M] (p : submodule R M) {x : M} {y : M} : mk (x + y) = mk x + mk y :=
  rfl

protected instance has_neg {R : Type u} {M : Type v} [ring R] [add_comm_group M] [semimodule R M] (p : submodule R M) : Neg (quotient p) :=
  { neg := fun (a : quotient p) => quotient.lift_on' a (fun (a : M) => mk (-a)) sorry }

@[simp] theorem mk_neg {R : Type u} {M : Type v} [ring R] [add_comm_group M] [semimodule R M] (p : submodule R M) {x : M} : mk (-x) = -mk x :=
  rfl

protected instance has_sub {R : Type u} {M : Type v} [ring R] [add_comm_group M] [semimodule R M] (p : submodule R M) : Sub (quotient p) :=
  { sub := fun (a b : quotient p) => quotient.lift_on₂' a b (fun (a b : M) => mk (a - b)) sorry }

@[simp] theorem mk_sub {R : Type u} {M : Type v} [ring R] [add_comm_group M] [semimodule R M] (p : submodule R M) {x : M} {y : M} : mk (x - y) = mk x - mk y :=
  rfl

protected instance add_comm_group {R : Type u} {M : Type v} [ring R] [add_comm_group M] [semimodule R M] (p : submodule R M) : add_comm_group (quotient p) :=
  add_comm_group.mk Add.add sorry 0 sorry sorry Neg.neg Sub.sub sorry sorry

protected instance has_scalar {R : Type u} {M : Type v} [ring R] [add_comm_group M] [semimodule R M] (p : submodule R M) : has_scalar R (quotient p) :=
  has_scalar.mk fun (a : R) (x : quotient p) => quotient.lift_on' x (fun (x : M) => mk (a • x)) sorry

@[simp] theorem mk_smul {R : Type u} {M : Type v} [ring R] [add_comm_group M] [semimodule R M] (p : submodule R M) {r : R} {x : M} : mk (r • x) = r • mk x :=
  rfl

protected instance semimodule {R : Type u} {M : Type v} [ring R] [add_comm_group M] [semimodule R M] (p : submodule R M) : semimodule R (quotient p) :=
  semimodule.of_core (semimodule.core.mk (has_scalar.mk has_scalar.smul) sorry sorry sorry sorry)

theorem mk_surjective {R : Type u} {M : Type v} [ring R] [add_comm_group M] [semimodule R M] (p : submodule R M) : function.surjective mk :=
  id fun (b : quotient p) => quot.induction_on b fun (x : M) => Exists.intro x rfl

theorem nontrivial_of_lt_top {R : Type u} {M : Type v} [ring R] [add_comm_group M] [semimodule R M] (p : submodule R M) (h : p < ⊤) : nontrivial (quotient p) := sorry

end quotient


theorem quot_hom_ext {R : Type u} {M : Type v} {M₂ : Type w} [ring R] [add_comm_group M] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] (p : submodule R M) {f : linear_map R (quotient p) M₂} {g : linear_map R (quotient p) M₂} (h : ∀ (x : M), coe_fn f (quotient.mk x) = coe_fn g (quotient.mk x)) : f = g :=
  linear_map.ext fun (x : quotient p) => quotient.induction_on' x h

end submodule


namespace submodule


theorem comap_smul {K : Type u'} {V : Type v'} {V₂ : Type w'} [field K] [add_comm_group V] [vector_space K V] [add_comm_group V₂] [vector_space K V₂] (f : linear_map K V V₂) (p : submodule K V₂) (a : K) (h : a ≠ 0) : comap (a • f) p = comap f p := sorry

theorem map_smul {K : Type u'} {V : Type v'} {V₂ : Type w'} [field K] [add_comm_group V] [vector_space K V] [add_comm_group V₂] [vector_space K V₂] (f : linear_map K V V₂) (p : submodule K V) (a : K) (h : a ≠ 0) : map (a • f) p = map f p := sorry

theorem comap_smul' {K : Type u'} {V : Type v'} {V₂ : Type w'} [field K] [add_comm_group V] [vector_space K V] [add_comm_group V₂] [vector_space K V₂] (f : linear_map K V V₂) (p : submodule K V₂) (a : K) : comap (a • f) p = infi fun (h : a ≠ 0) => comap f p := sorry

theorem map_smul' {K : Type u'} {V : Type v'} {V₂ : Type w'} [field K] [add_comm_group V] [vector_space K V] [add_comm_group V₂] [vector_space K V₂] (f : linear_map K V V₂) (p : submodule K V) (a : K) : map (a • f) p = supr fun (h : a ≠ 0) => map f p := sorry

end submodule


/-! ### Properties of linear maps -/

namespace linear_map


/-- If two linear maps are equal on a set `s`, then they are equal on `submodule.span s`.

See also `linear_map.eq_on_span'` for a version using `set.eq_on`. -/
theorem eq_on_span {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {s : set M} {f : linear_map R M M₂} {g : linear_map R M M₂} (H : set.eq_on (⇑f) (⇑g) s) {x : M} (h : x ∈ submodule.span R s) : coe_fn f x = coe_fn g x := sorry

/-- If two linear maps are equal on a set `s`, then they are equal on `submodule.span s`.

This version uses `set.eq_on`, and the hidden argument will expand to `h : x ∈ (span R s : set M)`.
See `linear_map.eq_on_span` for a version that takes `h : x ∈ span R s` as an argument. -/
theorem eq_on_span' {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {s : set M} {f : linear_map R M M₂} {g : linear_map R M M₂} (H : set.eq_on (⇑f) (⇑g) s) : set.eq_on ⇑f ⇑g ↑(submodule.span R s) :=
  eq_on_span H

/-- If `s` generates the whole semimodule and linear maps `f`, `g` are equal on `s`, then they are
equal. -/
theorem ext_on {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {s : set M} {f : linear_map R M M₂} {g : linear_map R M M₂} (hv : submodule.span R s = ⊤) (h : set.eq_on (⇑f) (⇑g) s) : f = g :=
  ext fun (x : M) => eq_on_span h (iff.mp submodule.eq_top_iff' hv x)

/-- If the range of `v : ι → M` generates the whole semimodule and linear maps `f`, `g` are equal at
each `v i`, then they are equal. -/
theorem ext_on_range {R : Type u} {M : Type v} {M₂ : Type w} {ι : Type x} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {v : ι → M} {f : linear_map R M M₂} {g : linear_map R M M₂} (hv : submodule.span R (set.range v) = ⊤) (h : ∀ (i : ι), coe_fn f (v i) = coe_fn g (v i)) : f = g :=
  ext_on hv (iff.mpr set.forall_range_iff h)

@[simp] theorem map_finsupp_sum {R : Type u} {M : Type v} {M₂ : Type w} {ι : Type x} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {γ : Type u_1} [HasZero γ] (f : linear_map R M M₂) {t : ι →₀ γ} {g : ι → γ → M} : coe_fn f (finsupp.sum t g) = finsupp.sum t fun (i : ι) (d : γ) => coe_fn f (g i d) :=
  map_sum f

theorem coe_finsupp_sum {R : Type u} {M : Type v} {M₂ : Type w} {ι : Type x} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {γ : Type u_1} [HasZero γ] (t : ι →₀ γ) (g : ι → γ → linear_map R M M₂) : ⇑(finsupp.sum t g) = finsupp.sum t fun (i : ι) (d : γ) => ⇑(g i d) :=
  coe_fn_sum (finsupp.support t) fun (a : ι) => g a (coe_fn t a)

@[simp] theorem finsupp_sum_apply {R : Type u} {M : Type v} {M₂ : Type w} {ι : Type x} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {γ : Type u_1} [HasZero γ] (t : ι →₀ γ) (g : ι → γ → linear_map R M M₂) (b : M) : coe_fn (finsupp.sum t g) b = finsupp.sum t fun (i : ι) (d : γ) => coe_fn (g i d) b :=
  sum_apply (finsupp.support t) (fun (a : ι) => g a (coe_fn t a)) b

@[simp] theorem map_dfinsupp_sum {R : Type u} {M : Type v} {M₂ : Type w} {ι : Type x} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {γ : ι → Type u_1} [DecidableEq ι] [(i : ι) → HasZero (γ i)] [(i : ι) → (x : γ i) → Decidable (x ≠ 0)] (f : linear_map R M M₂) {t : dfinsupp fun (i : ι) => γ i} {g : (i : ι) → γ i → M} : coe_fn f (dfinsupp.sum t g) = dfinsupp.sum t fun (i : ι) (d : γ i) => coe_fn f (g i d) :=
  map_sum f

theorem coe_dfinsupp_sum {R : Type u} {M : Type v} {M₂ : Type w} {ι : Type x} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {γ : ι → Type u_1} [DecidableEq ι] [(i : ι) → HasZero (γ i)] [(i : ι) → (x : γ i) → Decidable (x ≠ 0)] (t : dfinsupp fun (i : ι) => γ i) (g : (i : ι) → γ i → linear_map R M M₂) : ⇑(dfinsupp.sum t g) = dfinsupp.sum t fun (i : ι) (d : γ i) => ⇑(g i d) :=
  coe_fn_sum (dfinsupp.support t) fun (i : ι) => g i (coe_fn t i)

@[simp] theorem dfinsupp_sum_apply {R : Type u} {M : Type v} {M₂ : Type w} {ι : Type x} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {γ : ι → Type u_1} [DecidableEq ι] [(i : ι) → HasZero (γ i)] [(i : ι) → (x : γ i) → Decidable (x ≠ 0)] (t : dfinsupp fun (i : ι) => γ i) (g : (i : ι) → γ i → linear_map R M M₂) (b : M) : coe_fn (dfinsupp.sum t g) b = dfinsupp.sum t fun (i : ι) (d : γ i) => coe_fn (g i d) b :=
  sum_apply (dfinsupp.support t) (fun (i : ι) => g i (coe_fn t i)) b

theorem map_cod_restrict {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (p : submodule R M) (f : linear_map R M₂ M) (h : ∀ (c : M₂), coe_fn f c ∈ p) (p' : submodule R M₂) : submodule.map (cod_restrict p f h) p' = submodule.comap (submodule.subtype p) (submodule.map f p') := sorry

theorem comap_cod_restrict {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (p : submodule R M) (f : linear_map R M₂ M) (hf : ∀ (c : M₂), coe_fn f c ∈ p) (p' : submodule R ↥p) : submodule.comap (cod_restrict p f hf) p' = submodule.comap f (submodule.map (submodule.subtype p) p') := sorry

/-- The range of a linear map `f : M → M₂` is a submodule of `M₂`. -/
def range {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M M₂) : submodule R M₂ :=
  submodule.map f ⊤

theorem range_coe {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M M₂) : ↑(range f) = set.range ⇑f :=
  set.image_univ

@[simp] theorem mem_range {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {f : linear_map R M M₂} {x : M₂} : x ∈ range f ↔ ∃ (y : M), coe_fn f y = x :=
  iff.mp set.ext_iff (range_coe f)

theorem mem_range_self {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M M₂) (x : M) : coe_fn f x ∈ range f :=
  iff.mpr mem_range (Exists.intro x rfl)

@[simp] theorem range_id {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] : range id = ⊤ :=
  submodule.map_id ⊤

theorem range_comp {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (f : linear_map R M M₂) (g : linear_map R M₂ M₃) : range (comp g f) = submodule.map g (range f) :=
  submodule.map_comp f g ⊤

theorem range_comp_le_range {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (f : linear_map R M M₂) (g : linear_map R M₂ M₃) : range (comp g f) ≤ range g :=
  eq.mpr (id (Eq._oldrec (Eq.refl (range (comp g f) ≤ range g)) (range_comp f g))) (submodule.map_mono le_top)

theorem range_eq_top {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {f : linear_map R M M₂} : range f = ⊤ ↔ function.surjective ⇑f := sorry

theorem range_le_iff_comap {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {f : linear_map R M M₂} {p : submodule R M₂} : range f ≤ p ↔ submodule.comap f p = ⊤ := sorry

theorem map_le_range {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {f : linear_map R M M₂} {p : submodule R M} : submodule.map f p ≤ range f :=
  submodule.map_mono le_top

theorem range_coprod {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (f : linear_map R M M₃) (g : linear_map R M₂ M₃) : range (coprod f g) = range f ⊔ range g := sorry

theorem is_compl_range_inl_inr {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : is_compl (range (inl R M M₂)) (range (inr R M M₂)) := sorry

theorem sup_range_inl_inr {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : range (inl R M M₂) ⊔ range (inr R M M₂) = ⊤ :=
  is_compl.sup_eq_top is_compl_range_inl_inr

/-- Restrict the codomain of a linear map `f` to `f.range`. -/
def range_restrict {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M M₂) : linear_map R M ↥(range f) :=
  cod_restrict (range f) f (mem_range_self f)

/-- Given an element `x` of a module `M` over `R`, the natural map from
    `R` to scalar multiples of `x`.-/
def to_span_singleton (R : Type u) (M : Type v) [semiring R] [add_comm_monoid M] [semimodule R M] (x : M) : linear_map R R M :=
  smul_right id x

/-- The range of `to_span_singleton x` is the span of `x`.-/
theorem span_singleton_eq_range (R : Type u) (M : Type v) [semiring R] [add_comm_monoid M] [semimodule R M] (x : M) : submodule.span R (singleton x) = range (to_span_singleton R M x) :=
  submodule.ext fun (y : M) => iff.trans submodule.mem_span_singleton (iff.symm mem_range)

theorem to_span_singleton_one (R : Type u) (M : Type v) [semiring R] [add_comm_monoid M] [semimodule R M] (x : M) : coe_fn (to_span_singleton R M x) 1 = x :=
  one_smul R x

/-- The kernel of a linear map `f : M → M₂` is defined to be `comap f ⊥`. This is equivalent to the
set of `x : M` such that `f x = 0`. The kernel is a submodule of `M`. -/
def ker {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M M₂) : submodule R M :=
  submodule.comap f ⊥

@[simp] theorem mem_ker {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {f : linear_map R M M₂} {y : M} : y ∈ ker f ↔ coe_fn f y = 0 :=
  submodule.mem_bot R

@[simp] theorem ker_id {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] : ker id = ⊥ :=
  rfl

@[simp] theorem map_coe_ker {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M M₂) (x : ↥(ker f)) : coe_fn f ↑x = 0 :=
  iff.mp mem_ker (subtype.property x)

theorem comp_ker_subtype {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M M₂) : comp f (submodule.subtype (ker f)) = 0 := sorry

theorem ker_comp {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (f : linear_map R M M₂) (g : linear_map R M₂ M₃) : ker (comp g f) = submodule.comap f (ker g) :=
  rfl

theorem ker_le_ker_comp {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (f : linear_map R M M₂) (g : linear_map R M₂ M₃) : ker f ≤ ker (comp g f) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (ker f ≤ ker (comp g f))) (ker_comp f g))) (submodule.comap_mono bot_le)

theorem disjoint_ker {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {f : linear_map R M M₂} {p : submodule R M} : disjoint p (ker f) ↔ ∀ (x : M), x ∈ p → coe_fn f x = 0 → x = 0 := sorry

theorem disjoint_inl_inr {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : disjoint (range (inl R M M₂)) (range (inr R M M₂)) := sorry

theorem ker_eq_bot' {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {f : linear_map R M M₂} : ker f = ⊥ ↔ ∀ (m : M), coe_fn f m = 0 → m = 0 := sorry

theorem ker_eq_bot_of_inverse {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {f : linear_map R M M₂} {g : linear_map R M₂ M} (h : comp g f = id) : ker f = ⊥ := sorry

theorem le_ker_iff_map {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {f : linear_map R M M₂} {p : submodule R M} : p ≤ ker f ↔ submodule.map f p = ⊥ := sorry

theorem ker_cod_restrict {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (p : submodule R M) (f : linear_map R M₂ M) (hf : ∀ (c : M₂), coe_fn f c ∈ p) : ker (cod_restrict p f hf) = ker f := sorry

theorem range_cod_restrict {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (p : submodule R M) (f : linear_map R M₂ M) (hf : ∀ (c : M₂), coe_fn f c ∈ p) : range (cod_restrict p f hf) = submodule.comap (submodule.subtype p) (range f) :=
  map_cod_restrict p f hf ⊤

theorem ker_restrict {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {p : submodule R M} {f : linear_map R M M} (hf : ∀ (x : M), x ∈ p → coe_fn f x ∈ p) : ker (restrict f hf) = ker (dom_restrict f p) := sorry

theorem map_comap_eq {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M M₂) (q : submodule R M₂) : submodule.map f (submodule.comap f q) = range f ⊓ q := sorry

theorem map_comap_eq_self {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {f : linear_map R M M₂} {q : submodule R M₂} (h : q ≤ range f) : submodule.map f (submodule.comap f q) = q :=
  eq.mpr (id (Eq._oldrec (Eq.refl (submodule.map f (submodule.comap f q) = q)) (map_comap_eq f q)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (range f ⊓ q = q)) (propext inf_eq_right))) h)

@[simp] theorem ker_zero {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : ker 0 = ⊤ := sorry

@[simp] theorem range_zero {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : range 0 = ⊥ :=
  submodule.map_zero ⊤

theorem ker_eq_top {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {f : linear_map R M M₂} : ker f = ⊤ ↔ f = 0 :=
  { mp := fun (h : ker f = ⊤) => ext fun (x : M) => iff.mp mem_ker (Eq.symm h ▸ trivial),
    mpr := fun (h : f = 0) => Eq.symm h ▸ ker_zero }

theorem range_le_bot_iff {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M M₂) : range f ≤ ⊥ ↔ f = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (range f ≤ ⊥ ↔ f = 0)) (propext range_le_iff_comap))) ker_eq_top

theorem range_eq_bot {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {f : linear_map R M M₂} : range f = ⊥ ↔ f = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (range f = ⊥ ↔ f = 0)) (Eq.symm (propext (range_le_bot_iff f)))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (range f = ⊥ ↔ range f ≤ ⊥)) (propext le_bot_iff))) (iff.refl (range f = ⊥)))

theorem range_le_ker_iff {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] {f : linear_map R M M₂} {g : linear_map R M₂ M₃} : range f ≤ ker g ↔ comp g f = 0 := sorry

theorem comap_le_comap_iff {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {f : linear_map R M M₂} (hf : range f = ⊤) {p : submodule R M₂} {p' : submodule R M₂} : submodule.comap f p ≤ submodule.comap f p' ↔ p ≤ p' := sorry

theorem comap_injective {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {f : linear_map R M M₂} (hf : range f = ⊤) : function.injective (submodule.comap f) :=
  fun (p p' : submodule R M₂) (h : submodule.comap f p = submodule.comap f p') =>
    le_antisymm (iff.mp (comap_le_comap_iff hf) (le_of_eq h)) (iff.mp (comap_le_comap_iff hf) (ge_of_eq h))

theorem map_coprod_prod {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (f : linear_map R M M₃) (g : linear_map R M₂ M₃) (p : submodule R M) (q : submodule R M₂) : submodule.map (coprod f g) (submodule.prod p q) = submodule.map f p ⊔ submodule.map g q := sorry

theorem comap_prod_prod {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (f : linear_map R M M₂) (g : linear_map R M M₃) (p : submodule R M₂) (q : submodule R M₃) : submodule.comap (prod f g) (submodule.prod p q) = submodule.comap f p ⊓ submodule.comap g q :=
  submodule.ext fun (x : M) => iff.rfl

theorem prod_eq_inf_comap {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (p : submodule R M) (q : submodule R M₂) : submodule.prod p q = submodule.comap (fst R M M₂) p ⊓ submodule.comap (snd R M M₂) q :=
  submodule.ext fun (x : M × M₂) => iff.rfl

theorem prod_eq_sup_map {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (p : submodule R M) (q : submodule R M₂) : submodule.prod p q = submodule.map (inl R M M₂) p ⊔ submodule.map (inr R M M₂) q := sorry

theorem span_inl_union_inr {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {s : set M} {t : set M₂} : submodule.span R (⇑(inl R M M₂) '' s ∪ ⇑(inr R M M₂) '' t) = submodule.prod (submodule.span R s) (submodule.span R t) := sorry

@[simp] theorem ker_prod {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (f : linear_map R M M₂) (g : linear_map R M M₃) : ker (prod f g) = ker f ⊓ ker g := sorry

theorem range_prod_le {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (f : linear_map R M M₂) (g : linear_map R M M₃) : range (prod f g) ≤ submodule.prod (range f) (range g) := sorry

theorem ker_eq_bot_of_injective {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {f : linear_map R M M₂} (hf : function.injective ⇑f) : ker f = ⊥ := sorry

theorem comap_map_eq {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_group M] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M M₂) (p : submodule R M) : submodule.comap f (submodule.map f p) = p ⊔ ker f := sorry

theorem comap_map_eq_self {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_group M] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] {f : linear_map R M M₂} {p : submodule R M} (h : ker f ≤ p) : submodule.comap f (submodule.map f p) = p :=
  eq.mpr (id (Eq._oldrec (Eq.refl (submodule.comap f (submodule.map f p) = p)) (comap_map_eq f p)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (p ⊔ ker f = p)) (sup_of_le_left h))) (Eq.refl p))

theorem map_le_map_iff {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_group M] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M M₂) {p : submodule R M} {p' : submodule R M} : submodule.map f p ≤ submodule.map f p' ↔ p ≤ p' ⊔ ker f := sorry

theorem map_le_map_iff' {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_group M] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] {f : linear_map R M M₂} (hf : ker f = ⊥) {p : submodule R M} {p' : submodule R M} : submodule.map f p ≤ submodule.map f p' ↔ p ≤ p' :=
  eq.mpr (id (Eq._oldrec (Eq.refl (submodule.map f p ≤ submodule.map f p' ↔ p ≤ p')) (propext (map_le_map_iff f))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (p ≤ p' ⊔ ker f ↔ p ≤ p')) hf))
      (eq.mpr (id (Eq._oldrec (Eq.refl (p ≤ p' ⊔ ⊥ ↔ p ≤ p')) sup_bot_eq)) (iff.refl (p ≤ p'))))

theorem map_injective {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_group M] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] {f : linear_map R M M₂} (hf : ker f = ⊥) : function.injective (submodule.map f) :=
  fun (p p' : submodule R M) (h : submodule.map f p = submodule.map f p') =>
    le_antisymm (iff.mp (map_le_map_iff' hf) (le_of_eq h)) (iff.mp (map_le_map_iff' hf) (ge_of_eq h))

theorem map_eq_top_iff {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_group M] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] {f : linear_map R M M₂} (hf : range f = ⊤) {p : submodule R M} : submodule.map f p = ⊤ ↔ p ⊔ ker f = ⊤ := sorry

theorem sub_mem_ker_iff {R : Type u} {M : Type v} {M₂ : Type w} [ring R] [add_comm_group M] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] {f : linear_map R M M₂} {x : M} {y : M} : x - y ∈ ker f ↔ coe_fn f x = coe_fn f y := sorry

theorem disjoint_ker' {R : Type u} {M : Type v} {M₂ : Type w} [ring R] [add_comm_group M] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] {f : linear_map R M M₂} {p : submodule R M} : disjoint p (ker f) ↔ ∀ (x y : M), x ∈ p → y ∈ p → coe_fn f x = coe_fn f y → x = y := sorry

theorem inj_of_disjoint_ker {R : Type u} {M : Type v} {M₂ : Type w} [ring R] [add_comm_group M] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] {f : linear_map R M M₂} {p : submodule R M} {s : set M} (h : s ⊆ ↑p) (hd : disjoint p (ker f)) (x : M) (y : M) (H : x ∈ s) : y ∈ s → coe_fn f x = coe_fn f y → x = y :=
  fun (hy : y ∈ s) => iff.mp disjoint_ker' hd x y (h hx) (h hy)

theorem ker_eq_bot {R : Type u} {M : Type v} {M₂ : Type w} [ring R] [add_comm_group M] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] {f : linear_map R M M₂} : ker f = ⊥ ↔ function.injective ⇑f := sorry

theorem ker_le_iff {R : Type u} {M : Type v} {M₂ : Type w} [ring R] [add_comm_group M] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] {f : linear_map R M M₂} {p : submodule R M} : ker f ≤ p ↔ ∃ (y : M₂), ∃ (H : y ∈ range f), ⇑f ⁻¹' singleton y ⊆ ↑p := sorry

/-- If the union of the kernels `ker f` and `ker g` spans the domain, then the range of
`prod f g` is equal to the product of `range f` and `range g`. -/
theorem range_prod_eq {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} [ring R] [add_comm_group M] [add_comm_group M₂] [add_comm_group M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] {f : linear_map R M M₂} {g : linear_map R M M₃} (h : ker f ⊔ ker g = ⊤) : range (prod f g) = submodule.prod (range f) (range g) := sorry

theorem ker_smul {K : Type u'} {V : Type v'} {V₂ : Type w'} [field K] [add_comm_group V] [vector_space K V] [add_comm_group V₂] [vector_space K V₂] (f : linear_map K V V₂) (a : K) (h : a ≠ 0) : ker (a • f) = ker f :=
  submodule.comap_smul f ⊥ a h

theorem ker_smul' {K : Type u'} {V : Type v'} {V₂ : Type w'} [field K] [add_comm_group V] [vector_space K V] [add_comm_group V₂] [vector_space K V₂] (f : linear_map K V V₂) (a : K) : ker (a • f) = infi fun (h : a ≠ 0) => ker f :=
  submodule.comap_smul' f ⊥ a

theorem range_smul {K : Type u'} {V : Type v'} {V₂ : Type w'} [field K] [add_comm_group V] [vector_space K V] [add_comm_group V₂] [vector_space K V₂] (f : linear_map K V V₂) (a : K) (h : a ≠ 0) : range (a • f) = range f :=
  submodule.map_smul f ⊤ a h

theorem range_smul' {K : Type u'} {V : Type v'} {V₂ : Type w'} [field K] [add_comm_group V] [vector_space K V] [add_comm_group V₂] [vector_space K V₂] (f : linear_map K V V₂) (a : K) : range (a • f) = supr fun (h : a ≠ 0) => range f :=
  submodule.map_smul' f ⊤ a

end linear_map


theorem submodule.sup_eq_range {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (p : submodule R M) (q : submodule R M) : p ⊔ q = linear_map.range (linear_map.coprod (submodule.subtype p) (submodule.subtype q)) := sorry

namespace is_linear_map


theorem is_linear_map_add {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] : is_linear_map R fun (x : M × M) => prod.fst x + prod.snd x := sorry

theorem is_linear_map_sub {R : Type u_1} {M : Type u_2} [semiring R] [add_comm_group M] [semimodule R M] : is_linear_map R fun (x : M × M) => prod.fst x - prod.snd x := sorry

end is_linear_map


namespace submodule


@[simp] theorem map_top {R : Type u} {M : Type v} {M₂ : Type w} {T : semiring R} [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M M₂) : map f ⊤ = linear_map.range f :=
  rfl

@[simp] theorem comap_bot {R : Type u} {M : Type v} {M₂ : Type w} {T : semiring R} [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M M₂) : comap f ⊥ = linear_map.ker f :=
  rfl

@[simp] theorem ker_subtype {R : Type u} {M : Type v} {T : semiring R} [add_comm_monoid M] [semimodule R M] (p : submodule R M) : linear_map.ker (submodule.subtype p) = ⊥ :=
  linear_map.ker_eq_bot_of_injective fun (x y : ↥p) => subtype.ext_val

@[simp] theorem range_subtype {R : Type u} {M : Type v} {T : semiring R} [add_comm_monoid M] [semimodule R M] (p : submodule R M) : linear_map.range (submodule.subtype p) = p := sorry

theorem map_subtype_le {R : Type u} {M : Type v} {T : semiring R} [add_comm_monoid M] [semimodule R M] (p : submodule R M) (p' : submodule R ↥p) : map (submodule.subtype p) p' ≤ p := sorry

/-- Under the canonical linear map from a submodule `p` to the ambient space `M`, the image of the
maximal submodule of `p` is just `p `. -/
@[simp] theorem map_subtype_top {R : Type u} {M : Type v} {T : semiring R} [add_comm_monoid M] [semimodule R M] (p : submodule R M) : map (submodule.subtype p) ⊤ = p := sorry

@[simp] theorem comap_subtype_eq_top {R : Type u} {M : Type v} {T : semiring R} [add_comm_monoid M] [semimodule R M] {p : submodule R M} {p' : submodule R M} : comap (submodule.subtype p) p' = ⊤ ↔ p ≤ p' := sorry

@[simp] theorem comap_subtype_self {R : Type u} {M : Type v} {T : semiring R} [add_comm_monoid M] [semimodule R M] (p : submodule R M) : comap (submodule.subtype p) p = ⊤ :=
  iff.mpr comap_subtype_eq_top (le_refl p)

@[simp] theorem ker_of_le {R : Type u} {M : Type v} {T : semiring R} [add_comm_monoid M] [semimodule R M] (p : submodule R M) (p' : submodule R M) (h : p ≤ p') : linear_map.ker (of_le h) = ⊥ := sorry

theorem range_of_le {R : Type u} {M : Type v} {T : semiring R} [add_comm_monoid M] [semimodule R M] (p : submodule R M) (q : submodule R M) (h : p ≤ q) : linear_map.range (of_le h) = comap (submodule.subtype q) p := sorry

@[simp] theorem map_inl {R : Type u} {M : Type v} {M₂ : Type w} {T : semiring R} [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (p : submodule R M) : map (linear_map.inl R M M₂) p = prod p ⊥ := sorry

@[simp] theorem map_inr {R : Type u} {M : Type v} {M₂ : Type w} {T : semiring R} [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (q : submodule R M₂) : map (linear_map.inr R M M₂) q = prod ⊥ q := sorry

@[simp] theorem comap_fst {R : Type u} {M : Type v} {M₂ : Type w} {T : semiring R} [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (p : submodule R M) : comap (linear_map.fst R M M₂) p = prod p ⊤ := sorry

@[simp] theorem comap_snd {R : Type u} {M : Type v} {M₂ : Type w} {T : semiring R} [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (q : submodule R M₂) : comap (linear_map.snd R M M₂) q = prod ⊤ q := sorry

@[simp] theorem prod_comap_inl {R : Type u} {M : Type v} {M₂ : Type w} {T : semiring R} [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (p : submodule R M) (q : submodule R M₂) : comap (linear_map.inl R M M₂) (prod p q) = p := sorry

@[simp] theorem prod_comap_inr {R : Type u} {M : Type v} {M₂ : Type w} {T : semiring R} [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (p : submodule R M) (q : submodule R M₂) : comap (linear_map.inr R M M₂) (prod p q) = q := sorry

@[simp] theorem prod_map_fst {R : Type u} {M : Type v} {M₂ : Type w} {T : semiring R} [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (p : submodule R M) (q : submodule R M₂) : map (linear_map.fst R M M₂) (prod p q) = p := sorry

@[simp] theorem prod_map_snd {R : Type u} {M : Type v} {M₂ : Type w} {T : semiring R} [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (p : submodule R M) (q : submodule R M₂) : map (linear_map.snd R M M₂) (prod p q) = q := sorry

@[simp] theorem ker_inl {R : Type u} {M : Type v} {M₂ : Type w} {T : semiring R} [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : linear_map.ker (linear_map.inl R M M₂) = ⊥ := sorry

@[simp] theorem ker_inr {R : Type u} {M : Type v} {M₂ : Type w} {T : semiring R} [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : linear_map.ker (linear_map.inr R M M₂) = ⊥ := sorry

@[simp] theorem range_fst {R : Type u} {M : Type v} {M₂ : Type w} {T : semiring R} [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : linear_map.range (linear_map.fst R M M₂) = ⊤ := sorry

@[simp] theorem range_snd {R : Type u} {M : Type v} {M₂ : Type w} {T : semiring R} [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : linear_map.range (linear_map.snd R M M₂) = ⊤ := sorry

theorem disjoint_iff_comap_eq_bot {R : Type u} {M : Type v} {T : ring R} [add_comm_group M] [semimodule R M] {p : submodule R M} {q : submodule R M} : disjoint p q ↔ comap (submodule.subtype p) q = ⊥ := sorry

/-- If `N ⊆ M` then submodules of `N` are the same as submodules of `M` contained in `N` -/
def map_subtype.rel_iso {R : Type u} {M : Type v} {T : ring R} [add_comm_group M] [semimodule R M] (p : submodule R M) : submodule R ↥p ≃o Subtype fun (p' : submodule R M) => p' ≤ p :=
  rel_iso.mk
    (equiv.mk (fun (p' : submodule R ↥p) => { val := map (submodule.subtype p) p', property := sorry })
      (fun (q : Subtype fun (p' : submodule R M) => p' ≤ p) => comap (submodule.subtype p) ↑q) sorry sorry)
    sorry

/-- If `p ⊆ M` is a submodule, the ordering of submodules of `p` is embedded in the ordering of
submodules of `M`. -/
def map_subtype.order_embedding {R : Type u} {M : Type v} {T : ring R} [add_comm_group M] [semimodule R M] (p : submodule R M) : submodule R ↥p ↪o submodule R M :=
  rel_embedding.trans (rel_iso.to_rel_embedding (map_subtype.rel_iso p))
    (subtype.rel_embedding LessEq fun (p' : submodule R M) => p' ≤ p)

@[simp] theorem map_subtype_embedding_eq {R : Type u} {M : Type v} {T : ring R} [add_comm_group M] [semimodule R M] (p : submodule R M) (p' : submodule R ↥p) : coe_fn (map_subtype.order_embedding p) p' = map (submodule.subtype p) p' :=
  rfl

/-- The map from a module `M` to the quotient of `M` by a submodule `p` as a linear map. -/
def mkq {R : Type u} {M : Type v} {T : ring R} [add_comm_group M] [semimodule R M] (p : submodule R M) : linear_map R M (quotient p) :=
  linear_map.mk quotient.mk sorry sorry

@[simp] theorem mkq_apply {R : Type u} {M : Type v} {T : ring R} [add_comm_group M] [semimodule R M] (p : submodule R M) (x : M) : coe_fn (mkq p) x = quotient.mk x :=
  rfl

/-- The map from the quotient of `M` by a submodule `p` to `M₂` induced by a linear map `f : M → M₂`
vanishing on `p`, as a linear map. -/
def liftq {R : Type u} {M : Type v} {M₂ : Type w} {T : ring R} [add_comm_group M] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] (p : submodule R M) (f : linear_map R M M₂) (h : p ≤ linear_map.ker f) : linear_map R (quotient p) M₂ :=
  linear_map.mk (fun (x : quotient p) => quotient.lift_on' x ⇑f sorry) sorry sorry

@[simp] theorem liftq_apply {R : Type u} {M : Type v} {M₂ : Type w} {T : ring R} [add_comm_group M] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] (p : submodule R M) (f : linear_map R M M₂) {h : p ≤ linear_map.ker f} (x : M) : coe_fn (liftq p f h) (quotient.mk x) = coe_fn f x :=
  rfl

@[simp] theorem liftq_mkq {R : Type u} {M : Type v} {M₂ : Type w} {T : ring R} [add_comm_group M] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] (p : submodule R M) (f : linear_map R M M₂) (h : p ≤ linear_map.ker f) : linear_map.comp (liftq p f h) (mkq p) = f :=
  linear_map.ext fun (x : M) => Eq.refl (coe_fn (linear_map.comp (liftq p f h) (mkq p)) x)

@[simp] theorem range_mkq {R : Type u} {M : Type v} {T : ring R} [add_comm_group M] [semimodule R M] (p : submodule R M) : linear_map.range (mkq p) = ⊤ :=
  iff.mpr eq_top_iff'
    fun (x : quotient p) => quot.induction_on x fun (x : M) => Exists.intro x { left := trivial, right := rfl }

@[simp] theorem ker_mkq {R : Type u} {M : Type v} {T : ring R} [add_comm_group M] [semimodule R M] (p : submodule R M) : linear_map.ker (mkq p) = p := sorry

theorem le_comap_mkq {R : Type u} {M : Type v} {T : ring R} [add_comm_group M] [semimodule R M] (p : submodule R M) (p' : submodule R (quotient p)) : p ≤ comap (mkq p) p' := sorry

@[simp] theorem mkq_map_self {R : Type u} {M : Type v} {T : ring R} [add_comm_group M] [semimodule R M] (p : submodule R M) : map (mkq p) p = ⊥ := sorry

@[simp] theorem comap_map_mkq {R : Type u} {M : Type v} {T : ring R} [add_comm_group M] [semimodule R M] (p : submodule R M) (p' : submodule R M) : comap (mkq p) (map (mkq p) p') = p ⊔ p' := sorry

@[simp] theorem map_mkq_eq_top {R : Type u} {M : Type v} {T : ring R} [add_comm_group M] [semimodule R M] (p : submodule R M) (p' : submodule R M) : map (mkq p) p' = ⊤ ↔ p ⊔ p' = ⊤ := sorry

/-- The map from the quotient of `M` by submodule `p` to the quotient of `M₂` by submodule `q` along
`f : M → M₂` is linear. -/
def mapq {R : Type u} {M : Type v} {M₂ : Type w} {T : ring R} [add_comm_group M] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] (p : submodule R M) (q : submodule R M₂) (f : linear_map R M M₂) (h : p ≤ comap f q) : linear_map R (quotient p) (quotient q) :=
  liftq p (linear_map.comp (mkq q) f) sorry

@[simp] theorem mapq_apply {R : Type u} {M : Type v} {M₂ : Type w} {T : ring R} [add_comm_group M] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] (p : submodule R M) (q : submodule R M₂) (f : linear_map R M M₂) {h : p ≤ comap f q} (x : M) : coe_fn (mapq p q f h) (quotient.mk x) = quotient.mk (coe_fn f x) :=
  rfl

theorem mapq_mkq {R : Type u} {M : Type v} {M₂ : Type w} {T : ring R} [add_comm_group M] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] (p : submodule R M) (q : submodule R M₂) (f : linear_map R M M₂) {h : p ≤ comap f q} : linear_map.comp (mapq p q f h) (mkq p) = linear_map.comp (mkq q) f :=
  linear_map.ext fun (x : M) => Eq.refl (coe_fn (linear_map.comp (mapq p q f h) (mkq p)) x)

theorem comap_liftq {R : Type u} {M : Type v} {M₂ : Type w} {T : ring R} [add_comm_group M] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] (p : submodule R M) (q : submodule R M₂) (f : linear_map R M M₂) (h : p ≤ linear_map.ker f) : comap (liftq p f h) q = map (mkq p) (comap f q) := sorry

theorem map_liftq {R : Type u} {M : Type v} {M₂ : Type w} {T : ring R} [add_comm_group M] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] (p : submodule R M) (f : linear_map R M M₂) (h : p ≤ linear_map.ker f) (q : submodule R (quotient p)) : map (liftq p f h) q = map f (comap (mkq p) q) := sorry

theorem ker_liftq {R : Type u} {M : Type v} {M₂ : Type w} {T : ring R} [add_comm_group M] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] (p : submodule R M) (f : linear_map R M M₂) (h : p ≤ linear_map.ker f) : linear_map.ker (liftq p f h) = map (mkq p) (linear_map.ker f) :=
  comap_liftq p ⊥ f h

theorem range_liftq {R : Type u} {M : Type v} {M₂ : Type w} {T : ring R} [add_comm_group M] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] (p : submodule R M) (f : linear_map R M M₂) (h : p ≤ linear_map.ker f) : linear_map.range (liftq p f h) = linear_map.range f :=
  map_liftq p f h ⊤

theorem ker_liftq_eq_bot {R : Type u} {M : Type v} {M₂ : Type w} {T : ring R} [add_comm_group M] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] (p : submodule R M) (f : linear_map R M M₂) (h : p ≤ linear_map.ker f) (h' : linear_map.ker f ≤ p) : linear_map.ker (liftq p f h) = ⊥ := sorry

/-- The correspondence theorem for modules: there is an order isomorphism between submodules of the
quotient of `M` by `p`, and submodules of `M` larger than `p`. -/
def comap_mkq.rel_iso {R : Type u} {M : Type v} {T : ring R} [add_comm_group M] [semimodule R M] (p : submodule R M) : submodule R (quotient p) ≃o Subtype fun (p' : submodule R M) => p ≤ p' :=
  rel_iso.mk
    (equiv.mk (fun (p' : submodule R (quotient p)) => { val := comap (mkq p) p', property := le_comap_mkq p p' })
      (fun (q : Subtype fun (p' : submodule R M) => p ≤ p') => map (mkq p) ↑q) sorry sorry)
    sorry

/-- The ordering on submodules of the quotient of `M` by `p` embeds into the ordering on submodules
of `M`. -/
def comap_mkq.order_embedding {R : Type u} {M : Type v} {T : ring R} [add_comm_group M] [semimodule R M] (p : submodule R M) : submodule R (quotient p) ↪o submodule R M :=
  rel_embedding.trans (rel_iso.to_rel_embedding (comap_mkq.rel_iso p))
    (subtype.rel_embedding LessEq fun (p' : submodule R M) => p ≤ p')

@[simp] theorem comap_mkq_embedding_eq {R : Type u} {M : Type v} {T : ring R} [add_comm_group M] [semimodule R M] (p : submodule R M) (p' : submodule R (quotient p)) : coe_fn (comap_mkq.order_embedding p) p' = comap (mkq p) p' :=
  rfl

theorem span_preimage_eq {R : Type u} {M : Type v} {M₂ : Type w} {T : ring R} [add_comm_group M] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] {f : linear_map R M M₂} {s : set M₂} (h₀ : set.nonempty s) (h₁ : s ⊆ ↑(linear_map.range f)) : span R (⇑f ⁻¹' s) = comap f (span R s) := sorry

end submodule


namespace linear_map


theorem range_mkq_comp {R : Type u} {M : Type v} {M₂ : Type w} [ring R] [add_comm_group M] [add_comm_group M₂] [module R M] [module R M₂] (f : linear_map R M M₂) : comp (submodule.mkq (range f)) f = 0 := sorry

theorem ker_le_range_iff {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} [ring R] [add_comm_group M] [add_comm_group M₂] [add_comm_group M₃] [module R M] [module R M₂] [module R M₃] {f : linear_map R M M₂} {g : linear_map R M₂ M₃} : ker g ≤ range f ↔ comp (submodule.mkq (range f)) (submodule.subtype (ker g)) = 0 := sorry

/-- A monomorphism is injective. -/
theorem ker_eq_bot_of_cancel {R : Type u} {M : Type v} {M₂ : Type w} [ring R] [add_comm_group M] [add_comm_group M₂] [module R M] [module R M₂] {f : linear_map R M M₂} (h : ∀ (u v : linear_map R (↥(ker f)) M), comp f u = comp f v → u = v) : ker f = ⊥ := sorry

/-- An epimorphism is surjective. -/
theorem range_eq_top_of_cancel {R : Type u} {M : Type v} {M₂ : Type w} [ring R] [add_comm_group M] [add_comm_group M₂] [module R M] [module R M₂] {f : linear_map R M M₂} (h : ∀ (u v : linear_map R M₂ (submodule.quotient (range f))), comp u f = comp v f → u = v) : range f = ⊤ := sorry

end linear_map


@[simp] theorem linear_map.range_range_restrict {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M M₂) : linear_map.range (linear_map.range_restrict f) = ⊤ := sorry

/-! ### Linear equivalences -/

namespace linear_equiv


theorem map_eq_comap {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂} (e : linear_equiv R M M₂) {p : submodule R M} : submodule.map (↑e) p = submodule.comap (↑(symm e)) p := sorry

/-- A linear equivalence of two modules restricts to a linear equivalence from any submodule
of the domain onto the image of the submodule. -/
def of_submodule {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂} (e : linear_equiv R M M₂) (p : submodule R M) : linear_equiv R ↥p ↥(submodule.map (↑e) p) :=
  mk (linear_map.to_fun (linear_map.cod_restrict (submodule.map (↑e) p) (linear_map.dom_restrict (↑e) p) sorry)) sorry
    sorry (fun (y : ↥(submodule.map (↑e) p)) => { val := coe_fn (symm e) ↑y, property := sorry }) sorry sorry

@[simp] theorem of_submodule_apply {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂} (e : linear_equiv R M M₂) (p : submodule R M) (x : ↥p) : ↑(coe_fn (of_submodule e p) x) = coe_fn e ↑x :=
  rfl

@[simp] theorem of_submodule_symm_apply {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂} (e : linear_equiv R M M₂) (p : submodule R M) (x : ↥(submodule.map (↑e) p)) : ↑(coe_fn (symm (of_submodule e p)) x) = coe_fn (symm e) ↑x :=
  rfl

/-- Product of linear equivalences; the maps come from `equiv.prod_congr`. -/
protected def prod {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} {M₄ : Type z} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [add_comm_monoid M₄] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂} {semimodule_M₃ : semimodule R M₃} {semimodule_M₄ : semimodule R M₄} (e₁ : linear_equiv R M M₂) (e₂ : linear_equiv R M₃ M₄) : linear_equiv R (M × M₃) (M₂ × M₄) :=
  mk (equiv.to_fun (equiv.prod_congr (to_equiv e₁) (to_equiv e₂))) sorry sorry
    (equiv.inv_fun (equiv.prod_congr (to_equiv e₁) (to_equiv e₂))) sorry sorry

theorem prod_symm {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} {M₄ : Type z} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [add_comm_monoid M₄] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂} {semimodule_M₃ : semimodule R M₃} {semimodule_M₄ : semimodule R M₄} (e₁ : linear_equiv R M M₂) (e₂ : linear_equiv R M₃ M₄) : symm (linear_equiv.prod e₁ e₂) = linear_equiv.prod (symm e₁) (symm e₂) :=
  rfl

@[simp] theorem prod_apply {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} {M₄ : Type z} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [add_comm_monoid M₄] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂} {semimodule_M₃ : semimodule R M₃} {semimodule_M₄ : semimodule R M₄} (e₁ : linear_equiv R M M₂) (e₂ : linear_equiv R M₃ M₄) (p : M × M₃) : coe_fn (linear_equiv.prod e₁ e₂) p = (coe_fn e₁ (prod.fst p), coe_fn e₂ (prod.snd p)) :=
  rfl

@[simp] theorem coe_prod {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} {M₄ : Type z} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [add_comm_monoid M₄] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂} {semimodule_M₃ : semimodule R M₃} {semimodule_M₄ : semimodule R M₄} (e₁ : linear_equiv R M M₂) (e₂ : linear_equiv R M₃ M₄) : ↑(linear_equiv.prod e₁ e₂) = linear_map.prod_map ↑e₁ ↑e₂ :=
  rfl

/-- Linear equivalence between a curried and uncurried function.
  Differs from `tensor_product.curry`. -/
protected def uncurry (R : Type u) (V : Type v') (V₂ : Type w') [semiring R] : linear_equiv R (V → V₂ → R) (V × V₂ → R) :=
  mk (equiv.to_fun (equiv.arrow_arrow_equiv_prod_arrow V V₂ R)) sorry sorry
    (equiv.inv_fun (equiv.arrow_arrow_equiv_prod_arrow V V₂ R)) sorry sorry

@[simp] theorem coe_uncurry (R : Type u) (V : Type v') (V₂ : Type w') [semiring R] : ⇑(linear_equiv.uncurry R V V₂) = function.uncurry :=
  rfl

@[simp] theorem coe_uncurry_symm (R : Type u) (V : Type v') (V₂ : Type w') [semiring R] : ⇑(symm (linear_equiv.uncurry R V V₂)) = function.curry :=
  rfl

/-- Linear equivalence between two equal submodules. -/
def of_eq {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] {semimodule_M : semimodule R M} (p : submodule R M) (q : submodule R M) (h : p = q) : linear_equiv R ↥p ↥q :=
  mk (equiv.to_fun (equiv.set.of_eq sorry)) sorry sorry (equiv.inv_fun (equiv.set.of_eq sorry)) sorry sorry

@[simp] theorem coe_of_eq_apply {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] {semimodule_M : semimodule R M} {p : submodule R M} {q : submodule R M} (h : p = q) (x : ↥p) : ↑(coe_fn (of_eq p q h) x) = ↑x :=
  rfl

@[simp] theorem of_eq_symm {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] {semimodule_M : semimodule R M} {p : submodule R M} {q : submodule R M} (h : p = q) : symm (of_eq p q h) = of_eq q p (Eq.symm h) :=
  rfl

/-- A linear equivalence which maps a submodule of one module onto another, restricts to a linear
equivalence of the two submodules. -/
def of_submodules {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂} (e : linear_equiv R M M₂) (p : submodule R M) (q : submodule R M₂) (h : submodule.map (↑e) p = q) : linear_equiv R ↥p ↥q :=
  trans (of_submodule e p) (of_eq (submodule.map (↑e) p) q h)

@[simp] theorem of_submodules_apply {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂} (e : linear_equiv R M M₂) {p : submodule R M} {q : submodule R M₂} (h : submodule.map (↑e) p = q) (x : ↥p) : ↑(coe_fn (of_submodules e p q h) x) = coe_fn e ↑x :=
  rfl

@[simp] theorem of_submodules_symm_apply {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂} (e : linear_equiv R M M₂) {p : submodule R M} {q : submodule R M₂} (h : submodule.map (↑e) p = q) (x : ↥q) : ↑(coe_fn (symm (of_submodules e p q h)) x) = coe_fn (symm e) ↑x :=
  rfl

/-- The top submodule of `M` is linearly equivalent to `M`. -/
def of_top {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] {semimodule_M : semimodule R M} (p : submodule R M) (h : p = ⊤) : linear_equiv R (↥p) M :=
  mk (linear_map.to_fun (submodule.subtype p)) sorry sorry (fun (x : M) => { val := x, property := sorry }) sorry sorry

@[simp] theorem of_top_apply {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] {semimodule_M : semimodule R M} (p : submodule R M) {h : p = ⊤} (x : ↥p) : coe_fn (of_top p h) x = ↑x :=
  rfl

@[simp] theorem coe_of_top_symm_apply {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] {semimodule_M : semimodule R M} (p : submodule R M) {h : p = ⊤} (x : M) : ↑(coe_fn (symm (of_top p h)) x) = x :=
  rfl

theorem of_top_symm_apply {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] {semimodule_M : semimodule R M} (p : submodule R M) {h : p = ⊤} (x : M) : coe_fn (symm (of_top p h)) x = { val := x, property := Eq.symm h ▸ trivial } :=
  rfl

/-- If a linear map has an inverse, it is a linear equivalence. -/
def of_linear {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂} (f : linear_map R M M₂) (g : linear_map R M₂ M) (h₁ : linear_map.comp f g = linear_map.id) (h₂ : linear_map.comp g f = linear_map.id) : linear_equiv R M M₂ :=
  mk (linear_map.to_fun f) (linear_map.map_add' f) (linear_map.map_smul' f) ⇑g sorry sorry

@[simp] theorem of_linear_apply {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂} (f : linear_map R M M₂) (g : linear_map R M₂ M) {h₁ : linear_map.comp f g = linear_map.id} {h₂ : linear_map.comp g f = linear_map.id} (x : M) : coe_fn (of_linear f g h₁ h₂) x = coe_fn f x :=
  rfl

@[simp] theorem of_linear_symm_apply {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂} (f : linear_map R M M₂) (g : linear_map R M₂ M) {h₁ : linear_map.comp f g = linear_map.id} {h₂ : linear_map.comp g f = linear_map.id} (x : M₂) : coe_fn (symm (of_linear f g h₁ h₂)) x = coe_fn g x :=
  rfl

@[simp] protected theorem range {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂} (e : linear_equiv R M M₂) : linear_map.range ↑e = ⊤ :=
  iff.mpr linear_map.range_eq_top (equiv.surjective (to_equiv e))

theorem eq_bot_of_equiv {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] {semimodule_M : semimodule R M} (p : submodule R M) [semimodule R M₂] (e : linear_equiv R ↥p ↥⊥) : p = ⊥ := sorry

@[simp] protected theorem ker {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂} (e : linear_equiv R M M₂) : linear_map.ker ↑e = ⊥ :=
  linear_map.ker_eq_bot_of_injective (equiv.injective (to_equiv e))

@[simp] theorem map_neg {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_group M] [add_comm_group M₂] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂} (e : linear_equiv R M M₂) (a : M) : coe_fn e (-a) = -coe_fn e a :=
  linear_map.map_neg (to_linear_map e) a

@[simp] theorem map_sub {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_group M] [add_comm_group M₂] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂} (e : linear_equiv R M M₂) (a : M) (b : M) : coe_fn e (a - b) = coe_fn e a - coe_fn e b :=
  linear_map.map_sub (to_linear_map e) a b

/-- Equivalence given by a block lower diagonal matrix. `e₁` and `e₂` are diagonal square blocks,
  and `f` is a rectangular block below the diagonal. -/
protected def skew_prod {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} {M₄ : Type z} [semiring R] [add_comm_group M] [add_comm_group M₂] [add_comm_group M₃] [add_comm_group M₄] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂} {semimodule_M₃ : semimodule R M₃} {semimodule_M₄ : semimodule R M₄} (e₁ : linear_equiv R M M₂) (e₂ : linear_equiv R M₃ M₄) (f : linear_map R M M₄) : linear_equiv R (M × M₃) (M₂ × M₄) :=
  mk
    (linear_map.to_fun
      (linear_map.prod (linear_map.comp (↑e₁) (linear_map.fst R M M₃))
        (linear_map.comp (↑e₂) (linear_map.snd R M M₃) + linear_map.comp f (linear_map.fst R M M₃))))
    sorry sorry
    (fun (p : M₂ × M₄) =>
      (coe_fn (symm e₁) (prod.fst p), coe_fn (symm e₂) (prod.snd p - coe_fn f (coe_fn (symm e₁) (prod.fst p)))))
    sorry sorry

@[simp] theorem skew_prod_apply {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} {M₄ : Type z} [semiring R] [add_comm_group M] [add_comm_group M₂] [add_comm_group M₃] [add_comm_group M₄] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂} {semimodule_M₃ : semimodule R M₃} {semimodule_M₄ : semimodule R M₄} (e₁ : linear_equiv R M M₂) (e₂ : linear_equiv R M₃ M₄) (f : linear_map R M M₄) (x : M × M₃) : coe_fn (linear_equiv.skew_prod e₁ e₂ f) x = (coe_fn e₁ (prod.fst x), coe_fn e₂ (prod.snd x) + coe_fn f (prod.fst x)) :=
  rfl

@[simp] theorem skew_prod_symm_apply {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} {M₄ : Type z} [semiring R] [add_comm_group M] [add_comm_group M₂] [add_comm_group M₃] [add_comm_group M₄] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂} {semimodule_M₃ : semimodule R M₃} {semimodule_M₄ : semimodule R M₄} (e₁ : linear_equiv R M M₂) (e₂ : linear_equiv R M₃ M₄) (f : linear_map R M M₄) (x : M₂ × M₄) : coe_fn (symm (linear_equiv.skew_prod e₁ e₂ f)) x =
  (coe_fn (symm e₁) (prod.fst x), coe_fn (symm e₂) (prod.snd x - coe_fn f (coe_fn (symm e₁) (prod.fst x)))) :=
  rfl

/-- `x ↦ -x` as a `linear_equiv` -/
def neg (R : Type u) {M : Type v} [semiring R] [add_comm_group M] [semimodule R M] : linear_equiv R M M :=
  mk (equiv.to_fun (equiv.neg M)) sorry sorry (equiv.inv_fun (equiv.neg M)) sorry sorry

@[simp] theorem coe_neg {R : Type u} {M : Type v} [semiring R] [add_comm_group M] [semimodule R M] : ⇑(neg R) = -id :=
  rfl

theorem neg_apply {R : Type u} {M : Type v} [semiring R] [add_comm_group M] [semimodule R M] (x : M) : coe_fn (neg R) x = -x := sorry

@[simp] theorem symm_neg {R : Type u} {M : Type v} [semiring R] [add_comm_group M] [semimodule R M] : symm (neg R) = neg R :=
  rfl

/-- An `injective` linear map `f : M →ₗ[R] M₂` defines a linear equivalence
between `M` and `f.range`. -/
def of_injective {R : Type u} {M : Type v} {M₂ : Type w} [ring R] [add_comm_group M] [add_comm_group M₂] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂} (f : linear_map R M M₂) (h : linear_map.ker f = ⊥) : linear_equiv R M ↥(linear_map.range f) :=
  mk (equiv.to_fun (equiv.trans (equiv.set.range ⇑f sorry) (equiv.set.of_eq sorry))) sorry sorry
    (equiv.inv_fun (equiv.trans (equiv.set.range ⇑f sorry) (equiv.set.of_eq sorry))) sorry sorry

@[simp] theorem of_injective_apply {R : Type u} {M : Type v} {M₂ : Type w} [ring R] [add_comm_group M] [add_comm_group M₂] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂} (f : linear_map R M M₂) {h : linear_map.ker f = ⊥} (x : M) : ↑(coe_fn (of_injective f h) x) = coe_fn f x :=
  rfl

/-- A bijective linear map is a linear equivalence. Here, bijectivity is described by saying that
the kernel of `f` is `{0}` and the range is the universal set. -/
def of_bijective {R : Type u} {M : Type v} {M₂ : Type w} [ring R] [add_comm_group M] [add_comm_group M₂] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂} (f : linear_map R M M₂) (hf₁ : linear_map.ker f = ⊥) (hf₂ : linear_map.range f = ⊤) : linear_equiv R M M₂ :=
  trans (of_injective f hf₁) (of_top (linear_map.range f) hf₂)

@[simp] theorem of_bijective_apply {R : Type u} {M : Type v} {M₂ : Type w} [ring R] [add_comm_group M] [add_comm_group M₂] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂} (f : linear_map R M M₂) {hf₁ : linear_map.ker f = ⊥} {hf₂ : linear_map.range f = ⊤} (x : M) : coe_fn (of_bijective f hf₁ hf₂) x = coe_fn f x :=
  rfl

/-- Multiplying by a unit `a` of the ring `R` is a linear equivalence. -/
def smul_of_unit {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [semimodule R M] (a : units R) : linear_equiv R M M :=
  of_linear (↑a • 1) (↑(a⁻¹) • 1) sorry sorry

/-- A linear isomorphism between the domains and codomains of two spaces of linear maps gives a
linear isomorphism between the two function spaces. -/
def arrow_congr {R : Type u_1} {M₁ : Type u_2} {M₂ : Type u_3} {M₂₁ : Type u_4} {M₂₂ : Type u_5} [comm_ring R] [add_comm_group M₁] [add_comm_group M₂] [add_comm_group M₂₁] [add_comm_group M₂₂] [module R M₁] [module R M₂] [module R M₂₁] [module R M₂₂] (e₁ : linear_equiv R M₁ M₂) (e₂ : linear_equiv R M₂₁ M₂₂) : linear_equiv R (linear_map R M₁ M₂₁) (linear_map R M₂ M₂₂) :=
  mk (fun (f : linear_map R M₁ M₂₁) => linear_map.comp (↑e₂) (linear_map.comp f ↑(symm e₁))) sorry sorry
    (fun (f : linear_map R M₂ M₂₂) => linear_map.comp (↑(symm e₂)) (linear_map.comp f ↑e₁)) sorry sorry

@[simp] theorem arrow_congr_apply {R : Type u_1} {M₁ : Type u_2} {M₂ : Type u_3} {M₂₁ : Type u_4} {M₂₂ : Type u_5} [comm_ring R] [add_comm_group M₁] [add_comm_group M₂] [add_comm_group M₂₁] [add_comm_group M₂₂] [module R M₁] [module R M₂] [module R M₂₁] [module R M₂₂] (e₁ : linear_equiv R M₁ M₂) (e₂ : linear_equiv R M₂₁ M₂₂) (f : linear_map R M₁ M₂₁) (x : M₂) : coe_fn (coe_fn (arrow_congr e₁ e₂) f) x = coe_fn e₂ (coe_fn f (coe_fn (symm e₁) x)) :=
  rfl

@[simp] theorem arrow_congr_symm_apply {R : Type u_1} {M₁ : Type u_2} {M₂ : Type u_3} {M₂₁ : Type u_4} {M₂₂ : Type u_5} [comm_ring R] [add_comm_group M₁] [add_comm_group M₂] [add_comm_group M₂₁] [add_comm_group M₂₂] [module R M₁] [module R M₂] [module R M₂₁] [module R M₂₂] (e₁ : linear_equiv R M₁ M₂) (e₂ : linear_equiv R M₂₁ M₂₂) (f : linear_map R M₂ M₂₂) (x : M₁) : coe_fn (coe_fn (symm (arrow_congr e₁ e₂)) f) x = coe_fn (symm e₂) (coe_fn f (coe_fn e₁ x)) :=
  rfl

theorem arrow_congr_comp {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} [comm_ring R] [add_comm_group M] [add_comm_group M₂] [add_comm_group M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] {N : Type u_1} {N₂ : Type u_2} {N₃ : Type u_3} [add_comm_group N] [add_comm_group N₂] [add_comm_group N₃] [module R N] [module R N₂] [module R N₃] (e₁ : linear_equiv R M N) (e₂ : linear_equiv R M₂ N₂) (e₃ : linear_equiv R M₃ N₃) (f : linear_map R M M₂) (g : linear_map R M₂ M₃) : coe_fn (arrow_congr e₁ e₃) (linear_map.comp g f) =
  linear_map.comp (coe_fn (arrow_congr e₂ e₃) g) (coe_fn (arrow_congr e₁ e₂) f) := sorry

theorem arrow_congr_trans {R : Type u} [comm_ring R] {M₁ : Type u_1} {M₂ : Type u_2} {M₃ : Type u_3} {N₁ : Type u_4} {N₂ : Type u_5} {N₃ : Type u_6} [add_comm_group M₁] [module R M₁] [add_comm_group M₂] [module R M₂] [add_comm_group M₃] [module R M₃] [add_comm_group N₁] [module R N₁] [add_comm_group N₂] [module R N₂] [add_comm_group N₃] [module R N₃] (e₁ : linear_equiv R M₁ M₂) (e₂ : linear_equiv R N₁ N₂) (e₃ : linear_equiv R M₂ M₃) (e₄ : linear_equiv R N₂ N₃) : trans (arrow_congr e₁ e₂) (arrow_congr e₃ e₄) = arrow_congr (trans e₁ e₃) (trans e₂ e₄) :=
  rfl

/-- If `M₂` and `M₃` are linearly isomorphic then the two spaces of linear maps from `M` into `M₂`
and `M` into `M₃` are linearly isomorphic. -/
def congr_right {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} [comm_ring R] [add_comm_group M] [add_comm_group M₂] [add_comm_group M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (f : linear_equiv R M₂ M₃) : linear_equiv R (linear_map R M M₂) (linear_map R M M₃) :=
  arrow_congr (refl R M) f

/-- If `M` and `M₂` are linearly isomorphic then the two spaces of linear maps from `M` and `M₂` to
themselves are linearly isomorphic. -/
def conj {R : Type u} {M : Type v} {M₂ : Type w} [comm_ring R] [add_comm_group M] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] (e : linear_equiv R M M₂) : linear_equiv R (module.End R M) (module.End R M₂) :=
  arrow_congr e e

theorem conj_apply {R : Type u} {M : Type v} {M₂ : Type w} [comm_ring R] [add_comm_group M] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] (e : linear_equiv R M M₂) (f : module.End R M) : coe_fn (conj e) f = linear_map.comp (linear_map.comp (↑e) f) ↑(symm e) :=
  rfl

theorem symm_conj_apply {R : Type u} {M : Type v} {M₂ : Type w} [comm_ring R] [add_comm_group M] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] (e : linear_equiv R M M₂) (f : module.End R M₂) : coe_fn (conj (symm e)) f = linear_map.comp (linear_map.comp (↑(symm e)) f) ↑e :=
  rfl

theorem conj_comp {R : Type u} {M : Type v} {M₂ : Type w} [comm_ring R] [add_comm_group M] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] (e : linear_equiv R M M₂) (f : module.End R M) (g : module.End R M) : coe_fn (conj e) (linear_map.comp g f) = linear_map.comp (coe_fn (conj e) g) (coe_fn (conj e) f) :=
  arrow_congr_comp e e e f g

theorem conj_trans {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Type y} [comm_ring R] [add_comm_group M] [add_comm_group M₂] [add_comm_group M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] (e₁ : linear_equiv R M M₂) (e₂ : linear_equiv R M₂ M₃) : trans (conj e₁) (conj e₂) = conj (trans e₁ e₂) :=
  ext fun (f : module.End R M) => linear_map.ext fun (x : M₃) => Eq.refl (coe_fn (coe_fn (trans (conj e₁) (conj e₂)) f) x)

@[simp] theorem conj_id {R : Type u} {M : Type v} {M₂ : Type w} [comm_ring R] [add_comm_group M] [add_comm_group M₂] [semimodule R M] [semimodule R M₂] (e : linear_equiv R M M₂) : coe_fn (conj e) linear_map.id = linear_map.id := sorry

/-- Multiplying by a nonzero element `a` of the field `K` is a linear equivalence. -/
def smul_of_ne_zero (K : Type u') (M : Type v) [field K] [add_comm_group M] [module K M] (a : K) (ha : a ≠ 0) : linear_equiv K M M :=
  smul_of_unit (units.mk0 a ha)

theorem ker_to_span_singleton (K : Type u') (M : Type v) [field K] [add_comm_group M] [module K M] {x : M} (h : x ≠ 0) : linear_map.ker (linear_map.to_span_singleton K M x) = ⊥ := sorry

/-- Given a nonzero element `x` of a vector space `M` over a field `K`, the natural
    map from `K` to the span of `x`, with invertibility check to consider it as an
    isomorphism.-/
def to_span_nonzero_singleton (K : Type u') (M : Type v) [field K] [add_comm_group M] [module K M] (x : M) (h : x ≠ 0) : linear_equiv K K ↥(submodule.span K (singleton x)) :=
  trans (of_injective (linear_map.to_span_singleton K M x) (ker_to_span_singleton K M h))
    (of_eq (linear_map.range (linear_map.to_span_singleton K M x)) (submodule.span K (singleton x)) sorry)

theorem to_span_nonzero_singleton_one (K : Type u') (M : Type v) [field K] [add_comm_group M] [module K M] (x : M) (h : x ≠ 0) : coe_fn (to_span_nonzero_singleton K M x h) 1 = { val := x, property := submodule.mem_span_singleton_self x } := sorry

/-- Given a nonzero element `x` of a vector space `M` over a field `K`, the natural map
    from the span of `x` to `K`.-/
def coord (K : Type u') (M : Type v) [field K] [add_comm_group M] [module K M] (x : M) (h : x ≠ 0) : linear_equiv K (↥(submodule.span K (singleton x))) K :=
  symm (to_span_nonzero_singleton K M x h)

theorem coord_self (K : Type u') (M : Type v) [field K] [add_comm_group M] [module K M] (x : M) (h : x ≠ 0) : coe_fn (coord K M x h) { val := x, property := submodule.mem_span_singleton_self x } = 1 := sorry

end linear_equiv


namespace submodule


/-- If `s ≤ t`, then we can view `s` as a submodule of `t` by taking the comap
of `t.subtype`. -/
def comap_subtype_equiv_of_le {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {p : submodule R M} {q : submodule R M} (hpq : p ≤ q) : linear_equiv R ↥(comap (submodule.subtype q) p) ↥p :=
  linear_equiv.mk (fun (x : ↥(comap (submodule.subtype q) p)) => { val := ↑x, property := sorry }) sorry sorry
    (fun (x : ↥p) => { val := { val := ↑x, property := sorry }, property := sorry }) sorry sorry

/-- If `p = ⊥`, then `M / p ≃ₗ[R] M`. -/
def quot_equiv_of_eq_bot {R : Type u} {M : Type v} [ring R] [add_comm_group M] [module R M] (p : submodule R M) (hp : p = ⊥) : linear_equiv R (quotient p) M :=
  linear_equiv.of_linear (liftq p linear_map.id sorry) (mkq p) sorry sorry

@[simp] theorem quot_equiv_of_eq_bot_apply_mk {R : Type u} {M : Type v} [ring R] [add_comm_group M] [module R M] (p : submodule R M) (hp : p = ⊥) (x : M) : coe_fn (quot_equiv_of_eq_bot p hp) (quotient.mk x) = x :=
  rfl

@[simp] theorem quot_equiv_of_eq_bot_symm_apply {R : Type u} {M : Type v} [ring R] [add_comm_group M] [module R M] (p : submodule R M) (hp : p = ⊥) (x : M) : coe_fn (linear_equiv.symm (quot_equiv_of_eq_bot p hp)) x = quotient.mk x :=
  rfl

@[simp] theorem coe_quot_equiv_of_eq_bot_symm {R : Type u} {M : Type v} [ring R] [add_comm_group M] [module R M] (p : submodule R M) (hp : p = ⊥) : ↑(linear_equiv.symm (quot_equiv_of_eq_bot p hp)) = mkq p :=
  rfl

/-- Quotienting by equal submodules gives linearly equivalent quotients. -/
def quot_equiv_of_eq {R : Type u} {M : Type v} [ring R] [add_comm_group M] [module R M] (p : submodule R M) (q : submodule R M) (h : p = q) : linear_equiv R (quotient p) (quotient q) :=
  linear_equiv.mk (equiv.to_fun (quotient.congr (equiv.refl M) sorry)) sorry sorry
    (equiv.inv_fun (quotient.congr (equiv.refl M) sorry)) sorry sorry

end submodule


namespace submodule


@[simp] theorem mem_map_equiv {R : Type u} {M : Type v} {M₂ : Type w} [comm_ring R] [add_comm_group M] [add_comm_group M₂] [module R M] [module R M₂] (p : submodule R M) {e : linear_equiv R M M₂} {x : M₂} : x ∈ map (↑e) p ↔ coe_fn (linear_equiv.symm e) x ∈ p := sorry

theorem comap_le_comap_smul {R : Type u} {M : Type v} {M₂ : Type w} [comm_ring R] [add_comm_group M] [add_comm_group M₂] [module R M] [module R M₂] (q : submodule R M₂) (f : linear_map R M M₂) (c : R) : comap f q ≤ comap (c • f) q :=
  eq.mpr (id (Eq._oldrec (Eq.refl (comap f q ≤ comap (c • f) q)) (propext le_def')))
    fun (m : M) (h : m ∈ comap f q) => id (id (fun (h : coe_fn f m ∈ q) => smul_mem q c h) h)

theorem inf_comap_le_comap_add {R : Type u} {M : Type v} {M₂ : Type w} [comm_ring R] [add_comm_group M] [add_comm_group M₂] [module R M] [module R M₂] (q : submodule R M₂) (f₁ : linear_map R M M₂) (f₂ : linear_map R M M₂) : comap f₁ q ⊓ comap f₂ q ≤ comap (f₁ + f₂) q :=
  eq.mpr (id (Eq._oldrec (Eq.refl (comap f₁ q ⊓ comap f₂ q ≤ comap (f₁ + f₂) q)) (propext le_def')))
    fun (m : M) (h : m ∈ comap f₁ q ⊓ comap f₂ q) =>
      id (id (fun (h : coe_fn f₁ m ∈ q ∧ coe_fn f₂ m ∈ q) => add_mem q (and.left h) (and.right h)) h)

/-- Given modules `M`, `M₂` over a commutative ring, together with submodules `p ⊆ M`, `q ⊆ M₂`, the
set of maps $\\{f ∈ Hom(M, M₂) | f(p) ⊆ q \\}$ is a submodule of `Hom(M, M₂)`. -/
def compatible_maps {R : Type u} {M : Type v} {M₂ : Type w} [comm_ring R] [add_comm_group M] [add_comm_group M₂] [module R M] [module R M₂] (p : submodule R M) (q : submodule R M₂) : submodule R (linear_map R M M₂) :=
  mk (set_of fun (f : linear_map R M M₂) => p ≤ comap f q) sorry sorry sorry

/-- Given modules `M`, `M₂` over a commutative ring, together with submodules `p ⊆ M`, `q ⊆ M₂`, the
natural map $\\{f ∈ Hom(M, M₂) | f(p) ⊆ q \\} \to Hom(M/p, M₂/q)$ is linear. -/
def mapq_linear {R : Type u} {M : Type v} {M₂ : Type w} [comm_ring R] [add_comm_group M] [add_comm_group M₂] [module R M] [module R M₂] (p : submodule R M) (q : submodule R M₂) : linear_map R (↥(compatible_maps p q)) (linear_map R (quotient p) (quotient q)) :=
  linear_map.mk (fun (f : ↥(compatible_maps p q)) => mapq p q (subtype.val f) sorry) sorry sorry

end submodule


namespace equiv


/-- An equivalence whose underlying function is linear is a linear equivalence. -/
def to_linear_equiv {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [semimodule R M] [add_comm_monoid M₂] [semimodule R M₂] (e : M ≃ M₂) (h : is_linear_map R ⇑e) : linear_equiv R M M₂ :=
  linear_equiv.mk (to_fun e) sorry sorry (inv_fun e) (left_inv e) (right_inv e)

end equiv


namespace add_equiv


/-- An additive equivalence whose underlying function preserves `smul` is a linear equivalence. -/
def to_linear_equiv {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [semimodule R M] [add_comm_monoid M₂] [semimodule R M₂] (e : M ≃+ M₂) (h : ∀ (c : R) (x : M), coe_fn e (c • x) = c • coe_fn e x) : linear_equiv R M M₂ :=
  linear_equiv.mk (to_fun e) sorry h (inv_fun e) sorry sorry

@[simp] theorem coe_to_linear_equiv {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [semimodule R M] [add_comm_monoid M₂] [semimodule R M₂] (e : M ≃+ M₂) (h : ∀ (c : R) (x : M), coe_fn e (c • x) = c • coe_fn e x) : ⇑(to_linear_equiv e h) = ⇑e :=
  rfl

@[simp] theorem coe_to_linear_equiv_symm {R : Type u} {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M] [semimodule R M] [add_comm_monoid M₂] [semimodule R M₂] (e : M ≃+ M₂) (h : ∀ (c : R) (x : M), coe_fn e (c • x) = c • coe_fn e x) : ⇑(linear_equiv.symm (to_linear_equiv e h)) = ⇑(symm e) :=
  rfl

end add_equiv


namespace linear_map


/-- The first isomorphism law for modules. The quotient of `M` by the kernel of `f` is linearly
equivalent to the range of `f`. -/
def quot_ker_equiv_range {R : Type u} {M : Type v} {M₂ : Type w} [ring R] [add_comm_group M] [add_comm_group M₂] [module R M] [module R M₂] (f : linear_map R M M₂) : linear_equiv R (submodule.quotient (ker f)) ↥(range f) :=
  linear_equiv.trans (linear_equiv.of_injective (submodule.liftq (ker f) f sorry) sorry)
    (linear_equiv.of_eq (range (submodule.liftq (ker f) f sorry)) (range f) sorry)

@[simp] theorem quot_ker_equiv_range_apply_mk {R : Type u} {M : Type v} {M₂ : Type w} [ring R] [add_comm_group M] [add_comm_group M₂] [module R M] [module R M₂] (f : linear_map R M M₂) (x : M) : ↑(coe_fn (quot_ker_equiv_range f) (submodule.quotient.mk x)) = coe_fn f x :=
  rfl

@[simp] theorem quot_ker_equiv_range_symm_apply_image {R : Type u} {M : Type v} {M₂ : Type w} [ring R] [add_comm_group M] [add_comm_group M₂] [module R M] [module R M₂] (f : linear_map R M M₂) (x : M) (h : coe_fn f x ∈ range f) : coe_fn (linear_equiv.symm (quot_ker_equiv_range f)) { val := coe_fn f x, property := h } =
  coe_fn (submodule.mkq (ker f)) x :=
  linear_equiv.symm_apply_apply (quot_ker_equiv_range f) (coe_fn (submodule.mkq (ker f)) x)

/--
Canonical linear map from the quotient `p/(p ∩ p')` to `(p+p')/p'`, mapping `x + (p ∩ p')`
to `x + p'`, where `p` and `p'` are submodules of an ambient module.
-/
def quotient_inf_to_sup_quotient {R : Type u} {M : Type v} [ring R] [add_comm_group M] [module R M] (p : submodule R M) (p' : submodule R M) : linear_map R (submodule.quotient (submodule.comap (submodule.subtype p) (p ⊓ p')))
  (submodule.quotient (submodule.comap (submodule.subtype (p ⊔ p')) p')) :=
  submodule.liftq (submodule.comap (submodule.subtype p) (p ⊓ p'))
    (comp (submodule.mkq (submodule.comap (submodule.subtype (p ⊔ p')) p')) (submodule.of_le sorry)) sorry

/--
Second Isomorphism Law : the canonical map from `p/(p ∩ p')` to `(p+p')/p'` as a linear isomorphism.
-/
def quotient_inf_equiv_sup_quotient {R : Type u} {M : Type v} [ring R] [add_comm_group M] [module R M] (p : submodule R M) (p' : submodule R M) : linear_equiv R (submodule.quotient (submodule.comap (submodule.subtype p) (p ⊓ p')))
  (submodule.quotient (submodule.comap (submodule.subtype (p ⊔ p')) p')) :=
  linear_equiv.of_bijective (quotient_inf_to_sup_quotient p p') sorry sorry

@[simp] theorem coe_quotient_inf_to_sup_quotient {R : Type u} {M : Type v} [ring R] [add_comm_group M] [module R M] (p : submodule R M) (p' : submodule R M) : ⇑(quotient_inf_to_sup_quotient p p') = ⇑(quotient_inf_equiv_sup_quotient p p') :=
  rfl

@[simp] theorem quotient_inf_equiv_sup_quotient_apply_mk {R : Type u} {M : Type v} [ring R] [add_comm_group M] [module R M] (p : submodule R M) (p' : submodule R M) (x : ↥p) : coe_fn (quotient_inf_equiv_sup_quotient p p') (submodule.quotient.mk x) =
  submodule.quotient.mk (coe_fn (submodule.of_le le_sup_left) x) :=
  rfl

theorem quotient_inf_equiv_sup_quotient_symm_apply_left {R : Type u} {M : Type v} [ring R] [add_comm_group M] [module R M] (p : submodule R M) (p' : submodule R M) (x : ↥(p ⊔ p')) (hx : ↑x ∈ p) : coe_fn (linear_equiv.symm (quotient_inf_equiv_sup_quotient p p')) (submodule.quotient.mk x) =
  submodule.quotient.mk { val := ↑x, property := hx } := sorry

@[simp] theorem quotient_inf_equiv_sup_quotient_symm_apply_eq_zero_iff {R : Type u} {M : Type v} [ring R] [add_comm_group M] [module R M] {p : submodule R M} {p' : submodule R M} {x : ↥(p ⊔ p')} : coe_fn (linear_equiv.symm (quotient_inf_equiv_sup_quotient p p')) (submodule.quotient.mk x) = 0 ↔ ↑x ∈ p' := sorry

theorem quotient_inf_equiv_sup_quotient_symm_apply_right {R : Type u} {M : Type v} [ring R] [add_comm_group M] [module R M] (p : submodule R M) (p' : submodule R M) {x : ↥(p ⊔ p')} (hx : ↑x ∈ p') : coe_fn (linear_equiv.symm (quotient_inf_equiv_sup_quotient p p')) (submodule.quotient.mk x) = 0 :=
  iff.mpr quotient_inf_equiv_sup_quotient_symm_apply_eq_zero_iff hx

theorem is_linear_map_prod_iso {R : Type u_1} {M : Type u_2} {M₂ : Type u_3} {M₃ : Type u_4} [comm_semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_group M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] : is_linear_map R fun (p : linear_map R M M₂ × linear_map R M M₃) => prod (prod.fst p) (prod.snd p) :=
  is_linear_map.mk (fun (u v : linear_map R M M₂ × linear_map R M M₃) => rfl)
    fun (c : R) (u : linear_map R M M₂ × linear_map R M M₃) => rfl

/-- `pi` construction for linear functions. From a family of linear functions it produces a linear
function into a family of modules. -/
def pi {R : Type u} {M₂ : Type w} {ι : Type x} [semiring R] [add_comm_monoid M₂] [semimodule R M₂] {φ : ι → Type i} [(i : ι) → add_comm_monoid (φ i)] [(i : ι) → semimodule R (φ i)] (f : (i : ι) → linear_map R M₂ (φ i)) : linear_map R M₂ ((i : ι) → φ i) :=
  mk (fun (c : M₂) (i : ι) => coe_fn (f i) c) sorry sorry

@[simp] theorem pi_apply {R : Type u} {M₂ : Type w} {ι : Type x} [semiring R] [add_comm_monoid M₂] [semimodule R M₂] {φ : ι → Type i} [(i : ι) → add_comm_monoid (φ i)] [(i : ι) → semimodule R (φ i)] (f : (i : ι) → linear_map R M₂ (φ i)) (c : M₂) (i : ι) : coe_fn (pi f) c i = coe_fn (f i) c :=
  rfl

theorem ker_pi {R : Type u} {M₂ : Type w} {ι : Type x} [semiring R] [add_comm_monoid M₂] [semimodule R M₂] {φ : ι → Type i} [(i : ι) → add_comm_monoid (φ i)] [(i : ι) → semimodule R (φ i)] (f : (i : ι) → linear_map R M₂ (φ i)) : ker (pi f) = infi fun (i : ι) => ker (f i) := sorry

theorem pi_eq_zero {R : Type u} {M₂ : Type w} {ι : Type x} [semiring R] [add_comm_monoid M₂] [semimodule R M₂] {φ : ι → Type i} [(i : ι) → add_comm_monoid (φ i)] [(i : ι) → semimodule R (φ i)] (f : (i : ι) → linear_map R M₂ (φ i)) : pi f = 0 ↔ ∀ (i : ι), f i = 0 := sorry

theorem pi_zero {R : Type u} {M₂ : Type w} {ι : Type x} [semiring R] [add_comm_monoid M₂] [semimodule R M₂] {φ : ι → Type i} [(i : ι) → add_comm_monoid (φ i)] [(i : ι) → semimodule R (φ i)] : (pi fun (i : ι) => 0) = 0 :=
  ext fun (x : M₂) => funext fun (x_1 : ι) => Eq.refl (coe_fn (pi fun (i : ι) => 0) x x_1)

theorem pi_comp {R : Type u} {M₂ : Type w} {M₃ : Type y} {ι : Type x} [semiring R] [add_comm_monoid M₂] [semimodule R M₂] [add_comm_monoid M₃] [semimodule R M₃] {φ : ι → Type i} [(i : ι) → add_comm_monoid (φ i)] [(i : ι) → semimodule R (φ i)] (f : (i : ι) → linear_map R M₂ (φ i)) (g : linear_map R M₃ M₂) : comp (pi f) g = pi fun (i : ι) => comp (f i) g :=
  rfl

/-- The projections from a family of modules are linear maps. -/
def proj {R : Type u} {ι : Type x} [semiring R] {φ : ι → Type i} [(i : ι) → add_comm_monoid (φ i)] [(i : ι) → semimodule R (φ i)] (i : ι) : linear_map R ((i : ι) → φ i) (φ i) :=
  mk (fun (a : (i : ι) → φ i) => a i) sorry sorry

@[simp] theorem proj_apply {R : Type u} {ι : Type x} [semiring R] {φ : ι → Type i} [(i : ι) → add_comm_monoid (φ i)] [(i : ι) → semimodule R (φ i)] (i : ι) (b : (i : ι) → φ i) : coe_fn (proj i) b = b i :=
  rfl

theorem proj_pi {R : Type u} {M₂ : Type w} {ι : Type x} [semiring R] [add_comm_monoid M₂] [semimodule R M₂] {φ : ι → Type i} [(i : ι) → add_comm_monoid (φ i)] [(i : ι) → semimodule R (φ i)] (f : (i : ι) → linear_map R M₂ (φ i)) (i : ι) : comp (proj i) (pi f) = f i :=
  ext fun (c : M₂) => rfl

theorem infi_ker_proj {R : Type u} {ι : Type x} [semiring R] {φ : ι → Type i} [(i : ι) → add_comm_monoid (φ i)] [(i : ι) → semimodule R (φ i)] : (infi fun (i : ι) => ker (proj i)) = ⊥ := sorry

/-- If `I` and `J` are disjoint index sets, the product of the kernels of the `J`th projections of
`φ` is linearly equivalent to the product over `I`. -/
def infi_ker_proj_equiv (R : Type u) {ι : Type x} [semiring R] (φ : ι → Type i) [(i : ι) → add_comm_monoid (φ i)] [(i : ι) → semimodule R (φ i)] {I : set ι} {J : set ι} [decidable_pred fun (i : ι) => i ∈ I] (hd : disjoint I J) (hu : set.univ ⊆ I ∪ J) : linear_equiv R (↥(infi fun (i : ι) => infi fun (H : i ∈ J) => ker (proj i))) ((i : ↥I) → φ ↑i) :=
  linear_equiv.of_linear
    (pi fun (i : ↥I) => comp (proj ↑i) (submodule.subtype (infi fun (i : ι) => infi fun (H : i ∈ J) => ker (proj i))))
    (cod_restrict (infi fun (i : ι) => infi fun (H : i ∈ J) => ker (proj i))
      (pi fun (i : ι) => dite (i ∈ I) (fun (h : i ∈ I) => proj { val := i, property := h }) fun (h : ¬i ∈ I) => 0) sorry)
    sorry sorry

/-- `diag i j` is the identity map if `i = j`. Otherwise it is the constant 0 map. -/
def diag {R : Type u} {ι : Type x} [semiring R] {φ : ι → Type i} [(i : ι) → add_comm_monoid (φ i)] [(i : ι) → semimodule R (φ i)] [DecidableEq ι] (i : ι) (j : ι) : linear_map R (φ i) (φ j) :=
  function.update 0 i id j

theorem update_apply {R : Type u} {M₂ : Type w} {ι : Type x} [semiring R] [add_comm_monoid M₂] [semimodule R M₂] {φ : ι → Type i} [(i : ι) → add_comm_monoid (φ i)] [(i : ι) → semimodule R (φ i)] [DecidableEq ι] (f : (i : ι) → linear_map R M₂ (φ i)) (c : M₂) (i : ι) (j : ι) (b : linear_map R M₂ (φ i)) : coe_fn (function.update f i b j) c = function.update (fun (i : ι) => coe_fn (f i) c) i (coe_fn b c) j := sorry

/-- The standard basis of the product of `φ`. -/
def std_basis (R : Type u) {ι : Type x} [semiring R] (φ : ι → Type i) [(i : ι) → add_comm_monoid (φ i)] [(i : ι) → semimodule R (φ i)] [DecidableEq ι] (i : ι) : linear_map R (φ i) ((i : ι) → φ i) :=
  pi (diag i)

theorem std_basis_apply (R : Type u) {ι : Type x} [semiring R] (φ : ι → Type i) [(i : ι) → add_comm_monoid (φ i)] [(i : ι) → semimodule R (φ i)] [DecidableEq ι] (i : ι) (b : φ i) : coe_fn (std_basis R φ i) b = function.update 0 i b := sorry

@[simp] theorem std_basis_same (R : Type u) {ι : Type x} [semiring R] (φ : ι → Type i) [(i : ι) → add_comm_monoid (φ i)] [(i : ι) → semimodule R (φ i)] [DecidableEq ι] (i : ι) (b : φ i) : coe_fn (std_basis R φ i) b i = b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn (std_basis R φ i) b i = b)) (std_basis_apply R φ i b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (function.update 0 i b i = b)) (function.update_same i b 0))) (Eq.refl b))

theorem std_basis_ne (R : Type u) {ι : Type x} [semiring R] (φ : ι → Type i) [(i : ι) → add_comm_monoid (φ i)] [(i : ι) → semimodule R (φ i)] [DecidableEq ι] (i : ι) (j : ι) (h : j ≠ i) (b : φ i) : coe_fn (std_basis R φ i) b j = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn (std_basis R φ i) b j = 0)) (std_basis_apply R φ i b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (function.update 0 i b j = 0)) (function.update_noteq h b 0)))
      (Eq.refl (HasZero.zero j)))

theorem ker_std_basis (R : Type u) {ι : Type x} [semiring R] (φ : ι → Type i) [(i : ι) → add_comm_monoid (φ i)] [(i : ι) → semimodule R (φ i)] [DecidableEq ι] (i : ι) : ker (std_basis R φ i) = ⊥ := sorry

theorem proj_comp_std_basis (R : Type u) {ι : Type x} [semiring R] (φ : ι → Type i) [(i : ι) → add_comm_monoid (φ i)] [(i : ι) → semimodule R (φ i)] [DecidableEq ι] (i : ι) (j : ι) : comp (proj i) (std_basis R φ j) = diag j i :=
  eq.mpr (id (Eq._oldrec (Eq.refl (comp (proj i) (std_basis R φ j) = diag j i)) (std_basis.equations._eqn_1 R φ j)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (comp (proj i) (pi (diag j)) = diag j i)) (proj_pi (diag j) i)))
      (Eq.refl (diag j i)))

theorem proj_std_basis_same (R : Type u) {ι : Type x} [semiring R] (φ : ι → Type i) [(i : ι) → add_comm_monoid (φ i)] [(i : ι) → semimodule R (φ i)] [DecidableEq ι] (i : ι) : comp (proj i) (std_basis R φ i) = id := sorry

theorem proj_std_basis_ne (R : Type u) {ι : Type x} [semiring R] (φ : ι → Type i) [(i : ι) → add_comm_monoid (φ i)] [(i : ι) → semimodule R (φ i)] [DecidableEq ι] (i : ι) (j : ι) (h : i ≠ j) : comp (proj i) (std_basis R φ j) = 0 := sorry

theorem supr_range_std_basis_le_infi_ker_proj (R : Type u) {ι : Type x} [semiring R] (φ : ι → Type i) [(i : ι) → add_comm_monoid (φ i)] [(i : ι) → semimodule R (φ i)] [DecidableEq ι] (I : set ι) (J : set ι) (h : disjoint I J) : (supr fun (i : ι) => supr fun (H : i ∈ I) => range (std_basis R φ i)) ≤
  infi fun (i : ι) => infi fun (H : i ∈ J) => ker (proj i) := sorry

theorem infi_ker_proj_le_supr_range_std_basis (R : Type u) {ι : Type x} [semiring R] (φ : ι → Type i) [(i : ι) → add_comm_monoid (φ i)] [(i : ι) → semimodule R (φ i)] [DecidableEq ι] {I : finset ι} {J : set ι} (hu : set.univ ⊆ ↑I ∪ J) : (infi fun (i : ι) => infi fun (H : i ∈ J) => ker (proj i)) ≤
  supr fun (i : ι) => supr fun (H : i ∈ I) => range (std_basis R φ i) := sorry

theorem supr_range_std_basis_eq_infi_ker_proj (R : Type u) {ι : Type x} [semiring R] (φ : ι → Type i) [(i : ι) → add_comm_monoid (φ i)] [(i : ι) → semimodule R (φ i)] [DecidableEq ι] {I : set ι} {J : set ι} (hd : disjoint I J) (hu : set.univ ⊆ I ∪ J) (hI : set.finite I) : (supr fun (i : ι) => supr fun (H : i ∈ I) => range (std_basis R φ i)) =
  infi fun (i : ι) => infi fun (H : i ∈ J) => ker (proj i) := sorry

theorem supr_range_std_basis (R : Type u) {ι : Type x} [semiring R] (φ : ι → Type i) [(i : ι) → add_comm_monoid (φ i)] [(i : ι) → semimodule R (φ i)] [DecidableEq ι] [fintype ι] : (supr fun (i : ι) => range (std_basis R φ i)) = ⊤ := sorry

theorem disjoint_std_basis_std_basis (R : Type u) {ι : Type x} [semiring R] (φ : ι → Type i) [(i : ι) → add_comm_monoid (φ i)] [(i : ι) → semimodule R (φ i)] [DecidableEq ι] (I : set ι) (J : set ι) (h : disjoint I J) : disjoint (supr fun (i : ι) => supr fun (H : i ∈ I) => range (std_basis R φ i))
  (supr fun (i : ι) => supr fun (H : i ∈ J) => range (std_basis R φ i)) := sorry

theorem std_basis_eq_single (R : Type u) {ι : Type x} [semiring R] [DecidableEq ι] {a : R} : (fun (i : ι) => coe_fn (std_basis R (fun (_x : ι) => R) i) a) = fun (i : ι) => ⇑(finsupp.single i a) := sorry

/-- Given an `R`-module `M` and a function `m → n` between arbitrary types,
construct a linear map `(n → M) →ₗ[R] (m → M)` -/
def fun_left (R : Type u) (M : Type v) [semiring R] [add_comm_monoid M] [semimodule R M] {m : Type u_1} {n : Type u_2} (f : m → n) : linear_map R (n → M) (m → M) :=
  mk (fun (_x : n → M) => _x ∘ f) sorry sorry

@[simp] theorem fun_left_apply (R : Type u) (M : Type v) [semiring R] [add_comm_monoid M] [semimodule R M] {m : Type u_1} {n : Type u_2} (f : m → n) (g : n → M) (i : m) : coe_fn (fun_left R M f) g i = g (f i) :=
  rfl

@[simp] theorem fun_left_id (R : Type u) (M : Type v) [semiring R] [add_comm_monoid M] [semimodule R M] {n : Type u_2} (g : n → M) : coe_fn (fun_left R M id) g = g :=
  rfl

theorem fun_left_comp (R : Type u) (M : Type v) [semiring R] [add_comm_monoid M] [semimodule R M] {m : Type u_1} {n : Type u_2} {p : Type u_3} (f₁ : n → p) (f₂ : m → n) : fun_left R M (f₁ ∘ f₂) = comp (fun_left R M f₂) (fun_left R M f₁) :=
  rfl

/-- Given an `R`-module `M` and an equivalence `m ≃ n` between arbitrary types,
construct a linear equivalence `(n → M) ≃ₗ[R] (m → M)` -/
def fun_congr_left (R : Type u) (M : Type v) [semiring R] [add_comm_monoid M] [semimodule R M] {m : Type u_1} {n : Type u_2} (e : m ≃ n) : linear_equiv R (n → M) (m → M) :=
  linear_equiv.of_linear (fun_left R M ⇑e) (fun_left R M ⇑(equiv.symm e)) sorry sorry

@[simp] theorem fun_congr_left_apply (R : Type u) (M : Type v) [semiring R] [add_comm_monoid M] [semimodule R M] {m : Type u_1} {n : Type u_2} (e : m ≃ n) (x : n → M) : coe_fn (fun_congr_left R M e) x = coe_fn (fun_left R M ⇑e) x :=
  rfl

@[simp] theorem fun_congr_left_id (R : Type u) (M : Type v) [semiring R] [add_comm_monoid M] [semimodule R M] {n : Type u_2} : fun_congr_left R M (equiv.refl n) = linear_equiv.refl R (n → M) :=
  rfl

@[simp] theorem fun_congr_left_comp (R : Type u) (M : Type v) [semiring R] [add_comm_monoid M] [semimodule R M] {m : Type u_1} {n : Type u_2} {p : Type u_3} (e₁ : m ≃ n) (e₂ : n ≃ p) : fun_congr_left R M (equiv.trans e₁ e₂) = linear_equiv.trans (fun_congr_left R M e₂) (fun_congr_left R M e₁) :=
  rfl

@[simp] theorem fun_congr_left_symm (R : Type u) (M : Type v) [semiring R] [add_comm_monoid M] [semimodule R M] {m : Type u_1} {n : Type u_2} (e : m ≃ n) : linear_equiv.symm (fun_congr_left R M e) = fun_congr_left R M (equiv.symm e) :=
  rfl

protected instance automorphism_group (R : Type u) (M : Type v) [semiring R] [add_comm_monoid M] [semimodule R M] : group (linear_equiv R M M) :=
  group.mk (fun (f g : linear_equiv R M M) => linear_equiv.trans g f) sorry (linear_equiv.refl R M) sorry sorry
    (fun (f : linear_equiv R M M) => linear_equiv.symm f)
    (div_inv_monoid.div._default (fun (f g : linear_equiv R M M) => linear_equiv.trans g f) sorry (linear_equiv.refl R M)
      sorry sorry fun (f : linear_equiv R M M) => linear_equiv.symm f)
    sorry

protected instance automorphism_group.to_linear_map_is_monoid_hom (R : Type u) (M : Type v) [semiring R] [add_comm_monoid M] [semimodule R M] : is_monoid_hom linear_equiv.to_linear_map :=
  is_monoid_hom.mk rfl

/-- The group of invertible linear maps from `M` to itself -/
def general_linear_group (R : Type u) (M : Type v) [semiring R] [add_comm_monoid M] [semimodule R M]  :=
  units (linear_map R M M)

namespace general_linear_group


protected instance has_coe_to_fun {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] : has_coe_to_fun (general_linear_group R M) :=
  Mathlib.coe_fn_trans

/-- An invertible linear map `f` determines an equivalence from `M` to itself. -/
def to_linear_equiv {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (f : general_linear_group R M) : linear_equiv R M M :=
  linear_equiv.mk (to_fun (units.val f)) sorry sorry (to_fun (units.inv f)) sorry sorry

/-- An equivalence from `M` to itself determines an invertible linear map. -/
def of_linear_equiv {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (f : linear_equiv R M M) : general_linear_group R M :=
  units.mk ↑f ↑(linear_equiv.symm f) sorry sorry

/-- The general linear group on `R` and `M` is multiplicatively equivalent to the type of linear
equivalences between `M` and itself. -/
def general_linear_equiv (R : Type u) (M : Type v) [semiring R] [add_comm_monoid M] [semimodule R M] : general_linear_group R M ≃* linear_equiv R M M :=
  mul_equiv.mk to_linear_equiv of_linear_equiv sorry sorry sorry

@[simp] theorem general_linear_equiv_to_linear_map (R : Type u) (M : Type v) [semiring R] [add_comm_monoid M] [semimodule R M] (f : general_linear_group R M) : ↑(coe_fn (general_linear_equiv R M) f) = ↑f :=
  ext fun (x : M) => Eq.refl (coe_fn (↑(coe_fn (general_linear_equiv R M) f)) x)

end general_linear_group


end linear_map


namespace submodule


protected instance is_modular_lattice {R : Type u} {M : Type v} [ring R] [add_comm_group M] [module R M] : is_modular_lattice (submodule R M) := sorry

