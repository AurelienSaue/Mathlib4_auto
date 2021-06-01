/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.group.hom
import Mathlib.algebra.module.basic
import Mathlib.algebra.group_action_hom
import Mathlib.PostPort

universes u v w l x u_1 u_2 y z 

namespace Mathlib

/-!
# Linear maps and linear equivalences

In this file we define

* `linear_map R M M₂`, `M →ₗ[R] M₂` : a linear map between two R-`semimodule`s.

* `is_linear_map R f` : predicate saying that `f : M → M₂` is a linear map.

* `linear_equiv R M ₂`, `M ≃ₗ[R] M₂`: an invertible linear map

## Tags

linear map, linear equiv, linear equivalences, linear isomorphism, linear isomorphic
-/

/-- A map `f` between semimodules over a semiring is linear if it satisfies the two properties
`f (x + y) = f x + f y` and `f (c • x) = c • f x`. The predicate `is_linear_map R f` asserts this
property. A bundled version is available with `linear_map`, and should be favored over
`is_linear_map` most of the time. -/
structure is_linear_map (R : Type u) {M : Type v} {M₂ : Type w} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : M → M₂)
    where
  map_add : ∀ (x y : M), f (x + y) = f x + f y
  map_smul : ∀ (c : R) (x : M), f (c • x) = c • f x

/-- A map `f` between semimodules over a semiring is linear if it satisfies the two properties
`f (x + y) = f x + f y` and `f (c • x) = c • f x`. Elements of `linear_map R M M₂` (available under
the notation `M →ₗ[R] M₂`) are bundled versions of such maps. An unbundled version is available with
the predicate `is_linear_map`, but it should be avoided most of the time. -/
structure linear_map (R : Type u) (M : Type v) (M₂ : Type w) [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂]
    extends mul_action_hom R M M₂, add_hom M M₂ where

/-- The `add_hom` underlying a `linear_map`. -/
/-- The `mul_action_hom` underlying a `linear_map`. -/
namespace linear_map


protected instance has_coe_to_fun {R : Type u} {M : Type w} {M₂ : Type x} [semiring R]
    [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] :
    has_coe_to_fun (linear_map R M M₂) :=
  has_coe_to_fun.mk (fun (x : linear_map R M M₂) => M → M₂) to_fun

@[simp] theorem coe_mk {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : M → M₂)
    (h₁ : ∀ (x y : M), f (x + y) = f x + f y) (h₂ : ∀ (m : R) (x : M), f (m • x) = m • f x) :
    ⇑(mk f h₁ h₂) = f :=
  rfl

/-- Identity map as a `linear_map` -/
def id {R : Type u} {M : Type w} [semiring R] [add_comm_monoid M] [semimodule R M] :
    linear_map R M M :=
  mk id sorry sorry

theorem id_apply {R : Type u} {M : Type w} [semiring R] [add_comm_monoid M] [semimodule R M]
    (x : M) : coe_fn id x = x :=
  rfl

@[simp] theorem id_coe {R : Type u} {M : Type w} [semiring R] [add_comm_monoid M] [semimodule R M] :
    ⇑id = id :=
  funext fun (x : M) => Eq.refl (coe_fn id x)

@[simp] theorem to_fun_eq_coe {R : Type u} {M : Type w} {M₂ : Type x} [semiring R]
    [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂]
    (f : linear_map R M M₂) : to_fun f = ⇑f :=
  rfl

theorem is_linear {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M M₂) :
    is_linear_map R ⇑f :=
  is_linear_map.mk (map_add' f) (map_smul' f)

theorem coe_injective {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] :
    function.injective fun (f : linear_map R M M₂) => (fun (this : M → M₂) => this) ⇑f :=
  sorry

theorem ext {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {f : linear_map R M M₂}
    {g : linear_map R M M₂} (H : ∀ (x : M), coe_fn f x = coe_fn g x) : f = g :=
  coe_injective (funext H)

protected theorem congr_arg {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {f : linear_map R M M₂} {x : M}
    {x' : M} : x = x' → coe_fn f x = coe_fn f x' :=
  sorry

/-- If two linear maps are equal, they are equal at each point. -/
protected theorem congr_fun {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {f : linear_map R M M₂}
    {g : linear_map R M M₂} (h : f = g) (x : M) : coe_fn f x = coe_fn g x :=
  h ▸ rfl

theorem ext_iff {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {f : linear_map R M M₂}
    {g : linear_map R M M₂} : f = g ↔ ∀ (x : M), coe_fn f x = coe_fn g x :=
  { mp := fun (ᾰ : f = g) (x : M) => Eq._oldrec (Eq.refl (coe_fn f x)) ᾰ, mpr := ext }

@[simp] theorem mk_coe {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M M₂)
    (h₁ : ∀ (x y : M), coe_fn f (x + y) = coe_fn f x + coe_fn f y)
    (h₂ : ∀ (m : R) (x : M), coe_fn f (m • x) = m • coe_fn f x) : mk (⇑f) h₁ h₂ = f :=
  ext fun (_x : M) => rfl

@[simp] theorem map_add {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M M₂) (x : M)
    (y : M) : coe_fn f (x + y) = coe_fn f x + coe_fn f y :=
  map_add' f x y

@[simp] theorem map_smul {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M M₂) (c : R)
    (x : M) : coe_fn f (c • x) = c • coe_fn f x :=
  map_smul' f c x

@[simp] theorem map_zero {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M M₂) :
    coe_fn f 0 = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn f 0 = 0)) (Eq.symm (zero_smul R 0))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn f (0 • 0) = 0)) (map_smul f 0 0)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (0 • coe_fn f 0 = 0)) (zero_smul R (coe_fn f 0))))
        (Eq.refl 0)))

/--
A typeclass for `has_scalar` structures which can be moved through a `linear_map`.
This typeclass is generated automatically from a `is_scalar_tower` instance, but exists so that
we can also add an instance for `add_comm_group.int_module`, allowing `z •` to be moved even if
`R` does not support negation.
-/
class compatible_smul (M : Type w) (M₂ : Type x) [add_comm_monoid M] [add_comm_monoid M₂]
    (R : Type u_1) (S : Type u_2) [semiring S] [has_scalar R M] [semimodule S M] [has_scalar R M₂]
    [semimodule S M₂]
    where
  map_smul : ∀ (f : linear_map S M M₂) (c : R) (x : M), coe_fn f (c • x) = c • coe_fn f x

protected instance compatible_smul.is_scalar_tower {M : Type w} {M₂ : Type x} [add_comm_monoid M]
    [add_comm_monoid M₂] {R : Type u_1} {S : Type u_2} [semiring S] [has_scalar R S]
    [has_scalar R M] [semimodule S M] [is_scalar_tower R S M] [has_scalar R M₂] [semimodule S M₂]
    [is_scalar_tower R S M₂] : compatible_smul M M₂ R S :=
  compatible_smul.mk sorry

@[simp] theorem map_smul_of_tower {M : Type w} {M₂ : Type x} [add_comm_monoid M]
    [add_comm_monoid M₂] {R : Type u_1} {S : Type u_2} [semiring S] [has_scalar R M]
    [semimodule S M] [has_scalar R M₂] [semimodule S M₂] [compatible_smul M M₂ R S]
    (f : linear_map S M M₂) (c : R) (x : M) : coe_fn f (c • x) = c • coe_fn f x :=
  compatible_smul.map_smul f c x

protected instance is_add_monoid_hom {R : Type u} {M : Type w} {M₂ : Type x} [semiring R]
    [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂]
    (f : linear_map R M M₂) : is_add_monoid_hom ⇑f :=
  is_add_monoid_hom.mk (map_zero f)

/-- convert a linear map to an additive map -/
def to_add_monoid_hom {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M M₂) : M →+ M₂ :=
  add_monoid_hom.mk (⇑f) (map_zero f) (map_add f)

@[simp] theorem to_add_monoid_hom_coe {R : Type u} {M : Type w} {M₂ : Type x} [semiring R]
    [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂]
    (f : linear_map R M M₂) : ⇑(to_add_monoid_hom f) = ⇑f :=
  rfl

/-- If `M` and `M₂` are both `R`-semimodules and `S`-semimodules and `R`-semimodule structures
are defined by an action of `R` on `S` (formally, we have two scalar towers), then any `S`-linear
map from `M` to `M₂` is `R`-linear.

See also `linear_map.map_smul_of_tower`. -/
def restrict_scalars (R : Type u) {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {S : Type u_1} [semiring S]
    [semimodule S M] [semimodule S M₂] [compatible_smul M M₂ R S] (f : linear_map S M M₂) :
    linear_map R M M₂ :=
  mk (⇑f) (map_add f) sorry

@[simp] theorem map_sum {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M M₂) {ι : Type u_1}
    {t : finset ι} {g : ι → M} :
    coe_fn f (finset.sum t fun (i : ι) => g i) = finset.sum t fun (i : ι) => coe_fn f (g i) :=
  add_monoid_hom.map_sum (to_add_monoid_hom f) (fun (i : ι) => g i) t

theorem to_add_monoid_hom_injective {R : Type u} {M : Type w} {M₂ : Type x} [semiring R]
    [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] :
    function.injective to_add_monoid_hom :=
  fun (f g : linear_map R M M₂) (h : to_add_monoid_hom f = to_add_monoid_hom g) =>
    ext (add_monoid_hom.congr_fun h)

/-- If two `R`-linear maps from `R` are equal on `1`, then they are equal. -/
theorem ext_ring {R : Type u} {M : Type w} [semiring R] [add_comm_monoid M] [semimodule R M]
    {f : linear_map R R M} {g : linear_map R R M} (h : coe_fn f 1 = coe_fn g 1) : f = g :=
  sorry

/-- Composition of two linear maps is a linear map -/
def comp {R : Type u} {M : Type w} {M₂ : Type x} {M₃ : Type y} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] [add_comm_monoid M₃] {semimodule_M : semimodule R M}
    {semimodule_M₂ : semimodule R M₂} {semimodule_M₃ : semimodule R M₃} (f : linear_map R M₂ M₃)
    (g : linear_map R M M₂) : linear_map R M M₃ :=
  mk (⇑f ∘ ⇑g) sorry sorry

@[simp] theorem comp_apply {R : Type u} {M : Type w} {M₂ : Type x} {M₃ : Type y} [semiring R]
    [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] {semimodule_M : semimodule R M}
    {semimodule_M₂ : semimodule R M₂} {semimodule_M₃ : semimodule R M₃} (f : linear_map R M₂ M₃)
    (g : linear_map R M M₂) (x : M) : coe_fn (comp f g) x = coe_fn f (coe_fn g x) :=
  rfl

theorem comp_coe {R : Type u} {M : Type w} {M₂ : Type x} {M₃ : Type y} [semiring R]
    [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] {semimodule_M : semimodule R M}
    {semimodule_M₂ : semimodule R M₂} {semimodule_M₃ : semimodule R M₃} (f : linear_map R M₂ M₃)
    (g : linear_map R M M₂) : ⇑f ∘ ⇑g = ⇑(comp f g) :=
  rfl

/-- If a function `g` is a left and right inverse of a linear map `f`, then `g` is linear itself. -/
def inverse {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : linear_map R M M₂) (g : M₂ → M)
    (h₁ : function.left_inverse g ⇑f) (h₂ : function.right_inverse g ⇑f) : linear_map R M₂ M :=
  id
    (fun (h₂ : ∀ (x : M₂), coe_fn f (g x) = x) =>
      id (fun (h₁ : ∀ (x : M), g (coe_fn f x) = x) => mk g sorry sorry) h₁)
    h₂

@[simp] theorem map_neg {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_group M]
    [add_comm_group M₂] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂}
    (f : linear_map R M M₂) (x : M) : coe_fn f (-x) = -coe_fn f x :=
  add_monoid_hom.map_neg (to_add_monoid_hom f) x

@[simp] theorem map_sub {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_group M]
    [add_comm_group M₂] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂}
    (f : linear_map R M M₂) (x : M) (y : M) : coe_fn f (x - y) = coe_fn f x - coe_fn f y :=
  add_monoid_hom.map_sub (to_add_monoid_hom f) x y

protected instance is_add_group_hom {R : Type u} {M : Type w} {M₂ : Type x} [semiring R]
    [add_comm_group M] [add_comm_group M₂] {semimodule_M : semimodule R M}
    {semimodule_M₂ : semimodule R M₂} (f : linear_map R M M₂) : is_add_group_hom ⇑f :=
  is_add_group_hom.mk

protected instance compatible_smul.int_module {M : Type w} {M₂ : Type x} [add_comm_group M]
    [add_comm_group M₂] {S : Type u_1} [semiring S] [semimodule ℤ M] [semimodule S M]
    [semimodule ℤ M₂] [semimodule S M₂] : compatible_smul M M₂ ℤ S :=
  compatible_smul.mk sorry

end linear_map


namespace is_linear_map


/-- Convert an `is_linear_map` predicate to a `linear_map` -/
def mk' {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : M → M₂) (H : is_linear_map R f) :
    linear_map R M M₂ :=
  linear_map.mk f (map_add H) (map_smul H)

@[simp] theorem mk'_apply {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {f : M → M₂} (H : is_linear_map R f)
    (x : M) : coe_fn (mk' f H) x = f x :=
  rfl

theorem is_linear_map_smul {R : Type u_1} {M : Type u_2} [comm_semiring R] [add_comm_monoid M]
    [semimodule R M] (c : R) : is_linear_map R fun (z : M) => c • z :=
  sorry

theorem is_linear_map_smul' {R : Type u_1} {M : Type u_2} [semiring R] [add_comm_monoid M]
    [semimodule R M] (a : M) : is_linear_map R fun (c : R) => c • a :=
  mk (fun (x y : R) => add_smul x y a) fun (x y : R) => mul_smul x y a

theorem map_zero {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {f : M → M₂} (lin : is_linear_map R f) :
    f 0 = 0 :=
  linear_map.map_zero (mk' f lin)

theorem is_linear_map_neg {R : Type u} {M : Type w} [semiring R] [add_comm_group M]
    [semimodule R M] : is_linear_map R fun (z : M) => -z :=
  mk neg_add fun (x : R) (y : M) => Eq.symm (smul_neg x y)

theorem map_neg {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_group M]
    [add_comm_group M₂] [semimodule R M] [semimodule R M₂] {f : M → M₂} (lin : is_linear_map R f)
    (x : M) : f (-x) = -f x :=
  linear_map.map_neg (mk' f lin) x

theorem map_sub {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_group M]
    [add_comm_group M₂] [semimodule R M] [semimodule R M₂] {f : M → M₂} (lin : is_linear_map R f)
    (x : M) (y : M) : f (x - y) = f x - f y :=
  linear_map.map_sub (mk' f lin) x y

end is_linear_map


/-- Linear endomorphisms of a module, with associated ring structure
`linear_map.endomorphism_semiring` and algebra structure `module.endomorphism_algebra`. -/
def module.End (R : Type u) (M : Type v) [semiring R] [add_comm_monoid M] [semimodule R M] :=
  linear_map R M M

/-- Reinterpret an additive homomorphism as a `ℤ`-linear map. -/
def add_monoid_hom.to_int_linear_map {M : Type w} {M₂ : Type x} [add_comm_group M]
    [add_comm_group M₂] (f : M →+ M₂) : linear_map ℤ M M₂ :=
  linear_map.mk ⇑f sorry sorry

/-- Reinterpret an additive homomorphism as a `ℚ`-linear map. -/
def add_monoid_hom.to_rat_linear_map {M : Type w} {M₂ : Type x} [add_comm_group M]
    [vector_space ℚ M] [add_comm_group M₂] [vector_space ℚ M₂] (f : M →+ M₂) : linear_map ℚ M M₂ :=
  linear_map.mk (add_monoid_hom.to_fun f) sorry (add_monoid_hom.map_rat_module_smul f)

/-! ### Linear equivalences -/

/-- A linear equivalence is an invertible linear map. -/
structure linear_equiv (R : Type u) (M : Type v) (M₂ : Type w) [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂]
    extends M ≃+ M₂, linear_map R M M₂ where

namespace linear_equiv


-- see Note [function coercion]

protected instance linear_map.has_coe {R : Type u} {M : Type w} {M₂ : Type x} [semiring R]
    [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] :
    has_coe (linear_equiv R M M₂) (linear_map R M M₂) :=
  has_coe.mk to_linear_map

protected instance has_coe_to_fun {R : Type u} {M : Type w} {M₂ : Type x} [semiring R]
    [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] :
    has_coe_to_fun (linear_equiv R M M₂) :=
  has_coe_to_fun.mk (fun (f : linear_equiv R M M₂) => M → M₂)
    fun (f : linear_equiv R M M₂) => to_fun f

@[simp] theorem mk_apply {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] {to_fun : M → M₂} {inv_fun : M₂ → M}
    {map_add : ∀ (x y : M), to_fun (x + y) = to_fun x + to_fun y}
    {map_smul : ∀ (m : R) (x : M), to_fun (m • x) = m • to_fun x}
    {left_inv : function.left_inverse inv_fun to_fun}
    {right_inv : function.right_inverse inv_fun to_fun} {a : M} :
    coe_fn (mk to_fun map_add map_smul inv_fun left_inv right_inv) a = to_fun a :=
  rfl

-- This exists for compatibility, previously `≃ₗ[R]` extended `≃` instead of `≃+`.

def to_equiv {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : linear_equiv R M M₂ → M ≃ M₂ :=
  fun (f : linear_equiv R M M₂) => add_equiv.to_equiv (to_add_equiv f)

theorem injective_to_equiv {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] : function.injective to_equiv :=
  sorry

@[simp] theorem to_equiv_inj {R : Type u} {M : Type w} {M₂ : Type x} [semiring R]
    [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂]
    {e₁ : linear_equiv R M M₂} {e₂ : linear_equiv R M M₂} : to_equiv e₁ = to_equiv e₂ ↔ e₁ = e₂ :=
  function.injective.eq_iff injective_to_equiv

theorem injective_to_linear_map {R : Type u} {M : Type w} {M₂ : Type x} [semiring R]
    [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] :
    function.injective coe :=
  fun (e₁ e₂ : linear_equiv R M M₂) (H : ↑e₁ = ↑e₂) =>
    injective_to_equiv (equiv.ext (linear_map.congr_fun H))

@[simp] theorem to_linear_map_inj {R : Type u} {M : Type w} {M₂ : Type x} [semiring R]
    [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂]
    {e₁ : linear_equiv R M M₂} {e₂ : linear_equiv R M M₂} : ↑e₁ = ↑e₂ ↔ e₁ = e₂ :=
  function.injective.eq_iff injective_to_linear_map

@[simp] theorem coe_coe {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂}
    (e : linear_equiv R M M₂) : ⇑↑e = ⇑e :=
  rfl

@[simp] theorem coe_to_equiv {R : Type u} {M : Type w} {M₂ : Type x} [semiring R]
    [add_comm_monoid M] [add_comm_monoid M₂] {semimodule_M : semimodule R M}
    {semimodule_M₂ : semimodule R M₂} (e : linear_equiv R M M₂) : ⇑(to_equiv e) = ⇑e :=
  rfl

@[simp] theorem to_fun_apply {R : Type u} {M : Type w} {M₂ : Type x} [semiring R]
    [add_comm_monoid M] [add_comm_monoid M₂] {semimodule_M : semimodule R M}
    {semimodule_M₂ : semimodule R M₂} (e : linear_equiv R M M₂) {m : M} : to_fun e m = coe_fn e m :=
  rfl

theorem ext {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂}
    {e : linear_equiv R M M₂} {e' : linear_equiv R M M₂} (h : ∀ (x : M), coe_fn e x = coe_fn e' x) :
    e = e' :=
  injective_to_equiv (equiv.ext h)

protected theorem congr_arg {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂}
    {e : linear_equiv R M M₂} {x : M} {x' : M} : x = x' → coe_fn e x = coe_fn e x' :=
  sorry

protected theorem congr_fun {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂}
    {e : linear_equiv R M M₂} {e' : linear_equiv R M M₂} (h : e = e') (x : M) :
    coe_fn e x = coe_fn e' x :=
  h ▸ rfl

theorem ext_iff {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂}
    {e : linear_equiv R M M₂} {e' : linear_equiv R M M₂} :
    e = e' ↔ ∀ (x : M), coe_fn e x = coe_fn e' x :=
  { mp := fun (h : e = e') (x : M) => h ▸ rfl, mpr := ext }

/-- The identity map is a linear equivalence. -/
def refl (R : Type u) (M : Type w) [semiring R] [add_comm_monoid M] [semimodule R M] :
    linear_equiv R M M :=
  mk (linear_map.to_fun linear_map.id) sorry sorry (equiv.inv_fun (equiv.refl M)) sorry sorry

@[simp] theorem refl_apply {R : Type u} {M : Type w} [semiring R] [add_comm_monoid M]
    [semimodule R M] (x : M) : coe_fn (refl R M) x = x :=
  rfl

/-- Linear equivalences are symmetric. -/
def symm {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂}
    (e : linear_equiv R M M₂) : linear_equiv R M₂ M :=
  mk
    (linear_map.to_fun
      (linear_map.inverse (to_linear_map e) (inv_fun e) (left_inv e) (right_inv e)))
    sorry sorry (equiv.inv_fun (equiv.symm (to_equiv e))) sorry sorry

/-- See Note [custom simps projection] -/
def simps.inv_fun {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (e : linear_equiv R M M₂) : M₂ → M :=
  ⇑(symm e)

@[simp] theorem inv_fun_eq_symm {R : Type u} {M : Type w} {M₂ : Type x} [semiring R]
    [add_comm_monoid M] [add_comm_monoid M₂] {semimodule_M : semimodule R M}
    {semimodule_M₂ : semimodule R M₂} (e : linear_equiv R M M₂) : inv_fun e = ⇑(symm e) :=
  rfl

/-- Linear equivalences are transitive. -/
def trans {R : Type u} {M : Type w} {M₂ : Type x} {M₃ : Type y} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] [add_comm_monoid M₃] {semimodule_M : semimodule R M}
    {semimodule_M₂ : semimodule R M₂} {semimodule_M₃ : semimodule R M₃} (e₁ : linear_equiv R M M₂)
    (e₂ : linear_equiv R M₂ M₃) : linear_equiv R M M₃ :=
  mk (linear_map.to_fun (linear_map.comp (to_linear_map e₂) (to_linear_map e₁))) sorry sorry
    (equiv.inv_fun (equiv.trans (to_equiv e₁) (to_equiv e₂))) sorry sorry

@[simp] theorem coe_to_add_equiv {R : Type u} {M : Type w} {M₂ : Type x} [semiring R]
    [add_comm_monoid M] [add_comm_monoid M₂] {semimodule_M : semimodule R M}
    {semimodule_M₂ : semimodule R M₂} (e : linear_equiv R M M₂) : ⇑(to_add_equiv e) = ⇑e :=
  rfl

@[simp] theorem trans_apply {R : Type u} {M : Type w} {M₂ : Type x} {M₃ : Type y} [semiring R]
    [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] {semimodule_M : semimodule R M}
    {semimodule_M₂ : semimodule R M₂} {semimodule_M₃ : semimodule R M₃} (e₁ : linear_equiv R M M₂)
    (e₂ : linear_equiv R M₂ M₃) (c : M) : coe_fn (trans e₁ e₂) c = coe_fn e₂ (coe_fn e₁ c) :=
  rfl

@[simp] theorem apply_symm_apply {R : Type u} {M : Type w} {M₂ : Type x} [semiring R]
    [add_comm_monoid M] [add_comm_monoid M₂] {semimodule_M : semimodule R M}
    {semimodule_M₂ : semimodule R M₂} (e : linear_equiv R M M₂) (c : M₂) :
    coe_fn e (coe_fn (symm e) c) = c :=
  right_inv e c

@[simp] theorem symm_apply_apply {R : Type u} {M : Type w} {M₂ : Type x} [semiring R]
    [add_comm_monoid M] [add_comm_monoid M₂] {semimodule_M : semimodule R M}
    {semimodule_M₂ : semimodule R M₂} (e : linear_equiv R M M₂) (b : M) :
    coe_fn (symm e) (coe_fn e b) = b :=
  left_inv e b

@[simp] theorem symm_trans_apply {R : Type u} {M : Type w} {M₂ : Type x} {M₃ : Type y} [semiring R]
    [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] {semimodule_M : semimodule R M}
    {semimodule_M₂ : semimodule R M₂} {semimodule_M₃ : semimodule R M₃} (e₁ : linear_equiv R M M₂)
    (e₂ : linear_equiv R M₂ M₃) (c : M₃) :
    coe_fn (symm (trans e₁ e₂)) c = coe_fn (symm e₁) (coe_fn (symm e₂) c) :=
  rfl

@[simp] theorem trans_refl {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂}
    (e : linear_equiv R M M₂) : trans e (refl R M₂) = e :=
  injective_to_equiv (equiv.trans_refl (to_equiv e))

@[simp] theorem refl_trans {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂}
    (e : linear_equiv R M M₂) : trans (refl R M) e = e :=
  injective_to_equiv (equiv.refl_trans (to_equiv e))

theorem symm_apply_eq {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂}
    (e : linear_equiv R M M₂) {x : M₂} {y : M} : coe_fn (symm e) x = y ↔ x = coe_fn e y :=
  equiv.symm_apply_eq (to_equiv e)

theorem eq_symm_apply {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂}
    (e : linear_equiv R M M₂) {x : M₂} {y : M} : y = coe_fn (symm e) x ↔ coe_fn e y = x :=
  equiv.eq_symm_apply (to_equiv e)

@[simp] theorem trans_symm {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : linear_equiv R M M₂) :
    trans f (symm f) = refl R M :=
  sorry

@[simp] theorem symm_trans {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] (f : linear_equiv R M M₂) :
    trans (symm f) f = refl R M₂ :=
  sorry

@[simp] theorem refl_to_linear_map {R : Type u} {M : Type w} [semiring R] [add_comm_monoid M]
    [semimodule R M] : ↑(refl R M) = linear_map.id :=
  rfl

@[simp] theorem comp_coe {R : Type u} {M : Type w} {M₂ : Type x} {M₃ : Type y} [semiring R]
    [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [semimodule R M] [semimodule R M₂]
    [semimodule R M₃] (f : linear_equiv R M M₂) (f' : linear_equiv R M₂ M₃) :
    linear_map.comp ↑f' ↑f = ↑(trans f f') :=
  rfl

@[simp] theorem map_add {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂}
    (e : linear_equiv R M M₂) (a : M) (b : M) : coe_fn e (a + b) = coe_fn e a + coe_fn e b :=
  map_add' e a b

@[simp] theorem map_zero {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂}
    (e : linear_equiv R M M₂) : coe_fn e 0 = 0 :=
  linear_map.map_zero (to_linear_map e)

@[simp] theorem map_smul {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂}
    (e : linear_equiv R M M₂) (c : R) (x : M) : coe_fn e (c • x) = c • coe_fn e x :=
  map_smul' e c x

@[simp] theorem map_sum {R : Type u} {M : Type w} {M₂ : Type x} {ι : Type z} [semiring R]
    [add_comm_monoid M] [add_comm_monoid M₂] {semimodule_M : semimodule R M}
    {semimodule_M₂ : semimodule R M₂} (e : linear_equiv R M M₂) {s : finset ι} (u : ι → M) :
    coe_fn e (finset.sum s fun (i : ι) => u i) = finset.sum s fun (i : ι) => coe_fn e (u i) :=
  linear_map.map_sum (to_linear_map e)

@[simp] theorem map_eq_zero_iff {R : Type u} {M : Type w} {M₂ : Type x} [semiring R]
    [add_comm_monoid M] [add_comm_monoid M₂] {semimodule_M : semimodule R M}
    {semimodule_M₂ : semimodule R M₂} (e : linear_equiv R M M₂) {x : M} : coe_fn e x = 0 ↔ x = 0 :=
  add_equiv.map_eq_zero_iff (to_add_equiv e)

theorem map_ne_zero_iff {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂}
    (e : linear_equiv R M M₂) {x : M} : coe_fn e x ≠ 0 ↔ x ≠ 0 :=
  add_equiv.map_ne_zero_iff (to_add_equiv e)

@[simp] theorem symm_symm {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂}
    (e : linear_equiv R M M₂) : symm (symm e) = e :=
  sorry

protected theorem bijective {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂}
    (e : linear_equiv R M M₂) : function.bijective ⇑e :=
  equiv.bijective (to_equiv e)

protected theorem injective {R : Type u} {M : Type w} {M₂ : Type x} [semiring R] [add_comm_monoid M]
    [add_comm_monoid M₂] {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂}
    (e : linear_equiv R M M₂) : function.injective ⇑e :=
  equiv.injective (to_equiv e)

protected theorem surjective {R : Type u} {M : Type w} {M₂ : Type x} [semiring R]
    [add_comm_monoid M] [add_comm_monoid M₂] {semimodule_M : semimodule R M}
    {semimodule_M₂ : semimodule R M₂} (e : linear_equiv R M M₂) : function.surjective ⇑e :=
  equiv.surjective (to_equiv e)

protected theorem image_eq_preimage {R : Type u} {M : Type w} {M₂ : Type x} [semiring R]
    [add_comm_monoid M] [add_comm_monoid M₂] {semimodule_M : semimodule R M}
    {semimodule_M₂ : semimodule R M₂} (e : linear_equiv R M M₂) (s : set M) :
    ⇑e '' s = ⇑(symm e) ⁻¹' s :=
  equiv.image_eq_preimage (to_equiv e) s

/-- An involutive linear map is a linear equivalence. -/
def of_involutive {R : Type u} {M : Type w} [semiring R] [add_comm_monoid M] [semimodule R M]
    (f : linear_map R M M) (hf : function.involutive ⇑f) : linear_equiv R M M :=
  mk (linear_map.to_fun f) (linear_map.map_add' f) (linear_map.map_smul' f)
    (equiv.inv_fun (function.involutive.to_equiv (⇑f) hf)) sorry sorry

@[simp] theorem coe_of_involutive {R : Type u} {M : Type w} [semiring R] [add_comm_monoid M]
    [semimodule R M] (f : linear_map R M M) (hf : function.involutive ⇑f) :
    ⇑(of_involutive f hf) = ⇑f :=
  rfl

end Mathlib