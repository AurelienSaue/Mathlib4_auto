/-
Copyright (c) 2019 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.bracket
import Mathlib.algebra.algebra.basic
import Mathlib.linear_algebra.bilinear_form
import Mathlib.linear_algebra.matrix
import Mathlib.order.preorder_hom
import Mathlib.order.compactly_generated
import Mathlib.tactic.noncomm_ring
import PostPort

universes v l u w w₁ w₂ 

namespace Mathlib

/-!
# Lie algebras

This file defines Lie rings, and Lie algebras over a commutative ring. It shows how these arise from
associative rings and algebras via the ring commutator. In particular it defines the Lie algebra
of endomorphisms of a module as well as of the algebra of square matrices over a commutative ring.

It also includes definitions of morphisms of Lie algebras, Lie subalgebras, Lie modules, Lie
submodules, and the quotient of a Lie algebra by an ideal.

## Notations

We introduce the notation ⁅x, y⁆ for the Lie bracket. Note that these are the Unicode "square with
quill" brackets rather than the usual square brackets.

Working over a fixed commutative ring `R`, we introduce the notations:
 * `L →ₗ⁅R⁆ L'` for a morphism of Lie algebras,
 * `L ≃ₗ⁅R⁆ L'` for an equivalence of Lie algebras,
 * `M →ₗ⁅R,L⁆ N` for a morphism of Lie algebra modules `M`, `N` over a Lie algebra `L`,
 * `M ≃ₗ⁅R,L⁆ N` for an equivalence of Lie algebra modules `M`, `N` over a Lie algebra `L`.

## Implementation notes

Lie algebras are defined as modules with a compatible Lie ring structure and thus, like modules,
are partially unbundled.

## References
* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1--3*][bourbaki1975]

## Tags

lie bracket, ring commutator, jacobi identity, lie ring, lie algebra
-/

/-- A Lie ring is an additive group with compatible product, known as the bracket, satisfying the
Jacobi identity. The bracket is not associative unless it is identically zero. -/
class lie_ring (L : Type v) 
extends has_bracket L L, add_comm_group L
where
  add_lie : ∀ (x y z : L), has_bracket.bracket (x + y) z = has_bracket.bracket x z + has_bracket.bracket y z
  lie_add : ∀ (x y z : L), has_bracket.bracket x (y + z) = has_bracket.bracket x y + has_bracket.bracket x z
  lie_self : ∀ (x : L), has_bracket.bracket x x = 0
  leibniz_lie : ∀ (x y z : L),
  has_bracket.bracket x (has_bracket.bracket y z) =
    has_bracket.bracket (has_bracket.bracket x y) z + has_bracket.bracket y (has_bracket.bracket x z)

/-- A Lie algebra is a module with compatible product, known as the bracket, satisfying the Jacobi
identity. Forgetting the scalar multiplication, every Lie algebra is a Lie ring. -/
class lie_algebra (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] 
extends semimodule R L
where
  lie_smul : ∀ (t : R) (x y : L), has_bracket.bracket x (t • y) = t • has_bracket.bracket x y

/-- A Lie ring module is an additive group, together with an additive action of a
Lie ring on this group, such that the Lie bracket acts as the commutator of endomorphisms.
(For representations of Lie *algebras* see `lie_module`.) -/
class lie_ring_module (L : Type v) (M : Type w) [lie_ring L] [add_comm_group M] 
extends has_bracket L M
where
  add_lie : ∀ (x y : L) (m : M), has_bracket.bracket (x + y) m = has_bracket.bracket x m + has_bracket.bracket y m
  lie_add : ∀ (x : L) (m n : M), has_bracket.bracket x (m + n) = has_bracket.bracket x m + has_bracket.bracket x n
  leibniz_lie : ∀ (x y : L) (m : M),
  has_bracket.bracket x (has_bracket.bracket y m) =
    has_bracket.bracket (has_bracket.bracket x y) m + has_bracket.bracket y (has_bracket.bracket x m)

/-- A Lie module is a module over a commutative ring, together with a linear action of a Lie
algebra on this module, such that the Lie bracket acts as the commutator of endomorphisms. -/
class lie_module (R : Type u) (L : Type v) (M : Type w) [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] 
where
  smul_lie : ∀ (t : R) (x : L) (m : M), has_bracket.bracket (t • x) m = t • has_bracket.bracket x m
  lie_smul : ∀ (t : R) (x : L) (m : M), has_bracket.bracket x (t • m) = t • has_bracket.bracket x m

@[simp] theorem add_lie {L : Type v} {M : Type w} [lie_ring L] [add_comm_group M] [lie_ring_module L M] (x : L) (y : L) (m : M) : has_bracket.bracket (x + y) m = has_bracket.bracket x m + has_bracket.bracket y m :=
  lie_ring_module.add_lie x y m

@[simp] theorem lie_add {L : Type v} {M : Type w} [lie_ring L] [add_comm_group M] [lie_ring_module L M] (x : L) (m : M) (n : M) : has_bracket.bracket x (m + n) = has_bracket.bracket x m + has_bracket.bracket x n :=
  lie_ring_module.lie_add x m n

@[simp] theorem smul_lie {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (t : R) (x : L) (m : M) : has_bracket.bracket (t • x) m = t • has_bracket.bracket x m :=
  lie_module.smul_lie t x m

@[simp] theorem lie_smul {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (t : R) (x : L) (m : M) : has_bracket.bracket x (t • m) = t • has_bracket.bracket x m :=
  lie_module.lie_smul t x m

theorem leibniz_lie {L : Type v} {M : Type w} [lie_ring L] [add_comm_group M] [lie_ring_module L M] (x : L) (y : L) (m : M) : has_bracket.bracket x (has_bracket.bracket y m) =
  has_bracket.bracket (has_bracket.bracket x y) m + has_bracket.bracket y (has_bracket.bracket x m) :=
  lie_ring_module.leibniz_lie x y m

@[simp] theorem lie_zero {L : Type v} {M : Type w} [lie_ring L] [add_comm_group M] [lie_ring_module L M] (x : L) : has_bracket.bracket x 0 = 0 :=
  add_monoid_hom.map_zero (add_monoid_hom.mk' (has_bracket.bracket x) (lie_add x))

@[simp] theorem zero_lie {L : Type v} {M : Type w} [lie_ring L] [add_comm_group M] [lie_ring_module L M] (m : M) : has_bracket.bracket 0 m = 0 :=
  add_monoid_hom.map_zero (add_monoid_hom.mk' (fun (x : L) => has_bracket.bracket x m) fun (x y : L) => add_lie x y m)

@[simp] theorem lie_self {L : Type v} [lie_ring L] (x : L) : has_bracket.bracket x x = 0 :=
  lie_ring.lie_self x

protected instance lie_ring_self_module {L : Type v} [lie_ring L] : lie_ring_module L L :=
  lie_ring_module.mk sorry sorry sorry

@[simp] theorem lie_skew {L : Type v} [lie_ring L] (x : L) (y : L) : -has_bracket.bracket y x = has_bracket.bracket x y := sorry

/-- Every Lie algebra is a module over itself. -/
protected instance lie_algebra_self_module {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] : lie_module R L L :=
  lie_module.mk sorry lie_algebra.lie_smul

@[simp] theorem neg_lie {L : Type v} {M : Type w} [lie_ring L] [add_comm_group M] [lie_ring_module L M] (x : L) (m : M) : has_bracket.bracket (-x) m = -has_bracket.bracket x m := sorry

@[simp] theorem lie_neg {L : Type v} {M : Type w} [lie_ring L] [add_comm_group M] [lie_ring_module L M] (x : L) (m : M) : has_bracket.bracket x (-m) = -has_bracket.bracket x m := sorry

@[simp] theorem gsmul_lie {L : Type v} {M : Type w} [lie_ring L] [add_comm_group M] [lie_ring_module L M] (x : L) (m : M) (a : ℤ) : has_bracket.bracket (a • x) m = a • has_bracket.bracket x m :=
  add_monoid_hom.map_gsmul
    (add_monoid_hom.mk (fun (x : L) => has_bracket.bracket x m) (zero_lie m) fun (_x _x_1 : L) => add_lie _x _x_1 m) x a

@[simp] theorem lie_gsmul {L : Type v} {M : Type w} [lie_ring L] [add_comm_group M] [lie_ring_module L M] (x : L) (m : M) (a : ℤ) : has_bracket.bracket x (a • m) = a • has_bracket.bracket x m :=
  add_monoid_hom.map_gsmul
    (add_monoid_hom.mk (fun (m : M) => has_bracket.bracket x m) (lie_zero x) fun (_x _x_1 : M) => lie_add x _x _x_1) m a

@[simp] theorem lie_lie {L : Type v} {M : Type w} [lie_ring L] [add_comm_group M] [lie_ring_module L M] (x : L) (y : L) (m : M) : has_bracket.bracket (has_bracket.bracket x y) m =
  has_bracket.bracket x (has_bracket.bracket y m) - has_bracket.bracket y (has_bracket.bracket x m) := sorry

theorem lie_jacobi {L : Type v} [lie_ring L] (x : L) (y : L) (z : L) : has_bracket.bracket x (has_bracket.bracket y z) + has_bracket.bracket y (has_bracket.bracket z x) +
    has_bracket.bracket z (has_bracket.bracket x y) =
  0 := sorry

namespace lie_algebra


/-- A morphism of Lie algebras is a linear map respecting the bracket operations. -/
structure morphism (R : Type u) (L : Type v) (L' : Type w) [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L'] 
extends linear_map R L L'
where
  map_lie : ∀ {x y : L}, to_fun (has_bracket.bracket x y) = has_bracket.bracket (to_fun x) (to_fun y)

protected instance linear_map.has_coe {R : Type u} {L₁ : Type v} {L₂ : Type w} [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_algebra R L₁] [lie_algebra R L₂] : has_coe (morphism R L₁ L₂) (linear_map R L₁ L₂) :=
  has_coe.mk morphism.to_linear_map

/-- see Note [function coercion] -/
protected instance morphism.has_coe_to_fun {R : Type u} {L₁ : Type v} {L₂ : Type w} [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_algebra R L₁] [lie_algebra R L₂] : has_coe_to_fun (morphism R L₁ L₂) :=
  has_coe_to_fun.mk (fun (x : morphism R L₁ L₂) => L₁ → L₂) morphism.to_fun

@[simp] theorem coe_mk {R : Type u} {L₁ : Type v} {L₂ : Type w} [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_algebra R L₁] [lie_algebra R L₂] (f : L₁ → L₂) (h₁ : ∀ (x y : L₁), f (x + y) = f x + f y) (h₂ : ∀ (m : R) (x : L₁), f (m • x) = m • f x) (h₃ : ∀ {x y : L₁}, f (has_bracket.bracket x y) = has_bracket.bracket (f x) (f y)) : ⇑(morphism.mk f h₁ h₂ h₃) = f :=
  rfl

@[simp] theorem coe_to_linear_map {R : Type u} {L₁ : Type v} {L₂ : Type w} [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_algebra R L₁] [lie_algebra R L₂] (f : morphism R L₁ L₂) : ⇑↑f = ⇑f :=
  rfl

@[simp] theorem morphism.map_smul {R : Type u} {L₁ : Type v} {L₂ : Type w} [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_algebra R L₁] [lie_algebra R L₂] (f : morphism R L₁ L₂) (c : R) (x : L₁) : coe_fn f (c • x) = c • coe_fn f x :=
  linear_map.map_smul (↑f) c x

@[simp] theorem morphism.map_add {R : Type u} {L₁ : Type v} {L₂ : Type w} [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_algebra R L₁] [lie_algebra R L₂] (f : morphism R L₁ L₂) (x : L₁) (y : L₁) : coe_fn f (x + y) = coe_fn f x + coe_fn f y :=
  linear_map.map_add (↑f) x y

@[simp] theorem map_lie {R : Type u} {L₁ : Type v} {L₂ : Type w} [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_algebra R L₁] [lie_algebra R L₂] (f : morphism R L₁ L₂) (x : L₁) (y : L₁) : coe_fn f (has_bracket.bracket x y) = has_bracket.bracket (coe_fn f x) (coe_fn f y) :=
  morphism.map_lie f

@[simp] theorem map_zero {R : Type u} {L₁ : Type v} {L₂ : Type w} [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_algebra R L₁] [lie_algebra R L₂] (f : morphism R L₁ L₂) : coe_fn f 0 = 0 :=
  linear_map.map_zero ↑f

/-- The constant 0 map is a Lie algebra morphism. -/
protected instance morphism.has_zero {R : Type u} {L₁ : Type v} {L₂ : Type w} [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_algebra R L₁] [lie_algebra R L₂] : HasZero (morphism R L₁ L₂) :=
  { zero := morphism.mk (linear_map.to_fun 0) sorry sorry sorry }

/-- The identity map is a Lie algebra morphism. -/
protected instance morphism.has_one {R : Type u} {L₁ : Type v} [comm_ring R] [lie_ring L₁] [lie_algebra R L₁] : HasOne (morphism R L₁ L₁) :=
  { one := morphism.mk (linear_map.to_fun 1) sorry sorry sorry }

protected instance morphism.inhabited {R : Type u} {L₁ : Type v} {L₂ : Type w} [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_algebra R L₁] [lie_algebra R L₂] : Inhabited (morphism R L₁ L₂) :=
  { default := 0 }

theorem morphism.coe_injective {R : Type u} {L₁ : Type v} {L₂ : Type w} [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_algebra R L₁] [lie_algebra R L₂] : function.injective fun (f : morphism R L₁ L₂) => (fun (this : L₁ → L₂) => this) ⇑f := sorry

theorem morphism.ext {R : Type u} {L₁ : Type v} {L₂ : Type w} [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_algebra R L₁] [lie_algebra R L₂] {f : morphism R L₁ L₂} {g : morphism R L₁ L₂} (h : ∀ (x : L₁), coe_fn f x = coe_fn g x) : f = g :=
  morphism.coe_injective (funext h)

theorem morphism.ext_iff {R : Type u} {L₁ : Type v} {L₂ : Type w} [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_algebra R L₁] [lie_algebra R L₂] {f : morphism R L₁ L₂} {g : morphism R L₁ L₂} : f = g ↔ ∀ (x : L₁), coe_fn f x = coe_fn g x :=
  { mp := fun (ᾰ : f = g) (x : L₁) => Eq._oldrec (Eq.refl (coe_fn f x)) ᾰ, mpr := morphism.ext }

/-- The composition of morphisms is a morphism. -/
def morphism.comp {R : Type u} {L₁ : Type v} {L₂ : Type w} {L₃ : Type w₁} [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_ring L₃] [lie_algebra R L₁] [lie_algebra R L₂] [lie_algebra R L₃] (f : morphism R L₂ L₃) (g : morphism R L₁ L₂) : morphism R L₁ L₃ :=
  morphism.mk (linear_map.to_fun (linear_map.comp (morphism.to_linear_map f) (morphism.to_linear_map g))) sorry sorry
    sorry

@[simp] theorem morphism.comp_apply {R : Type u} {L₁ : Type v} {L₂ : Type w} {L₃ : Type w₁} [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_ring L₃] [lie_algebra R L₁] [lie_algebra R L₂] [lie_algebra R L₃] (f : morphism R L₂ L₃) (g : morphism R L₁ L₂) (x : L₁) : coe_fn (morphism.comp f g) x = coe_fn f (coe_fn g x) :=
  rfl

theorem morphism.comp_coe {R : Type u} {L₁ : Type v} {L₂ : Type w} {L₃ : Type w₁} [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_ring L₃] [lie_algebra R L₁] [lie_algebra R L₂] [lie_algebra R L₃] (f : morphism R L₂ L₃) (g : morphism R L₁ L₂) : ⇑f ∘ ⇑g = ⇑(morphism.comp f g) :=
  rfl

/-- The inverse of a bijective morphism is a morphism. -/
def morphism.inverse {R : Type u} {L₁ : Type v} {L₂ : Type w} [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_algebra R L₁] [lie_algebra R L₂] (f : morphism R L₁ L₂) (g : L₂ → L₁) (h₁ : function.left_inverse g ⇑f) (h₂ : function.right_inverse g ⇑f) : morphism R L₂ L₁ :=
  morphism.mk (linear_map.to_fun (linear_map.inverse (morphism.to_linear_map f) g h₁ h₂)) sorry sorry sorry

/-- An equivalence of Lie algebras is a morphism which is also a linear equivalence. We could
instead define an equivalence to be a morphism which is also a (plain) equivalence. However it is
more convenient to define via linear equivalence to get `.to_linear_equiv` for free. -/
structure equiv (R : Type u) (L : Type v) (L' : Type w) [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L'] 
extends morphism R L L', linear_equiv R L L'
where

namespace equiv


protected instance has_coe_to_lie_hom {R : Type u} {L₁ : Type v} {L₂ : Type w} [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_algebra R L₁] [lie_algebra R L₂] : has_coe (equiv R L₁ L₂) (morphism R L₁ L₂) :=
  has_coe.mk to_morphism

protected instance has_coe_to_linear_equiv {R : Type u} {L₁ : Type v} {L₂ : Type w} [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_algebra R L₁] [lie_algebra R L₂] : has_coe (equiv R L₁ L₂) (linear_equiv R L₁ L₂) :=
  has_coe.mk to_linear_equiv

/-- see Note [function coercion] -/
protected instance has_coe_to_fun {R : Type u} {L₁ : Type v} {L₂ : Type w} [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_algebra R L₁] [lie_algebra R L₂] : has_coe_to_fun (equiv R L₁ L₂) :=
  has_coe_to_fun.mk (fun (x : equiv R L₁ L₂) => L₁ → L₂) to_fun

@[simp] theorem coe_to_lie_equiv {R : Type u} {L₁ : Type v} {L₂ : Type w} [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_algebra R L₁] [lie_algebra R L₂] (e : equiv R L₁ L₂) : ⇑↑e = ⇑e :=
  rfl

@[simp] theorem coe_to_linear_equiv {R : Type u} {L₁ : Type v} {L₂ : Type w} [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_algebra R L₁] [lie_algebra R L₂] (e : equiv R L₁ L₂) : ⇑↑e = ⇑e :=
  rfl

protected instance has_one {R : Type u} {L₁ : Type v} [comm_ring R] [lie_ring L₁] [lie_algebra R L₁] : HasOne (equiv R L₁ L₁) :=
  { one := mk (linear_equiv.to_fun 1) sorry sorry sorry (linear_equiv.inv_fun 1) sorry sorry }

@[simp] theorem one_apply {R : Type u} {L₁ : Type v} [comm_ring R] [lie_ring L₁] [lie_algebra R L₁] (x : L₁) : coe_fn 1 x = x :=
  rfl

protected instance inhabited {R : Type u} {L₁ : Type v} [comm_ring R] [lie_ring L₁] [lie_algebra R L₁] : Inhabited (equiv R L₁ L₁) :=
  { default := 1 }

/-- Lie algebra equivalences are reflexive. -/
def refl {R : Type u} {L₁ : Type v} [comm_ring R] [lie_ring L₁] [lie_algebra R L₁] : equiv R L₁ L₁ :=
  1

@[simp] theorem refl_apply {R : Type u} {L₁ : Type v} [comm_ring R] [lie_ring L₁] [lie_algebra R L₁] (x : L₁) : coe_fn refl x = x :=
  rfl

/-- Lie algebra equivalences are symmetric. -/
def symm {R : Type u} {L₁ : Type v} {L₂ : Type w} [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_algebra R L₁] [lie_algebra R L₂] (e : equiv R L₁ L₂) : equiv R L₂ L₁ :=
  mk (morphism.to_fun (morphism.inverse (to_morphism e) (inv_fun e) (left_inv e) (right_inv e))) sorry sorry sorry
    (linear_equiv.inv_fun (linear_equiv.symm (to_linear_equiv e))) sorry sorry

@[simp] theorem symm_symm {R : Type u} {L₁ : Type v} {L₂ : Type w} [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_algebra R L₁] [lie_algebra R L₂] (e : equiv R L₁ L₂) : symm (symm e) = e := sorry

@[simp] theorem apply_symm_apply {R : Type u} {L₁ : Type v} {L₂ : Type w} [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_algebra R L₁] [lie_algebra R L₂] (e : equiv R L₁ L₂) (x : L₂) : coe_fn e (coe_fn (symm e) x) = x :=
  linear_equiv.apply_symm_apply (to_linear_equiv e)

@[simp] theorem symm_apply_apply {R : Type u} {L₁ : Type v} {L₂ : Type w} [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_algebra R L₁] [lie_algebra R L₂] (e : equiv R L₁ L₂) (x : L₁) : coe_fn (symm e) (coe_fn e x) = x :=
  linear_equiv.symm_apply_apply (to_linear_equiv e)

/-- Lie algebra equivalences are transitive. -/
def trans {R : Type u} {L₁ : Type v} {L₂ : Type w} {L₃ : Type w₁} [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_ring L₃] [lie_algebra R L₁] [lie_algebra R L₂] [lie_algebra R L₃] (e₁ : equiv R L₁ L₂) (e₂ : equiv R L₂ L₃) : equiv R L₁ L₃ :=
  mk (morphism.to_fun (morphism.comp (to_morphism e₂) (to_morphism e₁))) sorry sorry sorry
    (linear_equiv.inv_fun (linear_equiv.trans (to_linear_equiv e₁) (to_linear_equiv e₂))) sorry sorry

@[simp] theorem trans_apply {R : Type u} {L₁ : Type v} {L₂ : Type w} {L₃ : Type w₁} [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_ring L₃] [lie_algebra R L₁] [lie_algebra R L₂] [lie_algebra R L₃] (e₁ : equiv R L₁ L₂) (e₂ : equiv R L₂ L₃) (x : L₁) : coe_fn (trans e₁ e₂) x = coe_fn e₂ (coe_fn e₁ x) :=
  rfl

@[simp] theorem symm_trans_apply {R : Type u} {L₁ : Type v} {L₂ : Type w} {L₃ : Type w₁} [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_ring L₃] [lie_algebra R L₁] [lie_algebra R L₂] [lie_algebra R L₃] (e₁ : equiv R L₁ L₂) (e₂ : equiv R L₂ L₃) (x : L₃) : coe_fn (symm (trans e₁ e₂)) x = coe_fn (symm e₁) (coe_fn (symm e₂) x) :=
  rfl

end equiv


end lie_algebra


/-- A morphism of Lie algebra modules is a linear map which commutes with the action of the Lie
algebra. -/
structure lie_module_hom (R : Type u) (L : Type v) (M : Type w) (N : Type w₁) [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [add_comm_group N] [module R M] [module R N] [lie_ring_module L M] [lie_ring_module L N] [lie_module R L M] [lie_module R L N] 
extends linear_map R M N
where
  map_lie : ∀ {x : L} {m : M}, to_fun (has_bracket.bracket x m) = has_bracket.bracket x (to_fun m)

namespace lie_module_hom


protected instance linear_map.has_coe {R : Type u} {L : Type v} {M : Type w} {N : Type w₁} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [add_comm_group N] [module R M] [module R N] [lie_ring_module L M] [lie_ring_module L N] [lie_module R L M] [lie_module R L N] : has_coe (lie_module_hom R L M N) (linear_map R M N) :=
  has_coe.mk to_linear_map

/-- see Note [function coercion] -/
protected instance has_coe_to_fun {R : Type u} {L : Type v} {M : Type w} {N : Type w₁} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [add_comm_group N] [module R M] [module R N] [lie_ring_module L M] [lie_ring_module L N] [lie_module R L M] [lie_module R L N] : has_coe_to_fun (lie_module_hom R L M N) :=
  has_coe_to_fun.mk (fun (x : lie_module_hom R L M N) => M → N) to_fun

@[simp] theorem coe_mk {R : Type u} {L : Type v} {M : Type w} {N : Type w₁} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [add_comm_group N] [module R M] [module R N] [lie_ring_module L M] [lie_ring_module L N] [lie_module R L M] [lie_module R L N] (f : M → N) (h₁ : ∀ (x y : M), f (x + y) = f x + f y) (h₂ : ∀ (m : R) (x : M), f (m • x) = m • f x) (h₃ : ∀ {x : L} {m : M}, f (has_bracket.bracket x m) = has_bracket.bracket x (f m)) : ⇑(mk f h₁ h₂ h₃) = f :=
  rfl

@[simp] theorem coe_to_linear_map {R : Type u} {L : Type v} {M : Type w} {N : Type w₁} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [add_comm_group N] [module R M] [module R N] [lie_ring_module L M] [lie_ring_module L N] [lie_module R L M] [lie_module R L N] (f : lie_module_hom R L M N) : ⇑↑f = ⇑f :=
  rfl

@[simp] theorem map_lie' {R : Type u} {L : Type v} {M : Type w} {N : Type w₁} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [add_comm_group N] [module R M] [module R N] [lie_ring_module L M] [lie_ring_module L N] [lie_module R L M] [lie_module R L N] (f : lie_module_hom R L M N) (x : L) (m : M) : coe_fn f (has_bracket.bracket x m) = has_bracket.bracket x (coe_fn f m) :=
  map_lie f

/-- The constant 0 map is a Lie module morphism. -/
protected instance has_zero {R : Type u} {L : Type v} {M : Type w} {N : Type w₁} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [add_comm_group N] [module R M] [module R N] [lie_ring_module L M] [lie_ring_module L N] [lie_module R L M] [lie_module R L N] : HasZero (lie_module_hom R L M N) :=
  { zero := mk (linear_map.to_fun 0) sorry sorry sorry }

/-- The identity map is a Lie module morphism. -/
protected instance has_one {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] : HasOne (lie_module_hom R L M M) :=
  { one := mk (linear_map.to_fun 1) sorry sorry sorry }

protected instance inhabited {R : Type u} {L : Type v} {M : Type w} {N : Type w₁} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [add_comm_group N] [module R M] [module R N] [lie_ring_module L M] [lie_ring_module L N] [lie_module R L M] [lie_module R L N] : Inhabited (lie_module_hom R L M N) :=
  { default := 0 }

theorem coe_injective {R : Type u} {L : Type v} {M : Type w} {N : Type w₁} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [add_comm_group N] [module R M] [module R N] [lie_ring_module L M] [lie_ring_module L N] [lie_module R L M] [lie_module R L N] : function.injective fun (f : lie_module_hom R L M N) => (fun (this : M → N) => this) ⇑f := sorry

theorem ext {R : Type u} {L : Type v} {M : Type w} {N : Type w₁} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [add_comm_group N] [module R M] [module R N] [lie_ring_module L M] [lie_ring_module L N] [lie_module R L M] [lie_module R L N] {f : lie_module_hom R L M N} {g : lie_module_hom R L M N} (h : ∀ (m : M), coe_fn f m = coe_fn g m) : f = g :=
  coe_injective (funext h)

theorem ext_iff {R : Type u} {L : Type v} {M : Type w} {N : Type w₁} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [add_comm_group N] [module R M] [module R N] [lie_ring_module L M] [lie_ring_module L N] [lie_module R L M] [lie_module R L N] {f : lie_module_hom R L M N} {g : lie_module_hom R L M N} : f = g ↔ ∀ (m : M), coe_fn f m = coe_fn g m :=
  { mp := fun (ᾰ : f = g) (m : M) => Eq._oldrec (Eq.refl (coe_fn f m)) ᾰ, mpr := ext }

/-- The composition of Lie module morphisms is a morphism. -/
def comp {R : Type u} {L : Type v} {M : Type w} {N : Type w₁} {P : Type w₂} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [add_comm_group N] [add_comm_group P] [module R M] [module R N] [module R P] [lie_ring_module L M] [lie_ring_module L N] [lie_ring_module L P] [lie_module R L M] [lie_module R L N] [lie_module R L P] (f : lie_module_hom R L N P) (g : lie_module_hom R L M N) : lie_module_hom R L M P :=
  mk (linear_map.to_fun (linear_map.comp (to_linear_map f) (to_linear_map g))) sorry sorry sorry

@[simp] theorem comp_apply {R : Type u} {L : Type v} {M : Type w} {N : Type w₁} {P : Type w₂} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [add_comm_group N] [add_comm_group P] [module R M] [module R N] [module R P] [lie_ring_module L M] [lie_ring_module L N] [lie_ring_module L P] [lie_module R L M] [lie_module R L N] [lie_module R L P] (f : lie_module_hom R L N P) (g : lie_module_hom R L M N) (m : M) : coe_fn (comp f g) m = coe_fn f (coe_fn g m) :=
  rfl

theorem comp_coe {R : Type u} {L : Type v} {M : Type w} {N : Type w₁} {P : Type w₂} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [add_comm_group N] [add_comm_group P] [module R M] [module R N] [module R P] [lie_ring_module L M] [lie_ring_module L N] [lie_ring_module L P] [lie_module R L M] [lie_module R L N] [lie_module R L P] (f : lie_module_hom R L N P) (g : lie_module_hom R L M N) : ⇑f ∘ ⇑g = ⇑(comp f g) :=
  rfl

/-- The inverse of a bijective morphism of Lie modules is a morphism of Lie modules. -/
def inverse {R : Type u} {L : Type v} {M : Type w} {N : Type w₁} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [add_comm_group N] [module R M] [module R N] [lie_ring_module L M] [lie_ring_module L N] [lie_module R L M] [lie_module R L N] (f : lie_module_hom R L M N) (g : N → M) (h₁ : function.left_inverse g ⇑f) (h₂ : function.right_inverse g ⇑f) : lie_module_hom R L N M :=
  mk (linear_map.to_fun (linear_map.inverse (to_linear_map f) g h₁ h₂)) sorry sorry sorry

end lie_module_hom


/-- An equivalence of Lie algebra modules is a linear equivalence which is also a morphism of
Lie algebra modules. -/
structure lie_module_equiv (R : Type u) (L : Type v) (M : Type w) (N : Type w₁) [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [add_comm_group N] [module R M] [module R N] [lie_ring_module L M] [lie_ring_module L N] [lie_module R L M] [lie_module R L N] 
extends linear_equiv R M N, lie_module_hom R L M N
where

namespace lie_module_equiv


protected instance has_coe_to_lie_module_hom {R : Type u} {L : Type v} {M : Type w} {N : Type w₁} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [add_comm_group N] [module R M] [module R N] [lie_ring_module L M] [lie_ring_module L N] [lie_module R L M] [lie_module R L N] : has_coe (lie_module_equiv R L M N) (lie_module_hom R L M N) :=
  has_coe.mk to_lie_module_hom

protected instance has_coe_to_linear_equiv {R : Type u} {L : Type v} {M : Type w} {N : Type w₁} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [add_comm_group N] [module R M] [module R N] [lie_ring_module L M] [lie_ring_module L N] [lie_module R L M] [lie_module R L N] : has_coe (lie_module_equiv R L M N) (linear_equiv R M N) :=
  has_coe.mk to_linear_equiv

/-- see Note [function coercion] -/
protected instance has_coe_to_fun {R : Type u} {L : Type v} {M : Type w} {N : Type w₁} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [add_comm_group N] [module R M] [module R N] [lie_ring_module L M] [lie_ring_module L N] [lie_module R L M] [lie_module R L N] : has_coe_to_fun (lie_module_equiv R L M N) :=
  has_coe_to_fun.mk (fun (x : lie_module_equiv R L M N) => M → N) to_fun

@[simp] theorem coe_to_lie_module_hom {R : Type u} {L : Type v} {M : Type w} {N : Type w₁} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [add_comm_group N] [module R M] [module R N] [lie_ring_module L M] [lie_ring_module L N] [lie_module R L M] [lie_module R L N] (e : lie_module_equiv R L M N) : ⇑↑e = ⇑e :=
  rfl

@[simp] theorem coe_to_linear_equiv {R : Type u} {L : Type v} {M : Type w} {N : Type w₁} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [add_comm_group N] [module R M] [module R N] [lie_ring_module L M] [lie_ring_module L N] [lie_module R L M] [lie_module R L N] (e : lie_module_equiv R L M N) : ⇑↑e = ⇑e :=
  rfl

protected instance has_one {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] : HasOne (lie_module_equiv R L M M) :=
  { one := mk (linear_equiv.to_fun 1) sorry sorry (linear_equiv.inv_fun 1) sorry sorry sorry }

@[simp] theorem one_apply {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (m : M) : coe_fn 1 m = m :=
  rfl

protected instance inhabited {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] : Inhabited (lie_module_equiv R L M M) :=
  { default := 1 }

/-- Lie module equivalences are reflexive. -/
def refl {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] : lie_module_equiv R L M M :=
  1

@[simp] theorem refl_apply {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (m : M) : coe_fn refl m = m :=
  rfl

/-- Lie module equivalences are syemmtric. -/
def symm {R : Type u} {L : Type v} {M : Type w} {N : Type w₁} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [add_comm_group N] [module R M] [module R N] [lie_ring_module L M] [lie_ring_module L N] [lie_module R L M] [lie_module R L N] (e : lie_module_equiv R L M N) : lie_module_equiv R L N M :=
  mk (lie_module_hom.to_fun (lie_module_hom.inverse (to_lie_module_hom e) (inv_fun e) (left_inv e) (right_inv e))) sorry
    sorry (linear_equiv.inv_fun (linear_equiv.symm ↑e)) sorry sorry sorry

@[simp] theorem symm_symm {R : Type u} {L : Type v} {M : Type w} {N : Type w₁} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [add_comm_group N] [module R M] [module R N] [lie_ring_module L M] [lie_ring_module L N] [lie_module R L M] [lie_module R L N] (e : lie_module_equiv R L M N) : symm (symm e) = e := sorry

@[simp] theorem apply_symm_apply {R : Type u} {L : Type v} {M : Type w} {N : Type w₁} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [add_comm_group N] [module R M] [module R N] [lie_ring_module L M] [lie_ring_module L N] [lie_module R L M] [lie_module R L N] (e : lie_module_equiv R L M N) (x : N) : coe_fn e (coe_fn (symm e) x) = x :=
  linear_equiv.apply_symm_apply (to_linear_equiv e)

@[simp] theorem symm_apply_apply {R : Type u} {L : Type v} {M : Type w} {N : Type w₁} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [add_comm_group N] [module R M] [module R N] [lie_ring_module L M] [lie_ring_module L N] [lie_module R L M] [lie_module R L N] (e : lie_module_equiv R L M N) (x : M) : coe_fn (symm e) (coe_fn e x) = x :=
  linear_equiv.symm_apply_apply (to_linear_equiv e)

/-- Lie module equivalences are transitive. -/
def trans {R : Type u} {L : Type v} {M : Type w} {N : Type w₁} {P : Type w₂} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [add_comm_group N] [add_comm_group P] [module R M] [module R N] [module R P] [lie_ring_module L M] [lie_ring_module L N] [lie_ring_module L P] [lie_module R L M] [lie_module R L N] [lie_module R L P] (e₁ : lie_module_equiv R L M N) (e₂ : lie_module_equiv R L N P) : lie_module_equiv R L M P :=
  mk (lie_module_hom.to_fun (lie_module_hom.comp (to_lie_module_hom e₂) (to_lie_module_hom e₁))) sorry sorry
    (linear_equiv.inv_fun (linear_equiv.trans (to_linear_equiv e₁) (to_linear_equiv e₂))) sorry sorry sorry

@[simp] theorem trans_apply {R : Type u} {L : Type v} {M : Type w} {N : Type w₁} {P : Type w₂} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [add_comm_group N] [add_comm_group P] [module R M] [module R N] [module R P] [lie_ring_module L M] [lie_ring_module L N] [lie_ring_module L P] [lie_module R L M] [lie_module R L N] [lie_module R L P] (e₁ : lie_module_equiv R L M N) (e₂ : lie_module_equiv R L N P) (m : M) : coe_fn (trans e₁ e₂) m = coe_fn e₂ (coe_fn e₁ m) :=
  rfl

@[simp] theorem symm_trans_apply {R : Type u} {L : Type v} {M : Type w} {N : Type w₁} {P : Type w₂} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [add_comm_group N] [add_comm_group P] [module R M] [module R N] [module R P] [lie_ring_module L M] [lie_ring_module L N] [lie_ring_module L P] [lie_module R L M] [lie_module R L N] [lie_module R L P] (e₁ : lie_module_equiv R L M N) (e₂ : lie_module_equiv R L N P) (p : P) : coe_fn (symm (trans e₁ e₂)) p = coe_fn (symm e₁) (coe_fn (symm e₂) p) :=
  rfl

end lie_module_equiv


namespace ring_commutator


/-- The bracket operation for rings is the ring commutator, which captures the extent to which a
ring is commutative. It is identically zero exactly when the ring is commutative. -/
protected instance has_bracket {A : Type v} [ring A] : has_bracket A A :=
  has_bracket.mk fun (x y : A) => x * y - y * x

theorem commutator {A : Type v} [ring A] (x : A) (y : A) : has_bracket.bracket x y = x * y - y * x :=
  rfl

end ring_commutator


namespace lie_ring


/-- An associative ring gives rise to a Lie ring by taking the bracket to be the ring commutator. -/
protected instance of_associative_ring {A : Type v} [ring A] : lie_ring A :=
  mk sorry sorry sorry sorry

theorem of_associative_ring_bracket {A : Type v} [ring A] (x : A) (y : A) : has_bracket.bracket x y = x * y - y * x :=
  rfl

end lie_ring


/-- A Lie (ring) module is trivial iff all brackets vanish. -/
class lie_module.is_trivial (L : Type v) (M : Type w) [has_bracket L M] [HasZero M] 
where
  trivial : ∀ (x : L) (m : M), has_bracket.bracket x m = 0

@[simp] theorem trivial_lie_zero (L : Type v) (M : Type w) [has_bracket L M] [HasZero M] [lie_module.is_trivial L M] (x : L) (m : M) : has_bracket.bracket x m = 0 :=
  lie_module.is_trivial.trivial x m

/-- A Lie algebra is Abelian iff it is trivial as a Lie module over itself. -/
def is_lie_abelian (L : Type v) [has_bracket L L] [HasZero L]  :=
  lie_module.is_trivial L L

theorem commutative_ring_iff_abelian_lie_ring {A : Type v} [ring A] : is_commutative A Mul.mul ↔ is_lie_abelian A := sorry

namespace lie_algebra


/-- An associative algebra gives rise to a Lie algebra by taking the bracket to be the ring
commutator. -/
protected instance of_associative_algebra {A : Type v} [ring A] {R : Type u} [comm_ring R] [algebra R A] : lie_algebra R A :=
  mk sorry

/-- The map `of_associative_algebra` associating a Lie algebra to an associative algebra is
functorial. -/
def of_associative_algebra_hom {A : Type v} [ring A] {R : Type u} [comm_ring R] [algebra R A] {B : Type w} [ring B] [algebra R B] (f : alg_hom R A B) : morphism R A B :=
  morphism.mk (linear_map.to_fun (alg_hom.to_linear_map f)) sorry sorry sorry

@[simp] theorem of_associative_algebra_hom_id {A : Type v} [ring A] {R : Type u} [comm_ring R] [algebra R A] : of_associative_algebra_hom (alg_hom.id R A) = 1 :=
  rfl

@[simp] theorem of_associative_algebra_hom_apply {A : Type v} [ring A] {R : Type u} [comm_ring R] [algebra R A] {B : Type w} [ring B] [algebra R B] (f : alg_hom R A B) (x : A) : coe_fn (of_associative_algebra_hom f) x = coe_fn f x :=
  rfl

@[simp] theorem of_associative_algebra_hom_comp {A : Type v} [ring A] {R : Type u} [comm_ring R] [algebra R A] {B : Type w} {C : Type w₁} [ring B] [ring C] [algebra R B] [algebra R C] (f : alg_hom R A B) (g : alg_hom R B C) : of_associative_algebra_hom (alg_hom.comp g f) =
  morphism.comp (of_associative_algebra_hom g) (of_associative_algebra_hom f) :=
  rfl

end lie_algebra


/-- A Lie module yields a Lie algebra morphism into the linear endomorphisms of the module. -/
def lie_module.to_endo_morphism (R : Type u) (L : Type v) (M : Type w) [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] : lie_algebra.morphism R L (module.End R M) :=
  lie_algebra.morphism.mk (fun (x : L) => linear_map.mk (fun (m : M) => has_bracket.bracket x m) (lie_add x) sorry) sorry
    sorry sorry

/-- The adjoint action of a Lie algebra on itself. -/
def lie_algebra.ad (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] [lie_algebra R L] : lie_algebra.morphism R L (module.End R L) :=
  lie_module.to_endo_morphism R L L

@[simp] theorem lie_algebra.ad_apply (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] [lie_algebra R L] (x : L) (y : L) : coe_fn (coe_fn (lie_algebra.ad R L) x) y = has_bracket.bracket x y :=
  rfl

/-- A Lie subalgebra of a Lie algebra is submodule that is closed under the Lie bracket.
This is a sufficient condition for the subset itself to form a Lie algebra. -/
structure lie_subalgebra (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] [lie_algebra R L] 
extends submodule R L
where
  lie_mem' : ∀ {x y : L}, x ∈ carrier → y ∈ carrier → has_bracket.bracket x y ∈ carrier

/-- The zero algebra is a subalgebra of any Lie algebra. -/
protected instance lie_subalgebra.has_zero (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] [lie_algebra R L] : HasZero (lie_subalgebra R L) :=
  { zero := lie_subalgebra.mk (submodule.carrier 0) sorry sorry sorry sorry }

protected instance lie_subalgebra.inhabited (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] [lie_algebra R L] : Inhabited (lie_subalgebra R L) :=
  { default := 0 }

protected instance set.has_coe (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] [lie_algebra R L] : has_coe (lie_subalgebra R L) (set L) :=
  has_coe.mk lie_subalgebra.carrier

protected instance lie_subalgebra.has_mem (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] [lie_algebra R L] : has_mem L (lie_subalgebra R L) :=
  has_mem.mk fun (x : L) (L' : lie_subalgebra R L) => x ∈ ↑L'

protected instance lie_subalgebra_coe_submodule (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] [lie_algebra R L] : has_coe (lie_subalgebra R L) (submodule R L) :=
  has_coe.mk lie_subalgebra.to_submodule

/-- A Lie subalgebra forms a new Lie ring. -/
protected instance lie_subalgebra_lie_ring (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] [lie_algebra R L] (L' : lie_subalgebra R L) : lie_ring ↥L' :=
  lie_ring.mk sorry sorry sorry sorry

/-- A Lie subalgebra forms a new Lie algebra. -/
protected instance lie_subalgebra_lie_algebra (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] [lie_algebra R L] (L' : lie_subalgebra R L) : lie_algebra R ↥L' :=
  lie_algebra.mk sorry

namespace lie_subalgebra


@[simp] theorem zero_mem {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] (L' : lie_subalgebra R L) : 0 ∈ L' :=
  submodule.zero_mem ↑L'

theorem smul_mem {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] (L' : lie_subalgebra R L) (t : R) {x : L} (h : x ∈ L') : t • x ∈ L' :=
  submodule.smul_mem (↑L') t h

theorem add_mem {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] (L' : lie_subalgebra R L) {x : L} {y : L} (hx : x ∈ L') (hy : y ∈ L') : x + y ∈ L' :=
  submodule.add_mem (↑L') hx hy

theorem lie_mem {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] (L' : lie_subalgebra R L) {x : L} {y : L} (hx : x ∈ L') (hy : y ∈ L') : has_bracket.bracket x y ∈ L' :=
  lie_mem' L' hx hy

@[simp] theorem mem_coe {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] (L' : lie_subalgebra R L) {x : L} : x ∈ ↑L' ↔ x ∈ L' :=
  iff.rfl

@[simp] theorem mem_coe' {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] (L' : lie_subalgebra R L) {x : L} : x ∈ ↑L' ↔ x ∈ L' :=
  iff.rfl

@[simp] theorem coe_bracket {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] (L' : lie_subalgebra R L) (x : ↥L') (y : ↥L') : ↑(has_bracket.bracket x y) = has_bracket.bracket ↑x ↑y :=
  rfl

theorem ext {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] (L₁' : lie_subalgebra R L) (L₂' : lie_subalgebra R L) (h : ∀ (x : L), x ∈ L₁' ↔ x ∈ L₂') : L₁' = L₂' := sorry

theorem ext_iff {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] (L₁' : lie_subalgebra R L) (L₂' : lie_subalgebra R L) : L₁' = L₂' ↔ ∀ (x : L), x ∈ L₁' ↔ x ∈ L₂' :=
  { mp := fun (h : L₁' = L₂') (x : L) => eq.mpr (id (Eq._oldrec (Eq.refl (x ∈ L₁' ↔ x ∈ L₂')) h)) (iff.refl (x ∈ L₂')),
    mpr := ext L₁' L₂' }

@[simp] theorem mk_coe {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] (S : set L) (h₁ : 0 ∈ S) (h₂ : ∀ {a b : L}, a ∈ S → b ∈ S → a + b ∈ S) (h₃ : ∀ (c : R) {x : L}, x ∈ S → c • x ∈ S) (h₄ : ∀ {x y : L}, x ∈ S → y ∈ S → has_bracket.bracket x y ∈ S) : ↑(mk S h₁ h₂ h₃ h₄) = S :=
  rfl

theorem coe_injective {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] : function.injective coe := sorry

@[simp] theorem coe_set_eq {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] (L₁' : lie_subalgebra R L) (L₂' : lie_subalgebra R L) : ↑L₁' = ↑L₂' ↔ L₁' = L₂' :=
  function.injective.eq_iff coe_injective

theorem to_submodule_injective {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] : function.injective coe :=
  fun (L₁' L₂' : lie_subalgebra R L) (h : ↑L₁' = ↑L₂') =>
    eq.mpr (id (Eq._oldrec (Eq.refl (L₁' = L₂')) (Eq.symm (propext (coe_set_eq L₁' L₂')))))
      (eq.mp (Eq._oldrec (Eq.refl (↑L₁' = ↑L₂')) (propext submodule.ext'_iff)) h)

@[simp] theorem coe_to_submodule_eq {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] (L₁' : lie_subalgebra R L) (L₂' : lie_subalgebra R L) : ↑L₁' = ↑L₂' ↔ L₁' = L₂' :=
  function.injective.eq_iff to_submodule_injective

end lie_subalgebra


/-- A subalgebra of an associative algebra is a Lie subalgebra of the associated Lie algebra. -/
def lie_subalgebra_of_subalgebra (R : Type u) [comm_ring R] (A : Type v) [ring A] [algebra R A] (A' : subalgebra R A) : lie_subalgebra R A :=
  lie_subalgebra.mk (submodule.carrier (subalgebra.to_submodule A')) sorry sorry sorry sorry

/-- The embedding of a Lie subalgebra into the ambient space as a Lie morphism. -/
def lie_subalgebra.incl {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] (L' : lie_subalgebra R L) : lie_algebra.morphism R (↥L') L :=
  lie_algebra.morphism.mk (linear_map.to_fun (submodule.subtype (lie_subalgebra.to_submodule L'))) sorry sorry sorry

/-- The range of a morphism of Lie algebras is a Lie subalgebra. -/
def lie_algebra.morphism.range {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] {L₂ : Type w} [lie_ring L₂] [lie_algebra R L₂] (f : lie_algebra.morphism R L L₂) : lie_subalgebra R L₂ :=
  lie_subalgebra.mk (submodule.carrier (linear_map.range (lie_algebra.morphism.to_linear_map f))) sorry sorry sorry sorry

@[simp] theorem lie_algebra.morphism.range_bracket {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] {L₂ : Type w} [lie_ring L₂] [lie_algebra R L₂] (f : lie_algebra.morphism R L L₂) (x : ↥(lie_algebra.morphism.range f)) (y : ↥(lie_algebra.morphism.range f)) : ↑(has_bracket.bracket x y) = has_bracket.bracket ↑x ↑y :=
  rfl

@[simp] theorem lie_algebra.morphism.range_coe {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] {L₂ : Type w} [lie_ring L₂] [lie_algebra R L₂] (f : lie_algebra.morphism R L L₂) : ↑(lie_algebra.morphism.range f) = set.range ⇑f :=
  linear_map.range_coe ↑f

@[simp] theorem lie_subalgebra.range_incl {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] (L' : lie_subalgebra R L) : lie_algebra.morphism.range (lie_subalgebra.incl L') = L' := sorry

/-- The image of a Lie subalgebra under a Lie algebra morphism is a Lie subalgebra of the
codomain. -/
def lie_subalgebra.map {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] {L₂ : Type w} [lie_ring L₂] [lie_algebra R L₂] (f : lie_algebra.morphism R L L₂) (L' : lie_subalgebra R L) : lie_subalgebra R L₂ :=
  lie_subalgebra.mk (submodule.carrier (submodule.map ↑f ↑L')) sorry sorry sorry sorry

@[simp] theorem lie_subalgebra.mem_map_submodule {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] {L₂ : Type w} [lie_ring L₂] [lie_algebra R L₂] (e : lie_algebra.equiv R L L₂) (L' : lie_subalgebra R L) (x : L₂) : x ∈ lie_subalgebra.map (↑e) L' ↔ x ∈ submodule.map ↑e ↑L' :=
  iff.rfl

namespace lie_algebra


namespace equiv


/-- An injective Lie algebra morphism is an equivalence onto its range. -/
def of_injective {R : Type u} {L₁ : Type v} {L₂ : Type w} [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_algebra R L₁] [lie_algebra R L₂] (f : morphism R L₁ L₂) (h : function.injective ⇑f) : equiv R L₁ ↥(morphism.range f) :=
  (fun (h' : linear_map.ker ↑f = ⊥) =>
      mk (linear_equiv.to_fun (linear_equiv.of_injective (↑f) h')) sorry sorry sorry
        (linear_equiv.inv_fun (linear_equiv.of_injective (↑f) h')) sorry sorry)
    sorry

@[simp] theorem of_injective_apply {R : Type u} {L₁ : Type v} {L₂ : Type w} [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_algebra R L₁] [lie_algebra R L₂] (f : morphism R L₁ L₂) (h : function.injective ⇑f) (x : L₁) : ↑(coe_fn (of_injective f h) x) = coe_fn f x :=
  rfl

/-- Lie subalgebras that are equal as sets are equivalent as Lie algebras. -/
def of_eq {R : Type u} {L₁ : Type v} [comm_ring R] [lie_ring L₁] [lie_algebra R L₁] (L₁' : lie_subalgebra R L₁) (L₁'' : lie_subalgebra R L₁) (h : ↑L₁' = ↑L₁'') : equiv R ↥L₁' ↥L₁'' :=
  mk (linear_equiv.to_fun (linear_equiv.of_eq ↑L₁' ↑L₁'' sorry)) sorry sorry sorry
    (linear_equiv.inv_fun (linear_equiv.of_eq ↑L₁' ↑L₁'' sorry)) sorry sorry

@[simp] theorem of_eq_apply {R : Type u} {L₁ : Type v} [comm_ring R] [lie_ring L₁] [lie_algebra R L₁] (L : lie_subalgebra R L₁) (L' : lie_subalgebra R L₁) (h : ↑L = ↑L') (x : ↥L) : ↑(coe_fn (of_eq L L' h) x) = ↑x :=
  rfl

/-- An equivalence of Lie algebras restricts to an equivalence from any Lie subalgebra onto its
image. -/
def of_subalgebra {R : Type u} {L₁ : Type v} {L₂ : Type w} [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_algebra R L₁] [lie_algebra R L₂] (L₁'' : lie_subalgebra R L₁) (e : equiv R L₁ L₂) : equiv R ↥L₁'' ↥(lie_subalgebra.map (↑e) L₁'') :=
  mk (linear_equiv.to_fun (linear_equiv.of_submodule ↑e ↑L₁'')) sorry sorry sorry
    (linear_equiv.inv_fun (linear_equiv.of_submodule ↑e ↑L₁'')) sorry sorry

@[simp] theorem of_subalgebra_apply {R : Type u} {L₁ : Type v} {L₂ : Type w} [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_algebra R L₁] [lie_algebra R L₂] (L₁'' : lie_subalgebra R L₁) (e : equiv R L₁ L₂) (x : ↥L₁'') : ↑(coe_fn (of_subalgebra L₁'' e) x) = coe_fn e ↑x :=
  rfl

/-- An equivalence of Lie algebras restricts to an equivalence from any Lie subalgebra onto its
image. -/
def of_subalgebras {R : Type u} {L₁ : Type v} {L₂ : Type w} [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_algebra R L₁] [lie_algebra R L₂] (L₁' : lie_subalgebra R L₁) (L₂' : lie_subalgebra R L₂) (e : equiv R L₁ L₂) (h : lie_subalgebra.map (↑e) L₁' = L₂') : equiv R ↥L₁' ↥L₂' :=
  mk (linear_equiv.to_fun (linear_equiv.of_submodules ↑e ↑L₁' ↑L₂' sorry)) sorry sorry sorry
    (linear_equiv.inv_fun (linear_equiv.of_submodules ↑e ↑L₁' ↑L₂' sorry)) sorry sorry

@[simp] theorem of_subalgebras_apply {R : Type u} {L₁ : Type v} {L₂ : Type w} [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_algebra R L₁] [lie_algebra R L₂] (L₁' : lie_subalgebra R L₁) (L₂' : lie_subalgebra R L₂) (e : equiv R L₁ L₂) (h : lie_subalgebra.map (↑e) L₁' = L₂') (x : ↥L₁') : ↑(coe_fn (of_subalgebras L₁' L₂' e h) x) = coe_fn e ↑x :=
  rfl

@[simp] theorem of_subalgebras_symm_apply {R : Type u} {L₁ : Type v} {L₂ : Type w} [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_algebra R L₁] [lie_algebra R L₂] (L₁' : lie_subalgebra R L₁) (L₂' : lie_subalgebra R L₂) (e : equiv R L₁ L₂) (h : lie_subalgebra.map (↑e) L₁' = L₂') (x : ↥L₂') : ↑(coe_fn (symm (of_subalgebras L₁' L₂' e h)) x) = coe_fn (symm e) ↑x :=
  rfl

end equiv


end lie_algebra


/-- A Lie submodule of a Lie module is a submodule that is closed under the Lie bracket.
This is a sufficient condition for the subset itself to form a Lie module. -/
structure lie_submodule (R : Type u) (L : Type v) (M : Type w) [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] 
extends submodule R M
where
  lie_mem : ∀ {x : L} {m : M}, m ∈ carrier → has_bracket.bracket x m ∈ carrier

namespace lie_submodule


/-- The zero module is a Lie submodule of any Lie module. -/
protected instance has_zero {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] : HasZero (lie_submodule R L M) :=
  { zero := mk (submodule.carrier 0) sorry sorry sorry sorry }

protected instance inhabited {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] : Inhabited (lie_submodule R L M) :=
  { default := 0 }

protected instance coe_submodule {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] : has_coe (lie_submodule R L M) (submodule R M) :=
  has_coe.mk to_submodule

theorem coe_to_submodule {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L M) : ↑↑N = ↑N :=
  rfl

protected instance has_mem {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] : has_mem M (lie_submodule R L M) :=
  has_mem.mk fun (x : M) (N : lie_submodule R L M) => x ∈ ↑N

@[simp] theorem mem_carrier {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L M) {x : M} : x ∈ carrier N ↔ x ∈ ↑N :=
  iff.rfl

@[simp] theorem mem_coe_submodule {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L M) {x : M} : x ∈ ↑N ↔ x ∈ N :=
  iff.rfl

theorem mem_coe {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L M) {x : M} : x ∈ ↑N ↔ x ∈ N :=
  iff.rfl

@[simp] theorem zero_mem {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L M) : 0 ∈ N :=
  submodule.zero_mem ↑N

@[simp] theorem coe_to_set_mk {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (S : set M) (h₁ : 0 ∈ S) (h₂ : ∀ {a b : M}, a ∈ S → b ∈ S → a + b ∈ S) (h₃ : ∀ (c : R) {x : M}, x ∈ S → c • x ∈ S) (h₄ : ∀ {x : L} {m : M}, m ∈ S → has_bracket.bracket x m ∈ S) : ↑(mk S h₁ h₂ h₃ h₄) = S :=
  rfl

@[simp] theorem coe_to_submodule_mk {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (p : submodule R M) (h : ∀ {x : L} {m : M}, m ∈ submodule.carrier p → has_bracket.bracket x m ∈ submodule.carrier p) : ↑(mk (submodule.carrier p) (submodule.zero_mem' p) (submodule.add_mem' p) (submodule.smul_mem' p) h) = p := sorry

theorem ext {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L M) (N' : lie_submodule R L M) (h : ∀ (m : M), m ∈ N ↔ m ∈ N') : N = N' := sorry

@[simp] theorem coe_to_submodule_eq_iff {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L M) (N' : lie_submodule R L M) : ↑N = ↑N' ↔ N = N' := sorry

protected instance lie_ring_module {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L M) : lie_ring_module L ↥N :=
  lie_ring_module.mk sorry sorry sorry

protected instance lie_module {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L M) : lie_module R L ↥N :=
  lie_module.mk sorry sorry

end lie_submodule


/-- An ideal of a Lie algebra is a Lie submodule of the Lie algebra as a Lie module over itself. -/
def lie_ideal (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] [lie_algebra R L]  :=
  lie_submodule R L L

theorem lie_mem_right (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] [lie_algebra R L] (I : lie_ideal R L) (x : L) (y : L) (h : y ∈ I) : has_bracket.bracket x y ∈ I :=
  lie_submodule.lie_mem I h

theorem lie_mem_left (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] [lie_algebra R L] (I : lie_ideal R L) (x : L) (y : L) (h : x ∈ I) : has_bracket.bracket x y ∈ I :=
  eq.mpr (id (Eq._oldrec (Eq.refl (has_bracket.bracket x y ∈ I)) (Eq.symm (lie_skew x y))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (-has_bracket.bracket y x ∈ I)) (Eq.symm (neg_lie y x))))
      (lie_mem_right R L I (-y) x h))

/-- An ideal of a Lie algebra is a Lie subalgebra. -/
def lie_ideal_subalgebra (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] [lie_algebra R L] (I : lie_ideal R L) : lie_subalgebra R L :=
  lie_subalgebra.mk (submodule.carrier (lie_submodule.to_submodule I)) sorry sorry sorry sorry

protected instance lie_subalgebra.has_coe (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] [lie_algebra R L] : has_coe (lie_ideal R L) (lie_subalgebra R L) :=
  has_coe.mk fun (I : lie_ideal R L) => lie_ideal_subalgebra R L I

theorem lie_ideal.coe_to_subalgebra (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] [lie_algebra R L] (I : lie_ideal R L) : ↑↑I = ↑I :=
  rfl

namespace lie_submodule


theorem coe_injective {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] : function.injective coe := sorry

theorem coe_submodule_injective {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] : function.injective coe := sorry

protected instance partial_order {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] : partial_order (lie_submodule R L M) :=
  partial_order.mk (fun (N N' : lie_submodule R L M) => ∀ {x : M}, x ∈ N → x ∈ N') partial_order.lt sorry sorry sorry

theorem le_def {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L M) (N' : lie_submodule R L M) : N ≤ N' ↔ ↑N ⊆ ↑N' :=
  iff.rfl

@[simp] theorem coe_submodule_le_coe_submodule {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L M) (N' : lie_submodule R L M) : ↑N ≤ ↑N' ↔ N ≤ N' :=
  iff.rfl

protected instance has_bot {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] : has_bot (lie_submodule R L M) :=
  has_bot.mk 0

@[simp] theorem bot_coe {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] : ↑⊥ = singleton 0 :=
  rfl

@[simp] theorem bot_coe_submodule {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] : ↑⊥ = ⊥ :=
  rfl

@[simp] theorem mem_bot {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (x : M) : x ∈ ⊥ ↔ x = 0 :=
  set.mem_singleton_iff

protected instance has_top {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] : has_top (lie_submodule R L M) :=
  has_top.mk (mk (submodule.carrier ⊤) sorry sorry sorry sorry)

@[simp] theorem top_coe {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] : ↑⊤ = set.univ :=
  rfl

@[simp] theorem top_coe_submodule {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] : ↑⊤ = ⊤ :=
  rfl

theorem mem_top {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (x : M) : x ∈ ⊤ :=
  set.mem_univ x

protected instance has_inf {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] : has_inf (lie_submodule R L M) :=
  has_inf.mk fun (N N' : lie_submodule R L M) => mk (submodule.carrier (↑N ⊓ ↑N')) sorry sorry sorry sorry

protected instance has_Inf {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] : has_Inf (lie_submodule R L M) :=
  has_Inf.mk
    fun (S : set (lie_submodule R L M)) =>
      mk
        (submodule.carrier (Inf (set_of fun (_x : submodule R M) => ∃ (s : lie_submodule R L M), ∃ (H : s ∈ S), ↑s = _x)))
        sorry sorry sorry sorry

@[simp] theorem inf_coe {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L M) (N' : lie_submodule R L M) : ↑(N ⊓ N') = ↑N ∩ ↑N' :=
  rfl

@[simp] theorem Inf_coe_to_submodule {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (S : set (lie_submodule R L M)) : ↑(Inf S) = Inf (set_of fun (_x : submodule R M) => ∃ (s : lie_submodule R L M), ∃ (H : s ∈ S), ↑s = _x) :=
  rfl

@[simp] theorem Inf_coe {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (S : set (lie_submodule R L M)) : ↑(Inf S) = set.Inter fun (s : lie_submodule R L M) => set.Inter fun (H : s ∈ S) => ↑s := sorry

theorem Inf_glb {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (S : set (lie_submodule R L M)) : is_glb S (Inf S) := sorry

/-- The set of Lie submodules of a Lie module form a complete lattice.

We provide explicit values for the fields `bot`, `top`, `inf` to get more convenient definitions
than we would otherwise obtain from `complete_lattice_of_Inf`.  -/
protected instance complete_lattice {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] : complete_lattice (lie_submodule R L M) :=
  complete_lattice.mk complete_lattice.sup complete_lattice.le complete_lattice.lt sorry sorry sorry sorry sorry sorry
    has_inf.inf sorry sorry sorry ⊤ sorry ⊥ sorry complete_lattice.Sup complete_lattice.Inf sorry sorry sorry sorry

protected instance add_comm_monoid {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] : add_comm_monoid (lie_submodule R L M) :=
  add_comm_monoid.mk has_sup.sup sorry ⊥ sorry sorry sorry

@[simp] theorem add_eq_sup {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L M) (N' : lie_submodule R L M) : N + N' = N ⊔ N' :=
  rfl

@[simp] theorem sup_coe_to_submodule {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L M) (N' : lie_submodule R L M) : ↑(N ⊔ N') = ↑N ⊔ ↑N' := sorry

@[simp] theorem inf_coe_to_submodule {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L M) (N' : lie_submodule R L M) : ↑(N ⊓ N') = ↑N ⊓ ↑N' :=
  rfl

@[simp] theorem mem_inf {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L M) (N' : lie_submodule R L M) (x : M) : x ∈ N ⊓ N' ↔ x ∈ N ∧ x ∈ N' := sorry

theorem mem_sup {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L M) (N' : lie_submodule R L M) (x : M) : x ∈ N ⊔ N' ↔ ∃ (y : M), ∃ (H : y ∈ N), ∃ (z : M), ∃ (H : z ∈ N'), y + z = x := sorry

theorem eq_bot_iff {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L M) : N = ⊥ ↔ ∀ (m : M), m ∈ N → m = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (N = ⊥ ↔ ∀ (m : M), m ∈ N → m = 0)) (propext eq_bot_iff))) iff.rfl

theorem of_bot_eq_bot {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L ↥⊥) : N = ⊥ := sorry

theorem unique_of_bot {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L ↥⊥) (N' : lie_submodule R L ↥⊥) : N = N' :=
  eq.mpr (id (Eq._oldrec (Eq.refl (N = N')) (of_bot_eq_bot N)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (⊥ = N')) (of_bot_eq_bot N'))) (Eq.refl ⊥))

/-- The inclusion of a Lie submodule into its ambient space is a morphism of Lie modules. -/
def incl {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L M) : lie_module_hom R L (↥N) M :=
  lie_module_hom.mk (linear_map.to_fun (submodule.subtype ↑N)) sorry sorry sorry

@[simp] theorem incl_apply {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L M) (m : ↥N) : coe_fn (incl N) m = ↑m :=
  rfl

theorem incl_eq_val {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L M) : ⇑(incl N) = subtype.val :=
  rfl

/-- Given two nested Lie submodules `N ⊆ N'`, the inclusion `N ↪ N'` is a morphism of Lie modules.-/
def hom_of_le {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] {N : lie_submodule R L M} {N' : lie_submodule R L M} (h : N ≤ N') : lie_module_hom R L ↥N ↥N' :=
  lie_module_hom.mk (linear_map.to_fun (submodule.of_le h)) sorry sorry sorry

@[simp] theorem coe_hom_of_le {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] {N : lie_submodule R L M} {N' : lie_submodule R L M} (h : N ≤ N') (m : ↥N) : ↑(coe_fn (hom_of_le h) m) = ↑m :=
  rfl

theorem hom_of_le_apply {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] {N : lie_submodule R L M} {N' : lie_submodule R L M} (h : N ≤ N') (m : ↥N) : coe_fn (hom_of_le h) m = { val := subtype.val m, property := h (subtype.property m) } :=
  rfl

/-- The `lie_span` of a set `s ⊆ M` is the smallest Lie submodule of `M` that contains `s`. -/
def lie_span (R : Type u) (L : Type v) {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (s : set M) : lie_submodule R L M :=
  Inf (set_of fun (N : lie_submodule R L M) => s ⊆ ↑N)

theorem mem_lie_span {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] {s : set M} {x : M} : x ∈ lie_span R L s ↔ ∀ (N : lie_submodule R L M), s ⊆ ↑N → x ∈ N := sorry

theorem subset_lie_span {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] {s : set M} : s ⊆ ↑(lie_span R L s) := sorry

theorem submodule_span_le_lie_span {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] {s : set M} : submodule.span R s ≤ ↑(lie_span R L s) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (submodule.span R s ≤ ↑(lie_span R L s))) (propext submodule.span_le)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (s ⊆ ↑↑(lie_span R L s))) (coe_to_submodule (lie_span R L s)))) subset_lie_span)

theorem lie_span_le {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] {s : set M} {N : lie_submodule R L M} : lie_span R L s ≤ N ↔ s ⊆ ↑N := sorry

theorem lie_span_mono {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] {s : set M} {t : set M} (h : s ⊆ t) : lie_span R L s ≤ lie_span R L t :=
  eq.mpr (id (Eq._oldrec (Eq.refl (lie_span R L s ≤ lie_span R L t)) (propext lie_span_le)))
    (set.subset.trans h subset_lie_span)

theorem lie_span_eq {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L M) : lie_span R L ↑N = N :=
  le_antisymm (iff.mpr lie_span_le (eq.subset rfl)) subset_lie_span

theorem well_founded_of_noetherian (R : Type u) (L : Type v) (M : Type w) [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] [is_noetherian R M] : well_founded gt :=
  let f : gt →r gt := rel_hom.mk coe fun (N N' : lie_submodule R L M) (h : N > N') => h;
  rel_hom.well_founded f
    (eq.mpr (id (Eq._oldrec (Eq.refl (well_founded gt)) (Eq.symm (propext is_noetherian_iff_well_founded)))) _inst_8)

/-- Given a Lie module `M` over a Lie algebra `L`, the set of Lie ideals of `L` acts on the set
of submodules of `M`. -/
protected instance has_bracket {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] : has_bracket (lie_ideal R L) (lie_submodule R L M) :=
  has_bracket.mk
    fun (I : lie_ideal R L) (N : lie_submodule R L M) =>
      lie_span R L (set_of fun (m : M) => ∃ (x : ↥I), ∃ (n : ↥N), has_bracket.bracket ↑x ↑n = m)

theorem lie_ideal_oper_eq_span {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L M) (I : lie_ideal R L) : has_bracket.bracket I N = lie_span R L (set_of fun (m : M) => ∃ (x : ↥I), ∃ (n : ↥N), has_bracket.bracket ↑x ↑n = m) :=
  rfl

theorem lie_ideal_oper_eq_linear_span {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L M) (I : lie_ideal R L) : ↑(has_bracket.bracket I N) =
  submodule.span R (set_of fun (m : M) => ∃ (x : ↥I), ∃ (n : ↥N), has_bracket.bracket ↑x ↑n = m) := sorry

theorem lie_mem_lie {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L M) (I : lie_ideal R L) (x : ↥I) (m : ↥N) : has_bracket.bracket ↑x ↑m ∈ has_bracket.bracket I N :=
  eq.mpr (id (Eq._oldrec (Eq.refl (has_bracket.bracket ↑x ↑m ∈ has_bracket.bracket I N)) (lie_ideal_oper_eq_span N I)))
    (subset_lie_span (Exists.intro x (Exists.intro m (id (Eq.refl (has_bracket.bracket ↑x ↑m))))))

theorem lie_comm {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] (I : lie_ideal R L) (J : lie_ideal R L) : has_bracket.bracket I J = has_bracket.bracket J I := sorry

theorem lie_le_right {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L M) (I : lie_ideal R L) : has_bracket.bracket I N ≤ N := sorry

theorem lie_le_left {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] (I : lie_ideal R L) (J : lie_ideal R L) : has_bracket.bracket I J ≤ I :=
  eq.mpr (id (Eq._oldrec (Eq.refl (has_bracket.bracket I J ≤ I)) (lie_comm I J))) (lie_le_right I J)

theorem lie_le_inf {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] (I : lie_ideal R L) (J : lie_ideal R L) : has_bracket.bracket I J ≤ I ⊓ J :=
  eq.mpr (id (Eq._oldrec (Eq.refl (has_bracket.bracket I J ≤ I ⊓ J)) (propext le_inf_iff)))
    { left := lie_le_left I J, right := lie_le_right J I }

@[simp] theorem lie_bot {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (I : lie_ideal R L) : has_bracket.bracket I ⊥ = ⊥ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (has_bracket.bracket I ⊥ = ⊥)) (propext (eq_bot_iff (has_bracket.bracket I ⊥)))))
    (lie_le_right ⊥ I)

@[simp] theorem bot_lie {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L M) : has_bracket.bracket ⊥ N = ⊥ := sorry

theorem mono_lie {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L M) (N' : lie_submodule R L M) (I : lie_ideal R L) (J : lie_ideal R L) (h₁ : I ≤ J) (h₂ : N ≤ N') : has_bracket.bracket I N ≤ has_bracket.bracket J N' := sorry

theorem mono_lie_left {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L M) (I : lie_ideal R L) (J : lie_ideal R L) (h : I ≤ J) : has_bracket.bracket I N ≤ has_bracket.bracket J N :=
  mono_lie N N I J h (le_refl N)

theorem mono_lie_right {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L M) (N' : lie_submodule R L M) (I : lie_ideal R L) (h : N ≤ N') : has_bracket.bracket I N ≤ has_bracket.bracket I N' :=
  mono_lie N N' I I (le_refl I) h

@[simp] theorem lie_sup {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L M) (N' : lie_submodule R L M) (I : lie_ideal R L) : has_bracket.bracket I (N ⊔ N') = has_bracket.bracket I N ⊔ has_bracket.bracket I N' := sorry

@[simp] theorem sup_lie {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L M) (I : lie_ideal R L) (J : lie_ideal R L) : has_bracket.bracket (I ⊔ J) N = has_bracket.bracket I N ⊔ has_bracket.bracket J N := sorry

@[simp] theorem lie_inf {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L M) (N' : lie_submodule R L M) (I : lie_ideal R L) : has_bracket.bracket I (N ⊓ N') ≤ has_bracket.bracket I N ⊓ has_bracket.bracket I N' := sorry

@[simp] theorem inf_lie {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L M) (I : lie_ideal R L) (J : lie_ideal R L) : has_bracket.bracket (I ⊓ J) N ≤ has_bracket.bracket I N ⊓ has_bracket.bracket J N := sorry

@[simp] theorem trivial_lie_oper_zero {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L M) (I : lie_ideal R L) [lie_module.is_trivial L M] : has_bracket.bracket I N = ⊥ := sorry

/-- The quotient of a Lie module by a Lie submodule. It is a Lie module. -/
def quotient {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L M)  :=
  submodule.quotient (to_submodule N)

namespace quotient


/-- Map sending an element of `M` to the corresponding element of `M/N`, when `N` is a
lie_submodule of the lie_module `N`. -/
def mk {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] {N : lie_submodule R L M} : M → quotient N :=
  submodule.quotient.mk

theorem is_quotient_mk {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] {N : lie_submodule R L M} (m : M) : quotient.mk' m = mk m :=
  rfl

/-- Given a Lie module `M` over a Lie algebra `L`, together with a Lie submodule `N ⊆ M`, there
is a natural linear map from `L` to the endomorphisms of `M` leaving `N` invariant. -/
def lie_submodule_invariant {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] {N : lie_submodule R L M} : linear_map R L ↥(submodule.compatible_maps (to_submodule N) (to_submodule N)) :=
  linear_map.cod_restrict (submodule.compatible_maps (to_submodule N) (to_submodule N))
    (↑(lie_module.to_endo_morphism R L M)) (lie_mem N)

/-- Given a Lie module `M` over a Lie algebra `L`, together with a Lie submodule `N ⊆ M`, there
is a natural Lie algebra morphism from `L` to the linear endomorphism of the quotient `M/N`. -/
def action_as_endo_map {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L M) : lie_algebra.morphism R L (module.End R (quotient N)) :=
  lie_algebra.morphism.mk (linear_map.to_fun (linear_map.comp (submodule.mapq_linear ↑N ↑N) lie_submodule_invariant))
    sorry sorry sorry

/-- Given a Lie module `M` over a Lie algebra `L`, together with a Lie submodule `N ⊆ M`, there is
a natural bracket action of `L` on the quotient `M/N`. -/
def action_as_endo_map_bracket {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L M) : has_bracket L (quotient N) :=
  has_bracket.mk fun (x : L) (n : quotient N) => coe_fn (coe_fn (action_as_endo_map N) x) n

protected instance lie_quotient_lie_ring_module {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L M) : lie_ring_module L (quotient N) :=
  lie_ring_module.mk sorry sorry sorry

/-- The quotient of a Lie module by a Lie submodule, is a Lie module. -/
protected instance lie_quotient_lie_module {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L M) : lie_module R L (quotient N) :=
  lie_module.mk sorry sorry

protected instance lie_quotient_has_bracket {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] {I : lie_ideal R L} : has_bracket (quotient I) (quotient I) :=
  has_bracket.mk
    fun (x y : quotient I) => quotient.lift_on₂' x y (fun (x' y' : L) => mk (has_bracket.bracket x' y')) sorry

@[simp] theorem mk_bracket {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] {I : lie_ideal R L} (x : L) (y : L) : mk (has_bracket.bracket x y) = has_bracket.bracket (mk x) (mk y) :=
  rfl

protected instance lie_quotient_lie_ring {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] {I : lie_ideal R L} : lie_ring (quotient I) :=
  lie_ring.mk sorry sorry sorry sorry

protected instance lie_quotient_lie_algebra {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] {I : lie_ideal R L} : lie_algebra R (quotient I) :=
  lie_algebra.mk sorry

end quotient


end lie_submodule


namespace lie_algebra


/-- A generalisation of the derived series of a Lie algebra, whose zeroth term is a specified ideal.

It can be more convenient to work with this generalisation when considering the derived series of
an ideal since it provides a type-theoretic expression of the fact that the terms of the ideal's
derived series are also ideals of the enclosing algebra.

See also `lie_ideal.derived_series_eq_derived_series_of_ideal_comap` and
`lie_ideal.derived_series_eq_derived_series_of_ideal_map` below. -/
def derived_series_of_ideal (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] [lie_algebra R L] (k : ℕ) : lie_ideal R L → lie_ideal R L :=
  nat.iterate (fun (I : lie_ideal R L) => has_bracket.bracket I I) k

@[simp] theorem derived_series_of_ideal_zero (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] [lie_algebra R L] (I : lie_ideal R L) : derived_series_of_ideal R L 0 I = I :=
  rfl

@[simp] theorem derived_series_of_ideal_succ (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] [lie_algebra R L] (I : lie_ideal R L) (k : ℕ) : derived_series_of_ideal R L (k + 1) I =
  has_bracket.bracket (derived_series_of_ideal R L k I) (derived_series_of_ideal R L k I) :=
  function.iterate_succ_apply' (fun (I : lie_ideal R L) => has_bracket.bracket I I) k I

/-- The derived series of Lie ideals of a Lie algebra. -/
def derived_series (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] [lie_algebra R L] (k : ℕ) : lie_ideal R L :=
  derived_series_of_ideal R L k ⊤

theorem derived_series_def (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] [lie_algebra R L] (k : ℕ) : derived_series R L k = derived_series_of_ideal R L k ⊤ :=
  rfl

theorem derived_series_of_ideal_add {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] (I : lie_ideal R L) (k : ℕ) (l : ℕ) : derived_series_of_ideal R L (k + l) I = derived_series_of_ideal R L k (derived_series_of_ideal R L l I) := sorry

theorem derived_series_of_ideal_le {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] {I : lie_ideal R L} {J : lie_ideal R L} {k : ℕ} {l : ℕ} (h₁ : I ≤ J) (h₂ : l ≤ k) : derived_series_of_ideal R L k I ≤ derived_series_of_ideal R L l J := sorry

theorem derived_series_of_ideal_succ_le {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] (I : lie_ideal R L) (k : ℕ) : derived_series_of_ideal R L (k + 1) I ≤ derived_series_of_ideal R L k I :=
  derived_series_of_ideal_le (le_refl I) (nat.le_succ k)

theorem derived_series_of_ideal_le_self {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] (I : lie_ideal R L) (k : ℕ) : derived_series_of_ideal R L k I ≤ I :=
  derived_series_of_ideal_le (le_refl I) (zero_le k)

theorem derived_series_of_ideal_mono {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] {I : lie_ideal R L} {J : lie_ideal R L} (h : I ≤ J) (k : ℕ) : derived_series_of_ideal R L k I ≤ derived_series_of_ideal R L k J :=
  derived_series_of_ideal_le h (le_refl k)

theorem derived_series_of_ideal_antimono {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] (I : lie_ideal R L) {k : ℕ} {l : ℕ} (h : l ≤ k) : derived_series_of_ideal R L k I ≤ derived_series_of_ideal R L l I :=
  derived_series_of_ideal_le (le_refl I) h

theorem derived_series_of_ideal_add_le_add {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] (I : lie_ideal R L) (J : lie_ideal R L) (k : ℕ) (l : ℕ) : derived_series_of_ideal R L (k + l) (I + J) ≤ derived_series_of_ideal R L k I + derived_series_of_ideal R L l J := sorry

end lie_algebra


namespace lie_module


/-- The lower central series of Lie submodules of a Lie module. -/
def lower_central_series (R : Type u) (L : Type v) (M : Type w) [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (k : ℕ) : lie_submodule R L M :=
  nat.iterate (fun (I : lie_submodule R L M) => has_bracket.bracket ⊤ I) k ⊤

@[simp] theorem lower_central_series_zero (R : Type u) (L : Type v) (M : Type w) [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] : lower_central_series R L M 0 = ⊤ :=
  rfl

@[simp] theorem lower_central_series_succ (R : Type u) (L : Type v) (M : Type w) [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (k : ℕ) : lower_central_series R L M (k + 1) = has_bracket.bracket ⊤ (lower_central_series R L M k) :=
  function.iterate_succ_apply' (fun (I : lie_submodule R L M) => has_bracket.bracket ⊤ I) k ⊤

theorem trivial_iff_derived_eq_bot (R : Type u) (L : Type v) (M : Type w) [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] : is_trivial L M ↔ lower_central_series R L M 1 = ⊥ := sorry

theorem derived_series_le_lower_central_series (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] [lie_algebra R L] (k : ℕ) : lie_algebra.derived_series R L k ≤ lower_central_series R L L k := sorry

end lie_module


namespace lie_submodule


/-- A morphism of Lie modules `f : M → M'` pushes forward Lie submodules of `M` to Lie submodules
of `M'`. -/
def map {R : Type u} {L : Type v} {M : Type w} {M' : Type w₁} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] [add_comm_group M'] [module R M'] [lie_ring_module L M'] [lie_module R L M'] (f : lie_module_hom R L M M') (N : lie_submodule R L M) : lie_submodule R L M' :=
  mk (submodule.carrier (submodule.map ↑f ↑N)) sorry sorry sorry sorry

/-- A morphism of Lie modules `f : M → M'` pulls back Lie submodules of `M'` to Lie submodules of
`M`. -/
def comap {R : Type u} {L : Type v} {M : Type w} {M' : Type w₁} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] [add_comm_group M'] [module R M'] [lie_ring_module L M'] [lie_module R L M'] (f : lie_module_hom R L M M') (N : lie_submodule R L M') : lie_submodule R L M :=
  mk (submodule.carrier (submodule.comap ↑f ↑N)) sorry sorry sorry sorry

theorem map_le_iff_le_comap {R : Type u} {L : Type v} {M : Type w} {M' : Type w₁} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] [add_comm_group M'] [module R M'] [lie_ring_module L M'] [lie_module R L M'] {f : lie_module_hom R L M M'} {N : lie_submodule R L M} {N' : lie_submodule R L M'} : map f N ≤ N' ↔ N ≤ comap f N' :=
  set.image_subset_iff

theorem gc_map_comap {R : Type u} {L : Type v} {M : Type w} {M' : Type w₁} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] [add_comm_group M'] [module R M'] [lie_ring_module L M'] [lie_module R L M'] (f : lie_module_hom R L M M') : galois_connection (map f) (comap f) :=
  fun (N : lie_submodule R L M) (N' : lie_submodule R L M') => map_le_iff_le_comap

end lie_submodule


namespace lie_ideal


/-- A morphism of Lie algebras `f : L → L'` pushes forward Lie ideals of `L` to Lie ideals of `L'`.

Note that unlike `lie_submodule.map`, we must take the `lie_span` of the image. Mathematically
this is because although `f` makes `L'` into a Lie module over `L`, in general the `L` submodules of
`L'` are not the same as the ideals of `L'`. -/
def map {R : Type u} {L : Type v} {L' : Type w₂} [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L'] (f : lie_algebra.morphism R L L') (I : lie_ideal R L) : lie_ideal R L' :=
  lie_submodule.lie_span R L' (⇑f '' ↑I)

/-- A morphism of Lie algebras `f : L → L'` pulls back Lie ideals of `L'` to Lie ideals of `L`.

Note that `f` makes `L'` into a Lie module over `L` (turning `f` into a morphism of Lie modules)
and so this is a special case of `lie_submodule.comap` but we do not exploit this fact. -/
def comap {R : Type u} {L : Type v} {L' : Type w₂} [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L'] (f : lie_algebra.morphism R L L') (J : lie_ideal R L') : lie_ideal R L :=
  lie_submodule.mk (submodule.carrier (submodule.comap ↑f ↑J)) sorry sorry sorry sorry

@[simp] theorem map_coe_submodule {R : Type u} {L : Type v} {L' : Type w₂} [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L'] (f : lie_algebra.morphism R L L') (I : lie_ideal R L) (h : ↑(map f I) = ⇑f '' ↑I) : ↑(map f I) = submodule.map ↑f ↑I := sorry

@[simp] theorem comap_coe_submodule {R : Type u} {L : Type v} {L' : Type w₂} [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L'] (f : lie_algebra.morphism R L L') (J : lie_ideal R L') : ↑(comap f J) = submodule.comap ↑f ↑J :=
  rfl

theorem map_le {R : Type u} {L : Type v} {L' : Type w₂} [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L'] (f : lie_algebra.morphism R L L') (I : lie_ideal R L) (J : lie_ideal R L') : map f I ≤ J ↔ ⇑f '' ↑I ⊆ ↑J :=
  lie_submodule.lie_span_le

theorem mem_map {R : Type u} {L : Type v} {L' : Type w₂} [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L'] {f : lie_algebra.morphism R L L'} {I : lie_ideal R L} {x : L} (hx : x ∈ I) : coe_fn f x ∈ map f I :=
  lie_submodule.subset_lie_span (Exists.intro x (id { left := hx, right := rfl }))

@[simp] theorem mem_comap {R : Type u} {L : Type v} {L' : Type w₂} [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L'] {f : lie_algebra.morphism R L L'} {J : lie_ideal R L'} {x : L} : x ∈ comap f J ↔ coe_fn f x ∈ J :=
  iff.rfl

theorem map_le_iff_le_comap {R : Type u} {L : Type v} {L' : Type w₂} [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L'] {f : lie_algebra.morphism R L L'} {I : lie_ideal R L} {J : lie_ideal R L'} : map f I ≤ J ↔ I ≤ comap f J :=
  eq.mpr (id (Eq._oldrec (Eq.refl (map f I ≤ J ↔ I ≤ comap f J)) (propext (map_le f I J)))) set.image_subset_iff

theorem gc_map_comap {R : Type u} {L : Type v} {L' : Type w₂} [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L'] {f : lie_algebra.morphism R L L'} : galois_connection (map f) (comap f) :=
  fun (I : lie_ideal R L) (I' : lie_ideal R L') => map_le_iff_le_comap

theorem map_comap_le {R : Type u} {L : Type v} {L' : Type w₂} [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L'] {f : lie_algebra.morphism R L L'} {J : lie_ideal R L'} : map f (comap f J) ≤ J :=
  eq.mpr (id (Eq._oldrec (Eq.refl (map f (comap f J) ≤ J)) (propext map_le_iff_le_comap))) (le_refl (comap f J))

/-- See also `map_comap_eq` below. -/
theorem comap_map_le {R : Type u} {L : Type v} {L' : Type w₂} [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L'] {f : lie_algebra.morphism R L L'} {I : lie_ideal R L} : I ≤ comap f (map f I) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (I ≤ comap f (map f I))) (Eq.symm (propext map_le_iff_le_comap)))) (le_refl (map f I))

theorem map_mono {R : Type u} {L : Type v} {L' : Type w₂} [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L'] {f : lie_algebra.morphism R L L'} : monotone (map f) :=
  fun (I₁ I₂ : lie_ideal R L) (h : I₁ ≤ I₂) =>
    lie_submodule.lie_span_mono
      (set.image_subset (⇑f) (eq.mp (Eq._oldrec (Eq.refl (I₁ ≤ I₂)) (propext (lie_submodule.le_def I₁ I₂))) h))

theorem comap_mono {R : Type u} {L : Type v} {L' : Type w₂} [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L'] {f : lie_algebra.morphism R L L'} : monotone (comap f) := sorry

theorem map_of_image {R : Type u} {L : Type v} {L' : Type w₂} [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L'] {f : lie_algebra.morphism R L L'} {I : lie_ideal R L} {J : lie_ideal R L'} (h : ⇑f '' ↑I = ↑J) : map f I = J := sorry

/-- Note that this is not a special case of `lie_submodule.of_bot_eq_bot`. Indeed, given
`I : lie_ideal R L`, in general the two lattices `lie_ideal R I` and `lie_submodule R L I` are
different (though the latter does naturally inject into the former).

In other words, in general, ideals of `I`, regarded as a Lie algebra in its own right, are not the
same as ideals of `L` contained in `I`. -/
theorem of_bot_eq_bot {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] (I : lie_ideal R ↥⊥) : I = ⊥ := sorry

theorem unique_of_bot {R : Type u} {L : Type v} {M : Type w} [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] (I : lie_submodule R L ↥⊥) (J : lie_submodule R L ↥⊥) : I = J :=
  eq.mpr (id (Eq._oldrec (Eq.refl (I = J)) (lie_submodule.of_bot_eq_bot I)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (⊥ = J)) (lie_submodule.of_bot_eq_bot J))) (Eq.refl ⊥))

end lie_ideal


namespace lie_algebra.morphism


/-- The kernel of a morphism of Lie algebras, as an ideal in the domain. -/
def ker {R : Type u} {L : Type v} {L' : Type w₂} [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L'] (f : morphism R L L') : lie_ideal R L :=
  lie_ideal.comap f ⊥

/-- The range of a morphism of Lie algebras as an ideal in the codomain. -/
def ideal_range {R : Type u} {L : Type v} {L' : Type w₂} [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L'] (f : morphism R L L') : lie_ideal R L' :=
  lie_ideal.map f ⊤

/-- The condition that the image of a morphism of Lie algebras is an ideal. -/
def is_ideal_morphism {R : Type u} {L : Type v} {L' : Type w₂} [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L'] (f : morphism R L L')  :=
  ↑(ideal_range f) = range f

@[simp] theorem is_ideal_morphism_def {R : Type u} {L : Type v} {L' : Type w₂} [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L'] (f : morphism R L L') : is_ideal_morphism f ↔ ↑(ideal_range f) = range f :=
  iff.rfl

theorem range_subset_ideal_range {R : Type u} {L : Type v} {L' : Type w₂} [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L'] (f : morphism R L L') : ↑(range f) ⊆ ↑(ideal_range f) :=
  lie_submodule.subset_lie_span

theorem map_le_ideal_range {R : Type u} {L : Type v} {L' : Type w₂} [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L'] (f : morphism R L L') (I : lie_ideal R L) : lie_ideal.map f I ≤ ideal_range f :=
  lie_ideal.map_mono le_top

theorem ker_le_comap {R : Type u} {L : Type v} {L' : Type w₂} [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L'] (f : morphism R L L') (J : lie_ideal R L') : ker f ≤ lie_ideal.comap f J :=
  lie_ideal.comap_mono bot_le

@[simp] theorem ker_coe_submodule {R : Type u} {L : Type v} {L' : Type w₂} [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L'] (f : morphism R L L') : ↑(ker f) = linear_map.ker ↑f :=
  rfl

@[simp] theorem mem_ker {R : Type u} {L : Type v} {L' : Type w₂} [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L'] (f : morphism R L L') {x : L} : x ∈ ker f ↔ coe_fn f x = 0 := sorry

theorem mem_ideal_range {R : Type u} {L : Type v} {L' : Type w₂} [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L'] (f : morphism R L L') {x : L} : coe_fn f x ∈ ideal_range f :=
  lie_ideal.mem_map (lie_submodule.mem_top x)

@[simp] theorem mem_ideal_range_iff {R : Type u} {L : Type v} {L' : Type w₂} [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L'] (f : morphism R L L') (h : is_ideal_morphism f) {y : L'} : y ∈ ideal_range f ↔ ∃ (x : L), coe_fn f x = y := sorry

theorem le_ker_iff {R : Type u} {L : Type v} {L' : Type w₂} [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L'] (f : morphism R L L') (I : lie_ideal R L) : I ≤ ker f ↔ ∀ (x : L), x ∈ I → coe_fn f x = 0 := sorry

@[simp] theorem map_bot_iff {R : Type u} {L : Type v} {L' : Type w₂} [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L'] (f : morphism R L L') (I : lie_ideal R L) : lie_ideal.map f I = ⊥ ↔ I ≤ ker f := sorry

end lie_algebra.morphism


namespace lie_ideal


theorem map_sup_ker_eq_map {R : Type u} {L : Type v} {L' : Type w₂} [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L'] {f : lie_algebra.morphism R L L'} {I : lie_ideal R L} : map f (I ⊔ lie_algebra.morphism.ker f) = map f I := sorry

@[simp] theorem map_comap_eq {R : Type u} {L : Type v} {L' : Type w₂} [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L'] {f : lie_algebra.morphism R L L'} {J : lie_ideal R L'} (h : lie_algebra.morphism.is_ideal_morphism f) : map f (comap f J) = lie_algebra.morphism.ideal_range f ⊓ J := sorry

@[simp] theorem comap_map_eq {R : Type u} {L : Type v} {L' : Type w₂} [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L'] {f : lie_algebra.morphism R L L'} {I : lie_ideal R L} (h : ↑(map f I) = ⇑f '' ↑I) : comap f (map f I) = I ⊔ lie_algebra.morphism.ker f := sorry

/-- Regarding an ideal `I` as a subalgebra, the inclusion map into its ambient space is a morphism
of Lie algebras. -/
def incl {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] (I : lie_ideal R L) : lie_algebra.morphism R (↥I) L :=
  lie_subalgebra.incl ↑I

@[simp] theorem incl_apply {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] (I : lie_ideal R L) (x : ↥I) : coe_fn (incl I) x = ↑x :=
  rfl

@[simp] theorem incl_coe {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] (I : lie_ideal R L) : ↑(incl I) = submodule.subtype ↑I :=
  rfl

@[simp] theorem comap_incl_self {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] (I : lie_ideal R L) : comap (incl I) I = ⊤ := sorry

@[simp] theorem ker_incl {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] (I : lie_ideal R L) : lie_algebra.morphism.ker (incl I) = ⊥ := sorry

@[simp] theorem incl_ideal_range {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] (I : lie_ideal R L) : lie_algebra.morphism.ideal_range (incl I) = I := sorry

theorem incl_is_ideal_morphism {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] (I : lie_ideal R L) : lie_algebra.morphism.is_ideal_morphism (incl I) := sorry

/-- Note that the inequality can be strict; e.g., the inclusion of an Abelian subalgebra of a
simple algebra. -/
theorem map_bracket_le {R : Type u} {L : Type v} {L' : Type w₂} [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L'] (f : lie_algebra.morphism R L L') {I₁ : lie_ideal R L} {I₂ : lie_ideal R L} : map f (has_bracket.bracket I₁ I₂) ≤ has_bracket.bracket (map f I₁) (map f I₂) := sorry

theorem comap_bracket_le {R : Type u} {L : Type v} {L' : Type w₂} [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L'] (f : lie_algebra.morphism R L L') {J₁ : lie_ideal R L'} {J₂ : lie_ideal R L'} : has_bracket.bracket (comap f J₁) (comap f J₂) ≤ comap f (has_bracket.bracket J₁ J₂) := sorry

theorem map_comap_incl {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] {I₁ : lie_ideal R L} {I₂ : lie_ideal R L} : map (incl I₁) (comap (incl I₁) I₂) = I₁ ⊓ I₂ := sorry

theorem comap_bracket_eq {R : Type u} {L : Type v} {L' : Type w₂} [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L'] {f : lie_algebra.morphism R L L'} {J₁ : lie_ideal R L'} {J₂ : lie_ideal R L'} (h : lie_algebra.morphism.is_ideal_morphism f) : comap f (has_bracket.bracket (lie_algebra.morphism.ideal_range f ⊓ J₁) (lie_algebra.morphism.ideal_range f ⊓ J₂)) =
  has_bracket.bracket (comap f J₁) (comap f J₂) ⊔ lie_algebra.morphism.ker f := sorry

theorem map_comap_bracket_eq {R : Type u} {L : Type v} {L' : Type w₂} [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L'] {f : lie_algebra.morphism R L L'} {J₁ : lie_ideal R L'} {J₂ : lie_ideal R L'} (h : lie_algebra.morphism.is_ideal_morphism f) : map f (has_bracket.bracket (comap f J₁) (comap f J₂)) =
  has_bracket.bracket (lie_algebra.morphism.ideal_range f ⊓ J₁) (lie_algebra.morphism.ideal_range f ⊓ J₂) := sorry

theorem comap_bracket_incl {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] (I : lie_ideal R L) {I₁ : lie_ideal R L} {I₂ : lie_ideal R L} : has_bracket.bracket (comap (incl I) I₁) (comap (incl I) I₂) = comap (incl I) (has_bracket.bracket (I ⊓ I₁) (I ⊓ I₂)) := sorry

/-- This is a very useful result; it allows us to use the fact that inclusion distributes over the
Lie bracket operation on ideals, subject to the conditions shown. -/
theorem comap_bracket_incl_of_le {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] (I : lie_ideal R L) {I₁ : lie_ideal R L} {I₂ : lie_ideal R L} (h₁ : I₁ ≤ I) (h₂ : I₂ ≤ I) : has_bracket.bracket (comap (incl I) I₁) (comap (incl I) I₂) = comap (incl I) (has_bracket.bracket I₁ I₂) := sorry

theorem derived_series_eq_derived_series_of_ideal_comap {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] (I : lie_ideal R L) (k : ℕ) : lie_algebra.derived_series R (↥I) k = comap (incl I) (lie_algebra.derived_series_of_ideal R L k I) := sorry

theorem derived_series_eq_derived_series_of_ideal_map {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] (I : lie_ideal R L) (k : ℕ) : map (incl I) (lie_algebra.derived_series R (↥I) k) = lie_algebra.derived_series_of_ideal R L k I := sorry

theorem derived_series_eq_bot_iff {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] (I : lie_ideal R L) (k : ℕ) : lie_algebra.derived_series R (↥I) k = ⊥ ↔ lie_algebra.derived_series_of_ideal R L k I = ⊥ := sorry

theorem derived_series_add_eq_bot {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L] {k : ℕ} {l : ℕ} {I : lie_ideal R L} {J : lie_ideal R L} (hI : lie_algebra.derived_series R (↥I) k = ⊥) (hJ : lie_algebra.derived_series R (↥J) l = ⊥) : lie_algebra.derived_series R (↥(I + J)) (k + l) = ⊥ := sorry

end lie_ideal


namespace lie_module


/-- A Lie module is irreducible if it is zero or its only non-trivial Lie submodule is itself. -/
class is_irreducible (R : Type u) (L : Type v) (M : Type w) [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] 
where
  irreducible : ∀ (N : lie_submodule R L M), N ≠ ⊥ → N = ⊤

/-- A Lie module is nilpotent if its lower central series reaches 0 (in a finite number of steps).-/
class is_nilpotent (R : Type u) (L : Type v) (M : Type w) [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] 
where
  nilpotent : ∃ (k : ℕ), lower_central_series R L M k = ⊥

protected instance trivial_is_nilpotent (R : Type u) (L : Type v) (M : Type w) [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] [is_trivial L M] : is_nilpotent R L M :=
  is_nilpotent.mk
    (Exists.intro 1
      (id
        (id
          (eq.mpr
            (id
              (Eq.trans
                ((fun (a a_1 : lie_submodule R L M) (e_1 : a = a_1) (ᾰ ᾰ_1 : lie_submodule R L M) (e_2 : ᾰ = ᾰ_1) =>
                    congr (congr_arg Eq e_1) e_2)
                  (has_bracket.bracket ⊤ ⊤) ⊥ (lie_submodule.trivial_lie_oper_zero ⊤ ⊤) ⊥ ⊥ (Eq.refl ⊥))
                (propext (eq_self_iff_true ⊥))))
            trivial))))

end lie_module


namespace lie_algebra


/-- A Lie algebra is simple if it is irreducible as a Lie module over itself via the adjoint
action, and it is non-Abelian. -/
class is_simple (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] [lie_algebra R L] 
extends lie_module.is_irreducible R L L
where
  non_abelian : ¬is_lie_abelian L

/-- A Lie algebra is solvable if its derived series reaches 0 (in a finite number of steps). -/
class is_solvable (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] [lie_algebra R L] 
where
  solvable : ∃ (k : ℕ), derived_series R L k = ⊥

protected instance is_solvable_bot (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] [lie_algebra R L] : is_solvable R ↥⊥ :=
  is_solvable.mk (Exists.intro 0 (lie_ideal.of_bot_eq_bot ⊤))

protected instance is_solvable_add (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] [lie_algebra R L] {I : lie_ideal R L} {J : lie_ideal R L} [hI : is_solvable R ↥I] [hJ : is_solvable R ↥J] : is_solvable R ↥(I + J) :=
  is_solvable.dcases_on hI
    fun (hI : ∃ (k : ℕ), derived_series R (↥I) k = ⊥) =>
      Exists.dcases_on hI
        fun (k : ℕ) (hk : derived_series R (↥I) k = ⊥) =>
          is_solvable.dcases_on hJ
            fun (hJ : ∃ (k : ℕ), derived_series R (↥J) k = ⊥) =>
              Exists.dcases_on hJ
                fun (l : ℕ) (hl : derived_series R (↥J) l = ⊥) =>
                  is_solvable.mk (Exists.intro (k + l) (lie_ideal.derived_series_add_eq_bot hk hl))

/-- The (solvable) radical of Lie algebra is the `Sup` of all solvable ideals. -/
def radical (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] [lie_algebra R L] : lie_ideal R L :=
  Sup (set_of fun (I : lie_ideal R L) => is_solvable R ↥I)

/-- The radical of a Noetherian Lie algebra is solvable. -/
protected instance radical_is_solvable (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] [lie_algebra R L] [is_noetherian R L] : is_solvable R ↥(radical R L) :=
  eq.mp
    (Eq._oldrec (Eq.refl (well_founded gt))
      (Eq.symm (propext (complete_lattice.is_sup_closed_compact_iff_well_founded (lie_submodule R L L)))))
    (lie_submodule.well_founded_of_noetherian R L L) (set_of fun (I : lie_ideal R L) => is_solvable R ↥I)
    (Exists.intro ⊥ (id (lie_algebra.is_solvable_bot R L)))
    fun (I J : lie_submodule R L L) (hI : I ∈ set_of fun (I : lie_ideal R L) => is_solvable R ↥I)
      (hJ : J ∈ set_of fun (I : lie_ideal R L) => is_solvable R ↥I) => lie_algebra.is_solvable_add R L

protected instance is_solvable_of_is_nilpotent (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] [lie_algebra R L] [hL : lie_module.is_nilpotent R L L] : is_solvable R L :=
  Exists.dcases_on lie_module.is_nilpotent.nilpotent
    fun (k : ℕ) (h : lie_module.lower_central_series R L L k = ⊥) =>
      is_solvable.mk
        (Exists.intro k
          (id
            (eq.mpr (id (Eq._oldrec (Eq.refl (derived_series R L k = ⊥)) (Eq.symm (propext le_bot_iff))))
              (le_trans (lie_module.derived_series_le_lower_central_series R L k)
                (eq.mp (Eq._oldrec (Eq.refl (lie_module.lower_central_series R L L k = ⊥)) (Eq.symm (propext le_bot_iff)))
                  h)))))

end lie_algebra


namespace linear_equiv


/-- A linear equivalence of two modules induces a Lie algebra equivalence of their endomorphisms. -/
def lie_conj {R : Type u} {M₁ : Type v} {M₂ : Type w} [comm_ring R] [add_comm_group M₁] [module R M₁] [add_comm_group M₂] [module R M₂] (e : linear_equiv R M₁ M₂) : lie_algebra.equiv R (module.End R M₁) (module.End R M₂) :=
  lie_algebra.equiv.mk (to_fun (conj e)) sorry sorry sorry (inv_fun (conj e)) sorry sorry

@[simp] theorem lie_conj_apply {R : Type u} {M₁ : Type v} {M₂ : Type w} [comm_ring R] [add_comm_group M₁] [module R M₁] [add_comm_group M₂] [module R M₂] (e : linear_equiv R M₁ M₂) (f : module.End R M₁) : coe_fn (lie_conj e) f = coe_fn (conj e) f :=
  rfl

@[simp] theorem lie_conj_symm {R : Type u} {M₁ : Type v} {M₂ : Type w} [comm_ring R] [add_comm_group M₁] [module R M₁] [add_comm_group M₂] [module R M₂] (e : linear_equiv R M₁ M₂) : lie_algebra.equiv.symm (lie_conj e) = lie_conj (symm e) :=
  rfl

end linear_equiv


namespace alg_equiv


/-- An equivalence of associative algebras is an equivalence of associated Lie algebras. -/
def to_lie_equiv {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_ring R] [ring A₁] [ring A₂] [algebra R A₁] [algebra R A₂] (e : alg_equiv R A₁ A₂) : lie_algebra.equiv R A₁ A₂ :=
  lie_algebra.equiv.mk (to_fun e) sorry sorry sorry (linear_equiv.inv_fun (to_linear_equiv e)) sorry sorry

@[simp] theorem to_lie_equiv_apply {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_ring R] [ring A₁] [ring A₂] [algebra R A₁] [algebra R A₂] (e : alg_equiv R A₁ A₂) (x : A₁) : coe_fn (to_lie_equiv e) x = coe_fn e x :=
  rfl

@[simp] theorem to_lie_equiv_symm_apply {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_ring R] [ring A₁] [ring A₂] [algebra R A₁] [algebra R A₂] (e : alg_equiv R A₁ A₂) (x : A₂) : coe_fn (lie_algebra.equiv.symm (to_lie_equiv e)) x = coe_fn (symm e) x :=
  rfl

end alg_equiv


/-! ### Matrices

An important class of Lie algebras are those arising from the associative algebra structure on
square matrices over a commutative ring.
-/

/-- The natural equivalence between linear endomorphisms of finite free modules and square matrices
is compatible with the Lie algebra structures. -/
def lie_equiv_matrix' {R : Type u} [comm_ring R] {n : Type w} [DecidableEq n] [fintype n] : lie_algebra.equiv R (module.End R (n → R)) (matrix n n R) :=
  lie_algebra.equiv.mk (linear_equiv.to_fun linear_map.to_matrix') sorry sorry sorry
    (linear_equiv.inv_fun linear_map.to_matrix') sorry sorry

@[simp] theorem lie_equiv_matrix'_apply {R : Type u} [comm_ring R] {n : Type w} [DecidableEq n] [fintype n] (f : module.End R (n → R)) : coe_fn lie_equiv_matrix' f = coe_fn linear_map.to_matrix' f :=
  rfl

@[simp] theorem lie_equiv_matrix'_symm_apply {R : Type u} [comm_ring R] {n : Type w} [DecidableEq n] [fintype n] (A : matrix n n R) : coe_fn (lie_algebra.equiv.symm lie_equiv_matrix') A = coe_fn matrix.to_lin' A :=
  rfl

/-- An invertible matrix induces a Lie algebra equivalence from the space of matrices to itself. -/
def matrix.lie_conj {R : Type u} [comm_ring R] {n : Type w} [DecidableEq n] [fintype n] (P : matrix n n R) (h : is_unit P) : lie_algebra.equiv R (matrix n n R) (matrix n n R) :=
  lie_algebra.equiv.trans
    (lie_algebra.equiv.trans (lie_algebra.equiv.symm lie_equiv_matrix')
      (linear_equiv.lie_conj (matrix.to_linear_equiv P h)))
    lie_equiv_matrix'

@[simp] theorem matrix.lie_conj_apply {R : Type u} [comm_ring R] {n : Type w} [DecidableEq n] [fintype n] (P : matrix n n R) (A : matrix n n R) (h : is_unit P) : coe_fn (matrix.lie_conj P h) A = matrix.mul (matrix.mul P A) (P⁻¹) := sorry

@[simp] theorem matrix.lie_conj_symm_apply {R : Type u} [comm_ring R] {n : Type w} [DecidableEq n] [fintype n] (P : matrix n n R) (A : matrix n n R) (h : is_unit P) : coe_fn (lie_algebra.equiv.symm (matrix.lie_conj P h)) A = matrix.mul (matrix.mul (P⁻¹) A) P := sorry

/-- For square matrices, the natural map that reindexes a matrix's rows and columns with equivalent
types is an equivalence of Lie algebras. -/
def matrix.reindex_lie_equiv {R : Type u} [comm_ring R] {n : Type w} [DecidableEq n] [fintype n] {m : Type w₁} [DecidableEq m] [fintype m] (e : n ≃ m) : lie_algebra.equiv R (matrix n n R) (matrix m m R) :=
  lie_algebra.equiv.mk (linear_equiv.to_fun (matrix.reindex_linear_equiv e e)) sorry sorry sorry
    (linear_equiv.inv_fun (matrix.reindex_linear_equiv e e)) sorry sorry

@[simp] theorem matrix.reindex_lie_equiv_apply {R : Type u} [comm_ring R] {n : Type w} [DecidableEq n] [fintype n] {m : Type w₁} [DecidableEq m] [fintype m] (e : n ≃ m) (M : matrix n n R) : coe_fn (matrix.reindex_lie_equiv e) M = fun (i j : m) => M (coe_fn (equiv.symm e) i) (coe_fn (equiv.symm e) j) :=
  rfl

@[simp] theorem matrix.reindex_lie_equiv_symm_apply {R : Type u} [comm_ring R] {n : Type w} [DecidableEq n] [fintype n] {m : Type w₁} [DecidableEq m] [fintype m] (e : n ≃ m) (M : matrix m m R) : coe_fn (lie_algebra.equiv.symm (matrix.reindex_lie_equiv e)) M = fun (i j : n) => M (coe_fn e i) (coe_fn e j) :=
  rfl

