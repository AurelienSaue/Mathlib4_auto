/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury G. Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.linear_algebra.affine_space.affine_map
import Mathlib.algebra.invertible
import Mathlib.PostPort

universes u_1 u_2 u_3 u_4 u_5 l u_6 u_7 u_8 u_9 u_10 

namespace Mathlib

/-!
# Affine equivalences

In this file we define `affine_equiv k P₁ P₂` (notation: `P₁ ≃ᵃ[k] P₂`) to be the type of affine
equivalences between `P₁` and `P₂, i.e., equivalences such that both forward and inverse maps are
affine maps.

We define the following equivalences:

* `affine_equiv.refl k P`: the identity map as an `affine_equiv`;

* `e.symm`: the inverse map of an `affine_equiv` as an `affine_equiv`;

* `e.trans e'`: composition of two `affine_equiv`s; note that the order follows `mathlib`'s
  `category_theory` convention (apply `e`, then `e'`), not the convention used in function
  composition and compositions of bundled morphisms.

## Tags

affine space, affine equivalence
-/

/-- An affine equivalence is an equivalence between affine spaces such that both forward
and inverse maps are affine.

We define it using an `equiv` for the map and a `linear_equiv` for the linear part in order
to allow affine equivalences with good definitional equalities. -/
structure affine_equiv (k : Type u_1) (P₁ : Type u_2) (P₂ : Type u_3) {V₁ : Type u_4} {V₂ : Type u_5} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂] 
extends P₁ ≃ P₂
where
  linear : linear_equiv k V₁ V₂
  map_vadd' : ∀ (p : P₁) (v : V₁), coe_fn _to_equiv (v +ᵥ p) = coe_fn linear v +ᵥ coe_fn _to_equiv p

protected instance affine_equiv.has_coe_to_fun (k : Type u_1) {V1 : Type u_2} (P1 : Type u_3) {V2 : Type u_4} (P2 : Type u_5) [ring k] [add_comm_group V1] [module k V1] [add_torsor V1 P1] [add_comm_group V2] [module k V2] [add_torsor V2 P2] : has_coe_to_fun (affine_equiv k P1 P2) :=
  has_coe_to_fun.mk (fun (e : affine_equiv k P1 P2) => P1 → P2)
    fun (e : affine_equiv k P1 P2) => equiv.to_fun (affine_equiv.to_equiv e)

namespace linear_equiv


/-- Interpret a linear equivalence between modules as an affine equivalence. -/
def to_affine_equiv {k : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_comm_group V₂] [semimodule k V₂] (e : linear_equiv k V₁ V₂) : affine_equiv k V₁ V₂ :=
  affine_equiv.mk (to_equiv e) e sorry

@[simp] theorem coe_to_affine_equiv {k : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_comm_group V₂] [semimodule k V₂] (e : linear_equiv k V₁ V₂) : ⇑(to_affine_equiv e) = ⇑e :=
  rfl

end linear_equiv


namespace affine_equiv


/-- Identity map as an `affine_equiv`. -/
def refl (k : Type u_1) {V₁ : Type u_2} (P₁ : Type u_6) [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] : affine_equiv k P₁ P₁ :=
  mk (equiv.refl P₁) (linear_equiv.refl k V₁) sorry

@[simp] theorem coe_refl (k : Type u_1) {V₁ : Type u_2} (P₁ : Type u_6) [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] : ⇑(refl k P₁) = id :=
  rfl

theorem refl_apply (k : Type u_1) {V₁ : Type u_2} (P₁ : Type u_6) [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] (x : P₁) : coe_fn (refl k P₁) x = x :=
  rfl

@[simp] theorem to_equiv_refl (k : Type u_1) {V₁ : Type u_2} (P₁ : Type u_6) [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] : to_equiv (refl k P₁) = equiv.refl P₁ :=
  rfl

@[simp] theorem linear_refl (k : Type u_1) {V₁ : Type u_2} (P₁ : Type u_6) [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] : linear (refl k P₁) = linear_equiv.refl k V₁ :=
  rfl

@[simp] theorem map_vadd {k : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3} {P₁ : Type u_6} {P₂ : Type u_7} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂] (e : affine_equiv k P₁ P₂) (p : P₁) (v : V₁) : coe_fn e (v +ᵥ p) = coe_fn (linear e) v +ᵥ coe_fn e p :=
  map_vadd' e p v

@[simp] theorem coe_to_equiv {k : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3} {P₁ : Type u_6} {P₂ : Type u_7} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂] (e : affine_equiv k P₁ P₂) : ⇑(to_equiv e) = ⇑e :=
  rfl

/-- Reinterpret an `affine_equiv` as an `affine_map`. -/
def to_affine_map {k : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3} {P₁ : Type u_6} {P₂ : Type u_7} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂] (e : affine_equiv k P₁ P₂) : affine_map k P₁ P₂ :=
  affine_map.mk (⇑e) (↑(linear e)) (map_vadd' e)

@[simp] theorem coe_to_affine_map {k : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3} {P₁ : Type u_6} {P₂ : Type u_7} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂] (e : affine_equiv k P₁ P₂) : ⇑(to_affine_map e) = ⇑e :=
  rfl

@[simp] theorem to_affine_map_mk {k : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3} {P₁ : Type u_6} {P₂ : Type u_7} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂] (f : P₁ ≃ P₂) (f' : linear_equiv k V₁ V₂) (h : ∀ (p : P₁) (v : V₁), coe_fn f (v +ᵥ p) = coe_fn f' v +ᵥ coe_fn f p) : to_affine_map (mk f f' h) = affine_map.mk (⇑f) (↑f') h :=
  rfl

@[simp] theorem linear_to_affine_map {k : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3} {P₁ : Type u_6} {P₂ : Type u_7} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂] (e : affine_equiv k P₁ P₂) : affine_map.linear (to_affine_map e) = ↑(linear e) :=
  rfl

theorem injective_to_affine_map {k : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3} {P₁ : Type u_6} {P₂ : Type u_7} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂] : function.injective to_affine_map := sorry

@[simp] theorem to_affine_map_inj {k : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3} {P₁ : Type u_6} {P₂ : Type u_7} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂] {e : affine_equiv k P₁ P₂} {e' : affine_equiv k P₁ P₂} : to_affine_map e = to_affine_map e' ↔ e = e' :=
  function.injective.eq_iff injective_to_affine_map

theorem ext {k : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3} {P₁ : Type u_6} {P₂ : Type u_7} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂] {e : affine_equiv k P₁ P₂} {e' : affine_equiv k P₁ P₂} (h : ∀ (x : P₁), coe_fn e x = coe_fn e' x) : e = e' :=
  injective_to_affine_map (affine_map.ext h)

theorem injective_coe_fn {k : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3} {P₁ : Type u_6} {P₂ : Type u_7} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂] : function.injective fun (e : affine_equiv k P₁ P₂) (x : P₁) => coe_fn e x := sorry

@[simp] theorem coe_fn_inj {k : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3} {P₁ : Type u_6} {P₂ : Type u_7} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂] {e : affine_equiv k P₁ P₂} {e' : affine_equiv k P₁ P₂} : ⇑e = ⇑e' ↔ e = e' :=
  function.injective.eq_iff injective_coe_fn

theorem injective_to_equiv {k : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3} {P₁ : Type u_6} {P₂ : Type u_7} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂] : function.injective to_equiv :=
  fun (e e' : affine_equiv k P₁ P₂) (H : to_equiv e = to_equiv e') => ext (iff.mp equiv.ext_iff H)

@[simp] theorem to_equiv_inj {k : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3} {P₁ : Type u_6} {P₂ : Type u_7} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂] {e : affine_equiv k P₁ P₂} {e' : affine_equiv k P₁ P₂} : to_equiv e = to_equiv e' ↔ e = e' :=
  function.injective.eq_iff injective_to_equiv

/-- Construct an affine equivalence by verifying the relation between the map and its linear part at
one base point. Namely, this function takes an equivalence `e : P₁ ≃ P₂`, a linear equivalece
`e' : V₁ ≃ₗ[k] V₂`, and a point `p` such that for any other point `p'` we have
`e p' = e' (p' -ᵥ p) +ᵥ e p`. -/
def mk' {k : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3} {P₁ : Type u_6} {P₂ : Type u_7} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂] (e : P₁ ≃ P₂) (e' : linear_equiv k V₁ V₂) (p : P₁) (h : ∀ (p' : P₁), coe_fn e p' = coe_fn e' (p' -ᵥ p) +ᵥ coe_fn e p) : affine_equiv k P₁ P₂ :=
  mk e e' sorry

@[simp] theorem coe_mk' {k : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3} {P₁ : Type u_6} {P₂ : Type u_7} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂] (e : P₁ ≃ P₂) (e' : linear_equiv k V₁ V₂) (p : P₁) (h : ∀ (p' : P₁), coe_fn e p' = coe_fn e' (p' -ᵥ p) +ᵥ coe_fn e p) : ⇑(mk' e e' p h) = ⇑e :=
  rfl

@[simp] theorem to_equiv_mk' {k : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3} {P₁ : Type u_6} {P₂ : Type u_7} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂] (e : P₁ ≃ P₂) (e' : linear_equiv k V₁ V₂) (p : P₁) (h : ∀ (p' : P₁), coe_fn e p' = coe_fn e' (p' -ᵥ p) +ᵥ coe_fn e p) : to_equiv (mk' e e' p h) = e :=
  rfl

@[simp] theorem linear_mk' {k : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3} {P₁ : Type u_6} {P₂ : Type u_7} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂] (e : P₁ ≃ P₂) (e' : linear_equiv k V₁ V₂) (p : P₁) (h : ∀ (p' : P₁), coe_fn e p' = coe_fn e' (p' -ᵥ p) +ᵥ coe_fn e p) : linear (mk' e e' p h) = e' :=
  rfl

/-- Inverse of an affine equivalence as an affine equivalence. -/
def symm {k : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3} {P₁ : Type u_6} {P₂ : Type u_7} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂] (e : affine_equiv k P₁ P₂) : affine_equiv k P₂ P₁ :=
  mk (equiv.symm (to_equiv e)) (linear_equiv.symm (linear e)) sorry

@[simp] theorem symm_to_equiv {k : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3} {P₁ : Type u_6} {P₂ : Type u_7} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂] (e : affine_equiv k P₁ P₂) : equiv.symm (to_equiv e) = to_equiv (symm e) :=
  rfl

@[simp] theorem symm_linear {k : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3} {P₁ : Type u_6} {P₂ : Type u_7} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂] (e : affine_equiv k P₁ P₂) : linear_equiv.symm (linear e) = linear (symm e) :=
  rfl

protected theorem bijective {k : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3} {P₁ : Type u_6} {P₂ : Type u_7} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂] (e : affine_equiv k P₁ P₂) : function.bijective ⇑e :=
  equiv.bijective (to_equiv e)

protected theorem surjective {k : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3} {P₁ : Type u_6} {P₂ : Type u_7} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂] (e : affine_equiv k P₁ P₂) : function.surjective ⇑e :=
  equiv.surjective (to_equiv e)

protected theorem injective {k : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3} {P₁ : Type u_6} {P₂ : Type u_7} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂] (e : affine_equiv k P₁ P₂) : function.injective ⇑e :=
  equiv.injective (to_equiv e)

@[simp] theorem range_eq {k : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3} {P₁ : Type u_6} {P₂ : Type u_7} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂] (e : affine_equiv k P₁ P₂) : set.range ⇑e = set.univ :=
  function.surjective.range_eq (affine_equiv.surjective e)

@[simp] theorem apply_symm_apply {k : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3} {P₁ : Type u_6} {P₂ : Type u_7} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂] (e : affine_equiv k P₁ P₂) (p : P₂) : coe_fn e (coe_fn (symm e) p) = p :=
  equiv.apply_symm_apply (to_equiv e) p

@[simp] theorem symm_apply_apply {k : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3} {P₁ : Type u_6} {P₂ : Type u_7} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂] (e : affine_equiv k P₁ P₂) (p : P₁) : coe_fn (symm e) (coe_fn e p) = p :=
  equiv.symm_apply_apply (to_equiv e) p

theorem apply_eq_iff_eq_symm_apply {k : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3} {P₁ : Type u_6} {P₂ : Type u_7} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂] (e : affine_equiv k P₁ P₂) {p₁ : P₁} {p₂ : P₂} : coe_fn e p₁ = p₂ ↔ p₁ = coe_fn (symm e) p₂ :=
  equiv.apply_eq_iff_eq_symm_apply (to_equiv e)

@[simp] theorem apply_eq_iff_eq {k : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3} {P₁ : Type u_6} {P₂ : Type u_7} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂] (e : affine_equiv k P₁ P₂) {p₁ : P₁} {p₂ : P₁} : coe_fn e p₁ = coe_fn e p₂ ↔ p₁ = p₂ :=
  equiv.apply_eq_iff_eq (to_equiv e)

@[simp] theorem symm_refl {k : Type u_1} {V₁ : Type u_2} {P₁ : Type u_6} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] : symm (refl k P₁) = refl k P₁ :=
  rfl

/-- Composition of two `affine_equiv`alences, applied left to right. -/
def trans {k : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3} {V₃ : Type u_4} {P₁ : Type u_6} {P₂ : Type u_7} {P₃ : Type u_8} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂] [add_comm_group V₃] [semimodule k V₃] [add_torsor V₃ P₃] (e : affine_equiv k P₁ P₂) (e' : affine_equiv k P₂ P₃) : affine_equiv k P₁ P₃ :=
  mk (equiv.trans (to_equiv e) (to_equiv e')) (linear_equiv.trans (linear e) (linear e')) sorry

@[simp] theorem coe_trans {k : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3} {V₃ : Type u_4} {P₁ : Type u_6} {P₂ : Type u_7} {P₃ : Type u_8} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂] [add_comm_group V₃] [semimodule k V₃] [add_torsor V₃ P₃] (e : affine_equiv k P₁ P₂) (e' : affine_equiv k P₂ P₃) : ⇑(trans e e') = ⇑e' ∘ ⇑e :=
  rfl

theorem trans_apply {k : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3} {V₃ : Type u_4} {P₁ : Type u_6} {P₂ : Type u_7} {P₃ : Type u_8} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂] [add_comm_group V₃] [semimodule k V₃] [add_torsor V₃ P₃] (e : affine_equiv k P₁ P₂) (e' : affine_equiv k P₂ P₃) (p : P₁) : coe_fn (trans e e') p = coe_fn e' (coe_fn e p) :=
  rfl

theorem trans_assoc {k : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3} {V₃ : Type u_4} {V₄ : Type u_5} {P₁ : Type u_6} {P₂ : Type u_7} {P₃ : Type u_8} {P₄ : Type u_9} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂] [add_comm_group V₃] [semimodule k V₃] [add_torsor V₃ P₃] [add_comm_group V₄] [semimodule k V₄] [add_torsor V₄ P₄] (e₁ : affine_equiv k P₁ P₂) (e₂ : affine_equiv k P₂ P₃) (e₃ : affine_equiv k P₃ P₄) : trans (trans e₁ e₂) e₃ = trans e₁ (trans e₂ e₃) :=
  ext fun (_x : P₁) => rfl

@[simp] theorem trans_refl {k : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3} {P₁ : Type u_6} {P₂ : Type u_7} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂] (e : affine_equiv k P₁ P₂) : trans e (refl k P₂) = e :=
  ext fun (_x : P₁) => rfl

@[simp] theorem refl_trans {k : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3} {P₁ : Type u_6} {P₂ : Type u_7} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂] (e : affine_equiv k P₁ P₂) : trans (refl k P₁) e = e :=
  ext fun (_x : P₁) => rfl

@[simp] theorem trans_symm {k : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3} {P₁ : Type u_6} {P₂ : Type u_7} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂] (e : affine_equiv k P₁ P₂) : trans e (symm e) = refl k P₁ :=
  ext (symm_apply_apply e)

@[simp] theorem symm_trans {k : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3} {P₁ : Type u_6} {P₂ : Type u_7} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂] (e : affine_equiv k P₁ P₂) : trans (symm e) e = refl k P₂ :=
  ext (apply_symm_apply e)

@[simp] theorem apply_line_map {k : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3} {P₁ : Type u_6} {P₂ : Type u_7} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂] (e : affine_equiv k P₁ P₂) (a : P₁) (b : P₁) (c : k) : coe_fn e (coe_fn (affine_map.line_map a b) c) = coe_fn (affine_map.line_map (coe_fn e a) (coe_fn e b)) c :=
  affine_map.apply_line_map (to_affine_map e) a b c

protected instance group {k : Type u_1} {V₁ : Type u_2} {P₁ : Type u_6} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] : group (affine_equiv k P₁ P₁) :=
  group.mk (fun (e e' : affine_equiv k P₁ P₁) => trans e' e) sorry (refl k P₁) trans_refl refl_trans symm
    (div_inv_monoid.div._default (fun (e e' : affine_equiv k P₁ P₁) => trans e' e) sorry (refl k P₁) trans_refl refl_trans
      symm)
    trans_symm

theorem one_def {k : Type u_1} {V₁ : Type u_2} {P₁ : Type u_6} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] : 1 = refl k P₁ :=
  rfl

@[simp] theorem coe_one {k : Type u_1} {V₁ : Type u_2} {P₁ : Type u_6} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] : ⇑1 = id :=
  rfl

theorem mul_def {k : Type u_1} {V₁ : Type u_2} {P₁ : Type u_6} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] (e : affine_equiv k P₁ P₁) (e' : affine_equiv k P₁ P₁) : e * e' = trans e' e :=
  rfl

@[simp] theorem coe_mul {k : Type u_1} {V₁ : Type u_2} {P₁ : Type u_6} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] (e : affine_equiv k P₁ P₁) (e' : affine_equiv k P₁ P₁) : ⇑(e * e') = ⇑e ∘ ⇑e' :=
  rfl

theorem inv_def {k : Type u_1} {V₁ : Type u_2} {P₁ : Type u_6} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] (e : affine_equiv k P₁ P₁) : e⁻¹ = symm e :=
  rfl

/-- The map `v ↦ v +ᵥ b` as an affine equivalence between a module `V` and an affine space `P` with
tangent space `V`. -/
def vadd_const (k : Type u_1) {V₁ : Type u_2} {P₁ : Type u_6} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] (b : P₁) : affine_equiv k V₁ P₁ :=
  mk (equiv.vadd_const b) (linear_equiv.refl k V₁) sorry

@[simp] theorem linear_vadd_const (k : Type u_1) {V₁ : Type u_2} {P₁ : Type u_6} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] (b : P₁) : linear (vadd_const k b) = linear_equiv.refl k V₁ :=
  rfl

@[simp] theorem vadd_const_apply (k : Type u_1) {V₁ : Type u_2} {P₁ : Type u_6} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] (b : P₁) (v : V₁) : coe_fn (vadd_const k b) v = v +ᵥ b :=
  rfl

@[simp] theorem vadd_const_symm_apply (k : Type u_1) {V₁ : Type u_2} {P₁ : Type u_6} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] (b : P₁) (p : P₁) : coe_fn (symm (vadd_const k b)) p = p -ᵥ b :=
  rfl

/-- `p' ↦ p -ᵥ p'` as an equivalence. -/
def const_vsub (k : Type u_1) {V₁ : Type u_2} {P₁ : Type u_6} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] (p : P₁) : affine_equiv k P₁ V₁ :=
  mk (equiv.const_vsub p) (linear_equiv.neg k) sorry

@[simp] theorem coe_const_vsub (k : Type u_1) {V₁ : Type u_2} {P₁ : Type u_6} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] (p : P₁) : ⇑(const_vsub k p) = has_vsub.vsub p :=
  rfl

@[simp] theorem coe_const_vsub_symm (k : Type u_1) {V₁ : Type u_2} {P₁ : Type u_6} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] (p : P₁) : ⇑(symm (const_vsub k p)) = fun (v : V₁) => -v +ᵥ p :=
  rfl

/-- The map `p ↦ v +ᵥ p` as an affine automorphism of an affine space. -/
def const_vadd (k : Type u_1) {V₁ : Type u_2} (P₁ : Type u_6) [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] (v : V₁) : affine_equiv k P₁ P₁ :=
  mk (equiv.const_vadd P₁ v) (linear_equiv.refl k V₁) sorry

@[simp] theorem linear_const_vadd (k : Type u_1) {V₁ : Type u_2} (P₁ : Type u_6) [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] (v : V₁) : linear (const_vadd k P₁ v) = linear_equiv.refl k V₁ :=
  rfl

@[simp] theorem const_vadd_apply (k : Type u_1) {V₁ : Type u_2} (P₁ : Type u_6) [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] (v : V₁) (p : P₁) : coe_fn (const_vadd k P₁ v) p = v +ᵥ p :=
  rfl

@[simp] theorem const_vadd_symm_apply (k : Type u_1) {V₁ : Type u_2} (P₁ : Type u_6) [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] (v : V₁) (p : P₁) : coe_fn (symm (const_vadd k P₁ v)) p = -v +ᵥ p :=
  rfl

/-- Point reflection in `x` as a permutation. -/
def point_reflection (k : Type u_1) {V₁ : Type u_2} {P₁ : Type u_6} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] (x : P₁) : affine_equiv k P₁ P₁ :=
  trans (const_vsub k x) (vadd_const k x)

theorem point_reflection_apply (k : Type u_1) {V₁ : Type u_2} {P₁ : Type u_6} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] (x : P₁) (y : P₁) : coe_fn (point_reflection k x) y = x -ᵥ y +ᵥ x :=
  rfl

@[simp] theorem point_reflection_symm (k : Type u_1) {V₁ : Type u_2} {P₁ : Type u_6} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] (x : P₁) : symm (point_reflection k x) = point_reflection k x :=
  injective_to_equiv (equiv.point_reflection_symm x)

@[simp] theorem to_equiv_point_reflection (k : Type u_1) {V₁ : Type u_2} {P₁ : Type u_6} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] (x : P₁) : to_equiv (point_reflection k x) = equiv.point_reflection x :=
  rfl

@[simp] theorem point_reflection_self (k : Type u_1) {V₁ : Type u_2} {P₁ : Type u_6} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] (x : P₁) : coe_fn (point_reflection k x) x = x :=
  vsub_vadd x x

theorem point_reflection_involutive (k : Type u_1) {V₁ : Type u_2} {P₁ : Type u_6} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] (x : P₁) : function.involutive ⇑(point_reflection k x) :=
  equiv.point_reflection_involutive x

/-- `x` is the only fixed point of `point_reflection x`. This lemma requires
`x + x = y + y ↔ x = y`. There is no typeclass to use here, so we add it as an explicit argument. -/
theorem point_reflection_fixed_iff_of_injective_bit0 (k : Type u_1) {V₁ : Type u_2} {P₁ : Type u_6} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] {x : P₁} {y : P₁} (h : function.injective bit0) : coe_fn (point_reflection k x) y = y ↔ y = x :=
  equiv.point_reflection_fixed_iff_of_injective_bit0 h

theorem injective_point_reflection_left_of_injective_bit0 (k : Type u_1) {V₁ : Type u_2} {P₁ : Type u_6} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] (h : function.injective bit0) (y : P₁) : function.injective fun (x : P₁) => coe_fn (point_reflection k x) y :=
  equiv.injective_point_reflection_left_of_injective_bit0 h y

theorem injective_point_reflection_left_of_module (k : Type u_1) {V₁ : Type u_2} {P₁ : Type u_6} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] [invertible (bit0 1)] (y : P₁) : function.injective fun (x : P₁) => coe_fn (point_reflection k x) y := sorry

theorem point_reflection_fixed_iff_of_module (k : Type u_1) {V₁ : Type u_2} {P₁ : Type u_6} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] [invertible (bit0 1)] {x : P₁} {y : P₁} : coe_fn (point_reflection k x) y = y ↔ y = x :=
  iff.trans (function.injective.eq_iff' (injective_point_reflection_left_of_module k y) (point_reflection_self k y))
    eq_comm

end affine_equiv


namespace affine_map


theorem line_map_vadd {k : Type u_1} {V₁ : Type u_2} {P₁ : Type u_6} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] (v : V₁) (v' : V₁) (p : P₁) (c : k) : coe_fn (line_map v v') c +ᵥ p = coe_fn (line_map (v +ᵥ p) (v' +ᵥ p)) c :=
  affine_equiv.apply_line_map (affine_equiv.vadd_const k p) v v' c

theorem line_map_vsub {k : Type u_1} {V₁ : Type u_2} {P₁ : Type u_6} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] (p₁ : P₁) (p₂ : P₁) (p₃ : P₁) (c : k) : coe_fn (line_map p₁ p₂) c -ᵥ p₃ = coe_fn (line_map (p₁ -ᵥ p₃) (p₂ -ᵥ p₃)) c :=
  affine_equiv.apply_line_map (affine_equiv.symm (affine_equiv.vadd_const k p₃)) p₁ p₂ c

theorem vsub_line_map {k : Type u_1} {V₁ : Type u_2} {P₁ : Type u_6} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] (p₁ : P₁) (p₂ : P₁) (p₃ : P₁) (c : k) : p₁ -ᵥ coe_fn (line_map p₂ p₃) c = coe_fn (line_map (p₁ -ᵥ p₂) (p₁ -ᵥ p₃)) c :=
  affine_equiv.apply_line_map (affine_equiv.const_vsub k p₁) p₂ p₃ c

theorem vadd_line_map {k : Type u_1} {V₁ : Type u_2} {P₁ : Type u_6} [ring k] [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁] (v : V₁) (p₁ : P₁) (p₂ : P₁) (c : k) : v +ᵥ coe_fn (line_map p₁ p₂) c = coe_fn (line_map (v +ᵥ p₁) (v +ᵥ p₂)) c :=
  affine_equiv.apply_line_map (affine_equiv.const_vadd k P₁ v) p₁ p₂ c

theorem homothety_neg_one_apply {V₁ : Type u_2} {P₁ : Type u_6} [add_comm_group V₁] [add_torsor V₁ P₁] {R' : Type u_10} [comm_ring R'] [semimodule R' V₁] (c : P₁) (p : P₁) : coe_fn (homothety c (-1)) p = coe_fn (affine_equiv.point_reflection R' c) p := sorry

