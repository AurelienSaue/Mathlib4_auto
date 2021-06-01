/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Myers.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.linear_algebra.affine_space.basic
import Mathlib.linear_algebra.tensor_product
import Mathlib.data.set.intervals.unordered_interval
import Mathlib.PostPort

universes u_1 u_2 u_3 u_4 u_5 l u_6 u_7 u_8 u_9 u_10 u_11 u_12 

namespace Mathlib

/-!
# Affine maps

This file defines affine maps.

## Main definitions

* `affine_map` is the type of affine maps between two affine spaces with the same ring `k`.  Various
  basic examples of affine maps are defined, including `const`, `id`, `line_map` and `homothety`.

## Notations

* `P1 →ᵃ[k] P2` is a notation for `affine_map k P1 P2`;
* `affine_space V P`: a localized notation for `add_torsor V P` defined in
  `linear_algebra.affine_space.basic`.

## Implementation notes

`out_param` is used in the definition of `[add_torsor V P]` to make `V` an implicit argument
(deduced from `P`) in most cases; `include V` is needed in many cases for `V`, and type classes
using it, to be added as implicit arguments to individual lemmas.  As for modules, `k` is an
explicit argument rather than implied by `P` or `V`.

This file only provides purely algebraic definitions and results. Those depending on analysis or
topology are defined elsewhere; see `analysis.normed_space.add_torsor` and
`topology.algebra.affine`.

## References

* https://en.wikipedia.org/wiki/Affine_space
* https://en.wikipedia.org/wiki/Principal_homogeneous_space
-/

/-- An `affine_map k P1 P2` (notation: `P1 →ᵃ[k] P2`) is a map from `P1` to `P2` that
induces a corresponding linear map from `V1` to `V2`. -/
structure affine_map (k : Type u_1) {V1 : Type u_2} (P1 : Type u_3) {V2 : Type u_4} (P2 : Type u_5)
    [ring k] [add_comm_group V1] [module k V1] [add_torsor V1 P1] [add_comm_group V2] [module k V2]
    [add_torsor V2 P2]
    where
  to_fun : P1 → P2
  linear : linear_map k V1 V2
  map_vadd' : ∀ (p : P1) (v : V1), to_fun (v +ᵥ p) = coe_fn linear v +ᵥ to_fun p

protected instance affine_map.has_coe_to_fun (k : Type u_1) {V1 : Type u_2} (P1 : Type u_3)
    {V2 : Type u_4} (P2 : Type u_5) [ring k] [add_comm_group V1] [module k V1] [add_torsor V1 P1]
    [add_comm_group V2] [module k V2] [add_torsor V2 P2] : has_coe_to_fun (affine_map k P1 P2) :=
  has_coe_to_fun.mk (fun (x : affine_map k P1 P2) => P1 → P2) affine_map.to_fun

namespace linear_map


/-- Reinterpret a linear map as an affine map. -/
def to_affine_map {k : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3} [ring k] [add_comm_group V₁]
    [module k V₁] [add_comm_group V₂] [module k V₂] (f : linear_map k V₁ V₂) : affine_map k V₁ V₂ :=
  affine_map.mk (⇑f) f sorry

@[simp] theorem coe_to_affine_map {k : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3} [ring k]
    [add_comm_group V₁] [module k V₁] [add_comm_group V₂] [module k V₂] (f : linear_map k V₁ V₂) :
    ⇑(to_affine_map f) = ⇑f :=
  rfl

@[simp] theorem to_affine_map_linear {k : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3} [ring k]
    [add_comm_group V₁] [module k V₁] [add_comm_group V₂] [module k V₂] (f : linear_map k V₁ V₂) :
    affine_map.linear (to_affine_map f) = f :=
  rfl

end linear_map


namespace affine_map


/-- Constructing an affine map and coercing back to a function
produces the same map. -/
@[simp] theorem coe_mk {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V2 : Type u_4}
    {P2 : Type u_5} [ring k] [add_comm_group V1] [module k V1] [add_torsor V1 P1]
    [add_comm_group V2] [module k V2] [add_torsor V2 P2] (f : P1 → P2) (linear : linear_map k V1 V2)
    (add : ∀ (p : P1) (v : V1), f (v +ᵥ p) = coe_fn linear v +ᵥ f p) : ⇑(mk f linear add) = f :=
  rfl

/-- `to_fun` is the same as the result of coercing to a function. -/
@[simp] theorem to_fun_eq_coe {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V2 : Type u_4}
    {P2 : Type u_5} [ring k] [add_comm_group V1] [module k V1] [add_torsor V1 P1]
    [add_comm_group V2] [module k V2] [add_torsor V2 P2] (f : affine_map k P1 P2) : to_fun f = ⇑f :=
  rfl

/-- An affine map on the result of adding a vector to a point produces
the same result as the linear map applied to that vector, added to the
affine map applied to that point. -/
@[simp] theorem map_vadd {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V2 : Type u_4}
    {P2 : Type u_5} [ring k] [add_comm_group V1] [module k V1] [add_torsor V1 P1]
    [add_comm_group V2] [module k V2] [add_torsor V2 P2] (f : affine_map k P1 P2) (p : P1)
    (v : V1) : coe_fn f (v +ᵥ p) = coe_fn (linear f) v +ᵥ coe_fn f p :=
  map_vadd' f p v

/-- The linear map on the result of subtracting two points is the
result of subtracting the result of the affine map on those two
points. -/
@[simp] theorem linear_map_vsub {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V2 : Type u_4}
    {P2 : Type u_5} [ring k] [add_comm_group V1] [module k V1] [add_torsor V1 P1]
    [add_comm_group V2] [module k V2] [add_torsor V2 P2] (f : affine_map k P1 P2) (p1 : P1)
    (p2 : P1) : coe_fn (linear f) (p1 -ᵥ p2) = coe_fn f p1 -ᵥ coe_fn f p2 :=
  sorry

/-- Two affine maps are equal if they coerce to the same function. -/
theorem ext {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V2 : Type u_4} {P2 : Type u_5} [ring k]
    [add_comm_group V1] [module k V1] [add_torsor V1 P1] [add_comm_group V2] [module k V2]
    [add_torsor V2 P2] {f : affine_map k P1 P2} {g : affine_map k P1 P2}
    (h : ∀ (p : P1), coe_fn f p = coe_fn g p) : f = g :=
  sorry

theorem ext_iff {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V2 : Type u_4} {P2 : Type u_5}
    [ring k] [add_comm_group V1] [module k V1] [add_torsor V1 P1] [add_comm_group V2] [module k V2]
    [add_torsor V2 P2] {f : affine_map k P1 P2} {g : affine_map k P1 P2} :
    f = g ↔ ∀ (p : P1), coe_fn f p = coe_fn g p :=
  { mp := fun (h : f = g) (p : P1) => h ▸ rfl, mpr := ext }

theorem injective_coe_fn {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V2 : Type u_4}
    {P2 : Type u_5} [ring k] [add_comm_group V1] [module k V1] [add_torsor V1 P1]
    [add_comm_group V2] [module k V2] [add_torsor V2 P2] :
    function.injective fun (f : affine_map k P1 P2) (x : P1) => coe_fn f x :=
  sorry

protected theorem congr_arg {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V2 : Type u_4}
    {P2 : Type u_5} [ring k] [add_comm_group V1] [module k V1] [add_torsor V1 P1]
    [add_comm_group V2] [module k V2] [add_torsor V2 P2] (f : affine_map k P1 P2) {x : P1} {y : P1}
    (h : x = y) : coe_fn f x = coe_fn f y :=
  congr_arg (⇑f) h

protected theorem congr_fun {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V2 : Type u_4}
    {P2 : Type u_5} [ring k] [add_comm_group V1] [module k V1] [add_torsor V1 P1]
    [add_comm_group V2] [module k V2] [add_torsor V2 P2] {f : affine_map k P1 P2}
    {g : affine_map k P1 P2} (h : f = g) (x : P1) : coe_fn f x = coe_fn g x :=
  h ▸ rfl

/-- Constant function as an `affine_map`. -/
def const (k : Type u_1) {V1 : Type u_2} (P1 : Type u_3) {V2 : Type u_4} {P2 : Type u_5} [ring k]
    [add_comm_group V1] [module k V1] [add_torsor V1 P1] [add_comm_group V2] [module k V2]
    [add_torsor V2 P2] (p : P2) : affine_map k P1 P2 :=
  mk (function.const P1 p) 0 sorry

@[simp] theorem coe_const (k : Type u_1) {V1 : Type u_2} (P1 : Type u_3) {V2 : Type u_4}
    {P2 : Type u_5} [ring k] [add_comm_group V1] [module k V1] [add_torsor V1 P1]
    [add_comm_group V2] [module k V2] [add_torsor V2 P2] (p : P2) :
    ⇑(const k P1 p) = function.const P1 p :=
  rfl

@[simp] theorem const_linear (k : Type u_1) {V1 : Type u_2} (P1 : Type u_3) {V2 : Type u_4}
    {P2 : Type u_5} [ring k] [add_comm_group V1] [module k V1] [add_torsor V1 P1]
    [add_comm_group V2] [module k V2] [add_torsor V2 P2] (p : P2) : linear (const k P1 p) = 0 :=
  rfl

protected instance nonempty {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V2 : Type u_4}
    {P2 : Type u_5} [ring k] [add_comm_group V1] [module k V1] [add_torsor V1 P1]
    [add_comm_group V2] [module k V2] [add_torsor V2 P2] : Nonempty (affine_map k P1 P2) :=
  nonempty.elim add_torsor.nonempty fun (p : P2) => Nonempty.intro (const k P1 p)

/-- Construct an affine map by verifying the relation between the map and its linear part at one
base point. Namely, this function takes a map `f : P₁ → P₂`, a linear map `f' : V₁ →ₗ[k] V₂`, and
a point `p` such that for any other point `p'` we have `f p' = f' (p' -ᵥ p) +ᵥ f p`. -/
def mk' {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V2 : Type u_4} {P2 : Type u_5} [ring k]
    [add_comm_group V1] [module k V1] [add_torsor V1 P1] [add_comm_group V2] [module k V2]
    [add_torsor V2 P2] (f : P1 → P2) (f' : linear_map k V1 V2) (p : P1)
    (h : ∀ (p' : P1), f p' = coe_fn f' (p' -ᵥ p) +ᵥ f p) : affine_map k P1 P2 :=
  mk f f' sorry

@[simp] theorem coe_mk' {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V2 : Type u_4}
    {P2 : Type u_5} [ring k] [add_comm_group V1] [module k V1] [add_torsor V1 P1]
    [add_comm_group V2] [module k V2] [add_torsor V2 P2] (f : P1 → P2) (f' : linear_map k V1 V2)
    (p : P1) (h : ∀ (p' : P1), f p' = coe_fn f' (p' -ᵥ p) +ᵥ f p) : ⇑(mk' f f' p h) = f :=
  rfl

@[simp] theorem mk'_linear {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V2 : Type u_4}
    {P2 : Type u_5} [ring k] [add_comm_group V1] [module k V1] [add_torsor V1 P1]
    [add_comm_group V2] [module k V2] [add_torsor V2 P2] (f : P1 → P2) (f' : linear_map k V1 V2)
    (p : P1) (h : ∀ (p' : P1), f p' = coe_fn f' (p' -ᵥ p) +ᵥ f p) : linear (mk' f f' p h) = f' :=
  rfl

/-- The set of affine maps to a vector space is an additive commutative group. -/
protected instance add_comm_group {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V2 : Type u_4}
    [ring k] [add_comm_group V1] [module k V1] [add_torsor V1 P1] [add_comm_group V2]
    [module k V2] : add_comm_group (affine_map k P1 V2) :=
  add_comm_group.mk (fun (f g : affine_map k P1 V2) => mk (⇑f + ⇑g) (linear f + linear g) sorry)
    sorry (mk 0 0 sorry) sorry sorry (fun (f : affine_map k P1 V2) => mk (-⇑f) (-linear f) sorry)
    (add_group.sub._default
      (fun (f g : affine_map k P1 V2) => mk (⇑f + ⇑g) (linear f + linear g) sorry) sorry
      (mk 0 0 sorry) sorry sorry fun (f : affine_map k P1 V2) => mk (-⇑f) (-linear f) sorry)
    sorry sorry

@[simp] theorem coe_zero {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V2 : Type u_4} [ring k]
    [add_comm_group V1] [module k V1] [add_torsor V1 P1] [add_comm_group V2] [module k V2] :
    ⇑0 = 0 :=
  rfl

@[simp] theorem zero_linear {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V2 : Type u_4} [ring k]
    [add_comm_group V1] [module k V1] [add_torsor V1 P1] [add_comm_group V2] [module k V2] :
    linear 0 = 0 :=
  rfl

@[simp] theorem coe_add {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V2 : Type u_4} [ring k]
    [add_comm_group V1] [module k V1] [add_torsor V1 P1] [add_comm_group V2] [module k V2]
    (f : affine_map k P1 V2) (g : affine_map k P1 V2) : ⇑(f + g) = ⇑f + ⇑g :=
  rfl

@[simp] theorem add_linear {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V2 : Type u_4} [ring k]
    [add_comm_group V1] [module k V1] [add_torsor V1 P1] [add_comm_group V2] [module k V2]
    (f : affine_map k P1 V2) (g : affine_map k P1 V2) : linear (f + g) = linear f + linear g :=
  rfl

/-- The space of affine maps from `P1` to `P2` is an affine space over the space of affine maps
from `P1` to the vector space `V2` corresponding to `P2`. -/
protected instance add_torsor {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V2 : Type u_4}
    {P2 : Type u_5} [ring k] [add_comm_group V1] [module k V1] [add_torsor V1 P1]
    [add_comm_group V2] [module k V2] [add_torsor V2 P2] :
    add_torsor (affine_map k P1 V2) (affine_map k P1 P2) :=
  add_torsor.mk
    (fun (f : affine_map k P1 V2) (g : affine_map k P1 P2) =>
      mk (fun (p : P1) => coe_fn f p +ᵥ coe_fn g p) (linear f + linear g) sorry)
    sorry sorry
    (fun (f g : affine_map k P1 P2) =>
      mk (fun (p : P1) => coe_fn f p -ᵥ coe_fn g p) (linear f - linear g) sorry)
    sorry sorry

@[simp] theorem vadd_apply {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V2 : Type u_4}
    {P2 : Type u_5} [ring k] [add_comm_group V1] [module k V1] [add_torsor V1 P1]
    [add_comm_group V2] [module k V2] [add_torsor V2 P2] (f : affine_map k P1 V2)
    (g : affine_map k P1 P2) (p : P1) : coe_fn (f +ᵥ g) p = coe_fn f p +ᵥ coe_fn g p :=
  rfl

@[simp] theorem vsub_apply {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V2 : Type u_4}
    {P2 : Type u_5} [ring k] [add_comm_group V1] [module k V1] [add_torsor V1 P1]
    [add_comm_group V2] [module k V2] [add_torsor V2 P2] (f : affine_map k P1 P2)
    (g : affine_map k P1 P2) (p : P1) : coe_fn (f -ᵥ g) p = coe_fn f p -ᵥ coe_fn g p :=
  rfl

/-- `prod.fst` as an `affine_map`. -/
def fst {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V2 : Type u_4} {P2 : Type u_5} [ring k]
    [add_comm_group V1] [module k V1] [add_torsor V1 P1] [add_comm_group V2] [module k V2]
    [add_torsor V2 P2] : affine_map k (P1 × P2) P1 :=
  mk prod.fst (linear_map.fst k V1 V2) sorry

@[simp] theorem coe_fst {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V2 : Type u_4}
    {P2 : Type u_5} [ring k] [add_comm_group V1] [module k V1] [add_torsor V1 P1]
    [add_comm_group V2] [module k V2] [add_torsor V2 P2] : ⇑fst = prod.fst :=
  rfl

@[simp] theorem fst_linear {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V2 : Type u_4}
    {P2 : Type u_5} [ring k] [add_comm_group V1] [module k V1] [add_torsor V1 P1]
    [add_comm_group V2] [module k V2] [add_torsor V2 P2] : linear fst = linear_map.fst k V1 V2 :=
  rfl

/-- `prod.snd` as an `affine_map`. -/
def snd {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V2 : Type u_4} {P2 : Type u_5} [ring k]
    [add_comm_group V1] [module k V1] [add_torsor V1 P1] [add_comm_group V2] [module k V2]
    [add_torsor V2 P2] : affine_map k (P1 × P2) P2 :=
  mk prod.snd (linear_map.snd k V1 V2) sorry

@[simp] theorem coe_snd {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V2 : Type u_4}
    {P2 : Type u_5} [ring k] [add_comm_group V1] [module k V1] [add_torsor V1 P1]
    [add_comm_group V2] [module k V2] [add_torsor V2 P2] : ⇑snd = prod.snd :=
  rfl

@[simp] theorem snd_linear {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V2 : Type u_4}
    {P2 : Type u_5} [ring k] [add_comm_group V1] [module k V1] [add_torsor V1 P1]
    [add_comm_group V2] [module k V2] [add_torsor V2 P2] : linear snd = linear_map.snd k V1 V2 :=
  rfl

/-- Identity map as an affine map. -/
def id (k : Type u_1) {V1 : Type u_2} (P1 : Type u_3) [ring k] [add_comm_group V1] [module k V1]
    [add_torsor V1 P1] : affine_map k P1 P1 :=
  mk id linear_map.id sorry

/-- The identity affine map acts as the identity. -/
@[simp] theorem coe_id (k : Type u_1) {V1 : Type u_2} (P1 : Type u_3) [ring k] [add_comm_group V1]
    [module k V1] [add_torsor V1 P1] : ⇑(id k P1) = id :=
  rfl

@[simp] theorem id_linear (k : Type u_1) {V1 : Type u_2} (P1 : Type u_3) [ring k]
    [add_comm_group V1] [module k V1] [add_torsor V1 P1] : linear (id k P1) = linear_map.id :=
  rfl

/-- The identity affine map acts as the identity. -/
theorem id_apply (k : Type u_1) {V1 : Type u_2} {P1 : Type u_3} [ring k] [add_comm_group V1]
    [module k V1] [add_torsor V1 P1] (p : P1) : coe_fn (id k P1) p = p :=
  rfl

protected instance inhabited {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} [ring k]
    [add_comm_group V1] [module k V1] [add_torsor V1 P1] : Inhabited (affine_map k P1 P1) :=
  { default := id k P1 }

/-- Composition of affine maps. -/
def comp {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V2 : Type u_4} {P2 : Type u_5}
    {V3 : Type u_6} {P3 : Type u_7} [ring k] [add_comm_group V1] [module k V1] [add_torsor V1 P1]
    [add_comm_group V2] [module k V2] [add_torsor V2 P2] [add_comm_group V3] [module k V3]
    [add_torsor V3 P3] (f : affine_map k P2 P3) (g : affine_map k P1 P2) : affine_map k P1 P3 :=
  mk (⇑f ∘ ⇑g) (linear_map.comp (linear f) (linear g)) sorry

/-- Composition of affine maps acts as applying the two functions. -/
@[simp] theorem coe_comp {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V2 : Type u_4}
    {P2 : Type u_5} {V3 : Type u_6} {P3 : Type u_7} [ring k] [add_comm_group V1] [module k V1]
    [add_torsor V1 P1] [add_comm_group V2] [module k V2] [add_torsor V2 P2] [add_comm_group V3]
    [module k V3] [add_torsor V3 P3] (f : affine_map k P2 P3) (g : affine_map k P1 P2) :
    ⇑(comp f g) = ⇑f ∘ ⇑g :=
  rfl

/-- Composition of affine maps acts as applying the two functions. -/
theorem comp_apply {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V2 : Type u_4} {P2 : Type u_5}
    {V3 : Type u_6} {P3 : Type u_7} [ring k] [add_comm_group V1] [module k V1] [add_torsor V1 P1]
    [add_comm_group V2] [module k V2] [add_torsor V2 P2] [add_comm_group V3] [module k V3]
    [add_torsor V3 P3] (f : affine_map k P2 P3) (g : affine_map k P1 P2) (p : P1) :
    coe_fn (comp f g) p = coe_fn f (coe_fn g p) :=
  rfl

@[simp] theorem comp_id {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V2 : Type u_4}
    {P2 : Type u_5} [ring k] [add_comm_group V1] [module k V1] [add_torsor V1 P1]
    [add_comm_group V2] [module k V2] [add_torsor V2 P2] (f : affine_map k P1 P2) :
    comp f (id k P1) = f :=
  ext fun (p : P1) => rfl

@[simp] theorem id_comp {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V2 : Type u_4}
    {P2 : Type u_5} [ring k] [add_comm_group V1] [module k V1] [add_torsor V1 P1]
    [add_comm_group V2] [module k V2] [add_torsor V2 P2] (f : affine_map k P1 P2) :
    comp (id k P2) f = f :=
  ext fun (p : P1) => rfl

theorem comp_assoc {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V2 : Type u_4} {P2 : Type u_5}
    {V3 : Type u_6} {P3 : Type u_7} {V4 : Type u_8} {P4 : Type u_9} [ring k] [add_comm_group V1]
    [module k V1] [add_torsor V1 P1] [add_comm_group V2] [module k V2] [add_torsor V2 P2]
    [add_comm_group V3] [module k V3] [add_torsor V3 P3] [add_comm_group V4] [module k V4]
    [add_torsor V4 P4] (f₃₄ : affine_map k P3 P4) (f₂₃ : affine_map k P2 P3)
    (f₁₂ : affine_map k P1 P2) : comp (comp f₃₄ f₂₃) f₁₂ = comp f₃₄ (comp f₂₃ f₁₂) :=
  rfl

protected instance monoid {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} [ring k]
    [add_comm_group V1] [module k V1] [add_torsor V1 P1] : monoid (affine_map k P1 P1) :=
  monoid.mk comp comp_assoc (id k P1) id_comp comp_id

@[simp] theorem coe_mul {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} [ring k] [add_comm_group V1]
    [module k V1] [add_torsor V1 P1] (f : affine_map k P1 P1) (g : affine_map k P1 P1) :
    ⇑(f * g) = ⇑f ∘ ⇑g :=
  rfl

@[simp] theorem coe_one {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} [ring k] [add_comm_group V1]
    [module k V1] [add_torsor V1 P1] : ⇑1 = id :=
  rfl

/-! ### Definition of `affine_map.line_map` and lemmas about it -/

/-- The affine map from `k` to `P1` sending `0` to `p₀` and `1` to `p₁`. -/
def line_map {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} [ring k] [add_comm_group V1]
    [module k V1] [add_torsor V1 P1] (p₀ : P1) (p₁ : P1) : affine_map k k P1 :=
  linear_map.to_affine_map (linear_map.smul_right linear_map.id (p₁ -ᵥ p₀)) +ᵥ const k k p₀

theorem coe_line_map {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} [ring k] [add_comm_group V1]
    [module k V1] [add_torsor V1 P1] (p₀ : P1) (p₁ : P1) :
    ⇑(line_map p₀ p₁) = fun (c : k) => c • (p₁ -ᵥ p₀) +ᵥ p₀ :=
  rfl

theorem line_map_apply {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} [ring k] [add_comm_group V1]
    [module k V1] [add_torsor V1 P1] (p₀ : P1) (p₁ : P1) (c : k) :
    coe_fn (line_map p₀ p₁) c = c • (p₁ -ᵥ p₀) +ᵥ p₀ :=
  rfl

theorem line_map_apply_module' {k : Type u_1} {V1 : Type u_2} [ring k] [add_comm_group V1]
    [module k V1] (p₀ : V1) (p₁ : V1) (c : k) : coe_fn (line_map p₀ p₁) c = c • (p₁ - p₀) + p₀ :=
  rfl

theorem line_map_apply_module {k : Type u_1} {V1 : Type u_2} [ring k] [add_comm_group V1]
    [module k V1] (p₀ : V1) (p₁ : V1) (c : k) : coe_fn (line_map p₀ p₁) c = (1 - c) • p₀ + c • p₁ :=
  sorry

theorem line_map_apply_ring' {k : Type u_1} [ring k] (a : k) (b : k) (c : k) :
    coe_fn (line_map a b) c = c * (b - a) + a :=
  rfl

theorem line_map_apply_ring {k : Type u_1} [ring k] (a : k) (b : k) (c : k) :
    coe_fn (line_map a b) c = (1 - c) * a + c * b :=
  line_map_apply_module a b c

theorem line_map_vadd_apply {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} [ring k]
    [add_comm_group V1] [module k V1] [add_torsor V1 P1] (p : P1) (v : V1) (c : k) :
    coe_fn (line_map p (v +ᵥ p)) c = c • v +ᵥ p :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (coe_fn (line_map p (v +ᵥ p)) c = c • v +ᵥ p))
        (line_map_apply p (v +ᵥ p) c)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (c • (v +ᵥ p -ᵥ p) +ᵥ p = c • v +ᵥ p)) (vadd_vsub v p)))
      (Eq.refl (c • v +ᵥ p)))

@[simp] theorem line_map_linear {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} [ring k]
    [add_comm_group V1] [module k V1] [add_torsor V1 P1] (p₀ : P1) (p₁ : P1) :
    linear (line_map p₀ p₁) = linear_map.smul_right linear_map.id (p₁ -ᵥ p₀) :=
  add_zero (linear (linear_map.to_affine_map (linear_map.smul_right linear_map.id (p₁ -ᵥ p₀))))

theorem line_map_same_apply {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} [ring k]
    [add_comm_group V1] [module k V1] [add_torsor V1 P1] (p : P1) (c : k) :
    coe_fn (line_map p p) c = p :=
  sorry

@[simp] theorem line_map_same {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} [ring k]
    [add_comm_group V1] [module k V1] [add_torsor V1 P1] (p : P1) : line_map p p = const k k p :=
  ext (line_map_same_apply p)

@[simp] theorem line_map_apply_zero {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} [ring k]
    [add_comm_group V1] [module k V1] [add_torsor V1 P1] (p₀ : P1) (p₁ : P1) :
    coe_fn (line_map p₀ p₁) 0 = p₀ :=
  sorry

@[simp] theorem line_map_apply_one {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} [ring k]
    [add_comm_group V1] [module k V1] [add_torsor V1 P1] (p₀ : P1) (p₁ : P1) :
    coe_fn (line_map p₀ p₁) 1 = p₁ :=
  sorry

@[simp] theorem apply_line_map {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V2 : Type u_4}
    {P2 : Type u_5} [ring k] [add_comm_group V1] [module k V1] [add_torsor V1 P1]
    [add_comm_group V2] [module k V2] [add_torsor V2 P2] (f : affine_map k P1 P2) (p₀ : P1)
    (p₁ : P1) (c : k) :
    coe_fn f (coe_fn (line_map p₀ p₁) c) = coe_fn (line_map (coe_fn f p₀) (coe_fn f p₁)) c :=
  sorry

@[simp] theorem comp_line_map {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V2 : Type u_4}
    {P2 : Type u_5} [ring k] [add_comm_group V1] [module k V1] [add_torsor V1 P1]
    [add_comm_group V2] [module k V2] [add_torsor V2 P2] (f : affine_map k P1 P2) (p₀ : P1)
    (p₁ : P1) : comp f (line_map p₀ p₁) = line_map (coe_fn f p₀) (coe_fn f p₁) :=
  ext (apply_line_map f p₀ p₁)

@[simp] theorem fst_line_map {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V2 : Type u_4}
    {P2 : Type u_5} [ring k] [add_comm_group V1] [module k V1] [add_torsor V1 P1]
    [add_comm_group V2] [module k V2] [add_torsor V2 P2] (p₀ : P1 × P2) (p₁ : P1 × P2) (c : k) :
    prod.fst (coe_fn (line_map p₀ p₁) c) = coe_fn (line_map (prod.fst p₀) (prod.fst p₁)) c :=
  apply_line_map fst p₀ p₁ c

@[simp] theorem snd_line_map {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V2 : Type u_4}
    {P2 : Type u_5} [ring k] [add_comm_group V1] [module k V1] [add_torsor V1 P1]
    [add_comm_group V2] [module k V2] [add_torsor V2 P2] (p₀ : P1 × P2) (p₁ : P1 × P2) (c : k) :
    prod.snd (coe_fn (line_map p₀ p₁) c) = coe_fn (line_map (prod.snd p₀) (prod.snd p₁)) c :=
  apply_line_map snd p₀ p₁ c

theorem line_map_symm {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} [ring k] [add_comm_group V1]
    [module k V1] [add_torsor V1 P1] (p₀ : P1) (p₁ : P1) :
    line_map p₀ p₁ = comp (line_map p₁ p₀) (line_map 1 0) :=
  sorry

theorem line_map_apply_one_sub {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} [ring k]
    [add_comm_group V1] [module k V1] [add_torsor V1 P1] (p₀ : P1) (p₁ : P1) (c : k) :
    coe_fn (line_map p₀ p₁) (1 - c) = coe_fn (line_map p₁ p₀) c :=
  sorry

@[simp] theorem line_map_vsub_left {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} [ring k]
    [add_comm_group V1] [module k V1] [add_torsor V1 P1] (p₀ : P1) (p₁ : P1) (c : k) :
    coe_fn (line_map p₀ p₁) c -ᵥ p₀ = c • (p₁ -ᵥ p₀) :=
  vadd_vsub (coe_fn (linear_map.to_affine_map (linear_map.smul_right linear_map.id (p₁ -ᵥ p₀))) c)
    (coe_fn (const k k p₀) c)

@[simp] theorem left_vsub_line_map {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} [ring k]
    [add_comm_group V1] [module k V1] [add_torsor V1 P1] (p₀ : P1) (p₁ : P1) (c : k) :
    p₀ -ᵥ coe_fn (line_map p₀ p₁) c = c • (p₀ -ᵥ p₁) :=
  sorry

@[simp] theorem line_map_vsub_right {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} [ring k]
    [add_comm_group V1] [module k V1] [add_torsor V1 P1] (p₀ : P1) (p₁ : P1) (c : k) :
    coe_fn (line_map p₀ p₁) c -ᵥ p₁ = (1 - c) • (p₀ -ᵥ p₁) :=
  sorry

@[simp] theorem right_vsub_line_map {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} [ring k]
    [add_comm_group V1] [module k V1] [add_torsor V1 P1] (p₀ : P1) (p₁ : P1) (c : k) :
    p₁ -ᵥ coe_fn (line_map p₀ p₁) c = (1 - c) • (p₁ -ᵥ p₀) :=
  sorry

theorem line_map_vadd_line_map {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} [ring k]
    [add_comm_group V1] [module k V1] [add_torsor V1 P1] (v₁ : V1) (v₂ : V1) (p₁ : P1) (p₂ : P1)
    (c : k) :
    coe_fn (line_map v₁ v₂) c +ᵥ coe_fn (line_map p₁ p₂) c =
        coe_fn (line_map (v₁ +ᵥ p₁) (v₂ +ᵥ p₂)) c :=
  apply_line_map (fst +ᵥ snd) (v₁, p₁) (v₂, p₂) c

theorem line_map_vsub_line_map {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} [ring k]
    [add_comm_group V1] [module k V1] [add_torsor V1 P1] (p₁ : P1) (p₂ : P1) (p₃ : P1) (p₄ : P1)
    (c : k) :
    coe_fn (line_map p₁ p₂) c -ᵥ coe_fn (line_map p₃ p₄) c =
        coe_fn (line_map (p₁ -ᵥ p₃) (p₂ -ᵥ p₄)) c :=
  apply_line_map (fst -ᵥ snd) (p₁, p₃) (p₂, p₄) c

-- Why Lean fails to find this instance without a hint?

/-- Decomposition of an affine map in the special case when the point space and vector space
are the same. -/
theorem decomp {k : Type u_1} {V1 : Type u_2} {V2 : Type u_4} [ring k] [add_comm_group V1]
    [module k V1] [add_comm_group V2] [module k V2] (f : affine_map k V1 V2) :
    ⇑f = ⇑(linear f) + fun (z : V1) => coe_fn f 0 :=
  sorry

/-- Decomposition of an affine map in the special case when the point space and vector space
are the same. -/
theorem decomp' {k : Type u_1} {V1 : Type u_2} {V2 : Type u_4} [ring k] [add_comm_group V1]
    [module k V1] [add_comm_group V2] [module k V2] (f : affine_map k V1 V2) :
    ⇑(linear f) = ⇑f - fun (z : V1) => coe_fn f 0 :=
  sorry

theorem image_interval {k : Type u_1} [linear_ordered_field k] (f : affine_map k k k) (a : k)
    (b : k) : ⇑f '' set.interval a b = set.interval (coe_fn f a) (coe_fn f b) :=
  sorry

/-- Evaluation at a point as an affine map. -/
def proj {k : Type u_1} [ring k] {ι : Type u_10} {V : ι → Type u_11} {P : ι → Type u_12}
    [(i : ι) → add_comm_group (V i)] [(i : ι) → semimodule k (V i)]
    [(i : ι) → add_torsor (V i) (P i)] (i : ι) : affine_map k ((i : ι) → P i) (P i) :=
  mk (fun (f : (i : ι) → P i) => f i) (linear_map.proj i) sorry

@[simp] theorem proj_apply {k : Type u_1} [ring k] {ι : Type u_10} {V : ι → Type u_11}
    {P : ι → Type u_12} [(i : ι) → add_comm_group (V i)] [(i : ι) → semimodule k (V i)]
    [(i : ι) → add_torsor (V i) (P i)] (i : ι) (f : (i : ι) → P i) : coe_fn (proj i) f = f i :=
  rfl

@[simp] theorem proj_linear {k : Type u_1} [ring k] {ι : Type u_10} {V : ι → Type u_11}
    {P : ι → Type u_12} [(i : ι) → add_comm_group (V i)] [(i : ι) → semimodule k (V i)]
    [(i : ι) → add_torsor (V i) (P i)] (i : ι) : linear (proj i) = linear_map.proj i :=
  rfl

theorem pi_line_map_apply {k : Type u_1} [ring k] {ι : Type u_10} {V : ι → Type u_11}
    {P : ι → Type u_12} [(i : ι) → add_comm_group (V i)] [(i : ι) → semimodule k (V i)]
    [(i : ι) → add_torsor (V i) (P i)] (f : (i : ι) → P i) (g : (i : ι) → P i) (c : k) (i : ι) :
    coe_fn (line_map f g) c i = coe_fn (line_map (f i) (g i)) c :=
  apply_line_map (proj i) f g c

end affine_map


namespace affine_map


/-- If `k` is a commutative ring, then the set of affine maps with codomain in a `k`-module
is a `k`-module. -/
protected instance module {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V2 : Type u_4}
    [comm_ring k] [add_comm_group V1] [module k V1] [add_torsor V1 P1] [add_comm_group V2]
    [module k V2] : module k (affine_map k P1 V2) :=
  semimodule.mk sorry sorry

@[simp] theorem coe_smul {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V2 : Type u_4}
    [comm_ring k] [add_comm_group V1] [module k V1] [add_torsor V1 P1] [add_comm_group V2]
    [module k V2] (c : k) (f : affine_map k P1 V2) : ⇑(c • f) = c • ⇑f :=
  rfl

/-- `homothety c r` is the homothety about `c` with scale factor `r`. -/
def homothety {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} [comm_ring k] [add_comm_group V1]
    [module k V1] [add_torsor V1 P1] (c : P1) (r : k) : affine_map k P1 P1 :=
  r • (id k P1 -ᵥ const k P1 c) +ᵥ const k P1 c

theorem homothety_def {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} [comm_ring k]
    [add_comm_group V1] [module k V1] [add_torsor V1 P1] (c : P1) (r : k) :
    homothety c r = r • (id k P1 -ᵥ const k P1 c) +ᵥ const k P1 c :=
  rfl

theorem homothety_apply {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} [comm_ring k]
    [add_comm_group V1] [module k V1] [add_torsor V1 P1] (c : P1) (r : k) (p : P1) :
    coe_fn (homothety c r) p = r • (p -ᵥ c) +ᵥ c :=
  rfl

theorem homothety_eq_line_map {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} [comm_ring k]
    [add_comm_group V1] [module k V1] [add_torsor V1 P1] (c : P1) (r : k) (p : P1) :
    coe_fn (homothety c r) p = coe_fn (line_map c p) r :=
  rfl

@[simp] theorem homothety_one {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} [comm_ring k]
    [add_comm_group V1] [module k V1] [add_torsor V1 P1] (c : P1) : homothety c 1 = id k P1 :=
  sorry

theorem homothety_mul {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} [comm_ring k]
    [add_comm_group V1] [module k V1] [add_torsor V1 P1] (c : P1) (r₁ : k) (r₂ : k) :
    homothety c (r₁ * r₂) = comp (homothety c r₁) (homothety c r₂) :=
  sorry

@[simp] theorem homothety_zero {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} [comm_ring k]
    [add_comm_group V1] [module k V1] [add_torsor V1 P1] (c : P1) : homothety c 0 = const k P1 c :=
  sorry

@[simp] theorem homothety_add {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} [comm_ring k]
    [add_comm_group V1] [module k V1] [add_torsor V1 P1] (c : P1) (r₁ : k) (r₂ : k) :
    homothety c (r₁ + r₂) = r₁ • (id k P1 -ᵥ const k P1 c) +ᵥ homothety c r₂ :=
  sorry

/-- `homothety` as a multiplicative monoid homomorphism. -/
def homothety_hom {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} [comm_ring k] [add_comm_group V1]
    [module k V1] [add_torsor V1 P1] (c : P1) : k →* affine_map k P1 P1 :=
  monoid_hom.mk (homothety c) (homothety_one c) (homothety_mul c)

@[simp] theorem coe_homothety_hom {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} [comm_ring k]
    [add_comm_group V1] [module k V1] [add_torsor V1 P1] (c : P1) :
    ⇑(homothety_hom c) = homothety c :=
  rfl

/-- `homothety` as an affine map. -/
def homothety_affine {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} [comm_ring k]
    [add_comm_group V1] [module k V1] [add_torsor V1 P1] (c : P1) :
    affine_map k k (affine_map k P1 P1) :=
  mk (homothety c)
    (coe_fn (linear_map.flip (linear_map.lsmul k (affine_map k P1 V1))) (id k P1 -ᵥ const k P1 c))
    sorry

@[simp] theorem coe_homothety_affine {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} [comm_ring k]
    [add_comm_group V1] [module k V1] [add_torsor V1 P1] (c : P1) :
    ⇑(homothety_affine c) = homothety c :=
  rfl

end Mathlib