/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kenny Lau.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.ring_theory.polynomial.default
import Mathlib.algebra.big_operators.basic
import Mathlib.PostPort

universes u 

namespace Mathlib

/-!
# Lagrange interpolation

## Main definitions

* `lagrange.basis s x` where `s : finset F` and `x : F`: the Lagrange basis polynomial
  that evaluates to `1` at `x` and `0` at other elements of `s`.
* `lagrange.interpolate s f` where `s : finset F` and `f : s → F`: the Lagrange interpolant
  that evaluates to `f x` at `x` for `x ∈ s`.

-/

namespace lagrange


/-- Lagrange basis polynomials that evaluate to 1 at `x` and 0 at other elements of `s`. -/
def basis {F : Type u} [DecidableEq F] [field F] (s : finset F) (x : F) : polynomial F :=
  finset.prod (finset.erase s x) fun (y : F) => coe_fn polynomial.C (x - y⁻¹) * (polynomial.X - coe_fn polynomial.C y)

@[simp] theorem basis_empty {F : Type u} [DecidableEq F] [field F] (x : F) : basis ∅ x = 1 :=
  rfl

@[simp] theorem eval_basis_self {F : Type u} [DecidableEq F] [field F] (s : finset F) (x : F) : polynomial.eval x (basis s x) = 1 := sorry

@[simp] theorem eval_basis_ne {F : Type u} [DecidableEq F] [field F] (s : finset F) (x : F) (y : F) (h1 : y ∈ s) (h2 : y ≠ x) : polynomial.eval y (basis s x) = 0 := sorry

theorem eval_basis {F : Type u} [DecidableEq F] [field F] (s : finset F) (x : F) (y : F) (h : y ∈ s) : polynomial.eval y (basis s x) = ite (y = x) 1 0 := sorry

@[simp] theorem nat_degree_basis {F : Type u} [DecidableEq F] [field F] (s : finset F) (x : F) (hx : x ∈ s) : polynomial.nat_degree (basis s x) = finset.card s - 1 := sorry

/-- Lagrange interpolation: given a finset `s` and a function `f : s → F`,
`interpolate s f` is the unique polynomial of degree `< s.card`
that takes value `f x` on all `x` in `s`. -/
def interpolate {F : Type u} [DecidableEq F] [field F] (s : finset F) (f : ↥↑s → F) : polynomial F :=
  finset.sum (finset.attach s) fun (x : Subtype fun (x : F) => x ∈ s) => coe_fn polynomial.C (f x) * basis s ↑x

@[simp] theorem interpolate_empty {F : Type u} [DecidableEq F] [field F] (f : ↥↑∅ → F) : interpolate ∅ f = 0 :=
  rfl

@[simp] theorem eval_interpolate {F : Type u} [DecidableEq F] [field F] (s : finset F) (f : ↥↑s → F) (x : F) (H : x ∈ s) : polynomial.eval x (interpolate s f) = f { val := x, property := H } := sorry

theorem degree_interpolate_lt {F : Type u} [DecidableEq F] [field F] (s : finset F) (f : ↥↑s → F) : polynomial.degree (interpolate s f) < ↑(finset.card s) := sorry

/-- Linear version of `interpolate`. -/
def linterpolate {F : Type u} [DecidableEq F] [field F] (s : finset F) : linear_map F (↥↑s → F) (polynomial F) :=
  linear_map.mk (interpolate s) sorry sorry

@[simp] theorem interpolate_add {F : Type u} [DecidableEq F] [field F] (s : finset F) (f : ↥↑s → F) (g : ↥↑s → F) : interpolate s (f + g) = interpolate s f + interpolate s g :=
  linear_map.map_add (linterpolate s) f g

@[simp] theorem interpolate_zero {F : Type u} [DecidableEq F] [field F] (s : finset F) : interpolate s 0 = 0 :=
  linear_map.map_zero (linterpolate s)

@[simp] theorem interpolate_neg {F : Type u} [DecidableEq F] [field F] (s : finset F) (f : ↥↑s → F) : interpolate s (-f) = -interpolate s f :=
  linear_map.map_neg (linterpolate s) f

@[simp] theorem interpolate_sub {F : Type u} [DecidableEq F] [field F] (s : finset F) (f : ↥↑s → F) (g : ↥↑s → F) : interpolate s (f - g) = interpolate s f - interpolate s g :=
  linear_map.map_sub (linterpolate s) f g

@[simp] theorem interpolate_smul {F : Type u} [DecidableEq F] [field F] (s : finset F) (c : F) (f : ↥↑s → F) : interpolate s (c • f) = c • interpolate s f :=
  linear_map.map_smul (linterpolate s) c f

theorem eq_zero_of_eval_eq_zero {F' : Type u} [field F'] (s' : finset F') {f : polynomial F'} (hf1 : polynomial.degree f < ↑(finset.card s')) (hf2 : ∀ (x : F'), x ∈ s' → polynomial.eval x f = 0) : f = 0 := sorry

theorem eq_of_eval_eq {F' : Type u} [field F'] (s' : finset F') {f : polynomial F'} {g : polynomial F'} (hf : polynomial.degree f < ↑(finset.card s')) (hg : polynomial.degree g < ↑(finset.card s')) (hfg : ∀ (x : F'), x ∈ s' → polynomial.eval x f = polynomial.eval x g) : f = g := sorry

theorem eq_interpolate {F : Type u} [DecidableEq F] [field F] (s : finset F) (f : polynomial F) (hf : polynomial.degree f < ↑(finset.card s)) : (interpolate s fun (x : ↥↑s) => polynomial.eval (↑x) f) = f :=
  eq_of_eval_eq s (degree_interpolate_lt s fun (x : ↥↑s) => polynomial.eval (↑x) f) hf
    fun (x : F) (hx : x ∈ s) => eval_interpolate s (fun (x : ↥↑s) => polynomial.eval (↑x) f) x hx

/-- Lagrange interpolation induces isomorphism between functions from `s` and polynomials
of degree less than `s.card`. -/
def fun_equiv_degree_lt {F : Type u} [DecidableEq F] [field F] (s : finset F) : linear_equiv F (↥(polynomial.degree_lt F (finset.card s))) (↥↑s → F) :=
  linear_equiv.mk (fun (f : ↥(polynomial.degree_lt F (finset.card s))) (x : ↥↑s) => polynomial.eval (↑x) (subtype.val f))
    sorry sorry (fun (f : ↥↑s → F) => { val := interpolate s f, property := sorry }) sorry sorry

