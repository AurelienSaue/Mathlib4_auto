/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.group_theory.congruence
import Mathlib.linear_algebra.multilinear
import Mathlib.PostPort

universes u_1 u_2 u_4 u_3 u_6 u_5 

namespace Mathlib

/-!
# Tensor product of an indexed family of semimodules over commutative semirings

We define the tensor product of an indexed family `s : ι → Type*` of semimodules over commutative
semirings. We denote this space by `⨂[R] i, s i` and define it as `free_add_monoid (R × Π i, s i)`
quotiented by the appropriate equivalence relation. The treatment follows very closely that of the
binary tensor product in `linear_algebra/tensor_product.lean`.

## Main definitions

* `pi_tensor_product R s` with `R` a commutative semiring and `s : ι → Type*` is the tensor product
  of all the `s i`'s. This is denoted by `⨂[R] i, s i`.
* `tprod R f` with `f : Π i, s i` is the tensor product of the vectors `f i` over all `i : ι`.
  This is bundled as a multilinear map from `Π i, s i` to `⨂[R] i, s i`.
* `lift_add_hom` constructs an `add_monoid_hom` from `(⨂[R] i, s i)` to some space `F` from a
  function `φ : (R × Π i, s i) → F` with the appropriate properties.
* `lift φ` with `φ : multilinear_map R s E` is the corresponding linear map
  `(⨂[R] i, s i) →ₗ[R] E`. This is bundled as a linear equivalence.

## Notations

* `⨂[R] i, s i` is defined as localized notation in locale `tensor_product`
* `⨂ₜ[R] i, f i` with `f : Π i, f i` is defined globally as the tensor product of all the `f i`'s.

## Implementation notes

* We define it via `free_add_monoid (R × Π i, s i)` with the `R` representing a "hidden" tensor
  factor, rather than `free_add_monoid (Π i, s i)` to ensure that, if `ι` is an empty type,
  the space is isomorphic to the base ring `R`.
* We have not restricted the index type `ι` to be a `fintype`, as nothing we do here strictly
  requires it. However, problems may arise in the case where `ι` is infinite; use at your own
  caution.

## TODO

* Define tensor powers, symmetric subspace, etc.
* API for the various ways `ι` can be split into subsets; connect this with the binary
  tensor product.
* Include connection with holors.
* Port more of the API from the binary tensor product over to this case.

## Tags

multilinear, tensor, tensor product
-/

namespace pi_tensor_product


/-- The relation on `free_add_monoid (R × Π i, s i)` that generates a congruence whose quotient is
the tensor product. -/
inductive eqv {ι : Type u_1} [DecidableEq ι] (R : Type u_2) [comm_semiring R] (s : ι → Type u_4)
    [(i : ι) → add_comm_monoid (s i)] [(i : ι) → semimodule R (s i)] :
    free_add_monoid (R × ((i : ι) → s i)) → free_add_monoid (R × ((i : ι) → s i)) → Prop
    where
| of_zero : ∀ (r : R) (f : (i : ι) → s i) (i : ι), f i = 0 → eqv R s (free_add_monoid.of (r, f)) 0
| of_zero_scalar : ∀ (f : (i : ι) → s i), eqv R s (free_add_monoid.of (0, f)) 0
| of_add :
    ∀ (r : R) (f : (i : ι) → s i) (i : ι) (m₁ m₂ : s i),
      eqv R s
        (free_add_monoid.of (r, function.update f i m₁) +
          free_add_monoid.of (r, function.update f i m₂))
        (free_add_monoid.of (r, function.update f i (m₁ + m₂)))
| of_add_scalar :
    ∀ (r r' : R) (f : (i : ι) → s i),
      eqv R s (free_add_monoid.of (r, f) + free_add_monoid.of (r', f))
        (free_add_monoid.of (r + r', f))
| of_smul :
    ∀ (r : R) (f : (i : ι) → s i) (i : ι) (r' : R),
      eqv R s (free_add_monoid.of (r, function.update f i (r' • f i)))
        (free_add_monoid.of (r' * r, f))
| add_comm : ∀ (x y : free_add_monoid (R × ((i : ι) → s i))), eqv R s (x + y) (y + x)

end pi_tensor_product


/-- `pi_tensor_product R s` with `R` a commutative semiring and `s : ι → Type*` is the tensor
  product of all the `s i`'s. This is denoted by `⨂[R] i, s i`. -/
def pi_tensor_product {ι : Type u_1} [DecidableEq ι] (R : Type u_2) [comm_semiring R]
    (s : ι → Type u_4) [(i : ι) → add_comm_monoid (s i)] [(i : ι) → semimodule R (s i)] :=
  add_con.quotient (add_con_gen sorry)

/- This enables the notation `⨂[R] i : ι, s i` for the pi tensor product, given `s : ι → Type*`. -/

namespace pi_tensor_product


protected instance add_comm_monoid {ι : Type u_1} [DecidableEq ι] {R : Type u_2} [comm_semiring R]
    (s : ι → Type u_4) [(i : ι) → add_comm_monoid (s i)] [(i : ι) → semimodule R (s i)] :
    add_comm_monoid (pi_tensor_product R fun (i : ι) => s i) :=
  add_comm_monoid.mk add_monoid.add sorry add_monoid.zero sorry sorry sorry

protected instance inhabited {ι : Type u_1} [DecidableEq ι] {R : Type u_2} [comm_semiring R]
    (s : ι → Type u_4) [(i : ι) → add_comm_monoid (s i)] [(i : ι) → semimodule R (s i)] :
    Inhabited (pi_tensor_product R fun (i : ι) => s i) :=
  { default := 0 }

/-- `tprod_coeff R r f` with `r : R` and `f : Π i, s i` is the tensor product of the vectors `f i`
over all `i : ι`, multiplied by the coefficient `r`. Note that this is meant as an auxiliary
definition for this file alone, and that one should use `tprod` defined below for most purposes. -/
def tprod_coeff {ι : Type u_1} [DecidableEq ι] (R : Type u_2) [comm_semiring R] {s : ι → Type u_4}
    [(i : ι) → add_comm_monoid (s i)] [(i : ι) → semimodule R (s i)] (r : R) (f : (i : ι) → s i) :
    pi_tensor_product R fun (i : ι) => s i :=
  coe_fn (add_con.mk' (add_con_gen (eqv R fun (i : ι) => s i))) (free_add_monoid.of (r, f))

theorem zero_tprod_coeff {ι : Type u_1} [DecidableEq ι] {R : Type u_2} [comm_semiring R]
    {s : ι → Type u_4} [(i : ι) → add_comm_monoid (s i)] [(i : ι) → semimodule R (s i)]
    (f : (i : ι) → s i) : tprod_coeff R 0 f = 0 :=
  quotient.sound' (add_con_gen.rel.of (free_add_monoid.of (0, f)) 0 (eqv.of_zero_scalar f))

theorem zero_tprod_coeff' {ι : Type u_1} [DecidableEq ι] {R : Type u_2} [comm_semiring R]
    {s : ι → Type u_4} [(i : ι) → add_comm_monoid (s i)] [(i : ι) → semimodule R (s i)] (z : R)
    (f : (i : ι) → s i) (i : ι) (hf : f i = 0) : tprod_coeff R z f = 0 :=
  quotient.sound' (add_con_gen.rel.of (free_add_monoid.of (z, f)) 0 (eqv.of_zero z f i hf))

theorem add_tprod_coeff {ι : Type u_1} [DecidableEq ι] {R : Type u_2} [comm_semiring R]
    {s : ι → Type u_4} [(i : ι) → add_comm_monoid (s i)] [(i : ι) → semimodule R (s i)] (z : R)
    (f : (i : ι) → s i) (i : ι) (m₁ : s i) (m₂ : s i) :
    tprod_coeff R z (function.update f i m₁) + tprod_coeff R z (function.update f i m₂) =
        tprod_coeff R z (function.update f i (m₁ + m₂)) :=
  quotient.sound'
    (add_con_gen.rel.of
      (free_add_monoid.of (z, function.update f i m₁) +
        free_add_monoid.of (z, function.update f i m₂))
      (free_add_monoid.of (z, function.update f i (m₁ + m₂))) (eqv.of_add z f i m₁ m₂))

theorem add_tprod_coeff' {ι : Type u_1} [DecidableEq ι] {R : Type u_2} [comm_semiring R]
    {s : ι → Type u_4} [(i : ι) → add_comm_monoid (s i)] [(i : ι) → semimodule R (s i)] (z₁ : R)
    (z₂ : R) (f : (i : ι) → s i) :
    tprod_coeff R z₁ f + tprod_coeff R z₂ f = tprod_coeff R (z₁ + z₂) f :=
  quotient.sound'
    (add_con_gen.rel.of (free_add_monoid.of (z₁, f) + free_add_monoid.of (z₂, f))
      (free_add_monoid.of (z₁ + z₂, f)) (eqv.of_add_scalar z₁ z₂ f))

theorem smul_tprod_coeff_aux {ι : Type u_1} [DecidableEq ι] {R : Type u_2} [comm_semiring R]
    {s : ι → Type u_4} [(i : ι) → add_comm_monoid (s i)] [(i : ι) → semimodule R (s i)] (z : R)
    (f : (i : ι) → s i) (i : ι) (r : R) :
    tprod_coeff R z (function.update f i (r • f i)) = tprod_coeff R (r * z) f :=
  quotient.sound'
    (add_con_gen.rel.of (free_add_monoid.of (z, function.update f i (r • f i)))
      (free_add_monoid.of (r * z, f)) (eqv.of_smul z f i r))

theorem smul_tprod_coeff {ι : Type u_1} [DecidableEq ι] {R : Type u_2} [comm_semiring R]
    {R' : Type u_3} [comm_semiring R'] [algebra R' R] {s : ι → Type u_4}
    [(i : ι) → add_comm_monoid (s i)] [(i : ι) → semimodule R (s i)] (z : R) (f : (i : ι) → s i)
    (i : ι) (r : R') [semimodule R' (s i)] [is_scalar_tower R' R (s i)] :
    tprod_coeff R z (function.update f i (r • f i)) = tprod_coeff R (r • z) f :=
  sorry

/-- Construct an `add_monoid_hom` from `(⨂[R] i, s i)` to some space `F` from a function
`φ : (R × Π i, s i) → F` with the appropriate properties. -/
def lift_add_hom {ι : Type u_1} [DecidableEq ι] {R : Type u_2} [comm_semiring R] {s : ι → Type u_4}
    [(i : ι) → add_comm_monoid (s i)] [(i : ι) → semimodule R (s i)] {F : Type u_6}
    [add_comm_monoid F] (φ : R × ((i : ι) → s i) → F)
    (C0 : ∀ (r : R) (f : (i : ι) → s i) (i : ι), f i = 0 → φ (r, f) = 0)
    (C0' : ∀ (f : (i : ι) → s i), φ (0, f) = 0)
    (C_add :
      ∀ (r : R) (f : (i : ι) → s i) (i : ι) (m₁ m₂ : s i),
        φ (r, function.update f i m₁) + φ (r, function.update f i m₂) =
          φ (r, function.update f i (m₁ + m₂)))
    (C_add_scalar : ∀ (r r' : R) (f : (i : ι) → s i), φ (r, f) + φ (r', f) = φ (r + r', f))
    (C_smul :
      ∀ (r : R) (f : (i : ι) → s i) (i : ι) (r' : R),
        φ (r, function.update f i (r' • f i)) = φ (r' * r, f)) :
    (pi_tensor_product R fun (i : ι) => s i) →+ F :=
  add_con.lift (add_con_gen (eqv R s)) (coe_fn free_add_monoid.lift φ) sorry

-- Most of the time we want the instance below this one, which is easier for typeclass resolution

-- to find.

protected instance has_scalar' {ι : Type u_1} [DecidableEq ι] {R : Type u_2} [comm_semiring R]
    {R' : Type u_3} [comm_semiring R'] [algebra R' R] {s : ι → Type u_4}
    [(i : ι) → add_comm_monoid (s i)] [(i : ι) → semimodule R (s i)] :
    has_scalar R' (pi_tensor_product R fun (i : ι) => s i) :=
  has_scalar.mk
    fun (r : R') =>
      ⇑(lift_add_hom (fun (f : R × ((i : ι) → s i)) => tprod_coeff R (r • prod.fst f) (prod.snd f))
          sorry sorry sorry sorry sorry)

protected instance has_scalar {ι : Type u_1} [DecidableEq ι] {R : Type u_2} [comm_semiring R]
    {s : ι → Type u_4} [(i : ι) → add_comm_monoid (s i)] [(i : ι) → semimodule R (s i)] :
    has_scalar R (pi_tensor_product R fun (i : ι) => s i) :=
  pi_tensor_product.has_scalar'

theorem smul_tprod_coeff' {ι : Type u_1} [DecidableEq ι] {R : Type u_2} [comm_semiring R]
    {R' : Type u_3} [comm_semiring R'] [algebra R' R] {s : ι → Type u_4}
    [(i : ι) → add_comm_monoid (s i)] [(i : ι) → semimodule R (s i)] (r : R') (z : R)
    (f : (i : ι) → s i) : r • tprod_coeff R z f = tprod_coeff R (r • z) f :=
  rfl

protected theorem smul_add {ι : Type u_1} [DecidableEq ι] {R : Type u_2} [comm_semiring R]
    {R' : Type u_3} [comm_semiring R'] [algebra R' R] {s : ι → Type u_4}
    [(i : ι) → add_comm_monoid (s i)] [(i : ι) → semimodule R (s i)] (r : R')
    (x : pi_tensor_product R fun (i : ι) => s i) (y : pi_tensor_product R fun (i : ι) => s i) :
    r • (x + y) = r • x + r • y :=
  sorry

protected theorem induction_on' {ι : Type u_1} [DecidableEq ι] {R : Type u_2} [comm_semiring R]
    {s : ι → Type u_4} [(i : ι) → add_comm_monoid (s i)] [(i : ι) → semimodule R (s i)]
    {C : (pi_tensor_product R fun (i : ι) => s i) → Prop}
    (z : pi_tensor_product R fun (i : ι) => s i)
    (C1 : ∀ {r : R} {f : (i : ι) → s i}, C (tprod_coeff R r f))
    (Cp : ∀ {x y : pi_tensor_product R fun (i : ι) => s i}, C x → C y → C (x + y)) : C z :=
  sorry

-- Most of the time we want the instance below this one, which is easier for typeclass resolution

-- to find.

protected instance semimodule' {ι : Type u_1} [DecidableEq ι] {R : Type u_2} [comm_semiring R]
    {R' : Type u_3} [comm_semiring R'] [algebra R' R] {s : ι → Type u_4}
    [(i : ι) → add_comm_monoid (s i)] [(i : ι) → semimodule R (s i)] :
    semimodule R' (pi_tensor_product R fun (i : ι) => s i) :=
  semimodule.mk sorry sorry

protected instance semimodule {ι : Type u_1} [DecidableEq ι] {R : Type u_2} [comm_semiring R]
    {R' : Type u_3} [comm_semiring R'] [algebra R' R] {s : ι → Type u_4}
    [(i : ι) → add_comm_monoid (s i)] [(i : ι) → semimodule R (s i)] :
    semimodule R' (pi_tensor_product R fun (i : ι) => s i) :=
  pi_tensor_product.semimodule'

/-- The canonical `multilinear_map R s (⨂[R] i, s i)`. -/
def tprod {ι : Type u_1} [DecidableEq ι] (R : Type u_2) [comm_semiring R] {s : ι → Type u_4}
    [(i : ι) → add_comm_monoid (s i)] [(i : ι) → semimodule R (s i)] :
    multilinear_map R s (pi_tensor_product R fun (i : ι) => s i) :=
  multilinear_map.mk (tprod_coeff R 1) sorry sorry

@[simp] theorem tprod_coeff_eq_smul_tprod {ι : Type u_1} [DecidableEq ι] {R : Type u_2}
    [comm_semiring R] {s : ι → Type u_4} [(i : ι) → add_comm_monoid (s i)]
    [(i : ι) → semimodule R (s i)] (z : R) (f : (i : ι) → s i) :
    tprod_coeff R z f = z • coe_fn (tprod R) f :=
  sorry

protected theorem induction_on {ι : Type u_1} [DecidableEq ι] {R : Type u_2} [comm_semiring R]
    {s : ι → Type u_4} [(i : ι) → add_comm_monoid (s i)] [(i : ι) → semimodule R (s i)]
    {C : (pi_tensor_product R fun (i : ι) => s i) → Prop}
    (z : pi_tensor_product R fun (i : ι) => s i)
    (C1 : ∀ {r : R} {f : (i : ι) → s i}, C (r • coe_fn (tprod R) f))
    (Cp : ∀ {x y : pi_tensor_product R fun (i : ι) => s i}, C x → C y → C (x + y)) : C z :=
  sorry

theorem ext {ι : Type u_1} [DecidableEq ι] {R : Type u_2} [comm_semiring R] {s : ι → Type u_4}
    [(i : ι) → add_comm_monoid (s i)] [(i : ι) → semimodule R (s i)] {E : Type u_5}
    [add_comm_monoid E] [semimodule R E]
    {φ₁ : linear_map R (pi_tensor_product R fun (i : ι) => s i) E}
    {φ₂ : linear_map R (pi_tensor_product R fun (i : ι) => s i) E}
    (H :
      linear_map.comp_multilinear_map φ₁ (tprod R) = linear_map.comp_multilinear_map φ₂ (tprod R)) :
    φ₁ = φ₂ :=
  sorry

/-- Auxiliary function to constructing a linear map `(⨂[R] i, s i) → E` given a
`multilinear map R s E` with the property that its composition with the canonical
`multilinear_map R s (⨂[R] i, s i)` is the given multilinear map. -/
def lift_aux {ι : Type u_1} [DecidableEq ι] {R : Type u_2} [comm_semiring R] {s : ι → Type u_4}
    [(i : ι) → add_comm_monoid (s i)] [(i : ι) → semimodule R (s i)] {E : Type u_5}
    [add_comm_monoid E] [semimodule R E] (φ : multilinear_map R s E) :
    (pi_tensor_product R fun (i : ι) => s i) →+ E :=
  lift_add_hom (fun (p : R × ((i : ι) → s i)) => prod.fst p • coe_fn φ (prod.snd p)) sorry sorry
    sorry sorry sorry

theorem lift_aux_tprod {ι : Type u_1} [DecidableEq ι] {R : Type u_2} [comm_semiring R]
    {s : ι → Type u_4} [(i : ι) → add_comm_monoid (s i)] [(i : ι) → semimodule R (s i)]
    {E : Type u_5} [add_comm_monoid E] [semimodule R E] (φ : multilinear_map R s E)
    (f : (i : ι) → s i) : coe_fn (lift_aux φ) (coe_fn (tprod R) f) = coe_fn φ f :=
  sorry

theorem lift_aux_tprod_coeff {ι : Type u_1} [DecidableEq ι] {R : Type u_2} [comm_semiring R]
    {s : ι → Type u_4} [(i : ι) → add_comm_monoid (s i)] [(i : ι) → semimodule R (s i)]
    {E : Type u_5} [add_comm_monoid E] [semimodule R E] (φ : multilinear_map R s E) (z : R)
    (f : (i : ι) → s i) : coe_fn (lift_aux φ) (tprod_coeff R z f) = z • coe_fn φ f :=
  sorry

theorem lift_aux.smul {ι : Type u_1} [DecidableEq ι] {R : Type u_2} [comm_semiring R]
    {s : ι → Type u_4} [(i : ι) → add_comm_monoid (s i)] [(i : ι) → semimodule R (s i)]
    {E : Type u_5} [add_comm_monoid E] [semimodule R E] {φ : multilinear_map R s E} (r : R)
    (x : pi_tensor_product R fun (i : ι) => s i) :
    coe_fn (lift_aux φ) (r • x) = r • coe_fn (lift_aux φ) x :=
  sorry

/-- Constructing a linear map `(⨂[R] i, s i) → E` given a `multilinear_map R s E` with the
property that its composition with the canonical `multilinear_map R s E` is
the given multilinear map `φ`. -/
def lift {ι : Type u_1} [DecidableEq ι] {R : Type u_2} [comm_semiring R] {s : ι → Type u_4}
    [(i : ι) → add_comm_monoid (s i)] [(i : ι) → semimodule R (s i)] {E : Type u_5}
    [add_comm_monoid E] [semimodule R E] :
    linear_equiv R (multilinear_map R s E)
        (linear_map R (pi_tensor_product R fun (i : ι) => s i) E) :=
  linear_equiv.mk
    (fun (φ : multilinear_map R s E) =>
      linear_map.mk (add_monoid_hom.to_fun (lift_aux φ)) sorry sorry)
    sorry sorry
    (fun (φ' : linear_map R (pi_tensor_product R fun (i : ι) => s i) E) =>
      linear_map.comp_multilinear_map φ' (tprod R))
    sorry sorry

@[simp] theorem lift.tprod {ι : Type u_1} [DecidableEq ι] {R : Type u_2} [comm_semiring R]
    {s : ι → Type u_4} [(i : ι) → add_comm_monoid (s i)] [(i : ι) → semimodule R (s i)]
    {E : Type u_5} [add_comm_monoid E] [semimodule R E] {φ : multilinear_map R s E}
    (f : (i : ι) → s i) : coe_fn (coe_fn lift φ) (coe_fn (tprod R) f) = coe_fn φ f :=
  lift_aux_tprod φ f

theorem lift.unique' {ι : Type u_1} [DecidableEq ι] {R : Type u_2} [comm_semiring R]
    {s : ι → Type u_4} [(i : ι) → add_comm_monoid (s i)] [(i : ι) → semimodule R (s i)]
    {E : Type u_5} [add_comm_monoid E] [semimodule R E] {φ : multilinear_map R s E}
    {φ' : linear_map R (pi_tensor_product R fun (i : ι) => s i) E}
    (H : linear_map.comp_multilinear_map φ' (tprod R) = φ) : φ' = coe_fn lift φ :=
  ext (Eq.symm H ▸ Eq.symm (linear_equiv.symm_apply_apply lift φ))

theorem lift.unique {ι : Type u_1} [DecidableEq ι] {R : Type u_2} [comm_semiring R]
    {s : ι → Type u_4} [(i : ι) → add_comm_monoid (s i)] [(i : ι) → semimodule R (s i)]
    {E : Type u_5} [add_comm_monoid E] [semimodule R E] {φ : multilinear_map R s E}
    {φ' : linear_map R (pi_tensor_product R fun (i : ι) => s i) E}
    (H : ∀ (f : (i : ι) → s i), coe_fn φ' (coe_fn (tprod R) f) = coe_fn φ f) : φ' = coe_fn lift φ :=
  lift.unique' (multilinear_map.ext H)

theorem lift_tprod {ι : Type u_1} [DecidableEq ι] {R : Type u_2} [comm_semiring R]
    {s : ι → Type u_4} [(i : ι) → add_comm_monoid (s i)] [(i : ι) → semimodule R (s i)] :
    coe_fn lift (tprod R) = linear_map.id :=
  Eq.symm (lift.unique' rfl)

end pi_tensor_product


namespace pi_tensor_product


/- Unlike for the binary tensor product, we require `R` to be a `comm_ring` here, otherwise
this is false in the case where `ι` is empty. -/

protected instance add_comm_group {ι : Type u_1} [DecidableEq ι] {R : Type u_2} [comm_ring R]
    {s : ι → Type u_3} [(i : ι) → add_comm_group (s i)] [(i : ι) → module R (s i)] :
    add_comm_group (pi_tensor_product R fun (i : ι) => s i) :=
  semimodule.add_comm_monoid_to_add_comm_group R

end Mathlib