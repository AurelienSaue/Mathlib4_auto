/-
Copyright (c) 2020 Johan Commelin and Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin and Robert Y. Lewis
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.mv_polynomial.rename
import Mathlib.PostPort

universes u_1 u_2 u_3 u_4 u_5 

namespace Mathlib

/-!

# Monad operations on `mv_polynomial`

This file defines two monadic operations on `mv_polynomial`. Given `p : mv_polynomial σ R`,

* `mv_polynomial.bind₁` and `mv_polynomial.join₁` operate on the variable type `σ`.
* `mv_polynomial.bind₂` and `mv_polynomial.join₂` operate on the coefficient type `R`.

- `mv_polynomial.bind₁ f φ` with `f : σ → mv_polynomial τ R` and `φ : mv_polynomial σ R`,
  is the polynomial `φ(f 1, ..., f i, ...) : mv_polynomial τ R`.
- `mv_polynomial.join₁ φ` with `φ : mv_polynomial (mv_polynomial σ R) R` collapses `φ` to
  a `mv_polynomial σ R`, by evaluating `φ` under the map `X f ↦ f` for `f : mv_polynomial σ R`.
  In other words, if you have a polynomial `φ` in a set of variables indexed by a polynomial ring,
  you evaluate the polynomial in these indexing polynomials.
- `mv_polynomial.bind₂ f φ` with `f : R →+* mv_polynomial σ S` and `φ : mv_polynomial σ R`
  is the `mv_polynomial σ S` obtained from `φ` by mapping the coefficients of `φ` through `f`
  and considering the resulting polynomial as polynomial expression in `mv_polynomial σ R`.
- `mv_polynomial.join₂ φ` with `φ : mv_polynomial σ (mv_polynomial σ R)` collapses `φ` to
  a `mv_polynomial σ R`, by considering `φ` as polynomial expression in `mv_polynomial σ R`.

These operations themselves have algebraic structure: `mv_polynomial.bind₁`
and `mv_polynomial.join₁` are algebra homs and
`mv_polynomial.bind₂` and `mv_polynomial.join₂` are ring homs.

They interact in convenient ways with `mv_polynomial.rename`, `mv_polynomial.map`,
`mv_polynomial.vars`, and other polynomial operations.
Indeed, `mv_polynomial.rename` is the "map" operation for the (`bind₁`, `join₁`) pair,
whereas `mv_polynomial.map` is the "map" operation for the other pair.

## Implementation notes

We add an `is_lawful_monad` instance for the (`bind₁`, `join₁`) pair.
The second pair cannot be instantiated as a `monad`,
since it is not a monad in `Type` but in `CommRing` (or rather `CommSemiRing`).

-/

namespace mv_polynomial


/--
`bind₁` is the "left hand side" bind operation on `mv_polynomial`, operating on the variable type.
Given a polynomial `p : mv_polynomial σ R` and a map `f : σ → mv_polynomial τ R` taking variables
in `p` to polynomials in the variable type `τ`, `bind₁ f p` replaces each variable in `p` with
its value under `f`, producing a new polynomial in `τ`. The coefficient type remains the same.
This operation is an algebra hom.
-/
def bind₁ {σ : Type u_1} {τ : Type u_2} {R : Type u_3} [comm_semiring R]
    (f : σ → mv_polynomial τ R) : alg_hom R (mv_polynomial σ R) (mv_polynomial τ R) :=
  aeval f

/--
`bind₂` is the "right hand side" bind operation on `mv_polynomial`, operating on the coefficient type.
Given a polynomial `p : mv_polynomial σ R` and a map `f : R → mv_polynomial σ S` taking coefficients
in `p` to polynomials over a new ring `S`, `bind₂ f p` replaces each coefficient in `p` with its
value under `f`, producing a new polynomial over `S`. The variable type remains the same.
This operation is a ring hom.
-/
def bind₂ {σ : Type u_1} {R : Type u_3} {S : Type u_4} [comm_semiring R] [comm_semiring S]
    (f : R →+* mv_polynomial σ S) : mv_polynomial σ R →+* mv_polynomial σ S :=
  eval₂_hom f X

/--
`join₁` is the monadic join operation corresponding to `mv_polynomial.bind₁`. Given a polynomial `p`
with coefficients in `R` whose variables are polynomials in `σ` with coefficients in `R`,
`join₁ p` collapses `p` to a polynomial with variables in `σ` and coefficients in `R`.
This operation is an algebra hom.
-/
def join₁ {σ : Type u_1} {R : Type u_3} [comm_semiring R] :
    alg_hom R (mv_polynomial (mv_polynomial σ R) R) (mv_polynomial σ R) :=
  aeval id

/--
`join₂` is the monadic join operation corresponding to `mv_polynomial.bind₂`. Given a polynomial `p`
with variables in `σ` whose coefficients are polynomials in `σ` with coefficients in `R`,
`join₂ p` collapses `p` to a polynomial with variables in `σ` and coefficients in `R`.
This operation is a ring hom.
-/
def join₂ {σ : Type u_1} {R : Type u_3} [comm_semiring R] :
    mv_polynomial σ (mv_polynomial σ R) →+* mv_polynomial σ R :=
  eval₂_hom (ring_hom.id (mv_polynomial σ R)) X

@[simp] theorem aeval_eq_bind₁ {σ : Type u_1} {τ : Type u_2} {R : Type u_3} [comm_semiring R]
    (f : σ → mv_polynomial τ R) : aeval f = bind₁ f :=
  rfl

@[simp] theorem eval₂_hom_C_eq_bind₁ {σ : Type u_1} {τ : Type u_2} {R : Type u_3} [comm_semiring R]
    (f : σ → mv_polynomial τ R) : eval₂_hom C f = ↑(bind₁ f) :=
  rfl

@[simp] theorem eval₂_hom_eq_bind₂ {σ : Type u_1} {R : Type u_3} {S : Type u_4} [comm_semiring R]
    [comm_semiring S] (f : R →+* mv_polynomial σ S) : eval₂_hom f X = bind₂ f :=
  rfl

@[simp] theorem aeval_id_eq_join₁ (σ : Type u_1) (R : Type u_3) [comm_semiring R] :
    aeval id = join₁ :=
  rfl

theorem eval₂_hom_C_id_eq_join₁ (σ : Type u_1) (R : Type u_3) [comm_semiring R]
    (φ : mv_polynomial (mv_polynomial σ R) R) : coe_fn (eval₂_hom C id) φ = coe_fn join₁ φ :=
  rfl

@[simp] theorem eval₂_hom_id_X_eq_join₂ (σ : Type u_1) (R : Type u_3) [comm_semiring R] :
    eval₂_hom (ring_hom.id (mv_polynomial σ R)) X = join₂ :=
  rfl

-- In this file, we don't want to use these simp lemmas,

-- because we first need to show how these new definitions interact

-- and the proofs fall back on unfolding the definitions and call simp afterwards

@[simp] theorem bind₁_X_right {σ : Type u_1} {τ : Type u_2} {R : Type u_3} [comm_semiring R]
    (f : σ → mv_polynomial τ R) (i : σ) : coe_fn (bind₁ f) (X i) = f i :=
  aeval_X f i

@[simp] theorem bind₂_X_right {σ : Type u_1} {R : Type u_3} {S : Type u_4} [comm_semiring R]
    [comm_semiring S] (f : R →+* mv_polynomial σ S) (i : σ) : coe_fn (bind₂ f) (X i) = X i :=
  eval₂_hom_X' f X i

@[simp] theorem bind₁_X_left {σ : Type u_1} {R : Type u_3} [comm_semiring R] :
    bind₁ X = alg_hom.id R (mv_polynomial σ R) :=
  sorry

theorem aeval_X_left {σ : Type u_1} {R : Type u_3} [comm_semiring R] :
    aeval X = alg_hom.id R (mv_polynomial σ R) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (aeval X = alg_hom.id R (mv_polynomial σ R))) (aeval_eq_bind₁ X)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (bind₁ X = alg_hom.id R (mv_polynomial σ R))) bind₁_X_left))
      (Eq.refl (alg_hom.id R (mv_polynomial σ R))))

theorem aeval_X_left_apply {σ : Type u_1} {R : Type u_3} [comm_semiring R] (φ : mv_polynomial σ R) :
    coe_fn (aeval X) φ = φ :=
  sorry

@[simp] theorem bind₁_C_right {σ : Type u_1} {τ : Type u_2} {R : Type u_3} [comm_semiring R]
    (f : σ → mv_polynomial τ R) (x : R) : coe_fn (bind₁ f) (coe_fn C x) = coe_fn C x :=
  sorry

@[simp] theorem bind₂_C_right {σ : Type u_1} {R : Type u_3} {S : Type u_4} [comm_semiring R]
    [comm_semiring S] (f : R →+* mv_polynomial σ S) (r : R) :
    coe_fn (bind₂ f) (coe_fn C r) = coe_fn f r :=
  eval₂_hom_C f X r

@[simp] theorem bind₂_C_left {σ : Type u_1} {R : Type u_3} [comm_semiring R] :
    bind₂ C = ring_hom.id (mv_polynomial σ R) :=
  sorry

@[simp] theorem bind₂_comp_C {σ : Type u_1} {R : Type u_3} {S : Type u_4} [comm_semiring R]
    [comm_semiring S] (f : R →+* mv_polynomial σ S) : ring_hom.comp (bind₂ f) C = f :=
  ring_hom.ext (bind₂_C_right f)

@[simp] theorem join₂_map {σ : Type u_1} {R : Type u_3} {S : Type u_4} [comm_semiring R]
    [comm_semiring S] (f : R →+* mv_polynomial σ S) (φ : mv_polynomial σ R) :
    coe_fn join₂ (coe_fn (map f) φ) = coe_fn (bind₂ f) φ :=
  sorry

@[simp] theorem join₂_comp_map {σ : Type u_1} {R : Type u_3} {S : Type u_4} [comm_semiring R]
    [comm_semiring S] (f : R →+* mv_polynomial σ S) : ring_hom.comp join₂ (map f) = bind₂ f :=
  ring_hom.ext (join₂_map f)

theorem aeval_id_rename {σ : Type u_1} {τ : Type u_2} {R : Type u_3} [comm_semiring R]
    (f : σ → mv_polynomial τ R) (p : mv_polynomial σ R) :
    coe_fn (aeval id) (coe_fn (rename f) p) = coe_fn (aeval f) p :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (coe_fn (aeval id) (coe_fn (rename f) p) = coe_fn (aeval f) p))
        (aeval_rename f id p)))
    (eq.mpr
      (id
        (Eq._oldrec (Eq.refl (coe_fn (aeval (id ∘ f)) p = coe_fn (aeval f) p))
          (function.comp.left_id f)))
      (Eq.refl (coe_fn (aeval f) p)))

@[simp] theorem join₁_rename {σ : Type u_1} {τ : Type u_2} {R : Type u_3} [comm_semiring R]
    (f : σ → mv_polynomial τ R) (φ : mv_polynomial σ R) :
    coe_fn join₁ (coe_fn (rename f) φ) = coe_fn (bind₁ f) φ :=
  aeval_id_rename f φ

@[simp] theorem bind₁_id {σ : Type u_1} {R : Type u_3} [comm_semiring R] : bind₁ id = join₁ := rfl

@[simp] theorem bind₂_id {σ : Type u_1} {R : Type u_3} [comm_semiring R] :
    bind₂ (ring_hom.id (mv_polynomial σ R)) = join₂ :=
  rfl

theorem bind₁_bind₁ {σ : Type u_1} {τ : Type u_2} {R : Type u_3} [comm_semiring R] {υ : Type u_4}
    (f : σ → mv_polynomial τ R) (g : τ → mv_polynomial υ R) (φ : mv_polynomial σ R) :
    coe_fn (bind₁ g) (coe_fn (bind₁ f) φ) =
        coe_fn (bind₁ fun (i : σ) => coe_fn (bind₁ g) (f i)) φ :=
  sorry

theorem bind₁_comp_bind₁ {σ : Type u_1} {τ : Type u_2} {R : Type u_3} [comm_semiring R]
    {υ : Type u_4} (f : σ → mv_polynomial τ R) (g : τ → mv_polynomial υ R) :
    alg_hom.comp (bind₁ g) (bind₁ f) = bind₁ fun (i : σ) => coe_fn (bind₁ g) (f i) :=
  alg_hom_ext fun (i : σ) => bind₁_bind₁ (fun (n : σ) => f n) (fun (n : τ) => g n) (X i)

theorem bind₂_comp_bind₂ {σ : Type u_1} {R : Type u_3} {S : Type u_4} {T : Type u_5}
    [comm_semiring R] [comm_semiring S] [comm_semiring T] (f : R →+* mv_polynomial σ S)
    (g : S →+* mv_polynomial σ T) :
    ring_hom.comp (bind₂ g) (bind₂ f) = bind₂ (ring_hom.comp (bind₂ g) f) :=
  sorry

theorem bind₂_bind₂ {σ : Type u_1} {R : Type u_3} {S : Type u_4} {T : Type u_5} [comm_semiring R]
    [comm_semiring S] [comm_semiring T] (f : R →+* mv_polynomial σ S) (g : S →+* mv_polynomial σ T)
    (φ : mv_polynomial σ R) :
    coe_fn (bind₂ g) (coe_fn (bind₂ f) φ) = coe_fn (bind₂ (ring_hom.comp (bind₂ g) f)) φ :=
  ring_hom.congr_fun (bind₂_comp_bind₂ f g) φ

theorem rename_comp_bind₁ {σ : Type u_1} {τ : Type u_2} {R : Type u_3} [comm_semiring R]
    {υ : Type u_4} (f : σ → mv_polynomial τ R) (g : τ → υ) :
    alg_hom.comp (rename g) (bind₁ f) = bind₁ fun (i : σ) => coe_fn (rename g) (f i) :=
  sorry

theorem rename_bind₁ {σ : Type u_1} {τ : Type u_2} {R : Type u_3} [comm_semiring R] {υ : Type u_4}
    (f : σ → mv_polynomial τ R) (g : τ → υ) (φ : mv_polynomial σ R) :
    coe_fn (rename g) (coe_fn (bind₁ f) φ) =
        coe_fn (bind₁ fun (i : σ) => coe_fn (rename g) (f i)) φ :=
  alg_hom.congr_fun (rename_comp_bind₁ f g) φ

theorem map_bind₂ {σ : Type u_1} {R : Type u_3} {S : Type u_4} {T : Type u_5} [comm_semiring R]
    [comm_semiring S] [comm_semiring T] (f : R →+* mv_polynomial σ S) (g : S →+* T)
    (φ : mv_polynomial σ R) :
    coe_fn (map g) (coe_fn (bind₂ f) φ) = coe_fn (bind₂ (ring_hom.comp (map g) f)) φ :=
  sorry

theorem bind₁_comp_rename {σ : Type u_1} {τ : Type u_2} {R : Type u_3} [comm_semiring R]
    {υ : Type u_4} (f : τ → mv_polynomial υ R) (g : σ → τ) :
    alg_hom.comp (bind₁ f) (rename g) = bind₁ (f ∘ g) :=
  sorry

theorem bind₁_rename {σ : Type u_1} {τ : Type u_2} {R : Type u_3} [comm_semiring R] {υ : Type u_4}
    (f : τ → mv_polynomial υ R) (g : σ → τ) (φ : mv_polynomial σ R) :
    coe_fn (bind₁ f) (coe_fn (rename g) φ) = coe_fn (bind₁ (f ∘ g)) φ :=
  alg_hom.congr_fun (bind₁_comp_rename f g) φ

theorem bind₂_map {σ : Type u_1} {R : Type u_3} {S : Type u_4} {T : Type u_5} [comm_semiring R]
    [comm_semiring S] [comm_semiring T] (f : S →+* mv_polynomial σ T) (g : R →+* S)
    (φ : mv_polynomial σ R) :
    coe_fn (bind₂ f) (coe_fn (map g) φ) = coe_fn (bind₂ (ring_hom.comp f g)) φ :=
  sorry

@[simp] theorem map_comp_C {σ : Type u_1} {R : Type u_3} {S : Type u_4} [comm_semiring R]
    [comm_semiring S] (f : R →+* S) : ring_hom.comp (map f) C = ring_hom.comp C f :=
  ring_hom.ext fun (x : R) => map_C f x

-- mixing the two monad structures

theorem hom_bind₁ {σ : Type u_1} {τ : Type u_2} {R : Type u_3} {S : Type u_4} [comm_semiring R]
    [comm_semiring S] (f : mv_polynomial τ R →+* S) (g : σ → mv_polynomial τ R)
    (φ : mv_polynomial σ R) :
    coe_fn f (coe_fn (bind₁ g) φ) =
        coe_fn (eval₂_hom (ring_hom.comp f C) fun (i : σ) => coe_fn f (g i)) φ :=
  sorry

theorem map_bind₁ {σ : Type u_1} {τ : Type u_2} {R : Type u_3} {S : Type u_4} [comm_semiring R]
    [comm_semiring S] (f : R →+* S) (g : σ → mv_polynomial τ R) (φ : mv_polynomial σ R) :
    coe_fn (map f) (coe_fn (bind₁ g) φ) =
        coe_fn (bind₁ fun (i : σ) => coe_fn (map f) (g i)) (coe_fn (map f) φ) :=
  sorry

@[simp] theorem eval₂_hom_comp_C {σ : Type u_1} {R : Type u_3} {S : Type u_4} [comm_semiring R]
    [comm_semiring S] (f : R →+* S) (g : σ → S) : ring_hom.comp (eval₂_hom f g) C = f :=
  ring_hom.ext fun (r : R) => eval₂_C f g r

theorem eval₂_hom_bind₁ {σ : Type u_1} {τ : Type u_2} {R : Type u_3} {S : Type u_4}
    [comm_semiring R] [comm_semiring S] (f : R →+* S) (g : τ → S) (h : σ → mv_polynomial τ R)
    (φ : mv_polynomial σ R) :
    coe_fn (eval₂_hom f g) (coe_fn (bind₁ h) φ) =
        coe_fn (eval₂_hom f fun (i : σ) => coe_fn (eval₂_hom f g) (h i)) φ :=
  sorry

theorem aeval_bind₁ {σ : Type u_1} {τ : Type u_2} {R : Type u_3} {S : Type u_4} [comm_semiring R]
    [comm_semiring S] [algebra R S] (f : τ → S) (g : σ → mv_polynomial τ R)
    (φ : mv_polynomial σ R) :
    coe_fn (aeval f) (coe_fn (bind₁ g) φ) =
        coe_fn (aeval fun (i : σ) => coe_fn (aeval f) (g i)) φ :=
  eval₂_hom_bind₁ (algebra_map R S) (fun (n : τ) => f n) g φ

theorem aeval_comp_bind₁ {σ : Type u_1} {τ : Type u_2} {R : Type u_3} {S : Type u_4}
    [comm_semiring R] [comm_semiring S] [algebra R S] (f : τ → S) (g : σ → mv_polynomial τ R) :
    alg_hom.comp (aeval f) (bind₁ g) = aeval fun (i : σ) => coe_fn (aeval f) (g i) :=
  alg_hom_ext fun (i : σ) => aeval_bind₁ (fun (n : τ) => f n) (fun (n : σ) => g n) (X i)

theorem eval₂_hom_comp_bind₂ {σ : Type u_1} {R : Type u_3} {S : Type u_4} {T : Type u_5}
    [comm_semiring R] [comm_semiring S] [comm_semiring T] (f : S →+* T) (g : σ → T)
    (h : R →+* mv_polynomial σ S) :
    ring_hom.comp (eval₂_hom f g) (bind₂ h) = eval₂_hom (ring_hom.comp (eval₂_hom f g) h) g :=
  sorry

theorem eval₂_hom_bind₂ {σ : Type u_1} {R : Type u_3} {S : Type u_4} {T : Type u_5}
    [comm_semiring R] [comm_semiring S] [comm_semiring T] (f : S →+* T) (g : σ → T)
    (h : R →+* mv_polynomial σ S) (φ : mv_polynomial σ R) :
    coe_fn (eval₂_hom f g) (coe_fn (bind₂ h) φ) =
        coe_fn (eval₂_hom (ring_hom.comp (eval₂_hom f g) h) g) φ :=
  ring_hom.congr_fun (eval₂_hom_comp_bind₂ f g h) φ

theorem aeval_bind₂ {σ : Type u_1} {R : Type u_3} {S : Type u_4} {T : Type u_5} [comm_semiring R]
    [comm_semiring S] [comm_semiring T] [algebra S T] (f : σ → T) (g : R →+* mv_polynomial σ S)
    (φ : mv_polynomial σ R) :
    coe_fn (aeval f) (coe_fn (bind₂ g) φ) = coe_fn (eval₂_hom (ring_hom.comp (↑(aeval f)) g) f) φ :=
  eval₂_hom_bind₂ (algebra_map S T) (fun (n : σ) => f n) g φ

theorem eval₂_hom_C_left {σ : Type u_1} {τ : Type u_2} {R : Type u_3} [comm_semiring R]
    (f : σ → mv_polynomial τ R) : eval₂_hom C f = ↑(bind₁ f) :=
  rfl

theorem bind₁_monomial {σ : Type u_1} {τ : Type u_2} {R : Type u_3} [comm_semiring R]
    (f : σ → mv_polynomial τ R) (d : σ →₀ ℕ) (r : R) :
    coe_fn (bind₁ f) (monomial d r) =
        coe_fn C r * finset.prod (finsupp.support d) fun (i : σ) => f i ^ coe_fn d i :=
  sorry

theorem bind₂_monomial {σ : Type u_1} {R : Type u_3} {S : Type u_4} [comm_semiring R]
    [comm_semiring S] (f : R →+* mv_polynomial σ S) (d : σ →₀ ℕ) (r : R) :
    coe_fn (bind₂ f) (monomial d r) = coe_fn f r * monomial d 1 :=
  sorry

@[simp] theorem bind₂_monomial_one {σ : Type u_1} {R : Type u_3} {S : Type u_4} [comm_semiring R]
    [comm_semiring S] (f : R →+* mv_polynomial σ S) (d : σ →₀ ℕ) :
    coe_fn (bind₂ f) (monomial d 1) = monomial d 1 :=
  sorry

protected instance monad {R : Type u_3} [comm_semiring R] :
    Monad fun (σ : Type u_1) => mv_polynomial σ R :=
  sorry

protected instance is_lawful_functor {R : Type u_3} [comm_semiring R] :
    is_lawful_functor fun (σ : Type u_1) => mv_polynomial σ R :=
  is_lawful_functor.mk
    (fun (α : Type u_1) (x : mv_polynomial α R) =>
      eq.mpr
        (id
          (Eq.trans
            ((fun (a a_1 : mv_polynomial α R) (e_1 : a = a_1) (ᾰ ᾰ_1 : mv_polynomial α R)
                (e_2 : ᾰ = ᾰ_1) => congr (congr_arg Eq e_1) e_2)
              (id <$> x) x (rename_id x) x x (Eq.refl x))
            (propext (eq_self_iff_true x))))
        trivial)
    fun (α β γ : Type u_1) (g : α → β) (h : β → γ) (x : mv_polynomial α R) =>
      eq.mpr
        (id
          (Eq.trans
            ((fun (a a_1 : mv_polynomial γ R) (e_1 : a = a_1) (ᾰ ᾰ_1 : mv_polynomial γ R)
                (e_2 : ᾰ = ᾰ_1) => congr (congr_arg Eq e_1) e_2)
              ((h ∘ g) <$> x) (coe_fn (rename (h ∘ g)) x) (Eq.refl (coe_fn (rename (h ∘ g)) x))
              (h <$> g <$> x) (coe_fn (rename (h ∘ g)) x) (rename_rename g h x))
            (propext (eq_self_iff_true (coe_fn (rename (h ∘ g)) x)))))
        trivial

protected instance is_lawful_monad {R : Type u_3} [comm_semiring R] :
    is_lawful_monad fun (σ : Type u_1) => mv_polynomial σ R :=
  sorry

end Mathlib