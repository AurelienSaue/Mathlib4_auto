/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.polynomial.ring_division
import Mathlib.linear_algebra.dimension
import Mathlib.algebra.polynomial.big_operators
import Mathlib.PostPort

universes u_1 l 

namespace Mathlib

/-!
# Linear recurrence

Informally, a "linear recurrence" is an assertion of the form
`∀ n : ℕ, u (n + d) = a 0 * u n + a 1 * u (n+1) + ... + a (d-1) * u (n+d-1)`,
where `u` is a sequence, `d` is the *order* of the recurrence and the `a i`
are its *coefficients*.

In this file, we define the structure `linear_recurrence` so that
`linear_recurrence.mk d a` represents the above relation, and we call
a sequence `u` which verifies it a *solution* of the linear recurrence.

We prove a few basic lemmas about this concept, such as :

* the space of solutions is a submodule of `(ℕ → α)` (i.e a vector space if `α`
  is a field)
* the function that maps a solution `u` to its first `d` terms builds a `linear_equiv`
  between the solution space and `fin d → α`, aka `α ^ d`. As a consequence, two
  solutions are equal if and only if their first `d` terms are equals.
* a geometric sequence `q ^ n` is solution iff `q` is a root of a particular polynomial,
  which we call the *characteristic polynomial* of the recurrence

Of course, although we can inductively generate solutions (cf `mk_sol`), the
interesting part would be to determinate closed-forms for the solutions.
This is currently *not implemented*, as we are waiting for definition and
properties of eigenvalues and eigenvectors.

-/

/-- A "linear recurrence relation" over a commutative semiring is given by its
  order `n` and `n` coefficients. -/
structure linear_recurrence (α : Type u_1) [comm_semiring α] 
where
  order : ℕ
  coeffs : fin order → α

protected instance linear_recurrence.inhabited (α : Type u_1) [comm_semiring α] : Inhabited (linear_recurrence α) :=
  { default := linear_recurrence.mk 0 Inhabited.default }

namespace linear_recurrence


/-- We say that a sequence `u` is solution of `linear_recurrence order coeffs` when we have
  `u (n + order) = ∑ i : fin order, coeffs i * u (n + i)` for any `n`. -/
def is_solution {α : Type u_1} [comm_semiring α] (E : linear_recurrence α) (u : ℕ → α)  :=
  ∀ (n : ℕ), u (n + order E) = finset.sum finset.univ fun (i : fin (order E)) => coeffs E i * u (n + ↑i)

/-- A solution of a `linear_recurrence` which satisfies certain initial conditions.
  We will prove this is the only such solution. -/
def mk_sol {α : Type u_1} [comm_semiring α] (E : linear_recurrence α) (init : fin (order E) → α) : ℕ → α :=
  sorry

/-- `E.mk_sol` indeed gives solutions to `E`. -/
theorem is_sol_mk_sol {α : Type u_1} [comm_semiring α] (E : linear_recurrence α) (init : fin (order E) → α) : is_solution E (mk_sol α _inst_1 E init) := sorry

/-- `E.mk_sol init`'s first `E.order` terms are `init`. -/
theorem mk_sol_eq_init {α : Type u_1} [comm_semiring α] (E : linear_recurrence α) (init : fin (order E) → α) (n : fin (order E)) : mk_sol α _inst_1 E init ↑n = init n := sorry

/-- If `u` is a solution to `E` and `init` designates its first `E.order` values,
  then `∀ n, u n = E.mk_sol init n`. -/
theorem eq_mk_of_is_sol_of_eq_init {α : Type u_1} [comm_semiring α] (E : linear_recurrence α) {u : ℕ → α} {init : fin (order E) → α} (h : is_solution E u) (heq : ∀ (n : fin (order E)), u ↑n = init n) (n : ℕ) : u n = mk_sol α _inst_1 E init n := sorry

/-- If `u` is a solution to `E` and `init` designates its first `E.order` values,
  then `u = E.mk_sol init`. This proves that `E.mk_sol init` is the only solution
  of `E` whose first `E.order` values are given by `init`. -/
theorem eq_mk_of_is_sol_of_eq_init' {α : Type u_1} [comm_semiring α] (E : linear_recurrence α) {u : ℕ → α} {init : fin (order E) → α} (h : is_solution E u) (heq : ∀ (n : fin (order E)), u ↑n = init n) : u = mk_sol α _inst_1 E init :=
  funext (eq_mk_of_is_sol_of_eq_init α _inst_1 E (fun (x : ℕ) => u x) init h heq)

/-- The space of solutions of `E`, as a `submodule` over `α` of the semimodule `ℕ → α`. -/
def sol_space {α : Type u_1} [comm_semiring α] (E : linear_recurrence α) : submodule α (ℕ → α) :=
  submodule.mk (set_of fun (u : ℕ → α) => is_solution E u) sorry sorry sorry

/-- Defining property of the solution space : `u` is a solution
  iff it belongs to the solution space. -/
theorem is_sol_iff_mem_sol_space {α : Type u_1} [comm_semiring α] (E : linear_recurrence α) (u : ℕ → α) : is_solution E u ↔ u ∈ sol_space E :=
  iff.rfl

/-- The function that maps a solution `u` of `E` to its first
  `E.order` terms as a `linear_equiv`. -/
def to_init {α : Type u_1} [comm_semiring α] (E : linear_recurrence α) : linear_equiv α (↥(sol_space E)) (fin (order E) → α) :=
  linear_equiv.mk (fun (u : ↥(sol_space E)) (x : fin (order E)) => coe u ↑x) sorry sorry
    (fun (u : fin (order E) → α) => { val := mk_sol α _inst_1 E u, property := is_sol_mk_sol α _inst_1 E u }) sorry sorry

/-- Two solutions are equal iff they are equal on `range E.order`. -/
theorem sol_eq_of_eq_init {α : Type u_1} [comm_semiring α] (E : linear_recurrence α) (u : ℕ → α) (v : ℕ → α) (hu : is_solution E u) (hv : is_solution E v) : u = v ↔ set.eq_on u v ↑(finset.range (order E)) := sorry

/-! `E.tuple_succ` maps `![s₀, s₁, ..., sₙ]` to `![s₁, ..., sₙ, ∑ (E.coeffs i) * sᵢ]`,
  where `n := E.order`. This operation is quite useful for determining closed-form
  solutions of `E`. -/

/-- `E.tuple_succ` maps `![s₀, s₁, ..., sₙ]` to `![s₁, ..., sₙ, ∑ (E.coeffs i) * sᵢ]`,
  where `n := E.order`. -/
def tuple_succ {α : Type u_1} [comm_semiring α] (E : linear_recurrence α) : linear_map α (fin (order E) → α) (fin (order E) → α) :=
  linear_map.mk
    (fun (X : fin (order E) → α) (i : fin (order E)) =>
      dite (↑i + 1 < order E) (fun (h : ↑i + 1 < order E) => X { val := ↑i + 1, property := h })
        fun (h : ¬↑i + 1 < order E) => finset.sum finset.univ fun (i : fin (order E)) => coeffs E i * X i)
    sorry sorry

/-- The dimension of `E.sol_space` is `E.order`. -/
theorem sol_space_dim {α : Type u_1} [field α] (E : linear_recurrence α) : vector_space.dim α ↥(sol_space E) = ↑(order E) :=
  dim_fin_fun (order E) ▸ linear_equiv.dim_eq (to_init α comm_ring.to_comm_semiring E)

/-- The characteristic polynomial of `E` is
`X ^ E.order - ∑ i : fin E.order, (E.coeffs i) * X ^ i`. -/
def char_poly {α : Type u_1} [comm_ring α] (E : linear_recurrence α) : polynomial α :=
  coe_fn (polynomial.monomial (order E)) 1 -
    finset.sum finset.univ fun (i : fin (order E)) => coe_fn (polynomial.monomial ↑i) (coeffs E i)

/-- The geometric sequence `q^n` is a solution of `E` iff
  `q` is a root of `E`'s characteristic polynomial. -/
theorem geom_sol_iff_root_char_poly {α : Type u_1} [comm_ring α] (E : linear_recurrence α) (q : α) : (is_solution E fun (n : ℕ) => q ^ n) ↔ polynomial.is_root (char_poly E) q := sorry

