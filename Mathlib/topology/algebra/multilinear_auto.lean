/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.algebra.module
import Mathlib.linear_algebra.multilinear
import Mathlib.PostPort

universes u v w₁ w₂ l u_1 w₃ w₁' w₄ w u_2 u_3 

namespace Mathlib

/-!
# Continuous multilinear maps

We define continuous multilinear maps as maps from `Π(i : ι), M₁ i` to `M₂` which are multilinear
and continuous, by extending the space of multilinear maps with a continuity assumption.
Here, `M₁ i` and `M₂` are modules over a ring `R`, and `ι` is an arbitrary type, and all these
spaces are also topological spaces.

## Main definitions

* `continuous_multilinear_map R M₁ M₂` is the space of continuous multilinear maps from
  `Π(i : ι), M₁ i` to `M₂`. We show that it is an `R`-module.

## Implementation notes

We mostly follow the API of multilinear maps.

## Notation

We introduce the notation `M [×n]→L[R] M'` for the space of continuous `n`-multilinear maps from
`M^n` to `M'`. This is a particular case of the general notion (where we allow varying dependent
types as the arguments of our continuous multilinear maps), but arguably the most important one,
especially when defining iterated derivatives.
-/

/-- Continuous multilinear maps over the ring `R`, from `Πi, M₁ i` to `M₂` where `M₁ i` and `M₂`
are modules over `R` with a topological structure. In applications, there will be compatibility
conditions between the algebraic and the topological structures, but this is not needed for the
definition. -/
structure continuous_multilinear_map (R : Type u) {ι : Type v} (M₁ : ι → Type w₁) (M₂ : Type w₂)
    [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂]
    [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] [(i : ι) → topological_space (M₁ i)]
    [topological_space M₂]
    extends multilinear_map R M₁ M₂ where
  cont : continuous (multilinear_map.to_fun _to_multilinear_map)

namespace continuous_multilinear_map


protected instance has_coe_to_fun {R : Type u} {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂}
    [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂]
    [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] [(i : ι) → topological_space (M₁ i)]
    [topological_space M₂] : has_coe_to_fun (continuous_multilinear_map R M₁ M₂) :=
  has_coe_to_fun.mk (fun (f : continuous_multilinear_map R M₁ M₂) => ((i : ι) → M₁ i) → M₂)
    fun (f : continuous_multilinear_map R M₁ M₂) => multilinear_map.to_fun (to_multilinear_map f)

theorem coe_continuous {R : Type u} {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [DecidableEq ι]
    [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂]
    [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] [(i : ι) → topological_space (M₁ i)]
    [topological_space M₂] (f : continuous_multilinear_map R M₁ M₂) : continuous ⇑f :=
  cont f

@[simp] theorem coe_coe {R : Type u} {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [DecidableEq ι]
    [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂]
    [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] [(i : ι) → topological_space (M₁ i)]
    [topological_space M₂] (f : continuous_multilinear_map R M₁ M₂) :
    ⇑(to_multilinear_map f) = ⇑f :=
  rfl

theorem to_multilinear_map_inj {R : Type u} {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂}
    [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂]
    [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] [(i : ι) → topological_space (M₁ i)]
    [topological_space M₂] : function.injective to_multilinear_map :=
  sorry

theorem ext {R : Type u} {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [DecidableEq ι] [semiring R]
    [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → semimodule R (M₁ i)]
    [semimodule R M₂] [(i : ι) → topological_space (M₁ i)] [topological_space M₂]
    {f : continuous_multilinear_map R M₁ M₂} {f' : continuous_multilinear_map R M₁ M₂}
    (H : ∀ (x : (i : ι) → M₁ i), coe_fn f x = coe_fn f' x) : f = f' :=
  to_multilinear_map_inj (multilinear_map.ext H)

@[simp] theorem map_add {R : Type u} {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [DecidableEq ι]
    [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂]
    [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] [(i : ι) → topological_space (M₁ i)]
    [topological_space M₂] (f : continuous_multilinear_map R M₁ M₂) (m : (i : ι) → M₁ i) (i : ι)
    (x : M₁ i) (y : M₁ i) :
    coe_fn f (function.update m i (x + y)) =
        coe_fn f (function.update m i x) + coe_fn f (function.update m i y) :=
  multilinear_map.map_add' (to_multilinear_map f) m i x y

@[simp] theorem map_smul {R : Type u} {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [DecidableEq ι]
    [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂]
    [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] [(i : ι) → topological_space (M₁ i)]
    [topological_space M₂] (f : continuous_multilinear_map R M₁ M₂) (m : (i : ι) → M₁ i) (i : ι)
    (c : R) (x : M₁ i) :
    coe_fn f (function.update m i (c • x)) = c • coe_fn f (function.update m i x) :=
  multilinear_map.map_smul' (to_multilinear_map f) m i c x

theorem map_coord_zero {R : Type u} {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [DecidableEq ι]
    [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂]
    [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] [(i : ι) → topological_space (M₁ i)]
    [topological_space M₂] (f : continuous_multilinear_map R M₁ M₂) {m : (i : ι) → M₁ i} (i : ι)
    (h : m i = 0) : coe_fn f m = 0 :=
  multilinear_map.map_coord_zero (to_multilinear_map f) i h

@[simp] theorem map_zero {R : Type u} {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [DecidableEq ι]
    [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂]
    [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] [(i : ι) → topological_space (M₁ i)]
    [topological_space M₂] (f : continuous_multilinear_map R M₁ M₂) [Nonempty ι] : coe_fn f 0 = 0 :=
  multilinear_map.map_zero (to_multilinear_map f)

protected instance has_zero {R : Type u} {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂}
    [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂]
    [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] [(i : ι) → topological_space (M₁ i)]
    [topological_space M₂] : HasZero (continuous_multilinear_map R M₁ M₂) :=
  { zero := mk (multilinear_map.mk (multilinear_map.to_fun 0) sorry sorry) sorry }

protected instance inhabited {R : Type u} {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂}
    [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂]
    [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] [(i : ι) → topological_space (M₁ i)]
    [topological_space M₂] : Inhabited (continuous_multilinear_map R M₁ M₂) :=
  { default := 0 }

@[simp] theorem zero_apply {R : Type u} {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂}
    [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂]
    [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] [(i : ι) → topological_space (M₁ i)]
    [topological_space M₂] (m : (i : ι) → M₁ i) : coe_fn 0 m = 0 :=
  rfl

protected instance has_add {R : Type u} {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂}
    [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂]
    [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] [(i : ι) → topological_space (M₁ i)]
    [topological_space M₂] [has_continuous_add M₂] : Add (continuous_multilinear_map R M₁ M₂) :=
  { add :=
      fun (f f' : continuous_multilinear_map R M₁ M₂) =>
        mk
          (multilinear_map.mk
            (multilinear_map.to_fun (to_multilinear_map f + to_multilinear_map f')) sorry sorry)
          sorry }

@[simp] theorem add_apply {R : Type u} {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂}
    [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂]
    [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] [(i : ι) → topological_space (M₁ i)]
    [topological_space M₂] (f : continuous_multilinear_map R M₁ M₂)
    (f' : continuous_multilinear_map R M₁ M₂) [has_continuous_add M₂] (m : (i : ι) → M₁ i) :
    coe_fn (f + f') m = coe_fn f m + coe_fn f' m :=
  rfl

@[simp] theorem to_multilinear_map_add {R : Type u} {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂}
    [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂]
    [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] [(i : ι) → topological_space (M₁ i)]
    [topological_space M₂] [has_continuous_add M₂] (f : continuous_multilinear_map R M₁ M₂)
    (g : continuous_multilinear_map R M₁ M₂) :
    to_multilinear_map (f + g) = to_multilinear_map f + to_multilinear_map g :=
  rfl

protected instance add_comm_monoid {R : Type u} {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂}
    [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂]
    [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] [(i : ι) → topological_space (M₁ i)]
    [topological_space M₂] [has_continuous_add M₂] :
    add_comm_monoid (continuous_multilinear_map R M₁ M₂) :=
  add_comm_monoid.mk Add.add sorry 0 sorry sorry sorry

@[simp] theorem sum_apply {R : Type u} {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂}
    [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂]
    [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] [(i : ι) → topological_space (M₁ i)]
    [topological_space M₂] [has_continuous_add M₂] {α : Type u_1}
    (f : α → continuous_multilinear_map R M₁ M₂) (m : (i : ι) → M₁ i) {s : finset α} :
    coe_fn (finset.sum s fun (a : α) => f a) m = finset.sum s fun (a : α) => coe_fn (f a) m :=
  sorry

/-- If `f` is a continuous multilinear map, then `f.to_continuous_linear_map m i` is the continuous
linear map obtained by fixing all coordinates but `i` equal to those of `m`, and varying the
`i`-th coordinate. -/
def to_continuous_linear_map {R : Type u} {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂}
    [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂]
    [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] [(i : ι) → topological_space (M₁ i)]
    [topological_space M₂] (f : continuous_multilinear_map R M₁ M₂) (m : (i : ι) → M₁ i) (i : ι) :
    continuous_linear_map R (M₁ i) M₂ :=
  continuous_linear_map.mk
    (linear_map.mk (linear_map.to_fun (multilinear_map.to_linear_map (to_multilinear_map f) m i))
      sorry sorry)

/-- The cartesian product of two continuous multilinear maps, as a continuous multilinear map. -/
def prod {R : Type u} {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} {M₃ : Type w₃} [DecidableEq ι]
    [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [add_comm_monoid M₃]
    [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] [semimodule R M₃]
    [(i : ι) → topological_space (M₁ i)] [topological_space M₂] [topological_space M₃]
    (f : continuous_multilinear_map R M₁ M₂) (g : continuous_multilinear_map R M₁ M₃) :
    continuous_multilinear_map R M₁ (M₂ × M₃) :=
  mk
    (multilinear_map.mk
      (multilinear_map.to_fun (multilinear_map.prod (to_multilinear_map f) (to_multilinear_map g)))
      sorry sorry)
    sorry

@[simp] theorem prod_apply {R : Type u} {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂}
    {M₃ : Type w₃} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)]
    [add_comm_monoid M₂] [add_comm_monoid M₃] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂]
    [semimodule R M₃] [(i : ι) → topological_space (M₁ i)] [topological_space M₂]
    [topological_space M₃] (f : continuous_multilinear_map R M₁ M₂)
    (g : continuous_multilinear_map R M₁ M₃) (m : (i : ι) → M₁ i) :
    coe_fn (prod f g) m = (coe_fn f m, coe_fn g m) :=
  rfl

/-- If `g` is continuous multilinear and `f` is a collection of continuous linear maps,
then `g (f₁ m₁, ..., fₙ mₙ)` is again a continuous multilinear map, that we call
`g.comp_continuous_linear_map f`. -/
def comp_continuous_linear_map {R : Type u} {ι : Type v} {M₁ : ι → Type w₁} {M₁' : ι → Type w₁'}
    {M₄ : Type w₄} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)]
    [(i : ι) → add_comm_monoid (M₁' i)] [add_comm_monoid M₄] [(i : ι) → semimodule R (M₁ i)]
    [(i : ι) → semimodule R (M₁' i)] [semimodule R M₄] [(i : ι) → topological_space (M₁ i)]
    [(i : ι) → topological_space (M₁' i)] [topological_space M₄]
    (g : continuous_multilinear_map R M₁' M₄)
    (f : (i : ι) → continuous_linear_map R (M₁ i) (M₁' i)) : continuous_multilinear_map R M₁ M₄ :=
  mk
    (multilinear_map.mk
      (multilinear_map.to_fun
        (multilinear_map.comp_linear_map (to_multilinear_map g)
          fun (i : ι) => continuous_linear_map.to_linear_map (f i)))
      sorry sorry)
    sorry

@[simp] theorem comp_continuous_linear_map_apply {R : Type u} {ι : Type v} {M₁ : ι → Type w₁}
    {M₁' : ι → Type w₁'} {M₄ : Type w₄} [DecidableEq ι] [semiring R]
    [(i : ι) → add_comm_monoid (M₁ i)] [(i : ι) → add_comm_monoid (M₁' i)] [add_comm_monoid M₄]
    [(i : ι) → semimodule R (M₁ i)] [(i : ι) → semimodule R (M₁' i)] [semimodule R M₄]
    [(i : ι) → topological_space (M₁ i)] [(i : ι) → topological_space (M₁' i)]
    [topological_space M₄] (g : continuous_multilinear_map R M₁' M₄)
    (f : (i : ι) → continuous_linear_map R (M₁ i) (M₁' i)) (m : (i : ι) → M₁ i) :
    coe_fn (comp_continuous_linear_map g f) m = coe_fn g fun (i : ι) => coe_fn (f i) (m i) :=
  rfl

/-- In the specific case of continuous multilinear maps on spaces indexed by `fin (n+1)`, where one
can build an element of `Π(i : fin (n+1)), M i` using `cons`, one can express directly the
additivity of a multilinear map along the first variable. -/
theorem cons_add {R : Type u} {n : ℕ} {M : fin (Nat.succ n) → Type w} {M₂ : Type w₂} [semiring R]
    [(i : fin (Nat.succ n)) → add_comm_monoid (M i)] [add_comm_monoid M₂]
    [(i : fin (Nat.succ n)) → semimodule R (M i)] [semimodule R M₂]
    [(i : fin (Nat.succ n)) → topological_space (M i)] [topological_space M₂]
    (f : continuous_multilinear_map R M M₂) (m : (i : fin n) → M (fin.succ i)) (x : M 0) (y : M 0) :
    coe_fn f (fin.cons (x + y) m) = coe_fn f (fin.cons x m) + coe_fn f (fin.cons y m) :=
  multilinear_map.cons_add (to_multilinear_map f) m x y

/-- In the specific case of continuous multilinear maps on spaces indexed by `fin (n+1)`, where one
can build an element of `Π(i : fin (n+1)), M i` using `cons`, one can express directly the
multiplicativity of a multilinear map along the first variable. -/
theorem cons_smul {R : Type u} {n : ℕ} {M : fin (Nat.succ n) → Type w} {M₂ : Type w₂} [semiring R]
    [(i : fin (Nat.succ n)) → add_comm_monoid (M i)] [add_comm_monoid M₂]
    [(i : fin (Nat.succ n)) → semimodule R (M i)] [semimodule R M₂]
    [(i : fin (Nat.succ n)) → topological_space (M i)] [topological_space M₂]
    (f : continuous_multilinear_map R M M₂) (m : (i : fin n) → M (fin.succ i)) (c : R) (x : M 0) :
    coe_fn f (fin.cons (c • x) m) = c • coe_fn f (fin.cons x m) :=
  multilinear_map.cons_smul (to_multilinear_map f) m c x

theorem map_piecewise_add {R : Type u} {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂}
    [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂]
    [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] [(i : ι) → topological_space (M₁ i)]
    [topological_space M₂] (f : continuous_multilinear_map R M₁ M₂) (m : (i : ι) → M₁ i)
    (m' : (i : ι) → M₁ i) (t : finset ι) :
    coe_fn f (finset.piecewise t (m + m') m') =
        finset.sum (finset.powerset t) fun (s : finset ι) => coe_fn f (finset.piecewise s m m') :=
  multilinear_map.map_piecewise_add (to_multilinear_map f) m m' t

/-- Additivity of a continuous multilinear map along all coordinates at the same time,
writing `f (m + m')` as the sum  of `f (s.piecewise m m')` over all sets `s`. -/
theorem map_add_univ {R : Type u} {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [DecidableEq ι]
    [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂]
    [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] [(i : ι) → topological_space (M₁ i)]
    [topological_space M₂] (f : continuous_multilinear_map R M₁ M₂) [fintype ι] (m : (i : ι) → M₁ i)
    (m' : (i : ι) → M₁ i) :
    coe_fn f (m + m') =
        finset.sum finset.univ fun (s : finset ι) => coe_fn f (finset.piecewise s m m') :=
  multilinear_map.map_add_univ (to_multilinear_map f) m m'

/-- If `f` is continuous multilinear, then `f (Σ_{j₁ ∈ A₁} g₁ j₁, ..., Σ_{jₙ ∈ Aₙ} gₙ jₙ)` is the sum
of `f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions with `r 1 ∈ A₁`, ...,
`r n ∈ Aₙ`. This follows from multilinearity by expanding successively with respect to each
coordinate. -/
theorem map_sum_finset {R : Type u} {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [DecidableEq ι]
    [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂]
    [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] [(i : ι) → topological_space (M₁ i)]
    [topological_space M₂] (f : continuous_multilinear_map R M₁ M₂) {α : ι → Type u_1} [fintype ι]
    (g : (i : ι) → α i → M₁ i) (A : (i : ι) → finset (α i)) :
    (coe_fn f fun (i : ι) => finset.sum (A i) fun (j : α i) => g i j) =
        finset.sum (fintype.pi_finset A)
          fun (r : (a : ι) → α a) => coe_fn f fun (i : ι) => g i (r i) :=
  multilinear_map.map_sum_finset (to_multilinear_map f) (fun (i : ι) (j : α i) => g i j)
    fun (i : ι) => A i

/-- If `f` is continuous multilinear, then `f (Σ_{j₁} g₁ j₁, ..., Σ_{jₙ} gₙ jₙ)` is the sum of
`f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions `r`. This follows from
multilinearity by expanding successively with respect to each coordinate. -/
theorem map_sum {R : Type u} {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [DecidableEq ι]
    [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂]
    [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] [(i : ι) → topological_space (M₁ i)]
    [topological_space M₂] (f : continuous_multilinear_map R M₁ M₂) {α : ι → Type u_1} [fintype ι]
    (g : (i : ι) → α i → M₁ i) [(i : ι) → fintype (α i)] :
    (coe_fn f fun (i : ι) => finset.sum finset.univ fun (j : α i) => g i j) =
        finset.sum finset.univ fun (r : (i : ι) → α i) => coe_fn f fun (i : ι) => g i (r i) :=
  multilinear_map.map_sum (to_multilinear_map f) fun (i : ι) (j : α i) => g i j

/-- Reinterpret an `A`-multilinear map as an `R`-multilinear map, if `A` is an algebra over `R`
and their actions on all involved semimodules agree with the action of `R` on `A`. -/
def restrict_scalars (R : Type u) {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [DecidableEq ι]
    [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂]
    [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] [(i : ι) → topological_space (M₁ i)]
    [topological_space M₂] {A : Type u_1} [semiring A] [has_scalar R A]
    [(i : ι) → semimodule A (M₁ i)] [semimodule A M₂] [∀ (i : ι), is_scalar_tower R A (M₁ i)]
    [is_scalar_tower R A M₂] (f : continuous_multilinear_map A M₁ M₂) :
    continuous_multilinear_map R M₁ M₂ :=
  mk (multilinear_map.restrict_scalars R (to_multilinear_map f)) sorry

@[simp] theorem coe_restrict_scalars (R : Type u) {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂}
    [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂]
    [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] [(i : ι) → topological_space (M₁ i)]
    [topological_space M₂] {A : Type u_1} [semiring A] [has_scalar R A]
    [(i : ι) → semimodule A (M₁ i)] [semimodule A M₂] [∀ (i : ι), is_scalar_tower R A (M₁ i)]
    [is_scalar_tower R A M₂] (f : continuous_multilinear_map A M₁ M₂) :
    ⇑(restrict_scalars R f) = ⇑f :=
  rfl

@[simp] theorem map_sub {R : Type u} {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [DecidableEq ι]
    [ring R] [(i : ι) → add_comm_group (M₁ i)] [add_comm_group M₂] [(i : ι) → semimodule R (M₁ i)]
    [semimodule R M₂] [(i : ι) → topological_space (M₁ i)] [topological_space M₂]
    (f : continuous_multilinear_map R M₁ M₂) (m : (i : ι) → M₁ i) (i : ι) (x : M₁ i) (y : M₁ i) :
    coe_fn f (function.update m i (x - y)) =
        coe_fn f (function.update m i x) - coe_fn f (function.update m i y) :=
  multilinear_map.map_sub (to_multilinear_map f) m i x y

protected instance has_neg {R : Type u} {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂}
    [DecidableEq ι] [ring R] [(i : ι) → add_comm_group (M₁ i)] [add_comm_group M₂]
    [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] [(i : ι) → topological_space (M₁ i)]
    [topological_space M₂] [topological_add_group M₂] : Neg (continuous_multilinear_map R M₁ M₂) :=
  { neg :=
      fun (f : continuous_multilinear_map R M₁ M₂) =>
        mk (multilinear_map.mk (multilinear_map.to_fun (-to_multilinear_map f)) sorry sorry) sorry }

@[simp] theorem neg_apply {R : Type u} {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂}
    [DecidableEq ι] [ring R] [(i : ι) → add_comm_group (M₁ i)] [add_comm_group M₂]
    [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] [(i : ι) → topological_space (M₁ i)]
    [topological_space M₂] (f : continuous_multilinear_map R M₁ M₂) [topological_add_group M₂]
    (m : (i : ι) → M₁ i) : coe_fn (-f) m = -coe_fn f m :=
  rfl

protected instance has_sub {R : Type u} {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂}
    [DecidableEq ι] [ring R] [(i : ι) → add_comm_group (M₁ i)] [add_comm_group M₂]
    [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] [(i : ι) → topological_space (M₁ i)]
    [topological_space M₂] [topological_add_group M₂] : Sub (continuous_multilinear_map R M₁ M₂) :=
  { sub :=
      fun (f g : continuous_multilinear_map R M₁ M₂) =>
        mk
          (multilinear_map.mk (multilinear_map.to_fun (to_multilinear_map f - to_multilinear_map g))
            sorry sorry)
          sorry }

@[simp] theorem sub_apply {R : Type u} {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂}
    [DecidableEq ι] [ring R] [(i : ι) → add_comm_group (M₁ i)] [add_comm_group M₂]
    [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] [(i : ι) → topological_space (M₁ i)]
    [topological_space M₂] (f : continuous_multilinear_map R M₁ M₂)
    (f' : continuous_multilinear_map R M₁ M₂) [topological_add_group M₂] (m : (i : ι) → M₁ i) :
    coe_fn (f - f') m = coe_fn f m - coe_fn f' m :=
  rfl

protected instance add_comm_group {R : Type u} {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂}
    [DecidableEq ι] [ring R] [(i : ι) → add_comm_group (M₁ i)] [add_comm_group M₂]
    [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] [(i : ι) → topological_space (M₁ i)]
    [topological_space M₂] [topological_add_group M₂] :
    add_comm_group (continuous_multilinear_map R M₁ M₂) :=
  add_comm_group.mk Add.add sorry 0 sorry sorry Neg.neg Sub.sub sorry sorry

theorem map_piecewise_smul {R : Type u} {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂}
    [DecidableEq ι] [comm_semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂]
    [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] [(i : ι) → topological_space (M₁ i)]
    [topological_space M₂] (f : continuous_multilinear_map R M₁ M₂) (c : ι → R) (m : (i : ι) → M₁ i)
    (s : finset ι) :
    coe_fn f (finset.piecewise s (fun (i : ι) => c i • m i) m) =
        (finset.prod s fun (i : ι) => c i) • coe_fn f m :=
  multilinear_map.map_piecewise_smul (to_multilinear_map f) (fun (i : ι) => c i)
    (fun (i : ι) => m i) s

/-- Multiplicativity of a continuous multilinear map along all coordinates at the same time,
writing `f (λ i, c i • m i)` as `(∏ i, c i) • f m`. -/
theorem map_smul_univ {R : Type u} {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [DecidableEq ι]
    [comm_semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂]
    [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] [(i : ι) → topological_space (M₁ i)]
    [topological_space M₂] (f : continuous_multilinear_map R M₁ M₂) [fintype ι] (c : ι → R)
    (m : (i : ι) → M₁ i) :
    (coe_fn f fun (i : ι) => c i • m i) =
        (finset.prod finset.univ fun (i : ι) => c i) • coe_fn f m :=
  multilinear_map.map_smul_univ (to_multilinear_map f) (fun (i : ι) => c i) fun (i : ι) => m i

protected instance has_scalar {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [DecidableEq ι]
    [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → topological_space (M₁ i)]
    [topological_space M₂] {R' : Type u_1} {A : Type u_2} [comm_semiring R'] [semiring A]
    [algebra R' A] [(i : ι) → semimodule A (M₁ i)] [semimodule R' M₂] [semimodule A M₂]
    [is_scalar_tower R' A M₂] [topological_space R'] [topological_semimodule R' M₂] :
    has_scalar R' (continuous_multilinear_map A M₁ M₂) :=
  has_scalar.mk
    fun (c : R') (f : continuous_multilinear_map A M₁ M₂) =>
      mk (multilinear_map.mk (multilinear_map.to_fun (c • to_multilinear_map f)) sorry sorry) sorry

@[simp] theorem smul_apply {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [DecidableEq ι]
    [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → topological_space (M₁ i)]
    [topological_space M₂] {R' : Type u_1} {A : Type u_2} [comm_semiring R'] [semiring A]
    [algebra R' A] [(i : ι) → semimodule A (M₁ i)] [semimodule R' M₂] [semimodule A M₂]
    [is_scalar_tower R' A M₂] [topological_space R'] [topological_semimodule R' M₂]
    (f : continuous_multilinear_map A M₁ M₂) (c : R') (m : (i : ι) → M₁ i) :
    coe_fn (c • f) m = c • coe_fn f m :=
  rfl

@[simp] theorem to_multilinear_map_smul {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂}
    [DecidableEq ι] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂]
    [(i : ι) → topological_space (M₁ i)] [topological_space M₂] {R' : Type u_1} {A : Type u_2}
    [comm_semiring R'] [semiring A] [algebra R' A] [(i : ι) → semimodule A (M₁ i)]
    [semimodule R' M₂] [semimodule A M₂] [is_scalar_tower R' A M₂] [topological_space R']
    [topological_semimodule R' M₂] (c : R') (f : continuous_multilinear_map A M₁ M₂) :
    to_multilinear_map (c • f) = c • to_multilinear_map f :=
  rfl

protected instance is_scalar_tower {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [DecidableEq ι]
    [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → topological_space (M₁ i)]
    [topological_space M₂] {R' : Type u_1} {A : Type u_2} [comm_semiring R'] [semiring A]
    [algebra R' A] [(i : ι) → semimodule A (M₁ i)] [semimodule R' M₂] [semimodule A M₂]
    [is_scalar_tower R' A M₂] [topological_space R'] [topological_semimodule R' M₂] {R'' : Type u_3}
    [comm_semiring R''] [has_scalar R' R''] [algebra R'' A] [semimodule R'' M₂]
    [is_scalar_tower R'' A M₂] [is_scalar_tower R' R'' M₂] [topological_space R'']
    [topological_semimodule R'' M₂] : is_scalar_tower R' R'' (continuous_multilinear_map A M₁ M₂) :=
  is_scalar_tower.mk
    fun (c₁ : R') (c₂ : R'') (f : continuous_multilinear_map A M₁ M₂) =>
      ext fun (x : (i : ι) → M₁ i) => smul_assoc c₁ c₂ (coe_fn (to_multilinear_map f) x)

/-- The space of continuous multilinear maps over an algebra over `R` is a module over `R`, for the
pointwise addition and scalar multiplication. -/
protected instance semimodule {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [DecidableEq ι]
    [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → topological_space (M₁ i)]
    [topological_space M₂] {R' : Type u_1} {A : Type u_2} [comm_semiring R'] [semiring A]
    [algebra R' A] [(i : ι) → semimodule A (M₁ i)] [semimodule R' M₂] [semimodule A M₂]
    [is_scalar_tower R' A M₂] [topological_space R'] [topological_semimodule R' M₂]
    [has_continuous_add M₂] : semimodule R' (continuous_multilinear_map A M₁ M₂) :=
  semimodule.mk sorry sorry

/-- Linear map version of the map `to_multilinear_map` associating to a continuous multilinear map
the corresponding multilinear map. -/
@[simp] theorem to_multilinear_map_linear_apply {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂}
    [DecidableEq ι] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂]
    [(i : ι) → topological_space (M₁ i)] [topological_space M₂] {R' : Type u_1} {A : Type u_2}
    [comm_semiring R'] [semiring A] [algebra R' A] [(i : ι) → semimodule A (M₁ i)]
    [semimodule R' M₂] [semimodule A M₂] [is_scalar_tower R' A M₂] [topological_space R']
    [topological_semimodule R' M₂] [has_continuous_add M₂]
    (f : continuous_multilinear_map A M₁ M₂) :
    coe_fn to_multilinear_map_linear f = to_multilinear_map f :=
  Eq.refl (coe_fn to_multilinear_map_linear f)

end continuous_multilinear_map


namespace continuous_linear_map


/-- Composing a continuous multilinear map with a continuous linear map gives again a
continuous multilinear map. -/
def comp_continuous_multilinear_map {R : Type u} {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂}
    {M₃ : Type w₃} [DecidableEq ι] [ring R] [(i : ι) → add_comm_group (M₁ i)] [add_comm_group M₂]
    [add_comm_group M₃] [(i : ι) → module R (M₁ i)] [module R M₂] [module R M₃]
    [(i : ι) → topological_space (M₁ i)] [topological_space M₂] [topological_space M₃]
    (g : continuous_linear_map R M₂ M₃) (f : continuous_multilinear_map R M₁ M₂) :
    continuous_multilinear_map R M₁ M₃ :=
  continuous_multilinear_map.mk
    (multilinear_map.mk
      (multilinear_map.to_fun
        (linear_map.comp_multilinear_map (to_linear_map g)
          (continuous_multilinear_map.to_multilinear_map f)))
      sorry sorry)
    sorry

@[simp] theorem comp_continuous_multilinear_map_coe {R : Type u} {ι : Type v} {M₁ : ι → Type w₁}
    {M₂ : Type w₂} {M₃ : Type w₃} [DecidableEq ι] [ring R] [(i : ι) → add_comm_group (M₁ i)]
    [add_comm_group M₂] [add_comm_group M₃] [(i : ι) → module R (M₁ i)] [module R M₂] [module R M₃]
    [(i : ι) → topological_space (M₁ i)] [topological_space M₂] [topological_space M₃]
    (g : continuous_linear_map R M₂ M₃) (f : continuous_multilinear_map R M₁ M₂) :
    ⇑(comp_continuous_multilinear_map g f) = ⇑g ∘ ⇑f :=
  funext fun (m : (i : ι) → M₁ i) => Eq.refl (coe_fn (comp_continuous_multilinear_map g f) m)

end Mathlib