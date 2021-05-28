/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.linear_algebra.basic
import Mathlib.algebra.algebra.basic
import Mathlib.tactic.omega.default
import Mathlib.data.fintype.sort
import PostPort

universes u v w u' l v₁ v₂ u_1 v₃ v' u_2 u_3 u_5 u_6 u_7 u_4 

namespace Mathlib

/-!
# Multilinear maps

We define multilinear maps as maps from `Π(i : ι), M₁ i` to `M₂` which are linear in each
coordinate. Here, `M₁ i` and `M₂` are modules over a ring `R`, and `ι` is an arbitrary type
(although some statements will require it to be a fintype). This space, denoted by
`multilinear_map R M₁ M₂`, inherits a module structure by pointwise addition and multiplication.

## Main definitions

* `multilinear_map R M₁ M₂` is the space of multilinear maps from `Π(i : ι), M₁ i` to `M₂`.
* `f.map_smul` is the multiplicativity of the multilinear map `f` along each coordinate.
* `f.map_add` is the additivity of the multilinear map `f` along each coordinate.
* `f.map_smul_univ` expresses the multiplicativity of `f` over all coordinates at the same time,
  writing `f (λi, c i • m i)` as `(∏ i, c i) • f m`.
* `f.map_add_univ` expresses the additivity of `f` over all coordinates at the same time, writing
  `f (m + m')` as the sum over all subsets `s` of `ι` of `f (s.piecewise m m')`.
* `f.map_sum` expresses `f (Σ_{j₁} g₁ j₁, ..., Σ_{jₙ} gₙ jₙ)` as the sum of
  `f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all possible functions.

We also register isomorphisms corresponding to currying or uncurrying variables, transforming a
multilinear function `f` on `n+1` variables into a linear function taking values in multilinear
functions in `n` variables, and into a multilinear function in `n` variables taking values in linear
functions. These operations are called `f.curry_left` and `f.curry_right` respectively
(with inverses `f.uncurry_left` and `f.uncurry_right`). These operations induce linear equivalences
between spaces of multilinear functions in `n+1` variables and spaces of linear functions into
multilinear functions in `n` variables (resp. multilinear functions in `n` variables taking values
in linear functions), called respectively `multilinear_curry_left_equiv` and
`multilinear_curry_right_equiv`.

## Implementation notes

Expressing that a map is linear along the `i`-th coordinate when all other coordinates are fixed
can be done in two (equivalent) different ways:
* fixing a vector `m : Π(j : ι - i), M₁ j.val`, and then choosing separately the `i`-th coordinate
* fixing a vector `m : Πj, M₁ j`, and then modifying its `i`-th coordinate
The second way is more artificial as the value of `m` at `i` is not relevant, but it has the
advantage of avoiding subtype inclusion issues. This is the definition we use, based on
`function.update` that allows to change the value of `m` at `i`.
-/

/-- Multilinear maps over the ring `R`, from `Πi, M₁ i` to `M₂` where `M₁ i` and `M₂` are modules
over `R`. -/
structure multilinear_map (R : Type u) {ι : Type u'} (M₁ : ι → Type v) (M₂ : Type w) [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] 
where
  to_fun : ((i : ι) → M₁ i) → M₂
  map_add' : ∀ (m : (i : ι) → M₁ i) (i : ι) (x y : M₁ i),
  to_fun (function.update m i (x + y)) = to_fun (function.update m i x) + to_fun (function.update m i y)
  map_smul' : ∀ (m : (i : ι) → M₁ i) (i : ι) (c : R) (x : M₁ i),
  to_fun (function.update m i (c • x)) = c • to_fun (function.update m i x)

namespace multilinear_map


protected instance has_coe_to_fun {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] : has_coe_to_fun (multilinear_map R M₁ M₂) :=
  has_coe_to_fun.mk (fun (x : multilinear_map R M₁ M₂) => ((i : ι) → M₁ i) → M₂) to_fun

@[simp] theorem to_fun_eq_coe {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] (f : multilinear_map R M₁ M₂) : to_fun f = ⇑f :=
  rfl

@[simp] theorem coe_mk {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] (f : ((i : ι) → M₁ i) → M₂) (h₁ : ∀ (m : (i : ι) → M₁ i) (i : ι) (x y : M₁ i),
  f (function.update m i (x + y)) = f (function.update m i x) + f (function.update m i y)) (h₂ : ∀ (m : (i : ι) → M₁ i) (i : ι) (c : R) (x : M₁ i), f (function.update m i (c • x)) = c • f (function.update m i x)) : ⇑(mk f h₁ h₂) = f :=
  rfl

theorem congr_fun {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] {f : multilinear_map R M₁ M₂} {g : multilinear_map R M₁ M₂} (h : f = g) (x : (i : ι) → M₁ i) : coe_fn f x = coe_fn g x :=
  congr_arg (fun (h : multilinear_map R M₁ M₂) => coe_fn h x) h

theorem congr_arg {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] (f : multilinear_map R M₁ M₂) {x : (i : ι) → M₁ i} {y : (i : ι) → M₁ i} (h : x = y) : coe_fn f x = coe_fn f y :=
  congr_arg (fun (x : (i : ι) → M₁ i) => coe_fn f x) h

theorem coe_inj {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] {f : multilinear_map R M₁ M₂} {g : multilinear_map R M₁ M₂} (h : ⇑f = ⇑g) : f = g := sorry

theorem ext {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] {f : multilinear_map R M₁ M₂} {f' : multilinear_map R M₁ M₂} (H : ∀ (x : (i : ι) → M₁ i), coe_fn f x = coe_fn f' x) : f = f' :=
  coe_inj (funext H)

theorem ext_iff {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] {f : multilinear_map R M₁ M₂} {g : multilinear_map R M₁ M₂} : f = g ↔ ∀ (x : (i : ι) → M₁ i), coe_fn f x = coe_fn g x :=
  { mp := fun (h : f = g) (x : (i : ι) → M₁ i) => h ▸ rfl,
    mpr := fun (h : ∀ (x : (i : ι) → M₁ i), coe_fn f x = coe_fn g x) => ext h }

@[simp] theorem map_add {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] (f : multilinear_map R M₁ M₂) (m : (i : ι) → M₁ i) (i : ι) (x : M₁ i) (y : M₁ i) : coe_fn f (function.update m i (x + y)) = coe_fn f (function.update m i x) + coe_fn f (function.update m i y) :=
  map_add' f m i x y

@[simp] theorem map_smul {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] (f : multilinear_map R M₁ M₂) (m : (i : ι) → M₁ i) (i : ι) (c : R) (x : M₁ i) : coe_fn f (function.update m i (c • x)) = c • coe_fn f (function.update m i x) :=
  map_smul' f m i c x

theorem map_coord_zero {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] (f : multilinear_map R M₁ M₂) {m : (i : ι) → M₁ i} (i : ι) (h : m i = 0) : coe_fn f m = 0 := sorry

@[simp] theorem map_update_zero {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] (f : multilinear_map R M₁ M₂) (m : (i : ι) → M₁ i) (i : ι) : coe_fn f (function.update m i 0) = 0 :=
  map_coord_zero f i (function.update_same i 0 m)

@[simp] theorem map_zero {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] (f : multilinear_map R M₁ M₂) [Nonempty ι] : coe_fn f 0 = 0 :=
  Exists.dcases_on (set.exists_mem_of_nonempty ι) fun (i : ι) (h : i ∈ set.univ) => map_coord_zero f i rfl

protected instance has_add {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] : Add (multilinear_map R M₁ M₂) :=
  { add := fun (f f' : multilinear_map R M₁ M₂) => mk (fun (x : (i : ι) → M₁ i) => coe_fn f x + coe_fn f' x) sorry sorry }

@[simp] theorem add_apply {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] (f : multilinear_map R M₁ M₂) (f' : multilinear_map R M₁ M₂) (m : (i : ι) → M₁ i) : coe_fn (f + f') m = coe_fn f m + coe_fn f' m :=
  rfl

protected instance has_zero {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] : HasZero (multilinear_map R M₁ M₂) :=
  { zero := mk (fun (_x : (i : ι) → M₁ i) => 0) sorry sorry }

protected instance inhabited {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] : Inhabited (multilinear_map R M₁ M₂) :=
  { default := 0 }

@[simp] theorem zero_apply {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] (m : (i : ι) → M₁ i) : coe_fn 0 m = 0 :=
  rfl

protected instance add_comm_monoid {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] : add_comm_monoid (multilinear_map R M₁ M₂) :=
  add_comm_monoid.mk Add.add sorry 0 sorry sorry sorry

@[simp] theorem sum_apply {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] {α : Type u_1} (f : α → multilinear_map R M₁ M₂) (m : (i : ι) → M₁ i) {s : finset α} : coe_fn (finset.sum s fun (a : α) => f a) m = finset.sum s fun (a : α) => coe_fn (f a) m := sorry

/-- If `f` is a multilinear map, then `f.to_linear_map m i` is the linear map obtained by fixing all
coordinates but `i` equal to those of `m`, and varying the `i`-th coordinate. -/
def to_linear_map {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] (f : multilinear_map R M₁ M₂) (m : (i : ι) → M₁ i) (i : ι) : linear_map R (M₁ i) M₂ :=
  linear_map.mk (fun (x : M₁ i) => coe_fn f (function.update m i x)) sorry sorry

/-- The cartesian product of two multilinear maps, as a multilinear map. -/
def prod {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} {M₃ : Type v₃} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [add_comm_monoid M₃] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] [semimodule R M₃] (f : multilinear_map R M₁ M₂) (g : multilinear_map R M₁ M₃) : multilinear_map R M₁ (M₂ × M₃) :=
  mk (fun (m : (i : ι) → M₁ i) => (coe_fn f m, coe_fn g m)) sorry sorry

/-- Given a multilinear map `f` on `n` variables (parameterized by `fin n`) and a subset `s` of `k`
of these variables, one gets a new multilinear map on `fin k` by varying these variables, and fixing
the other ones equal to a given value `z`. It is denoted by `f.restr s hk z`, where `hk` is a
proof that the cardinality of `s` is `k`. The implicit identification between `fin k` and `s` that
we use is the canonical (increasing) bijection. -/
def restr {R : Type u} {M₂ : Type v₂} {M' : Type v'} [semiring R] [add_comm_monoid M₂] [add_comm_monoid M'] [semimodule R M₂] [semimodule R M'] {k : ℕ} {n : ℕ} (f : multilinear_map R (fun (i : fin n) => M') M₂) (s : finset (fin n)) (hk : finset.card s = k) (z : M') : multilinear_map R (fun (i : fin k) => M') M₂ :=
  mk
    (fun (v : fin k → M') =>
      coe_fn f
        fun (j : fin n) =>
          dite (j ∈ s)
            (fun (h : j ∈ s) => v (coe_fn (order_iso.symm (finset.order_iso_of_fin s hk)) { val := j, property := h }))
            fun (h : ¬j ∈ s) => z)
    sorry sorry

/-- In the specific case of multilinear maps on spaces indexed by `fin (n+1)`, where one can build
an element of `Π(i : fin (n+1)), M i` using `cons`, one can express directly the additivity of a
multilinear map along the first variable. -/
theorem cons_add {R : Type u} {n : ℕ} {M : fin (Nat.succ n) → Type v} {M₂ : Type v₂} [semiring R] [(i : fin (Nat.succ n)) → add_comm_monoid (M i)] [add_comm_monoid M₂] [(i : fin (Nat.succ n)) → semimodule R (M i)] [semimodule R M₂] (f : multilinear_map R M M₂) (m : (i : fin n) → M (fin.succ i)) (x : M 0) (y : M 0) : coe_fn f (fin.cons (x + y) m) = coe_fn f (fin.cons x m) + coe_fn f (fin.cons y m) := sorry

/-- In the specific case of multilinear maps on spaces indexed by `fin (n+1)`, where one can build
an element of `Π(i : fin (n+1)), M i` using `cons`, one can express directly the multiplicativity
of a multilinear map along the first variable. -/
theorem cons_smul {R : Type u} {n : ℕ} {M : fin (Nat.succ n) → Type v} {M₂ : Type v₂} [semiring R] [(i : fin (Nat.succ n)) → add_comm_monoid (M i)] [add_comm_monoid M₂] [(i : fin (Nat.succ n)) → semimodule R (M i)] [semimodule R M₂] (f : multilinear_map R M M₂) (m : (i : fin n) → M (fin.succ i)) (c : R) (x : M 0) : coe_fn f (fin.cons (c • x) m) = c • coe_fn f (fin.cons x m) := sorry

/-- In the specific case of multilinear maps on spaces indexed by `fin (n+1)`, where one can build
an element of `Π(i : fin (n+1)), M i` using `snoc`, one can express directly the additivity of a
multilinear map along the first variable. -/
theorem snoc_add {R : Type u} {n : ℕ} {M : fin (Nat.succ n) → Type v} {M₂ : Type v₂} [semiring R] [(i : fin (Nat.succ n)) → add_comm_monoid (M i)] [add_comm_monoid M₂] [(i : fin (Nat.succ n)) → semimodule R (M i)] [semimodule R M₂] (f : multilinear_map R M M₂) (m : (i : fin n) → M (coe_fn fin.cast_succ i)) (x : M (fin.last n)) (y : M (fin.last n)) : coe_fn f (fin.snoc m (x + y)) = coe_fn f (fin.snoc m x) + coe_fn f (fin.snoc m y) := sorry

/-- In the specific case of multilinear maps on spaces indexed by `fin (n+1)`, where one can build
an element of `Π(i : fin (n+1)), M i` using `cons`, one can express directly the multiplicativity
of a multilinear map along the first variable. -/
theorem snoc_smul {R : Type u} {n : ℕ} {M : fin (Nat.succ n) → Type v} {M₂ : Type v₂} [semiring R] [(i : fin (Nat.succ n)) → add_comm_monoid (M i)] [add_comm_monoid M₂] [(i : fin (Nat.succ n)) → semimodule R (M i)] [semimodule R M₂] (f : multilinear_map R M M₂) (m : (i : fin n) → M (coe_fn fin.cast_succ i)) (c : R) (x : M (fin.last n)) : coe_fn f (fin.snoc m (c • x)) = c • coe_fn f (fin.snoc m x) := sorry

/-- If `g` is a multilinear map and `f` is a collection of linear maps,
then `g (f₁ m₁, ..., fₙ mₙ)` is again a multilinear map, that we call
`g.comp_linear_map f`. -/
def comp_linear_map {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] {M₁' : ι → Type u_1} [(i : ι) → add_comm_monoid (M₁' i)] [(i : ι) → semimodule R (M₁' i)] (g : multilinear_map R M₁' M₂) (f : (i : ι) → linear_map R (M₁ i) (M₁' i)) : multilinear_map R M₁ M₂ :=
  mk (fun (m : (i : ι) → M₁ i) => coe_fn g fun (i : ι) => coe_fn (f i) (m i)) sorry sorry

@[simp] theorem comp_linear_map_apply {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] {M₁' : ι → Type u_1} [(i : ι) → add_comm_monoid (M₁' i)] [(i : ι) → semimodule R (M₁' i)] (g : multilinear_map R M₁' M₂) (f : (i : ι) → linear_map R (M₁ i) (M₁' i)) (m : (i : ι) → M₁ i) : coe_fn (comp_linear_map g f) m = coe_fn g fun (i : ι) => coe_fn (f i) (m i) :=
  rfl

/-- If one adds to a vector `m'` another vector `m`, but only for coordinates in a finset `t`, then
the image under a multilinear map `f` is the sum of `f (s.piecewise m m')` along all subsets `s` of
`t`. This is mainly an auxiliary statement to prove the result when `t = univ`, given in
`map_add_univ`, although it can be useful in its own right as it does not require the index set `ι`
to be finite.-/
theorem map_piecewise_add {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] (f : multilinear_map R M₁ M₂) (m : (i : ι) → M₁ i) (m' : (i : ι) → M₁ i) (t : finset ι) : coe_fn f (finset.piecewise t (m + m') m') =
  finset.sum (finset.powerset t) fun (s : finset ι) => coe_fn f (finset.piecewise s m m') := sorry

/-- Additivity of a multilinear map along all coordinates at the same time,
writing `f (m + m')` as the sum  of `f (s.piecewise m m')` over all sets `s`. -/
theorem map_add_univ {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] (f : multilinear_map R M₁ M₂) [fintype ι] (m : (i : ι) → M₁ i) (m' : (i : ι) → M₁ i) : coe_fn f (m + m') = finset.sum finset.univ fun (s : finset ι) => coe_fn f (finset.piecewise s m m') := sorry

/-- If `f` is multilinear, then `f (Σ_{j₁ ∈ A₁} g₁ j₁, ..., Σ_{jₙ ∈ Aₙ} gₙ jₙ)` is the sum of
`f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions with `r 1 ∈ A₁`, ...,
`r n ∈ Aₙ`. This follows from multilinearity by expanding successively with respect to each
coordinate. Here, we give an auxiliary statement tailored for an inductive proof. Use instead
`map_sum_finset`. -/
theorem map_sum_finset_aux {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] (f : multilinear_map R M₁ M₂) {α : ι → Type u_1} (g : (i : ι) → α i → M₁ i) (A : (i : ι) → finset (α i)) [fintype ι] {n : ℕ} (h : (finset.sum finset.univ fun (i : ι) => finset.card (A i)) = n) : (coe_fn f fun (i : ι) => finset.sum (A i) fun (j : α i) => g i j) =
  finset.sum (fintype.pi_finset A) fun (r : (a : ι) → α a) => coe_fn f fun (i : ι) => g i (r i) := sorry

/-- If `f` is multilinear, then `f (Σ_{j₁ ∈ A₁} g₁ j₁, ..., Σ_{jₙ ∈ Aₙ} gₙ jₙ)` is the sum of
`f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions with `r 1 ∈ A₁`, ...,
`r n ∈ Aₙ`. This follows from multilinearity by expanding successively with respect to each
coordinate. -/
theorem map_sum_finset {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] (f : multilinear_map R M₁ M₂) {α : ι → Type u_1} (g : (i : ι) → α i → M₁ i) (A : (i : ι) → finset (α i)) [fintype ι] : (coe_fn f fun (i : ι) => finset.sum (A i) fun (j : α i) => g i j) =
  finset.sum (fintype.pi_finset A) fun (r : (a : ι) → α a) => coe_fn f fun (i : ι) => g i (r i) :=
  map_sum_finset_aux f (fun (i : ι) (j : α i) => g i j) (fun (i : ι) => A i) rfl

/-- If `f` is multilinear, then `f (Σ_{j₁} g₁ j₁, ..., Σ_{jₙ} gₙ jₙ)` is the sum of
`f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions `r`. This follows from
multilinearity by expanding successively with respect to each coordinate. -/
theorem map_sum {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] (f : multilinear_map R M₁ M₂) {α : ι → Type u_1} (g : (i : ι) → α i → M₁ i) [fintype ι] [(i : ι) → fintype (α i)] : (coe_fn f fun (i : ι) => finset.sum finset.univ fun (j : α i) => g i j) =
  finset.sum finset.univ fun (r : (i : ι) → α i) => coe_fn f fun (i : ι) => g i (r i) :=
  map_sum_finset f g fun (i : ι) => finset.univ

theorem map_update_sum {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] (f : multilinear_map R M₁ M₂) {α : Type u_1} (t : finset α) (i : ι) (g : α → M₁ i) (m : (i : ι) → M₁ i) : coe_fn f (function.update m i (finset.sum t fun (a : α) => g a)) =
  finset.sum t fun (a : α) => coe_fn f (function.update m i (g a)) := sorry

/-- Reinterpret an `A`-multilinear map as an `R`-multilinear map, if `A` is an algebra over `R`
and their actions on all involved semimodules agree with the action of `R` on `A`. -/
def restrict_scalars (R : Type u) {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] {A : Type u_1} [semiring A] [has_scalar R A] [(i : ι) → semimodule A (M₁ i)] [semimodule A M₂] [∀ (i : ι), is_scalar_tower R A (M₁ i)] [is_scalar_tower R A M₂] (f : multilinear_map A M₁ M₂) : multilinear_map R M₁ M₂ :=
  mk ⇑f sorry sorry

@[simp] theorem coe_restrict_scalars (R : Type u) {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] {A : Type u_1} [semiring A] [has_scalar R A] [(i : ι) → semimodule A (M₁ i)] [semimodule A M₂] [∀ (i : ι), is_scalar_tower R A (M₁ i)] [is_scalar_tower R A M₂] (f : multilinear_map A M₁ M₂) : ⇑(restrict_scalars R f) = ⇑f :=
  rfl

/-- Transfer the arguments to a map along an equivalence between argument indices.

The naming is derived from `finsupp.dom_congr`, noting that here the permutation applies to the
domain of the domain. -/
@[simp] theorem dom_dom_congr_apply {R : Type u} {M₂ : Type v₂} {M₃ : Type v₃} [semiring R] [add_comm_monoid M₂] [add_comm_monoid M₃] [semimodule R M₂] [semimodule R M₃] {ι₁ : Type u_1} {ι₂ : Type u_2} [DecidableEq ι₁] [DecidableEq ι₂] (σ : ι₁ ≃ ι₂) (m : multilinear_map R (fun (i : ι₁) => M₂) M₃) (v : ι₂ → M₂) : coe_fn (dom_dom_congr σ m) v = coe_fn m fun (i : ι₁) => v (coe_fn σ i) :=
  Eq.refl (coe_fn (dom_dom_congr σ m) v)

theorem dom_dom_congr_trans {R : Type u} {M₂ : Type v₂} {M₃ : Type v₃} [semiring R] [add_comm_monoid M₂] [add_comm_monoid M₃] [semimodule R M₂] [semimodule R M₃] {ι₁ : Type u_1} {ι₂ : Type u_2} {ι₃ : Type u_3} [DecidableEq ι₁] [DecidableEq ι₂] [DecidableEq ι₃] (σ₁ : ι₁ ≃ ι₂) (σ₂ : ι₂ ≃ ι₃) (m : multilinear_map R (fun (i : ι₁) => M₂) M₃) : dom_dom_congr (equiv.trans σ₁ σ₂) m = dom_dom_congr σ₂ (dom_dom_congr σ₁ m) :=
  rfl

theorem dom_dom_congr_mul {R : Type u} {M₂ : Type v₂} {M₃ : Type v₃} [semiring R] [add_comm_monoid M₂] [add_comm_monoid M₃] [semimodule R M₂] [semimodule R M₃] {ι₁ : Type u_1} [DecidableEq ι₁] (σ₁ : equiv.perm ι₁) (σ₂ : equiv.perm ι₁) (m : multilinear_map R (fun (i : ι₁) => M₂) M₃) : dom_dom_congr (σ₂ * σ₁) m = dom_dom_congr σ₂ (dom_dom_congr σ₁ m) :=
  rfl

/-- `multilinear_map.dom_dom_congr` as an equivalence.

This is declared separately because it does not work with dot notation. -/
def dom_dom_congr_equiv {R : Type u} {M₂ : Type v₂} {M₃ : Type v₃} [semiring R] [add_comm_monoid M₂] [add_comm_monoid M₃] [semimodule R M₂] [semimodule R M₃] {ι₁ : Type u_1} {ι₂ : Type u_2} [DecidableEq ι₁] [DecidableEq ι₂] (σ : ι₁ ≃ ι₂) : multilinear_map R (fun (i : ι₁) => M₂) M₃ ≃+ multilinear_map R (fun (i : ι₂) => M₂) M₃ :=
  add_equiv.mk (dom_dom_congr σ) (dom_dom_congr (equiv.symm σ)) sorry sorry sorry

end multilinear_map


namespace linear_map


/-- Composing a multilinear map with a linear map gives again a multilinear map. -/
def comp_multilinear_map {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} {M₃ : Type v₃} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [add_comm_monoid M₃] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] [semimodule R M₃] (g : linear_map R M₂ M₃) (f : multilinear_map R M₁ M₂) : multilinear_map R M₁ M₃ :=
  multilinear_map.mk (⇑g ∘ ⇑f) sorry sorry

@[simp] theorem coe_comp_multilinear_map {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} {M₃ : Type v₃} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [add_comm_monoid M₃] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] [semimodule R M₃] (g : linear_map R M₂ M₃) (f : multilinear_map R M₁ M₂) : ⇑(comp_multilinear_map g f) = ⇑g ∘ ⇑f :=
  rfl

theorem comp_multilinear_map_apply {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} {M₃ : Type v₃} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [add_comm_monoid M₃] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] [semimodule R M₃] (g : linear_map R M₂ M₃) (f : multilinear_map R M₁ M₂) (m : (i : ι) → M₁ i) : coe_fn (comp_multilinear_map g f) m = coe_fn g (coe_fn f m) :=
  rfl

@[simp] theorem comp_multilinear_map_dom_dom_congr {R : Type u} {M₂ : Type v₂} {M₃ : Type v₃} {M' : Type v'} [semiring R] [add_comm_monoid M₂] [add_comm_monoid M₃] [add_comm_monoid M'] [semimodule R M₂] [semimodule R M₃] [semimodule R M'] {ι₁ : Type u_1} {ι₂ : Type u_2} [DecidableEq ι₁] [DecidableEq ι₂] (σ : ι₁ ≃ ι₂) (g : linear_map R M₂ M₃) (f : multilinear_map R (fun (i : ι₁) => M') M₂) : multilinear_map.dom_dom_congr σ (comp_multilinear_map g f) = comp_multilinear_map g (multilinear_map.dom_dom_congr σ f) := sorry

end linear_map


namespace multilinear_map


/-- If one multiplies by `c i` the coordinates in a finset `s`, then the image under a multilinear
map is multiplied by `∏ i in s, c i`. This is mainly an auxiliary statement to prove the result when
`s = univ`, given in `map_smul_univ`, although it can be useful in its own right as it does not
require the index set `ι` to be finite. -/
theorem map_piecewise_smul {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [comm_semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] (f : multilinear_map R M₁ M₂) (c : ι → R) (m : (i : ι) → M₁ i) (s : finset ι) : coe_fn f (finset.piecewise s (fun (i : ι) => c i • m i) m) = (finset.prod s fun (i : ι) => c i) • coe_fn f m := sorry

/-- Multiplicativity of a multilinear map along all coordinates at the same time,
writing `f (λi, c i • m i)` as `(∏ i, c i) • f m`. -/
theorem map_smul_univ {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [comm_semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] (f : multilinear_map R M₁ M₂) [fintype ι] (c : ι → R) (m : (i : ι) → M₁ i) : (coe_fn f fun (i : ι) => c i • m i) = (finset.prod finset.univ fun (i : ι) => c i) • coe_fn f m := sorry

protected instance has_scalar {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] {R' : Type u_1} {A : Type u_2} [monoid R'] [semiring A] [(i : ι) → semimodule A (M₁ i)] [distrib_mul_action R' M₂] [semimodule A M₂] [smul_comm_class A R' M₂] : has_scalar R' (multilinear_map A M₁ M₂) :=
  has_scalar.mk fun (c : R') (f : multilinear_map A M₁ M₂) => mk (fun (m : (i : ι) → M₁ i) => c • coe_fn f m) sorry sorry

@[simp] theorem smul_apply {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] {R' : Type u_1} {A : Type u_2} [monoid R'] [semiring A] [(i : ι) → semimodule A (M₁ i)] [distrib_mul_action R' M₂] [semimodule A M₂] [smul_comm_class A R' M₂] (f : multilinear_map A M₁ M₂) (c : R') (m : (i : ι) → M₁ i) : coe_fn (c • f) m = c • coe_fn f m :=
  rfl

protected instance distrib_mul_action {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] {R' : Type u_1} {A : Type u_2} [monoid R'] [semiring A] [(i : ι) → semimodule A (M₁ i)] [distrib_mul_action R' M₂] [semimodule A M₂] [smul_comm_class A R' M₂] : distrib_mul_action R' (multilinear_map A M₁ M₂) :=
  distrib_mul_action.mk sorry sorry

/-- The space of multilinear maps over an algebra over `R` is a module over `R`, for the pointwise
addition and scalar multiplication. -/
protected instance semimodule {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] {R' : Type u_1} {A : Type u_2} [semiring R'] [semiring A] [(i : ι) → semimodule A (M₁ i)] [semimodule R' M₂] [semimodule A M₂] [smul_comm_class A R' M₂] : semimodule R' (multilinear_map A M₁ M₂) :=
  semimodule.mk sorry sorry

/-- Given two multilinear maps `(ι₁ → N) → N₁` and `(ι₂ → N) → N₂`, this produces the map
`(ι₁ ⊕ ι₂ → N) → N₁ ⊗ N₂` by taking the coproduct of the domain and the tensor product
of the codomain.

This can be thought of as combining `equiv.sum_arrow_equiv_prod_arrow.symm` with
`tensor_product.map`, noting that the two operations can't be separated as the intermediate result
is not a `multilinear_map`.

While this can be generalized to work for dependent `Π i : ι₁, N'₁ i` instead of `ι₁ → N`, doing so
introduces `sum.elim N'₁ N'₂` types in the result which are difficult to work with and not defeq
to the simple case defined here. See [this zulip thread](
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Instances.20on.20.60sum.2Eelim.20A.20B.20i.60/near/218484619).
-/
def dom_coprod {R : Type u} [comm_semiring R] {ι₁ : Type u_1} {ι₂ : Type u_2} [DecidableEq ι₁] [DecidableEq ι₂] {N₁ : Type u_5} [add_comm_monoid N₁] [semimodule R N₁] {N₂ : Type u_6} [add_comm_monoid N₂] [semimodule R N₂] {N : Type u_7} [add_comm_monoid N] [semimodule R N] (a : multilinear_map R (fun (_x : ι₁) => N) N₁) (b : multilinear_map R (fun (_x : ι₂) => N) N₂) : multilinear_map R (fun (_x : ι₁ ⊕ ι₂) => N) (tensor_product R N₁ N₂) :=
  mk
    (fun (v : ι₁ ⊕ ι₂ → N) =>
      tensor_product.tmul R (coe_fn a fun (i : ι₁) => v (sum.inl i)) (coe_fn b fun (i : ι₂) => v (sum.inr i)))
    sorry sorry

/-- A more bundled version of `multilinear_map.dom_coprod` that maps
`((ι₁ → N) → N₁) ⊗ ((ι₂ → N) → N₂)` to `(ι₁ ⊕ ι₂ → N) → N₁ ⊗ N₂`. -/
def dom_coprod' {R : Type u} [comm_semiring R] {ι₁ : Type u_1} {ι₂ : Type u_2} [DecidableEq ι₁] [DecidableEq ι₂] {N₁ : Type u_5} [add_comm_monoid N₁] [semimodule R N₁] {N₂ : Type u_6} [add_comm_monoid N₂] [semimodule R N₂] {N : Type u_7} [add_comm_monoid N] [semimodule R N] : linear_map R (tensor_product R (multilinear_map R (fun (_x : ι₁) => N) N₁) (multilinear_map R (fun (_x : ι₂) => N) N₂))
  (multilinear_map R (fun (_x : ι₁ ⊕ ι₂) => N) (tensor_product R N₁ N₂)) :=
  tensor_product.lift (linear_map.mk₂ R dom_coprod sorry sorry sorry sorry)

@[simp] theorem dom_coprod'_apply {R : Type u} [comm_semiring R] {ι₁ : Type u_1} {ι₂ : Type u_2} [DecidableEq ι₁] [DecidableEq ι₂] {N₁ : Type u_5} [add_comm_monoid N₁] [semimodule R N₁] {N₂ : Type u_6} [add_comm_monoid N₂] [semimodule R N₂] {N : Type u_7} [add_comm_monoid N] [semimodule R N] (a : multilinear_map R (fun (_x : ι₁) => N) N₁) (b : multilinear_map R (fun (_x : ι₂) => N) N₂) : coe_fn dom_coprod' (tensor_product.tmul R a b) = dom_coprod a b :=
  rfl

/-- When passed an `equiv.sum_congr`, `multilinear_map.dom_dom_congr` distributes over
`multilinear_map.dom_coprod`. -/
theorem dom_coprod_dom_dom_congr_sum_congr {R : Type u} [comm_semiring R] {ι₁ : Type u_1} {ι₂ : Type u_2} {ι₃ : Type u_3} {ι₄ : Type u_4} [DecidableEq ι₁] [DecidableEq ι₂] [DecidableEq ι₃] [DecidableEq ι₄] {N₁ : Type u_5} [add_comm_monoid N₁] [semimodule R N₁] {N₂ : Type u_6} [add_comm_monoid N₂] [semimodule R N₂] {N : Type u_7} [add_comm_monoid N] [semimodule R N] (a : multilinear_map R (fun (_x : ι₁) => N) N₁) (b : multilinear_map R (fun (_x : ι₂) => N) N₂) (σa : ι₁ ≃ ι₃) (σb : ι₂ ≃ ι₄) : dom_dom_congr (equiv.sum_congr σa σb) (dom_coprod a b) = dom_coprod (dom_dom_congr σa a) (dom_dom_congr σb b) :=
  rfl

/-- Given an `R`-algebra `A`, `mk_pi_algebra` is the multilinear map on `A^ι` associating
to `m` the product of all the `m i`.

See also `multilinear_map.mk_pi_algebra_fin` for a version that works with a non-commutative
algebra `A` but requires `ι = fin n`. -/
protected def mk_pi_algebra (R : Type u) (ι : Type u') [DecidableEq ι] [comm_semiring R] (A : Type u_1) [comm_semiring A] [algebra R A] [fintype ι] : multilinear_map R (fun (i : ι) => A) A :=
  mk (fun (m : ι → A) => finset.prod finset.univ fun (i : ι) => m i) sorry sorry

@[simp] theorem mk_pi_algebra_apply {R : Type u} {ι : Type u'} [DecidableEq ι] [comm_semiring R] {A : Type u_1} [comm_semiring A] [algebra R A] [fintype ι] (m : ι → A) : coe_fn (multilinear_map.mk_pi_algebra R ι A) m = finset.prod finset.univ fun (i : ι) => m i :=
  rfl

/-- Given an `R`-algebra `A`, `mk_pi_algebra_fin` is the multilinear map on `A^n` associating
to `m` the product of all the `m i`.

See also `multilinear_map.mk_pi_algebra` for a version that assumes `[comm_semiring A]` but works
for `A^ι` with any finite type `ι`. -/
protected def mk_pi_algebra_fin (R : Type u) (n : ℕ) [comm_semiring R] (A : Type u_1) [semiring A] [algebra R A] : multilinear_map R (fun (i : fin n) => A) A :=
  mk (fun (m : fin n → A) => list.prod (list.of_fn m)) sorry sorry

@[simp] theorem mk_pi_algebra_fin_apply {R : Type u} {n : ℕ} [comm_semiring R] {A : Type u_1} [semiring A] [algebra R A] (m : fin n → A) : coe_fn (multilinear_map.mk_pi_algebra_fin R n A) m = list.prod (list.of_fn m) :=
  rfl

theorem mk_pi_algebra_fin_apply_const {R : Type u} {n : ℕ} [comm_semiring R] {A : Type u_1} [semiring A] [algebra R A] (a : A) : (coe_fn (multilinear_map.mk_pi_algebra_fin R n A) fun (_x : fin n) => a) = a ^ n := sorry

/-- Given an `R`-multilinear map `f` taking values in `R`, `f.smul_right z` is the map
sending `m` to `f m • z`. -/
def smul_right {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [comm_semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] (f : multilinear_map R M₁ R) (z : M₂) : multilinear_map R M₁ M₂ :=
  linear_map.comp_multilinear_map (linear_map.smul_right linear_map.id z) f

@[simp] theorem smul_right_apply {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [comm_semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] (f : multilinear_map R M₁ R) (z : M₂) (m : (i : ι) → M₁ i) : coe_fn (smul_right f z) m = coe_fn f m • z :=
  rfl

/-- The canonical multilinear map on `R^ι` when `ι` is finite, associating to `m` the product of
all the `m i` (multiplied by a fixed reference element `z` in the target module). See also
`mk_pi_algebra` for a more general version. -/
protected def mk_pi_ring (R : Type u) (ι : Type u') {M₂ : Type v₂} [DecidableEq ι] [comm_semiring R] [add_comm_monoid M₂] [semimodule R M₂] [fintype ι] (z : M₂) : multilinear_map R (fun (i : ι) => R) M₂ :=
  smul_right (multilinear_map.mk_pi_algebra R ι R) z

@[simp] theorem mk_pi_ring_apply {R : Type u} {ι : Type u'} {M₂ : Type v₂} [DecidableEq ι] [comm_semiring R] [add_comm_monoid M₂] [semimodule R M₂] [fintype ι] (z : M₂) (m : ι → R) : coe_fn (multilinear_map.mk_pi_ring R ι z) m = (finset.prod finset.univ fun (i : ι) => m i) • z :=
  rfl

theorem mk_pi_ring_apply_one_eq_self {R : Type u} {ι : Type u'} {M₂ : Type v₂} [DecidableEq ι] [comm_semiring R] [add_comm_monoid M₂] [semimodule R M₂] [fintype ι] (f : multilinear_map R (fun (i : ι) => R) M₂) : multilinear_map.mk_pi_ring R ι (coe_fn f fun (i : ι) => 1) = f := sorry

protected instance has_neg {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_group M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] : Neg (multilinear_map R M₁ M₂) :=
  { neg := fun (f : multilinear_map R M₁ M₂) => mk (fun (m : (i : ι) → M₁ i) => -coe_fn f m) sorry sorry }

@[simp] theorem neg_apply {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_group M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] (f : multilinear_map R M₁ M₂) (m : (i : ι) → M₁ i) : coe_fn (-f) m = -coe_fn f m :=
  rfl

protected instance has_sub {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_group M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] : Sub (multilinear_map R M₁ M₂) :=
  { sub := fun (f g : multilinear_map R M₁ M₂) => mk (fun (m : (i : ι) → M₁ i) => coe_fn f m - coe_fn g m) sorry sorry }

@[simp] theorem sub_apply {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_group M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] (f : multilinear_map R M₁ M₂) (g : multilinear_map R M₁ M₂) (m : (i : ι) → M₁ i) : coe_fn (f - g) m = coe_fn f m - coe_fn g m :=
  rfl

protected instance add_comm_group {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_group M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] : add_comm_group (multilinear_map R M₁ M₂) :=
  add_comm_group.mk Add.add sorry 0 sorry sorry Neg.neg Sub.sub sorry sorry

@[simp] theorem map_neg {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_group (M₁ i)] [add_comm_group M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] (f : multilinear_map R M₁ M₂) (m : (i : ι) → M₁ i) (i : ι) (x : M₁ i) : coe_fn f (function.update m i (-x)) = -coe_fn f (function.update m i x) := sorry

@[simp] theorem map_sub {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [semiring R] [(i : ι) → add_comm_group (M₁ i)] [add_comm_group M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] (f : multilinear_map R M₁ M₂) (m : (i : ι) → M₁ i) (i : ι) (x : M₁ i) (y : M₁ i) : coe_fn f (function.update m i (x - y)) = coe_fn f (function.update m i x) - coe_fn f (function.update m i y) := sorry

/-- When `ι` is finite, multilinear maps on `R^ι` with values in `M₂` are in bijection with `M₂`,
as such a multilinear map is completely determined by its value on the constant vector made of ones.
We register this bijection as a linear equivalence in `multilinear_map.pi_ring_equiv`. -/
protected def pi_ring_equiv {R : Type u} {ι : Type u'} {M₂ : Type v₂} [DecidableEq ι] [comm_semiring R] [add_comm_group M₂] [semimodule R M₂] [fintype ι] : linear_equiv R M₂ (multilinear_map R (fun (i : ι) => R) M₂) :=
  linear_equiv.mk (fun (z : M₂) => multilinear_map.mk_pi_ring R ι z) sorry sorry
    (fun (f : multilinear_map R (fun (i : ι) => R) M₂) => coe_fn f fun (i : ι) => 1) sorry sorry

end multilinear_map


/-!
### Currying

We associate to a multilinear map in `n+1` variables (i.e., based on `fin n.succ`) two
curried functions, named `f.curry_left` (which is a linear map on `E 0` taking values
in multilinear maps in `n` variables) and `f.curry_right` (wich is a multilinear map in `n`
variables taking values in linear maps on `E 0`). In both constructions, the variable that is
singled out is `0`, to take advantage of the operations `cons` and `tail` on `fin n`.
The inverse operations are called `uncurry_left` and `uncurry_right`.

We also register linear equiv versions of these correspondences, in
`multilinear_curry_left_equiv` and `multilinear_curry_right_equiv`.
-/

/-! #### Left currying -/

/-- Given a linear map `f` from `M 0` to multilinear maps on `n` variables,
construct the corresponding multilinear map on `n+1` variables obtained by concatenating
the variables, given by `m ↦ f (m 0) (tail m)`-/
def linear_map.uncurry_left {R : Type u} {n : ℕ} {M : fin (Nat.succ n) → Type v} {M₂ : Type v₂} [comm_semiring R] [(i : fin (Nat.succ n)) → add_comm_monoid (M i)] [add_comm_monoid M₂] [(i : fin (Nat.succ n)) → semimodule R (M i)] [semimodule R M₂] (f : linear_map R (M 0) (multilinear_map R (fun (i : fin n) => M (fin.succ i)) M₂)) : multilinear_map R M M₂ :=
  multilinear_map.mk (fun (m : (i : fin (Nat.succ n)) → M i) => coe_fn (coe_fn f (m 0)) (fin.tail m)) sorry sorry

@[simp] theorem linear_map.uncurry_left_apply {R : Type u} {n : ℕ} {M : fin (Nat.succ n) → Type v} {M₂ : Type v₂} [comm_semiring R] [(i : fin (Nat.succ n)) → add_comm_monoid (M i)] [add_comm_monoid M₂] [(i : fin (Nat.succ n)) → semimodule R (M i)] [semimodule R M₂] (f : linear_map R (M 0) (multilinear_map R (fun (i : fin n) => M (fin.succ i)) M₂)) (m : (i : fin (Nat.succ n)) → M i) : coe_fn (linear_map.uncurry_left f) m = coe_fn (coe_fn f (m 0)) (fin.tail m) :=
  rfl

/-- Given a multilinear map `f` in `n+1` variables, split the first variable to obtain
a linear map into multilinear maps in `n` variables, given by `x ↦ (m ↦ f (cons x m))`. -/
def multilinear_map.curry_left {R : Type u} {n : ℕ} {M : fin (Nat.succ n) → Type v} {M₂ : Type v₂} [comm_semiring R] [(i : fin (Nat.succ n)) → add_comm_monoid (M i)] [add_comm_monoid M₂] [(i : fin (Nat.succ n)) → semimodule R (M i)] [semimodule R M₂] (f : multilinear_map R M M₂) : linear_map R (M 0) (multilinear_map R (fun (i : fin n) => M (fin.succ i)) M₂) :=
  linear_map.mk
    (fun (x : M 0) => multilinear_map.mk (fun (m : (i : fin n) → M (fin.succ i)) => coe_fn f (fin.cons x m)) sorry sorry)
    sorry sorry

@[simp] theorem multilinear_map.curry_left_apply {R : Type u} {n : ℕ} {M : fin (Nat.succ n) → Type v} {M₂ : Type v₂} [comm_semiring R] [(i : fin (Nat.succ n)) → add_comm_monoid (M i)] [add_comm_monoid M₂] [(i : fin (Nat.succ n)) → semimodule R (M i)] [semimodule R M₂] (f : multilinear_map R M M₂) (x : M 0) (m : (i : fin n) → M (fin.succ i)) : coe_fn (coe_fn (multilinear_map.curry_left f) x) m = coe_fn f (fin.cons x m) :=
  rfl

@[simp] theorem linear_map.curry_uncurry_left {R : Type u} {n : ℕ} {M : fin (Nat.succ n) → Type v} {M₂ : Type v₂} [comm_semiring R] [(i : fin (Nat.succ n)) → add_comm_monoid (M i)] [add_comm_monoid M₂] [(i : fin (Nat.succ n)) → semimodule R (M i)] [semimodule R M₂] (f : linear_map R (M 0) (multilinear_map R (fun (i : fin n) => M (fin.succ i)) M₂)) : multilinear_map.curry_left (linear_map.uncurry_left f) = f := sorry

@[simp] theorem multilinear_map.uncurry_curry_left {R : Type u} {n : ℕ} {M : fin (Nat.succ n) → Type v} {M₂ : Type v₂} [comm_semiring R] [(i : fin (Nat.succ n)) → add_comm_monoid (M i)] [add_comm_monoid M₂] [(i : fin (Nat.succ n)) → semimodule R (M i)] [semimodule R M₂] (f : multilinear_map R M M₂) : linear_map.uncurry_left (multilinear_map.curry_left f) = f := sorry

/-- The space of multilinear maps on `Π(i : fin (n+1)), M i` is canonically isomorphic to
the space of linear maps from `M 0` to the space of multilinear maps on
`Π(i : fin n), M i.succ `, by separating the first variable. We register this isomorphism as a
linear isomorphism in `multilinear_curry_left_equiv R M M₂`.

The direct and inverse maps are given by `f.uncurry_left` and `f.curry_left`. Use these
unless you need the full framework of linear equivs. -/
def multilinear_curry_left_equiv (R : Type u) {n : ℕ} (M : fin (Nat.succ n) → Type v) (M₂ : Type v₂) [comm_semiring R] [(i : fin (Nat.succ n)) → add_comm_monoid (M i)] [add_comm_monoid M₂] [(i : fin (Nat.succ n)) → semimodule R (M i)] [semimodule R M₂] : linear_equiv R (linear_map R (M 0) (multilinear_map R (fun (i : fin n) => M (fin.succ i)) M₂)) (multilinear_map R M M₂) :=
  linear_equiv.mk linear_map.uncurry_left sorry sorry multilinear_map.curry_left linear_map.curry_uncurry_left sorry

/-! #### Right currying -/

/-- Given a multilinear map `f` in `n` variables to the space of linear maps from `M (last n)` to
`M₂`, construct the corresponding multilinear map on `n+1` variables obtained by concatenating
the variables, given by `m ↦ f (init m) (m (last n))`-/
def multilinear_map.uncurry_right {R : Type u} {n : ℕ} {M : fin (Nat.succ n) → Type v} {M₂ : Type v₂} [comm_semiring R] [(i : fin (Nat.succ n)) → add_comm_monoid (M i)] [add_comm_monoid M₂] [(i : fin (Nat.succ n)) → semimodule R (M i)] [semimodule R M₂] (f : multilinear_map R (fun (i : fin n) => M (coe_fn fin.cast_succ i)) (linear_map R (M (fin.last n)) M₂)) : multilinear_map R M M₂ :=
  multilinear_map.mk (fun (m : (i : fin (Nat.succ n)) → M i) => coe_fn (coe_fn f (fin.init m)) (m (fin.last n))) sorry
    sorry

@[simp] theorem multilinear_map.uncurry_right_apply {R : Type u} {n : ℕ} {M : fin (Nat.succ n) → Type v} {M₂ : Type v₂} [comm_semiring R] [(i : fin (Nat.succ n)) → add_comm_monoid (M i)] [add_comm_monoid M₂] [(i : fin (Nat.succ n)) → semimodule R (M i)] [semimodule R M₂] (f : multilinear_map R (fun (i : fin n) => M (coe_fn fin.cast_succ i)) (linear_map R (M (fin.last n)) M₂)) (m : (i : fin (Nat.succ n)) → M i) : coe_fn (multilinear_map.uncurry_right f) m = coe_fn (coe_fn f (fin.init m)) (m (fin.last n)) :=
  rfl

/-- Given a multilinear map `f` in `n+1` variables, split the last variable to obtain
a multilinear map in `n` variables taking values in linear maps from `M (last n)` to `M₂`, given by
`m ↦ (x ↦ f (snoc m x))`. -/
def multilinear_map.curry_right {R : Type u} {n : ℕ} {M : fin (Nat.succ n) → Type v} {M₂ : Type v₂} [comm_semiring R] [(i : fin (Nat.succ n)) → add_comm_monoid (M i)] [add_comm_monoid M₂] [(i : fin (Nat.succ n)) → semimodule R (M i)] [semimodule R M₂] (f : multilinear_map R M M₂) : multilinear_map R (fun (i : fin n) => M (coe_fn fin.cast_succ i)) (linear_map R (M (fin.last n)) M₂) :=
  multilinear_map.mk
    (fun (m : (i : fin n) → M (coe_fn fin.cast_succ i)) =>
      linear_map.mk (fun (x : M (fin.last n)) => coe_fn f (fin.snoc m x)) sorry sorry)
    sorry sorry

@[simp] theorem multilinear_map.curry_right_apply {R : Type u} {n : ℕ} {M : fin (Nat.succ n) → Type v} {M₂ : Type v₂} [comm_semiring R] [(i : fin (Nat.succ n)) → add_comm_monoid (M i)] [add_comm_monoid M₂] [(i : fin (Nat.succ n)) → semimodule R (M i)] [semimodule R M₂] (f : multilinear_map R M M₂) (m : (i : fin n) → M (coe_fn fin.cast_succ i)) (x : M (fin.last n)) : coe_fn (coe_fn (multilinear_map.curry_right f) m) x = coe_fn f (fin.snoc m x) :=
  rfl

@[simp] theorem multilinear_map.curry_uncurry_right {R : Type u} {n : ℕ} {M : fin (Nat.succ n) → Type v} {M₂ : Type v₂} [comm_semiring R] [(i : fin (Nat.succ n)) → add_comm_monoid (M i)] [add_comm_monoid M₂] [(i : fin (Nat.succ n)) → semimodule R (M i)] [semimodule R M₂] (f : multilinear_map R (fun (i : fin n) => M (coe_fn fin.cast_succ i)) (linear_map R (M (fin.last n)) M₂)) : multilinear_map.curry_right (multilinear_map.uncurry_right f) = f := sorry

@[simp] theorem multilinear_map.uncurry_curry_right {R : Type u} {n : ℕ} {M : fin (Nat.succ n) → Type v} {M₂ : Type v₂} [comm_semiring R] [(i : fin (Nat.succ n)) → add_comm_monoid (M i)] [add_comm_monoid M₂] [(i : fin (Nat.succ n)) → semimodule R (M i)] [semimodule R M₂] (f : multilinear_map R M M₂) : multilinear_map.uncurry_right (multilinear_map.curry_right f) = f := sorry

/-- The space of multilinear maps on `Π(i : fin (n+1)), M i` is canonically isomorphic to
the space of linear maps from the space of multilinear maps on `Π(i : fin n), M i.cast_succ` to the
space of linear maps on `M (last n)`, by separating the last variable. We register this isomorphism
as a linear isomorphism in `multilinear_curry_right_equiv R M M₂`.

The direct and inverse maps are given by `f.uncurry_right` and `f.curry_right`. Use these
unless you need the full framework of linear equivs. -/
def multilinear_curry_right_equiv (R : Type u) {n : ℕ} (M : fin (Nat.succ n) → Type v) (M₂ : Type v₂) [comm_semiring R] [(i : fin (Nat.succ n)) → add_comm_monoid (M i)] [add_comm_monoid M₂] [(i : fin (Nat.succ n)) → semimodule R (M i)] [semimodule R M₂] : linear_equiv R (multilinear_map R (fun (i : fin n) => M (coe_fn fin.cast_succ i)) (linear_map R (M (fin.last n)) M₂))
  (multilinear_map R M M₂) :=
  linear_equiv.mk multilinear_map.uncurry_right sorry sorry multilinear_map.curry_right
    multilinear_map.curry_uncurry_right sorry

namespace multilinear_map


/-- The pushforward of an indexed collection of submodule `p i ⊆ M₁ i` by `f : M₁ → M₂`.

Note that this is not a submodule - it is not closed under addition. -/
def map {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [ring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] [Nonempty ι] (f : multilinear_map R M₁ M₂) (p : (i : ι) → submodule R (M₁ i)) : sub_mul_action R M₂ :=
  sub_mul_action.mk (⇑f '' set_of fun (v : (i : ι) → M₁ i) => ∀ (i : ι), v i ∈ p i) sorry

/-- The map is always nonempty. This lemma is needed to apply `sub_mul_action.zero_mem`. -/
theorem map_nonempty {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [ring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] [Nonempty ι] (f : multilinear_map R M₁ M₂) (p : (i : ι) → submodule R (M₁ i)) : set.nonempty ↑(map f p) :=
  Exists.intro (coe_fn f 0) (Exists.intro 0 { left := fun (i : ι) => submodule.zero_mem (p i), right := rfl })

/-- The range of a multilinear map, closed under scalar multiplication. -/
def range {R : Type u} {ι : Type u'} {M₁ : ι → Type v₁} {M₂ : Type v₂} [DecidableEq ι] [ring R] [(i : ι) → add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [(i : ι) → semimodule R (M₁ i)] [semimodule R M₂] [Nonempty ι] (f : multilinear_map R M₁ M₂) : sub_mul_action R M₂ :=
  map f fun (i : ι) => ⊤

