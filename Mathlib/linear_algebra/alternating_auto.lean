/-
Copyright (c) 2020 Zhangir Azerbayev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Wieser, Zhangir Azerbayev
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.linear_algebra.multilinear
import Mathlib.linear_algebra.linear_independent
import Mathlib.group_theory.perm.sign
import Mathlib.PostPort

universes u_1 u_2 u_3 u_6 l u_4 u_5 u_7 

namespace Mathlib

/-!
# Alternating Maps

We construct the bundled function `alternating_map`, which extends `multilinear_map` with all the
arguments of the same type.

## Main definitions
* `alternating_map R M N ι` is the space of `R`-linear alternating maps from `ι → M` to `N`.
* `f.map_eq_zero_of_eq` expresses that `f` is zero when two inputs are equal.
* `f.map_swap` expresses that `f` is negated when two inputs are swapped.
* `f.map_perm` expresses how `f` varies by a sign change under a permutation of its inputs.
* An `add_comm_monoid`, `add_comm_group`, and `semimodule` structure over `alternating_map`s that
  matches the definitions over `multilinear_map`s.
* `multilinear_map.alternatization`, which makes an alternating map out of a non-alternating one.

## Implementation notes
`alternating_map` is defined in terms of `map_eq_zero_of_eq`, as this is easier to work with than
using `map_swap` as a definition, and does not require `has_neg N`.

`alternating_map`s are provided with a coercion to `multilinear_map`, along with a set of
`norm_cast` lemmas that act on the algebraic structure:

* `alternating_map.coe_add`
* `alternating_map.coe_zero`
* `alternating_map.coe_sub`
* `alternating_map.coe_neg`
* `alternating_map.coe_smul`
-/

-- semiring / add_comm_monoid

-- semiring / add_comm_group

/--
An alternating map is a multilinear map that vanishes when two of its arguments are equal.
-/
structure alternating_map (R : Type u_1) [semiring R] (M : Type u_2) [add_comm_monoid M]
    [semimodule R M] (N : Type u_3) [add_comm_monoid N] [semimodule R N] (ι : Type u_6)
    [DecidableEq ι]
    extends multilinear_map R (fun (i : ι) => M) N where
  map_eq_zero_of_eq' : ∀ (v : ι → M) (i j : ι), v i = v j → i ≠ j → to_fun v = 0

/-- The multilinear map associated to an alternating map -/
namespace alternating_map


/-! Basic coercion simp lemmas, largely copied from `ring_hom` and `multilinear_map` -/

protected instance has_coe_to_fun {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] {N : Type u_3} [add_comm_monoid N] [semimodule R N] {ι : Type u_6}
    [DecidableEq ι] : has_coe_to_fun (alternating_map R M N ι) :=
  has_coe_to_fun.mk (fun (x : alternating_map R M N ι) => ((i : ι) → (fun (i : ι) => M) i) → N)
    fun (x : alternating_map R M N ι) => to_fun x

@[simp] theorem to_fun_eq_coe {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] {N : Type u_3} [add_comm_monoid N] [semimodule R N] {ι : Type u_6}
    [DecidableEq ι] (f : alternating_map R M N ι) : to_fun f = ⇑f :=
  rfl

@[simp] theorem coe_mk {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] {N : Type u_3} [add_comm_monoid N] [semimodule R N] {ι : Type u_6}
    [DecidableEq ι] (f : (ι → M) → N)
    (h₁ :
      ∀ (m : (i : ι) → (fun (i : ι) => M) i) (i : ι) (x y : M),
        f (function.update m i (x + y)) = f (function.update m i x) + f (function.update m i y))
    (h₂ :
      ∀ (m : (i : ι) → (fun (i : ι) => M) i) (i : ι) (c : R) (x : M),
        f (function.update m i (c • x)) = c • f (function.update m i x))
    (h₃ : ∀ (v : ι → M) (i j : ι), v i = v j → i ≠ j → f v = 0) : ⇑(mk f h₁ h₂ h₃) = f :=
  rfl

theorem congr_fun {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M] [semimodule R M]
    {N : Type u_3} [add_comm_monoid N] [semimodule R N] {ι : Type u_6} [DecidableEq ι]
    {f : alternating_map R M N ι} {g : alternating_map R M N ι} (h : f = g) (x : ι → M) :
    coe_fn f x = coe_fn g x :=
  congr_arg (fun (h : alternating_map R M N ι) => coe_fn h x) h

theorem congr_arg {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M] [semimodule R M]
    {N : Type u_3} [add_comm_monoid N] [semimodule R N] {ι : Type u_6} [DecidableEq ι]
    (f : alternating_map R M N ι) {x : ι → M} {y : ι → M} (h : x = y) : coe_fn f x = coe_fn f y :=
  congr_arg (fun (x : ι → M) => coe_fn f x) h

theorem coe_inj {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M] [semimodule R M]
    {N : Type u_3} [add_comm_monoid N] [semimodule R N] {ι : Type u_6} [DecidableEq ι]
    {f : alternating_map R M N ι} {g : alternating_map R M N ι} (h : ⇑f = ⇑g) : f = g :=
  sorry

theorem ext {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M] [semimodule R M]
    {N : Type u_3} [add_comm_monoid N] [semimodule R N] {ι : Type u_6} [DecidableEq ι]
    {f : alternating_map R M N ι} {f' : alternating_map R M N ι}
    (H : ∀ (x : (i : ι) → (fun (i : ι) => M) i), coe_fn f x = coe_fn f' x) : f = f' :=
  coe_inj (funext H)

theorem ext_iff {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M] [semimodule R M]
    {N : Type u_3} [add_comm_monoid N] [semimodule R N] {ι : Type u_6} [DecidableEq ι]
    {f : alternating_map R M N ι} {g : alternating_map R M N ι} :
    f = g ↔ ∀ (x : (i : ι) → (fun (i : ι) => M) i), coe_fn f x = coe_fn g x :=
  { mp := fun (h : f = g) (x : (i : ι) → (fun (i : ι) => M) i) => h ▸ rfl,
    mpr := fun (h : ∀ (x : (i : ι) → (fun (i : ι) => M) i), coe_fn f x = coe_fn g x) => ext h }

protected instance multilinear_map.has_coe {R : Type u_1} [semiring R] {M : Type u_2}
    [add_comm_monoid M] [semimodule R M] {N : Type u_3} [add_comm_monoid N] [semimodule R N]
    {ι : Type u_6} [DecidableEq ι] :
    has_coe (alternating_map R M N ι) (multilinear_map R (fun (i : ι) => M) N) :=
  has_coe.mk fun (x : alternating_map R M N ι) => to_multilinear_map x

@[simp] theorem coe_multilinear_map {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] {N : Type u_3} [add_comm_monoid N] [semimodule R N] {ι : Type u_6}
    [DecidableEq ι] (f : alternating_map R M N ι) : ⇑↑f = ⇑f :=
  rfl

@[simp] theorem to_multilinear_map_eq_coe {R : Type u_1} [semiring R] {M : Type u_2}
    [add_comm_monoid M] [semimodule R M] {N : Type u_3} [add_comm_monoid N] [semimodule R N]
    {ι : Type u_6} [DecidableEq ι] (f : alternating_map R M N ι) : to_multilinear_map f = ↑f :=
  rfl

@[simp] theorem coe_multilinear_map_mk {R : Type u_1} [semiring R] {M : Type u_2}
    [add_comm_monoid M] [semimodule R M] {N : Type u_3} [add_comm_monoid N] [semimodule R N]
    {ι : Type u_6} [DecidableEq ι] (f : (ι → M) → N)
    (h₁ :
      ∀ (m : (i : ι) → (fun (i : ι) => M) i) (i : ι) (x y : M),
        f (function.update m i (x + y)) = f (function.update m i x) + f (function.update m i y))
    (h₂ :
      ∀ (m : (i : ι) → (fun (i : ι) => M) i) (i : ι) (c : R) (x : M),
        f (function.update m i (c • x)) = c • f (function.update m i x))
    (h₃ : ∀ (v : ι → M) (i j : ι), v i = v j → i ≠ j → f v = 0) :
    ↑(mk f h₁ h₂ h₃) = multilinear_map.mk f h₁ h₂ :=
  rfl

/-!
### Simp-normal forms of the structure fields

These are expressed in terms of `⇑f` instead of `f.to_fun`.
-/

@[simp] theorem map_add {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] {N : Type u_3} [add_comm_monoid N] [semimodule R N] {ι : Type u_6}
    [DecidableEq ι] (f : alternating_map R M N ι) (v : ι → M) (i : ι) (x : M) (y : M) :
    coe_fn f (function.update v i (x + y)) =
        coe_fn f (function.update v i x) + coe_fn f (function.update v i y) :=
  multilinear_map.map_add' (to_multilinear_map f) v i x y

@[simp] theorem map_sub {R : Type u_1} [semiring R] {M' : Type u_4} [add_comm_group M']
    [semimodule R M'] {N' : Type u_5} [add_comm_group N'] [semimodule R N'] {ι : Type u_6}
    [DecidableEq ι] (g' : alternating_map R M' N' ι) (v' : ι → M') (i : ι) (x : M') (y : M') :
    coe_fn g' (function.update v' i (x - y)) =
        coe_fn g' (function.update v' i x) - coe_fn g' (function.update v' i y) :=
  multilinear_map.map_sub (to_multilinear_map g') v' i x y

@[simp] theorem map_neg {R : Type u_1} [semiring R] {M' : Type u_4} [add_comm_group M']
    [semimodule R M'] {N' : Type u_5} [add_comm_group N'] [semimodule R N'] {ι : Type u_6}
    [DecidableEq ι] (g' : alternating_map R M' N' ι) (v' : ι → M') (i : ι) (x : M') :
    coe_fn g' (function.update v' i (-x)) = -coe_fn g' (function.update v' i x) :=
  multilinear_map.map_neg (to_multilinear_map g') v' i x

@[simp] theorem map_smul {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] {N : Type u_3} [add_comm_monoid N] [semimodule R N] {ι : Type u_6}
    [DecidableEq ι] (f : alternating_map R M N ι) (v : ι → M) (i : ι) (r : R) (x : M) :
    coe_fn f (function.update v i (r • x)) = r • coe_fn f (function.update v i x) :=
  multilinear_map.map_smul' (to_multilinear_map f) v i r x

@[simp] theorem map_eq_zero_of_eq {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] {N : Type u_3} [add_comm_monoid N] [semimodule R N] {ι : Type u_6}
    [DecidableEq ι] (f : alternating_map R M N ι) (v : ι → M) {i : ι} {j : ι} (h : v i = v j)
    (hij : i ≠ j) : coe_fn f v = 0 :=
  map_eq_zero_of_eq' f v i j h hij

/-!
### Algebraic structure inherited from `multilinear_map`

`alternating_map` carries the same `add_comm_monoid`, `add_comm_group`, and `semimodule` structure
as `multilinear_map`
-/

protected instance has_add {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] {N : Type u_3} [add_comm_monoid N] [semimodule R N] {ι : Type u_6}
    [DecidableEq ι] : Add (alternating_map R M N ι) :=
  { add :=
      fun (a b : alternating_map R M N ι) =>
        mk (multilinear_map.to_fun (↑a + ↑b)) sorry sorry sorry }

@[simp] theorem add_apply {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] {N : Type u_3} [add_comm_monoid N] [semimodule R N] {ι : Type u_6}
    [DecidableEq ι] (f : alternating_map R M N ι) (f' : alternating_map R M N ι) (v : ι → M) :
    coe_fn (f + f') v = coe_fn f v + coe_fn f' v :=
  rfl

theorem coe_add {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M] [semimodule R M]
    {N : Type u_3} [add_comm_monoid N] [semimodule R N] {ι : Type u_6} [DecidableEq ι]
    (f : alternating_map R M N ι) (f' : alternating_map R M N ι) : ↑(f + f') = ↑f + ↑f' :=
  rfl

protected instance has_zero {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] {N : Type u_3} [add_comm_monoid N] [semimodule R N] {ι : Type u_6}
    [DecidableEq ι] : HasZero (alternating_map R M N ι) :=
  { zero := mk (multilinear_map.to_fun 0) sorry sorry sorry }

@[simp] theorem zero_apply {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] {N : Type u_3} [add_comm_monoid N] [semimodule R N] {ι : Type u_6}
    [DecidableEq ι] (v : ι → M) : coe_fn 0 v = 0 :=
  rfl

theorem coe_zero {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M] [semimodule R M]
    {N : Type u_3} [add_comm_monoid N] [semimodule R N] {ι : Type u_6} [DecidableEq ι] : ↑0 = 0 :=
  rfl

protected instance inhabited {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] {N : Type u_3} [add_comm_monoid N] [semimodule R N] {ι : Type u_6}
    [DecidableEq ι] : Inhabited (alternating_map R M N ι) :=
  { default := 0 }

protected instance add_comm_monoid {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] {N : Type u_3} [add_comm_monoid N] [semimodule R N] {ι : Type u_6}
    [DecidableEq ι] : add_comm_monoid (alternating_map R M N ι) :=
  add_comm_monoid.mk Add.add sorry 0 sorry sorry sorry

protected instance has_neg {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] {N' : Type u_5} [add_comm_group N'] [semimodule R N'] {ι : Type u_6}
    [DecidableEq ι] : Neg (alternating_map R M N' ι) :=
  { neg :=
      fun (f : alternating_map R M N' ι) => mk (multilinear_map.to_fun (-↑f)) sorry sorry sorry }

@[simp] theorem neg_apply {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] {N' : Type u_5} [add_comm_group N'] [semimodule R N'] {ι : Type u_6}
    [DecidableEq ι] (g : alternating_map R M N' ι) (m : ι → M) : coe_fn (-g) m = -coe_fn g m :=
  rfl

theorem coe_neg {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M] [semimodule R M]
    {N' : Type u_5} [add_comm_group N'] [semimodule R N'] {ι : Type u_6} [DecidableEq ι]
    (g : alternating_map R M N' ι) : ↑(-g) = -↑g :=
  rfl

protected instance has_sub {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] {N' : Type u_5} [add_comm_group N'] [semimodule R N'] {ι : Type u_6}
    [DecidableEq ι] : Sub (alternating_map R M N' ι) :=
  { sub :=
      fun (f g : alternating_map R M N' ι) =>
        mk (multilinear_map.to_fun (↑f - ↑g)) sorry sorry sorry }

@[simp] theorem sub_apply {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] {N' : Type u_5} [add_comm_group N'] [semimodule R N'] {ι : Type u_6}
    [DecidableEq ι] (g : alternating_map R M N' ι) (g₂ : alternating_map R M N' ι) (m : ι → M) :
    coe_fn (g - g₂) m = coe_fn g m - coe_fn g₂ m :=
  rfl

theorem coe_sub {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M] [semimodule R M]
    {N' : Type u_5} [add_comm_group N'] [semimodule R N'] {ι : Type u_6} [DecidableEq ι]
    (g : alternating_map R M N' ι) (g₂ : alternating_map R M N' ι) : ↑(g - g₂) = ↑g - ↑g₂ :=
  rfl

protected instance add_comm_group {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] {N' : Type u_5} [add_comm_group N'] [semimodule R N'] {ι : Type u_6}
    [DecidableEq ι] : add_comm_group (alternating_map R M N' ι) :=
  add_comm_group.mk Add.add sorry 0 sorry sorry Neg.neg Sub.sub sorry sorry

protected instance has_scalar {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] {N : Type u_3} [add_comm_monoid N] [semimodule R N] {ι : Type u_6}
    [DecidableEq ι] {S : Type u_7} [monoid S] [distrib_mul_action S N] [smul_comm_class R S N] :
    has_scalar S (alternating_map R M N ι) :=
  has_scalar.mk
    fun (c : S) (f : alternating_map R M N ι) =>
      mk (multilinear_map.to_fun (c • ↑f)) sorry sorry sorry

@[simp] theorem smul_apply {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] {N : Type u_3} [add_comm_monoid N] [semimodule R N] {ι : Type u_6}
    [DecidableEq ι] (f : alternating_map R M N ι) {S : Type u_7} [monoid S] [distrib_mul_action S N]
    [smul_comm_class R S N] (c : S) (m : ι → M) : coe_fn (c • f) m = c • coe_fn f m :=
  rfl

theorem coe_smul {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M] [semimodule R M]
    {N : Type u_3} [add_comm_monoid N] [semimodule R N] {ι : Type u_6} [DecidableEq ι]
    (f : alternating_map R M N ι) {S : Type u_7} [monoid S] [distrib_mul_action S N]
    [smul_comm_class R S N] (c : S) : ↑(c • f) = c • ↑f :=
  rfl

protected instance distrib_mul_action {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] {N : Type u_3} [add_comm_monoid N] [semimodule R N] {ι : Type u_6}
    [DecidableEq ι] {S : Type u_7} [monoid S] [distrib_mul_action S N] [smul_comm_class R S N] :
    distrib_mul_action S (alternating_map R M N ι) :=
  distrib_mul_action.mk sorry sorry

/-- The space of multilinear maps over an algebra over `R` is a module over `R`, for the pointwise
addition and scalar multiplication. -/
protected instance semimodule {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] {N : Type u_3} [add_comm_monoid N] [semimodule R N] {ι : Type u_6}
    [DecidableEq ι] {S : Type u_7} [semiring S] [semimodule S N] [smul_comm_class R S N] :
    semimodule S (alternating_map R M N ι) :=
  semimodule.mk sorry sorry

end alternating_map


/-!
### Composition with linear maps
-/

namespace linear_map


/-- Composing a alternating map with a linear map gives again a alternating map. -/
def comp_alternating_map {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] {N : Type u_3} [add_comm_monoid N] [semimodule R N] {ι : Type u_6}
    [DecidableEq ι] {N₂ : Type u_7} [add_comm_monoid N₂] [semimodule R N₂] (g : linear_map R N N₂) :
    alternating_map R M N ι →+ alternating_map R M N₂ ι :=
  add_monoid_hom.mk
    (fun (f : alternating_map R M N ι) =>
      alternating_map.mk (multilinear_map.to_fun (comp_multilinear_map g ↑f)) sorry sorry sorry)
    sorry sorry

@[simp] theorem coe_comp_alternating_map {R : Type u_1} [semiring R] {M : Type u_2}
    [add_comm_monoid M] [semimodule R M] {N : Type u_3} [add_comm_monoid N] [semimodule R N]
    {ι : Type u_6} [DecidableEq ι] {N₂ : Type u_7} [add_comm_monoid N₂] [semimodule R N₂]
    (g : linear_map R N N₂) (f : alternating_map R M N ι) :
    ⇑(coe_fn (comp_alternating_map g) f) = ⇑g ∘ ⇑f :=
  rfl

theorem comp_alternating_map_apply {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] {N : Type u_3} [add_comm_monoid N] [semimodule R N] {ι : Type u_6}
    [DecidableEq ι] {N₂ : Type u_7} [add_comm_monoid N₂] [semimodule R N₂] (g : linear_map R N N₂)
    (f : alternating_map R M N ι) (m : ι → M) :
    coe_fn (coe_fn (comp_alternating_map g) f) m = coe_fn g (coe_fn f m) :=
  rfl

end linear_map


namespace alternating_map


/-!
### Other lemmas from `multilinear_map`
-/

theorem map_update_sum {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] {N : Type u_3} [add_comm_monoid N] [semimodule R N] {ι : Type u_6}
    [DecidableEq ι] (f : alternating_map R M N ι) {α : Type u_4} (t : finset α) (i : ι) (g : α → M)
    (m : ι → M) :
    coe_fn f (function.update m i (finset.sum t fun (a : α) => g a)) =
        finset.sum t fun (a : α) => coe_fn f (function.update m i (g a)) :=
  multilinear_map.map_update_sum (to_multilinear_map f) t i g m

/-!
### Theorems specific to alternating maps

Various properties of reordered and repeated inputs which follow from
`alternating_map.map_eq_zero_of_eq`.
-/

theorem map_update_self {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] {N : Type u_3} [add_comm_monoid N] [semimodule R N] {ι : Type u_6}
    [DecidableEq ι] (f : alternating_map R M N ι) (v : ι → M) {i : ι} {j : ι} (hij : i ≠ j) :
    coe_fn f (function.update v i (v j)) = 0 :=
  sorry

theorem map_update_update {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] {N : Type u_3} [add_comm_monoid N] [semimodule R N] {ι : Type u_6}
    [DecidableEq ι] (f : alternating_map R M N ι) (v : ι → M) {i : ι} {j : ι} (hij : i ≠ j)
    (m : M) : coe_fn f (function.update (function.update v i m) j m) = 0 :=
  sorry

theorem map_swap_add {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M] [semimodule R M]
    {N : Type u_3} [add_comm_monoid N] [semimodule R N] {ι : Type u_6} [DecidableEq ι]
    (f : alternating_map R M N ι) (v : ι → M) {i : ι} {j : ι} (hij : i ≠ j) :
    coe_fn f (v ∘ ⇑(equiv.swap i j)) + coe_fn f v = 0 :=
  sorry

theorem map_add_swap {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M] [semimodule R M]
    {N : Type u_3} [add_comm_monoid N] [semimodule R N] {ι : Type u_6} [DecidableEq ι]
    (f : alternating_map R M N ι) (v : ι → M) {i : ι} {j : ι} (hij : i ≠ j) :
    coe_fn f v + coe_fn f (v ∘ ⇑(equiv.swap i j)) = 0 :=
  sorry

theorem map_swap {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M] [semimodule R M]
    {N' : Type u_5} [add_comm_group N'] [semimodule R N'] {ι : Type u_6} [DecidableEq ι]
    (g : alternating_map R M N' ι) (v : ι → M) {i : ι} {j : ι} (hij : i ≠ j) :
    coe_fn g (v ∘ ⇑(equiv.swap i j)) = -coe_fn g v :=
  eq_neg_of_add_eq_zero (map_swap_add g v hij)

theorem map_perm {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M] [semimodule R M]
    {N' : Type u_5} [add_comm_group N'] [semimodule R N'] {ι : Type u_6} [DecidableEq ι]
    (g : alternating_map R M N' ι) [fintype ι] (v : ι → M) (σ : equiv.perm ι) :
    coe_fn g (v ∘ ⇑σ) = ↑(coe_fn equiv.perm.sign σ) • coe_fn g v :=
  sorry

theorem map_congr_perm {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] {N' : Type u_5} [add_comm_group N'] [semimodule R N'] {ι : Type u_6}
    [DecidableEq ι] (g : alternating_map R M N' ι) (v : ι → M) [fintype ι] (σ : equiv.perm ι) :
    coe_fn g v = ↑(coe_fn equiv.perm.sign σ) • coe_fn g (v ∘ ⇑σ) :=
  sorry

theorem coe_dom_dom_congr {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] {N' : Type u_5} [add_comm_group N'] [semimodule R N'] {ι : Type u_6}
    [DecidableEq ι] (g : alternating_map R M N' ι) [fintype ι] (σ : equiv.perm ι) :
    multilinear_map.dom_dom_congr σ ↑g = ↑(coe_fn equiv.perm.sign σ) • ↑g :=
  multilinear_map.ext fun (v : ι → M) => map_perm g v σ

/-- If the arguments are linearly dependent then the result is `0`.

TODO: Can the `division_ring` requirement be relaxed? -/
theorem map_linear_dependent {ι : Type u_6} [DecidableEq ι] {K : Type u_1} [division_ring K]
    {M : Type u_2} [add_comm_group M] [semimodule K M] {N : Type u_3} [add_comm_group N]
    [semimodule K N] (f : alternating_map K M N ι) (v : ι → M) (h : ¬linear_independent K v) :
    coe_fn f v = 0 :=
  sorry

end alternating_map


namespace multilinear_map


/-- Produce an `alternating_map` out of a `multilinear_map`, by summing over all argument
permutations. -/
def alternatization {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M] [semimodule R M]
    {N' : Type u_5} [add_comm_group N'] [semimodule R N'] {ι : Type u_6} [DecidableEq ι]
    [fintype ι] : multilinear_map R (fun (i : ι) => M) N' →+ alternating_map R M N' ι :=
  add_monoid_hom.mk
    (fun (m : multilinear_map R (fun (i : ι) => M) N') =>
      alternating_map.mk
        ⇑(finset.sum finset.univ
            fun (σ : equiv.perm ι) => ↑(coe_fn equiv.perm.sign σ) • dom_dom_congr σ m)
        sorry sorry sorry)
    sorry sorry

theorem alternatization_def {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] {N' : Type u_5} [add_comm_group N'] [semimodule R N'] {ι : Type u_6}
    [DecidableEq ι] [fintype ι] (m : multilinear_map R (fun (i : ι) => M) N') :
    ⇑(coe_fn alternatization m) =
        ⇑(finset.sum finset.univ
            fun (σ : equiv.perm ι) => ↑(coe_fn equiv.perm.sign σ) • dom_dom_congr σ m) :=
  rfl

theorem alternatization_apply {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] {N' : Type u_5} [add_comm_group N'] [semimodule R N'] {ι : Type u_6}
    [DecidableEq ι] [fintype ι] (m : multilinear_map R (fun (i : ι) => M) N') (v : ι → M) :
    coe_fn (coe_fn alternatization m) v =
        finset.sum finset.univ
          fun (σ : equiv.perm ι) => ↑(coe_fn equiv.perm.sign σ) • coe_fn (dom_dom_congr σ m) v :=
  sorry

end multilinear_map


namespace alternating_map


/-- Alternatizing a multilinear map that is already alternating results in a scale factor of `n!`,
where `n` is the number of inputs. -/
theorem coe_alternatization {R : Type u_1} [semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] {N' : Type u_5} [add_comm_group N'] [semimodule R N'] {ι : Type u_6}
    [DecidableEq ι] [fintype ι] (a : alternating_map R M N' ι) :
    coe_fn multilinear_map.alternatization ↑a = nat.factorial (fintype.card ι) • a :=
  sorry

end alternating_map


namespace linear_map


/-- Composition with a linear map before and after alternatization are equivalent. -/
theorem comp_multilinear_map_alternatization {R : Type u_1} [semiring R] {M : Type u_2}
    [add_comm_monoid M] [semimodule R M] {N' : Type u_5} [add_comm_group N'] [semimodule R N']
    {ι : Type u_6} [DecidableEq ι] {N'₂ : Type u_7} [add_comm_group N'₂] [semimodule R N'₂]
    [fintype ι] (g : linear_map R N' N'₂) (f : multilinear_map R (fun (_x : ι) => M) N') :
    coe_fn multilinear_map.alternatization (comp_multilinear_map g f) =
        coe_fn (comp_alternating_map g) (coe_fn multilinear_map.alternatization f) :=
  sorry

end Mathlib