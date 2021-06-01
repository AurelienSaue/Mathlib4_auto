/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kevin Buzzard, Scott Morrison, Johan Commelin, Chris Hughes,
  Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.group.commute
import Mathlib.algebra.group_with_zero.defs
import Mathlib.PostPort

universes u_6 u_7 l u_1 u_2 u_3 u_4 u_5 

namespace Mathlib

/-!
# monoid and group homomorphisms

This file defines the bundled structures for monoid and group homomorphisms. Namely, we define
`monoid_hom` (resp., `add_monoid_hom`) to be bundled homomorphisms between multiplicative (resp.,
additive) monoids or groups.

We also define coercion to a function, and  usual operations: composition, identity homomorphism,
pointwise multiplication and pointwise inversion.

This file also defines the lesser-used (and notation-less) homomorphism types which are used as
building blocks for other homomorphisms:

* `zero_hom`
* `one_hom`
* `add_hom`
* `mul_hom`
* `monoid_with_zero_hom`

## Notations

* `→*` for bundled monoid homs (also use for group homs)
* `→+` for bundled add_monoid homs (also use for add_group homs)

## implementation notes

There's a coercion from bundled homs to fun, and the canonical
notation is to use the bundled hom as a function via this coercion.

There is no `group_hom` -- the idea is that `monoid_hom` is used.
The constructor for `monoid_hom` needs a proof of `map_one` as well
as `map_mul`; a separate constructor `monoid_hom.mk'` will construct
group homs (i.e. monoid homs between groups) given only a proof
that multiplication is preserved,

Implicit `{}` brackets are often used instead of type class `[]` brackets.  This is done when the
instances can be inferred because they are implicit arguments to the type `monoid_hom`.  When they
can be inferred from the type it is faster to use this method than to use type class inference.

Historically this file also included definitions of unbundled homomorphism classes; they were
deprecated and moved to `deprecated/group`.

## Tags

monoid_hom, add_monoid_hom

-/

-- for easy multiple inheritance

/-- Homomorphism that preserves zero -/
structure zero_hom (M : Type u_6) (N : Type u_7) [HasZero M] [HasZero N] where
  to_fun : M → N
  map_zero' : to_fun 0 = 0

/-- Homomorphism that preserves addition -/
structure add_hom (M : Type u_6) (N : Type u_7) [Add M] [Add N] where
  to_fun : M → N
  map_add' : ∀ (x y : M), to_fun (x + y) = to_fun x + to_fun y

/-- Bundled add_monoid homomorphisms; use this for bundled add_group homomorphisms too. -/
structure add_monoid_hom (M : Type u_6) (N : Type u_7) [add_monoid M] [add_monoid N]
    extends zero_hom M N, add_hom M N where

infixr:25 " →+ " => Mathlib.add_monoid_hom

/-- Homomorphism that preserves one -/
structure one_hom (M : Type u_6) (N : Type u_7) [HasOne M] [HasOne N] where
  to_fun : M → N
  map_one' : to_fun 1 = 1

/-- Homomorphism that preserves multiplication -/
structure mul_hom (M : Type u_6) (N : Type u_7) [Mul M] [Mul N] where
  to_fun : M → N
  map_mul' : ∀ (x y : M), to_fun (x * y) = to_fun x * to_fun y

/-- Bundled monoid homomorphisms; use this for bundled group homomorphisms too. -/
structure monoid_hom (M : Type u_6) (N : Type u_7) [monoid M] [monoid N]
    extends one_hom M N, mul_hom M N where

/-- Bundled monoid with zero homomorphisms; use this for bundled group with zero homomorphisms
too. -/
structure monoid_with_zero_hom (M : Type u_6) (N : Type u_7) [monoid_with_zero M]
    [monoid_with_zero N]
    extends zero_hom M N, monoid_hom M N where

infixr:25 " →* " => Mathlib.monoid_hom

-- completely uninteresting lemmas about coercion to function, that all homs need

/-! Bundled morphisms can be down-cast to weaker bundlings -/

protected instance monoid_hom.has_coe_to_one_hom {M : Type u_1} {N : Type u_2} {mM : monoid M}
    {mN : monoid N} : has_coe (M →* N) (one_hom M N) :=
  has_coe.mk monoid_hom.to_one_hom

protected instance add_monoid_hom.has_coe_to_add_hom {M : Type u_1} {N : Type u_2}
    {mM : add_monoid M} {mN : add_monoid N} : has_coe (M →+ N) (add_hom M N) :=
  has_coe.mk add_monoid_hom.to_add_hom

protected instance monoid_with_zero_hom.has_coe_to_monoid_hom {M : Type u_1} {N : Type u_2}
    {mM : monoid_with_zero M} {mN : monoid_with_zero N} :
    has_coe (monoid_with_zero_hom M N) (M →* N) :=
  has_coe.mk monoid_with_zero_hom.to_monoid_hom

protected instance monoid_with_zero_hom.has_coe_to_zero_hom {M : Type u_1} {N : Type u_2}
    {mM : monoid_with_zero M} {mN : monoid_with_zero N} :
    has_coe (monoid_with_zero_hom M N) (zero_hom M N) :=
  has_coe.mk monoid_with_zero_hom.to_zero_hom

/-! The simp-normal form of morphism coercion is `f.to_..._hom`. This choice is primarily because
this is the way things were before the above coercions were introduced. Bundled morphisms defined
elsewhere in Mathlib may choose `↑f` as their simp-normal form instead. -/

@[simp] theorem monoid_hom.coe_eq_to_one_hom {M : Type u_1} {N : Type u_2} {mM : monoid M}
    {mN : monoid N} (f : M →* N) : ↑f = monoid_hom.to_one_hom f :=
  rfl

@[simp] theorem add_monoid_hom.coe_eq_to_add_hom {M : Type u_1} {N : Type u_2} {mM : add_monoid M}
    {mN : add_monoid N} (f : M →+ N) : ↑f = add_monoid_hom.to_add_hom f :=
  rfl

@[simp] theorem monoid_with_zero_hom.coe_eq_to_monoid_hom {M : Type u_1} {N : Type u_2}
    {mM : monoid_with_zero M} {mN : monoid_with_zero N} (f : monoid_with_zero_hom M N) :
    ↑f = monoid_with_zero_hom.to_monoid_hom f :=
  rfl

@[simp] theorem monoid_with_zero_hom.coe_eq_to_zero_hom {M : Type u_1} {N : Type u_2}
    {mM : monoid_with_zero M} {mN : monoid_with_zero N} (f : monoid_with_zero_hom M N) :
    ↑f = monoid_with_zero_hom.to_zero_hom f :=
  rfl

protected instance zero_hom.has_coe_to_fun {M : Type u_1} {N : Type u_2} {mM : HasZero M}
    {mN : HasZero N} : has_coe_to_fun (zero_hom M N) :=
  has_coe_to_fun.mk (fun (x : zero_hom M N) => M → N) zero_hom.to_fun

protected instance mul_hom.has_coe_to_fun {M : Type u_1} {N : Type u_2} {mM : Mul M} {mN : Mul N} :
    has_coe_to_fun (mul_hom M N) :=
  has_coe_to_fun.mk (fun (x : mul_hom M N) => M → N) mul_hom.to_fun

protected instance add_monoid_hom.has_coe_to_fun {M : Type u_1} {N : Type u_2} {mM : add_monoid M}
    {mN : add_monoid N} : has_coe_to_fun (M →+ N) :=
  has_coe_to_fun.mk (fun (x : M →+ N) => M → N) add_monoid_hom.to_fun

protected instance monoid_with_zero_hom.has_coe_to_fun {M : Type u_1} {N : Type u_2}
    {mM : monoid_with_zero M} {mN : monoid_with_zero N} :
    has_coe_to_fun (monoid_with_zero_hom M N) :=
  has_coe_to_fun.mk (fun (x : monoid_with_zero_hom M N) => M → N) monoid_with_zero_hom.to_fun

-- these must come after the coe_to_fun definitions

@[simp] theorem zero_hom.to_fun_eq_coe {M : Type u_1} {N : Type u_2} [HasZero M] [HasZero N]
    (f : zero_hom M N) : zero_hom.to_fun f = ⇑f :=
  rfl

@[simp] theorem mul_hom.to_fun_eq_coe {M : Type u_1} {N : Type u_2} [Mul M] [Mul N]
    (f : mul_hom M N) : mul_hom.to_fun f = ⇑f :=
  rfl

@[simp] theorem add_monoid_hom.to_fun_eq_coe {M : Type u_1} {N : Type u_2} [add_monoid M]
    [add_monoid N] (f : M →+ N) : add_monoid_hom.to_fun f = ⇑f :=
  rfl

@[simp] theorem monoid_with_zero_hom.to_fun_eq_coe {M : Type u_1} {N : Type u_2}
    [monoid_with_zero M] [monoid_with_zero N] (f : monoid_with_zero_hom M N) :
    monoid_with_zero_hom.to_fun f = ⇑f :=
  rfl

@[simp] theorem one_hom.coe_mk {M : Type u_1} {N : Type u_2} [HasOne M] [HasOne N] (f : M → N)
    (h1 : f 1 = 1) : ⇑(one_hom.mk f h1) = f :=
  rfl

@[simp] theorem add_hom.coe_mk {M : Type u_1} {N : Type u_2} [Add M] [Add N] (f : M → N)
    (hmul : ∀ (x y : M), f (x + y) = f x + f y) : ⇑(add_hom.mk f hmul) = f :=
  rfl

@[simp] theorem add_monoid_hom.coe_mk {M : Type u_1} {N : Type u_2} [add_monoid M] [add_monoid N]
    (f : M → N) (h1 : f 0 = 0) (hmul : ∀ (x y : M), f (x + y) = f x + f y) :
    ⇑(add_monoid_hom.mk f h1 hmul) = f :=
  rfl

@[simp] theorem monoid_with_zero_hom.coe_mk {M : Type u_1} {N : Type u_2} [monoid_with_zero M]
    [monoid_with_zero N] (f : M → N) (h0 : f 0 = 0) (h1 : f 1 = 1)
    (hmul : ∀ (x y : M), f (x * y) = f x * f y) : ⇑(monoid_with_zero_hom.mk f h0 h1 hmul) = f :=
  rfl

@[simp] theorem monoid_hom.to_one_hom_coe {M : Type u_1} {N : Type u_2} [monoid M] [monoid N]
    (f : M →* N) : ⇑(monoid_hom.to_one_hom f) = ⇑f :=
  rfl

@[simp] theorem add_monoid_hom.to_add_hom_coe {M : Type u_1} {N : Type u_2} [add_monoid M]
    [add_monoid N] (f : M →+ N) : ⇑(add_monoid_hom.to_add_hom f) = ⇑f :=
  rfl

@[simp] theorem monoid_with_zero_hom.to_zero_hom_coe {M : Type u_1} {N : Type u_2}
    [monoid_with_zero M] [monoid_with_zero N] (f : monoid_with_zero_hom M N) :
    ⇑(monoid_with_zero_hom.to_zero_hom f) = ⇑f :=
  rfl

@[simp] theorem monoid_with_zero_hom.to_monoid_hom_coe {M : Type u_1} {N : Type u_2}
    [monoid_with_zero M] [monoid_with_zero N] (f : monoid_with_zero_hom M N) :
    ⇑(monoid_with_zero_hom.to_monoid_hom f) = ⇑f :=
  rfl

theorem one_hom.congr_fun {M : Type u_1} {N : Type u_2} [HasOne M] [HasOne N] {f : one_hom M N}
    {g : one_hom M N} (h : f = g) (x : M) : coe_fn f x = coe_fn g x :=
  congr_arg (fun (h : one_hom M N) => coe_fn h x) h

theorem add_hom.congr_fun {M : Type u_1} {N : Type u_2} [Add M] [Add N] {f : add_hom M N}
    {g : add_hom M N} (h : f = g) (x : M) : coe_fn f x = coe_fn g x :=
  congr_arg (fun (h : add_hom M N) => coe_fn h x) h

theorem add_monoid_hom.congr_fun {M : Type u_1} {N : Type u_2} [add_monoid M] [add_monoid N]
    {f : M →+ N} {g : M →+ N} (h : f = g) (x : M) : coe_fn f x = coe_fn g x :=
  congr_arg (fun (h : M →+ N) => coe_fn h x) h

theorem monoid_with_zero_hom.congr_fun {M : Type u_1} {N : Type u_2} [monoid_with_zero M]
    [monoid_with_zero N] {f : monoid_with_zero_hom M N} {g : monoid_with_zero_hom M N} (h : f = g)
    (x : M) : coe_fn f x = coe_fn g x :=
  congr_arg (fun (h : monoid_with_zero_hom M N) => coe_fn h x) h

theorem one_hom.congr_arg {M : Type u_1} {N : Type u_2} [HasOne M] [HasOne N] (f : one_hom M N)
    {x : M} {y : M} (h : x = y) : coe_fn f x = coe_fn f y :=
  congr_arg (fun (x : M) => coe_fn f x) h

theorem add_hom.congr_arg {M : Type u_1} {N : Type u_2} [Add M] [Add N] (f : add_hom M N) {x : M}
    {y : M} (h : x = y) : coe_fn f x = coe_fn f y :=
  congr_arg (fun (x : M) => coe_fn f x) h

theorem add_monoid_hom.congr_arg {M : Type u_1} {N : Type u_2} [add_monoid M] [add_monoid N]
    (f : M →+ N) {x : M} {y : M} (h : x = y) : coe_fn f x = coe_fn f y :=
  congr_arg (fun (x : M) => coe_fn f x) h

theorem monoid_with_zero_hom.congr_arg {M : Type u_1} {N : Type u_2} [monoid_with_zero M]
    [monoid_with_zero N] (f : monoid_with_zero_hom M N) {x : M} {y : M} (h : x = y) :
    coe_fn f x = coe_fn f y :=
  congr_arg (fun (x : M) => coe_fn f x) h

theorem one_hom.coe_inj {M : Type u_1} {N : Type u_2} [HasOne M] [HasOne N] {f : one_hom M N}
    {g : one_hom M N} (h : ⇑f = ⇑g) : f = g :=
  sorry

theorem mul_hom.coe_inj {M : Type u_1} {N : Type u_2} [Mul M] [Mul N] {f : mul_hom M N}
    {g : mul_hom M N} (h : ⇑f = ⇑g) : f = g :=
  sorry

theorem add_monoid_hom.coe_inj {M : Type u_1} {N : Type u_2} [add_monoid M] [add_monoid N]
    {f : M →+ N} {g : M →+ N} (h : ⇑f = ⇑g) : f = g :=
  sorry

theorem monoid_with_zero_hom.coe_inj {M : Type u_1} {N : Type u_2} [monoid_with_zero M]
    [monoid_with_zero N] {f : monoid_with_zero_hom M N} {g : monoid_with_zero_hom M N}
    (h : ⇑f = ⇑g) : f = g :=
  sorry

theorem zero_hom.ext {M : Type u_1} {N : Type u_2} [HasZero M] [HasZero N] {f : zero_hom M N}
    {g : zero_hom M N} (h : ∀ (x : M), coe_fn f x = coe_fn g x) : f = g :=
  zero_hom.coe_inj (funext h)

theorem mul_hom.ext {M : Type u_1} {N : Type u_2} [Mul M] [Mul N] {f : mul_hom M N}
    {g : mul_hom M N} (h : ∀ (x : M), coe_fn f x = coe_fn g x) : f = g :=
  mul_hom.coe_inj (funext h)

theorem add_monoid_hom.ext {M : Type u_1} {N : Type u_2} [add_monoid M] [add_monoid N] {f : M →+ N}
    {g : M →+ N} (h : ∀ (x : M), coe_fn f x = coe_fn g x) : f = g :=
  add_monoid_hom.coe_inj (funext h)

theorem monoid_with_zero_hom.ext {M : Type u_1} {N : Type u_2} [monoid_with_zero M]
    [monoid_with_zero N] {f : monoid_with_zero_hom M N} {g : monoid_with_zero_hom M N}
    (h : ∀ (x : M), coe_fn f x = coe_fn g x) : f = g :=
  monoid_with_zero_hom.coe_inj (funext h)

theorem zero_hom.ext_iff {M : Type u_1} {N : Type u_2} [HasZero M] [HasZero N] {f : zero_hom M N}
    {g : zero_hom M N} : f = g ↔ ∀ (x : M), coe_fn f x = coe_fn g x :=
  { mp := fun (h : f = g) (x : M) => h ▸ rfl,
    mpr := fun (h : ∀ (x : M), coe_fn f x = coe_fn g x) => zero_hom.ext h }

theorem mul_hom.ext_iff {M : Type u_1} {N : Type u_2} [Mul M] [Mul N] {f : mul_hom M N}
    {g : mul_hom M N} : f = g ↔ ∀ (x : M), coe_fn f x = coe_fn g x :=
  { mp := fun (h : f = g) (x : M) => h ▸ rfl,
    mpr := fun (h : ∀ (x : M), coe_fn f x = coe_fn g x) => mul_hom.ext h }

theorem add_monoid_hom.ext_iff {M : Type u_1} {N : Type u_2} [add_monoid M] [add_monoid N]
    {f : M →+ N} {g : M →+ N} : f = g ↔ ∀ (x : M), coe_fn f x = coe_fn g x :=
  { mp := fun (h : f = g) (x : M) => h ▸ rfl,
    mpr := fun (h : ∀ (x : M), coe_fn f x = coe_fn g x) => add_monoid_hom.ext h }

theorem monoid_with_zero_hom.ext_iff {M : Type u_1} {N : Type u_2} [monoid_with_zero M]
    [monoid_with_zero N] {f : monoid_with_zero_hom M N} {g : monoid_with_zero_hom M N} :
    f = g ↔ ∀ (x : M), coe_fn f x = coe_fn g x :=
  { mp := fun (h : f = g) (x : M) => h ▸ rfl,
    mpr := fun (h : ∀ (x : M), coe_fn f x = coe_fn g x) => monoid_with_zero_hom.ext h }

@[simp] theorem zero_hom.mk_coe {M : Type u_1} {N : Type u_2} [HasZero M] [HasZero N]
    (f : zero_hom M N) (h1 : coe_fn f 0 = 0) : zero_hom.mk (⇑f) h1 = f :=
  zero_hom.ext fun (_x : M) => rfl

@[simp] theorem mul_hom.mk_coe {M : Type u_1} {N : Type u_2} [Mul M] [Mul N] (f : mul_hom M N)
    (hmul : ∀ (x y : M), coe_fn f (x * y) = coe_fn f x * coe_fn f y) : mul_hom.mk (⇑f) hmul = f :=
  mul_hom.ext fun (_x : M) => rfl

@[simp] theorem add_monoid_hom.mk_coe {M : Type u_1} {N : Type u_2} [add_monoid M] [add_monoid N]
    (f : M →+ N) (h1 : coe_fn f 0 = 0)
    (hmul : ∀ (x y : M), coe_fn f (x + y) = coe_fn f x + coe_fn f y) :
    add_monoid_hom.mk (⇑f) h1 hmul = f :=
  add_monoid_hom.ext fun (_x : M) => rfl

@[simp] theorem monoid_with_zero_hom.mk_coe {M : Type u_1} {N : Type u_2} [monoid_with_zero M]
    [monoid_with_zero N] (f : monoid_with_zero_hom M N) (h0 : coe_fn f 0 = 0) (h1 : coe_fn f 1 = 1)
    (hmul : ∀ (x y : M), coe_fn f (x * y) = coe_fn f x * coe_fn f y) :
    monoid_with_zero_hom.mk (⇑f) h0 h1 hmul = f :=
  monoid_with_zero_hom.ext fun (_x : M) => rfl

/-- If `f` is a monoid homomorphism then `f 1 = 1`. -/
@[simp] theorem one_hom.map_one {M : Type u_1} {N : Type u_2} [HasOne M] [HasOne N]
    (f : one_hom M N) : coe_fn f 1 = 1 :=
  one_hom.map_one' f

@[simp] theorem monoid_hom.map_one {M : Type u_1} {N : Type u_2} [monoid M] [monoid N]
    (f : M →* N) : coe_fn f 1 = 1 :=
  monoid_hom.map_one' f

@[simp] theorem monoid_with_zero_hom.map_one {M : Type u_1} {N : Type u_2} [monoid_with_zero M]
    [monoid_with_zero N] (f : monoid_with_zero_hom M N) : coe_fn f 1 = 1 :=
  monoid_with_zero_hom.map_one' f

/-- If `f` is an additive monoid homomorphism then `f 0 = 0`. -/
@[simp] theorem monoid_with_zero_hom.map_zero {M : Type u_1} {N : Type u_2} [monoid_with_zero M]
    [monoid_with_zero N] (f : monoid_with_zero_hom M N) : coe_fn f 0 = 0 :=
  monoid_with_zero_hom.map_zero' f

@[simp] theorem mul_hom.map_mul {M : Type u_1} {N : Type u_2} [Mul M] [Mul N] (f : mul_hom M N)
    (a : M) (b : M) : coe_fn f (a * b) = coe_fn f a * coe_fn f b :=
  mul_hom.map_mul' f a b

/-- If `f` is a monoid homomorphism then `f (a * b) = f a * f b`. -/
@[simp] theorem add_monoid_hom.map_add {M : Type u_1} {N : Type u_2} [add_monoid M] [add_monoid N]
    (f : M →+ N) (a : M) (b : M) : coe_fn f (a + b) = coe_fn f a + coe_fn f b :=
  add_monoid_hom.map_add' f a b

@[simp] theorem monoid_with_zero_hom.map_mul {M : Type u_1} {N : Type u_2} [monoid_with_zero M]
    [monoid_with_zero N] (f : monoid_with_zero_hom M N) (a : M) (b : M) :
    coe_fn f (a * b) = coe_fn f a * coe_fn f b :=
  monoid_with_zero_hom.map_mul' f a b

/-- If `f` is an additive monoid homomorphism then `f (a + b) = f a + f b`. -/
namespace monoid_hom


theorem Mathlib.add_monoid_hom.map_add_eq_zero {M : Type u_1} {N : Type u_2} {mM : add_monoid M}
    {mN : add_monoid N} (f : M →+ N) {a : M} {b : M} (h : a + b = 0) :
    coe_fn f a + coe_fn f b = 0 :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (coe_fn f a + coe_fn f b = 0)) (Eq.symm (add_monoid_hom.map_add f a b))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn f (a + b) = 0)) h))
      (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn f 0 = 0)) (add_monoid_hom.map_zero f))) (Eq.refl 0)))

/-- Given a monoid homomorphism `f : M →* N` and an element `x : M`, if `x` has a right inverse,
then `f x` has a right inverse too. For elements invertible on both sides see `is_unit.map`. -/
theorem Mathlib.add_monoid_hom.map_exists_right_neg {M : Type u_1} {N : Type u_2}
    {mM : add_monoid M} {mN : add_monoid N} (f : M →+ N) {x : M} (hx : ∃ (y : M), x + y = 0) :
    ∃ (y : N), coe_fn f x + y = 0 :=
  sorry

/-- Given a monoid homomorphism `f : M →* N` and an element `x : M`, if `x` has a left inverse,
then `f x` has a left inverse too. For elements invertible on both sides see `is_unit.map`. -/
theorem Mathlib.add_monoid_hom.map_exists_left_neg {M : Type u_1} {N : Type u_2} {mM : add_monoid M}
    {mN : add_monoid N} (f : M →+ N) {x : M} (hx : ∃ (y : M), y + x = 0) :
    ∃ (y : N), y + coe_fn f x = 0 :=
  sorry

end monoid_hom


/-- The identity map from a type with 1 to itself. -/
def one_hom.id (M : Type u_1) [HasOne M] : one_hom M M := one_hom.mk id sorry

/-- The identity map from a type with multiplication to itself. -/
def add_hom.id (M : Type u_1) [Add M] : add_hom M M := add_hom.mk id sorry

/-- The identity map from a monoid to itself. -/
def add_monoid_hom.id (M : Type u_1) [add_monoid M] : M →+ M := add_monoid_hom.mk id sorry sorry

/-- The identity map from a monoid_with_zero to itself. -/
def monoid_with_zero_hom.id (M : Type u_1) [monoid_with_zero M] : monoid_with_zero_hom M M :=
  monoid_with_zero_hom.mk id sorry sorry sorry

/-- The identity map from an type with zero to itself. -/
/-- The identity map from an type with addition to itself. -/
/-- The identity map from an additive monoid to itself. -/
@[simp] theorem zero_hom.id_apply {M : Type u_1} [HasZero M] (x : M) :
    coe_fn (zero_hom.id M) x = x :=
  rfl

@[simp] theorem mul_hom.id_apply {M : Type u_1} [Mul M] (x : M) : coe_fn (mul_hom.id M) x = x := rfl

@[simp] theorem monoid_hom.id_apply {M : Type u_1} [monoid M] (x : M) :
    coe_fn (monoid_hom.id M) x = x :=
  rfl

@[simp] theorem monoid_with_zero_hom.id_apply {M : Type u_1} [monoid_with_zero M] (x : M) :
    coe_fn (monoid_with_zero_hom.id M) x = x :=
  rfl

/-- Composition of `one_hom`s as a `one_hom`. -/
def zero_hom.comp {M : Type u_1} {N : Type u_2} {P : Type u_3} [HasZero M] [HasZero N] [HasZero P]
    (hnp : zero_hom N P) (hmn : zero_hom M N) : zero_hom M P :=
  zero_hom.mk (⇑hnp ∘ ⇑hmn) sorry

/-- Composition of `mul_hom`s as a `mul_hom`. -/
def mul_hom.comp {M : Type u_1} {N : Type u_2} {P : Type u_3} [Mul M] [Mul N] [Mul P]
    (hnp : mul_hom N P) (hmn : mul_hom M N) : mul_hom M P :=
  mul_hom.mk (⇑hnp ∘ ⇑hmn) sorry

/-- Composition of monoid morphisms as a monoid morphism. -/
def monoid_hom.comp {M : Type u_1} {N : Type u_2} {P : Type u_3} [monoid M] [monoid N] [monoid P]
    (hnp : N →* P) (hmn : M →* N) : M →* P :=
  monoid_hom.mk (⇑hnp ∘ ⇑hmn) sorry sorry

/-- Composition of `monoid_with_zero_hom`s as a `monoid_with_zero_hom`. -/
def monoid_with_zero_hom.comp {M : Type u_1} {N : Type u_2} {P : Type u_3} [monoid_with_zero M]
    [monoid_with_zero N] [monoid_with_zero P] (hnp : monoid_with_zero_hom N P)
    (hmn : monoid_with_zero_hom M N) : monoid_with_zero_hom M P :=
  monoid_with_zero_hom.mk (⇑hnp ∘ ⇑hmn) sorry sorry sorry

/-- Composition of `zero_hom`s as a `zero_hom`. -/
/-- Composition of `add_hom`s as a `add_hom`. -/
/-- Composition of additive monoid morphisms as an additive monoid morphism. -/
@[simp] theorem one_hom.coe_comp {M : Type u_1} {N : Type u_2} {P : Type u_3} [HasOne M] [HasOne N]
    [HasOne P] (g : one_hom N P) (f : one_hom M N) : ⇑(one_hom.comp g f) = ⇑g ∘ ⇑f :=
  rfl

@[simp] theorem add_hom.coe_comp {M : Type u_1} {N : Type u_2} {P : Type u_3} [Add M] [Add N]
    [Add P] (g : add_hom N P) (f : add_hom M N) : ⇑(add_hom.comp g f) = ⇑g ∘ ⇑f :=
  rfl

@[simp] theorem add_monoid_hom.coe_comp {M : Type u_1} {N : Type u_2} {P : Type u_3} [add_monoid M]
    [add_monoid N] [add_monoid P] (g : N →+ P) (f : M →+ N) :
    ⇑(add_monoid_hom.comp g f) = ⇑g ∘ ⇑f :=
  rfl

@[simp] theorem monoid_with_zero_hom.coe_comp {M : Type u_1} {N : Type u_2} {P : Type u_3}
    [monoid_with_zero M] [monoid_with_zero N] [monoid_with_zero P] (g : monoid_with_zero_hom N P)
    (f : monoid_with_zero_hom M N) : ⇑(monoid_with_zero_hom.comp g f) = ⇑g ∘ ⇑f :=
  rfl

theorem one_hom.comp_apply {M : Type u_1} {N : Type u_2} {P : Type u_3} [HasOne M] [HasOne N]
    [HasOne P] (g : one_hom N P) (f : one_hom M N) (x : M) :
    coe_fn (one_hom.comp g f) x = coe_fn g (coe_fn f x) :=
  rfl

theorem add_hom.comp_apply {M : Type u_1} {N : Type u_2} {P : Type u_3} [Add M] [Add N] [Add P]
    (g : add_hom N P) (f : add_hom M N) (x : M) :
    coe_fn (add_hom.comp g f) x = coe_fn g (coe_fn f x) :=
  rfl

theorem monoid_hom.comp_apply {M : Type u_1} {N : Type u_2} {P : Type u_3} [monoid M] [monoid N]
    [monoid P] (g : N →* P) (f : M →* N) (x : M) :
    coe_fn (monoid_hom.comp g f) x = coe_fn g (coe_fn f x) :=
  rfl

theorem monoid_with_zero_hom.comp_apply {M : Type u_1} {N : Type u_2} {P : Type u_3}
    [monoid_with_zero M] [monoid_with_zero N] [monoid_with_zero P] (g : monoid_with_zero_hom N P)
    (f : monoid_with_zero_hom M N) (x : M) :
    coe_fn (monoid_with_zero_hom.comp g f) x = coe_fn g (coe_fn f x) :=
  rfl

/-- Composition of monoid homomorphisms is associative. -/
theorem zero_hom.comp_assoc {M : Type u_1} {N : Type u_2} {P : Type u_3} {Q : Type u_4} [HasZero M]
    [HasZero N] [HasZero P] [HasZero Q] (f : zero_hom M N) (g : zero_hom N P) (h : zero_hom P Q) :
    zero_hom.comp (zero_hom.comp h g) f = zero_hom.comp h (zero_hom.comp g f) :=
  rfl

theorem mul_hom.comp_assoc {M : Type u_1} {N : Type u_2} {P : Type u_3} {Q : Type u_4} [Mul M]
    [Mul N] [Mul P] [Mul Q] (f : mul_hom M N) (g : mul_hom N P) (h : mul_hom P Q) :
    mul_hom.comp (mul_hom.comp h g) f = mul_hom.comp h (mul_hom.comp g f) :=
  rfl

theorem add_monoid_hom.comp_assoc {M : Type u_1} {N : Type u_2} {P : Type u_3} {Q : Type u_4}
    [add_monoid M] [add_monoid N] [add_monoid P] [add_monoid Q] (f : M →+ N) (g : N →+ P)
    (h : P →+ Q) :
    add_monoid_hom.comp (add_monoid_hom.comp h g) f =
        add_monoid_hom.comp h (add_monoid_hom.comp g f) :=
  rfl

theorem monoid_with_zero_hom.comp_assoc {M : Type u_1} {N : Type u_2} {P : Type u_3} {Q : Type u_4}
    [monoid_with_zero M] [monoid_with_zero N] [monoid_with_zero P] [monoid_with_zero Q]
    (f : monoid_with_zero_hom M N) (g : monoid_with_zero_hom N P) (h : monoid_with_zero_hom P Q) :
    monoid_with_zero_hom.comp (monoid_with_zero_hom.comp h g) f =
        monoid_with_zero_hom.comp h (monoid_with_zero_hom.comp g f) :=
  rfl

theorem one_hom.cancel_right {M : Type u_1} {N : Type u_2} {P : Type u_3} [HasOne M] [HasOne N]
    [HasOne P] {g₁ : one_hom N P} {g₂ : one_hom N P} {f : one_hom M N}
    (hf : function.surjective ⇑f) : one_hom.comp g₁ f = one_hom.comp g₂ f ↔ g₁ = g₂ :=
  sorry

theorem add_hom.cancel_right {M : Type u_1} {N : Type u_2} {P : Type u_3} [Add M] [Add N] [Add P]
    {g₁ : add_hom N P} {g₂ : add_hom N P} {f : add_hom M N} (hf : function.surjective ⇑f) :
    add_hom.comp g₁ f = add_hom.comp g₂ f ↔ g₁ = g₂ :=
  sorry

theorem add_monoid_hom.cancel_right {M : Type u_1} {N : Type u_2} {P : Type u_3} [add_monoid M]
    [add_monoid N] [add_monoid P] {g₁ : N →+ P} {g₂ : N →+ P} {f : M →+ N}
    (hf : function.surjective ⇑f) : add_monoid_hom.comp g₁ f = add_monoid_hom.comp g₂ f ↔ g₁ = g₂ :=
  sorry

theorem monoid_with_zero_hom.cancel_right {M : Type u_1} {N : Type u_2} {P : Type u_3}
    [monoid_with_zero M] [monoid_with_zero N] [monoid_with_zero P] {g₁ : monoid_with_zero_hom N P}
    {g₂ : monoid_with_zero_hom N P} {f : monoid_with_zero_hom M N} (hf : function.surjective ⇑f) :
    monoid_with_zero_hom.comp g₁ f = monoid_with_zero_hom.comp g₂ f ↔ g₁ = g₂ :=
  sorry

theorem one_hom.cancel_left {M : Type u_1} {N : Type u_2} {P : Type u_3} [HasOne M] [HasOne N]
    [HasOne P] {g : one_hom N P} {f₁ : one_hom M N} {f₂ : one_hom M N}
    (hg : function.injective ⇑g) : one_hom.comp g f₁ = one_hom.comp g f₂ ↔ f₁ = f₂ :=
  sorry

theorem add_hom.cancel_left {M : Type u_1} {N : Type u_2} {P : Type u_3} [HasZero M] [HasZero N]
    [HasZero P] {g : zero_hom N P} {f₁ : zero_hom M N} {f₂ : zero_hom M N}
    (hg : function.injective ⇑g) : zero_hom.comp g f₁ = zero_hom.comp g f₂ ↔ f₁ = f₂ :=
  sorry

theorem monoid_hom.cancel_left {M : Type u_1} {N : Type u_2} {P : Type u_3} [monoid M] [monoid N]
    [monoid P] {g : N →* P} {f₁ : M →* N} {f₂ : M →* N} (hg : function.injective ⇑g) :
    monoid_hom.comp g f₁ = monoid_hom.comp g f₂ ↔ f₁ = f₂ :=
  sorry

theorem monoid_with_zero_hom.cancel_left {M : Type u_1} {N : Type u_2} {P : Type u_3}
    [monoid_with_zero M] [monoid_with_zero N] [monoid_with_zero P] {g : monoid_with_zero_hom N P}
    {f₁ : monoid_with_zero_hom M N} {f₂ : monoid_with_zero_hom M N} (hg : function.injective ⇑g) :
    monoid_with_zero_hom.comp g f₁ = monoid_with_zero_hom.comp g f₂ ↔ f₁ = f₂ :=
  sorry

@[simp] theorem one_hom.comp_id {M : Type u_1} {N : Type u_2} [HasOne M] [HasOne N]
    (f : one_hom M N) : one_hom.comp f (one_hom.id M) = f :=
  one_hom.ext fun (x : M) => rfl

@[simp] theorem mul_hom.comp_id {M : Type u_1} {N : Type u_2} [Mul M] [Mul N] (f : mul_hom M N) :
    mul_hom.comp f (mul_hom.id M) = f :=
  mul_hom.ext fun (x : M) => rfl

@[simp] theorem add_monoid_hom.comp_id {M : Type u_1} {N : Type u_2} [add_monoid M] [add_monoid N]
    (f : M →+ N) : add_monoid_hom.comp f (add_monoid_hom.id M) = f :=
  add_monoid_hom.ext fun (x : M) => rfl

@[simp] theorem monoid_with_zero_hom.comp_id {M : Type u_1} {N : Type u_2} [monoid_with_zero M]
    [monoid_with_zero N] (f : monoid_with_zero_hom M N) :
    monoid_with_zero_hom.comp f (monoid_with_zero_hom.id M) = f :=
  monoid_with_zero_hom.ext fun (x : M) => rfl

@[simp] theorem zero_hom.id_comp {M : Type u_1} {N : Type u_2} [HasZero M] [HasZero N]
    (f : zero_hom M N) : zero_hom.comp (zero_hom.id N) f = f :=
  zero_hom.ext fun (x : M) => rfl

@[simp] theorem mul_hom.id_comp {M : Type u_1} {N : Type u_2} [Mul M] [Mul N] (f : mul_hom M N) :
    mul_hom.comp (mul_hom.id N) f = f :=
  mul_hom.ext fun (x : M) => rfl

@[simp] theorem monoid_hom.id_comp {M : Type u_1} {N : Type u_2} [monoid M] [monoid N]
    (f : M →* N) : monoid_hom.comp (monoid_hom.id N) f = f :=
  monoid_hom.ext fun (x : M) => rfl

@[simp] theorem monoid_with_zero_hom.id_comp {M : Type u_1} {N : Type u_2} [monoid_with_zero M]
    [monoid_with_zero N] (f : monoid_with_zero_hom M N) :
    monoid_with_zero_hom.comp (monoid_with_zero_hom.id N) f = f :=
  monoid_with_zero_hom.ext fun (x : M) => rfl

namespace monoid


/-- The monoid of endomorphisms. -/
protected def End (M : Type u_1) [monoid M] := M →* M

namespace End


protected instance monoid (M : Type u_1) [monoid M] : monoid (monoid.End M) :=
  mk monoid_hom.comp sorry (monoid_hom.id M) monoid_hom.id_comp monoid_hom.comp_id

protected instance inhabited (M : Type u_1) [monoid M] : Inhabited (monoid.End M) :=
  { default := 1 }

protected instance has_coe_to_fun (M : Type u_1) [monoid M] : has_coe_to_fun (monoid.End M) :=
  has_coe_to_fun.mk (fun (x : monoid.End M) => M → M) monoid_hom.to_fun

end End


@[simp] theorem coe_one (M : Type u_1) [monoid M] : ⇑1 = id := rfl

@[simp] theorem coe_mul (M : Type u_1) [monoid M] (f : monoid.End M) (g : monoid.End M) :
    ⇑(f * g) = ⇑f ∘ ⇑g :=
  rfl

end monoid


namespace add_monoid


/-- The monoid of endomorphisms. -/
protected def End (A : Type u_6) [add_monoid A] := A →+ A

namespace End


protected instance monoid (A : Type u_6) [add_monoid A] : monoid (add_monoid.End A) :=
  monoid.mk add_monoid_hom.comp sorry (add_monoid_hom.id A) add_monoid_hom.id_comp
    add_monoid_hom.comp_id

protected instance inhabited (A : Type u_6) [add_monoid A] : Inhabited (add_monoid.End A) :=
  { default := 1 }

protected instance has_coe_to_fun (A : Type u_6) [add_monoid A] :
    has_coe_to_fun (add_monoid.End A) :=
  has_coe_to_fun.mk (fun (x : add_monoid.End A) => A → A) add_monoid_hom.to_fun

end End


@[simp] theorem coe_one (A : Type u_6) [add_monoid A] : ⇑1 = id := rfl

@[simp] theorem coe_mul (A : Type u_6) [add_monoid A] (f : add_monoid.End A)
    (g : add_monoid.End A) : ⇑(f * g) = ⇑f ∘ ⇑g :=
  rfl

end add_monoid


/-- `1` is the homomorphism sending all elements to `1`. -/
/-- `1` is the multiplicative homomorphism sending all elements to `1`. -/
protected instance zero_hom.has_zero {M : Type u_1} {N : Type u_2} [HasZero M] [HasZero N] :
    HasZero (zero_hom M N) :=
  { zero := zero_hom.mk (fun (_x : M) => 0) sorry }

/-- `1` is the monoid homomorphism sending all elements to `1`. -/
protected instance add_hom.has_zero {M : Type u_1} {N : Type u_2} [Add M] [add_monoid N] :
    HasZero (add_hom M N) :=
  { zero := add_hom.mk (fun (_x : M) => 0) sorry }

protected instance add_monoid_hom.has_zero {M : Type u_1} {N : Type u_2} [add_monoid M]
    [add_monoid N] : HasZero (M →+ N) :=
  { zero := add_monoid_hom.mk (fun (_x : M) => 0) sorry sorry }

/-- `0` is the homomorphism sending all elements to `0`. -/
/-- `0` is the additive homomorphism sending all elements to `0`. -/
/-- `0` is the additive monoid homomorphism sending all elements to `0`. -/
@[simp] theorem one_hom.one_apply {M : Type u_1} {N : Type u_2} [HasOne M] [HasOne N] (x : M) :
    coe_fn 1 x = 1 :=
  rfl

@[simp] theorem add_monoid_hom.zero_apply {M : Type u_1} {N : Type u_2} [add_monoid M]
    [add_monoid N] (x : M) : coe_fn 0 x = 0 :=
  rfl

@[simp] theorem zero_hom.zero_comp {M : Type u_1} {N : Type u_2} {P : Type u_3} [HasZero M]
    [HasZero N] [HasZero P] (f : zero_hom M N) : zero_hom.comp 0 f = 0 :=
  rfl

@[simp] theorem zero_hom.comp_zero {M : Type u_1} {N : Type u_2} {P : Type u_3} [HasZero M]
    [HasZero N] [HasZero P] (f : zero_hom N P) : zero_hom.comp f 0 = 0 :=
  sorry

protected instance one_hom.inhabited {M : Type u_1} {N : Type u_2} [HasOne M] [HasOne N] :
    Inhabited (one_hom M N) :=
  { default := 1 }

protected instance add_hom.inhabited {M : Type u_1} {N : Type u_2} [Add M] [add_monoid N] :
    Inhabited (add_hom M N) :=
  { default := 0 }

-- unlike the other homs, `monoid_with_zero_hom` does not have a `1` or `0`

protected instance add_monoid_hom.inhabited {M : Type u_1} {N : Type u_2} [add_monoid M]
    [add_monoid N] : Inhabited (M →+ N) :=
  { default := 0 }

protected instance monoid_with_zero_hom.inhabited {M : Type u_1} [monoid_with_zero M] :
    Inhabited (monoid_with_zero_hom M M) :=
  { default := monoid_with_zero_hom.id M }

namespace monoid_hom


/-- Given two monoid morphisms `f`, `g` to a commutative monoid, `f * g` is the monoid morphism
sending `x` to `f x * g x`. -/
protected instance has_mul {M : Type u_1} {N : Type u_2} {mM : monoid M} [comm_monoid N] :
    Mul (M →* N) :=
  { mul := fun (f g : M →* N) => mk (fun (m : M) => coe_fn f m * coe_fn g m) sorry sorry }

/-- Given two additive monoid morphisms `f`, `g` to an additive commutative monoid, `f + g` is the
additive monoid morphism sending `x` to `f x + g x`. -/
@[simp] theorem Mathlib.add_monoid_hom.add_apply {M : Type u_1} {N : Type u_2} {mM : add_monoid M}
    {mN : add_comm_monoid N} (f : M →+ N) (g : M →+ N) (x : M) :
    coe_fn (f + g) x = coe_fn f x + coe_fn g x :=
  rfl

@[simp] theorem one_comp {M : Type u_1} {N : Type u_2} {P : Type u_3} [monoid M] [monoid N]
    [monoid P] (f : M →* N) : comp 1 f = 1 :=
  rfl

@[simp] theorem Mathlib.add_monoid_hom.comp_zero {M : Type u_1} {N : Type u_2} {P : Type u_3}
    [add_monoid M] [add_monoid N] [add_monoid P] (f : N →+ P) : add_monoid_hom.comp f 0 = 0 :=
  sorry

theorem mul_comp {M : Type u_1} {N : Type u_2} {P : Type u_3} [monoid M] [comm_monoid N]
    [comm_monoid P] (g₁ : N →* P) (g₂ : N →* P) (f : M →* N) :
    comp (g₁ * g₂) f = comp g₁ f * comp g₂ f :=
  rfl

theorem comp_mul {M : Type u_1} {N : Type u_2} {P : Type u_3} [monoid M] [comm_monoid N]
    [comm_monoid P] (g : N →* P) (f₁ : M →* N) (f₂ : M →* N) :
    comp g (f₁ * f₂) = comp g f₁ * comp g f₂ :=
  sorry

/-- (M →* N) is a comm_monoid if N is commutative. -/
protected instance comm_monoid {M : Type u_1} {N : Type u_2} [monoid M] [comm_monoid N] :
    comm_monoid (M →* N) :=
  comm_monoid.mk Mul.mul sorry 1 sorry sorry sorry

/-- `flip` arguments of `f : M →* N →* P` -/
def Mathlib.add_monoid_hom.flip {M : Type u_1} {N : Type u_2} {P : Type u_3} {mM : add_monoid M}
    {mN : add_monoid N} {mP : add_comm_monoid P} (f : M →+ N →+ P) : N →+ M →+ P :=
  add_monoid_hom.mk
    (fun (y : N) => add_monoid_hom.mk (fun (x : M) => coe_fn (coe_fn f x) y) sorry sorry) sorry
    sorry

@[simp] theorem flip_apply {M : Type u_1} {N : Type u_2} {P : Type u_3} {mM : monoid M}
    {mN : monoid N} {mP : comm_monoid P} (f : M →* N →* P) (x : M) (y : N) :
    coe_fn (coe_fn (flip f) y) x = coe_fn (coe_fn f x) y :=
  rfl

/-- Evaluation of a `monoid_hom` at a point as a monoid homomorphism. See also `monoid_hom.apply`
for the evaluation of any function at a point. -/
def Mathlib.add_monoid_hom.eval {M : Type u_1} {N : Type u_2} [add_monoid M] [add_comm_monoid N] :
    M →+ (M →+ N) →+ N :=
  add_monoid_hom.flip (add_monoid_hom.id (M →+ N))

@[simp] theorem Mathlib.add_monoid_hom.eval_apply {M : Type u_1} {N : Type u_2} [add_monoid M]
    [add_comm_monoid N] (x : M) (f : M →+ N) :
    coe_fn (coe_fn add_monoid_hom.eval x) f = coe_fn f x :=
  rfl

/-- Composition of monoid morphisms (`monoid_hom.comp`) as a monoid morphism. -/
def Mathlib.add_monoid_hom.comp_hom {M : Type u_1} {N : Type u_2} {P : Type u_3} [add_monoid M]
    [add_comm_monoid N] [add_comm_monoid P] : (N →+ P) →+ (M →+ N) →+ M →+ P :=
  add_monoid_hom.mk
    (fun (g : N →+ P) =>
      add_monoid_hom.mk (add_monoid_hom.comp g) sorry (add_monoid_hom.comp_add g))
    sorry sorry

/-- If two homomorphism from a group to a monoid are equal at `x`, then they are equal at `x⁻¹`. -/
theorem eq_on_inv {M : Type u_1} {G : Type u_2} [group G] [monoid M] {f : G →* M} {g : G →* M}
    {x : G} (h : coe_fn f x = coe_fn g x) : coe_fn f (x⁻¹) = coe_fn g (x⁻¹) :=
  left_inv_eq_right_inv (map_mul_eq_one f (inv_mul_self x))
    (Eq.subst (Eq.symm h) (map_mul_eq_one g) (mul_inv_self x))

/-- Group homomorphisms preserve inverse. -/
@[simp] theorem Mathlib.add_monoid_hom.map_neg {G : Type u_1} {H : Type u_2} [add_group G]
    [add_group H] (f : G →+ H) (g : G) : coe_fn f (-g) = -coe_fn f g :=
  eq_neg_of_add_eq_zero (add_monoid_hom.map_add_eq_zero f (neg_add_self g))

/-- Group homomorphisms preserve division. -/
@[simp] theorem Mathlib.add_monoid_hom.map_add_neg {G : Type u_1} {H : Type u_2} [add_group G]
    [add_group H] (f : G →+ H) (g : G) (h : G) : coe_fn f (g + -h) = coe_fn f g + -coe_fn f h :=
  sorry

/-- A homomorphism from a group to a monoid is injective iff its kernel is trivial. -/
theorem injective_iff {G : Type u_1} {H : Type u_2} [group G] [monoid H] (f : G →* H) :
    function.injective ⇑f ↔ ∀ (a : G), coe_fn f a = 1 → a = 1 :=
  sorry

/-- Makes a group homomorphism from a proof that the map preserves multiplication. -/
def Mathlib.add_monoid_hom.mk' {M : Type u_1} {G : Type u_4} [mM : add_monoid M] [add_group G]
    (f : M → G) (map_mul : ∀ (a b : M), f (a + b) = f a + f b) : M →+ G :=
  add_monoid_hom.mk f sorry map_mul

@[simp] theorem Mathlib.add_monoid_hom.coe_mk' {M : Type u_1} {G : Type u_4} [mM : add_monoid M]
    [add_group G] {f : M → G} (map_mul : ∀ (a b : M), f (a + b) = f a + f b) :
    ⇑(add_monoid_hom.mk' f map_mul) = f :=
  rfl

/-- Makes a group homomorphism from a proof that the map preserves right division `λ x y, x * y⁻¹`.
-/
def of_map_mul_inv {G : Type u_4} [group G] {H : Type u_1} [group H] (f : G → H)
    (map_div : ∀ (a b : G), f (a * (b⁻¹)) = f a * (f b⁻¹)) : G →* H :=
  mk' f sorry

@[simp] theorem Mathlib.add_monoid_hom.coe_of_map_add_neg {G : Type u_4} [add_group G]
    {H : Type u_1} [add_group H] (f : G → H) (map_div : ∀ (a b : G), f (a + -b) = f a + -f b) :
    ⇑(add_monoid_hom.of_map_add_neg f map_div) = f :=
  rfl

/-- If `f` is a monoid homomorphism to a commutative group, then `f⁻¹` is the homomorphism sending
`x` to `(f x)⁻¹`. -/
protected instance Mathlib.add_monoid_hom.has_neg {M : Type u_1} {G : Type u_2} [add_monoid M]
    [add_comm_group G] : Neg (M →+ G) :=
  { neg := fun (f : M →+ G) => add_monoid_hom.mk' (fun (g : M) => -coe_fn f g) sorry }

/-- If `f` is an additive monoid homomorphism to an additive commutative group, then `-f` is the
homomorphism sending `x` to `-(f x)`. -/
@[simp] theorem inv_apply {M : Type u_1} {G : Type u_2} {mM : monoid M} {gG : comm_group G}
    (f : M →* G) (x : M) : coe_fn (f⁻¹) x = (coe_fn f x⁻¹) :=
  rfl

/-- If `f` and `g` are monoid homomorphisms to a commutative group, then `f / g` is the homomorphism
sending `x` to `(f x) / (g x). -/
protected instance has_div {M : Type u_1} {G : Type u_2} [monoid M] [comm_group G] : Div (M →* G) :=
  { div := fun (f g : M →* G) => mk' (fun (x : M) => coe_fn f x / coe_fn g x) sorry }

/-- If `f` and `g` are monoid homomorphisms to an additive commutative group, then `f - g`
is the homomorphism sending `x` to `(f x) - (g x). -/
@[simp] theorem Mathlib.add_monoid_hom.sub_apply {M : Type u_1} {G : Type u_2} {mM : add_monoid M}
    {gG : add_comm_group G} (f : M →+ G) (g : M →+ G) (x : M) :
    coe_fn (f - g) x = coe_fn f x - coe_fn g x :=
  rfl

/-- If `G` is a commutative group, then `M →* G` a commutative group too. -/
protected instance Mathlib.add_monoid_hom.add_comm_group {M : Type u_1} {G : Type u_2}
    [add_monoid M] [add_comm_group G] : add_comm_group (M →+ G) :=
  add_comm_group.mk add_comm_monoid.add sorry add_comm_monoid.zero sorry sorry Neg.neg Sub.sub sorry
    sorry

/-- If `G` is an additive commutative group, then `M →+ G` an additive commutative group too. -/
end monoid_hom


namespace add_monoid_hom


/-- Additive group homomorphisms preserve subtraction. -/
@[simp] theorem map_sub {G : Type u_4} {H : Type u_5} [add_group G] [add_group H] (f : G →+ H)
    (g : G) (h : G) : coe_fn f (g - h) = coe_fn f g - coe_fn f h :=
  sorry

/-- Define a morphism of additive groups given a map which respects difference. -/
def of_map_sub {G : Type u_4} {H : Type u_5} [add_group G] [add_group H] (f : G → H)
    (hf : ∀ (x y : G), f (x - y) = f x - f y) : G →+ H :=
  of_map_add_neg f sorry

@[simp] theorem coe_of_map_sub {G : Type u_4} {H : Type u_5} [add_group G] [add_group H] (f : G → H)
    (hf : ∀ (x y : G), f (x - y) = f x - f y) : ⇑(of_map_sub f hf) = f :=
  rfl

end add_monoid_hom


@[simp] protected theorem add_semiconj_by.map {M : Type u_1} {N : Type u_2} [add_monoid M]
    [add_monoid N] {a : M} {x : M} {y : M} (h : add_semiconj_by a x y) (f : M →+ N) :
    add_semiconj_by (coe_fn f a) (coe_fn f x) (coe_fn f y) :=
  sorry

@[simp] protected theorem add_commute.map {M : Type u_1} {N : Type u_2} [add_monoid M]
    [add_monoid N] {x : M} {y : M} (h : add_commute x y) (f : M →+ N) :
    add_commute (coe_fn f x) (coe_fn f y) :=
  add_semiconj_by.map h f

end Mathlib