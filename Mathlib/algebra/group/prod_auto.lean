/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.group.hom
import Mathlib.data.equiv.mul_add
import Mathlib.data.prod
import Mathlib.PostPort

universes u_5 u_6 u_3 u_4 u_1 u_2 u_7 u_8 u_9 

namespace Mathlib

/-!
# Monoid, group etc structures on `M × N`

In this file we define one-binop (`monoid`, `group` etc) structures on `M × N`. We also prove
trivial `simp` lemmas, and define the following operations on `monoid_hom`s:

* `fst M N : M × N →* M`, `snd M N : M × N →* N`: projections `prod.fst` and `prod.snd`
  as `monoid_hom`s;
* `inl M N : M →* M × N`, `inr M N : N →* M × N`: inclusions of first/second monoid
  into the product;
* `f.prod g : `M →* N × P`: sends `x` to `(f x, g x)`;
* `f.coprod g : M × N →* P`: sends `(x, y)` to `f x * g y`;
* `f.prod_map g : M × N → M' × N'`: `prod.map f g` as a `monoid_hom`,
  sends `(x, y)` to `(f x, g y)`.
-/

namespace prod


protected instance has_add {M : Type u_5} {N : Type u_6} [Add M] [Add N] : Add (M × N) :=
  { add := fun (p q : M × N) => (fst p + fst q, snd p + snd q) }

@[simp] theorem fst_add {M : Type u_5} {N : Type u_6} [Add M] [Add N] (p : M × N) (q : M × N) :
    fst (p + q) = fst p + fst q :=
  rfl

@[simp] theorem snd_add {M : Type u_5} {N : Type u_6} [Add M] [Add N] (p : M × N) (q : M × N) :
    snd (p + q) = snd p + snd q :=
  rfl

@[simp] theorem mk_add_mk {M : Type u_5} {N : Type u_6} [Add M] [Add N] (a₁ : M) (a₂ : M) (b₁ : N)
    (b₂ : N) : (a₁, b₁) + (a₂, b₂) = (a₁ + a₂, b₁ + b₂) :=
  rfl

protected instance has_one {M : Type u_5} {N : Type u_6} [HasOne M] [HasOne N] : HasOne (M × N) :=
  { one := (1, 1) }

@[simp] theorem fst_zero {M : Type u_5} {N : Type u_6} [HasZero M] [HasZero N] : fst 0 = 0 := rfl

@[simp] theorem snd_one {M : Type u_5} {N : Type u_6} [HasOne M] [HasOne N] : snd 1 = 1 := rfl

theorem zero_eq_mk {M : Type u_5} {N : Type u_6} [HasZero M] [HasZero N] : 0 = (0, 0) := rfl

@[simp] theorem mk_eq_zero {M : Type u_5} {N : Type u_6} [HasZero M] [HasZero N] {x : M} {y : N} :
    (x, y) = 0 ↔ x = 0 ∧ y = 0 :=
  mk.inj_iff

theorem fst_mul_snd {M : Type u_5} {N : Type u_6} [monoid M] [monoid N] (p : M × N) :
    (fst p, 1) * (1, snd p) = p :=
  ext (mul_one (fst p)) (one_mul (snd p))

protected instance has_inv {M : Type u_5} {N : Type u_6} [has_inv M] [has_inv N] :
    has_inv (M × N) :=
  has_inv.mk fun (p : M × N) => (fst p⁻¹, snd p⁻¹)

@[simp] theorem fst_inv {G : Type u_3} {H : Type u_4} [has_inv G] [has_inv H] (p : G × H) :
    fst (p⁻¹) = (fst p⁻¹) :=
  rfl

@[simp] theorem snd_neg {G : Type u_3} {H : Type u_4} [Neg G] [Neg H] (p : G × H) :
    snd (-p) = -snd p :=
  rfl

@[simp] theorem inv_mk {G : Type u_3} {H : Type u_4} [has_inv G] [has_inv H] (a : G) (b : H) :
    (a, b)⁻¹ = (a⁻¹, b⁻¹) :=
  rfl

protected instance has_sub {M : Type u_5} {N : Type u_6} [Sub M] [Sub N] : Sub (M × N) :=
  { sub := fun (p q : M × N) => (fst p - fst q, snd p - snd q) }

@[simp] theorem fst_sub {A : Type u_1} {B : Type u_2} [add_group A] [add_group B] (a : A × B)
    (b : A × B) : fst (a - b) = fst a - fst b :=
  rfl

@[simp] theorem snd_sub {A : Type u_1} {B : Type u_2} [add_group A] [add_group B] (a : A × B)
    (b : A × B) : snd (a - b) = snd a - snd b :=
  rfl

@[simp] theorem mk_sub_mk {A : Type u_1} {B : Type u_2} [add_group A] [add_group B] (x₁ : A)
    (x₂ : A) (y₁ : B) (y₂ : B) : (x₁, y₁) - (x₂, y₂) = (x₁ - x₂, y₁ - y₂) :=
  rfl

protected instance semigroup {M : Type u_5} {N : Type u_6} [semigroup M] [semigroup N] :
    semigroup (M × N) :=
  semigroup.mk Mul.mul sorry

protected instance add_monoid {M : Type u_5} {N : Type u_6} [add_monoid M] [add_monoid N] :
    add_monoid (M × N) :=
  add_monoid.mk add_semigroup.add sorry 0 sorry sorry

protected instance group {G : Type u_3} {H : Type u_4} [group G] [group H] : group (G × H) :=
  group.mk monoid.mul sorry monoid.one sorry sorry has_inv.inv Div.div sorry

protected instance add_comm_semigroup {G : Type u_3} {H : Type u_4} [add_comm_semigroup G]
    [add_comm_semigroup H] : add_comm_semigroup (G × H) :=
  add_comm_semigroup.mk add_semigroup.add sorry sorry

protected instance left_cancel_semigroup {G : Type u_3} {H : Type u_4} [left_cancel_semigroup G]
    [left_cancel_semigroup H] : left_cancel_semigroup (G × H) :=
  left_cancel_semigroup.mk semigroup.mul sorry sorry

protected instance right_cancel_semigroup {G : Type u_3} {H : Type u_4} [right_cancel_semigroup G]
    [right_cancel_semigroup H] : right_cancel_semigroup (G × H) :=
  right_cancel_semigroup.mk semigroup.mul sorry sorry

protected instance add_comm_monoid {M : Type u_5} {N : Type u_6} [add_comm_monoid M]
    [add_comm_monoid N] : add_comm_monoid (M × N) :=
  add_comm_monoid.mk add_comm_semigroup.add sorry add_monoid.zero sorry sorry sorry

protected instance comm_group {G : Type u_3} {H : Type u_4} [comm_group G] [comm_group H] :
    comm_group (G × H) :=
  comm_group.mk comm_semigroup.mul sorry group.one sorry sorry group.inv group.div sorry sorry

end prod


namespace monoid_hom


/-- Given monoids `M`, `N`, the natural projection homomorphism from `M × N` to `M`.-/
def fst (M : Type u_5) (N : Type u_6) [monoid M] [monoid N] : M × N →* M := mk prod.fst sorry sorry

/-- Given monoids `M`, `N`, the natural projection homomorphism from `M × N` to `N`.-/
def Mathlib.add_monoid_hom.snd (M : Type u_5) (N : Type u_6) [add_monoid M] [add_monoid N] :
    M × N →+ N :=
  add_monoid_hom.mk prod.snd sorry sorry

/-- Given monoids `M`, `N`, the natural inclusion homomorphism from `M` to `M × N`. -/
def Mathlib.add_monoid_hom.inl (M : Type u_5) (N : Type u_6) [add_monoid M] [add_monoid N] :
    M →+ M × N :=
  add_monoid_hom.mk (fun (x : M) => (x, 0)) sorry sorry

/-- Given monoids `M`, `N`, the natural inclusion homomorphism from `N` to `M × N`. -/
def Mathlib.add_monoid_hom.inr (M : Type u_5) (N : Type u_6) [add_monoid M] [add_monoid N] :
    N →+ M × N :=
  add_monoid_hom.mk (fun (y : N) => (0, y)) sorry sorry

@[simp] theorem Mathlib.add_monoid_hom.coe_fst {M : Type u_5} {N : Type u_6} [add_monoid M]
    [add_monoid N] : ⇑(add_monoid_hom.fst M N) = prod.fst :=
  rfl

@[simp] theorem Mathlib.add_monoid_hom.coe_snd {M : Type u_5} {N : Type u_6} [add_monoid M]
    [add_monoid N] : ⇑(add_monoid_hom.snd M N) = prod.snd :=
  rfl

@[simp] theorem inl_apply {M : Type u_5} {N : Type u_6} [monoid M] [monoid N] (x : M) :
    coe_fn (inl M N) x = (x, 1) :=
  rfl

@[simp] theorem inr_apply {M : Type u_5} {N : Type u_6} [monoid M] [monoid N] (y : N) :
    coe_fn (inr M N) y = (1, y) :=
  rfl

@[simp] theorem Mathlib.add_monoid_hom.fst_comp_inl {M : Type u_5} {N : Type u_6} [add_monoid M]
    [add_monoid N] :
    add_monoid_hom.comp (add_monoid_hom.fst M N) (add_monoid_hom.inl M N) = add_monoid_hom.id M :=
  rfl

@[simp] theorem Mathlib.add_monoid_hom.snd_comp_inl {M : Type u_5} {N : Type u_6} [add_monoid M]
    [add_monoid N] : add_monoid_hom.comp (add_monoid_hom.snd M N) (add_monoid_hom.inl M N) = 0 :=
  rfl

@[simp] theorem Mathlib.add_monoid_hom.fst_comp_inr {M : Type u_5} {N : Type u_6} [add_monoid M]
    [add_monoid N] : add_monoid_hom.comp (add_monoid_hom.fst M N) (add_monoid_hom.inr M N) = 0 :=
  rfl

@[simp] theorem Mathlib.add_monoid_hom.snd_comp_inr {M : Type u_5} {N : Type u_6} [add_monoid M]
    [add_monoid N] :
    add_monoid_hom.comp (add_monoid_hom.snd M N) (add_monoid_hom.inr M N) = add_monoid_hom.id N :=
  rfl

/-- Combine two `monoid_hom`s `f : M →* N`, `g : M →* P` into `f.prod g : M →* N × P`
given by `(f.prod g) x = (f x, g x)` -/
protected def prod {M : Type u_5} {N : Type u_6} {P : Type u_7} [monoid M] [monoid N] [monoid P]
    (f : M →* N) (g : M →* P) : M →* N × P :=
  mk (fun (x : M) => (coe_fn f x, coe_fn g x)) sorry sorry

@[simp] theorem prod_apply {M : Type u_5} {N : Type u_6} {P : Type u_7} [monoid M] [monoid N]
    [monoid P] (f : M →* N) (g : M →* P) (x : M) :
    coe_fn (monoid_hom.prod f g) x = (coe_fn f x, coe_fn g x) :=
  rfl

@[simp] theorem fst_comp_prod {M : Type u_5} {N : Type u_6} {P : Type u_7} [monoid M] [monoid N]
    [monoid P] (f : M →* N) (g : M →* P) : comp (fst N P) (monoid_hom.prod f g) = f :=
  ext fun (x : M) => rfl

@[simp] theorem snd_comp_prod {M : Type u_5} {N : Type u_6} {P : Type u_7} [monoid M] [monoid N]
    [monoid P] (f : M →* N) (g : M →* P) : comp (snd N P) (monoid_hom.prod f g) = g :=
  ext fun (x : M) => rfl

@[simp] theorem Mathlib.add_monoid_hom.prod_unique {M : Type u_5} {N : Type u_6} {P : Type u_7}
    [add_monoid M] [add_monoid N] [add_monoid P] (f : M →+ N × P) :
    add_monoid_hom.prod (add_monoid_hom.comp (add_monoid_hom.fst N P) f)
          (add_monoid_hom.comp (add_monoid_hom.snd N P) f) =
        f :=
  sorry

/-- `prod.map` as a `monoid_hom`. -/
def Mathlib.add_monoid_hom.prod_map {M : Type u_5} {N : Type u_6} [add_monoid M] [add_monoid N]
    {M' : Type u_8} {N' : Type u_9} [add_monoid M'] [add_monoid N'] (f : M →+ M') (g : N →+ N') :
    M × N →+ M' × N' :=
  add_monoid_hom.prod (add_monoid_hom.comp f (add_monoid_hom.fst M N))
    (add_monoid_hom.comp g (add_monoid_hom.snd M N))

theorem Mathlib.add_monoid_hom.prod_map_def {M : Type u_5} {N : Type u_6} [add_monoid M]
    [add_monoid N] {M' : Type u_8} {N' : Type u_9} [add_monoid M'] [add_monoid N'] (f : M →+ M')
    (g : N →+ N') :
    add_monoid_hom.prod_map f g =
        add_monoid_hom.prod (add_monoid_hom.comp f (add_monoid_hom.fst M N))
          (add_monoid_hom.comp g (add_monoid_hom.snd M N)) :=
  rfl

@[simp] theorem coe_prod_map {M : Type u_5} {N : Type u_6} [monoid M] [monoid N] {M' : Type u_8}
    {N' : Type u_9} [monoid M'] [monoid N'] (f : M →* M') (g : N →* N') :
    ⇑(prod_map f g) = prod.map ⇑f ⇑g :=
  rfl

theorem prod_comp_prod_map {M : Type u_5} {N : Type u_6} {P : Type u_7} [monoid M] [monoid N]
    {M' : Type u_8} {N' : Type u_9} [monoid M'] [monoid N'] [monoid P] (f : P →* M) (g : P →* N)
    (f' : M →* M') (g' : N →* N') :
    comp (prod_map f' g') (monoid_hom.prod f g) = monoid_hom.prod (comp f' f) (comp g' g) :=
  rfl

/-- Coproduct of two `monoid_hom`s with the same codomain:
`f.coprod g (p : M × N) = f p.1 * g p.2`. -/
def coprod {M : Type u_5} {N : Type u_6} {P : Type u_7} [monoid M] [monoid N] [comm_monoid P]
    (f : M →* P) (g : N →* P) : M × N →* P :=
  comp f (fst M N) * comp g (snd M N)

@[simp] theorem coprod_apply {M : Type u_5} {N : Type u_6} {P : Type u_7} [monoid M] [monoid N]
    [comm_monoid P] (f : M →* P) (g : N →* P) (p : M × N) :
    coe_fn (coprod f g) p = coe_fn f (prod.fst p) * coe_fn g (prod.snd p) :=
  rfl

@[simp] theorem Mathlib.add_monoid_hom.coprod_comp_inl {M : Type u_5} {N : Type u_6} {P : Type u_7}
    [add_monoid M] [add_monoid N] [add_comm_monoid P] (f : M →+ P) (g : N →+ P) :
    add_monoid_hom.comp (add_monoid_hom.coprod f g) (add_monoid_hom.inl M N) = f :=
  sorry

@[simp] theorem Mathlib.add_monoid_hom.coprod_comp_inr {M : Type u_5} {N : Type u_6} {P : Type u_7}
    [add_monoid M] [add_monoid N] [add_comm_monoid P] (f : M →+ P) (g : N →+ P) :
    add_monoid_hom.comp (add_monoid_hom.coprod f g) (add_monoid_hom.inr M N) = g :=
  sorry

@[simp] theorem Mathlib.add_monoid_hom.coprod_unique {M : Type u_5} {N : Type u_6} {P : Type u_7}
    [add_monoid M] [add_monoid N] [add_comm_monoid P] (f : M × N →+ P) :
    add_monoid_hom.coprod (add_monoid_hom.comp f (add_monoid_hom.inl M N))
          (add_monoid_hom.comp f (add_monoid_hom.inr M N)) =
        f :=
  sorry

@[simp] theorem coprod_inl_inr {M : Type u_1} {N : Type u_2} [comm_monoid M] [comm_monoid N] :
    coprod (inl M N) (inr M N) = id (M × N) :=
  coprod_unique (id (M × N))

theorem comp_coprod {M : Type u_5} {N : Type u_6} {P : Type u_7} [monoid M] [monoid N]
    [comm_monoid P] {Q : Type u_1} [comm_monoid Q] (h : P →* Q) (f : M →* P) (g : N →* P) :
    comp h (coprod f g) = coprod (comp h f) (comp h g) :=
  sorry

end monoid_hom


namespace mul_equiv


/-- The equivalence between `M × N` and `N × M` given by swapping the components is multiplicative. -/
def prod_comm {M : Type u_5} {N : Type u_6} [monoid M] [monoid N] : M × N ≃* N × M :=
  mk (equiv.to_fun (equiv.prod_comm M N)) (equiv.inv_fun (equiv.prod_comm M N)) sorry sorry sorry

@[simp] theorem coe_prod_comm {M : Type u_5} {N : Type u_6} [monoid M] [monoid N] :
    ⇑prod_comm = prod.swap :=
  rfl

@[simp] theorem coe_prod_comm_symm {M : Type u_5} {N : Type u_6} [monoid M] [monoid N] :
    ⇑(symm prod_comm) = prod.swap :=
  rfl

/-- The monoid equivalence between units of a product of two monoids, and the product of the
    units of each monoid. -/
def prod_units {M : Type u_5} {N : Type u_6} [monoid M] [monoid N] :
    units (M × N) ≃* units M × units N :=
  mk (⇑(monoid_hom.prod (units.map (monoid_hom.fst M N)) (units.map (monoid_hom.snd M N))))
    (fun (u : units M × units N) =>
      units.mk (↑(prod.fst u), ↑(prod.snd u)) (↑(prod.fst u⁻¹), ↑(prod.snd u⁻¹)) sorry sorry)
    sorry sorry sorry

end Mathlib