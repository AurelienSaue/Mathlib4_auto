/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.group.hom
import Mathlib.algebra.group.type_tags
import Mathlib.algebra.group.units_hom
import Mathlib.PostPort

universes u_8 u_9 l u_3 u_4 u_1 u_5 u_2 u_6 u_7 

namespace Mathlib

/-!
# Multiplicative and additive equivs

In this file we define two extensions of `equiv` called `add_equiv` and `mul_equiv`, which are
datatypes representing isomorphisms of `add_monoid`s/`add_group`s and `monoid`s/`group`s.

## Notations

The extended equivs all have coercions to functions, and the coercions are the canonical
notation when treating the isomorphisms as maps.

## Implementation notes

The fields for `mul_equiv`, `add_equiv` now avoid the unbundled `is_mul_hom` and `is_add_hom`, as
these are deprecated.

## Tags

equiv, mul_equiv, add_equiv
-/

/-- add_equiv α β is the type of an equiv α ≃ β which preserves addition. -/
structure add_equiv (A : Type u_8) (B : Type u_9) [Add A] [Add B] extends add_hom A B, A ≃ B where

/-- The `equiv` underlying an `add_equiv`. -/
/-- The `add_hom` underlying a `add_equiv`. -/
/-- `mul_equiv α β` is the type of an equiv `α ≃ β` which preserves multiplication. -/
structure mul_equiv (M : Type u_8) (N : Type u_9) [Mul M] [Mul N] extends mul_hom M N, M ≃ N where

infixl:25 " ≃* " => Mathlib.mul_equiv

infixl:25 " ≃+ " => Mathlib.add_equiv

/-- The `equiv` underlying a `mul_equiv`. -/
/-- The `mul_hom` underlying a `mul_equiv`. -/
namespace mul_equiv


protected instance has_coe_to_fun {M : Type u_3} {N : Type u_4} [Mul M] [Mul N] :
    has_coe_to_fun (M ≃* N) :=
  has_coe_to_fun.mk (fun (x : M ≃* N) => M → N) to_fun

@[simp] theorem Mathlib.add_equiv.to_fun_apply {M : Type u_3} {N : Type u_4} [Add M] [Add N]
    {f : M ≃+ N} {m : M} : add_equiv.to_fun f m = coe_fn f m :=
  rfl

@[simp] theorem Mathlib.add_equiv.to_equiv_apply {M : Type u_3} {N : Type u_4} [Add M] [Add N]
    {f : M ≃+ N} {m : M} : coe_fn (add_equiv.to_equiv f) m = coe_fn f m :=
  rfl

/-- A multiplicative isomorphism preserves multiplication (canonical form). -/
@[simp] theorem map_mul {M : Type u_3} {N : Type u_4} [Mul M] [Mul N] (f : M ≃* N) (x : M) (y : M) :
    coe_fn f (x * y) = coe_fn f x * coe_fn f y :=
  map_mul' f

/-- Makes a multiplicative isomorphism from a bijection which preserves multiplication. -/
def mk' {M : Type u_3} {N : Type u_4} [Mul M] [Mul N] (f : M ≃ N)
    (h : ∀ (x y : M), coe_fn f (x * y) = coe_fn f x * coe_fn f y) : M ≃* N :=
  mk (equiv.to_fun f) (equiv.inv_fun f) (equiv.left_inv f) (equiv.right_inv f) h

protected theorem Mathlib.add_equiv.bijective {M : Type u_3} {N : Type u_4} [Add M] [Add N]
    (e : M ≃+ N) : function.bijective ⇑e :=
  equiv.bijective (add_equiv.to_equiv e)

protected theorem Mathlib.add_equiv.injective {M : Type u_3} {N : Type u_4} [Add M] [Add N]
    (e : M ≃+ N) : function.injective ⇑e :=
  equiv.injective (add_equiv.to_equiv e)

protected theorem Mathlib.add_equiv.surjective {M : Type u_3} {N : Type u_4} [Add M] [Add N]
    (e : M ≃+ N) : function.surjective ⇑e :=
  equiv.surjective (add_equiv.to_equiv e)

/-- The identity map is a multiplicative isomorphism. -/
def refl (M : Type u_1) [Mul M] : M ≃* M :=
  mk (equiv.to_fun (equiv.refl M)) (equiv.inv_fun (equiv.refl M)) sorry sorry sorry

protected instance inhabited {M : Type u_3} [Mul M] : Inhabited (M ≃* M) := { default := refl M }

/-- The inverse of an isomorphism is an isomorphism. -/
def Mathlib.add_equiv.symm {M : Type u_3} {N : Type u_4} [Add M] [Add N] (h : M ≃+ N) : N ≃+ M :=
  add_equiv.mk (equiv.to_fun (equiv.symm (add_equiv.to_equiv h)))
    (equiv.inv_fun (equiv.symm (add_equiv.to_equiv h))) sorry sorry sorry

/-- See Note [custom simps projection] -/
-- we don't hyperlink the note in the additive version, since that breaks syntax highlighting

-- in the whole file.

def simps.inv_fun {M : Type u_3} {N : Type u_4} [Mul M] [Mul N] (e : M ≃* N) : N → M := ⇑(symm e)

@[simp] theorem Mathlib.add_equiv.to_equiv_symm {M : Type u_3} {N : Type u_4} [Add M] [Add N]
    (f : M ≃+ N) : add_equiv.to_equiv (add_equiv.symm f) = equiv.symm (add_equiv.to_equiv f) :=
  rfl

@[simp] theorem Mathlib.add_equiv.coe_mk {M : Type u_3} {N : Type u_4} [Add M] [Add N] (f : M → N)
    (g : N → M) (h₁ : function.left_inverse g f) (h₂ : function.right_inverse g f)
    (h₃ : ∀ (x y : M), f (x + y) = f x + f y) : ⇑(add_equiv.mk f g h₁ h₂ h₃) = f :=
  rfl

@[simp] theorem Mathlib.add_equiv.coe_symm_mk {M : Type u_3} {N : Type u_4} [Add M] [Add N]
    (f : M → N) (g : N → M) (h₁ : function.left_inverse g f) (h₂ : function.right_inverse g f)
    (h₃ : ∀ (x y : M), f (x + y) = f x + f y) : ⇑(add_equiv.symm (add_equiv.mk f g h₁ h₂ h₃)) = g :=
  rfl

/-- Transitivity of multiplication-preserving isomorphisms -/
def Mathlib.add_equiv.trans {M : Type u_3} {N : Type u_4} {P : Type u_5} [Add M] [Add N] [Add P]
    (h1 : M ≃+ N) (h2 : N ≃+ P) : M ≃+ P :=
  add_equiv.mk (equiv.to_fun (equiv.trans (add_equiv.to_equiv h1) (add_equiv.to_equiv h2)))
    (equiv.inv_fun (equiv.trans (add_equiv.to_equiv h1) (add_equiv.to_equiv h2))) sorry sorry sorry

/-- e.right_inv in canonical form -/
@[simp] theorem apply_symm_apply {M : Type u_3} {N : Type u_4} [Mul M] [Mul N] (e : M ≃* N)
    (y : N) : coe_fn e (coe_fn (symm e) y) = y :=
  equiv.apply_symm_apply (to_equiv e)

/-- e.left_inv in canonical form -/
@[simp] theorem Mathlib.add_equiv.symm_apply_apply {M : Type u_3} {N : Type u_4} [Add M] [Add N]
    (e : M ≃+ N) (x : M) : coe_fn (add_equiv.symm e) (coe_fn e x) = x :=
  equiv.symm_apply_apply (add_equiv.to_equiv e)

@[simp] theorem Mathlib.add_equiv.refl_apply {M : Type u_3} [Add M] (m : M) :
    coe_fn (add_equiv.refl M) m = m :=
  rfl

@[simp] theorem Mathlib.add_equiv.trans_apply {M : Type u_3} {N : Type u_4} {P : Type u_5} [Add M]
    [Add N] [Add P] (e₁ : M ≃+ N) (e₂ : N ≃+ P) (m : M) :
    coe_fn (add_equiv.trans e₁ e₂) m = coe_fn e₂ (coe_fn e₁ m) :=
  rfl

@[simp] theorem Mathlib.add_equiv.apply_eq_iff_eq {M : Type u_3} {N : Type u_4} [Add M] [Add N]
    (e : M ≃+ N) {x : M} {y : M} : coe_fn e x = coe_fn e y ↔ x = y :=
  function.injective.eq_iff (add_equiv.injective e)

theorem Mathlib.add_equiv.apply_eq_iff_symm_apply {M : Type u_3} {N : Type u_4} [Add M] [Add N]
    (e : M ≃+ N) {x : M} {y : N} : coe_fn e x = y ↔ x = coe_fn (add_equiv.symm e) y :=
  equiv.apply_eq_iff_eq_symm_apply (add_equiv.to_equiv e)

theorem symm_apply_eq {M : Type u_3} {N : Type u_4} [Mul M] [Mul N] (e : M ≃* N) {x : N} {y : M} :
    coe_fn (symm e) x = y ↔ x = coe_fn e y :=
  equiv.symm_apply_eq (to_equiv e)

theorem eq_symm_apply {M : Type u_3} {N : Type u_4} [Mul M] [Mul N] (e : M ≃* N) {x : N} {y : M} :
    y = coe_fn (symm e) x ↔ coe_fn e y = x :=
  equiv.eq_symm_apply (to_equiv e)

/-- a multiplicative equiv of monoids sends 1 to 1 (and is hence a monoid isomorphism) -/
@[simp] theorem Mathlib.add_equiv.map_zero {M : Type u_1} {N : Type u_2} [add_monoid M]
    [add_monoid N] (h : M ≃+ N) : coe_fn h 0 = 0 :=
  sorry

@[simp] theorem Mathlib.add_equiv.map_eq_zero_iff {M : Type u_1} {N : Type u_2} [add_monoid M]
    [add_monoid N] (h : M ≃+ N) {x : M} : coe_fn h x = 0 ↔ x = 0 :=
  add_equiv.map_zero h ▸ equiv.apply_eq_iff_eq (add_equiv.to_equiv h)

theorem map_ne_one_iff {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] (h : M ≃* N) {x : M} :
    coe_fn h x ≠ 1 ↔ x ≠ 1 :=
  { mp := mt (iff.mpr (map_eq_one_iff h)), mpr := mt (iff.mp (map_eq_one_iff h)) }

/-- A bijective `monoid` homomorphism is an isomorphism -/
def Mathlib.add_equiv.of_bijective {M : Type u_1} {N : Type u_2} [add_monoid M] [add_monoid N]
    (f : M →+ N) (hf : function.bijective ⇑f) : M ≃+ N :=
  add_equiv.mk (equiv.to_fun (equiv.of_bijective (⇑f) hf))
    (equiv.inv_fun (equiv.of_bijective (⇑f) hf)) sorry sorry (add_monoid_hom.map_add' f)

/--
Extract the forward direction of a multiplicative equivalence
as a multiplication-preserving function.
-/
def Mathlib.add_equiv.to_add_monoid_hom {M : Type u_1} {N : Type u_2} [add_monoid M] [add_monoid N]
    (h : M ≃+ N) : M →+ N :=
  add_monoid_hom.mk (add_equiv.to_fun h) (add_equiv.map_zero h) sorry

@[simp] theorem coe_to_monoid_hom {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] (e : M ≃* N) :
    ⇑(to_monoid_hom e) = ⇑e :=
  rfl

theorem Mathlib.add_equiv.to_add_monoid_hom_apply {M : Type u_1} {N : Type u_2} [add_monoid M]
    [add_monoid N] (e : M ≃+ N) (x : M) : coe_fn (add_equiv.to_add_monoid_hom e) x = coe_fn e x :=
  rfl

/-- A multiplicative equivalence of groups preserves inversion. -/
@[simp] theorem map_inv {G : Type u_6} {H : Type u_7} [group G] [group H] (h : G ≃* H) (x : G) :
    coe_fn h (x⁻¹) = (coe_fn h x⁻¹) :=
  monoid_hom.map_inv (to_monoid_hom h) x

/-- Two multiplicative isomorphisms agree if they are defined by the
    same underlying function. -/
theorem ext {M : Type u_3} {N : Type u_4} [Mul M] [Mul N] {f : M ≃* N} {g : M ≃* N}
    (h : ∀ (x : M), coe_fn f x = coe_fn g x) : f = g :=
  sorry

protected theorem congr_arg {M : Type u_3} {N : Type u_4} [Mul M] [Mul N] {f : M ≃* N} {x : M}
    {x' : M} : x = x' → coe_fn f x = coe_fn f x' :=
  sorry

protected theorem congr_fun {M : Type u_3} {N : Type u_4} [Mul M] [Mul N] {f : M ≃* N} {g : M ≃* N}
    (h : f = g) (x : M) : coe_fn f x = coe_fn g x :=
  h ▸ rfl

theorem ext_iff {M : Type u_3} {N : Type u_4} [Mul M] [Mul N] {f : M ≃* N} {g : M ≃* N} :
    f = g ↔ ∀ (x : M), coe_fn f x = coe_fn g x :=
  { mp := fun (h : f = g) (x : M) => h ▸ rfl, mpr := ext }

theorem Mathlib.add_equiv.to_add_monoid_hom_injective {M : Type u_1} {N : Type u_2} [add_monoid M]
    [add_monoid N] : function.injective add_equiv.to_add_monoid_hom :=
  fun (f g : M ≃+ N) (h : add_equiv.to_add_monoid_hom f = add_equiv.to_add_monoid_hom g) =>
    add_equiv.ext (iff.mp add_monoid_hom.ext_iff h)

end mul_equiv


-- We don't use `to_additive` to generate definition because it fails to tell Lean about

-- equational lemmas

/-- Given a pair of additive monoid homomorphisms `f`, `g` such that `g.comp f = id` and
`f.comp g = id`, returns an additive equivalence with `to_fun = f` and `inv_fun = g`.  This
constructor is useful if the underlying type(s) have specialized `ext` lemmas for additive
monoid homomorphisms. -/
def add_monoid_hom.to_add_equiv {M : Type u_3} {N : Type u_4} [add_monoid M] [add_monoid N]
    (f : M →+ N) (g : N →+ M) (h₁ : add_monoid_hom.comp g f = add_monoid_hom.id M)
    (h₂ : add_monoid_hom.comp f g = add_monoid_hom.id N) : M ≃+ N :=
  add_equiv.mk ⇑f ⇑g sorry sorry (add_monoid_hom.map_add f)

/-- Given a pair of monoid homomorphisms `f`, `g` such that `g.comp f = id` and `f.comp g = id`,
returns an multiplicative equivalence with `to_fun = f` and `inv_fun = g`.  This constructor is
useful if the underlying type(s) have specialized `ext` lemmas for monoid homomorphisms. -/
def monoid_hom.to_mul_equiv {M : Type u_3} {N : Type u_4} [monoid M] [monoid N] (f : M →* N)
    (g : N →* M) (h₁ : monoid_hom.comp g f = monoid_hom.id M)
    (h₂ : monoid_hom.comp f g = monoid_hom.id N) : M ≃* N :=
  mul_equiv.mk ⇑f ⇑g sorry sorry (monoid_hom.map_mul f)

@[simp] theorem monoid_hom.coe_to_mul_equiv {M : Type u_3} {N : Type u_4} [monoid M] [monoid N]
    (f : M →* N) (g : N →* M) (h₁ : monoid_hom.comp g f = monoid_hom.id M)
    (h₂ : monoid_hom.comp f g = monoid_hom.id N) : ⇑(monoid_hom.to_mul_equiv f g h₁ h₂) = ⇑f :=
  rfl

/-- An additive equivalence of additive groups preserves subtraction. -/
theorem add_equiv.map_sub {A : Type u_1} {B : Type u_2} [add_group A] [add_group B] (h : A ≃+ B)
    (x : A) (y : A) : coe_fn h (x - y) = coe_fn h x - coe_fn h y :=
  add_monoid_hom.map_sub (add_equiv.to_add_monoid_hom h) x y

protected instance add_equiv.inhabited {M : Type u_1} [Add M] : Inhabited (M ≃+ M) :=
  { default := add_equiv.refl M }

/-- A group is isomorphic to its group of units. -/
def to_add_units {G : Type u_1} [add_group G] : G ≃+ add_units G :=
  add_equiv.mk (fun (x : G) => add_units.mk x (-x) (add_neg_self x) (neg_add_self x)) coe sorry
    sorry sorry

namespace units


/-- A multiplicative equivalence of monoids defines a multiplicative equivalence
of their groups of units. -/
def map_equiv {M : Type u_3} {N : Type u_4} [monoid M] [monoid N] (h : M ≃* N) :
    units M ≃* units N :=
  mul_equiv.mk (monoid_hom.to_fun (map (mul_equiv.to_monoid_hom h)))
    ⇑(map (mul_equiv.to_monoid_hom (mul_equiv.symm h))) sorry sorry sorry

/-- Left multiplication by a unit of a monoid is a permutation of the underlying type. -/
def mul_left {M : Type u_3} [monoid M] (u : units M) : equiv.perm M :=
  equiv.mk (fun (x : M) => ↑u * x) (fun (x : M) => ↑(u⁻¹) * x) (inv_mul_cancel_left u)
    (mul_inv_cancel_left u)

@[simp] theorem coe_mul_left {M : Type u_3} [monoid M] (u : units M) : ⇑(mul_left u) = Mul.mul ↑u :=
  rfl

@[simp] theorem Mathlib.add_units.add_left_symm {M : Type u_3} [add_monoid M] (u : add_units M) :
    equiv.symm (add_units.add_left u) = add_units.add_left (-u) :=
  equiv.ext fun (x : M) => rfl

/-- Right multiplication by a unit of a monoid is a permutation of the underlying type. -/
def mul_right {M : Type u_3} [monoid M] (u : units M) : equiv.perm M :=
  equiv.mk (fun (x : M) => x * ↑u) (fun (x : M) => x * ↑(u⁻¹)) sorry sorry

@[simp] theorem Mathlib.add_units.coe_add_right {M : Type u_3} [add_monoid M] (u : add_units M) :
    ⇑(add_units.add_right u) = fun (x : M) => x + ↑u :=
  rfl

@[simp] theorem Mathlib.add_units.add_right_symm {M : Type u_3} [add_monoid M] (u : add_units M) :
    equiv.symm (add_units.add_right u) = add_units.add_right (-u) :=
  equiv.ext fun (x : M) => rfl

end units


namespace equiv


/-- Left multiplication in a `group` is a permutation of the underlying type. -/
protected def add_left {G : Type u_6} [add_group G] (a : G) : perm G :=
  add_units.add_left (coe_fn to_add_units a)

@[simp] theorem coe_add_left {G : Type u_6} [add_group G] (a : G) :
    ⇑(equiv.add_left a) = Add.add a :=
  rfl

/-- extra simp lemma that `dsimp` can use. `simp` will never use this. -/
@[simp] theorem add_left_symm_apply {G : Type u_6} [add_group G] (a : G) :
    ⇑(equiv.symm (equiv.add_left a)) = Add.add (-a) :=
  rfl

@[simp] theorem mul_left_symm {G : Type u_6} [group G] (a : G) :
    equiv.symm (equiv.mul_left a) = equiv.mul_left (a⁻¹) :=
  ext fun (x : G) => rfl

/-- Right multiplication in a `group` is a permutation of the underlying type. -/
protected def add_right {G : Type u_6} [add_group G] (a : G) : perm G :=
  add_units.add_right (coe_fn to_add_units a)

@[simp] theorem coe_mul_right {G : Type u_6} [group G] (a : G) :
    ⇑(equiv.mul_right a) = fun (x : G) => x * a :=
  rfl

@[simp] theorem mul_right_symm {G : Type u_6} [group G] (a : G) :
    equiv.symm (equiv.mul_right a) = equiv.mul_right (a⁻¹) :=
  ext fun (x : G) => rfl

/-- extra simp lemma that `dsimp` can use. `simp` will never use this.  -/
@[simp] theorem add_right_symm_apply {G : Type u_6} [add_group G] (a : G) :
    ⇑(equiv.symm (equiv.add_right a)) = fun (x : G) => x + -a :=
  rfl

/-- Inversion on a `group` is a permutation of the underlying type. -/
protected def neg (G : Type u_6) [add_group G] : perm G :=
  mk (fun (a : G) => -a) (fun (a : G) => -a) sorry sorry

@[simp] theorem coe_inv {G : Type u_6} [group G] : ⇑(equiv.inv G) = has_inv.inv := rfl

@[simp] theorem neg_symm {G : Type u_6} [add_group G] : equiv.symm (equiv.neg G) = equiv.neg G :=
  rfl

end equiv


/-- Reinterpret `G ≃+ H` as `multiplicative G ≃* multiplicative H`. -/
def add_equiv.to_multiplicative {G : Type u_6} {H : Type u_7} [add_monoid G] [add_monoid H] :
    G ≃+ H ≃ (multiplicative G ≃* multiplicative H) :=
  equiv.mk
    (fun (f : G ≃+ H) =>
      mul_equiv.mk ⇑(coe_fn add_monoid_hom.to_multiplicative (add_equiv.to_add_monoid_hom f))
        ⇑(coe_fn add_monoid_hom.to_multiplicative (add_equiv.to_add_monoid_hom (add_equiv.symm f)))
        sorry sorry sorry)
    (fun (f : multiplicative G ≃* multiplicative H) =>
      add_equiv.mk ⇑(mul_equiv.to_monoid_hom f) ⇑(mul_equiv.to_monoid_hom (mul_equiv.symm f)) sorry
        sorry sorry)
    sorry sorry

/-- Reinterpret `G ≃* H` as `additive G ≃+ additive H`. -/
def mul_equiv.to_additive {G : Type u_6} {H : Type u_7} [monoid G] [monoid H] :
    G ≃* H ≃ (additive G ≃+ additive H) :=
  equiv.mk
    (fun (f : G ≃* H) =>
      add_equiv.mk ⇑(coe_fn monoid_hom.to_additive (mul_equiv.to_monoid_hom f))
        ⇑(coe_fn monoid_hom.to_additive (mul_equiv.to_monoid_hom (mul_equiv.symm f))) sorry sorry
        sorry)
    (fun (f : additive G ≃+ additive H) =>
      mul_equiv.mk ⇑(add_equiv.to_add_monoid_hom f)
        ⇑(add_equiv.to_add_monoid_hom (add_equiv.symm f)) sorry sorry sorry)
    sorry sorry

/-- Reinterpret `additive G ≃+ H` as `G ≃* multiplicative H`. -/
def add_equiv.to_multiplicative' {G : Type u_6} {H : Type u_7} [monoid G] [add_monoid H] :
    additive G ≃+ H ≃ (G ≃* multiplicative H) :=
  equiv.mk
    (fun (f : additive G ≃+ H) =>
      mul_equiv.mk ⇑(coe_fn add_monoid_hom.to_multiplicative' (add_equiv.to_add_monoid_hom f))
        ⇑(coe_fn add_monoid_hom.to_multiplicative''
            (add_equiv.to_add_monoid_hom (add_equiv.symm f)))
        sorry sorry sorry)
    (fun (f : G ≃* multiplicative H) =>
      add_equiv.mk ⇑(mul_equiv.to_monoid_hom f) ⇑(mul_equiv.to_monoid_hom (mul_equiv.symm f)) sorry
        sorry sorry)
    sorry sorry

/-- Reinterpret `G ≃* multiplicative H` as `additive G ≃+ H` as. -/
def mul_equiv.to_additive' {G : Type u_6} {H : Type u_7} [monoid G] [add_monoid H] :
    G ≃* multiplicative H ≃ (additive G ≃+ H) :=
  equiv.symm add_equiv.to_multiplicative'

/-- Reinterpret `G ≃+ additive H` as `multiplicative G ≃* H`. -/
def add_equiv.to_multiplicative'' {G : Type u_6} {H : Type u_7} [add_monoid G] [monoid H] :
    G ≃+ additive H ≃ (multiplicative G ≃* H) :=
  equiv.mk
    (fun (f : G ≃+ additive H) =>
      mul_equiv.mk ⇑(coe_fn add_monoid_hom.to_multiplicative'' (add_equiv.to_add_monoid_hom f))
        ⇑(coe_fn add_monoid_hom.to_multiplicative' (add_equiv.to_add_monoid_hom (add_equiv.symm f)))
        sorry sorry sorry)
    (fun (f : multiplicative G ≃* H) =>
      add_equiv.mk ⇑(mul_equiv.to_monoid_hom f) ⇑(mul_equiv.to_monoid_hom (mul_equiv.symm f)) sorry
        sorry sorry)
    sorry sorry

/-- Reinterpret `multiplicative G ≃* H` as `G ≃+ additive H` as. -/
def mul_equiv.to_additive'' {G : Type u_6} {H : Type u_7} [add_monoid G] [monoid H] :
    multiplicative G ≃* H ≃ (G ≃+ additive H) :=
  equiv.symm add_equiv.to_multiplicative''

end Mathlib