/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury G. Kudryashov
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.analysis.specific_limits
import Mathlib.order.iterate
import Mathlib.order.semiconj_Sup
import Mathlib.algebra.iterate_hom
import PostPort

universes l u_1 

namespace Mathlib

/-!
# Translation number of a monotone real map that commutes with `x ↦ x + 1`

Let `f : ℝ → ℝ` be a monotone map such that `f (x + 1) = f x + 1` for all `x`. Then the limit
$$
  \tau(f)=\lim_{n\to\infty}{f^n(x)-x}{n}
$$
exists and does not depend on `x`. This number is called the *translation number* of `f`.
Different authors use different notation for this number: `τ`, `ρ`, `rot`, etc

In this file we define a structure `circle_deg1_lift` for bundled maps with these properties, define
translation number of `f : circle_deg1_lift`, prove some estimates relating `f^n(x)-x` to `τ(f)`. In
case of a continuous map `f` we also prove that `f` admits a point `x` such that `f^n(x)=x+m` if and
only if `τ(f)=m/n`.

Maps of this type naturally appear as lifts of orientation preserving circle homeomorphisms. More
precisely, let `f` be an orientation preserving homeomorphism of the circle $S^1=ℝ/ℤ$, and
consider a real number `a` such that
`⟦a⟧ = f 0`, where `⟦⟧` means the natural projection `ℝ → ℝ/ℤ`. Then there exists a unique
continuous function `F : ℝ → ℝ` such that `F 0 = a` and `⟦F x⟧ = f ⟦x⟧` for all `x` (this fact is
not formalized yet). This function is strictly monotone, continuous, and satisfies
`F (x + 1) = F x + 1`. The number `⟦τ F⟧ : ℝ / ℤ` is called the *rotation number* of `f`.
It does not depend on the choice of `a`.

## Main definitions

* `circle_deg1_lift`: a monotone map `f : ℝ → ℝ` such that `f (x + 1) = f x + 1` for all `x`;
  the type `circle_deg1_lift` is equipped with `lattice` and `monoid` structures; the
  multiplication is given by composition: `(f * g) x = f (g x)`.
* `circle_deg1_lift.translation_number`: translation number of `f : circle_deg1_lift`.

## Main statements

We prove the following properties of `circle_deg1_lift.translation_number`.

* `circle_deg1_lift.translation_number_eq_of_dist_bounded`: if the distance between `(f^n) 0`
  and `(g^n) 0` is bounded from above uniformly in `n : ℕ`, then `f` and `g` have equal
  translation numbers.

* `circle_deg1_lift.translation_number_eq_of_semiconj_by`: if two `circle_deg1_lift` maps `f`, `g`
  are semiconjugate by a `circle_deg1_lift` map, then `τ f = τ g`.

* `circle_deg1_lift.translation_number_units_inv`: if `f` is an invertible `circle_deg1_lift` map
  (equivalently, `f` is a lift of an orientation-preserving circle homeomorphism), then
  the translation number of `f⁻¹` is the negative of the translation number of `f`.

* `circle_deg1_lift.translation_number_mul_of_commute`: if `f` and `g` commute, then
  `τ (f * g) = τ f + τ g`.

* `circle_deg1_lift.translation_number_eq_rat_iff`: the translation number of `f` is equal to
  a rational number `m / n` if and only if `(f^n) x = x + m` for some `x`.

* `circle_deg1_lift.semiconj_of_bijective_of_translation_number_eq`: if `f` and `g` are two
  bijective `circle_deg1_lift` maps and their translation numbers are equal, then these
  maps are semiconjugate to each other.

* `circle_deg1_lift.semiconj_of_group_action_of_forall_translation_number_eq`: let `f₁` and `f₂` be
  two actions of a group `G` on the circle by degree 1 maps (formally, `f₁` and `f₂` are two
  homomorphisms from `G →* circle_deg1_lift`). If the translation numbers of `f₁ g` and `f₂ g` are
  equal to each other for all `g : G`, then these two actions are semiconjugate by some `F :
  circle_deg1_lift`. This is a version of Proposition 5.4 from [Étienne Ghys, Groupes
  d'homeomorphismes du cercle et cohomologie bornee][ghys87:groupes].

## Notation

We use a local notation `τ` for the translation number of `f : circle_deg1_lift`.

## Implementation notes

We define the translation number of `f : circle_deg1_lift` to be the limit of the sequence
`(f ^ (2 ^ n)) 0 / (2 ^ n)`, then prove that `((f ^ n) x - x) / n` tends to this number for any `x`.
This way it is much easier to prove that the limit exists and basic properties of the limit.

We define translation number for a wider class of maps `f : ℝ → ℝ` instead of lifts of orientation
preserving circle homeomorphisms for two reasons:

* non-strictly monotone circle self-maps with discontinuities naturally appear as Poincaré maps
  for some flows on the two-torus (e.g., one can take a constant flow and glue in a few Cherry
  cells);
* definition and some basic properties still work for this class.

## References

* [Étienne Ghys, Groupes d'homeomorphismes du cercle et cohomologie bornee][ghys87:groupes]

## TODO

Here are some short-term goals.

* Introduce a structure or a typeclass for lifts of circle homeomorphisms. We use `units
  circle_deg1_lift` for now, but it's better to have a dedicated type (or a typeclass?).

* Prove that the `semiconj_by` relation on circle homeomorphisms is an equivalence relation.

* Introduce `conditionally_complete_lattice` structure, use it in the proof of
  `circle_deg1_lift.semiconj_of_group_action_of_forall_translation_number_eq`.

* Prove that the orbits of the irrational rotation are dense in the circle. Deduce that a
  homeomorphism with an irrational rotation is semiconjugate to the corresponding irrational
  translation by a continuous `circle_deg1_lift`.

## Tags

circle homeomorphism, rotation number
-/

/-!
### Definition and monoid structure
-/

/-- A lift of a monotone degree one map `S¹ → S¹`. -/
structure circle_deg1_lift 
where
  to_fun : ℝ → ℝ
  monotone' : monotone to_fun
  map_add_one' : ∀ (x : ℝ), to_fun (x + 1) = to_fun x + 1

namespace circle_deg1_lift


protected instance has_coe_to_fun : has_coe_to_fun circle_deg1_lift :=
  has_coe_to_fun.mk (fun (_x : circle_deg1_lift) => ℝ → ℝ) to_fun

@[simp] theorem coe_mk (f : ℝ → ℝ) (h₁ : monotone f) (h₂ : ∀ (x : ℝ), f (x + 1) = f x + 1) : ⇑(mk f h₁ h₂) = f :=
  rfl

protected theorem monotone (f : circle_deg1_lift) : monotone ⇑f :=
  monotone' f

theorem mono (f : circle_deg1_lift) {x : ℝ} {y : ℝ} (h : x ≤ y) : coe_fn f x ≤ coe_fn f y :=
  circle_deg1_lift.monotone f h

theorem strict_mono_iff_injective (f : circle_deg1_lift) : strict_mono ⇑f ↔ function.injective ⇑f :=
  monotone.strict_mono_iff_injective (circle_deg1_lift.monotone f)

@[simp] theorem map_add_one (f : circle_deg1_lift) (x : ℝ) : coe_fn f (x + 1) = coe_fn f x + 1 :=
  map_add_one' f

@[simp] theorem map_one_add (f : circle_deg1_lift) (x : ℝ) : coe_fn f (1 + x) = 1 + coe_fn f x := sorry

theorem coe_inj {f : circle_deg1_lift} {g : circle_deg1_lift} : ⇑f = ⇑g → f = g := sorry

theorem ext {f : circle_deg1_lift} {g : circle_deg1_lift} (h : ∀ (x : ℝ), coe_fn f x = coe_fn g x) : f = g :=
  coe_inj (funext h)

theorem ext_iff {f : circle_deg1_lift} {g : circle_deg1_lift} : f = g ↔ ∀ (x : ℝ), coe_fn f x = coe_fn g x :=
  { mp := fun (h : f = g) (x : ℝ) => h ▸ rfl, mpr := fun (h : ∀ (x : ℝ), coe_fn f x = coe_fn g x) => ext h }

protected instance monoid : monoid circle_deg1_lift :=
  monoid.mk (fun (f g : circle_deg1_lift) => mk (⇑f ∘ ⇑g) sorry sorry) sorry (mk id monotone_id sorry) sorry sorry

protected instance inhabited : Inhabited circle_deg1_lift :=
  { default := 1 }

@[simp] theorem coe_mul (f : circle_deg1_lift) (g : circle_deg1_lift) : ⇑(f * g) = ⇑f ∘ ⇑g :=
  rfl

theorem mul_apply (f : circle_deg1_lift) (g : circle_deg1_lift) (x : ℝ) : coe_fn (f * g) x = coe_fn f (coe_fn g x) :=
  rfl

@[simp] theorem coe_one : ⇑1 = id :=
  rfl

protected instance units_has_coe_to_fun : has_coe_to_fun (units circle_deg1_lift) :=
  has_coe_to_fun.mk (fun (_x : units circle_deg1_lift) => ℝ → ℝ) fun (f : units circle_deg1_lift) => ⇑↑f

@[simp] theorem units_coe (f : units circle_deg1_lift) : ⇑↑f = ⇑f :=
  rfl

@[simp] theorem units_inv_apply_apply (f : units circle_deg1_lift) (x : ℝ) : coe_fn (f⁻¹) (coe_fn f x) = x := sorry

@[simp] theorem units_apply_inv_apply (f : units circle_deg1_lift) (x : ℝ) : coe_fn f (coe_fn (f⁻¹) x) = x := sorry

/-- If a lift of a circle map is bijective, then it is an order automorphism of the line. -/
def to_order_iso : units circle_deg1_lift →* ℝ ≃o ℝ :=
  monoid_hom.mk
    (fun (f : units circle_deg1_lift) =>
      rel_iso.mk (equiv.mk (⇑f) (⇑(f⁻¹)) (units_inv_apply_apply f) (units_apply_inv_apply f)) sorry)
    sorry sorry

@[simp] theorem coe_to_order_iso (f : units circle_deg1_lift) : ⇑(coe_fn to_order_iso f) = ⇑f :=
  rfl

@[simp] theorem coe_to_order_iso_symm (f : units circle_deg1_lift) : ⇑(order_iso.symm (coe_fn to_order_iso f)) = ⇑(f⁻¹) :=
  rfl

@[simp] theorem coe_to_order_iso_inv (f : units circle_deg1_lift) : ⇑(coe_fn to_order_iso f⁻¹) = ⇑(f⁻¹) :=
  rfl

theorem is_unit_iff_bijective {f : circle_deg1_lift} : is_unit f ↔ function.bijective ⇑f := sorry

theorem coe_pow (f : circle_deg1_lift) (n : ℕ) : ⇑(f ^ n) = nat.iterate (⇑f) n := sorry

theorem semiconj_by_iff_semiconj {f : circle_deg1_lift} {g₁ : circle_deg1_lift} {g₂ : circle_deg1_lift} : semiconj_by f g₁ g₂ ↔ function.semiconj ⇑f ⇑g₁ ⇑g₂ :=
  ext_iff

theorem commute_iff_commute {f : circle_deg1_lift} {g : circle_deg1_lift} : commute f g ↔ function.commute ⇑f ⇑g :=
  ext_iff

/-!
### Translate by a constant
-/

/-- The map `y ↦ x + y` as a `circle_deg1_lift`. More precisely, we define a homomorphism from
`multiplicative ℝ` to `units circle_deg1_lift`, so the translation by `x` is
`translation (multiplicative.of_add x)`. -/
def translate : multiplicative ℝ →* units circle_deg1_lift :=
  monoid_hom.comp
    (units.map
      (monoid_hom.mk (fun (x : multiplicative ℝ) => mk (fun (y : ℝ) => coe_fn multiplicative.to_add x + y) sorry sorry)
        sorry sorry))
    (mul_equiv.to_monoid_hom to_units)

@[simp] theorem translate_apply (x : ℝ) (y : ℝ) : coe_fn (coe_fn translate (coe_fn multiplicative.of_add x)) y = x + y :=
  rfl

@[simp] theorem translate_inv_apply (x : ℝ) (y : ℝ) : coe_fn (coe_fn translate (coe_fn multiplicative.of_add x)⁻¹) y = -x + y :=
  rfl

@[simp] theorem translate_gpow (x : ℝ) (n : ℤ) : coe_fn translate (coe_fn multiplicative.of_add x) ^ n = coe_fn translate (coe_fn multiplicative.of_add (↑n * x)) := sorry

@[simp] theorem translate_pow (x : ℝ) (n : ℕ) : coe_fn translate (coe_fn multiplicative.of_add x) ^ n = coe_fn translate (coe_fn multiplicative.of_add (↑n * x)) :=
  translate_gpow x ↑n

@[simp] theorem translate_iterate (x : ℝ) (n : ℕ) : nat.iterate (⇑(coe_fn translate (coe_fn multiplicative.of_add x))) n =
  ⇑(coe_fn translate (coe_fn multiplicative.of_add (↑n * x))) := sorry

/-!
### Commutativity with integer translations

In this section we prove that `f` commutes with translations by an integer number. First we formulate
these statements (for a natural or an integer number, addition on the left or on the right, addition
or subtraction) using `function.commute`, then reformulate as `simp` lemmas `map_int_add` etc.
-/

theorem commute_nat_add (f : circle_deg1_lift) (n : ℕ) : function.commute (⇑f) (Add.add ↑n) := sorry

theorem commute_add_nat (f : circle_deg1_lift) (n : ℕ) : function.commute ⇑f fun (x : ℝ) => x + ↑n := sorry

theorem commute_sub_nat (f : circle_deg1_lift) (n : ℕ) : function.commute ⇑f fun (x : ℝ) => x - ↑n := sorry

theorem commute_add_int (f : circle_deg1_lift) (n : ℤ) : function.commute ⇑f fun (x : ℝ) => x + ↑n := sorry

theorem commute_int_add (f : circle_deg1_lift) (n : ℤ) : function.commute (⇑f) (Add.add ↑n) := sorry

theorem commute_sub_int (f : circle_deg1_lift) (n : ℤ) : function.commute ⇑f fun (x : ℝ) => x - ↑n := sorry

@[simp] theorem map_int_add (f : circle_deg1_lift) (m : ℤ) (x : ℝ) : coe_fn f (↑m + x) = ↑m + coe_fn f x :=
  commute_int_add f m x

@[simp] theorem map_add_int (f : circle_deg1_lift) (x : ℝ) (m : ℤ) : coe_fn f (x + ↑m) = coe_fn f x + ↑m :=
  commute_add_int f m x

@[simp] theorem map_sub_int (f : circle_deg1_lift) (x : ℝ) (n : ℤ) : coe_fn f (x - ↑n) = coe_fn f x - ↑n :=
  commute_sub_int f n x

@[simp] theorem map_add_nat (f : circle_deg1_lift) (x : ℝ) (n : ℕ) : coe_fn f (x + ↑n) = coe_fn f x + ↑n :=
  map_add_int f x ↑n

@[simp] theorem map_nat_add (f : circle_deg1_lift) (n : ℕ) (x : ℝ) : coe_fn f (↑n + x) = ↑n + coe_fn f x :=
  map_int_add f (↑n) x

@[simp] theorem map_sub_nat (f : circle_deg1_lift) (x : ℝ) (n : ℕ) : coe_fn f (x - ↑n) = coe_fn f x - ↑n :=
  map_sub_int f x ↑n

theorem map_int_of_map_zero (f : circle_deg1_lift) (n : ℤ) : coe_fn f ↑n = coe_fn f 0 + ↑n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn f ↑n = coe_fn f 0 + ↑n)) (Eq.symm (map_add_int f 0 n))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn f ↑n = coe_fn f (0 + ↑n))) (zero_add ↑n))) (Eq.refl (coe_fn f ↑n)))

@[simp] theorem map_fract_sub_fract_eq (f : circle_deg1_lift) (x : ℝ) : coe_fn f (fract x) - fract x = coe_fn f x - x := sorry

/-!
### Pointwise order on circle maps
-/

/-- Monotone circle maps form a lattice with respect to the pointwise order -/
protected instance lattice : lattice circle_deg1_lift :=
  lattice.mk (fun (f g : circle_deg1_lift) => mk (fun (x : ℝ) => max (coe_fn f x) (coe_fn g x)) sorry sorry)
    (fun (f g : circle_deg1_lift) => ∀ (x : ℝ), coe_fn f x ≤ coe_fn g x)
    (semilattice_sup.lt._default fun (f g : circle_deg1_lift) => ∀ (x : ℝ), coe_fn f x ≤ coe_fn g x) sorry sorry sorry
    sorry sorry sorry (fun (f g : circle_deg1_lift) => mk (fun (x : ℝ) => min (coe_fn f x) (coe_fn g x)) sorry sorry)
    sorry sorry sorry

@[simp] theorem sup_apply (f : circle_deg1_lift) (g : circle_deg1_lift) (x : ℝ) : coe_fn (f ⊔ g) x = max (coe_fn f x) (coe_fn g x) :=
  rfl

@[simp] theorem inf_apply (f : circle_deg1_lift) (g : circle_deg1_lift) (x : ℝ) : coe_fn (f ⊓ g) x = min (coe_fn f x) (coe_fn g x) :=
  rfl

theorem iterate_monotone (n : ℕ) : monotone fun (f : circle_deg1_lift) => nat.iterate (⇑f) n :=
  fun (f g : circle_deg1_lift) (h : f ≤ g) => monotone.iterate_le_of_le (circle_deg1_lift.monotone f) h n

theorem iterate_mono {f : circle_deg1_lift} {g : circle_deg1_lift} (h : f ≤ g) (n : ℕ) : nat.iterate (⇑f) n ≤ nat.iterate (⇑g) n :=
  iterate_monotone n h

theorem pow_mono {f : circle_deg1_lift} {g : circle_deg1_lift} (h : f ≤ g) (n : ℕ) : f ^ n ≤ g ^ n := sorry

theorem pow_monotone (n : ℕ) : monotone fun (f : circle_deg1_lift) => f ^ n :=
  fun (f g : circle_deg1_lift) (h : f ≤ g) => pow_mono h n

/-!
### Estimates on `(f * g) 0`

We prove the estimates `f 0 + ⌊g 0⌋ ≤ f (g 0) ≤ f 0 + ⌈g 0⌉` and some corollaries with added/removed
floors and ceils.

We also prove that for two semiconjugate maps `g₁`, `g₂`, the distance between `g₁ 0` and `g₂ 0`
is less than two.
-/

theorem map_le_of_map_zero (f : circle_deg1_lift) (x : ℝ) : coe_fn f x ≤ coe_fn f 0 + ↑(ceil x) :=
  trans_rel_left LessEq (circle_deg1_lift.monotone f (le_ceil x)) (map_int_of_map_zero f (ceil x))

theorem map_map_zero_le (f : circle_deg1_lift) (g : circle_deg1_lift) : coe_fn f (coe_fn g 0) ≤ coe_fn f 0 + ↑(ceil (coe_fn g 0)) :=
  map_le_of_map_zero f (coe_fn g 0)

theorem floor_map_map_zero_le (f : circle_deg1_lift) (g : circle_deg1_lift) : floor (coe_fn f (coe_fn g 0)) ≤ floor (coe_fn f 0) + ceil (coe_fn g 0) :=
  trans_rel_left LessEq (floor_mono (map_map_zero_le f g)) (floor_add_int (coe_fn f 0) (ceil (coe_fn g 0)))

theorem ceil_map_map_zero_le (f : circle_deg1_lift) (g : circle_deg1_lift) : ceil (coe_fn f (coe_fn g 0)) ≤ ceil (coe_fn f 0) + ceil (coe_fn g 0) :=
  trans_rel_left LessEq (ceil_mono (map_map_zero_le f g)) (ceil_add_int (coe_fn f 0) (ceil (coe_fn g 0)))

theorem map_map_zero_lt (f : circle_deg1_lift) (g : circle_deg1_lift) : coe_fn f (coe_fn g 0) < coe_fn f 0 + coe_fn g 0 + 1 :=
  trans_rel_left Less (lt_of_le_of_lt (map_map_zero_le f g) (add_lt_add_left (ceil_lt_add_one (coe_fn g 0)) (coe_fn f 0)))
    (Eq.symm (add_assoc (coe_fn f 0) (coe_fn g 0) 1))

theorem le_map_of_map_zero (f : circle_deg1_lift) (x : ℝ) : coe_fn f 0 + ↑(floor x) ≤ coe_fn f x :=
  trans_rel_right LessEq (Eq.symm (map_int_of_map_zero f (floor x))) (circle_deg1_lift.monotone f (floor_le x))

theorem le_map_map_zero (f : circle_deg1_lift) (g : circle_deg1_lift) : coe_fn f 0 + ↑(floor (coe_fn g 0)) ≤ coe_fn f (coe_fn g 0) :=
  le_map_of_map_zero f (coe_fn g 0)

theorem le_floor_map_map_zero (f : circle_deg1_lift) (g : circle_deg1_lift) : floor (coe_fn f 0) + floor (coe_fn g 0) ≤ floor (coe_fn f (coe_fn g 0)) :=
  trans_rel_right LessEq (Eq.symm (floor_add_int (coe_fn f 0) (floor (coe_fn g 0)))) (floor_mono (le_map_map_zero f g))

theorem le_ceil_map_map_zero (f : circle_deg1_lift) (g : circle_deg1_lift) : ceil (coe_fn f 0) + floor (coe_fn g 0) ≤ ceil (coe_fn (f * g) 0) :=
  trans_rel_right LessEq (Eq.symm (ceil_add_int (coe_fn f 0) (floor (coe_fn g 0)))) (ceil_mono (le_map_map_zero f g))

theorem lt_map_map_zero (f : circle_deg1_lift) (g : circle_deg1_lift) : coe_fn f 0 + coe_fn g 0 - 1 < coe_fn f (coe_fn g 0) := sorry

theorem dist_map_map_zero_lt (f : circle_deg1_lift) (g : circle_deg1_lift) : dist (coe_fn f 0 + coe_fn g 0) (coe_fn f (coe_fn g 0)) < 1 := sorry

theorem dist_map_zero_lt_of_semiconj {f : circle_deg1_lift} {g₁ : circle_deg1_lift} {g₂ : circle_deg1_lift} (h : function.semiconj ⇑f ⇑g₁ ⇑g₂) : dist (coe_fn g₁ 0) (coe_fn g₂ 0) < bit0 1 := sorry

theorem dist_map_zero_lt_of_semiconj_by {f : circle_deg1_lift} {g₁ : circle_deg1_lift} {g₂ : circle_deg1_lift} (h : semiconj_by f g₁ g₂) : dist (coe_fn g₁ 0) (coe_fn g₂ 0) < bit0 1 :=
  dist_map_zero_lt_of_semiconj (iff.mp semiconj_by_iff_semiconj h)

/-!
### Limits at infinities and continuity
-/

protected theorem tendsto_at_bot (f : circle_deg1_lift) : filter.tendsto (⇑f) filter.at_bot filter.at_bot := sorry

protected theorem tendsto_at_top (f : circle_deg1_lift) : filter.tendsto (⇑f) filter.at_top filter.at_top := sorry

theorem continuous_iff_surjective (f : circle_deg1_lift) : continuous ⇑f ↔ function.surjective ⇑f := sorry

/-!
### Estimates on `(f^n) x`

If we know that `f x` is `≤`/`<`/`≥`/`>`/`=` to `x + m`, then we have a similar estimate on
`f^[n] x` and `x + n * m`.

For `≤`, `≥`, and `=` we formulate both `of` (implication) and `iff` versions because implications
work for `n = 0`. For `<` and `>` we formulate only `iff` versions.
-/

theorem iterate_le_of_map_le_add_int (f : circle_deg1_lift) {x : ℝ} {m : ℤ} (h : coe_fn f x ≤ x + ↑m) (n : ℕ) : nat.iterate (⇑f) n x ≤ x + ↑n * ↑m := sorry

theorem le_iterate_of_add_int_le_map (f : circle_deg1_lift) {x : ℝ} {m : ℤ} (h : x + ↑m ≤ coe_fn f x) (n : ℕ) : x + ↑n * ↑m ≤ nat.iterate (⇑f) n x := sorry

theorem iterate_eq_of_map_eq_add_int (f : circle_deg1_lift) {x : ℝ} {m : ℤ} (h : coe_fn f x = x + ↑m) (n : ℕ) : nat.iterate (⇑f) n x = x + ↑n * ↑m := sorry

theorem iterate_pos_le_iff (f : circle_deg1_lift) {x : ℝ} {m : ℤ} {n : ℕ} (hn : 0 < n) : nat.iterate (⇑f) n x ≤ x + ↑n * ↑m ↔ coe_fn f x ≤ x + ↑m := sorry

theorem iterate_pos_lt_iff (f : circle_deg1_lift) {x : ℝ} {m : ℤ} {n : ℕ} (hn : 0 < n) : nat.iterate (⇑f) n x < x + ↑n * ↑m ↔ coe_fn f x < x + ↑m := sorry

theorem iterate_pos_eq_iff (f : circle_deg1_lift) {x : ℝ} {m : ℤ} {n : ℕ} (hn : 0 < n) : nat.iterate (⇑f) n x = x + ↑n * ↑m ↔ coe_fn f x = x + ↑m := sorry

theorem le_iterate_pos_iff (f : circle_deg1_lift) {x : ℝ} {m : ℤ} {n : ℕ} (hn : 0 < n) : x + ↑n * ↑m ≤ nat.iterate (⇑f) n x ↔ x + ↑m ≤ coe_fn f x := sorry

theorem lt_iterate_pos_iff (f : circle_deg1_lift) {x : ℝ} {m : ℤ} {n : ℕ} (hn : 0 < n) : x + ↑n * ↑m < nat.iterate (⇑f) n x ↔ x + ↑m < coe_fn f x := sorry

theorem mul_floor_map_zero_le_floor_iterate_zero (f : circle_deg1_lift) (n : ℕ) : ↑n * floor (coe_fn f 0) ≤ floor (nat.iterate (⇑f) n 0) := sorry

/-!
### Definition of translation number
-/

/-- An auxiliary sequence used to define the translation number. -/
def transnum_aux_seq (f : circle_deg1_lift) (n : ℕ) : ℝ :=
  coe_fn (f ^ bit0 1 ^ n) 0 / bit0 1 ^ n

/-- The translation number of a `circle_deg1_lift`, $τ(f)=\lim_{n→∞}\frac{f^n(x)-x}{n}$. We use
an auxiliary sequence `\frac{f^{2^n}(0)}{2^n}` to define `τ(f)` because some proofs are simpler
this way. -/
def translation_number (f : circle_deg1_lift) : ℝ :=
  lim filter.at_top (transnum_aux_seq f)

-- TODO: choose two different symbols for `circle_deg1_lift.translation_number` and the future

-- `circle_mono_homeo.rotation_number`, then make them `localized notation`s

theorem transnum_aux_seq_def (f : circle_deg1_lift) : transnum_aux_seq f = fun (n : ℕ) => coe_fn (f ^ bit0 1 ^ n) 0 / bit0 1 ^ n :=
  rfl

theorem translation_number_eq_of_tendsto_aux (f : circle_deg1_lift) {τ' : ℝ} (h : filter.tendsto (transnum_aux_seq f) filter.at_top (nhds τ')) : translation_number f = τ' :=
  filter.tendsto.lim_eq h

theorem translation_number_eq_of_tendsto₀ (f : circle_deg1_lift) {τ' : ℝ} (h : filter.tendsto (fun (n : ℕ) => nat.iterate (⇑f) n 0 / ↑n) filter.at_top (nhds τ')) : translation_number f = τ' := sorry

theorem translation_number_eq_of_tendsto₀' (f : circle_deg1_lift) {τ' : ℝ} (h : filter.tendsto (fun (n : ℕ) => nat.iterate (⇑f) (n + 1) 0 / (↑n + 1)) filter.at_top (nhds τ')) : translation_number f = τ' :=
  translation_number_eq_of_tendsto₀ f (iff.mp (filter.tendsto_add_at_top_iff_nat 1) h)

theorem transnum_aux_seq_zero (f : circle_deg1_lift) : transnum_aux_seq f 0 = coe_fn f 0 := sorry

theorem transnum_aux_seq_dist_lt (f : circle_deg1_lift) (n : ℕ) : dist (transnum_aux_seq f n) (transnum_aux_seq f (n + 1)) < 1 / bit0 1 / bit0 1 ^ n := sorry

theorem tendsto_translation_number_aux (f : circle_deg1_lift) : filter.tendsto (transnum_aux_seq f) filter.at_top (nhds (translation_number f)) :=
  cauchy_seq.tendsto_lim (cauchy_seq_of_le_geometric_two 1 fun (n : ℕ) => le_of_lt (transnum_aux_seq_dist_lt f n))

theorem dist_map_zero_translation_number_le (f : circle_deg1_lift) : dist (coe_fn f 0) (translation_number f) ≤ 1 :=
  transnum_aux_seq_zero f ▸
    dist_le_of_le_geometric_two_of_tendsto₀ 1 (fun (n : ℕ) => le_of_lt (transnum_aux_seq_dist_lt f n))
      (tendsto_translation_number_aux f)

theorem tendsto_translation_number_of_dist_bounded_aux (f : circle_deg1_lift) (x : ℕ → ℝ) (C : ℝ) (H : ∀ (n : ℕ), dist (coe_fn (f ^ n) 0) (x n) ≤ C) : filter.tendsto (fun (n : ℕ) => x (bit0 1 ^ n) / bit0 1 ^ n) filter.at_top (nhds (translation_number f)) := sorry

theorem translation_number_eq_of_dist_bounded {f : circle_deg1_lift} {g : circle_deg1_lift} (C : ℝ) (H : ∀ (n : ℕ), dist (coe_fn (f ^ n) 0) (coe_fn (g ^ n) 0) ≤ C) : translation_number f = translation_number g :=
  Eq.symm
    (translation_number_eq_of_tendsto_aux g
      (tendsto_translation_number_of_dist_bounded_aux f (fun (n : ℕ) => coe_fn (g ^ n) 0) C H))

@[simp] theorem translation_number_one : translation_number 1 = 0 := sorry

theorem translation_number_eq_of_semiconj_by {f : circle_deg1_lift} {g₁ : circle_deg1_lift} {g₂ : circle_deg1_lift} (H : semiconj_by f g₁ g₂) : translation_number g₁ = translation_number g₂ :=
  translation_number_eq_of_dist_bounded (bit0 1)
    fun (n : ℕ) => le_of_lt (dist_map_zero_lt_of_semiconj_by (semiconj_by.pow_right H n))

theorem translation_number_eq_of_semiconj {f : circle_deg1_lift} {g₁ : circle_deg1_lift} {g₂ : circle_deg1_lift} (H : function.semiconj ⇑f ⇑g₁ ⇑g₂) : translation_number g₁ = translation_number g₂ :=
  translation_number_eq_of_semiconj_by (iff.mpr semiconj_by_iff_semiconj H)

theorem translation_number_mul_of_commute {f : circle_deg1_lift} {g : circle_deg1_lift} (h : commute f g) : translation_number (f * g) = translation_number f + translation_number g := sorry

@[simp] theorem translation_number_units_inv (f : units circle_deg1_lift) : translation_number ↑(f⁻¹) = -translation_number ↑f := sorry

@[simp] theorem translation_number_pow (f : circle_deg1_lift) (n : ℕ) : translation_number (f ^ n) = ↑n * translation_number f := sorry

@[simp] theorem translation_number_gpow (f : units circle_deg1_lift) (n : ℤ) : translation_number ↑(f ^ n) = ↑n * translation_number ↑f := sorry

@[simp] theorem translation_number_conj_eq (f : units circle_deg1_lift) (g : circle_deg1_lift) : translation_number (↑f * g * ↑(f⁻¹)) = translation_number g :=
  Eq.symm (translation_number_eq_of_semiconj_by (units.mk_semiconj_by f g))

@[simp] theorem translation_number_conj_eq' (f : units circle_deg1_lift) (g : circle_deg1_lift) : translation_number (↑(f⁻¹) * g * ↑f) = translation_number g :=
  translation_number_conj_eq (f⁻¹) g

theorem dist_pow_map_zero_mul_translation_number_le (f : circle_deg1_lift) (n : ℕ) : dist (coe_fn (f ^ n) 0) (↑n * translation_number f) ≤ 1 :=
  translation_number_pow f n ▸ dist_map_zero_translation_number_le (f ^ n)

theorem tendsto_translation_number₀' (f : circle_deg1_lift) : filter.tendsto (fun (n : ℕ) => coe_fn (f ^ (n + 1)) 0 / (↑n + 1)) filter.at_top (nhds (translation_number f)) := sorry

theorem tendsto_translation_number₀ (f : circle_deg1_lift) : filter.tendsto (fun (n : ℕ) => coe_fn (f ^ n) 0 / ↑n) filter.at_top (nhds (translation_number f)) :=
  iff.mp (filter.tendsto_add_at_top_iff_nat 1) (tendsto_translation_number₀' f)

/-- For any `x : ℝ` the sequence $\frac{f^n(x)-x}{n}$ tends to the translation number of `f`.
In particular, this limit does not depend on `x`. -/
theorem tendsto_translation_number (f : circle_deg1_lift) (x : ℝ) : filter.tendsto (fun (n : ℕ) => (coe_fn (f ^ n) x - x) / ↑n) filter.at_top (nhds (translation_number f)) := sorry

theorem tendsto_translation_number' (f : circle_deg1_lift) (x : ℝ) : filter.tendsto (fun (n : ℕ) => (coe_fn (f ^ (n + 1)) x - x) / (↑n + 1)) filter.at_top (nhds (translation_number f)) :=
  iff.mpr (filter.tendsto_add_at_top_iff_nat 1) (tendsto_translation_number f x)

theorem translation_number_mono : monotone translation_number :=
  fun (f g : circle_deg1_lift) (h : f ≤ g) =>
    le_of_tendsto_of_tendsto' (tendsto_translation_number₀ f) (tendsto_translation_number₀ g)
      fun (n : ℕ) => div_le_div_of_le_of_nonneg (pow_mono h n 0) (nat.cast_nonneg n)

theorem translation_number_translate (x : ℝ) : translation_number ↑(coe_fn translate (coe_fn multiplicative.of_add x)) = x := sorry

theorem translation_number_le_of_le_add (f : circle_deg1_lift) {z : ℝ} (hz : ∀ (x : ℝ), coe_fn f x ≤ x + z) : translation_number f ≤ z :=
  translation_number_translate z ▸ translation_number_mono fun (x : ℝ) => trans_rel_left LessEq (hz x) (add_comm x z)

theorem le_translation_number_of_add_le (f : circle_deg1_lift) {z : ℝ} (hz : ∀ (x : ℝ), x + z ≤ coe_fn f x) : z ≤ translation_number f := sorry

theorem translation_number_le_of_le_add_int (f : circle_deg1_lift) {x : ℝ} {m : ℤ} (h : coe_fn f x ≤ x + ↑m) : translation_number f ≤ ↑m := sorry

theorem translation_number_le_of_le_add_nat (f : circle_deg1_lift) {x : ℝ} {m : ℕ} (h : coe_fn f x ≤ x + ↑m) : translation_number f ≤ ↑m :=
  translation_number_le_of_le_add_int f h

theorem le_translation_number_of_add_int_le (f : circle_deg1_lift) {x : ℝ} {m : ℤ} (h : x + ↑m ≤ coe_fn f x) : ↑m ≤ translation_number f := sorry

theorem le_translation_number_of_add_nat_le (f : circle_deg1_lift) {x : ℝ} {m : ℕ} (h : x + ↑m ≤ coe_fn f x) : ↑m ≤ translation_number f :=
  le_translation_number_of_add_int_le f h

/-- If `f x - x` is an integer number `m` for some point `x`, then `τ f = m`.
On the circle this means that a map with a fixed point has rotation number zero. -/
theorem translation_number_of_eq_add_int (f : circle_deg1_lift) {x : ℝ} {m : ℤ} (h : coe_fn f x = x + ↑m) : translation_number f = ↑m :=
  le_antisymm (translation_number_le_of_le_add_int f (le_of_eq h))
    (le_translation_number_of_add_int_le f (le_of_eq (Eq.symm h)))

theorem floor_sub_le_translation_number (f : circle_deg1_lift) (x : ℝ) : ↑(floor (coe_fn f x - x)) ≤ translation_number f :=
  le_translation_number_of_add_int_le f (iff.mp le_sub_iff_add_le' (floor_le (coe_fn f x - x)))

theorem translation_number_le_ceil_sub (f : circle_deg1_lift) (x : ℝ) : translation_number f ≤ ↑(ceil (coe_fn f x - x)) :=
  translation_number_le_of_le_add_int f (iff.mp sub_le_iff_le_add' (le_ceil (coe_fn f x - x)))

theorem map_lt_of_translation_number_lt_int (f : circle_deg1_lift) {n : ℤ} (h : translation_number f < ↑n) (x : ℝ) : coe_fn f x < x + ↑n :=
  iff.mp not_le (mt (le_translation_number_of_add_int_le f) (iff.mpr not_le h))

theorem map_lt_of_translation_number_lt_nat (f : circle_deg1_lift) {n : ℕ} (h : translation_number f < ↑n) (x : ℝ) : coe_fn f x < x + ↑n :=
  map_lt_of_translation_number_lt_int f h x

theorem map_lt_add_floor_translation_number_add_one (f : circle_deg1_lift) (x : ℝ) : coe_fn f x < x + ↑(floor (translation_number f)) + 1 := sorry

theorem map_lt_add_translation_number_add_one (f : circle_deg1_lift) (x : ℝ) : coe_fn f x < x + translation_number f + 1 :=
  lt_of_lt_of_le (map_lt_add_floor_translation_number_add_one f x)
    (add_le_add (id (add_le_add (le_refl x) (id (floor_le (translation_number f))))) (le_refl 1))

theorem lt_map_of_int_lt_translation_number (f : circle_deg1_lift) {n : ℤ} (h : ↑n < translation_number f) (x : ℝ) : x + ↑n < coe_fn f x :=
  iff.mp not_le (mt (translation_number_le_of_le_add_int f) (iff.mpr not_le h))

theorem lt_map_of_nat_lt_translation_number (f : circle_deg1_lift) {n : ℕ} (h : ↑n < translation_number f) (x : ℝ) : x + ↑n < coe_fn f x :=
  lt_map_of_int_lt_translation_number f h x

/-- If `f^n x - x`, `n > 0`, is an integer number `m` for some point `x`, then
`τ f = m / n`. On the circle this means that a map with a periodic orbit has
a rational rotation number. -/
theorem translation_number_of_map_pow_eq_add_int (f : circle_deg1_lift) {x : ℝ} {n : ℕ} {m : ℤ} (h : coe_fn (f ^ n) x = x + ↑m) (hn : 0 < n) : translation_number f = ↑m / ↑n := sorry

/-- If a predicate depends only on `f x - x` and holds for all `0 ≤ x ≤ 1`,
then it holds for all `x`. -/
theorem forall_map_sub_of_Icc (f : circle_deg1_lift) (P : ℝ → Prop) (h : ∀ (x : ℝ), x ∈ set.Icc 0 1 → P (coe_fn f x - x)) (x : ℝ) : P (coe_fn f x - x) :=
  map_fract_sub_fract_eq f x ▸ h (fract x) { left := fract_nonneg x, right := le_of_lt (fract_lt_one x) }

theorem translation_number_lt_of_forall_lt_add (f : circle_deg1_lift) (hf : continuous ⇑f) {z : ℝ} (hz : ∀ (x : ℝ), coe_fn f x < x + z) : translation_number f < z := sorry

theorem lt_translation_number_of_forall_add_lt (f : circle_deg1_lift) (hf : continuous ⇑f) {z : ℝ} (hz : ∀ (x : ℝ), x + z < coe_fn f x) : z < translation_number f := sorry

/-- If `f` is a continuous monotone map `ℝ → ℝ`, `f (x + 1) = f x + 1`, then there exists `x`
such that `f x = x + τ f`. -/
theorem exists_eq_add_translation_number (f : circle_deg1_lift) (hf : continuous ⇑f) : ∃ (x : ℝ), coe_fn f x = x + translation_number f := sorry

theorem translation_number_eq_int_iff (f : circle_deg1_lift) (hf : continuous ⇑f) {m : ℤ} : translation_number f = ↑m ↔ ∃ (x : ℝ), coe_fn f x = x + ↑m := sorry

theorem continuous_pow (f : circle_deg1_lift) (hf : continuous ⇑f) (n : ℕ) : continuous ⇑(f ^ n) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (continuous ⇑(f ^ n))) (coe_pow f n))) (continuous.iterate hf n)

theorem translation_number_eq_rat_iff (f : circle_deg1_lift) (hf : continuous ⇑f) {m : ℤ} {n : ℕ} (hn : 0 < n) : translation_number f = ↑m / ↑n ↔ ∃ (x : ℝ), coe_fn (f ^ n) x = x + ↑m := sorry

/-- Consider two actions `f₁ f₂ : G →* circle_deg1_lift` of a group on the real line by lifts of
orientation preserving circle homeomorphisms. Suppose that for each `g : G` the homeomorphisms
`f₁ g` and `f₂ g` have equal rotation numbers. Then there exists `F : circle_deg1_lift`  such that
`F * f₁ g = f₂ g * F` for all `g : G`.

This is a version of Proposition 5.4 from [Étienne Ghys, Groupes d'homeomorphismes du cercle et
cohomologie bornee][ghys87:groupes]. -/
theorem semiconj_of_group_action_of_forall_translation_number_eq {G : Type u_1} [group G] (f₁ : G →* circle_deg1_lift) (f₂ : G →* circle_deg1_lift) (h : ∀ (g : G), translation_number (coe_fn f₁ g) = translation_number (coe_fn f₂ g)) : ∃ (F : circle_deg1_lift), ∀ (g : G), function.semiconj ⇑F ⇑(coe_fn f₁ g) ⇑(coe_fn f₂ g) := sorry

/-- If two lifts of circle homeomorphisms have the same translation number, then they are
semiconjugate by a `circle_deg1_lift`. This version uses arguments `f₁ f₂ : units circle_deg1_lift`
to assume that `f₁` and `f₂` are homeomorphisms. -/
theorem units_semiconj_of_translation_number_eq {f₁ : units circle_deg1_lift} {f₂ : units circle_deg1_lift} (h : translation_number ↑f₁ = translation_number ↑f₂) : ∃ (F : circle_deg1_lift), function.semiconj ⇑F ⇑f₁ ⇑f₂ := sorry

/-- If two lifts of circle homeomorphisms have the same translation number, then they are
semiconjugate by a `circle_deg1_lift`. This version uses assumptions `is_unit f₁` and `is_unit f₂`
to assume that `f₁` and `f₂` are homeomorphisms. -/
theorem semiconj_of_is_unit_of_translation_number_eq {f₁ : circle_deg1_lift} {f₂ : circle_deg1_lift} (h₁ : is_unit f₁) (h₂ : is_unit f₂) (h : translation_number f₁ = translation_number f₂) : ∃ (F : circle_deg1_lift), function.semiconj ⇑F ⇑f₁ ⇑f₂ := sorry

/-- If two lifts of circle homeomorphisms have the same translation number, then they are
semiconjugate by a `circle_deg1_lift`. This version uses assumptions `bijective f₁` and
`bijective f₂` to assume that `f₁` and `f₂` are homeomorphisms. -/
theorem semiconj_of_bijective_of_translation_number_eq {f₁ : circle_deg1_lift} {f₂ : circle_deg1_lift} (h₁ : function.bijective ⇑f₁) (h₂ : function.bijective ⇑f₂) (h : translation_number f₁ = translation_number f₂) : ∃ (F : circle_deg1_lift), function.semiconj ⇑F ⇑f₁ ⇑f₂ :=
  semiconj_of_is_unit_of_translation_number_eq (iff.mpr is_unit_iff_bijective h₁) (iff.mpr is_unit_iff_bijective h₂) h

