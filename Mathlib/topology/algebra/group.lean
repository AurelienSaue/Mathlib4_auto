/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.order.filter.pointwise
import Mathlib.group_theory.quotient_group
import Mathlib.topology.algebra.monoid
import Mathlib.topology.homeomorph
import Mathlib.PostPort

universes w u l u_1 x u_2 

namespace Mathlib

/-!
# Theory of topological groups

This file defines the following typeclasses:

* `topological_group`, `topological_add_group`: multiplicative and additive topological groups,
  i.e., groups with continuous `(*)` and `(⁻¹)` / `(+)` and `(-)`;

* `has_continuous_sub G` means that `G` has a continuous subtraction operation.

There is an instance deducing `has_continuous_sub` from `topological_group` but we use a separate
typeclass because, e.g., `ℕ` and `ℝ≥0` have continuous subtraction but are not additive groups.

We also define `homeomorph` versions of several `equiv`s: `homeomorph.mul_left`,
`homeomorph.mul_right`, `homeomorph.inv`, and prove a few facts about neighbourhood filters in
groups.

## Tags

topological space, group, topological group
-/

/-!
### Groups with continuous multiplication

In this section we prove a few statements about groups with continuous `(*)`.
-/

/-- Multiplication from the left in a topological group as a homeomorphism. -/
protected def homeomorph.add_left {G : Type w} [topological_space G] [add_group G] [has_continuous_add G] (a : G) : G ≃ₜ G :=
  homeomorph.mk (equiv.mk (equiv.to_fun (equiv.add_left a)) (equiv.inv_fun (equiv.add_left a)) sorry sorry)

@[simp] theorem homeomorph.coe_mul_left {G : Type w} [topological_space G] [group G] [has_continuous_mul G] (a : G) : ⇑(homeomorph.mul_left a) = Mul.mul a :=
  rfl

theorem homeomorph.add_left_symm {G : Type w} [topological_space G] [add_group G] [has_continuous_add G] (a : G) : homeomorph.symm (homeomorph.add_left a) = homeomorph.add_left (-a) :=
  homeomorph.ext fun (x : G) => Eq.refl (coe_fn (homeomorph.symm (homeomorph.add_left a)) x)

theorem is_open_map_mul_left {G : Type w} [topological_space G] [group G] [has_continuous_mul G] (a : G) : is_open_map fun (x : G) => a * x :=
  homeomorph.is_open_map (homeomorph.mul_left a)

theorem is_closed_map_mul_left {G : Type w} [topological_space G] [group G] [has_continuous_mul G] (a : G) : is_closed_map fun (x : G) => a * x :=
  homeomorph.is_closed_map (homeomorph.mul_left a)

/-- Multiplication from the right in a topological group as a homeomorphism. -/
protected def homeomorph.mul_right {G : Type w} [topological_space G] [group G] [has_continuous_mul G] (a : G) : G ≃ₜ G :=
  homeomorph.mk (equiv.mk (equiv.to_fun (equiv.mul_right a)) (equiv.inv_fun (equiv.mul_right a)) sorry sorry)

theorem is_open_map_add_right {G : Type w} [topological_space G] [add_group G] [has_continuous_add G] (a : G) : is_open_map fun (x : G) => x + a :=
  homeomorph.is_open_map (homeomorph.add_right a)

theorem is_closed_map_mul_right {G : Type w} [topological_space G] [group G] [has_continuous_mul G] (a : G) : is_closed_map fun (x : G) => x * a :=
  homeomorph.is_closed_map (homeomorph.mul_right a)

theorem is_open_map_div_right {G : Type w} [topological_space G] [group G] [has_continuous_mul G] (a : G) : is_open_map fun (x : G) => x / a := sorry

theorem is_closed_map_div_right {G : Type w} [topological_space G] [group G] [has_continuous_mul G] (a : G) : is_closed_map fun (x : G) => x / a := sorry

/-!
### Topological groups

A topological group is a group in which the multiplication and inversion operations are
continuous. Topological additive groups are defined in the same way. Equivalently, we can require
that the division operation `λ x y, x * y⁻¹` (resp., subtraction) is continuous.
-/

/-- A topological (additive) group is a group in which the addition and negation operations are
continuous. -/
class topological_add_group (G : Type u) [topological_space G] [add_group G] 
extends has_continuous_add G
where
  continuous_neg : continuous fun (a : G) => -a

/-- A topological group is a group in which the multiplication and inversion operations are
continuous. -/
class topological_group (G : Type u_1) [topological_space G] [group G] 
extends has_continuous_mul G
where
  continuous_inv : continuous has_inv.inv

theorem continuous_on_neg {G : Type w} [topological_space G] [add_group G] [topological_add_group G] {s : set G} : continuous_on Neg.neg s :=
  continuous.continuous_on continuous_neg

theorem continuous_within_at_neg {G : Type w} [topological_space G] [add_group G] [topological_add_group G] {s : set G} {x : G} : continuous_within_at Neg.neg s x :=
  continuous.continuous_within_at continuous_neg

theorem continuous_at_inv {G : Type w} [topological_space G] [group G] [topological_group G] {x : G} : continuous_at has_inv.inv x :=
  continuous.continuous_at continuous_inv

theorem tendsto_neg {G : Type w} [topological_space G] [add_group G] [topological_add_group G] (a : G) : filter.tendsto Neg.neg (nhds a) (nhds (-a)) :=
  continuous_at_neg

/-- If a function converges to a value in a multiplicative topological group, then its inverse
converges to the inverse of this value. For the version in normed fields assuming additionally
that the limit is nonzero, use `tendsto.inv'`. -/
theorem filter.tendsto.inv {α : Type u} {G : Type w} [topological_space G] [group G] [topological_group G] {f : α → G} {l : filter α} {y : G} (h : filter.tendsto f l (nhds y)) : filter.tendsto (fun (x : α) => f x⁻¹) l (nhds (y⁻¹)) :=
  filter.tendsto.comp (continuous.tendsto continuous_inv y) h

theorem continuous.inv {α : Type u} {G : Type w} [topological_space G] [group G] [topological_group G] [topological_space α] {f : α → G} (hf : continuous f) : continuous fun (x : α) => f x⁻¹ :=
  continuous.comp continuous_inv hf

theorem continuous_on.inv {α : Type u} {G : Type w} [topological_space G] [group G] [topological_group G] [topological_space α] {f : α → G} {s : set α} (hf : continuous_on f s) : continuous_on (fun (x : α) => f x⁻¹) s :=
  continuous.comp_continuous_on continuous_inv hf

theorem continuous_within_at.inv {α : Type u} {G : Type w} [topological_space G] [group G] [topological_group G] [topological_space α] {f : α → G} {s : set α} {x : α} (hf : continuous_within_at f s x) : continuous_within_at (fun (x : α) => f x⁻¹) s x :=
  filter.tendsto.inv hf

protected instance prod.topological_add_group {G : Type w} {H : Type x} [topological_space G] [add_group G] [topological_add_group G] [topological_space H] [add_group H] [topological_add_group H] : topological_add_group (G × H) :=
  topological_add_group.mk (continuous.prod_map continuous_neg continuous_neg)

/-- Inversion in a topological group as a homeomorphism. -/
protected def homeomorph.neg (G : Type w) [topological_space G] [add_group G] [topological_add_group G] : G ≃ₜ G :=
  homeomorph.mk (equiv.mk (equiv.to_fun (equiv.neg G)) (equiv.inv_fun (equiv.neg G)) sorry sorry)

theorem nhds_zero_symm (G : Type w) [topological_space G] [add_group G] [topological_add_group G] : filter.comap Neg.neg (nhds 0) = nhds 0 :=
  Eq.trans (homeomorph.comap_nhds_eq (homeomorph.neg G) 0) (congr_arg nhds neg_zero)

/-- The map `(x, y) ↦ (x, xy)` as a homeomorphism. This is a shear mapping. -/
protected def homeomorph.shear_add_right (G : Type w) [topological_space G] [add_group G] [topological_add_group G] : G × G ≃ₜ G × G :=
  homeomorph.mk
    (equiv.mk (equiv.to_fun (equiv.prod_shear (equiv.refl G) equiv.add_left))
      (equiv.inv_fun (equiv.prod_shear (equiv.refl G) equiv.add_left)) sorry sorry)

@[simp] theorem homeomorph.shear_mul_right_coe (G : Type w) [topological_space G] [group G] [topological_group G] : ⇑(homeomorph.shear_mul_right G) = fun (z : G × G) => (prod.fst z, prod.fst z * prod.snd z) :=
  rfl

@[simp] theorem homeomorph.shear_mul_right_symm_coe (G : Type w) [topological_space G] [group G] [topological_group G] : ⇑(homeomorph.symm (homeomorph.shear_mul_right G)) = fun (z : G × G) => (prod.fst z, prod.fst z⁻¹ * prod.snd z) :=
  rfl

theorem inv_closure {G : Type w} [topological_space G] [group G] [topological_group G] (s : set G) : closure s⁻¹ = closure (s⁻¹) :=
  homeomorph.preimage_closure (homeomorph.inv G) s

theorem exists_nhds_half_neg {G : Type w} [topological_space G] [add_group G] [topological_add_group G] {s : set G} (hs : s ∈ nhds 0) : ∃ (V : set G), ∃ (H : V ∈ nhds 0), ∀ (v : G), v ∈ V → ∀ (w : G), w ∈ V → v - w ∈ s := sorry

theorem nhds_translation_mul_inv {G : Type w} [topological_space G] [group G] [topological_group G] (x : G) : filter.comap (fun (y : G) => y * (x⁻¹)) (nhds 1) = nhds x := sorry

@[simp] theorem map_mul_left_nhds {G : Type w} [topological_space G] [group G] [topological_group G] (x : G) (y : G) : filter.map (Mul.mul x) (nhds y) = nhds (x * y) :=
  homeomorph.map_nhds_eq (homeomorph.mul_left x) y

theorem map_mul_left_nhds_one {G : Type w} [topological_space G] [group G] [topological_group G] (x : G) : filter.map (Mul.mul x) (nhds 1) = nhds x := sorry

theorem topological_group.ext {G : Type u_1} [group G] {t : topological_space G} {t' : topological_space G} (tg : topological_group G) (tg' : topological_group G) (h : nhds 1 = nhds 1) : t = t' := sorry

theorem topological_group.of_nhds_aux {G : Type u_1} [group G] [topological_space G] (hinv : filter.tendsto (fun (x : G) => x⁻¹) (nhds 1) (nhds 1)) (hleft : ∀ (x₀ : G), nhds x₀ = filter.map (fun (x : G) => x₀ * x) (nhds 1)) (hconj : ∀ (x₀ : G), filter.map (fun (x : G) => x₀ * x * (x₀⁻¹)) (nhds 1) ≤ nhds 1) : continuous fun (x : G) => x⁻¹ := sorry

theorem topological_add_group.of_nhds_zero' {G : Type (max u_1 u_2)} [add_group G] [topological_space G] (hmul : filter.tendsto (function.uncurry Add.add) (filter.prod (nhds 0) (nhds 0)) (nhds 0)) (hinv : filter.tendsto (fun (x : G) => -x) (nhds 0) (nhds 0)) (hleft : ∀ (x₀ : G), nhds x₀ = filter.map (fun (x : G) => x₀ + x) (nhds 0)) (hright : ∀ (x₀ : G), nhds x₀ = filter.map (fun (x : G) => x + x₀) (nhds 0)) : topological_add_group G := sorry

theorem topological_add_group.of_nhds_zero {G : Type (max u_1 u_2)} [add_group G] [topological_space G] (hmul : filter.tendsto (function.uncurry Add.add) (filter.prod (nhds 0) (nhds 0)) (nhds 0)) (hinv : filter.tendsto (fun (x : G) => -x) (nhds 0) (nhds 0)) (hleft : ∀ (x₀ : G), nhds x₀ = filter.map (fun (x : G) => x₀ + x) (nhds 0)) (hconj : ∀ (x₀ : G), filter.tendsto (fun (x : G) => x₀ + x + -x₀) (nhds 0) (nhds 0)) : topological_add_group G :=
  topological_add_group.mk (topological_add_group.of_nhds_aux hinv hleft hconj)

theorem topological_add_group.of_comm_of_nhds_zero {G : Type (max u_1 u_2)} [add_comm_group G] [topological_space G] (hmul : filter.tendsto (function.uncurry Add.add) (filter.prod (nhds 0) (nhds 0)) (nhds 0)) (hinv : filter.tendsto (fun (x : G) => -x) (nhds 0) (nhds 0)) (hleft : ∀ (x₀ : G), nhds x₀ = filter.map (fun (x : G) => x₀ + x) (nhds 0)) : topological_add_group G := sorry

protected instance quotient_group.quotient.topological_space {G : Type u_1} [group G] [topological_space G] (N : subgroup G) : topological_space (quotient_group.quotient N) :=
  quotient.topological_space

theorem quotient_group.is_open_map_coe {G : Type w} [topological_space G] [group G] [topological_group G] (N : subgroup G) : is_open_map coe := sorry

protected instance topological_add_group_quotient {G : Type w} [topological_space G] [add_group G] [topological_add_group G] (N : add_subgroup G) [add_subgroup.normal N] : topological_add_group (quotient_add_group.quotient N) :=
  topological_add_group.mk
    (eq.mpr
      ((fun (f f_1 : quotient_add_group.quotient N → quotient_add_group.quotient N) (e_3 : f = f_1) =>
          congr_arg continuous e_3)
        Neg.neg (quotient.lift (coe ∘ fun (a : G) => -a) (quotient_add_group.div_inv_monoid._proof_5 N))
        (Eq.refl Neg.neg))
      (continuous_quotient_lift (quotient_add_group.div_inv_monoid._proof_5 N)
        (continuous.comp continuous_quot_mk continuous_neg)))

/-- A typeclass saying that `λ p : G × G, p.1 - p.2` is a continuous function. This property
automatically holds for topological additive groups but it also holds, e.g., for `ℝ≥0`. -/
class has_continuous_sub (G : Type u_1) [topological_space G] [Sub G] 
where
  continuous_sub : continuous fun (p : G × G) => prod.fst p - prod.snd p

protected instance topological_add_group.to_has_continuous_sub {G : Type w} [topological_space G] [add_group G] [topological_add_group G] : has_continuous_sub G :=
  has_continuous_sub.mk
    (eq.mpr
      (id
        ((fun (f f_1 : G × G → G) (e_3 : f = f_1) => congr_arg continuous e_3)
          (fun (p : G × G) => prod.fst p - prod.snd p) (fun (p : G × G) => prod.fst p + -prod.snd p)
          (funext fun (p : G × G) => sub_eq_add_neg (prod.fst p) (prod.snd p))))
      (continuous.add continuous_fst (continuous.neg continuous_snd)))

theorem filter.tendsto.sub {α : Type u} {G : Type w} [topological_space G] [Sub G] [has_continuous_sub G] {f : α → G} {g : α → G} {l : filter α} {a : G} {b : G} (hf : filter.tendsto f l (nhds a)) (hg : filter.tendsto g l (nhds b)) : filter.tendsto (fun (x : α) => f x - g x) l (nhds (a - b)) :=
  filter.tendsto.comp (continuous.tendsto continuous_sub (a, b)) (filter.tendsto.prod_mk_nhds hf hg)

theorem continuous.sub {α : Type u} {G : Type w} [topological_space G] [Sub G] [has_continuous_sub G] [topological_space α] {f : α → G} {g : α → G} (hf : continuous f) (hg : continuous g) : continuous fun (x : α) => f x - g x :=
  continuous.comp continuous_sub (continuous.prod_mk hf hg)

theorem continuous_within_at.sub {α : Type u} {G : Type w} [topological_space G] [Sub G] [has_continuous_sub G] [topological_space α] {f : α → G} {g : α → G} {s : set α} {x : α} (hf : continuous_within_at f s x) (hg : continuous_within_at g s x) : continuous_within_at (fun (x : α) => f x - g x) s x :=
  filter.tendsto.sub hf hg

theorem continuous_on.sub {α : Type u} {G : Type w} [topological_space G] [Sub G] [has_continuous_sub G] [topological_space α] {f : α → G} {g : α → G} {s : set α} (hf : continuous_on f s) (hg : continuous_on g s) : continuous_on (fun (x : α) => f x - g x) s :=
  fun (x : α) (hx : x ∈ s) => continuous_within_at.sub (hf x hx) (hg x hx)

theorem nhds_translation {G : Type w} [topological_space G] [add_group G] [topological_add_group G] (x : G) : filter.comap (fun (y : G) => y - x) (nhds 0) = nhds x := sorry

/-- additive group with a neighbourhood around 0.
Only used to construct a topology and uniform space.

This is currently only available for commutative groups, but it can be extended to
non-commutative groups too.
-/
class add_group_with_zero_nhd (G : Type u) 
extends add_comm_group G
where
  Z : filter G
  zero_Z : pure 0 ≤ Z
  sub_Z : filter.tendsto (fun (p : G × G) => prod.fst p - prod.snd p) (filter.prod Z Z) Z

namespace add_group_with_zero_nhd


protected instance topological_space (G : Type w) [add_group_with_zero_nhd G] : topological_space G :=
  topological_space.mk_of_nhds fun (a : G) => filter.map (fun (x : G) => x + a) (Z G)

theorem neg_Z {G : Type w} [add_group_with_zero_nhd G] : filter.tendsto (fun (a : G) => -a) (Z G) (Z G) := sorry

theorem add_Z {G : Type w} [add_group_with_zero_nhd G] : filter.tendsto (fun (p : G × G) => prod.fst p + prod.snd p) (filter.prod (Z G) (Z G)) (Z G) := sorry

theorem exists_Z_half {G : Type w} [add_group_with_zero_nhd G] {s : set G} (hs : s ∈ Z G) : ∃ (V : set G), ∃ (H : V ∈ Z G), ∀ (v : G), v ∈ V → ∀ (w : G), w ∈ V → v + w ∈ s := sorry

theorem nhds_eq {G : Type w} [add_group_with_zero_nhd G] (a : G) : nhds a = filter.map (fun (x : G) => x + a) (Z G) := sorry

theorem nhds_zero_eq_Z {G : Type w} [add_group_with_zero_nhd G] : nhds 0 = Z G := sorry

protected instance has_continuous_add {G : Type w} [add_group_with_zero_nhd G] : has_continuous_add G :=
  has_continuous_add.mk (iff.mpr continuous_iff_continuous_at fun (_x : G × G) => sorry)

protected instance topological_add_group {G : Type w} [add_group_with_zero_nhd G] : topological_add_group G := sorry

end add_group_with_zero_nhd


theorem is_open.add_left {G : Type w} [topological_space G] [add_group G] [topological_add_group G] {s : set G} {t : set G} : is_open t → is_open (s + t) :=
  fun (ht : is_open t) =>
    eq.mpr (id (Eq._oldrec (Eq.refl (is_open (s + t))) (Eq.symm set.Union_add_left_image)))
      (is_open_Union fun (a : G) => is_open_Union fun (ha : a ∈ s) => (fun (a : G) => is_open_map_add_left a t ht) a)

theorem is_open.add_right {G : Type w} [topological_space G] [add_group G] [topological_add_group G] {s : set G} {t : set G} : is_open s → is_open (s + t) :=
  fun (hs : is_open s) =>
    eq.mpr (id (Eq._oldrec (Eq.refl (is_open (s + t))) (Eq.symm set.Union_add_right_image)))
      (is_open_Union fun (a : G) => is_open_Union fun (ha : a ∈ t) => (fun (a : G) => is_open_map_add_right a s hs) a)

theorem topological_group.t1_space (G : Type w) [topological_space G] [group G] [topological_group G] (h : is_closed (singleton 1)) : t1_space G := sorry

theorem topological_group.regular_space (G : Type w) [topological_space G] [group G] [topological_group G] [t1_space G] : regular_space G := sorry

theorem topological_group.t2_space (G : Type w) [topological_space G] [group G] [topological_group G] [t1_space G] : t2_space G :=
  regular_space.t2_space G

/-! Some results about an open set containing the product of two sets in a topological group. -/

/-- Given a compact set `K` inside an open set `U`, there is a open neighborhood `V` of `1`
  such that `KV ⊆ U`. -/
theorem compact_open_separated_add {G : Type w} [topological_space G] [add_group G] [topological_add_group G] {K : set G} {U : set G} (hK : is_compact K) (hU : is_open U) (hKU : K ⊆ U) : ∃ (V : set G), is_open V ∧ 0 ∈ V ∧ K + V ⊆ U := sorry

/-- A compact set is covered by finitely many left multiplicative translates of a set
  with non-empty interior. -/
theorem compact_covered_by_add_left_translates {G : Type w} [topological_space G] [add_group G] [topological_add_group G] {K : set G} {V : set G} (hK : is_compact K) (hV : set.nonempty (interior V)) : ∃ (t : finset G), K ⊆ set.Union fun (g : G) => set.Union fun (H : g ∈ t) => (fun (h : G) => g + h) ⁻¹' V := sorry

/-- Every locally compact separable topological group is σ-compact.
  Note: this is not true if we drop the topological group hypothesis. -/
protected instance separable_locally_compact_group.sigma_compact_space {G : Type w} [topological_space G] [group G] [topological_group G] [topological_space.separable_space G] [locally_compact_space G] : sigma_compact_space G := sorry

theorem nhds_add {G : Type w} [topological_space G] [add_comm_group G] [topological_add_group G] (x : G) (y : G) : nhds (x + y) = nhds x + nhds y := sorry

theorem nhds_is_mul_hom {G : Type w} [topological_space G] [comm_group G] [topological_group G] : is_mul_hom fun (x : G) => nhds x :=
  is_mul_hom.mk fun (_x _x_1 : G) => nhds_mul _x _x_1

protected instance additive.topological_add_group {G : Type u_1} [h : topological_space G] [group G] [topological_group G] : topological_add_group (additive G) :=
  topological_add_group.mk continuous_inv

protected instance multiplicative.topological_group {G : Type u_1} [h : topological_space G] [add_group G] [topological_add_group G] : topological_group (multiplicative G) :=
  topological_group.mk continuous_neg

