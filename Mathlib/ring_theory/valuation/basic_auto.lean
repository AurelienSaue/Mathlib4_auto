/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Johan Commelin, Patrick Massot
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.linear_ordered_comm_group_with_zero
import Mathlib.algebra.group_power.default
import Mathlib.ring_theory.ideal.operations
import Mathlib.algebra.punit_instances
import Mathlib.PostPort

universes u_1 u_2 l u_3 u_4 

namespace Mathlib

/-!

# The basics of valuation theory.

The basic theory of valuations (non-archimedean norms) on a commutative ring,
following T. Wedhorn's unpublished notes “Adic Spaces” ([wedhorn_adic]).

The definition of a valuation we use here is Definition 1.22 of [wedhorn_adic].
A valuation on a ring `R` is a monoid homomorphism `v` to a linearly ordered
commutative group with zero, that in addition satisfies the following two axioms:
 * `v 0 = 0`
 * `∀ x y, v (x + y) ≤ max (v x) (v y)`

`valuation R Γ₀`is the type of valuations `R → Γ₀`, with a coercion to the underlying
function. If `v` is a valuation from `R` to `Γ₀` then the induced group
homomorphism `units(R) → Γ₀` is called `unit_map v`.

The equivalence "relation" `is_equiv v₁ v₂ : Prop` defined in 1.27 of [wedhorn_adic] is not strictly
speaking a relation, because `v₁ : valuation R Γ₁` and `v₂ : valuation R Γ₂` might
not have the same type. This corresponds in ZFC to the set-theoretic difficulty
that the class of all valuations (as `Γ₀` varies) on a ring `R` is not a set.
The "relation" is however reflexive, symmetric and transitive in the obvious
sense. Note that we use 1.27(iii) of [wedhorn_adic] as the definition of equivalence.

The support of a valuation `v : valuation R Γ₀` is `supp v`. If `J` is an ideal of `R`
with `h : J ⊆ supp v` then the induced valuation
on R / J = `ideal.quotient J` is `on_quot v h`.

## Main definitions

* `valuation R Γ₀`, the type of valuations on `R` with values in `Γ₀`
* `valuation.is_equiv`, the heterogeneous equivalence relation on valuations
* `valuation.supp`, the support of a valuation

-/

-- universes u u₀ u₁ u₂ -- v is used for valuations

/-- The type of Γ₀-valued valuations on R. -/
structure valuation (R : Type u_1) (Γ₀ : Type u_2) [linear_ordered_comm_group_with_zero Γ₀] [ring R]
    extends monoid_with_zero_hom R Γ₀ where
  map_add' : ∀ (x y : R), to_fun (x + y) ≤ max (to_fun x) (to_fun y)

/-- The `monoid_with_zero_hom` underlying a valuation. -/
namespace valuation


/-- A valuation is coerced to the underlying function R → Γ₀. -/
protected instance has_coe_to_fun (R : Type u_1) (Γ₀ : Type u_2)
    [linear_ordered_comm_group_with_zero Γ₀] [ring R] : has_coe_to_fun (valuation R Γ₀) :=
  has_coe_to_fun.mk (fun (_x : valuation R Γ₀) => R → Γ₀) to_fun

/-- A valuation is coerced to a monoid morphism R → Γ₀. -/
protected instance monoid_with_zero_hom.has_coe (R : Type u_1) (Γ₀ : Type u_2)
    [linear_ordered_comm_group_with_zero Γ₀] [ring R] :
    has_coe (valuation R Γ₀) (monoid_with_zero_hom R Γ₀) :=
  has_coe.mk to_monoid_with_zero_hom

@[simp] theorem coe_coe {R : Type u_1} {Γ₀ : Type u_2} [linear_ordered_comm_group_with_zero Γ₀]
    [ring R] (v : valuation R Γ₀) : ⇑↑v = ⇑v :=
  rfl

@[simp] theorem map_zero {R : Type u_1} {Γ₀ : Type u_2} [linear_ordered_comm_group_with_zero Γ₀]
    [ring R] (v : valuation R Γ₀) : coe_fn v 0 = 0 :=
  map_zero' v

@[simp] theorem map_one {R : Type u_1} {Γ₀ : Type u_2} [linear_ordered_comm_group_with_zero Γ₀]
    [ring R] (v : valuation R Γ₀) : coe_fn v 1 = 1 :=
  map_one' v

@[simp] theorem map_mul {R : Type u_1} {Γ₀ : Type u_2} [linear_ordered_comm_group_with_zero Γ₀]
    [ring R] (v : valuation R Γ₀) (x : R) (y : R) : coe_fn v (x * y) = coe_fn v x * coe_fn v y :=
  map_mul' v

@[simp] theorem map_add {R : Type u_1} {Γ₀ : Type u_2} [linear_ordered_comm_group_with_zero Γ₀]
    [ring R] (v : valuation R Γ₀) (x : R) (y : R) :
    coe_fn v (x + y) ≤ max (coe_fn v x) (coe_fn v y) :=
  map_add' v

theorem map_add_le {R : Type u_1} {Γ₀ : Type u_2} [linear_ordered_comm_group_with_zero Γ₀] [ring R]
    (v : valuation R Γ₀) {x : R} {y : R} {g : Γ₀} (hx : coe_fn v x ≤ g) (hy : coe_fn v y ≤ g) :
    coe_fn v (x + y) ≤ g :=
  le_trans (map_add v x y) (max_le hx hy)

theorem map_add_lt {R : Type u_1} {Γ₀ : Type u_2} [linear_ordered_comm_group_with_zero Γ₀] [ring R]
    (v : valuation R Γ₀) {x : R} {y : R} {g : Γ₀} (hx : coe_fn v x < g) (hy : coe_fn v y < g) :
    coe_fn v (x + y) < g :=
  lt_of_le_of_lt (map_add v x y) (max_lt hx hy)

theorem map_sum_le {R : Type u_1} {Γ₀ : Type u_2} [linear_ordered_comm_group_with_zero Γ₀] [ring R]
    (v : valuation R Γ₀) {ι : Type u_3} {s : finset ι} {f : ι → R} {g : Γ₀}
    (hf : ∀ (i : ι), i ∈ s → coe_fn v (f i) ≤ g) : coe_fn v (finset.sum s fun (i : ι) => f i) ≤ g :=
  sorry

theorem map_sum_lt {R : Type u_1} {Γ₀ : Type u_2} [linear_ordered_comm_group_with_zero Γ₀] [ring R]
    (v : valuation R Γ₀) {ι : Type u_3} {s : finset ι} {f : ι → R} {g : Γ₀} (hg : g ≠ 0)
    (hf : ∀ (i : ι), i ∈ s → coe_fn v (f i) < g) : coe_fn v (finset.sum s fun (i : ι) => f i) < g :=
  sorry

theorem map_sum_lt' {R : Type u_1} {Γ₀ : Type u_2} [linear_ordered_comm_group_with_zero Γ₀] [ring R]
    (v : valuation R Γ₀) {ι : Type u_3} {s : finset ι} {f : ι → R} {g : Γ₀} (hg : 0 < g)
    (hf : ∀ (i : ι), i ∈ s → coe_fn v (f i) < g) : coe_fn v (finset.sum s fun (i : ι) => f i) < g :=
  map_sum_lt v (ne_of_gt hg) hf

@[simp] theorem map_pow {R : Type u_1} {Γ₀ : Type u_2} [linear_ordered_comm_group_with_zero Γ₀]
    [ring R] (v : valuation R Γ₀) (x : R) (n : ℕ) : coe_fn v (x ^ n) = coe_fn v x ^ n :=
  monoid_hom.map_pow (monoid_with_zero_hom.to_monoid_hom (to_monoid_with_zero_hom v))

theorem ext {R : Type u_1} {Γ₀ : Type u_2} [linear_ordered_comm_group_with_zero Γ₀] [ring R]
    {v₁ : valuation R Γ₀} {v₂ : valuation R Γ₀} (h : ∀ (r : R), coe_fn v₁ r = coe_fn v₂ r) :
    v₁ = v₂ :=
  sorry

theorem ext_iff {R : Type u_1} {Γ₀ : Type u_2} [linear_ordered_comm_group_with_zero Γ₀] [ring R]
    {v₁ : valuation R Γ₀} {v₂ : valuation R Γ₀} : v₁ = v₂ ↔ ∀ (r : R), coe_fn v₁ r = coe_fn v₂ r :=
  { mp := fun (h : v₁ = v₂) (r : R) => congr_arg (fun {v₁ : valuation R Γ₀} => coe_fn v₁ r) h,
    mpr := ext }

-- The following definition is not an instance, because we have more than one `v` on a given `R`.

-- In addition, type class inference would not be able to infer `v`.

/-- A valuation gives a preorder on the underlying ring. -/
def to_preorder {R : Type u_1} {Γ₀ : Type u_2} [linear_ordered_comm_group_with_zero Γ₀] [ring R]
    (v : valuation R Γ₀) : preorder R :=
  preorder.lift ⇑v

/-- If `v` is a valuation on a division ring then `v(x) = 0` iff `x = 0`. -/
@[simp] theorem zero_iff {Γ₀ : Type u_2} [linear_ordered_comm_group_with_zero Γ₀] {K : Type u_1}
    [division_ring K] (v : valuation K Γ₀) {x : K} : coe_fn v x = 0 ↔ x = 0 :=
  monoid_with_zero_hom.map_eq_zero (to_monoid_with_zero_hom v)

theorem ne_zero_iff {Γ₀ : Type u_2} [linear_ordered_comm_group_with_zero Γ₀] {K : Type u_1}
    [division_ring K] (v : valuation K Γ₀) {x : K} : coe_fn v x ≠ 0 ↔ x ≠ 0 :=
  monoid_with_zero_hom.map_ne_zero (to_monoid_with_zero_hom v)

@[simp] theorem map_inv {Γ₀ : Type u_2} [linear_ordered_comm_group_with_zero Γ₀] {K : Type u_1}
    [division_ring K] (v : valuation K Γ₀) {x : K} : coe_fn v (x⁻¹) = (coe_fn v x⁻¹) :=
  monoid_with_zero_hom.map_inv' (to_monoid_with_zero_hom v) x

theorem map_units_inv {R : Type u_1} {Γ₀ : Type u_2} [linear_ordered_comm_group_with_zero Γ₀]
    [ring R] (v : valuation R Γ₀) (x : units R) : coe_fn v ↑(x⁻¹) = (coe_fn v ↑x⁻¹) :=
  monoid_hom.map_units_inv (monoid_with_zero_hom.to_monoid_hom (to_monoid_with_zero_hom v)) x

theorem unit_map_eq {R : Type u_1} {Γ₀ : Type u_2} [linear_ordered_comm_group_with_zero Γ₀] [ring R]
    (v : valuation R Γ₀) (u : units R) : ↑(coe_fn (units.map ↑v) u) = coe_fn v ↑u :=
  rfl

@[simp] theorem map_neg {R : Type u_1} {Γ₀ : Type u_2} [linear_ordered_comm_group_with_zero Γ₀]
    [ring R] (v : valuation R Γ₀) (x : R) : coe_fn v (-x) = coe_fn v x :=
  monoid_hom.map_neg (monoid_with_zero_hom.to_monoid_hom (to_monoid_with_zero_hom v)) x

theorem map_sub_swap {R : Type u_1} {Γ₀ : Type u_2} [linear_ordered_comm_group_with_zero Γ₀]
    [ring R] (v : valuation R Γ₀) (x : R) (y : R) : coe_fn v (x - y) = coe_fn v (y - x) :=
  monoid_hom.map_sub_swap (monoid_with_zero_hom.to_monoid_hom (to_monoid_with_zero_hom v)) x y

theorem map_sub_le_max {R : Type u_1} {Γ₀ : Type u_2} [linear_ordered_comm_group_with_zero Γ₀]
    [ring R] (v : valuation R Γ₀) (x : R) (y : R) :
    coe_fn v (x - y) ≤ max (coe_fn v x) (coe_fn v y) :=
  sorry

theorem map_add_of_distinct_val {R : Type u_1} {Γ₀ : Type u_2}
    [linear_ordered_comm_group_with_zero Γ₀] [ring R] (v : valuation R Γ₀) {x : R} {y : R}
    (h : coe_fn v x ≠ coe_fn v y) : coe_fn v (x + y) = max (coe_fn v x) (coe_fn v y) :=
  sorry

theorem map_eq_of_sub_lt {R : Type u_1} {Γ₀ : Type u_2} [linear_ordered_comm_group_with_zero Γ₀]
    [ring R] (v : valuation R Γ₀) {x : R} {y : R} (h : coe_fn v (y - x) < coe_fn v x) :
    coe_fn v y = coe_fn v x :=
  sorry

/-- A ring homomorphism S → R induces a map valuation R Γ₀ → valuation S Γ₀ -/
def comap {R : Type u_1} {Γ₀ : Type u_2} [linear_ordered_comm_group_with_zero Γ₀] [ring R]
    {S : Type u_3} [ring S] (f : S →+* R) (v : valuation R Γ₀) : valuation S Γ₀ :=
  mk (⇑v ∘ ⇑f) sorry sorry sorry sorry

@[simp] theorem comap_id {R : Type u_1} {Γ₀ : Type u_2} [linear_ordered_comm_group_with_zero Γ₀]
    [ring R] (v : valuation R Γ₀) : comap (ring_hom.id R) v = v :=
  ext fun (r : R) => rfl

theorem comap_comp {R : Type u_1} {Γ₀ : Type u_2} [linear_ordered_comm_group_with_zero Γ₀] [ring R]
    (v : valuation R Γ₀) {S₁ : Type u_3} {S₂ : Type u_4} [ring S₁] [ring S₂] (f : S₁ →+* S₂)
    (g : S₂ →+* R) : comap (ring_hom.comp g f) v = comap f (comap g v) :=
  ext fun (r : S₁) => rfl

/-- A ≤-preserving group homomorphism Γ₀ → Γ'₀ induces a map valuation R Γ₀ → valuation R Γ'₀. -/
def map {R : Type u_1} {Γ₀ : Type u_2} [linear_ordered_comm_group_with_zero Γ₀] {Γ'₀ : Type u_3}
    [linear_ordered_comm_group_with_zero Γ'₀] [ring R] (f : monoid_with_zero_hom Γ₀ Γ'₀)
    (hf : monotone ⇑f) (v : valuation R Γ₀) : valuation R Γ'₀ :=
  mk (⇑f ∘ ⇑v) sorry sorry sorry sorry

/-- Two valuations on R are defined to be equivalent if they induce the same preorder on R. -/
def is_equiv {R : Type u_1} {Γ₀ : Type u_2} [linear_ordered_comm_group_with_zero Γ₀]
    {Γ'₀ : Type u_3} [linear_ordered_comm_group_with_zero Γ'₀] [ring R] (v₁ : valuation R Γ₀)
    (v₂ : valuation R Γ'₀) :=
  ∀ (r s : R), coe_fn v₁ r ≤ coe_fn v₁ s ↔ coe_fn v₂ r ≤ coe_fn v₂ s

namespace is_equiv


theorem refl {R : Type u_1} {Γ₀ : Type u_2} [linear_ordered_comm_group_with_zero Γ₀] [ring R]
    {v : valuation R Γ₀} : is_equiv v v :=
  fun (_x _x_1 : R) => iff.refl (coe_fn v _x ≤ coe_fn v _x_1)

theorem symm {R : Type u_1} {Γ₀ : Type u_2} [linear_ordered_comm_group_with_zero Γ₀]
    {Γ'₀ : Type u_3} [linear_ordered_comm_group_with_zero Γ'₀] [ring R] {v₁ : valuation R Γ₀}
    {v₂ : valuation R Γ'₀} (h : is_equiv v₁ v₂) : is_equiv v₂ v₁ :=
  fun (_x _x_1 : R) => iff.symm (h _x _x_1)

theorem trans {R : Type u_1} {Γ₀ : Type u_2} [linear_ordered_comm_group_with_zero Γ₀]
    {Γ'₀ : Type u_3} [linear_ordered_comm_group_with_zero Γ'₀] {Γ''₀ : Type u_4}
    [linear_ordered_comm_group_with_zero Γ''₀] [ring R] {v₁ : valuation R Γ₀} {v₂ : valuation R Γ'₀}
    {v₃ : valuation R Γ''₀} (h₁₂ : is_equiv v₁ v₂) (h₂₃ : is_equiv v₂ v₃) : is_equiv v₁ v₃ :=
  fun (_x _x_1 : R) => iff.trans (h₁₂ _x _x_1) (h₂₃ _x _x_1)

theorem of_eq {R : Type u_1} {Γ₀ : Type u_2} [linear_ordered_comm_group_with_zero Γ₀] [ring R]
    {v : valuation R Γ₀} {v' : valuation R Γ₀} (h : v = v') : is_equiv v v' :=
  Eq._oldrec refl h

theorem map {R : Type u_1} {Γ₀ : Type u_2} [linear_ordered_comm_group_with_zero Γ₀] {Γ'₀ : Type u_3}
    [linear_ordered_comm_group_with_zero Γ'₀] [ring R] {v : valuation R Γ₀} {v' : valuation R Γ₀}
    (f : monoid_with_zero_hom Γ₀ Γ'₀) (hf : monotone ⇑f) (inf : function.injective ⇑f)
    (h : is_equiv v v') : is_equiv (map f hf v) (map f hf v') :=
  sorry

/-- `comap` preserves equivalence. -/
theorem comap {R : Type u_1} {Γ₀ : Type u_2} [linear_ordered_comm_group_with_zero Γ₀]
    {Γ'₀ : Type u_3} [linear_ordered_comm_group_with_zero Γ'₀] [ring R] {v₁ : valuation R Γ₀}
    {v₂ : valuation R Γ'₀} {S : Type u_4} [ring S] (f : S →+* R) (h : is_equiv v₁ v₂) :
    is_equiv (comap f v₁) (comap f v₂) :=
  fun (r s : S) => h (coe_fn f r) (coe_fn f s)

theorem val_eq {R : Type u_1} {Γ₀ : Type u_2} [linear_ordered_comm_group_with_zero Γ₀]
    {Γ'₀ : Type u_3} [linear_ordered_comm_group_with_zero Γ'₀] [ring R] {v₁ : valuation R Γ₀}
    {v₂ : valuation R Γ'₀} (h : is_equiv v₁ v₂) {r : R} {s : R} :
    coe_fn v₁ r = coe_fn v₁ s ↔ coe_fn v₂ r = coe_fn v₂ s :=
  sorry

theorem ne_zero {R : Type u_1} {Γ₀ : Type u_2} [linear_ordered_comm_group_with_zero Γ₀]
    {Γ'₀ : Type u_3} [linear_ordered_comm_group_with_zero Γ'₀] [ring R] {v₁ : valuation R Γ₀}
    {v₂ : valuation R Γ'₀} (h : is_equiv v₁ v₂) {r : R} : coe_fn v₁ r ≠ 0 ↔ coe_fn v₂ r ≠ 0 :=
  eq.mp (Eq._oldrec (Eq.refl (coe_fn v₁ r ≠ 0 ↔ coe_fn v₂ r ≠ coe_fn v₂ 0)) (map_zero v₂))
    (eq.mp
      (Eq._oldrec (Eq.refl (coe_fn v₁ r ≠ coe_fn v₁ 0 ↔ coe_fn v₂ r ≠ coe_fn v₂ 0)) (map_zero v₁))
      (not_iff_not_of_iff (val_eq h)))

theorem Mathlib.valuation.is_equiv_of_map_strict_mono {R : Type u_1} {Γ₀ : Type u_2}
    [linear_ordered_comm_group_with_zero Γ₀] {Γ'₀ : Type u_3}
    [linear_ordered_comm_group_with_zero Γ'₀] [ring R] {v : valuation R Γ₀}
    (f : monoid_with_zero_hom Γ₀ Γ'₀) (H : strict_mono ⇑f) :
    is_equiv (map f (strict_mono.monotone H) v) v :=
  fun (x y : R) =>
    { mp := iff.mp (strict_mono.le_iff_le H),
      mpr := fun (h : coe_fn v x ≤ coe_fn v y) => strict_mono.monotone H h }

theorem Mathlib.valuation.is_equiv_of_val_le_one {Γ₀ : Type u_2}
    [linear_ordered_comm_group_with_zero Γ₀] {Γ'₀ : Type u_3}
    [linear_ordered_comm_group_with_zero Γ'₀] {K : Type u_1} [division_ring K] (v : valuation K Γ₀)
    (v' : valuation K Γ'₀) (h : ∀ {x : K}, coe_fn v x ≤ 1 ↔ coe_fn v' x ≤ 1) : is_equiv v v' :=
  sorry

/-- The support of a valuation `v : R → Γ₀` is the ideal of `R` where `v` vanishes. -/
def Mathlib.valuation.supp {R : Type u_1} {Γ₀ : Type u_2} [linear_ordered_comm_group_with_zero Γ₀]
    [comm_ring R] (v : valuation R Γ₀) : ideal R :=
  submodule.mk (set_of fun (x : R) => coe_fn v x = 0) sorry sorry sorry

-- @[simp] lemma mem_supp_iff' (x : R) : x ∈ (supp v : set R) ↔ v x = 0 := iff.rfl

@[simp] theorem Mathlib.valuation.mem_supp_iff {R : Type u_1} {Γ₀ : Type u_2}
    [linear_ordered_comm_group_with_zero Γ₀] [comm_ring R] (v : valuation R Γ₀) (x : R) :
    x ∈ supp v ↔ coe_fn v x = 0 :=
  iff.rfl

/-- The support of a valuation is a prime ideal. -/
protected instance Mathlib.valuation.supp.ideal.is_prime {R : Type u_1} {Γ₀ : Type u_2}
    [linear_ordered_comm_group_with_zero Γ₀] [comm_ring R] (v : valuation R Γ₀) :
    ideal.is_prime (supp v) :=
  { left :=
      fun (h : supp v = ⊤) =>
        one_ne_zero
          ((fun (this : 1 = 0) => this)
            (Eq.trans (Eq.symm (map_one v))
              ((fun (this : 1 ∈ supp v) => this)
                (eq.mpr (id (Eq._oldrec (Eq.refl (1 ∈ supp v)) h)) trivial)))),
    right :=
      fun (x y : R) (hxy : x * y ∈ supp v) =>
        id
          (id
            (fun (hxy : coe_fn v (x * y) = 0) =>
              eq_zero_or_eq_zero_of_mul_eq_zero
                (eq.mp (Eq._oldrec (Eq.refl (coe_fn v (x * y) = 0)) (map_mul v x y)) hxy))
            hxy) }

theorem Mathlib.valuation.map_add_supp {R : Type u_1} {Γ₀ : Type u_2}
    [linear_ordered_comm_group_with_zero Γ₀] [comm_ring R] (v : valuation R Γ₀) (a : R) {s : R}
    (h : s ∈ supp v) : coe_fn v (a + s) = coe_fn v a :=
  sorry

/-- If `hJ : J ⊆ supp v` then `on_quot_val hJ` is the induced function on R/J as a function.
Note: it's just the function; the valuation is `on_quot hJ`. -/
def Mathlib.valuation.on_quot_val {R : Type u_1} {Γ₀ : Type u_2}
    [linear_ordered_comm_group_with_zero Γ₀] [comm_ring R] (v : valuation R Γ₀) {J : ideal R}
    (hJ : J ≤ supp v) : ideal.quotient J → Γ₀ :=
  fun (q : ideal.quotient J) => quotient.lift_on' q ⇑v sorry

/-- The extension of valuation v on R to valuation on R/J if J ⊆ supp v -/
def Mathlib.valuation.on_quot {R : Type u_1} {Γ₀ : Type u_2}
    [linear_ordered_comm_group_with_zero Γ₀] [comm_ring R] (v : valuation R Γ₀) {J : ideal R}
    (hJ : J ≤ supp v) : valuation (ideal.quotient J) Γ₀ :=
  mk (on_quot_val v hJ) sorry sorry sorry sorry

@[simp] theorem Mathlib.valuation.on_quot_comap_eq {R : Type u_1} {Γ₀ : Type u_2}
    [linear_ordered_comm_group_with_zero Γ₀] [comm_ring R] (v : valuation R Γ₀) {J : ideal R}
    (hJ : J ≤ supp v) : comap (ideal.quotient.mk J) (on_quot v hJ) = v :=
  sorry

theorem Mathlib.valuation.comap_supp {R : Type u_1} {Γ₀ : Type u_2}
    [linear_ordered_comm_group_with_zero Γ₀] [comm_ring R] (v : valuation R Γ₀) {S : Type u_3}
    [comm_ring S] (f : S →+* R) : supp (comap f v) = ideal.comap f (supp v) :=
  sorry

theorem Mathlib.valuation.self_le_supp_comap {R : Type u_1} {Γ₀ : Type u_2}
    [linear_ordered_comm_group_with_zero Γ₀] [comm_ring R] (J : ideal R)
    (v : valuation (ideal.quotient J) Γ₀) : J ≤ supp (comap (ideal.quotient.mk J) v) :=
  sorry

@[simp] theorem Mathlib.valuation.comap_on_quot_eq {R : Type u_1} {Γ₀ : Type u_2}
    [linear_ordered_comm_group_with_zero Γ₀] [comm_ring R] (J : ideal R)
    (v : valuation (ideal.quotient J) Γ₀) :
    on_quot (comap (ideal.quotient.mk J) v) (self_le_supp_comap J v) = v :=
  sorry

/-- The quotient valuation on R/J has support supp(v)/J if J ⊆ supp v. -/
theorem Mathlib.valuation.supp_quot {R : Type u_1} {Γ₀ : Type u_2}
    [linear_ordered_comm_group_with_zero Γ₀] [comm_ring R] (v : valuation R Γ₀) {J : ideal R}
    (hJ : J ≤ supp v) : supp (on_quot v hJ) = ideal.map (ideal.quotient.mk J) (supp v) :=
  sorry

theorem Mathlib.valuation.supp_quot_supp {R : Type u_1} {Γ₀ : Type u_2}
    [linear_ordered_comm_group_with_zero Γ₀] [comm_ring R] (v : valuation R Γ₀) :
    supp (on_quot v (le_refl (supp v))) = 0 :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (supp (on_quot v (le_refl (supp v))) = 0))
        (supp_quot v (le_refl (supp v)))))
    (ideal.map_quotient_self (supp v))

end Mathlib