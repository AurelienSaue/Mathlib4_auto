/-
Copyright (c) 2021 Jordan Brown, Thomas Browning and Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jordan Brown, Thomas Browning and Patrick Lutz
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.group_theory.abelianization
import Mathlib.data.bracket
import PostPort

universes u_1 u_2 l 

namespace Mathlib

/-!
# Solvable Groups

In this file we introduce the notion of a solvable group. We define a solvable group as one whose
derived series is eventually trivial. This requires defining the commutator of two subgroups and
the derived series of a group.

## Main definitions

* `general_commutator H₁ H₂` : the commutator of the subgroups `H₁` and `H₂`
* `derived_series G n` : the `n`th term in the derived series of `G`, defined by iterating
  `general_commutator` starting with the top subgroup
* `is_solvable G` : the group `G` is solvable
-/

/-- The commutator of two subgroups `H₁` and `H₂`. -/
protected instance general_commutator {G : Type u_1} [group G] : has_bracket (subgroup G) (subgroup G) :=
  has_bracket.mk
    fun (H₁ H₂ : subgroup G) =>
      subgroup.closure
        (set_of fun (x : G) => ∃ (p : G), ∃ (H : p ∈ H₁), ∃ (q : G), ∃ (H : q ∈ H₂), p * q * (p⁻¹) * (q⁻¹) = x)

theorem general_commutator_def {G : Type u_1} [group G] (H₁ : subgroup G) (H₂ : subgroup G) : has_bracket.bracket H₁ H₂ =
  subgroup.closure
    (set_of fun (x : G) => ∃ (p : G), ∃ (H : p ∈ H₁), ∃ (q : G), ∃ (H : q ∈ H₂), p * q * (p⁻¹) * (q⁻¹) = x) :=
  rfl

protected instance general_commutator_normal {G : Type u_1} [group G] (H₁ : subgroup G) (H₂ : subgroup G) [h₁ : subgroup.normal H₁] [h₂ : subgroup.normal H₂] : subgroup.normal (has_bracket.bracket H₁ H₂) := sorry

theorem general_commutator_mono {G : Type u_1} [group G] {H₁ : subgroup G} {H₂ : subgroup G} {K₁ : subgroup G} {K₂ : subgroup G} (h₁ : H₁ ≤ K₁) (h₂ : H₂ ≤ K₂) : has_bracket.bracket H₁ H₂ ≤ has_bracket.bracket K₁ K₂ := sorry

theorem general_commutator_def' {G : Type u_1} [group G] (H₁ : subgroup G) (H₂ : subgroup G) [subgroup.normal H₁] [subgroup.normal H₂] : has_bracket.bracket H₁ H₂ =
  subgroup.normal_closure
    (set_of fun (x : G) => ∃ (p : G), ∃ (H : p ∈ H₁), ∃ (q : G), ∃ (H : q ∈ H₂), p * q * (p⁻¹) * (q⁻¹) = x) := sorry

theorem general_commutator_le {G : Type u_1} [group G] (H₁ : subgroup G) (H₂ : subgroup G) (K : subgroup G) : has_bracket.bracket H₁ H₂ ≤ K ↔ ∀ (p : G), p ∈ H₁ → ∀ (q : G), q ∈ H₂ → p * q * (p⁻¹) * (q⁻¹) ∈ K := sorry

theorem general_commutator_comm {G : Type u_1} [group G] (H₁ : subgroup G) (H₂ : subgroup G) : has_bracket.bracket H₁ H₂ = has_bracket.bracket H₂ H₁ := sorry

theorem general_commutator_le_right {G : Type u_1} [group G] (H₁ : subgroup G) (H₂ : subgroup G) [h : subgroup.normal H₂] : has_bracket.bracket H₁ H₂ ≤ H₂ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (has_bracket.bracket H₁ H₂ ≤ H₂)) (propext (general_commutator_le H₁ H₂ H₂))))
    fun (p : G) (hp : p ∈ H₁) (q : G) (hq : q ∈ H₂) =>
      subgroup.mul_mem H₂ (subgroup.normal.conj_mem h q hq p) (subgroup.inv_mem H₂ hq)

theorem general_commutator_le_left {G : Type u_1} [group G] (H₁ : subgroup G) (H₂ : subgroup G) [h : subgroup.normal H₁] : has_bracket.bracket H₁ H₂ ≤ H₁ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (has_bracket.bracket H₁ H₂ ≤ H₁)) (general_commutator_comm H₁ H₂)))
    (general_commutator_le_right H₂ H₁)

@[simp] theorem general_commutator_bot {G : Type u_1} [group G] (H : subgroup G) : has_bracket.bracket H ⊥ = ⊥ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (has_bracket.bracket H ⊥ = ⊥)) (propext eq_bot_iff))) (general_commutator_le_right H ⊥)

@[simp] theorem bot_general_commutator {G : Type u_1} [group G] (H : subgroup G) : has_bracket.bracket ⊥ H = ⊥ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (has_bracket.bracket ⊥ H = ⊥)) (propext eq_bot_iff))) (general_commutator_le_left ⊥ H)

theorem general_commutator_le_inf {G : Type u_1} [group G] (H₁ : subgroup G) (H₂ : subgroup G) [subgroup.normal H₁] [subgroup.normal H₂] : has_bracket.bracket H₁ H₂ ≤ H₁ ⊓ H₂ := sorry

/-- The derived series of the group `G`, obtained by starting from the subgroup `⊤` and repeatedly
  taking the commutator of the previous subgroup with itself for `n` times. -/
def derived_series (G : Type u_1) [group G] : ℕ → subgroup G :=
  sorry

@[simp] theorem derived_series_zero (G : Type u_1) [group G] : derived_series G 0 = ⊤ :=
  rfl

@[simp] theorem derived_series_succ (G : Type u_1) [group G] (n : ℕ) : derived_series G (n + 1) = has_bracket.bracket (derived_series G n) (derived_series G n) :=
  rfl

theorem derived_series_normal (G : Type u_1) [group G] (n : ℕ) : subgroup.normal (derived_series G n) := sorry

@[simp] theorem general_commutator_eq_commutator (G : Type u_1) [group G] : has_bracket.bracket ⊤ ⊤ = commutator G := sorry

theorem commutator_def' (G : Type u_1) [group G] : commutator G = subgroup.closure (set_of fun (x : G) => ∃ (p : G), ∃ (q : G), p * q * (p⁻¹) * (q⁻¹) = x) := sorry

@[simp] theorem derived_series_one (G : Type u_1) [group G] : derived_series G 1 = commutator G :=
  general_commutator_eq_commutator G

theorem map_commutator_eq_commutator_map {G : Type u_1} [group G] {G' : Type u_2} [group G'] {f : G →* G'} (H₁ : subgroup G) (H₂ : subgroup G) : subgroup.map f (has_bracket.bracket H₁ H₂) = has_bracket.bracket (subgroup.map f H₁) (subgroup.map f H₂) := sorry

theorem commutator_le_map_commutator {G : Type u_1} [group G] {G' : Type u_2} [group G'] {f : G →* G'} {H₁ : subgroup G} {H₂ : subgroup G} {K₁ : subgroup G'} {K₂ : subgroup G'} (h₁ : K₁ ≤ subgroup.map f H₁) (h₂ : K₂ ≤ subgroup.map f H₂) : has_bracket.bracket K₁ K₂ ≤ subgroup.map f (has_bracket.bracket H₁ H₂) := sorry

theorem map_derived_series_le_derived_series {G : Type u_1} [group G] {G' : Type u_2} [group G'] (f : G →* G') (n : ℕ) : subgroup.map f (derived_series G n) ≤ derived_series G' n := sorry

theorem derived_series_le_map_derived_series {G : Type u_1} [group G] {G' : Type u_2} [group G'] {f : G →* G'} (hf : function.surjective ⇑f) (n : ℕ) : derived_series G' n ≤ subgroup.map f (derived_series G n) := sorry

theorem map_derived_series_eq {G : Type u_1} [group G] {G' : Type u_2} [group G'] {f : G →* G'} (hf : function.surjective ⇑f) (n : ℕ) : subgroup.map f (derived_series G n) = derived_series G' n :=
  le_antisymm (map_derived_series_le_derived_series f n) (derived_series_le_map_derived_series hf n)

/-- A group `G` is solvable if its derived series is eventually trivial. We use this definition
  because it's the most convenient one to work with. -/
class is_solvable (G : Type u_1) [group G] 
where
  solvable : ∃ (n : ℕ), derived_series G n = ⊥

theorem is_solvable_def (G : Type u_1) [group G] : is_solvable G ↔ ∃ (n : ℕ), derived_series G n = ⊥ :=
  { mp := fun (h : is_solvable G) => is_solvable.solvable,
    mpr := fun (h : ∃ (n : ℕ), derived_series G n = ⊥) => is_solvable.mk h }

protected instance is_solvable_of_comm {G : Type u_1} [comm_group G] : is_solvable G :=
  is_solvable.mk
    (Exists.intro 1
      (id
        (eq.mpr (id (Eq._oldrec (Eq.refl (derived_series G 1 = ⊥)) (propext eq_bot_iff)))
          (eq.mpr (id (Eq._oldrec (Eq.refl (derived_series G 1 ≤ ⊥)) (derived_series_one G)))
            (trans_rel_left LessEq (abelianization.commutator_subset_ker (monoid_hom.id G)) rfl)))))

theorem is_solvable_of_top_eq_bot (G : Type u_1) [group G] (h : ⊤ = ⊥) : is_solvable G := sorry

protected instance is_solvable_of_subsingleton (G : Type u_1) [group G] [subsingleton G] : is_solvable G :=
  is_solvable_of_top_eq_bot G
    (subgroup.ext
      fun (x : G) =>
        eq.mpr
          (id
            (Eq.trans
              ((fun (a a_1 : Prop) (e_1 : a = a_1) (b b_1 : Prop) (e_2 : b = b_1) => congr (congr_arg Iff e_1) e_2)
                (x ∈ ⊤) True (propext ((fun {G : Type u_1} (x : G) => iff_true_intro (subgroup.mem_top x)) x)) (x ∈ ⊥)
                True (Eq.trans (propext subgroup.mem_bot) (propext (eq_iff_true_of_subsingleton x 1))))
              (propext (iff_self True))))
          trivial)

theorem solvable_of_solvable_injective {G : Type u_1} [group G] {G' : Type u_2} [group G'] {f : G →* G'} (hf : function.injective ⇑f) [h : is_solvable G'] : is_solvable G := sorry

protected instance subgroup_solvable_of_solvable {G : Type u_1} [group G] (H : subgroup G) [h : is_solvable G] : is_solvable ↥H :=
  solvable_of_solvable_injective ((fun (this : function.injective ⇑(subgroup.subtype H)) => this) subtype.val_injective)

theorem solvable_of_surjective {G : Type u_1} [group G] {G' : Type u_2} [group G'] {f : G →* G'} (hf : function.surjective ⇑f) [h : is_solvable G] : is_solvable G' := sorry

protected instance solvable_quotient_of_solvable {G : Type u_1} [group G] (H : subgroup G) [subgroup.normal H] [h : is_solvable G] : is_solvable (quotient_group.quotient H) :=
  solvable_of_surjective
    ((fun (this : function.surjective ⇑(quotient_group.mk' H)) => this)
      (id
        fun (b : quotient_group.quotient H) =>
          quot.rec (fun (b : G) => Exists.intro b (Eq.refl (coe_fn (quotient_group.mk' H) b)))
            (fun (b_a b_b : G) (b_p : setoid.r b_a b_b) =>
              Eq.refl (Eq._oldrec (Exists.intro b_a (Eq.refl (coe_fn (quotient_group.mk' H) b_a))) (quot.sound b_p)))
            b))

