/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.set_theory.cardinal_ordinal
import Mathlib.PostPort

universes u_1 u v u_2 

namespace Mathlib

/-!
# Cofinality on ordinals, regular cardinals
-/

namespace order


/-- Cofinality of a reflexive order `≼`. This is the smallest cardinality
  of a subset `S : set α` such that `∀ a, ∃ b ∈ S, a ≼ b`. -/
def cof {α : Type u_1} (r : α → α → Prop) [is_refl α r] : cardinal :=
  cardinal.min sorry
    fun (S : Subtype fun (S : set α) => ∀ (a : α), ∃ (b : α), ∃ (H : b ∈ S), r a b) =>
      cardinal.mk ↥S

theorem cof_le {α : Type u_1} (r : α → α → Prop) [is_refl α r] {S : set α}
    (h : ∀ (a : α), ∃ (b : α), ∃ (H : b ∈ S), r a b) : cof r ≤ cardinal.mk ↥S :=
  sorry

theorem le_cof {α : Type u_1} {r : α → α → Prop} [is_refl α r] (c : cardinal) :
    c ≤ cof r ↔ ∀ {S : set α}, (∀ (a : α), ∃ (b : α), ∃ (H : b ∈ S), r a b) → c ≤ cardinal.mk ↥S :=
  sorry

end order


theorem rel_iso.cof.aux {α : Type u} {β : Type v} {r : α → α → Prop} {s : β → β → Prop}
    [is_refl α r] [is_refl β s] (f : r ≃r s) :
    cardinal.lift (order.cof r) ≤ cardinal.lift (order.cof s) :=
  sorry

theorem rel_iso.cof {α : Type u} {β : Type v} {r : α → α → Prop} {s : β → β → Prop} [is_refl α r]
    [is_refl β s] (f : r ≃r s) : cardinal.lift (order.cof r) = cardinal.lift (order.cof s) :=
  le_antisymm sorry sorry

def strict_order.cof {α : Type u_1} (r : α → α → Prop) [h : is_irrefl α r] : cardinal :=
  order.cof fun (x y : α) => ¬r y x

namespace ordinal


/-- Cofinality of an ordinal. This is the smallest cardinal of a
  subset `S` of the ordinal which is unbounded, in the sense
  `∀ a, ∃ b ∈ S, ¬(b > a)`. It is defined for all ordinals, but
  `cof 0 = 0` and `cof (succ o) = 1`, so it is only really
  interesting on limit ordinals (when it is an infinite cardinal). -/
def cof (o : ordinal) : cardinal := quot.lift_on o (fun (_x : Well_order) => sorry) sorry

theorem cof_type {α : Type u_1} (r : α → α → Prop) [is_well_order α r] :
    cof (type r) = strict_order.cof r :=
  rfl

theorem le_cof_type {α : Type u_1} {r : α → α → Prop} [is_well_order α r] {c : cardinal} :
    c ≤ cof (type r) ↔
        ∀ (S : set α), (∀ (a : α), ∃ (b : α), ∃ (H : b ∈ S), ¬r b a) → c ≤ cardinal.mk ↥S :=
  sorry

theorem cof_type_le {α : Type u_1} {r : α → α → Prop} [is_well_order α r] (S : set α)
    (h : ∀ (a : α), ∃ (b : α), ∃ (H : b ∈ S), ¬r b a) : cof (type r) ≤ cardinal.mk ↥S :=
  iff.mp le_cof_type (le_refl (cof (type r))) S h

theorem lt_cof_type {α : Type u_1} {r : α → α → Prop} [is_well_order α r] (S : set α)
    (hl : cardinal.mk ↥S < cof (type r)) : ∃ (a : α), ∀ (b : α), b ∈ S → r b a :=
  iff.mp not_forall_not
    fun (h : ∀ (x : α), ¬∀ (b : α), b ∈ S → r b x) =>
      not_le_of_lt hl (cof_type_le S fun (a : α) => iff.mp not_ball (h a))

theorem cof_eq {α : Type u_1} (r : α → α → Prop) [is_well_order α r] :
    ∃ (S : set α), (∀ (a : α), ∃ (b : α), ∃ (H : b ∈ S), ¬r b a) ∧ cardinal.mk ↥S = cof (type r) :=
  sorry

theorem ord_cof_eq {α : Type u_1} (r : α → α → Prop) [is_well_order α r] :
    ∃ (S : set α),
        (∀ (a : α), ∃ (b : α), ∃ (H : b ∈ S), ¬r b a) ∧
          type (subrel r S) = cardinal.ord (cof (type r)) :=
  sorry

theorem lift_cof (o : ordinal) : cardinal.lift (cof o) = cof (lift o) := sorry

theorem cof_le_card (o : ordinal) : cof o ≤ card o := sorry

theorem cof_ord_le (c : cardinal) : cof (cardinal.ord c) ≤ c := sorry

@[simp] theorem cof_zero : cof 0 = 0 := sorry

@[simp] theorem cof_eq_zero {o : ordinal} : cof o = 0 ↔ o = 0 := sorry

@[simp] theorem cof_succ (o : ordinal) : cof (succ o) = 1 := sorry

@[simp] theorem cof_eq_one_iff_is_succ {o : ordinal} : cof o = 1 ↔ ∃ (a : ordinal), o = succ a :=
  sorry

@[simp] theorem cof_add (a : ordinal) (b : ordinal) : b ≠ 0 → cof (a + b) = cof b := sorry

@[simp] theorem cof_cof (o : ordinal) : cof (cardinal.ord (cof o)) = cof o := sorry

theorem omega_le_cof {o : ordinal} : cardinal.omega ≤ cof o ↔ is_limit o := sorry

@[simp] theorem cof_omega : cof omega = cardinal.omega :=
  le_antisymm
    (eq.mpr (id (Eq._oldrec (Eq.refl (cof omega ≤ cardinal.omega)) (Eq.symm card_omega)))
      (cof_le_card omega))
    (iff.mpr omega_le_cof omega_is_limit)

theorem cof_eq' {α : Type u_1} (r : α → α → Prop) [is_well_order α r] (h : is_limit (type r)) :
    ∃ (S : set α), (∀ (a : α), ∃ (b : α), ∃ (H : b ∈ S), r a b) ∧ cardinal.mk ↥S = cof (type r) :=
  sorry

theorem cof_sup_le_lift {ι : Type u_1} (f : ι → ordinal) (H : ∀ (i : ι), f i < sup f) :
    cof (sup f) ≤ cardinal.lift (cardinal.mk ι) :=
  sorry

theorem cof_sup_le {ι : Type u} (f : ι → ordinal) (H : ∀ (i : ι), f i < sup f) :
    cof (sup f) ≤ cardinal.mk ι :=
  sorry

theorem cof_bsup_le_lift {o : ordinal} (f : (a : ordinal) → a < o → ordinal) :
    (∀ (i : ordinal) (h : i < o), f i h < bsup o f) → cof (bsup o f) ≤ cardinal.lift (card o) :=
  sorry

theorem cof_bsup_le {o : ordinal} (f : (a : ordinal) → a < o → ordinal) :
    (∀ (i : ordinal) (h : i < o), f i h < bsup o f) → cof (bsup o f) ≤ card o :=
  sorry

@[simp] theorem cof_univ : cof univ = cardinal.univ := sorry

theorem sup_lt_ord {ι : Type u} (f : ι → ordinal) {c : ordinal} (H1 : cardinal.mk ι < cof c)
    (H2 : ∀ (i : ι), f i < c) : sup f < c :=
  sorry

theorem sup_lt {ι : Type u} (f : ι → cardinal) {c : cardinal}
    (H1 : cardinal.mk ι < cof (cardinal.ord c)) (H2 : ∀ (i : ι), f i < c) : cardinal.sup f < c :=
  sorry

/-- If the union of s is unbounded and s is smaller than the cofinality, then s has an unbounded member -/
theorem unbounded_of_unbounded_sUnion {α : Type u_1} (r : α → α → Prop) [wo : is_well_order α r]
    {s : set (set α)} (h₁ : unbounded r (⋃₀s)) (h₂ : cardinal.mk ↥s < strict_order.cof r) :
    ∃ (x : set α), ∃ (H : x ∈ s), unbounded r x :=
  sorry

/-- If the union of s is unbounded and s is smaller than the cofinality, then s has an unbounded member -/
theorem unbounded_of_unbounded_Union {α : Type u} {β : Type u} (r : α → α → Prop)
    [wo : is_well_order α r] (s : β → set α) (h₁ : unbounded r (set.Union fun (x : β) => s x))
    (h₂ : cardinal.mk β < strict_order.cof r) : ∃ (x : β), unbounded r (s x) :=
  sorry

/-- The infinite pigeonhole principle-/
theorem infinite_pigeonhole {β : Type u} {α : Type u} (f : β → α)
    (h₁ : cardinal.omega ≤ cardinal.mk β)
    (h₂ : cardinal.mk α < cof (cardinal.ord (cardinal.mk β))) :
    ∃ (a : α), cardinal.mk ↥(f ⁻¹' singleton a) = cardinal.mk β :=
  sorry

/-- pigeonhole principle for a cardinality below the cardinality of the domain -/
theorem infinite_pigeonhole_card {β : Type u} {α : Type u} (f : β → α) (θ : cardinal)
    (hθ : θ ≤ cardinal.mk β) (h₁ : cardinal.omega ≤ θ) (h₂ : cardinal.mk α < cof (cardinal.ord θ)) :
    ∃ (a : α), θ ≤ cardinal.mk ↥(f ⁻¹' singleton a) :=
  sorry

theorem infinite_pigeonhole_set {β : Type u} {α : Type u} {s : set β} (f : ↥s → α) (θ : cardinal)
    (hθ : θ ≤ cardinal.mk ↥s) (h₁ : cardinal.omega ≤ θ)
    (h₂ : cardinal.mk α < cof (cardinal.ord θ)) :
    ∃ (a : α),
        ∃ (t : set β),
          ∃ (h : t ⊆ s),
            θ ≤ cardinal.mk ↥t ∧ ∀ {x : β} (hx : x ∈ t), f { val := x, property := h hx } = a :=
  sorry

end ordinal


namespace cardinal


/-- A cardinal is a limit if it is not zero or a successor
  cardinal. Note that `ω` is a limit cardinal by this definition. -/
def is_limit (c : cardinal) := c ≠ 0 ∧ ∀ (x : cardinal), x < c → succ x < c

/-- A cardinal is a strong limit if it is not zero and it is
  closed under powersets. Note that `ω` is a strong limit by this definition. -/
def is_strong_limit (c : cardinal) := c ≠ 0 ∧ ∀ (x : cardinal), x < c → bit0 1 ^ x < c

theorem is_strong_limit.is_limit {c : cardinal} (H : is_strong_limit c) : is_limit c :=
  { left := and.left H,
    right :=
      fun (x : cardinal) (h : x < c) =>
        lt_of_le_of_lt (iff.mpr succ_le (cantor x)) (and.right H x h) }

/-- A cardinal is regular if it is infinite and it equals its own cofinality. -/
def is_regular (c : cardinal) := omega ≤ c ∧ ordinal.cof (ord c) = c

theorem cof_is_regular {o : ordinal} (h : ordinal.is_limit o) : is_regular (ordinal.cof o) :=
  { left := iff.mpr ordinal.omega_le_cof h, right := ordinal.cof_cof o }

theorem omega_is_regular : is_regular omega := sorry

theorem succ_is_regular {c : cardinal} (h : omega ≤ c) : is_regular (succ c) := sorry

theorem sup_lt_ord_of_is_regular {ι : Type u} (f : ι → ordinal) {c : cardinal} (hc : is_regular c)
    (H1 : mk ι < c) (H2 : ∀ (i : ι), f i < ord c) : ordinal.sup f < ord c :=
  ordinal.sup_lt_ord (fun (i : ι) => f i)
    (eq.mpr (id (Eq._oldrec (Eq.refl (mk ι < ordinal.cof (ord c))) (and.right hc))) H1) H2

theorem sup_lt_of_is_regular {ι : Type u} (f : ι → cardinal) {c : cardinal} (hc : is_regular c)
    (H1 : mk ι < c) (H2 : ∀ (i : ι), f i < c) : sup f < c :=
  ordinal.sup_lt (fun (i : ι) => f i)
    (eq.mpr (id (Eq._oldrec (Eq.refl (mk ι < ordinal.cof (ord c))) (and.right hc))) H1) H2

theorem sum_lt_of_is_regular {ι : Type u} (f : ι → cardinal) {c : cardinal} (hc : is_regular c)
    (H1 : mk ι < c) (H2 : ∀ (i : ι), f i < c) : sum f < c :=
  lt_of_le_of_lt (sum_le_sup f) (mul_lt_of_lt (and.left hc) H1 (sup_lt_of_is_regular f hc H1 H2))

/-- A cardinal is inaccessible if it is an
  uncountable regular strong limit cardinal. -/
def is_inaccessible (c : cardinal) := omega < c ∧ is_regular c ∧ is_strong_limit c

theorem is_inaccessible.mk {c : cardinal} (h₁ : omega < c) (h₂ : c ≤ ordinal.cof (ord c))
    (h₃ : ∀ (x : cardinal), x < c → bit0 1 ^ x < c) : is_inaccessible c :=
  sorry

/- Lean's foundations prove the existence of ω many inaccessible
   cardinals -/

theorem univ_inaccessible : is_inaccessible univ := sorry

theorem lt_power_cof {c : cardinal} : omega ≤ c → c < c ^ ordinal.cof (ord c) := sorry

theorem lt_cof_power {a : cardinal} {b : cardinal} (ha : omega ≤ a) (b1 : 1 < b) :
    a < ordinal.cof (ord (b ^ a)) :=
  sorry

end Mathlib