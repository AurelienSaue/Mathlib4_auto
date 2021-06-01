/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.finset.fold
import Mathlib.data.multiset.lattice
import Mathlib.order.order_dual
import Mathlib.order.complete_lattice
import Mathlib.PostPort

universes u_1 u_2 u_3 u_4 u_5 

namespace Mathlib

/-!
# Lattice operations on finsets
-/

namespace finset


/-! ### sup -/

/-- Supremum of a finite set: `sup {a, b, c} f = f a ⊔ f b ⊔ f c` -/
def sup {α : Type u_1} {β : Type u_2} [semilattice_sup_bot α] (s : finset β) (f : β → α) : α :=
  fold has_sup.sup ⊥ f s

theorem sup_def {α : Type u_1} {β : Type u_2} [semilattice_sup_bot α] {s : finset β} {f : β → α} :
    sup s f = multiset.sup (multiset.map f (val s)) :=
  rfl

@[simp] theorem sup_empty {α : Type u_1} {β : Type u_2} [semilattice_sup_bot α] {f : β → α} :
    sup ∅ f = ⊥ :=
  fold_empty

@[simp] theorem sup_insert {α : Type u_1} {β : Type u_2} [semilattice_sup_bot α] {s : finset β}
    {f : β → α} [DecidableEq β] {b : β} : sup (insert b s) f = f b ⊔ sup s f :=
  fold_insert_idem

@[simp] theorem sup_singleton {α : Type u_1} {β : Type u_2} [semilattice_sup_bot α] {f : β → α}
    {b : β} : sup (singleton b) f = f b :=
  multiset.sup_singleton

theorem sup_union {α : Type u_1} {β : Type u_2} [semilattice_sup_bot α] {s₁ : finset β}
    {s₂ : finset β} {f : β → α} [DecidableEq β] : sup (s₁ ∪ s₂) f = sup s₁ f ⊔ sup s₂ f :=
  sorry

theorem sup_congr {α : Type u_1} {β : Type u_2} [semilattice_sup_bot α] {s₁ : finset β}
    {s₂ : finset β} {f : β → α} {g : β → α} (hs : s₁ = s₂) (hfg : ∀ (a : β), a ∈ s₂ → f a = g a) :
    sup s₁ f = sup s₂ g :=
  Eq._oldrec (fun (hfg : ∀ (a : β), a ∈ s₁ → f a = g a) => fold_congr hfg) hs hfg

@[simp] theorem sup_le_iff {α : Type u_1} {β : Type u_2} [semilattice_sup_bot α] {s : finset β}
    {f : β → α} {a : α} : sup s f ≤ a ↔ ∀ (b : β), b ∈ s → f b ≤ a :=
  sorry

theorem sup_const {α : Type u_1} {β : Type u_2} [semilattice_sup_bot α] {s : finset β}
    (h : finset.nonempty s) (c : α) : (sup s fun (_x : β) => c) = c :=
  eq_of_forall_ge_iff fun (b : α) => iff.trans sup_le_iff (nonempty.forall_const h)

theorem sup_le {α : Type u_1} {β : Type u_2} [semilattice_sup_bot α] {s : finset β} {f : β → α}
    {a : α} : (∀ (b : β), b ∈ s → f b ≤ a) → sup s f ≤ a :=
  iff.mpr sup_le_iff

theorem le_sup {α : Type u_1} {β : Type u_2} [semilattice_sup_bot α] {s : finset β} {f : β → α}
    {b : β} (hb : b ∈ s) : f b ≤ sup s f :=
  iff.mp sup_le_iff (le_refl (sup s f)) b hb

theorem sup_mono_fun {α : Type u_1} {β : Type u_2} [semilattice_sup_bot α] {s : finset β}
    {f : β → α} {g : β → α} (h : ∀ (b : β), b ∈ s → f b ≤ g b) : sup s f ≤ sup s g :=
  sup_le fun (b : β) (hb : b ∈ s) => le_trans (h b hb) (le_sup hb)

theorem sup_mono {α : Type u_1} {β : Type u_2} [semilattice_sup_bot α] {s₁ : finset β}
    {s₂ : finset β} {f : β → α} (h : s₁ ⊆ s₂) : sup s₁ f ≤ sup s₂ f :=
  sup_le fun (b : β) (hb : b ∈ s₁) => le_sup (h hb)

@[simp] theorem sup_lt_iff {α : Type u_1} {β : Type u_2} [semilattice_sup_bot α] {s : finset β}
    {f : β → α} [is_total α LessEq] {a : α} (ha : ⊥ < a) :
    sup s f < a ↔ ∀ (b : β), b ∈ s → f b < a :=
  sorry

theorem comp_sup_eq_sup_comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} [semilattice_sup_bot α]
    [semilattice_sup_bot γ] {s : finset β} {f : β → α} (g : α → γ)
    (g_sup : ∀ (x y : α), g (x ⊔ y) = g x ⊔ g y) (bot : g ⊥ = ⊥) : g (sup s f) = sup s (g ∘ f) :=
  sorry

theorem comp_sup_eq_sup_comp_of_is_total {α : Type u_1} {β : Type u_2} [semilattice_sup_bot α]
    {s : finset β} {f : β → α} [is_total α LessEq] {γ : Type} [semilattice_sup_bot γ] (g : α → γ)
    (mono_g : monotone g) (bot : g ⊥ = ⊥) : g (sup s f) = sup s (g ∘ f) :=
  comp_sup_eq_sup_comp g (monotone.map_sup mono_g) bot

/-- Computating `sup` in a subtype (closed under `sup`) is the same as computing it in `α`. -/
theorem sup_coe {α : Type u_1} {β : Type u_2} [semilattice_sup_bot α] {P : α → Prop} {Pbot : P ⊥}
    {Psup : ∀ {x y : α}, P x → P y → P (x ⊔ y)} (t : finset β)
    (f : β → Subtype fun (x : α) => P x) : ↑(sup t f) = sup t fun (x : β) => ↑(f x) :=
  sorry

@[simp] theorem sup_to_finset {α : Type u_1} {β : Type u_2} [DecidableEq β] (s : finset α)
    (f : α → multiset β) :
    multiset.to_finset (sup s f) = sup s fun (x : α) => multiset.to_finset (f x) :=
  comp_sup_eq_sup_comp multiset.to_finset multiset.to_finset_union rfl

theorem subset_range_sup_succ (s : finset ℕ) : s ⊆ range (Nat.succ (sup s id)) :=
  fun (n : ℕ) (hn : n ∈ s) => iff.mpr mem_range (nat.lt_succ_of_le (le_sup hn))

theorem exists_nat_subset_range (s : finset ℕ) : ∃ (n : ℕ), s ⊆ range n :=
  Exists.intro (Nat.succ (sup s id)) (subset_range_sup_succ s)

theorem sup_subset {α : Type u_1} {β : Type u_2} [semilattice_sup_bot β] {s : finset α}
    {t : finset α} (hst : s ⊆ t) (f : α → β) : sup s f ≤ sup t f :=
  sorry

theorem sup_closed_of_sup_closed {α : Type u_1} [semilattice_sup_bot α] {s : set α} (t : finset α)
    (htne : finset.nonempty t) (h_subset : ↑t ⊆ s) (h : ∀ {a b : α}, a ∈ s → b ∈ s → a ⊔ b ∈ s) :
    sup t id ∈ s :=
  sorry

theorem sup_le_of_le_directed {α : Type u_1} [semilattice_sup_bot α] (s : set α)
    (hs : set.nonempty s) (hdir : directed_on LessEq s) (t : finset α) :
    (∀ (x : α) (H : x ∈ t), ∃ (y : α), ∃ (H : y ∈ s), x ≤ y) → ∃ (x : α), x ∈ s ∧ sup t id ≤ x :=
  sorry

theorem sup_eq_supr {α : Type u_1} {β : Type u_2} [complete_lattice β] (s : finset α) (f : α → β) :
    sup s f = supr fun (a : α) => supr fun (H : a ∈ s) => f a :=
  le_antisymm
    (sup_le fun (a : α) (ha : a ∈ s) => le_supr_of_le a (le_supr (fun (ha : a ∈ s) => f a) ha))
    (supr_le fun (a : α) => supr_le fun (ha : a ∈ s) => le_sup ha)

theorem sup_eq_Sup {α : Type u_1} [complete_lattice α] (s : finset α) : sup s id = Sup ↑s := sorry

/-! ### inf -/

/-- Infimum of a finite set: `inf {a, b, c} f = f a ⊓ f b ⊓ f c` -/
def inf {α : Type u_1} {β : Type u_2} [semilattice_inf_top α] (s : finset β) (f : β → α) : α :=
  fold has_inf.inf ⊤ f s

theorem inf_def {α : Type u_1} {β : Type u_2} [semilattice_inf_top α] {s : finset β} {f : β → α} :
    inf s f = multiset.inf (multiset.map f (val s)) :=
  rfl

@[simp] theorem inf_empty {α : Type u_1} {β : Type u_2} [semilattice_inf_top α] {f : β → α} :
    inf ∅ f = ⊤ :=
  fold_empty

theorem le_inf_iff {α : Type u_1} {β : Type u_2} [semilattice_inf_top α] {s : finset β} {f : β → α}
    {a : α} : a ≤ inf s f ↔ ∀ (b : β), b ∈ s → a ≤ f b :=
  sup_le_iff

@[simp] theorem inf_insert {α : Type u_1} {β : Type u_2} [semilattice_inf_top α] {s : finset β}
    {f : β → α} [DecidableEq β] {b : β} : inf (insert b s) f = f b ⊓ inf s f :=
  fold_insert_idem

@[simp] theorem inf_singleton {α : Type u_1} {β : Type u_2} [semilattice_inf_top α] {f : β → α}
    {b : β} : inf (singleton b) f = f b :=
  multiset.inf_singleton

theorem inf_union {α : Type u_1} {β : Type u_2} [semilattice_inf_top α] {s₁ : finset β}
    {s₂ : finset β} {f : β → α} [DecidableEq β] : inf (s₁ ∪ s₂) f = inf s₁ f ⊓ inf s₂ f :=
  sup_union

theorem inf_congr {α : Type u_1} {β : Type u_2} [semilattice_inf_top α] {s₁ : finset β}
    {s₂ : finset β} {f : β → α} {g : β → α} (hs : s₁ = s₂) (hfg : ∀ (a : β), a ∈ s₂ → f a = g a) :
    inf s₁ f = inf s₂ g :=
  Eq._oldrec (fun (hfg : ∀ (a : β), a ∈ s₁ → f a = g a) => fold_congr hfg) hs hfg

theorem inf_le {α : Type u_1} {β : Type u_2} [semilattice_inf_top α] {s : finset β} {f : β → α}
    {b : β} (hb : b ∈ s) : inf s f ≤ f b :=
  iff.mp le_inf_iff (le_refl (inf s f)) b hb

theorem le_inf {α : Type u_1} {β : Type u_2} [semilattice_inf_top α] {s : finset β} {f : β → α}
    {a : α} : (∀ (b : β), b ∈ s → a ≤ f b) → a ≤ inf s f :=
  iff.mpr le_inf_iff

theorem inf_mono_fun {α : Type u_1} {β : Type u_2} [semilattice_inf_top α] {s : finset β}
    {f : β → α} {g : β → α} (h : ∀ (b : β), b ∈ s → f b ≤ g b) : inf s f ≤ inf s g :=
  le_inf fun (b : β) (hb : b ∈ s) => le_trans (inf_le hb) (h b hb)

theorem inf_mono {α : Type u_1} {β : Type u_2} [semilattice_inf_top α] {s₁ : finset β}
    {s₂ : finset β} {f : β → α} (h : s₁ ⊆ s₂) : inf s₂ f ≤ inf s₁ f :=
  le_inf fun (b : β) (hb : b ∈ s₁) => inf_le (h hb)

theorem lt_inf_iff {α : Type u_1} {β : Type u_2} [semilattice_inf_top α] {s : finset β} {f : β → α}
    [h : is_total α LessEq] {a : α} (ha : a < ⊤) : a < inf s f ↔ ∀ (b : β), b ∈ s → a < f b :=
  sup_lt_iff ha

theorem comp_inf_eq_inf_comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} [semilattice_inf_top α]
    [semilattice_inf_top γ] {s : finset β} {f : β → α} (g : α → γ)
    (g_inf : ∀ (x y : α), g (x ⊓ y) = g x ⊓ g y) (top : g ⊤ = ⊤) : g (inf s f) = inf s (g ∘ f) :=
  comp_sup_eq_sup_comp g g_inf top

theorem comp_inf_eq_inf_comp_of_is_total {α : Type u_1} {β : Type u_2} [semilattice_inf_top α]
    {s : finset β} {f : β → α} [h : is_total α LessEq] {γ : Type} [semilattice_inf_top γ]
    (g : α → γ) (mono_g : monotone g) (top : g ⊤ = ⊤) : g (inf s f) = inf s (g ∘ f) :=
  comp_inf_eq_inf_comp g (monotone.map_inf mono_g) top

/-- Computating `inf` in a subtype (closed under `inf`) is the same as computing it in `α`. -/
theorem inf_coe {α : Type u_1} {β : Type u_2} [semilattice_inf_top α] {P : α → Prop} {Ptop : P ⊤}
    {Pinf : ∀ {x y : α}, P x → P y → P (x ⊓ y)} (t : finset β)
    (f : β → Subtype fun (x : α) => P x) : ↑(inf t f) = inf t fun (x : β) => ↑(f x) :=
  sorry

theorem inf_eq_infi {α : Type u_1} {β : Type u_2} [complete_lattice β] (s : finset α) (f : α → β) :
    inf s f = infi fun (a : α) => infi fun (H : a ∈ s) => f a :=
  sup_eq_supr s f

theorem inf_eq_Inf {α : Type u_1} [complete_lattice α] (s : finset α) : inf s id = Inf ↑s := sorry

/-! ### max and min of finite sets -/

/-- Let `s` be a finset in a linear order. Then `s.max` is the maximum of `s` if `s` is not empty,
and `none` otherwise. It belongs to `option α`. If you want to get an element of `α`, see
`s.max'`. -/
protected def max {α : Type u_1} [linear_order α] : finset α → Option α :=
  fold (option.lift_or_get max) none some

theorem max_eq_sup_with_bot {α : Type u_1} [linear_order α] (s : finset α) :
    finset.max s = sup s some :=
  rfl

@[simp] theorem max_empty {α : Type u_1} [linear_order α] : finset.max ∅ = none := rfl

@[simp] theorem max_insert {α : Type u_1} [linear_order α] {a : α} {s : finset α} :
    finset.max (insert a s) = option.lift_or_get max (some a) (finset.max s) :=
  fold_insert_idem

@[simp] theorem max_singleton {α : Type u_1} [linear_order α] {a : α} :
    finset.max (singleton a) = some a :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (finset.max (singleton a) = some a)) (Eq.symm (insert_emptyc_eq a))))
    max_insert

theorem max_of_mem {α : Type u_1} [linear_order α] {s : finset α} {a : α} (h : a ∈ s) :
    ∃ (b : α), b ∈ finset.max s :=
  Exists.imp (fun (b : α) => Exists.fst) (le_sup h a rfl)

theorem max_of_nonempty {α : Type u_1} [linear_order α] {s : finset α} (h : finset.nonempty s) :
    ∃ (a : α), a ∈ finset.max s :=
  (fun (_a : finset.nonempty s) =>
      Exists.dcases_on _a
        fun (w : α) (h_1 : w ∈ s) => idRhs (∃ (a : α), a ∈ finset.max s) (max_of_mem h_1))
    h

theorem max_eq_none {α : Type u_1} [linear_order α] {s : finset α} : finset.max s = none ↔ s = ∅ :=
  sorry

theorem mem_of_max {α : Type u_1} [linear_order α] {s : finset α} {a : α} :
    a ∈ finset.max s → a ∈ s :=
  sorry

theorem le_max_of_mem {α : Type u_1} [linear_order α] {s : finset α} {a : α} {b : α} (h₁ : a ∈ s)
    (h₂ : b ∈ finset.max s) : a ≤ b :=
  sorry

/-- Let `s` be a finset in a linear order. Then `s.min` is the minimum of `s` if `s` is not empty,
and `none` otherwise. It belongs to `option α`. If you want to get an element of `α`, see
`s.min'`. -/
protected def min {α : Type u_1} [linear_order α] : finset α → Option α :=
  fold (option.lift_or_get min) none some

theorem min_eq_inf_with_top {α : Type u_1} [linear_order α] (s : finset α) :
    finset.min s = inf s some :=
  rfl

@[simp] theorem min_empty {α : Type u_1} [linear_order α] : finset.min ∅ = none := rfl

@[simp] theorem min_insert {α : Type u_1} [linear_order α] {a : α} {s : finset α} :
    finset.min (insert a s) = option.lift_or_get min (some a) (finset.min s) :=
  fold_insert_idem

@[simp] theorem min_singleton {α : Type u_1} [linear_order α] {a : α} :
    finset.min (singleton a) = some a :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (finset.min (singleton a) = some a)) (Eq.symm (insert_emptyc_eq a))))
    min_insert

theorem min_of_mem {α : Type u_1} [linear_order α] {s : finset α} {a : α} (h : a ∈ s) :
    ∃ (b : α), b ∈ finset.min s :=
  Exists.imp (fun (b : α) => Exists.fst) (inf_le h a rfl)

theorem min_of_nonempty {α : Type u_1} [linear_order α] {s : finset α} (h : finset.nonempty s) :
    ∃ (a : α), a ∈ finset.min s :=
  (fun (_a : finset.nonempty s) =>
      Exists.dcases_on _a
        fun (w : α) (h_1 : w ∈ s) => idRhs (∃ (a : α), a ∈ finset.min s) (min_of_mem h_1))
    h

theorem min_eq_none {α : Type u_1} [linear_order α] {s : finset α} : finset.min s = none ↔ s = ∅ :=
  sorry

theorem mem_of_min {α : Type u_1} [linear_order α] {s : finset α} {a : α} :
    a ∈ finset.min s → a ∈ s :=
  sorry

theorem min_le_of_mem {α : Type u_1} [linear_order α] {s : finset α} {a : α} {b : α} (h₁ : b ∈ s)
    (h₂ : a ∈ finset.min s) : a ≤ b :=
  sorry

/-- Given a nonempty finset `s` in a linear order `α `, then `s.min' h` is its minimum, as an
element of `α`, where `h` is a proof of nonemptiness. Without this assumption, use instead `s.min`,
taking values in `option α`. -/
def min' {α : Type u_1} [linear_order α] (s : finset α) (H : finset.nonempty s) : α :=
  option.get sorry

/-- Given a nonempty finset `s` in a linear order `α `, then `s.max' h` is its maximum, as an
element of `α`, where `h` is a proof of nonemptiness. Without this assumption, use instead `s.max`,
taking values in `option α`. -/
def max' {α : Type u_1} [linear_order α] (s : finset α) (H : finset.nonempty s) : α :=
  option.get sorry

theorem min'_mem {α : Type u_1} [linear_order α] (s : finset α) (H : finset.nonempty s) :
    min' s H ∈ s :=
  sorry

theorem min'_le {α : Type u_1} [linear_order α] (s : finset α) (x : α) (H2 : x ∈ s) :
    min' s (Exists.intro x H2) ≤ x :=
  min_le_of_mem H2 (option.get_mem (min'._match_2 s (Exists.intro x H2)))

theorem le_min' {α : Type u_1} [linear_order α] (s : finset α) (H : finset.nonempty s) (x : α)
    (H2 : ∀ (y : α), y ∈ s → x ≤ y) : x ≤ min' s H :=
  H2 (min' s H) (min'_mem s H)

/-- `{a}.min' _` is `a`. -/
@[simp] theorem min'_singleton {α : Type u_1} [linear_order α] (a : α) :
    min' (singleton a) (singleton_nonempty a) = a :=
  sorry

theorem max'_mem {α : Type u_1} [linear_order α] (s : finset α) (H : finset.nonempty s) :
    max' s H ∈ s :=
  sorry

theorem le_max' {α : Type u_1} [linear_order α] (s : finset α) (x : α) (H2 : x ∈ s) :
    x ≤ max' s (Exists.intro x H2) :=
  le_max_of_mem H2 (option.get_mem (max'._match_2 s (Exists.intro x H2)))

theorem max'_le {α : Type u_1} [linear_order α] (s : finset α) (H : finset.nonempty s) (x : α)
    (H2 : ∀ (y : α), y ∈ s → y ≤ x) : max' s H ≤ x :=
  H2 (max' s H) (max'_mem s H)

/-- `{a}.max' _` is `a`. -/
@[simp] theorem max'_singleton {α : Type u_1} [linear_order α] (a : α) :
    max' (singleton a) (singleton_nonempty a) = a :=
  sorry

theorem min'_lt_max' {α : Type u_1} [linear_order α] (s : finset α) {i : α} {j : α} (H1 : i ∈ s)
    (H2 : j ∈ s) (H3 : i ≠ j) : min' s (Exists.intro i H1) < max' s (Exists.intro i H1) :=
  sorry

/--
If there's more than 1 element, the min' is less than the max'. An alternate version of
`min'_lt_max'` which is sometimes more convenient.
-/
theorem min'_lt_max'_of_card {α : Type u_1} [linear_order α] (s : finset α) (h₂ : 1 < card s) :
    min' s (iff.mp card_pos (lt_trans zero_lt_one h₂)) <
        max' s (iff.mp card_pos (lt_trans zero_lt_one h₂)) :=
  sorry

theorem max'_eq_of_dual_min' {α : Type u_1} [linear_order α] {s : finset α}
    (hs : finset.nonempty s) :
    max' s hs =
        coe_fn order_dual.of_dual
          (min' (image (⇑order_dual.to_dual) s) (nonempty.image hs ⇑order_dual.to_dual)) :=
  sorry

theorem min'_eq_of_dual_max' {α : Type u_1} [linear_order α] {s : finset α}
    (hs : finset.nonempty s) :
    min' s hs =
        coe_fn order_dual.of_dual
          (max' (image (⇑order_dual.to_dual) s) (nonempty.image hs ⇑order_dual.to_dual)) :=
  sorry

@[simp] theorem of_dual_max_eq_min_of_dual {α : Type u_1} [linear_order α] {a : α} {b : α} :
    coe_fn order_dual.of_dual (max a b) =
        min (coe_fn order_dual.of_dual a) (coe_fn order_dual.of_dual b) :=
  rfl

@[simp] theorem of_dual_min_eq_max_of_dual {α : Type u_1} [linear_order α] {a : α} {b : α} :
    coe_fn order_dual.of_dual (min a b) =
        max (coe_fn order_dual.of_dual a) (coe_fn order_dual.of_dual b) :=
  rfl

theorem exists_max_image {α : Type u_1} {β : Type u_2} [linear_order α] (s : finset β) (f : β → α)
    (h : finset.nonempty s) : ∃ (x : β), ∃ (H : x ∈ s), ∀ (x' : β), x' ∈ s → f x' ≤ f x :=
  sorry

theorem exists_min_image {α : Type u_1} {β : Type u_2} [linear_order α] (s : finset β) (f : β → α)
    (h : finset.nonempty s) : ∃ (x : β), ∃ (H : x ∈ s), ∀ (x' : β), x' ∈ s → f x ≤ f x' :=
  exists_max_image s f h

end finset


namespace multiset


theorem count_sup {α : Type u_1} {β : Type u_2} [DecidableEq β] (s : finset α) (f : α → multiset β)
    (b : β) : count b (finset.sup s f) = finset.sup s fun (a : α) => count b (f a) :=
  sorry

theorem mem_sup {α : Type u_1} {β : Type u_2} [DecidableEq β] {s : finset α} {f : α → multiset β}
    {x : β} : x ∈ finset.sup s f ↔ ∃ (v : α), ∃ (H : v ∈ s), x ∈ f v :=
  sorry

end multiset


namespace finset


theorem mem_sup {α : Type u_1} {β : Type u_2} [DecidableEq β] {s : finset α} {f : α → finset β}
    {x : β} : x ∈ sup s f ↔ ∃ (v : α), ∃ (H : v ∈ s), x ∈ f v :=
  sorry

theorem sup_eq_bUnion {α : Type u_1} {β : Type u_2} [DecidableEq β] (s : finset α)
    (t : α → finset β) : sup s t = finset.bUnion s t :=
  sorry

end finset


/-- Supremum of `s i`, `i : ι`, is equal to the supremum over `t : finset ι` of suprema
`⨆ i ∈ t, s i`. This version assumes `ι` is a `Type*`. See `supr_eq_supr_finset'` for a version
that works for `ι : Sort*`. -/
theorem supr_eq_supr_finset {α : Type u_1} {ι : Type u_4} [complete_lattice α] (s : ι → α) :
    (supr fun (i : ι) => s i) =
        supr fun (t : finset ι) => supr fun (i : ι) => supr fun (H : i ∈ t) => s i :=
  sorry

/-- Supremum of `s i`, `i : ι`, is equal to the supremum over `t : finset ι` of suprema
`⨆ i ∈ t, s i`. This version works for `ι : Sort*`. See `supr_eq_supr_finset` for a version
that assumes `ι : Type*` but has no `plift`s. -/
theorem supr_eq_supr_finset' {α : Type u_1} {ι' : Sort u_5} [complete_lattice α] (s : ι' → α) :
    (supr fun (i : ι') => s i) =
        supr
          fun (t : finset (plift ι')) =>
            supr fun (i : plift ι') => supr fun (H : i ∈ t) => s (plift.down i) :=
  sorry

/-- Infimum of `s i`, `i : ι`, is equal to the infimum over `t : finset ι` of infima
`⨆ i ∈ t, s i`. This version assumes `ι` is a `Type*`. See `infi_eq_infi_finset'` for a version
that works for `ι : Sort*`. -/
theorem infi_eq_infi_finset {α : Type u_1} {ι : Type u_4} [complete_lattice α] (s : ι → α) :
    (infi fun (i : ι) => s i) =
        infi fun (t : finset ι) => infi fun (i : ι) => infi fun (H : i ∈ t) => s i :=
  supr_eq_supr_finset fun (i : ι) => s i

/-- Infimum of `s i`, `i : ι`, is equal to the infimum over `t : finset ι` of infima
`⨆ i ∈ t, s i`. This version works for `ι : Sort*`. See `infi_eq_infi_finset` for a version
that assumes `ι : Type*` but has no `plift`s. -/
theorem infi_eq_infi_finset' {α : Type u_1} {ι' : Sort u_5} [complete_lattice α] (s : ι' → α) :
    (infi fun (i : ι') => s i) =
        infi
          fun (t : finset (plift ι')) =>
            infi fun (i : plift ι') => infi fun (H : i ∈ t) => s (plift.down i) :=
  supr_eq_supr_finset' fun (i : ι') => s i

namespace set


/-- Union of an indexed family of sets `s : ι → set α` is equal to the union of the unions
of finite subfamilies. This version assumes `ι : Type*`. See also `Union_eq_Union_finset'` for
a version that works for `ι : Sort*`. -/
theorem Union_eq_Union_finset {α : Type u_1} {ι : Type u_4} (s : ι → set α) :
    (Union fun (i : ι) => s i) =
        Union fun (t : finset ι) => Union fun (i : ι) => Union fun (H : i ∈ t) => s i :=
  supr_eq_supr_finset s

/-- Union of an indexed family of sets `s : ι → set α` is equal to the union of the unions
of finite subfamilies. This version works for `ι : Sort*`. See also `Union_eq_Union_finset` for
a version that assumes `ι : Type*` but avoids `plift`s in the right hand side. -/
theorem Union_eq_Union_finset' {α : Type u_1} {ι' : Sort u_5} (s : ι' → set α) :
    (Union fun (i : ι') => s i) =
        Union
          fun (t : finset (plift ι')) =>
            Union fun (i : plift ι') => Union fun (H : i ∈ t) => s (plift.down i) :=
  supr_eq_supr_finset' s

/-- Intersection of an indexed family of sets `s : ι → set α` is equal to the intersection of the
intersections of finite subfamilies. This version assumes `ι : Type*`. See also
`Inter_eq_Inter_finset'` for a version that works for `ι : Sort*`. -/
theorem Inter_eq_Inter_finset {α : Type u_1} {ι : Type u_4} (s : ι → set α) :
    (Inter fun (i : ι) => s i) =
        Inter fun (t : finset ι) => Inter fun (i : ι) => Inter fun (H : i ∈ t) => s i :=
  infi_eq_infi_finset s

/-- Intersection of an indexed family of sets `s : ι → set α` is equal to the intersection of the
intersections of finite subfamilies. This version works for `ι : Sort*`. See also
`Inter_eq_Inter_finset` for a version that assumes `ι : Type*` but avoids `plift`s in the right
hand side. -/
theorem Inter_eq_Inter_finset' {α : Type u_1} {ι' : Sort u_5} (s : ι' → set α) :
    (Inter fun (i : ι') => s i) =
        Inter
          fun (t : finset (plift ι')) =>
            Inter fun (i : plift ι') => Inter fun (H : i ∈ t) => s (plift.down i) :=
  infi_eq_infi_finset' s

end set


namespace finset


/-! ### Interaction with big lattice/set operations -/

theorem supr_coe {α : Type u_1} {β : Type u_2} [has_Sup β] (f : α → β) (s : finset α) :
    (supr fun (x : α) => supr fun (H : x ∈ ↑s) => f x) =
        supr fun (x : α) => supr fun (H : x ∈ s) => f x :=
  rfl

theorem infi_coe {α : Type u_1} {β : Type u_2} [has_Inf β] (f : α → β) (s : finset α) :
    (infi fun (x : α) => infi fun (H : x ∈ ↑s) => f x) =
        infi fun (x : α) => infi fun (H : x ∈ s) => f x :=
  rfl

theorem supr_singleton {α : Type u_1} {β : Type u_2} [complete_lattice β] (a : α) (s : α → β) :
    (supr fun (x : α) => supr fun (H : x ∈ singleton a) => s x) = s a :=
  sorry

theorem infi_singleton {α : Type u_1} {β : Type u_2} [complete_lattice β] (a : α) (s : α → β) :
    (infi fun (x : α) => infi fun (H : x ∈ singleton a) => s x) = s a :=
  sorry

theorem supr_option_to_finset {α : Type u_1} {β : Type u_2} [complete_lattice β] (o : Option α)
    (f : α → β) :
    (supr fun (x : α) => supr fun (H : x ∈ option.to_finset o) => f x) =
        supr fun (x : α) => supr fun (H : x ∈ o) => f x :=
  sorry

theorem infi_option_to_finset {α : Type u_1} {β : Type u_2} [complete_lattice β] (o : Option α)
    (f : α → β) :
    (infi fun (x : α) => infi fun (H : x ∈ option.to_finset o) => f x) =
        infi fun (x : α) => infi fun (H : x ∈ o) => f x :=
  supr_option_to_finset o fun (x : α) => f x

theorem supr_union {α : Type u_1} {β : Type u_2} [complete_lattice β] [DecidableEq α] {f : α → β}
    {s : finset α} {t : finset α} :
    (supr fun (x : α) => supr fun (H : x ∈ s ∪ t) => f x) =
        (supr fun (x : α) => supr fun (H : x ∈ s) => f x) ⊔
          supr fun (x : α) => supr fun (H : x ∈ t) => f x :=
  sorry

theorem infi_union {α : Type u_1} {β : Type u_2} [complete_lattice β] [DecidableEq α] {f : α → β}
    {s : finset α} {t : finset α} :
    (infi fun (x : α) => infi fun (H : x ∈ s ∪ t) => f x) =
        (infi fun (x : α) => infi fun (H : x ∈ s) => f x) ⊓
          infi fun (x : α) => infi fun (H : x ∈ t) => f x :=
  sorry

theorem supr_insert {α : Type u_1} {β : Type u_2} [complete_lattice β] [DecidableEq α] (a : α)
    (s : finset α) (t : α → β) :
    (supr fun (x : α) => supr fun (H : x ∈ insert a s) => t x) =
        t a ⊔ supr fun (x : α) => supr fun (H : x ∈ s) => t x :=
  sorry

theorem infi_insert {α : Type u_1} {β : Type u_2} [complete_lattice β] [DecidableEq α] (a : α)
    (s : finset α) (t : α → β) :
    (infi fun (x : α) => infi fun (H : x ∈ insert a s) => t x) =
        t a ⊓ infi fun (x : α) => infi fun (H : x ∈ s) => t x :=
  sorry

theorem supr_finset_image {α : Type u_1} {β : Type u_2} {γ : Type u_3} [complete_lattice β]
    [DecidableEq α] {f : γ → α} {g : α → β} {s : finset γ} :
    (supr fun (x : α) => supr fun (H : x ∈ image f s) => g x) =
        supr fun (y : γ) => supr fun (H : y ∈ s) => g (f y) :=
  sorry

theorem sup_finset_image {α : Type u_1} {β : Type u_2} {γ : Type u_3} [complete_lattice β]
    [DecidableEq α] {f : γ → α} {g : α → β} {s : finset γ} : sup s (g ∘ f) = sup (image f s) g :=
  sorry

theorem infi_finset_image {α : Type u_1} {β : Type u_2} {γ : Type u_3} [complete_lattice β]
    [DecidableEq α] {f : γ → α} {g : α → β} {s : finset γ} :
    (infi fun (x : α) => infi fun (H : x ∈ image f s) => g x) =
        infi fun (y : γ) => infi fun (H : y ∈ s) => g (f y) :=
  sorry

theorem supr_insert_update {α : Type u_1} {β : Type u_2} [complete_lattice β] [DecidableEq α]
    {x : α} {t : finset α} (f : α → β) {s : β} (hx : ¬x ∈ t) :
    (supr fun (i : α) => supr fun (H : i ∈ insert x t) => function.update f x s i) =
        s ⊔ supr fun (i : α) => supr fun (H : i ∈ t) => f i :=
  sorry

theorem infi_insert_update {α : Type u_1} {β : Type u_2} [complete_lattice β] [DecidableEq α]
    {x : α} {t : finset α} (f : α → β) {s : β} (hx : ¬x ∈ t) :
    (infi fun (i : α) => infi fun (H : i ∈ insert x t) => function.update f x s i) =
        s ⊓ infi fun (i : α) => infi fun (H : i ∈ t) => f i :=
  supr_insert_update f hx

theorem supr_bUnion {α : Type u_1} {β : Type u_2} {γ : Type u_3} [complete_lattice β]
    [DecidableEq α] (s : finset γ) (t : γ → finset α) (f : α → β) :
    (supr fun (y : α) => supr fun (H : y ∈ finset.bUnion s t) => f y) =
        supr
          fun (x : γ) =>
            supr fun (H : x ∈ s) => supr fun (y : α) => supr fun (H : y ∈ t x) => f y :=
  sorry

theorem infi_bUnion {α : Type u_1} {β : Type u_2} {γ : Type u_3} [complete_lattice β]
    [DecidableEq α] (s : finset γ) (t : γ → finset α) (f : α → β) :
    (infi fun (y : α) => infi fun (H : y ∈ finset.bUnion s t) => f y) =
        infi
          fun (x : γ) =>
            infi fun (H : x ∈ s) => infi fun (y : α) => infi fun (H : y ∈ t x) => f y :=
  supr_bUnion s t fun (y : α) => f y

@[simp] theorem set_bUnion_coe {α : Type u_1} {β : Type u_2} (s : finset α) (t : α → set β) :
    (set.Union fun (x : α) => set.Union fun (H : x ∈ ↑s) => t x) =
        set.Union fun (x : α) => set.Union fun (H : x ∈ s) => t x :=
  rfl

@[simp] theorem set_bInter_coe {α : Type u_1} {β : Type u_2} (s : finset α) (t : α → set β) :
    (set.Inter fun (x : α) => set.Inter fun (H : x ∈ ↑s) => t x) =
        set.Inter fun (x : α) => set.Inter fun (H : x ∈ s) => t x :=
  rfl

@[simp] theorem set_bUnion_singleton {α : Type u_1} {β : Type u_2} (a : α) (s : α → set β) :
    (set.Union fun (x : α) => set.Union fun (H : x ∈ singleton a) => s x) = s a :=
  supr_singleton a s

@[simp] theorem set_bInter_singleton {α : Type u_1} {β : Type u_2} (a : α) (s : α → set β) :
    (set.Inter fun (x : α) => set.Inter fun (H : x ∈ singleton a) => s x) = s a :=
  infi_singleton a s

@[simp] theorem set_bUnion_preimage_singleton {α : Type u_1} {β : Type u_2} (f : α → β)
    (s : finset β) :
    (set.Union fun (y : β) => set.Union fun (H : y ∈ s) => f ⁻¹' singleton y) = f ⁻¹' ↑s :=
  set.bUnion_preimage_singleton f ↑s

@[simp] theorem set_bUnion_option_to_finset {α : Type u_1} {β : Type u_2} (o : Option α)
    (f : α → set β) :
    (set.Union fun (x : α) => set.Union fun (H : x ∈ option.to_finset o) => f x) =
        set.Union fun (x : α) => set.Union fun (H : x ∈ o) => f x :=
  supr_option_to_finset o f

@[simp] theorem set_bInter_option_to_finset {α : Type u_1} {β : Type u_2} (o : Option α)
    (f : α → set β) :
    (set.Inter fun (x : α) => set.Inter fun (H : x ∈ option.to_finset o) => f x) =
        set.Inter fun (x : α) => set.Inter fun (H : x ∈ o) => f x :=
  infi_option_to_finset o f

theorem set_bUnion_union {α : Type u_1} {β : Type u_2} [DecidableEq α] (s : finset α) (t : finset α)
    (u : α → set β) :
    (set.Union fun (x : α) => set.Union fun (H : x ∈ s ∪ t) => u x) =
        (set.Union fun (x : α) => set.Union fun (H : x ∈ s) => u x) ∪
          set.Union fun (x : α) => set.Union fun (H : x ∈ t) => u x :=
  supr_union

theorem set_bInter_inter {α : Type u_1} {β : Type u_2} [DecidableEq α] (s : finset α) (t : finset α)
    (u : α → set β) :
    (set.Inter fun (x : α) => set.Inter fun (H : x ∈ s ∪ t) => u x) =
        (set.Inter fun (x : α) => set.Inter fun (H : x ∈ s) => u x) ∩
          set.Inter fun (x : α) => set.Inter fun (H : x ∈ t) => u x :=
  infi_union

@[simp] theorem set_bUnion_insert {α : Type u_1} {β : Type u_2} [DecidableEq α] (a : α)
    (s : finset α) (t : α → set β) :
    (set.Union fun (x : α) => set.Union fun (H : x ∈ insert a s) => t x) =
        t a ∪ set.Union fun (x : α) => set.Union fun (H : x ∈ s) => t x :=
  supr_insert a s t

@[simp] theorem set_bInter_insert {α : Type u_1} {β : Type u_2} [DecidableEq α] (a : α)
    (s : finset α) (t : α → set β) :
    (set.Inter fun (x : α) => set.Inter fun (H : x ∈ insert a s) => t x) =
        t a ∩ set.Inter fun (x : α) => set.Inter fun (H : x ∈ s) => t x :=
  infi_insert a s t

@[simp] theorem set_bUnion_finset_image {α : Type u_1} {β : Type u_2} {γ : Type u_3} [DecidableEq α]
    {f : γ → α} {g : α → set β} {s : finset γ} :
    (set.Union fun (x : α) => set.Union fun (H : x ∈ image f s) => g x) =
        set.Union fun (y : γ) => set.Union fun (H : y ∈ s) => g (f y) :=
  supr_finset_image

@[simp] theorem set_bInter_finset_image {α : Type u_1} {β : Type u_2} {γ : Type u_3} [DecidableEq α]
    {f : γ → α} {g : α → set β} {s : finset γ} :
    (set.Inter fun (x : α) => set.Inter fun (H : x ∈ image f s) => g x) =
        set.Inter fun (y : γ) => set.Inter fun (H : y ∈ s) => g (f y) :=
  infi_finset_image

theorem set_bUnion_insert_update {α : Type u_1} {β : Type u_2} [DecidableEq α] {x : α}
    {t : finset α} (f : α → set β) {s : set β} (hx : ¬x ∈ t) :
    (set.Union fun (i : α) => set.Union fun (H : i ∈ insert x t) => function.update f x s i) =
        s ∪ set.Union fun (i : α) => set.Union fun (H : i ∈ t) => f i :=
  supr_insert_update f hx

theorem set_bInter_insert_update {α : Type u_1} {β : Type u_2} [DecidableEq α] {x : α}
    {t : finset α} (f : α → set β) {s : set β} (hx : ¬x ∈ t) :
    (set.Inter fun (i : α) => set.Inter fun (H : i ∈ insert x t) => function.update f x s i) =
        s ∩ set.Inter fun (i : α) => set.Inter fun (H : i ∈ t) => f i :=
  infi_insert_update f hx

@[simp] theorem set_bUnion_bUnion {α : Type u_1} {β : Type u_2} {γ : Type u_3} [DecidableEq α]
    (s : finset γ) (t : γ → finset α) (f : α → set β) :
    (set.Union fun (y : α) => set.Union fun (H : y ∈ finset.bUnion s t) => f y) =
        set.Union
          fun (x : γ) =>
            set.Union
              fun (H : x ∈ s) => set.Union fun (y : α) => set.Union fun (H : y ∈ t x) => f y :=
  supr_bUnion s t f

@[simp] theorem set_bInter_bUnion {α : Type u_1} {β : Type u_2} {γ : Type u_3} [DecidableEq α]
    (s : finset γ) (t : γ → finset α) (f : α → set β) :
    (set.Inter fun (y : α) => set.Inter fun (H : y ∈ finset.bUnion s t) => f y) =
        set.Inter
          fun (x : γ) =>
            set.Inter
              fun (H : x ∈ s) => set.Inter fun (y : α) => set.Inter fun (H : y ∈ t x) => f y :=
  infi_bUnion s t f

end Mathlib