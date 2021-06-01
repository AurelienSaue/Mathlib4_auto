/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.set_theory.ordinal_arithmetic
import Mathlib.tactic.omega.default
import Mathlib.PostPort

universes u_1 u v w u_2 

namespace Mathlib

/-!
# Cardinals and ordinals

Relationships between cardinals and ordinals, properties of cardinals that are proved
using ordinals.

## Main definitions and results

* The `aleph'` function gives the cardinals listed by their ordinal
  index, and is the inverse of `aleph_idx`.
  `aleph' n = n`, `aleph' ω = ω`, `aleph' (ω + 1) = ℵ₁`, etc. It is an order isomorphism
  between ordinals and cardinals.
* The `aleph` function gives the infinite cardinals listed by their
  ordinal index. `aleph 0 = ω`, `aleph 1 = succ ω` is the first
  uncountable cardinal, and so on.

* `mul_eq_max` and `add_eq_max` state that the product (resp. sum) of two infinite cardinals
  is just their maximum. Several variations around this fact are also given.
* `mk_list_eq_mk` : when `α` is infinite, `α` and `list α` have the same cardinality.
* simp lemmas for inequalities between `bit0 a` and `bit1 b` are registered, making simp
  able to prove inequalities about numeral cardinals.
-/

namespace cardinal


theorem ord_is_limit {c : cardinal} (co : omega ≤ c) : ordinal.is_limit (ord c) := sorry

/-- The `aleph'` index function, which gives the ordinal index of a cardinal.
  (The `aleph'` part is because unlike `aleph` this counts also the
  finite stages. So `aleph_idx n = n`, `aleph_idx ω = ω`,
  `aleph_idx ℵ₁ = ω + 1` and so on.)
  In this definition, we register additionally that this function is an initial segment,
  i.e., it is order preserving and its range is an initial segment of the ordinals.
  For the basic function version, see `aleph_idx`.
  For an upgraded version stating that the range is everything, see `aleph_idx.rel_iso`. -/
def aleph_idx.initial_seg : initial_seg Less Less :=
  rel_embedding.collapse (order_embedding.lt_embedding ord.order_embedding)

/-- The `aleph'` index function, which gives the ordinal index of a cardinal.
  (The `aleph'` part is because unlike `aleph` this counts also the
  finite stages. So `aleph_idx n = n`, `aleph_idx ω = ω`,
  `aleph_idx ℵ₁ = ω + 1` and so on.)
  For an upgraded version stating that the range is everything, see `aleph_idx.rel_iso`. -/
def aleph_idx : cardinal → ordinal := ⇑sorry

@[simp] theorem aleph_idx.initial_seg_coe : ⇑aleph_idx.initial_seg = aleph_idx := rfl

@[simp] theorem aleph_idx_lt {a : cardinal} {b : cardinal} : aleph_idx a < aleph_idx b ↔ a < b :=
  rel_embedding.map_rel_iff (initial_seg.to_rel_embedding aleph_idx.initial_seg)

@[simp] theorem aleph_idx_le {a : cardinal} {b : cardinal} : aleph_idx a ≤ aleph_idx b ↔ a ≤ b :=
  sorry

theorem aleph_idx.init {a : cardinal} {b : ordinal} :
    b < aleph_idx a → ∃ (c : cardinal), aleph_idx c = b :=
  initial_seg.init aleph_idx.initial_seg a b

/-- The `aleph'` index function, which gives the ordinal index of a cardinal.
  (The `aleph'` part is because unlike `aleph` this counts also the
  finite stages. So `aleph_idx n = n`, `aleph_idx ω = ω`,
  `aleph_idx ℵ₁ = ω + 1` and so on.)
  In this version, we register additionally that this function is an order isomorphism
  between cardinals and ordinals.
  For the basic function version, see `aleph_idx`. -/
def aleph_idx.rel_iso : Less ≃r Less := rel_iso.of_surjective ↑aleph_idx.initial_seg sorry

@[simp] theorem aleph_idx.rel_iso_coe : ⇑aleph_idx.rel_iso = aleph_idx := rfl

@[simp] theorem type_cardinal : ordinal.type Less = ordinal.univ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (ordinal.type Less = ordinal.univ)) ordinal.univ_id))
    (quotient.sound (Nonempty.intro aleph_idx.rel_iso))

@[simp] theorem mk_cardinal : mk cardinal = univ := sorry

/-- The `aleph'` function gives the cardinals listed by their ordinal
  index, and is the inverse of `aleph_idx`.
  `aleph' n = n`, `aleph' ω = ω`, `aleph' (ω + 1) = ℵ₁`, etc.
  In this version, we register additionally that this function is an order isomorphism
  between ordinals and cardinals.
  For the basic function version, see `aleph'`. -/
def aleph'.rel_iso : Less ≃r Less := rel_iso.symm aleph_idx.rel_iso

/-- The `aleph'` function gives the cardinals listed by their ordinal
  index, and is the inverse of `aleph_idx`.
  `aleph' n = n`, `aleph' ω = ω`, `aleph' (ω + 1) = ℵ₁`, etc. -/
def aleph' : ordinal → cardinal := ⇑sorry

@[simp] theorem aleph'.rel_iso_coe : ⇑aleph'.rel_iso = aleph' := rfl

@[simp] theorem aleph'_lt {o₁ : ordinal} {o₂ : ordinal} : aleph' o₁ < aleph' o₂ ↔ o₁ < o₂ :=
  rel_iso.map_rel_iff aleph'.rel_iso

@[simp] theorem aleph'_le {o₁ : ordinal} {o₂ : ordinal} : aleph' o₁ ≤ aleph' o₂ ↔ o₁ ≤ o₂ :=
  iff.mpr le_iff_le_iff_lt_iff_lt aleph'_lt

@[simp] theorem aleph'_aleph_idx (c : cardinal) : aleph' (aleph_idx c) = c :=
  equiv.symm_apply_apply (rel_iso.to_equiv aleph_idx.rel_iso) c

@[simp] theorem aleph_idx_aleph' (o : ordinal) : aleph_idx (aleph' o) = o :=
  equiv.apply_symm_apply (rel_iso.to_equiv aleph_idx.rel_iso) o

@[simp] theorem aleph'_zero : aleph' 0 = 0 := sorry

@[simp] theorem aleph'_succ {o : ordinal} : aleph' (ordinal.succ o) = succ (aleph' o) := sorry

@[simp] theorem aleph'_nat (n : ℕ) : aleph' ↑n = ↑n := sorry

theorem aleph'_le_of_limit {o : ordinal} (l : ordinal.is_limit o) {c : cardinal} :
    aleph' o ≤ c ↔ ∀ (o' : ordinal), o' < o → aleph' o' ≤ c :=
  sorry

@[simp] theorem aleph'_omega : aleph' ordinal.omega = omega := sorry

/-- `aleph'` and `aleph_idx` form an equivalence between `ordinal` and `cardinal` -/
@[simp] def aleph'_equiv : ordinal ≃ cardinal :=
  equiv.mk aleph' aleph_idx aleph_idx_aleph' aleph'_aleph_idx

/-- The `aleph` function gives the infinite cardinals listed by their
  ordinal index. `aleph 0 = ω`, `aleph 1 = succ ω` is the first
  uncountable cardinal, and so on. -/
def aleph (o : ordinal) : cardinal := aleph' (ordinal.omega + o)

@[simp] theorem aleph_lt {o₁ : ordinal} {o₂ : ordinal} : aleph o₁ < aleph o₂ ↔ o₁ < o₂ :=
  iff.trans aleph'_lt (ordinal.add_lt_add_iff_left ordinal.omega)

@[simp] theorem aleph_le {o₁ : ordinal} {o₂ : ordinal} : aleph o₁ ≤ aleph o₂ ↔ o₁ ≤ o₂ :=
  iff.mpr le_iff_le_iff_lt_iff_lt aleph_lt

@[simp] theorem aleph_succ {o : ordinal} : aleph (ordinal.succ o) = succ (aleph o) := sorry

@[simp] theorem aleph_zero : aleph 0 = omega := sorry

theorem omega_le_aleph' {o : ordinal} : omega ≤ aleph' o ↔ ordinal.omega ≤ o :=
  eq.mpr (id (Eq._oldrec (Eq.refl (omega ≤ aleph' o ↔ ordinal.omega ≤ o)) (Eq.symm aleph'_omega)))
    (eq.mpr
      (id
        (Eq._oldrec (Eq.refl (aleph' ordinal.omega ≤ aleph' o ↔ ordinal.omega ≤ o))
          (propext aleph'_le)))
      (iff.refl (ordinal.omega ≤ o)))

theorem omega_le_aleph (o : ordinal) : omega ≤ aleph o :=
  eq.mpr (id (Eq._oldrec (Eq.refl (omega ≤ aleph o)) (aleph.equations._eqn_1 o)))
    (eq.mpr
      (id (Eq._oldrec (Eq.refl (omega ≤ aleph' (ordinal.omega + o))) (propext omega_le_aleph')))
      (ordinal.le_add_right ordinal.omega o))

theorem ord_aleph_is_limit (o : ordinal) : ordinal.is_limit (ord (aleph o)) :=
  ord_is_limit (omega_le_aleph o)

theorem exists_aleph {c : cardinal} : omega ≤ c ↔ ∃ (o : ordinal), c = aleph o := sorry

theorem aleph'_is_normal : ordinal.is_normal (ord ∘ aleph') := sorry

theorem aleph_is_normal : ordinal.is_normal (ord ∘ aleph) :=
  ordinal.is_normal.trans aleph'_is_normal (ordinal.add_is_normal ordinal.omega)

/-! ### Properties of `mul` -/

/-- If `α` is an infinite type, then `α × α` and `α` have the same cardinality. -/
theorem mul_eq_self {c : cardinal} (h : omega ≤ c) : c * c = c := sorry

/-- If `α` and `β` are infinite types, then the cardinality of `α × β` is the maximum
of the cardinalities of `α` and `β`. -/
theorem mul_eq_max {a : cardinal} {b : cardinal} (ha : omega ≤ a) (hb : omega ≤ b) :
    a * b = max a b :=
  sorry

theorem mul_lt_of_lt {a : cardinal} {b : cardinal} {c : cardinal} (hc : omega ≤ c) (h1 : a < c)
    (h2 : b < c) : a * b < c :=
  sorry

theorem mul_le_max_of_omega_le_left {a : cardinal} {b : cardinal} (h : omega ≤ a) :
    a * b ≤ max a b :=
  sorry

theorem mul_eq_max_of_omega_le_left {a : cardinal} {b : cardinal} (h : omega ≤ a) (h' : b ≠ 0) :
    a * b = max a b :=
  sorry

theorem mul_eq_left {a : cardinal} {b : cardinal} (ha : omega ≤ a) (hb : b ≤ a) (hb' : b ≠ 0) :
    a * b = a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a * b = a)) (mul_eq_max_of_omega_le_left ha hb')))
    (eq.mpr (id (Eq._oldrec (Eq.refl (max a b = a)) (max_eq_left hb))) (Eq.refl a))

theorem mul_eq_right {a : cardinal} {b : cardinal} (hb : omega ≤ b) (ha : a ≤ b) (ha' : a ≠ 0) :
    a * b = b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a * b = b)) (mul_comm a b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b * a = b)) (mul_eq_left hb ha ha'))) (Eq.refl b))

theorem le_mul_left {a : cardinal} {b : cardinal} (h : b ≠ 0) : a ≤ b * a := sorry

theorem le_mul_right {a : cardinal} {b : cardinal} (h : b ≠ 0) : a ≤ a * b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ≤ a * b)) (mul_comm a b))) (le_mul_left h)

theorem mul_eq_left_iff {a : cardinal} {b : cardinal} :
    a * b = a ↔ max omega b ≤ a ∧ b ≠ 0 ∨ b = 1 ∨ a = 0 :=
  sorry

/-! ### Properties of `add` -/

/-- If `α` is an infinite type, then `α ⊕ α` and `α` have the same cardinality. -/
theorem add_eq_self {c : cardinal} (h : omega ≤ c) : c + c = c := sorry

/-- If `α` is an infinite type, then the cardinality of `α ⊕ β` is the maximum
of the cardinalities of `α` and `β`. -/
theorem add_eq_max {a : cardinal} {b : cardinal} (ha : omega ≤ a) : a + b = max a b :=
  le_antisymm
    (add_eq_self (le_trans ha (le_max_left a b)) ▸ add_le_add (le_max_left a b) (le_max_right a b))
    (max_le (self_le_add_right a b) (self_le_add_left b a))

theorem add_lt_of_lt {a : cardinal} {b : cardinal} {c : cardinal} (hc : omega ≤ c) (h1 : a < c)
    (h2 : b < c) : a + b < c :=
  sorry

theorem eq_of_add_eq_of_omega_le {a : cardinal} {b : cardinal} {c : cardinal} (h : a + b = c)
    (ha : a < c) (hc : omega ≤ c) : b = c :=
  sorry

theorem add_eq_left {a : cardinal} {b : cardinal} (ha : omega ≤ a) (hb : b ≤ a) : a + b = a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a + b = a)) (add_eq_max ha)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (max a b = a)) (max_eq_left hb))) (Eq.refl a))

theorem add_eq_right {a : cardinal} {b : cardinal} (hb : omega ≤ b) (ha : a ≤ b) : a + b = b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a + b = b)) (add_comm a b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b + a = b)) (add_eq_left hb ha))) (Eq.refl b))

theorem add_eq_left_iff {a : cardinal} {b : cardinal} : a + b = a ↔ max omega b ≤ a ∨ b = 0 := sorry

theorem add_eq_right_iff {a : cardinal} {b : cardinal} : a + b = b ↔ max omega a ≤ b ∨ a = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a + b = b ↔ max omega a ≤ b ∨ a = 0)) (add_comm a b)))
    (eq.mpr
      (id (Eq._oldrec (Eq.refl (b + a = b ↔ max omega a ≤ b ∨ a = 0)) (propext add_eq_left_iff)))
      (iff.refl (max omega a ≤ b ∨ a = 0)))

theorem add_one_eq {a : cardinal} (ha : omega ≤ a) : a + 1 = a :=
  (fun (this : 1 ≤ a) => add_eq_left ha this) (le_trans (le_of_lt one_lt_omega) ha)

protected theorem eq_of_add_eq_add_left {a : cardinal} {b : cardinal} {c : cardinal}
    (h : a + b = a + c) (ha : a < omega) : b = c :=
  sorry

protected theorem eq_of_add_eq_add_right {a : cardinal} {b : cardinal} {c : cardinal}
    (h : a + b = c + b) (hb : b < omega) : a = c :=
  sorry

/-! ### Properties about power -/

theorem pow_le {κ : cardinal} {μ : cardinal} (H1 : omega ≤ κ) (H2 : μ < omega) : κ ^ μ ≤ κ := sorry

theorem power_self_eq {c : cardinal} (h : omega ≤ c) : c ^ c = bit0 1 ^ c := sorry

theorem power_nat_le {c : cardinal} {n : ℕ} (h : omega ≤ c) : c ^ ↑n ≤ c :=
  pow_le h (nat_lt_omega n)

theorem powerlt_omega {c : cardinal} (h : omega ≤ c) : c ^< omega = c := sorry

theorem powerlt_omega_le (c : cardinal) : c ^< omega ≤ max c omega := sorry

/-! ### Computing cardinality of various types -/

theorem mk_list_eq_mk {α : Type u} (H1 : omega ≤ mk α) : mk (List α) = mk α := sorry

theorem mk_finset_eq_mk {α : Type u} (h : omega ≤ mk α) : mk (finset α) = mk α :=
  Eq.symm
    (le_antisymm (mk_le_of_injective fun (x y : α) => iff.mp finset.singleton_inj)
      (trans_rel_left LessEq (mk_le_of_surjective list.to_finset_surjective) (mk_list_eq_mk h)))

theorem mk_bounded_set_le_of_omega_le (α : Type u) (c : cardinal) (hα : omega ≤ mk α) :
    mk (Subtype fun (t : set α) => mk ↥t ≤ c) ≤ mk α ^ c :=
  sorry

theorem mk_bounded_set_le (α : Type u) (c : cardinal) :
    mk (Subtype fun (t : set α) => mk ↥t ≤ c) ≤ max (mk α) omega ^ c :=
  sorry

theorem mk_bounded_subset_le {α : Type u} (s : set α) (c : cardinal) :
    mk (Subtype fun (t : set α) => t ⊆ s ∧ mk ↥t ≤ c) ≤ max (mk ↥s) omega ^ c :=
  sorry

/-! ### Properties of `compl` -/

theorem mk_compl_of_omega_le {α : Type u_1} (s : set α) (h : omega ≤ mk α) (h2 : mk ↥s < mk α) :
    mk ↥(sᶜ) = mk α :=
  eq_of_add_eq_of_omega_le (mk_sum_compl s) h2 h

theorem mk_compl_finset_of_omega_le {α : Type u_1} (s : finset α) (h : omega ≤ mk α) :
    mk ↥(↑sᶜ) = mk α :=
  mk_compl_of_omega_le (↑s) h (lt_of_lt_of_le (finset_card_lt_omega s) h)

theorem mk_compl_eq_mk_compl_infinite {α : Type u_1} {s : set α} {t : set α} (h : omega ≤ mk α)
    (hs : mk ↥s < mk α) (ht : mk ↥t < mk α) : mk ↥(sᶜ) = mk ↥(tᶜ) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (mk ↥(sᶜ) = mk ↥(tᶜ))) (mk_compl_of_omega_le s h hs)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (mk α = mk ↥(tᶜ))) (mk_compl_of_omega_le t h ht)))
      (Eq.refl (mk α)))

theorem mk_compl_eq_mk_compl_finite_lift {α : Type u} {β : Type v} {s : set α} {t : set β}
    (hα : mk α < omega) (h1 : lift (mk α) = lift (mk β)) (h2 : lift (mk ↥s) = lift (mk ↥t)) :
    lift (mk ↥(sᶜ)) = lift (mk ↥(tᶜ)) :=
  sorry

theorem mk_compl_eq_mk_compl_finite {α : Type u} {β : Type u} {s : set α} {t : set β}
    (hα : mk α < omega) (h1 : mk α = mk β) (h : mk ↥s = mk ↥t) : mk ↥(sᶜ) = mk ↥(tᶜ) :=
  sorry

theorem mk_compl_eq_mk_compl_finite_same {α : Type u_1} {s : set α} {t : set α} (hα : mk α < omega)
    (h : mk ↥s = mk ↥t) : mk ↥(sᶜ) = mk ↥(tᶜ) :=
  mk_compl_eq_mk_compl_finite hα rfl h

/-! ### Extending an injection to an equiv -/

theorem extend_function {α : Type u_1} {β : Type u_2} {s : set α} (f : ↥s ↪ β)
    (h : Nonempty (↥(sᶜ) ≃ ↥(set.range ⇑fᶜ))) :
    ∃ (g : α ≃ β), ∀ (x : ↥s), coe_fn g ↑x = coe_fn f x :=
  sorry

theorem extend_function_finite {α : Type u_1} {β : Type u_2} {s : set α} (f : ↥s ↪ β)
    (hs : mk α < omega) (h : Nonempty (α ≃ β)) :
    ∃ (g : α ≃ β), ∀ (x : ↥s), coe_fn g ↑x = coe_fn f x :=
  sorry

theorem extend_function_of_lt {α : Type u_1} {β : Type u_2} {s : set α} (f : ↥s ↪ β)
    (hs : mk ↥s < mk α) (h : Nonempty (α ≃ β)) :
    ∃ (g : α ≃ β), ∀ (x : ↥s), coe_fn g ↑x = coe_fn f x :=
  sorry

/-!
This section proves inequalities for `bit0` and `bit1`, enabling `simp` to solve inequalities
for numeral cardinals. The complexity of the resulting algorithm is not good, as in some cases
`simp` reduces an inequality to a disjunction of two situations, depending on whether a cardinal
is finite or infinite. Since the evaluation of the branches is not lazy, this is bad. It is good
enough for practical situations, though.

For specific numbers, these inequalities could also be deduced from the corresponding
inequalities of natural numbers using `norm_cast`:
```
example : (37 : cardinal) < 42 :=
by { norm_cast, norm_num }
```
-/

@[simp] theorem bit0_ne_zero (a : cardinal) : ¬bit0 a = 0 ↔ ¬a = 0 := sorry

@[simp] theorem bit1_ne_zero (a : cardinal) : ¬bit1 a = 0 := sorry

@[simp] theorem zero_lt_bit0 (a : cardinal) : 0 < bit0 a ↔ 0 < a := sorry

@[simp] theorem zero_lt_bit1 (a : cardinal) : 0 < bit1 a :=
  lt_of_lt_of_le zero_lt_one (self_le_add_left 1 (bit0 a))

@[simp] theorem one_le_bit0 (a : cardinal) : 1 ≤ bit0 a ↔ 0 < a :=
  { mp := fun (h : 1 ≤ bit0 a) => iff.mp (zero_lt_bit0 a) (lt_of_lt_of_le zero_lt_one h),
    mpr := fun (h : 0 < a) => le_trans (iff.mpr one_le_iff_pos h) (self_le_add_left a a) }

@[simp] theorem one_le_bit1 (a : cardinal) : 1 ≤ bit1 a := self_le_add_left 1 (bit0 a)

theorem bit0_eq_self {c : cardinal} (h : omega ≤ c) : bit0 c = c := add_eq_self h

@[simp] theorem bit0_lt_omega {c : cardinal} : bit0 c < omega ↔ c < omega := sorry

@[simp] theorem omega_le_bit0 {c : cardinal} : omega ≤ bit0 c ↔ omega ≤ c := sorry

@[simp] theorem bit1_eq_self_iff {c : cardinal} : bit1 c = c ↔ omega ≤ c := sorry

@[simp] theorem bit1_lt_omega {c : cardinal} : bit1 c < omega ↔ c < omega := sorry

@[simp] theorem omega_le_bit1 {c : cardinal} : omega ≤ bit1 c ↔ omega ≤ c := sorry

@[simp] theorem bit0_le_bit0 {a : cardinal} {b : cardinal} : bit0 a ≤ bit0 b ↔ a ≤ b := sorry

@[simp] theorem bit0_le_bit1 {a : cardinal} {b : cardinal} : bit0 a ≤ bit1 b ↔ a ≤ b := sorry

@[simp] theorem bit1_le_bit1 {a : cardinal} {b : cardinal} : bit1 a ≤ bit1 b ↔ a ≤ b :=
  { mp :=
      fun (h : bit1 a ≤ bit1 b) => iff.mp bit0_le_bit1 (le_trans (self_le_add_right (bit0 a) 1) h),
    mpr :=
      fun (h : a ≤ b) =>
        le_trans (add_le_add_right (add_le_add_left h a) 1)
          (add_le_add_right (add_le_add_right h b) 1) }

@[simp] theorem bit1_le_bit0 {a : cardinal} {b : cardinal} :
    bit1 a ≤ bit0 b ↔ a < b ∨ a ≤ b ∧ omega ≤ a :=
  sorry

@[simp] theorem bit0_lt_bit0 {a : cardinal} {b : cardinal} : bit0 a < bit0 b ↔ a < b := sorry

@[simp] theorem bit1_lt_bit0 {a : cardinal} {b : cardinal} : bit1 a < bit0 b ↔ a < b := sorry

@[simp] theorem bit1_lt_bit1 {a : cardinal} {b : cardinal} : bit1 a < bit1 b ↔ a < b := sorry

@[simp] theorem bit0_lt_bit1 {a : cardinal} {b : cardinal} :
    bit0 a < bit1 b ↔ a < b ∨ a ≤ b ∧ a < omega :=
  sorry

-- This strategy works generally to prove inequalities between numerals in `cardinality`.

theorem one_lt_two : 1 < bit0 1 := sorry

@[simp] theorem one_lt_bit0 {a : cardinal} : 1 < bit0 a ↔ 0 < a := sorry

@[simp] theorem one_lt_bit1 (a : cardinal) : 1 < bit1 a ↔ 0 < a := sorry

@[simp] theorem one_le_one : 1 ≤ 1 := le_refl 1

end Mathlib