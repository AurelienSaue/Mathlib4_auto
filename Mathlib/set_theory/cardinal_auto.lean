/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.set.countable
import Mathlib.set_theory.schroeder_bernstein
import Mathlib.data.fintype.card
import Mathlib.PostPort

universes u u_1 u_2 v w u_3 

namespace Mathlib

/-!
# Cardinal Numbers

We define cardinal numbers as a quotient of types under the equivalence relation of equinumerity.
We define the order on cardinal numbers, define omega, and do basic cardinal arithmetic:
  addition, multiplication, power, cardinal successor, minimum, supremum,
    infinitary sums and products

The fact that the cardinality of `α × α` coincides with that of `α` when `α` is infinite is not
proved in this file, as it relies on facts on well-orders. Instead, it is in
`cardinal_ordinal.lean` (together with many other facts on cardinals, for instance the
cardinality of `list α`).

## Implementation notes

* There is a type of cardinal numbers in every universe level: `cardinal.{u} : Type (u + 1)`
  is the quotient of types in `Type u`.
  There is a lift operation lifting cardinal numbers to a higher level.
* Cardinal arithmetic specifically for infinite cardinals (like `κ * κ = κ`) is in the file
  `set_theory/ordinal.lean`, because concepts from that file are used in the proof.

## References

* <https://en.wikipedia.org/wiki/Cardinal_number>

## Tags

cardinal number, cardinal arithmetic, cardinal exponentiation, omega
-/

/-- The equivalence relation on types given by equivalence (bijective correspondence) of types.
  Quotienting by this equivalence relation gives the cardinal numbers.
-/
protected instance cardinal.is_equivalent : setoid (Type u) :=
  setoid.mk (fun (α β : Type u) => Nonempty (α ≃ β)) sorry

/-- `cardinal.{u}` is the type of cardinal numbers in `Type u`,
  defined as the quotient of `Type u` by existence of an equivalence
  (a bijection with explicit inverse). -/
def cardinal := quotient sorry

namespace cardinal


/-- The cardinal number of a type -/
def mk : Type u → cardinal := quotient.mk

protected theorem eq {α : Type u} {β : Type u} : mk α = mk β ↔ Nonempty (α ≃ β) := quotient.eq

@[simp] theorem mk_def (α : Type u) : quotient.mk α = mk α := rfl

@[simp] theorem mk_out (c : cardinal) : mk (quotient.out c) = c := quotient.out_eq c

/-- We define the order on cardinal numbers by `mk α ≤ mk β` if and only if
  there exists an embedding (injective function) from α to β. -/
protected instance has_le : HasLessEq cardinal :=
  { LessEq :=
      fun (q₁ q₂ : cardinal) =>
        quotient.lift_on₂ q₁ q₂ (fun (α β : Type u) => Nonempty (α ↪ β)) sorry }

theorem mk_le_of_injective {α : Type u} {β : Type u} {f : α → β} (hf : function.injective f) :
    mk α ≤ mk β :=
  Nonempty.intro (function.embedding.mk f hf)

theorem mk_le_of_surjective {α : Type u} {β : Type u} {f : α → β} (hf : function.surjective f) :
    mk β ≤ mk α :=
  Nonempty.intro (function.embedding.of_surjective f hf)

theorem le_mk_iff_exists_set {c : cardinal} {α : Type u} : c ≤ mk α ↔ ∃ (p : set α), mk ↥p = c :=
  sorry

theorem out_embedding {c : cardinal} {c' : cardinal} :
    c ≤ c' ↔ Nonempty (quotient.out c ↪ quotient.out c') :=
  sorry

protected instance linear_order : linear_order cardinal :=
  linear_order.mk LessEq (partial_order.lt._default LessEq) sorry sorry sorry sorry
    (classical.dec_rel LessEq) Mathlib.decidable_eq_of_decidable_le
    Mathlib.decidable_lt_of_decidable_le

protected instance distrib_lattice : distrib_lattice cardinal :=
  Mathlib.distrib_lattice_of_linear_order

protected instance has_zero : HasZero cardinal := { zero := quotient.mk pempty }

protected instance inhabited : Inhabited cardinal := { default := 0 }

theorem ne_zero_iff_nonempty {α : Type u} : mk α ≠ 0 ↔ Nonempty α := sorry

protected instance has_one : HasOne cardinal := { one := quotient.mk PUnit }

protected instance nontrivial : nontrivial cardinal :=
  nontrivial.mk
    (Exists.intro 1 (Exists.intro 0 (iff.mpr ne_zero_iff_nonempty (Nonempty.intro PUnit.unit))))

theorem le_one_iff_subsingleton {α : Type u} : mk α ≤ 1 ↔ subsingleton α := sorry

theorem one_lt_iff_nontrivial {α : Type u} : 1 < mk α ↔ nontrivial α := sorry

protected instance has_add : Add cardinal :=
  { add :=
      fun (q₁ q₂ : cardinal) => quotient.lift_on₂ q₁ q₂ (fun (α β : Type u) => mk (α ⊕ β)) sorry }

@[simp] theorem add_def (α : Type (max u_1 u_2)) (β : Type (max u_1 u_2)) :
    mk α + mk β = mk (α ⊕ β) :=
  rfl

protected instance has_mul : Mul cardinal :=
  { mul :=
      fun (q₁ q₂ : cardinal) => quotient.lift_on₂ q₁ q₂ (fun (α β : Type u) => mk (α × β)) sorry }

@[simp] theorem mul_def (α : Type u) (β : Type u) : mk α * mk β = mk (α × β) := rfl

protected theorem eq_zero_or_eq_zero_of_mul_eq_zero {a : cardinal} {b : cardinal} :
    a * b = 0 → a = 0 ∨ b = 0 :=
  sorry

protected instance comm_semiring : comm_semiring cardinal :=
  comm_semiring.mk Add.add sorry 0 zero_add sorry add_comm Mul.mul sorry 1 one_mul sorry zero_mul
    sorry left_distrib sorry mul_comm

/-- The cardinal exponential. `mk α ^ mk β` is the cardinal of `β → α`. -/
protected def power (a : cardinal) (b : cardinal) : cardinal :=
  quotient.lift_on₂ a b (fun (α β : Type u) => mk (β → α)) sorry

protected instance has_pow : has_pow cardinal cardinal := has_pow.mk cardinal.power

@[simp] theorem power_def (α : Type u_1) (β : Type u_1) : mk α ^ mk β = mk (β → α) := rfl

@[simp] theorem power_zero {a : cardinal} : a ^ 0 = 1 :=
  quotient.induction_on a
    fun (α : Type u_1) => quotient.sound (Nonempty.intro (equiv.pempty_arrow_equiv_punit α))

@[simp] theorem power_one {a : cardinal} : a ^ 1 = a :=
  quotient.induction_on a
    fun (α : Type u_1) => quotient.sound (Nonempty.intro (equiv.punit_arrow_equiv α))

@[simp] theorem one_power {a : cardinal} : 1 ^ a = 1 :=
  quotient.induction_on a
    fun (α : Type u_1) => quotient.sound (Nonempty.intro (equiv.arrow_punit_equiv_punit α))

@[simp] theorem prop_eq_two : mk (ulift Prop) = bit0 1 :=
  quot.sound
    (Nonempty.intro
      (equiv.trans equiv.ulift
        (equiv.trans equiv.Prop_equiv_bool equiv.bool_equiv_punit_sum_punit)))

@[simp] theorem zero_power {a : cardinal} : a ≠ 0 → 0 ^ a = 0 := sorry

theorem power_ne_zero {a : cardinal} (b : cardinal) : a ≠ 0 → a ^ b ≠ 0 := sorry

theorem mul_power {a : cardinal} {b : cardinal} {c : cardinal} : (a * b) ^ c = a ^ c * b ^ c :=
  quotient.induction_on₃ a b c
    fun (α β γ : Type u_1) =>
      quotient.sound (Nonempty.intro (equiv.arrow_prod_equiv_prod_arrow α β γ))

theorem power_add {a : cardinal} {b : cardinal} {c : cardinal} : a ^ (b + c) = a ^ b * a ^ c :=
  quotient.induction_on₃ a b c
    fun (α β γ : Type u_1) =>
      quotient.sound (Nonempty.intro (equiv.sum_arrow_equiv_prod_arrow β γ α))

theorem power_mul {a : cardinal} {b : cardinal} {c : cardinal} : (a ^ b) ^ c = a ^ (b * c) :=
  eq.mpr (id (Eq._oldrec (Eq.refl ((a ^ b) ^ c = a ^ (b * c))) (mul_comm b c)))
    (quotient.induction_on₃ a b c
      fun (α β γ : Type u_1) =>
        quotient.sound (Nonempty.intro (equiv.arrow_arrow_equiv_prod_arrow γ β α)))

@[simp] theorem pow_cast_right (κ : cardinal) (n : ℕ) : κ ^ ↑n = κ ^ n := sorry

protected theorem zero_le (a : cardinal) : 0 ≤ a := sorry

protected theorem add_le_add {a : cardinal} {b : cardinal} {c : cardinal} {d : cardinal} :
    a ≤ b → c ≤ d → a + c ≤ b + d :=
  sorry

protected theorem add_le_add_left (a : cardinal) {b : cardinal} {c : cardinal} :
    b ≤ c → a + b ≤ a + c :=
  cardinal.add_le_add (le_refl a)

protected theorem le_iff_exists_add {a : cardinal} {b : cardinal} :
    a ≤ b ↔ ∃ (c : cardinal), b = a + c :=
  sorry

protected instance order_bot : order_bot cardinal :=
  order_bot.mk 0 linear_order.le linear_order.lt linear_order.le_refl linear_order.le_trans
    linear_order.le_antisymm cardinal.zero_le

protected instance canonically_ordered_comm_semiring : canonically_ordered_comm_semiring cardinal :=
  canonically_ordered_comm_semiring.mk comm_semiring.add comm_semiring.add_assoc comm_semiring.zero
    comm_semiring.zero_add comm_semiring.add_zero comm_semiring.add_comm order_bot.le order_bot.lt
    order_bot.le_refl order_bot.le_trans order_bot.le_antisymm sorry sorry order_bot.bot
    order_bot.bot_le cardinal.le_iff_exists_add comm_semiring.mul comm_semiring.mul_assoc
    comm_semiring.one comm_semiring.one_mul comm_semiring.mul_one comm_semiring.zero_mul
    comm_semiring.mul_zero comm_semiring.left_distrib comm_semiring.right_distrib
    comm_semiring.mul_comm cardinal.eq_zero_or_eq_zero_of_mul_eq_zero

@[simp] theorem zero_lt_one : 0 < 1 := lt_of_le_of_ne (zero_le 1) zero_ne_one

theorem zero_power_le (c : cardinal) : 0 ^ c ≤ 1 := sorry

theorem power_le_power_left {a : cardinal} {b : cardinal} {c : cardinal} :
    a ≠ 0 → b ≤ c → a ^ b ≤ a ^ c :=
  sorry

theorem power_le_max_power_one {a : cardinal} {b : cardinal} {c : cardinal} (h : b ≤ c) :
    a ^ b ≤ max (a ^ c) 1 :=
  sorry

theorem power_le_power_right {a : cardinal} {b : cardinal} {c : cardinal} : a ≤ b → a ^ c ≤ b ^ c :=
  sorry

theorem cantor (a : cardinal) : a < bit0 1 ^ a := sorry

protected instance no_top_order : no_top_order cardinal :=
  no_top_order.mk fun (a : cardinal) => Exists.intro (bit0 1 ^ a) (cantor a)

/-- The minimum cardinal in a family of cardinals (the existence
  of which is provided by `injective_min`). -/
def min {ι : Type u_1} (I : Nonempty ι) (f : ι → cardinal) : cardinal := f (classical.some sorry)

theorem min_eq {ι : Type u_1} (I : Nonempty ι) (f : ι → cardinal) : ∃ (i : ι), min I f = f i :=
  Exists.intro (classical.some (min._proof_1 I f)) rfl

theorem min_le {ι : Type u_1} {I : Nonempty ι} (f : ι → cardinal) (i : ι) : min I f ≤ f i := sorry

theorem le_min {ι : Type u_1} {I : Nonempty ι} {f : ι → cardinal} {a : cardinal} :
    a ≤ min I f ↔ ∀ (i : ι), a ≤ f i :=
  sorry

protected theorem wf : well_founded Less := sorry

protected instance has_wf : has_well_founded cardinal := has_well_founded.mk Less cardinal.wf

protected instance wo : is_well_order cardinal Less := is_well_order.mk cardinal.wf

/-- The successor cardinal - the smallest cardinal greater than
  `c`. This is not the same as `c + 1` except in the case of finite `c`. -/
def succ (c : cardinal) : cardinal := min sorry subtype.val

theorem lt_succ_self (c : cardinal) : c < succ c := sorry

theorem succ_le {a : cardinal} {b : cardinal} : succ a ≤ b ↔ a < b :=
  { mp := lt_of_lt_of_le (lt_succ_self a),
    mpr := fun (h : a < b) => min_le subtype.val { val := b, property := h } }

theorem lt_succ {a : cardinal} {b : cardinal} : a < succ b ↔ a ≤ b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a < succ b ↔ a ≤ b)) (Eq.symm (propext not_le))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (¬succ b ≤ a ↔ a ≤ b)) (propext succ_le)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (¬b < a ↔ a ≤ b)) (propext not_lt))) (iff.refl (a ≤ b))))

theorem add_one_le_succ (c : cardinal) : c + 1 ≤ succ c := sorry

theorem succ_ne_zero (c : cardinal) : succ c ≠ 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (succ c ≠ 0)) (Eq.symm (propext pos_iff_ne_zero))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (0 < succ c)) (propext lt_succ))) (zero_le c))

/-- The indexed sum of cardinals is the cardinality of the
  indexed disjoint union, i.e. sigma type. -/
def sum {ι : Type u_1} (f : ι → cardinal) : cardinal := mk (sigma fun (i : ι) => quotient.out (f i))

theorem le_sum {ι : Type u_1} (f : ι → cardinal) (i : ι) : f i ≤ sum f := sorry

@[simp] theorem sum_mk {ι : Type u_1} (f : ι → Type u_2) :
    (sum fun (i : ι) => mk (f i)) = mk (sigma fun (i : ι) => f i) :=
  quot.sound
    (Nonempty.intro
      (equiv.sigma_congr_right
        fun (i : ι) => Classical.choice (quotient.exact (quot.out_eq (mk (f i))))))

theorem sum_const (ι : Type u) (a : cardinal) : (sum fun (_x : ι) => a) = mk ι * a := sorry

theorem sum_le_sum {ι : Type u_1} (f : ι → cardinal) (g : ι → cardinal) (H : ∀ (i : ι), f i ≤ g i) :
    sum f ≤ sum g :=
  sorry

/-- The indexed supremum of cardinals is the smallest cardinal above
  everything in the family. -/
def sup {ι : Type u_1} (f : ι → cardinal) : cardinal :=
  min sorry fun (a : Subtype fun (c : cardinal) => ∀ (i : ι), f i ≤ c) => subtype.val a

theorem le_sup {ι : Type u_1} (f : ι → cardinal) (i : ι) : f i ≤ sup f := sorry

theorem sup_le {ι : Type u_1} {f : ι → cardinal} {a : cardinal} : sup f ≤ a ↔ ∀ (i : ι), f i ≤ a :=
  { mp := fun (h : sup f ≤ a) (i : ι) => le_trans (le_sup f i) h,
    mpr :=
      fun (h : ∀ (i : ι), f i ≤ a) => id (id (min_le subtype.val { val := a, property := h })) }

theorem sup_le_sup {ι : Type u_1} (f : ι → cardinal) (g : ι → cardinal) (H : ∀ (i : ι), f i ≤ g i) :
    sup f ≤ sup g :=
  iff.mpr sup_le fun (i : ι) => le_trans (H i) (le_sup g i)

theorem sup_le_sum {ι : Type u_1} (f : ι → cardinal) : sup f ≤ sum f :=
  iff.mpr sup_le (le_sum fun (i : ι) => f i)

theorem sum_le_sup {ι : Type u} (f : ι → cardinal) : sum f ≤ mk ι * sup f :=
  eq.mpr (id (Eq._oldrec (Eq.refl (sum f ≤ mk ι * sup f)) (Eq.symm (sum_const ι (sup f)))))
    (sum_le_sum f (fun (_x : ι) => sup f) (le_sup fun (i : ι) => f i))

theorem sup_eq_zero {ι : Type u_1} {f : ι → cardinal} (h : ι → False) : sup f = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (sup f = 0)) (Eq.symm (propext nonpos_iff_eq_zero))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (sup f ≤ 0)) (propext sup_le)))
      fun (x : ι) => False._oldrec (h x))

/-- The indexed product of cardinals is the cardinality of the Pi type
  (dependent product). -/
def prod {ι : Type u} (f : ι → cardinal) : cardinal := mk ((i : ι) → quotient.out (f i))

@[simp] theorem prod_mk {ι : Type u_1} (f : ι → Type u_2) :
    (prod fun (i : ι) => mk (f i)) = mk ((i : ι) → f i) :=
  quot.sound
    (Nonempty.intro
      (equiv.Pi_congr_right fun (i : ι) => Classical.choice (quotient.exact (mk_out (mk (f i))))))

theorem prod_const (ι : Type u) (a : cardinal) : (prod fun (_x : ι) => a) = a ^ mk ι := sorry

theorem prod_le_prod {ι : Type u_1} (f : ι → cardinal) (g : ι → cardinal)
    (H : ∀ (i : ι), f i ≤ g i) : prod f ≤ prod g :=
  sorry

theorem prod_ne_zero {ι : Type u_1} (f : ι → cardinal) : prod f ≠ 0 ↔ ∀ (i : ι), f i ≠ 0 := sorry

theorem prod_eq_zero {ι : Type u_1} (f : ι → cardinal) : prod f = 0 ↔ ∃ (i : ι), f i = 0 := sorry

/-- The universe lift operation on cardinals. You can specify the universes explicitly with
  `lift.{u v} : cardinal.{u} → cardinal.{max u v}` -/
def lift (c : cardinal) : cardinal :=
  quotient.lift_on c (fun (α : Type u) => quotient.mk (ulift α)) sorry

theorem lift_mk (α : Type u) : lift (mk α) = mk (ulift α) := rfl

theorem lift_umax : lift = lift := sorry

theorem lift_id' (a : cardinal) : lift a = a :=
  quot.induction_on a fun (α : Type (max u_1 u_2)) => quot.sound (Nonempty.intro equiv.ulift)

@[simp] theorem lift_id (a : cardinal) : lift a = a := lift_id'

@[simp] theorem lift_lift (a : cardinal) : lift (lift a) = lift a :=
  quot.induction_on a
    fun (α : Type u) =>
      quotient.sound
        (Nonempty.intro
          (equiv.trans equiv.ulift (equiv.trans equiv.ulift (equiv.symm equiv.ulift))))

theorem lift_mk_le {α : Type u} {β : Type v} : lift (mk α) ≤ lift (mk β) ↔ Nonempty (α ↪ β) := sorry

theorem lift_mk_eq {α : Type u} {β : Type v} : lift (mk α) = lift (mk β) ↔ Nonempty (α ≃ β) := sorry

@[simp] theorem lift_le {a : cardinal} {b : cardinal} : lift a ≤ lift b ↔ a ≤ b := sorry

@[simp] theorem lift_inj {a : cardinal} {b : cardinal} : lift a = lift b ↔ a = b := sorry

@[simp] theorem lift_lt {a : cardinal} {b : cardinal} : lift a < lift b ↔ a < b := sorry

@[simp] theorem lift_zero : lift 0 = 0 :=
  quotient.sound (Nonempty.intro (equiv.trans equiv.ulift equiv.pempty_equiv_pempty))

@[simp] theorem lift_one : lift 1 = 1 :=
  quotient.sound (Nonempty.intro (equiv.trans equiv.ulift equiv.punit_equiv_punit))

@[simp] theorem lift_add (a : cardinal) (b : cardinal) : lift (a + b) = lift a + lift b :=
  quotient.induction_on₂ a b
    fun (α β : Type u_1) =>
      quotient.sound
        (Nonempty.intro
          (equiv.trans equiv.ulift (equiv.symm (equiv.sum_congr equiv.ulift equiv.ulift))))

@[simp] theorem lift_mul (a : cardinal) (b : cardinal) : lift (a * b) = lift a * lift b :=
  quotient.induction_on₂ a b
    fun (α β : Type u_1) =>
      quotient.sound
        (Nonempty.intro
          (equiv.trans equiv.ulift (equiv.symm (equiv.prod_congr equiv.ulift equiv.ulift))))

@[simp] theorem lift_power (a : cardinal) (b : cardinal) : lift (a ^ b) = lift a ^ lift b :=
  quotient.induction_on₂ a b
    fun (α β : Type u_1) =>
      quotient.sound
        (Nonempty.intro
          (equiv.trans equiv.ulift (equiv.symm (equiv.arrow_congr equiv.ulift equiv.ulift))))

@[simp] theorem lift_two_power (a : cardinal) : lift (bit0 1 ^ a) = bit0 1 ^ lift a := sorry

@[simp] theorem lift_min {ι : Type u_1} {I : Nonempty ι} (f : ι → cardinal) :
    lift (min I f) = min I (lift ∘ f) :=
  sorry

theorem lift_down {a : cardinal} {b : cardinal} : b ≤ lift a → ∃ (a' : cardinal), lift a' = b :=
  sorry

theorem le_lift_iff {a : cardinal} {b : cardinal} :
    b ≤ lift a ↔ ∃ (a' : cardinal), lift a' = b ∧ a' ≤ a :=
  sorry

theorem lt_lift_iff {a : cardinal} {b : cardinal} :
    b < lift a ↔ ∃ (a' : cardinal), lift a' = b ∧ a' < a :=
  sorry

@[simp] theorem lift_succ (a : cardinal) : lift (succ a) = succ (lift a) := sorry

@[simp] theorem lift_max {a : cardinal} {b : cardinal} : lift a = lift b ↔ lift a = lift b := sorry

theorem mk_prod {α : Type u} {β : Type v} : mk (α × β) = lift (mk α) * lift (mk β) :=
  quotient.sound
    (Nonempty.intro (equiv.prod_congr (equiv.symm equiv.ulift) (equiv.symm equiv.ulift)))

theorem sum_const_eq_lift_mul (ι : Type u) (a : cardinal) :
    (sum fun (_x : ι) => a) = lift (mk ι) * lift a :=
  sorry

/-- `ω` is the smallest infinite cardinal, also known as ℵ₀. -/
def omega : cardinal := lift (mk ℕ)

theorem mk_nat : mk ℕ = omega := Eq.symm (lift_id (mk ℕ))

theorem omega_ne_zero : omega ≠ 0 := iff.mpr ne_zero_iff_nonempty (Nonempty.intro (ulift.up 0))

theorem omega_pos : 0 < omega := iff.mpr pos_iff_ne_zero omega_ne_zero

@[simp] theorem lift_omega : lift omega = omega := lift_lift (mk ℕ)

/- properties about the cast from nat -/

@[simp] theorem mk_fin (n : ℕ) : mk (fin n) = ↑n := sorry

@[simp] theorem lift_nat_cast (n : ℕ) : lift ↑n = ↑n := sorry

theorem lift_eq_nat_iff {a : cardinal} {n : ℕ} : lift a = ↑n ↔ a = ↑n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (lift a = ↑n ↔ a = ↑n)) (Eq.symm (lift_nat_cast n))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (lift a = lift ↑n ↔ a = ↑n)) (propext lift_inj)))
      (iff.refl (a = ↑n)))

theorem nat_eq_lift_eq_iff {n : ℕ} {a : cardinal} : ↑n = lift a ↔ ↑n = a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑n = lift a ↔ ↑n = a)) (Eq.symm (lift_nat_cast n))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (lift ↑n = lift a ↔ ↑n = a)) (propext lift_inj)))
      (iff.refl (↑n = a)))

theorem lift_mk_fin (n : ℕ) : lift (mk (fin n)) = ↑n := sorry

theorem fintype_card (α : Type u) [fintype α] : mk α = ↑(fintype.card α) := sorry

theorem card_le_of_finset {α : Type u_1} (s : finset α) : ↑(finset.card s) ≤ mk α := sorry

@[simp] theorem nat_cast_pow {m : ℕ} {n : ℕ} : ↑(m ^ n) = ↑m ^ ↑n := sorry

@[simp] theorem nat_cast_le {m : ℕ} {n : ℕ} : ↑m ≤ ↑n ↔ m ≤ n := sorry

@[simp] theorem nat_cast_lt {m : ℕ} {n : ℕ} : ↑m < ↑n ↔ m < n := sorry

@[simp] theorem nat_cast_inj {m : ℕ} {n : ℕ} : ↑m = ↑n ↔ m = n := sorry

@[simp] theorem nat_succ (n : ℕ) : ↑(Nat.succ n) = succ ↑n :=
  le_antisymm (add_one_le_succ (nat.cast n))
    (iff.mpr succ_le (iff.mpr nat_cast_lt (nat.lt_succ_self n)))

@[simp] theorem succ_zero : succ 0 = 1 := sorry

theorem card_le_of {α : Type u} {n : ℕ} (H : ∀ (s : finset α), finset.card s ≤ n) : mk α ≤ ↑n :=
  sorry

theorem cantor' (a : cardinal) {b : cardinal} (hb : 1 < b) : a < b ^ a := sorry

theorem one_le_iff_pos {c : cardinal} : 1 ≤ c ↔ 0 < c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (1 ≤ c ↔ 0 < c)) (Eq.symm succ_zero)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (succ 0 ≤ c ↔ 0 < c)) (propext succ_le))) (iff.refl (0 < c)))

theorem one_le_iff_ne_zero {c : cardinal} : 1 ≤ c ↔ c ≠ 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (1 ≤ c ↔ c ≠ 0)) (propext one_le_iff_pos)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (0 < c ↔ c ≠ 0)) (propext pos_iff_ne_zero)))
      (iff.refl (c ≠ 0)))

theorem nat_lt_omega (n : ℕ) : ↑n < omega := sorry

@[simp] theorem one_lt_omega : 1 < omega := sorry

theorem lt_omega {c : cardinal} : c < omega ↔ ∃ (n : ℕ), c = ↑n := sorry

theorem omega_le {c : cardinal} : omega ≤ c ↔ ∀ (n : ℕ), ↑n ≤ c := sorry

theorem lt_omega_iff_fintype {α : Type u} : mk α < omega ↔ Nonempty (fintype α) := sorry

theorem lt_omega_iff_finite {α : Type u_1} {S : set α} : mk ↥S < omega ↔ set.finite S :=
  lt_omega_iff_fintype

protected instance can_lift_cardinal_nat : can_lift cardinal ℕ :=
  can_lift.mk coe (fun (x : cardinal) => x < omega) sorry

theorem add_lt_omega {a : cardinal} {b : cardinal} (ha : a < omega) (hb : b < omega) :
    a + b < omega :=
  sorry

theorem add_lt_omega_iff {a : cardinal} {b : cardinal} : a + b < omega ↔ a < omega ∧ b < omega :=
  sorry

theorem mul_lt_omega {a : cardinal} {b : cardinal} (ha : a < omega) (hb : b < omega) :
    a * b < omega :=
  sorry

theorem mul_lt_omega_iff {a : cardinal} {b : cardinal} :
    a * b < omega ↔ a = 0 ∨ b = 0 ∨ a < omega ∧ b < omega :=
  sorry

theorem mul_lt_omega_iff_of_ne_zero {a : cardinal} {b : cardinal} (ha : a ≠ 0) (hb : b ≠ 0) :
    a * b < omega ↔ a < omega ∧ b < omega :=
  sorry

theorem power_lt_omega {a : cardinal} {b : cardinal} (ha : a < omega) (hb : b < omega) :
    a ^ b < omega :=
  sorry

theorem eq_one_iff_subsingleton_and_nonempty {α : Type u_1} :
    mk α = 1 ↔ subsingleton α ∧ Nonempty α :=
  sorry

theorem infinite_iff {α : Type u} : infinite α ↔ omega ≤ mk α := sorry

theorem countable_iff {α : Type u} (s : set α) : set.countable s ↔ mk ↥s ≤ omega := sorry

theorem denumerable_iff {α : Type u} : Nonempty (denumerable α) ↔ mk α = omega := sorry

theorem mk_int : mk ℤ = omega := iff.mp denumerable_iff (Nonempty.intro denumerable.int)

theorem mk_pnat : mk ℕ+ = omega := iff.mp denumerable_iff (Nonempty.intro denumerable.pnat)

theorem two_le_iff {α : Type u} : bit0 1 ≤ mk α ↔ ∃ (x : α), ∃ (y : α), x ≠ y := sorry

theorem two_le_iff' {α : Type u} (x : α) : bit0 1 ≤ mk α ↔ ∃ (y : α), x ≠ y := sorry

/-- König's theorem -/
theorem sum_lt_prod {ι : Type u_1} (f : ι → cardinal) (g : ι → cardinal)
    (H : ∀ (i : ι), f i < g i) : sum f < prod g :=
  sorry

@[simp] theorem mk_empty : mk empty = 0 := fintype_card empty

@[simp] theorem mk_pempty : mk pempty = 0 := fintype_card pempty

@[simp] theorem mk_plift_of_false {p : Prop} (h : ¬p) : mk (plift p) = 0 :=
  quotient.sound (Nonempty.intro (equiv.trans equiv.plift (equiv.equiv_pempty h)))

theorem mk_unit : mk Unit = 1 := Eq.trans (fintype_card Unit) nat.cast_one

@[simp] theorem mk_punit : mk PUnit = 1 := Eq.trans (fintype_card PUnit) nat.cast_one

@[simp] theorem mk_singleton {α : Type u} (x : α) : mk ↥(singleton x) = 1 :=
  quotient.sound (Nonempty.intro (equiv.set.singleton x))

@[simp] theorem mk_plift_of_true {p : Prop} (h : p) : mk (plift p) = 1 :=
  quotient.sound (Nonempty.intro (equiv.trans equiv.plift (equiv.prop_equiv_punit h)))

@[simp] theorem mk_bool : mk Bool = bit0 1 :=
  quotient.sound (Nonempty.intro equiv.bool_equiv_punit_sum_punit)

@[simp] theorem mk_Prop : mk Prop = bit0 1 :=
  Eq.trans (quotient.sound (Nonempty.intro equiv.Prop_equiv_bool)) mk_bool

@[simp] theorem mk_set {α : Type u} : mk (set α) = bit0 1 ^ mk α := sorry

@[simp] theorem mk_option {α : Type u} : mk (Option α) = mk α + 1 :=
  quotient.sound (Nonempty.intro (equiv.option_equiv_sum_punit α))

theorem mk_list_eq_sum_pow (α : Type u) : mk (List α) = sum fun (n : ℕ) => mk α ^ ↑n := sorry

theorem mk_quot_le {α : Type u} {r : α → α → Prop} : mk (Quot r) ≤ mk α :=
  mk_le_of_surjective quot.exists_rep

theorem mk_quotient_le {α : Type u} {s : setoid α} : mk (quotient s) ≤ mk α := mk_quot_le

theorem mk_subtype_le {α : Type u} (p : α → Prop) : mk (Subtype p) ≤ mk α :=
  Nonempty.intro (function.embedding.subtype p)

theorem mk_subtype_le_of_subset {α : Type u} {p : α → Prop} {q : α → Prop}
    (h : ∀ {x : α}, p x → q x) : mk (Subtype p) ≤ mk (Subtype q) :=
  Nonempty.intro (function.embedding.subtype_map (function.embedding.refl α) h)

@[simp] theorem mk_emptyc (α : Type u) : mk ↥∅ = 0 :=
  quotient.sound (Nonempty.intro (equiv.set.pempty α))

theorem mk_emptyc_iff {α : Type u} {s : set α} : mk ↥s = 0 ↔ s = ∅ := sorry

theorem mk_univ {α : Type u} : mk ↥set.univ = mk α :=
  quotient.sound (Nonempty.intro (equiv.set.univ α))

theorem mk_image_le {α : Type u} {β : Type u} {f : α → β} {s : set α} : mk ↥(f '' s) ≤ mk ↥s :=
  mk_le_of_surjective set.surjective_onto_image

theorem mk_image_le_lift {α : Type u} {β : Type v} {f : α → β} {s : set α} :
    lift (mk ↥(f '' s)) ≤ lift (mk ↥s) :=
  iff.mpr lift_mk_le
    (Nonempty.intro
      (function.embedding.of_surjective (set.image_factorization f s) set.surjective_onto_image))

theorem mk_range_le {α : Type u} {β : Type u} {f : α → β} : mk ↥(set.range f) ≤ mk α :=
  mk_le_of_surjective set.surjective_onto_range

theorem mk_range_eq {α : Type u} {β : Type u} (f : α → β) (h : function.injective f) :
    mk ↥(set.range f) = mk α :=
  quotient.sound (Nonempty.intro (equiv.symm (equiv.set.range f h)))

theorem mk_range_eq_of_injective {α : Type u} {β : Type v} {f : α → β} (hf : function.injective f) :
    lift (mk ↥(set.range f)) = lift (mk α) :=
  sorry

theorem mk_range_eq_lift {α : Type u} {β : Type v} {f : α → β} (hf : function.injective f) :
    lift (mk ↥(set.range f)) = lift (mk α) :=
  iff.mpr lift_mk_eq (Nonempty.intro (equiv.symm (equiv.set.range f hf)))

theorem mk_image_eq {α : Type u} {β : Type u} {f : α → β} {s : set α} (hf : function.injective f) :
    mk ↥(f '' s) = mk ↥s :=
  quotient.sound (Nonempty.intro (equiv.symm (equiv.set.image f s hf)))

theorem mk_Union_le_sum_mk {α : Type u} {ι : Type u} {f : ι → set α} :
    mk ↥(set.Union fun (i : ι) => f i) ≤ sum fun (i : ι) => mk ↥(f i) :=
  trans_rel_left LessEq (mk_le_of_surjective (set.sigma_to_Union_surjective f))
    (Eq.symm (sum_mk fun (i : ι) => ↥(f i)))

theorem mk_Union_eq_sum_mk {α : Type u} {ι : Type u} {f : ι → set α}
    (h : ∀ (i j : ι), i ≠ j → disjoint (f i) (f j)) :
    mk ↥(set.Union fun (i : ι) => f i) = sum fun (i : ι) => mk ↥(f i) :=
  Eq.trans (quot.sound (Nonempty.intro (set.Union_eq_sigma_of_disjoint h)))
    (Eq.symm (sum_mk fun (i : ι) => ↥(f i)))

theorem mk_Union_le {α : Type u} {ι : Type u} (f : ι → set α) :
    mk ↥(set.Union fun (i : ι) => f i) ≤ mk ι * sup fun (i : ι) => mk ↥(f i) :=
  le_trans mk_Union_le_sum_mk (sum_le_sup fun (i : ι) => mk ↥(f i))

theorem mk_sUnion_le {α : Type u} (A : set (set α)) :
    mk ↥(⋃₀A) ≤ mk ↥A * sup fun (s : ↥A) => mk ↥s :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (mk ↥(⋃₀A) ≤ mk ↥A * sup fun (s : ↥A) => mk ↥s)) set.sUnion_eq_Union))
    (mk_Union_le fun (i : ↥A) => ↑i)

theorem mk_bUnion_le {ι : Type u} {α : Type u} (A : ι → set α) (s : set ι) :
    mk ↥(set.Union fun (x : ι) => set.Union fun (H : x ∈ s) => A x) ≤
        mk ↥s * sup fun (x : ↥s) => mk ↥(A (subtype.val x)) :=
  sorry

@[simp] theorem finset_card {α : Type u} {s : finset α} : ↑(finset.card s) = mk ↥↑s := sorry

theorem finset_card_lt_omega {α : Type u} (s : finset α) : mk ↥↑s < omega :=
  eq.mpr (id (Eq._oldrec (Eq.refl (mk ↥↑s < omega)) (propext lt_omega_iff_fintype)))
    (Nonempty.intro (finset.subtype.fintype s))

theorem mk_union_add_mk_inter {α : Type u} {S : set α} {T : set α} :
    mk ↥(S ∪ T) + mk ↥(S ∩ T) = mk ↥S + mk ↥T :=
  quot.sound (Nonempty.intro (equiv.set.union_sum_inter S T))

/-- The cardinality of a union is at most the sum of the cardinalities
of the two sets. -/
theorem mk_union_le {α : Type u} (S : set α) (T : set α) : mk ↥(S ∪ T) ≤ mk ↥S + mk ↥T :=
  mk_union_add_mk_inter ▸ self_le_add_right (mk ↥(S ∪ T)) (mk ↥(S ∩ T))

theorem mk_union_of_disjoint {α : Type u} {S : set α} {T : set α} (H : disjoint S T) :
    mk ↥(S ∪ T) = mk ↥S + mk ↥T :=
  quot.sound (Nonempty.intro (equiv.set.union H))

theorem mk_sum_compl {α : Type u_1} (s : set α) : mk ↥s + mk ↥(sᶜ) = mk α :=
  quotient.sound (Nonempty.intro (equiv.set.sum_compl s))

theorem mk_le_mk_of_subset {α : Type u_1} {s : set α} {t : set α} (h : s ⊆ t) : mk ↥s ≤ mk ↥t :=
  Nonempty.intro (set.embedding_of_subset s t h)

theorem mk_subtype_mono {α : Type u} {p : α → Prop} {q : α → Prop} (h : ∀ (x : α), p x → q x) :
    mk (Subtype fun (x : α) => p x) ≤ mk (Subtype fun (x : α) => q x) :=
  Nonempty.intro (set.embedding_of_subset (fun (x : α) => p x) (fun (x : α) => q x) h)

theorem mk_set_le {α : Type u} (s : set α) : mk ↥s ≤ mk α := mk_subtype_le s

theorem mk_image_eq_lift {α : Type u} {β : Type v} (f : α → β) (s : set α)
    (h : function.injective f) : lift (mk ↥(f '' s)) = lift (mk ↥s) :=
  iff.mpr lift_mk_eq (Nonempty.intro (equiv.symm (equiv.set.image f s h)))

theorem mk_image_eq_of_inj_on_lift {α : Type u} {β : Type v} (f : α → β) (s : set α)
    (h : set.inj_on f s) : lift (mk ↥(f '' s)) = lift (mk ↥s) :=
  iff.mpr lift_mk_eq (Nonempty.intro (equiv.symm (equiv.set.image_of_inj_on f s h)))

theorem mk_image_eq_of_inj_on {α : Type u} {β : Type u} (f : α → β) (s : set α)
    (h : set.inj_on f s) : mk ↥(f '' s) = mk ↥s :=
  quotient.sound (Nonempty.intro (equiv.symm (equiv.set.image_of_inj_on f s h)))

theorem mk_subtype_of_equiv {α : Type u} {β : Type u} (p : β → Prop) (e : α ≃ β) :
    mk (Subtype fun (a : α) => p (coe_fn e a)) = mk (Subtype fun (b : β) => p b) :=
  quotient.sound (Nonempty.intro (equiv.subtype_equiv_of_subtype e))

theorem mk_sep {α : Type u} (s : set α) (t : α → Prop) :
    mk ↥(has_sep.sep (fun (x : α) => t x) s) = mk ↥(set_of fun (x : ↥s) => t (subtype.val x)) :=
  quotient.sound (Nonempty.intro (equiv.set.sep s t))

theorem mk_preimage_of_injective_lift {α : Type u} {β : Type v} (f : α → β) (s : set β)
    (h : function.injective f) : lift (mk ↥(f ⁻¹' s)) ≤ lift (mk ↥s) :=
  sorry

theorem mk_preimage_of_subset_range_lift {α : Type u} {β : Type v} (f : α → β) (s : set β)
    (h : s ⊆ set.range f) : lift (mk ↥s) ≤ lift (mk ↥(f ⁻¹' s)) :=
  sorry

theorem mk_preimage_of_injective_of_subset_range_lift {α : Type u} {β : Type v} (f : α → β)
    (s : set β) (h : function.injective f) (h2 : s ⊆ set.range f) :
    lift (mk ↥(f ⁻¹' s)) = lift (mk ↥s) :=
  le_antisymm (mk_preimage_of_injective_lift f s h) (mk_preimage_of_subset_range_lift f s h2)

theorem mk_preimage_of_injective {α : Type u} {β : Type u} (f : α → β) (s : set β)
    (h : function.injective f) : mk ↥(f ⁻¹' s) ≤ mk ↥s :=
  sorry

theorem mk_preimage_of_subset_range {α : Type u} {β : Type u} (f : α → β) (s : set β)
    (h : s ⊆ set.range f) : mk ↥s ≤ mk ↥(f ⁻¹' s) :=
  sorry

theorem mk_preimage_of_injective_of_subset_range {α : Type u} {β : Type u} (f : α → β) (s : set β)
    (h : function.injective f) (h2 : s ⊆ set.range f) : mk ↥(f ⁻¹' s) = mk ↥s :=
  sorry

theorem mk_subset_ge_of_subset_image_lift {α : Type u} {β : Type v} (f : α → β) {s : set α}
    {t : set β} (h : t ⊆ f '' s) :
    lift (mk ↥t) ≤ lift (mk ↥(has_sep.sep (fun (x : α) => f x ∈ t) s)) :=
  sorry

theorem mk_subset_ge_of_subset_image {α : Type u} {β : Type u} (f : α → β) {s : set α} {t : set β}
    (h : t ⊆ f '' s) : mk ↥t ≤ mk ↥(has_sep.sep (fun (x : α) => f x ∈ t) s) :=
  sorry

theorem le_mk_iff_exists_subset {c : cardinal} {α : Type u} {s : set α} :
    c ≤ mk ↥s ↔ ∃ (p : set α), p ⊆ s ∧ mk ↥p = c :=
  sorry

/-- The function α^{<β}, defined to be sup_{γ < β} α^γ.
  We index over {s : set β.out // mk s < β } instead of {γ // γ < β}, because the latter lives in a
  higher universe -/
def powerlt (α : cardinal) (β : cardinal) : cardinal :=
  sup fun (s : Subtype fun (s : set (quotient.out β)) => mk ↥s < β) => α ^ mk ↥s

infixl:80 " ^< " => Mathlib.cardinal.powerlt

theorem powerlt_aux {c : cardinal} {c' : cardinal} (h : c < c') :
    ∃ (s : Subtype fun (s : set (quotient.out c')) => mk ↥s < c'), mk ↥s = c :=
  sorry

theorem le_powerlt {c₁ : cardinal} {c₂ : cardinal} {c₃ : cardinal} (h : c₂ < c₃) :
    c₁ ^ c₂ ≤ c₁ ^< c₃ :=
  sorry

theorem powerlt_le {c₁ : cardinal} {c₂ : cardinal} {c₃ : cardinal} :
    c₁ ^< c₂ ≤ c₃ ↔ ∀ (c₄ : cardinal), c₄ < c₂ → c₁ ^ c₄ ≤ c₃ :=
  sorry

theorem powerlt_le_powerlt_left {a : cardinal} {b : cardinal} {c : cardinal} (h : b ≤ c) :
    a ^< b ≤ a ^< c :=
  sorry

theorem powerlt_succ {c₁ : cardinal} {c₂ : cardinal} (h : c₁ ≠ 0) : c₁ ^< succ c₂ = c₁ ^ c₂ := sorry

theorem powerlt_max {c₁ : cardinal} {c₂ : cardinal} {c₃ : cardinal} :
    c₁ ^< max c₂ c₃ = max (c₁ ^< c₂) (c₁ ^< c₃) :=
  sorry

theorem zero_powerlt {a : cardinal} (h : a ≠ 0) : 0 ^< a = 1 := sorry

theorem powerlt_zero {a : cardinal} : a ^< 0 = 0 := sorry

end Mathlib