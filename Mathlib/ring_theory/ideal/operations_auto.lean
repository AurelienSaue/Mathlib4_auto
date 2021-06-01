/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.nat.choose.sum
import Mathlib.data.equiv.ring
import Mathlib.algebra.algebra.operations
import Mathlib.ring_theory.ideal.basic
import Mathlib.algebra.algebra.tower
import Mathlib.PostPort

universes u v w x u_1 u_2 u_3 u_4 

namespace Mathlib

/-!
# More operations on modules and ideals
-/

namespace submodule


protected instance has_scalar' {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M]
    [module R M] : has_scalar (ideal R) (submodule R M) :=
  has_scalar.mk
    fun (I : ideal R) (N : submodule R M) =>
      supr fun (r : ↥I) => map (subtype.val r • linear_map.id) N

/-- `N.annihilator` is the ideal of all elements `r : R` such that `r • N = 0`. -/
def annihilator {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [module R M]
    (N : submodule R M) : ideal R :=
  linear_map.ker (linear_map.lsmul R ↥N)

/-- `N.colon P` is the ideal of all elements `r : R` such that `r • P ⊆ N`. -/
def colon {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [module R M]
    (N : submodule R M) (P : submodule R M) : ideal R :=
  annihilator (map (mkq N) P)

theorem mem_annihilator {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [module R M]
    {N : submodule R M} {r : R} : r ∈ annihilator N ↔ ∀ (n : M), n ∈ N → r • n = 0 :=
  sorry

theorem mem_annihilator' {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [module R M]
    {N : submodule R M} {r : R} : r ∈ annihilator N ↔ N ≤ comap (r • linear_map.id) ⊥ :=
  iff.trans mem_annihilator
    { mp :=
        fun (H : ∀ (n : M), n ∈ N → r • n = 0) (n : M) (hn : n ∈ N) => iff.mpr (mem_bot R) (H n hn),
      mpr :=
        fun (H : N ≤ comap (r • linear_map.id) ⊥) (n : M) (hn : n ∈ N) =>
          iff.mp (mem_bot R) (H hn) }

theorem annihilator_bot {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [module R M] :
    annihilator ⊥ = ⊤ :=
  iff.mpr (ideal.eq_top_iff_one (annihilator ⊥)) (iff.mpr mem_annihilator' bot_le)

theorem annihilator_eq_top_iff {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M]
    [module R M] {N : submodule R M} : annihilator N = ⊤ ↔ N = ⊥ :=
  sorry

theorem annihilator_mono {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [module R M]
    {N : submodule R M} {P : submodule R M} (h : N ≤ P) : annihilator P ≤ annihilator N :=
  fun (r : R) (hrp : r ∈ annihilator P) =>
    iff.mpr mem_annihilator fun (n : M) (hn : n ∈ N) => iff.mp mem_annihilator hrp n (h hn)

theorem annihilator_supr {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [module R M]
    (ι : Sort w) (f : ι → submodule R M) :
    annihilator (supr fun (i : ι) => f i) = infi fun (i : ι) => annihilator (f i) :=
  sorry

theorem mem_colon {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [module R M]
    {N : submodule R M} {P : submodule R M} {r : R} :
    r ∈ colon N P ↔ ∀ (p : M), p ∈ P → r • p ∈ N :=
  sorry

theorem mem_colon' {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [module R M]
    {N : submodule R M} {P : submodule R M} {r : R} :
    r ∈ colon N P ↔ P ≤ comap (r • linear_map.id) N :=
  mem_colon

theorem colon_mono {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [module R M]
    {N₁ : submodule R M} {N₂ : submodule R M} {P₁ : submodule R M} {P₂ : submodule R M}
    (hn : N₁ ≤ N₂) (hp : P₁ ≤ P₂) : colon N₁ P₂ ≤ colon N₂ P₁ :=
  fun (r : R) (hrnp : r ∈ colon N₁ P₂) =>
    iff.mpr mem_colon fun (p₁ : M) (hp₁ : p₁ ∈ P₁) => hn (iff.mp mem_colon hrnp p₁ (hp hp₁))

theorem infi_colon_supr {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [module R M]
    (ι₁ : Sort w) (f : ι₁ → submodule R M) (ι₂ : Sort x) (g : ι₂ → submodule R M) :
    colon (infi fun (i : ι₁) => f i) (supr fun (j : ι₂) => g j) =
        infi fun (i : ι₁) => infi fun (j : ι₂) => colon (f i) (g j) :=
  sorry

theorem smul_mem_smul {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [module R M]
    {I : ideal R} {N : submodule R M} {r : R} {n : M} (hr : r ∈ I) (hn : n ∈ N) : r • n ∈ I • N :=
  le_supr (fun (r : ↥I) => map (subtype.val r • linear_map.id) N) { val := r, property := hr }
    (r • n) (Exists.intro n { left := hn, right := rfl })

theorem smul_le {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [module R M]
    {I : ideal R} {N : submodule R M} {P : submodule R M} :
    I • N ≤ P ↔ ∀ (r : R), r ∈ I → ∀ (n : M), n ∈ N → r • n ∈ P :=
  sorry

theorem smul_induction_on {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [module R M]
    {I : ideal R} {N : submodule R M} {p : M → Prop} {x : M} (H : x ∈ I • N)
    (Hb : ∀ (r : R), r ∈ I → ∀ (n : M), n ∈ N → p (r • n)) (H0 : p 0)
    (H1 : ∀ (x y : M), p x → p y → p (x + y)) (H2 : ∀ (c : R) (n : M), p n → p (c • n)) : p x :=
  iff.mpr smul_le Hb x H

theorem mem_smul_span_singleton {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M]
    [module R M] {I : ideal R} {m : M} {x : M} :
    x ∈ I • span R (singleton m) ↔ ∃ (y : R), ∃ (H : y ∈ I), y • m = x :=
  sorry

theorem smul_le_right {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [module R M]
    {I : ideal R} {N : submodule R M} : I • N ≤ N :=
  iff.mpr smul_le fun (r : R) (hr : r ∈ I) (n : M) => smul_mem N r

theorem smul_mono {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [module R M]
    {I : ideal R} {J : ideal R} {N : submodule R M} {P : submodule R M} (hij : I ≤ J)
    (hnp : N ≤ P) : I • N ≤ J • P :=
  iff.mpr smul_le fun (r : R) (hr : r ∈ I) (n : M) (hn : n ∈ N) => smul_mem_smul (hij hr) (hnp hn)

theorem smul_mono_left {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [module R M]
    {I : ideal R} {J : ideal R} {N : submodule R M} (h : I ≤ J) : I • N ≤ J • N :=
  smul_mono h (le_refl N)

theorem smul_mono_right {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [module R M]
    {I : ideal R} {N : submodule R M} {P : submodule R M} (h : N ≤ P) : I • N ≤ I • P :=
  smul_mono (le_refl I) h

@[simp] theorem smul_bot {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [module R M]
    (I : ideal R) : I • ⊥ = ⊥ :=
  sorry

@[simp] theorem bot_smul {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [module R M]
    (N : submodule R M) : ⊥ • N = ⊥ :=
  sorry

@[simp] theorem top_smul {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [module R M]
    (N : submodule R M) : ⊤ • N = N :=
  le_antisymm smul_le_right fun (r : M) (hri : r ∈ N) => one_smul R r ▸ smul_mem_smul mem_top hri

theorem smul_sup {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [module R M]
    (I : ideal R) (N : submodule R M) (P : submodule R M) : I • (N ⊔ P) = I • N ⊔ I • P :=
  sorry

theorem sup_smul {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [module R M]
    (I : ideal R) (J : ideal R) (N : submodule R M) : (I ⊔ J) • N = I • N ⊔ J • N :=
  sorry

protected theorem smul_assoc {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [module R M]
    (I : ideal R) (J : ideal R) (N : submodule R M) : (I • J) • N = I • J • N :=
  sorry

theorem span_smul_span {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [module R M]
    (S : set R) (T : set M) :
    ideal.span S • span R T =
        span R
          (set.Union
            fun (s : R) =>
              set.Union
                fun (H : s ∈ S) =>
                  set.Union fun (t : M) => set.Union fun (H : t ∈ T) => singleton (s • t)) :=
  sorry

theorem map_smul'' {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [module R M]
    (I : ideal R) (N : submodule R M) {M' : Type w} [add_comm_group M'] [module R M']
    (f : linear_map R M M') : map f (I • N) = I • map f N :=
  sorry

end submodule


namespace ideal


theorem exists_sub_one_mem_and_mem {R : Type u} [comm_ring R] {ι : Type v} (s : finset ι)
    {f : ι → ideal R} (hf : ∀ (i : ι), i ∈ s → ∀ (j : ι), j ∈ s → i ≠ j → f i ⊔ f j = ⊤) (i : ι)
    (his : i ∈ s) : ∃ (r : R), r - 1 ∈ f i ∧ ∀ (j : ι), j ∈ s → j ≠ i → r ∈ f j :=
  sorry

theorem exists_sub_mem {R : Type u} [comm_ring R] {ι : Type v} [fintype ι] {f : ι → ideal R}
    (hf : ∀ (i j : ι), i ≠ j → f i ⊔ f j = ⊤) (g : ι → R) : ∃ (r : R), ∀ (i : ι), r - g i ∈ f i :=
  sorry

/-- The homomorphism from `R/(⋂ i, f i)` to `∏ i, (R / f i)` featured in the Chinese
  Remainder Theorem. It is bijective if the ideals `f i` are comaximal. -/
def quotient_inf_to_pi_quotient {R : Type u} [comm_ring R] {ι : Type v} (f : ι → ideal R) :
    quotient (infi fun (i : ι) => f i) →+* (i : ι) → quotient (f i) :=
  quotient.lift (infi fun (i : ι) => f i)
    (eq.mpr sorry (pi.ring_hom fun (i : ι) => quotient.mk (f i))) sorry

theorem quotient_inf_to_pi_quotient_bijective {R : Type u} [comm_ring R] {ι : Type v} [fintype ι]
    {f : ι → ideal R} (hf : ∀ (i j : ι), i ≠ j → f i ⊔ f j = ⊤) :
    function.bijective ⇑(quotient_inf_to_pi_quotient f) :=
  sorry

/-- Chinese Remainder Theorem. Eisenbud Ex.2.6. Similar to Atiyah-Macdonald 1.10 and Stacks 00DT -/
def quotient_inf_ring_equiv_pi_quotient {R : Type u} [comm_ring R] {ι : Type v} [fintype ι]
    (f : ι → ideal R) (hf : ∀ (i j : ι), i ≠ j → f i ⊔ f j = ⊤) :
    quotient (infi fun (i : ι) => f i) ≃+* ((i : ι) → quotient (f i)) :=
  ring_equiv.mk
    (equiv.to_fun (equiv.of_bijective ⇑(quotient_inf_to_pi_quotient fun (i : ι) => f i) sorry))
    (equiv.inv_fun (equiv.of_bijective ⇑(quotient_inf_to_pi_quotient fun (i : ι) => f i) sorry))
    sorry sorry sorry sorry

protected instance has_mul {R : Type u} [comm_ring R] : Mul (ideal R) := { mul := has_scalar.smul }

theorem mul_mem_mul {R : Type u} [comm_ring R] {I : ideal R} {J : ideal R} {r : R} {s : R}
    (hr : r ∈ I) (hs : s ∈ J) : r * s ∈ I * J :=
  submodule.smul_mem_smul hr hs

theorem mul_mem_mul_rev {R : Type u} [comm_ring R] {I : ideal R} {J : ideal R} {r : R} {s : R}
    (hr : r ∈ I) (hs : s ∈ J) : s * r ∈ I * J :=
  mul_comm r s ▸ mul_mem_mul hr hs

theorem mul_le {R : Type u} [comm_ring R] {I : ideal R} {J : ideal R} {K : ideal R} :
    I * J ≤ K ↔ ∀ (r : R), r ∈ I → ∀ (s : R), s ∈ J → r * s ∈ K :=
  submodule.smul_le

theorem mul_le_left {R : Type u} [comm_ring R] {I : ideal R} {J : ideal R} : I * J ≤ J :=
  iff.mpr mul_le fun (r : R) (hr : r ∈ I) (s : R) => mul_mem_left J r

theorem mul_le_right {R : Type u} [comm_ring R] {I : ideal R} {J : ideal R} : I * J ≤ I :=
  iff.mpr mul_le fun (r : R) (hr : r ∈ I) (s : R) (hs : s ∈ J) => mul_mem_right I s hr

@[simp] theorem sup_mul_right_self {R : Type u} [comm_ring R] {I : ideal R} {J : ideal R} :
    I ⊔ I * J = I :=
  iff.mpr sup_eq_left mul_le_right

@[simp] theorem sup_mul_left_self {R : Type u} [comm_ring R] {I : ideal R} {J : ideal R} :
    I ⊔ J * I = I :=
  iff.mpr sup_eq_left mul_le_left

@[simp] theorem mul_right_self_sup {R : Type u} [comm_ring R] {I : ideal R} {J : ideal R} :
    I * J ⊔ I = I :=
  iff.mpr sup_eq_right mul_le_right

@[simp] theorem mul_left_self_sup {R : Type u} [comm_ring R] {I : ideal R} {J : ideal R} :
    J * I ⊔ I = I :=
  iff.mpr sup_eq_right mul_le_left

protected theorem mul_comm {R : Type u} [comm_ring R] (I : ideal R) (J : ideal R) : I * J = J * I :=
  le_antisymm
    (iff.mpr mul_le fun (r : R) (hrI : r ∈ I) (s : R) (hsJ : s ∈ J) => mul_mem_mul_rev hsJ hrI)
    (iff.mpr mul_le fun (r : R) (hrJ : r ∈ J) (s : R) (hsI : s ∈ I) => mul_mem_mul_rev hsI hrJ)

protected theorem mul_assoc {R : Type u} [comm_ring R] (I : ideal R) (J : ideal R) (K : ideal R) :
    I * J * K = I * (J * K) :=
  submodule.smul_assoc I J K

theorem span_mul_span {R : Type u} [comm_ring R] (S : set R) (T : set R) :
    span S * span T =
        span
          (set.Union
            fun (s : R) =>
              set.Union
                fun (H : s ∈ S) =>
                  set.Union fun (t : R) => set.Union fun (H : t ∈ T) => singleton (s * t)) :=
  submodule.span_smul_span S T

theorem span_mul_span' {R : Type u} [comm_ring R] (S : set R) (T : set R) :
    span S * span T = span (S * T) :=
  sorry

theorem span_singleton_mul_span_singleton {R : Type u} [comm_ring R] (r : R) (s : R) :
    span (singleton r) * span (singleton s) = span (singleton (r * s)) :=
  sorry

theorem mul_le_inf {R : Type u} [comm_ring R] {I : ideal R} {J : ideal R} : I * J ≤ I ⊓ J :=
  iff.mpr mul_le
    fun (r : R) (hri : r ∈ I) (s : R) (hsj : s ∈ J) =>
      { left := mul_mem_right I s hri, right := mul_mem_left J r hsj }

theorem prod_le_inf {R : Type u} {ι : Type u_1} [comm_ring R] {s : finset ι} {f : ι → ideal R} :
    finset.prod s f ≤ finset.inf s f :=
  sorry

theorem mul_eq_inf_of_coprime {R : Type u} [comm_ring R] {I : ideal R} {J : ideal R}
    (h : I ⊔ J = ⊤) : I * J = I ⊓ J :=
  sorry

theorem mul_bot {R : Type u} [comm_ring R] (I : ideal R) : I * ⊥ = ⊥ := submodule.smul_bot I

theorem bot_mul {R : Type u} [comm_ring R] (I : ideal R) : ⊥ * I = ⊥ := submodule.bot_smul I

theorem mul_top {R : Type u} [comm_ring R] (I : ideal R) : I * ⊤ = I :=
  ideal.mul_comm ⊤ I ▸ submodule.top_smul I

theorem top_mul {R : Type u} [comm_ring R] (I : ideal R) : ⊤ * I = I := submodule.top_smul I

theorem mul_mono {R : Type u} [comm_ring R] {I : ideal R} {J : ideal R} {K : ideal R} {L : ideal R}
    (hik : I ≤ K) (hjl : J ≤ L) : I * J ≤ K * L :=
  submodule.smul_mono hik hjl

theorem mul_mono_left {R : Type u} [comm_ring R] {I : ideal R} {J : ideal R} {K : ideal R}
    (h : I ≤ J) : I * K ≤ J * K :=
  submodule.smul_mono_left h

theorem mul_mono_right {R : Type u} [comm_ring R] {I : ideal R} {J : ideal R} {K : ideal R}
    (h : J ≤ K) : I * J ≤ I * K :=
  submodule.smul_mono_right h

theorem mul_sup {R : Type u} [comm_ring R] (I : ideal R) (J : ideal R) (K : ideal R) :
    I * (J ⊔ K) = I * J ⊔ I * K :=
  submodule.smul_sup I J K

theorem sup_mul {R : Type u} [comm_ring R] (I : ideal R) (J : ideal R) (K : ideal R) :
    (I ⊔ J) * K = I * K ⊔ J * K :=
  submodule.sup_smul I J K

theorem pow_le_pow {R : Type u} [comm_ring R] {I : ideal R} {m : ℕ} {n : ℕ} (h : m ≤ n) :
    I ^ n ≤ I ^ m :=
  sorry

theorem mul_eq_bot {R : Type u_1} [integral_domain R] {I : ideal R} {J : ideal R} :
    I * J = ⊥ ↔ I = ⊥ ∨ J = ⊥ :=
  sorry

/-- The radical of an ideal `I` consists of the elements `r` such that `r^n ∈ I` for some `n`. -/
def radical {R : Type u} [comm_ring R] (I : ideal R) : ideal R :=
  submodule.mk (set_of fun (r : R) => ∃ (n : ℕ), r ^ n ∈ I) sorry sorry sorry

theorem le_radical {R : Type u} [comm_ring R] {I : ideal R} : I ≤ radical I :=
  fun (r : R) (hri : r ∈ I) => Exists.intro 1 (Eq.symm (pow_one r) ▸ hri)

theorem radical_top (R : Type u) [comm_ring R] : radical ⊤ = ⊤ :=
  iff.mpr (eq_top_iff_one (radical ⊤)) (Exists.intro 0 submodule.mem_top)

theorem radical_mono {R : Type u} [comm_ring R] {I : ideal R} {J : ideal R} (H : I ≤ J) :
    radical I ≤ radical J :=
  sorry

@[simp] theorem radical_idem {R : Type u} [comm_ring R] (I : ideal R) :
    radical (radical I) = radical I :=
  sorry

theorem radical_eq_top {R : Type u} [comm_ring R] {I : ideal R} : radical I = ⊤ ↔ I = ⊤ := sorry

theorem is_prime.radical {R : Type u} [comm_ring R] {I : ideal R} (H : is_prime I) :
    radical I = I :=
  sorry

theorem radical_sup {R : Type u} [comm_ring R] (I : ideal R) (J : ideal R) :
    radical (I ⊔ J) = radical (radical I ⊔ radical J) :=
  sorry

theorem radical_inf {R : Type u} [comm_ring R] (I : ideal R) (J : ideal R) :
    radical (I ⊓ J) = radical I ⊓ radical J :=
  sorry

theorem radical_mul {R : Type u} [comm_ring R] (I : ideal R) (J : ideal R) :
    radical (I * J) = radical I ⊓ radical J :=
  sorry

theorem is_prime.radical_le_iff {R : Type u} [comm_ring R] {I : ideal R} {J : ideal R}
    (hj : is_prime J) : radical I ≤ J ↔ I ≤ J :=
  sorry

theorem radical_eq_Inf {R : Type u} [comm_ring R] (I : ideal R) :
    radical I = Inf (set_of fun (J : ideal R) => I ≤ J ∧ is_prime J) :=
  sorry

@[simp] theorem radical_bot_of_integral_domain {R : Type u} [integral_domain R] : radical ⊥ = ⊥ :=
  iff.mpr eq_bot_iff
    fun (x : R) (hx : x ∈ radical ⊥) =>
      Exists.rec_on hx fun (n : ℕ) (hn : x ^ n ∈ ⊥) => pow_eq_zero hn

protected instance comm_semiring {R : Type u} [comm_ring R] : comm_semiring (ideal R) :=
  submodule.comm_semiring

@[simp] theorem add_eq_sup {R : Type u} [comm_ring R] {I : ideal R} {J : ideal R} : I + J = I ⊔ J :=
  rfl

@[simp] theorem zero_eq_bot {R : Type u} [comm_ring R] : 0 = ⊥ := rfl

@[simp] theorem one_eq_top {R : Type u} [comm_ring R] : 1 = ⊤ := sorry

theorem top_pow (R : Type u) [comm_ring R] (n : ℕ) : ⊤ ^ n = ⊤ := sorry

theorem radical_pow {R : Type u} [comm_ring R] (I : ideal R) (n : ℕ) (H : n > 0) :
    radical (I ^ n) = radical I :=
  sorry

theorem is_prime.mul_le {R : Type u} [comm_ring R] {I : ideal R} {J : ideal R} {P : ideal R}
    (hp : is_prime P) : I * J ≤ P ↔ I ≤ P ∨ J ≤ P :=
  sorry

theorem is_prime.inf_le {R : Type u} [comm_ring R] {I : ideal R} {J : ideal R} {P : ideal R}
    (hp : is_prime P) : I ⊓ J ≤ P ↔ I ≤ P ∨ J ≤ P :=
  { mp := fun (h : I ⊓ J ≤ P) => iff.mp (is_prime.mul_le hp) (le_trans mul_le_inf h),
    mpr := fun (h : I ≤ P ∨ J ≤ P) => or.cases_on h (le_trans inf_le_left) (le_trans inf_le_right) }

theorem is_prime.prod_le {R : Type u} {ι : Type u_1} [comm_ring R] {s : finset ι} {f : ι → ideal R}
    {P : ideal R} (hp : is_prime P) (hne : finset.nonempty s) :
    finset.prod s f ≤ P ↔ ∃ (i : ι), ∃ (H : i ∈ s), f i ≤ P :=
  sorry

theorem is_prime.inf_le' {R : Type u} {ι : Type u_1} [comm_ring R] {s : finset ι} {f : ι → ideal R}
    {P : ideal R} (hp : is_prime P) (hsne : finset.nonempty s) :
    finset.inf s f ≤ P ↔ ∃ (i : ι), ∃ (H : i ∈ s), f i ≤ P :=
  sorry

theorem subset_union {R : Type u} [comm_ring R] {I : ideal R} {J : ideal R} {K : ideal R} :
    ↑I ⊆ ↑J ∪ ↑K ↔ I ≤ J ∨ I ≤ K :=
  sorry

theorem subset_union_prime' {R : Type u} {ι : Type u_1} [comm_ring R] {s : finset ι}
    {f : ι → ideal R} {a : ι} {b : ι} (hp : ∀ (i : ι), i ∈ s → is_prime (f i)) {I : ideal R} :
    (↑I ⊆ ↑(f a) ∪ ↑(f b) ∪ set.Union fun (i : ι) => set.Union fun (H : i ∈ ↑s) => ↑(f i)) ↔
        I ≤ f a ∨ I ≤ f b ∨ ∃ (i : ι), ∃ (H : i ∈ s), I ≤ f i :=
  sorry

/-- Prime avoidance. Atiyah-Macdonald 1.11, Eisenbud 3.3, Stacks 00DS, Matsumura Ex.1.6. -/
theorem subset_union_prime {R : Type u} {ι : Type u_1} [comm_ring R] {s : finset ι}
    {f : ι → ideal R} (a : ι) (b : ι) (hp : ∀ (i : ι), i ∈ s → i ≠ a → i ≠ b → is_prime (f i))
    {I : ideal R} :
    (↑I ⊆ set.Union fun (i : ι) => set.Union fun (H : i ∈ ↑s) => ↑(f i)) ↔
        ∃ (i : ι), ∃ (H : i ∈ s), I ≤ f i :=
  sorry

/-- `I.map f` is the span of the image of the ideal `I` under `f`, which may be bigger than
  the image itself. -/
def map {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (f : R →+* S) (I : ideal R) :
    ideal S :=
  span (⇑f '' ↑I)

/-- `I.comap f` is the preimage of `I` under `f`. -/
def comap {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (f : R →+* S) (I : ideal S) :
    ideal R :=
  submodule.mk (⇑f ⁻¹' ↑I) sorry sorry sorry

theorem map_mono {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] {f : R →+* S} {I : ideal R}
    {J : ideal R} (h : I ≤ J) : map f I ≤ map f J :=
  span_mono (set.image_subset (⇑f) h)

theorem mem_map_of_mem {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] {f : R →+* S}
    {I : ideal R} {x : R} (h : x ∈ I) : coe_fn f x ∈ map f I :=
  subset_span (Exists.intro x { left := h, right := rfl })

theorem map_le_iff_le_comap {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] {f : R →+* S}
    {I : ideal R} {K : ideal S} : map f I ≤ K ↔ I ≤ comap f K :=
  iff.trans span_le set.image_subset_iff

@[simp] theorem mem_comap {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] {f : R →+* S}
    {K : ideal S} {x : R} : x ∈ comap f K ↔ coe_fn f x ∈ K :=
  iff.rfl

theorem comap_mono {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] {f : R →+* S} {K : ideal S}
    {L : ideal S} (h : K ≤ L) : comap f K ≤ comap f L :=
  set.preimage_mono fun (x : R) (hx : x ∈ ↑(comap f K)) => h hx

theorem comap_ne_top {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (f : R →+* S)
    {K : ideal S} (hK : K ≠ ⊤) : comap f K ≠ ⊤ :=
  iff.mpr (ne_top_iff_one (comap f K))
    (eq.mpr (id (Eq._oldrec (Eq.refl (¬1 ∈ comap f K)) (propext mem_comap)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (¬coe_fn f 1 ∈ K)) (ring_hom.map_one f)))
        (iff.mp (ne_top_iff_one K) hK)))

theorem is_prime.comap {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (f : R →+* S)
    {K : ideal S} [hK : is_prime K] : is_prime (comap f K) :=
  sorry

theorem map_top {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (f : R →+* S) : map f ⊤ = ⊤ :=
  iff.mpr (eq_top_iff_one (map f ⊤))
    (subset_span (Exists.intro 1 { left := trivial, right := ring_hom.map_one f }))

theorem map_mul {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (f : R →+* S) (I : ideal R)
    (J : ideal R) : map f (I * J) = map f I * map f J :=
  sorry

theorem gc_map_comap {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (f : R →+* S) :
    galois_connection (map f) (comap f) :=
  fun (I : ideal R) (J : ideal S) => map_le_iff_le_comap

@[simp] theorem comap_id {R : Type u} [comm_ring R] (I : ideal R) : comap (ring_hom.id R) I = I :=
  ext fun (_x : R) => iff.rfl

@[simp] theorem map_id {R : Type u} [comm_ring R] (I : ideal R) : map (ring_hom.id R) I = I :=
  galois_connection.l_unique (gc_map_comap (ring_hom.id R)) galois_connection.id comap_id

theorem comap_comap {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] {T : Type u_1}
    [comm_ring T] {I : ideal T} (f : R →+* S) (g : S →+* T) :
    comap f (comap g I) = comap (ring_hom.comp g f) I :=
  rfl

theorem map_map {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] {T : Type u_1} [comm_ring T]
    {I : ideal R} (f : R →+* S) (g : S →+* T) : map g (map f I) = map (ring_hom.comp g f) I :=
  galois_connection.l_unique
    (galois_connection.compose (map f) (comap f) (map g) (comap g) (gc_map_comap f)
      (gc_map_comap g))
    (gc_map_comap (ring_hom.comp g f)) fun (_x : ideal T) => comap_comap f g

theorem map_le_of_le_comap {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] {f : R →+* S}
    {I : ideal R} {K : ideal S} : I ≤ comap f K → map f I ≤ K :=
  galois_connection.l_le (gc_map_comap f)

theorem le_comap_of_map_le {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] {f : R →+* S}
    {I : ideal R} {K : ideal S} : map f I ≤ K → I ≤ comap f K :=
  galois_connection.le_u (gc_map_comap f)

theorem le_comap_map {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] {f : R →+* S}
    {I : ideal R} : I ≤ comap f (map f I) :=
  galois_connection.le_u_l (gc_map_comap f) I

theorem map_comap_le {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] {f : R →+* S}
    {K : ideal S} : map f (comap f K) ≤ K :=
  galois_connection.l_u_le (gc_map_comap f) K

@[simp] theorem comap_top {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] {f : R →+* S} :
    comap f ⊤ = ⊤ :=
  galois_connection.u_top (gc_map_comap f)

@[simp] theorem comap_eq_top_iff {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] {f : R →+* S}
    {I : ideal S} : comap f I = ⊤ ↔ I = ⊤ :=
  sorry

@[simp] theorem map_bot {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] {f : R →+* S} :
    map f ⊥ = ⊥ :=
  galois_connection.l_bot (gc_map_comap f)

@[simp] theorem map_comap_map {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (f : R →+* S)
    (I : ideal R) : map f (comap f (map f I)) = map f I :=
  congr_fun (galois_connection.l_u_l_eq_l (gc_map_comap f)) I

@[simp] theorem comap_map_comap {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (f : R →+* S)
    (K : ideal S) : comap f (map f (comap f K)) = comap f K :=
  congr_fun (galois_connection.u_l_u_eq_u (gc_map_comap f)) K

theorem map_sup {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (f : R →+* S) (I : ideal R)
    (J : ideal R) : map f (I ⊔ J) = map f I ⊔ map f J :=
  galois_connection.l_sup (gc_map_comap f)

theorem comap_inf {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (f : R →+* S) (K : ideal S)
    (L : ideal S) : comap f (K ⊓ L) = comap f K ⊓ comap f L :=
  rfl

theorem map_supr {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (f : R →+* S) {ι : Sort u_1}
    (K : ι → ideal R) : map f (supr K) = supr fun (i : ι) => map f (K i) :=
  galois_connection.l_supr (gc_map_comap f)

theorem comap_infi {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (f : R →+* S)
    {ι : Sort u_1} (K : ι → ideal S) : comap f (infi K) = infi fun (i : ι) => comap f (K i) :=
  galois_connection.u_infi (gc_map_comap f)

theorem map_Sup {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (f : R →+* S)
    (s : set (ideal R)) :
    map f (Sup s) = supr fun (I : ideal R) => supr fun (H : I ∈ s) => map f I :=
  galois_connection.l_Sup (gc_map_comap f)

theorem comap_Inf {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (f : R →+* S)
    (s : set (ideal S)) :
    comap f (Inf s) = infi fun (I : ideal S) => infi fun (H : I ∈ s) => comap f I :=
  galois_connection.u_Inf (gc_map_comap f)

theorem comap_Inf' {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (f : R →+* S)
    (s : set (ideal S)) :
    comap f (Inf s) = infi fun (I : ideal R) => infi fun (H : I ∈ comap f '' s) => I :=
  sorry

theorem comap_radical {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (f : R →+* S)
    (K : ideal S) : comap f (radical K) = radical (comap f K) :=
  sorry

theorem comap_is_prime {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (f : R →+* S)
    (K : ideal S) [H : is_prime K] : is_prime (comap f K) :=
  sorry

@[simp] theorem map_quotient_self {R : Type u} [comm_ring R] (I : ideal R) :
    map (quotient.mk I) I = ⊥ :=
  iff.mpr eq_bot_iff
    (iff.mpr map_le_iff_le_comap
      fun (x : R) (hx : x ∈ I) =>
        iff.mpr (submodule.mem_bot (quotient I)) (iff.mpr quotient.eq_zero_iff_mem hx))

theorem map_inf_le {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (f : R →+* S) {I : ideal R}
    {J : ideal R} : map f (I ⊓ J) ≤ map f I ⊓ map f J :=
  monotone.map_inf_le (galois_connection.monotone_l (gc_map_comap f)) I J

theorem map_radical_le {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (f : R →+* S)
    {I : ideal R} : map f (radical I) ≤ radical (map f I) :=
  sorry

theorem le_comap_sup {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (f : R →+* S)
    {K : ideal S} {L : ideal S} : comap f K ⊔ comap f L ≤ comap f (K ⊔ L) :=
  monotone.le_map_sup (galois_connection.monotone_u (gc_map_comap f)) K L

theorem le_comap_mul {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (f : R →+* S)
    {K : ideal S} {L : ideal S} : comap f K * comap f L ≤ comap f (K * L) :=
  iff.mp map_le_iff_le_comap
    (Eq.symm (map_mul f (comap f K) (comap f L)) ▸
      mul_mono (iff.mpr map_le_iff_le_comap (le_refl (comap f K)))
        (iff.mpr map_le_iff_le_comap (le_refl (comap f L))))

theorem map_comap_of_surjective {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (f : R →+* S)
    (hf : function.surjective ⇑f) (I : ideal S) : map f (comap f I) = I :=
  sorry

/-- `map` and `comap` are adjoint, and the composition `map f ∘ comap f` is the
  identity -/
def gi_map_comap {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (f : R →+* S)
    (hf : function.surjective ⇑f) : galois_insertion (map f) (comap f) :=
  galois_insertion.monotone_intro sorry sorry sorry (map_comap_of_surjective f hf)

theorem map_surjective_of_surjective {R : Type u} {S : Type v} [comm_ring R] [comm_ring S]
    (f : R →+* S) (hf : function.surjective ⇑f) : function.surjective (map f) :=
  galois_insertion.l_surjective (gi_map_comap f hf)

theorem comap_injective_of_surjective {R : Type u} {S : Type v} [comm_ring R] [comm_ring S]
    (f : R →+* S) (hf : function.surjective ⇑f) : function.injective (comap f) :=
  galois_insertion.u_injective (gi_map_comap f hf)

theorem map_sup_comap_of_surjective {R : Type u} {S : Type v} [comm_ring R] [comm_ring S]
    (f : R →+* S) (hf : function.surjective ⇑f) (I : ideal S) (J : ideal S) :
    map f (comap f I ⊔ comap f J) = I ⊔ J :=
  galois_insertion.l_sup_u (gi_map_comap f hf) I J

theorem map_supr_comap_of_surjective {R : Type u} {S : Type v} [comm_ring R] [comm_ring S]
    (f : R →+* S) {ι : Sort u_1} (hf : function.surjective ⇑f) (K : ι → ideal S) :
    map f (supr fun (i : ι) => comap f (K i)) = supr K :=
  galois_insertion.l_supr_u (gi_map_comap f hf) fun (i : ι) => K i

theorem map_inf_comap_of_surjective {R : Type u} {S : Type v} [comm_ring R] [comm_ring S]
    (f : R →+* S) (hf : function.surjective ⇑f) (I : ideal S) (J : ideal S) :
    map f (comap f I ⊓ comap f J) = I ⊓ J :=
  galois_insertion.l_inf_u (gi_map_comap f hf) I J

theorem map_infi_comap_of_surjective {R : Type u} {S : Type v} [comm_ring R] [comm_ring S]
    (f : R →+* S) {ι : Sort u_1} (hf : function.surjective ⇑f) (K : ι → ideal S) :
    map f (infi fun (i : ι) => comap f (K i)) = infi K :=
  galois_insertion.l_infi_u (gi_map_comap f hf) fun (i : ι) => K i

theorem mem_image_of_mem_map_of_surjective {R : Type u} {S : Type v} [comm_ring R] [comm_ring S]
    (f : R →+* S) (hf : function.surjective ⇑f) {I : ideal R} {y : S} (H : y ∈ map f I) :
    y ∈ ⇑f '' ↑I :=
  sorry

theorem mem_map_iff_of_surjective {R : Type u} {S : Type v} [comm_ring R] [comm_ring S]
    (f : R →+* S) (hf : function.surjective ⇑f) {I : ideal R} {y : S} :
    y ∈ map f I ↔ ∃ (x : R), x ∈ I ∧ coe_fn f x = y :=
  sorry

theorem comap_map_of_surjective {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (f : R →+* S)
    (hf : function.surjective ⇑f) (I : ideal R) : comap f (map f I) = I ⊔ comap f ⊥ :=
  sorry

theorem le_map_of_comap_le_of_surjective {R : Type u} {S : Type v} [comm_ring R] [comm_ring S]
    (f : R →+* S) {I : ideal R} {K : ideal S} (hf : function.surjective ⇑f) :
    comap f K ≤ I → K ≤ map f I :=
  fun (h : comap f K ≤ I) => map_comap_of_surjective f hf K ▸ map_mono h

/-- Correspondence theorem -/
def rel_iso_of_surjective {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (f : R →+* S)
    (hf : function.surjective ⇑f) : ideal S ≃o Subtype fun (p : ideal R) => comap f ⊥ ≤ p :=
  rel_iso.mk
    (equiv.mk (fun (J : ideal S) => { val := comap f J, property := sorry })
      (fun (I : Subtype fun (p : ideal R) => comap f ⊥ ≤ p) => map f (subtype.val I)) sorry sorry)
    sorry

/-- The map on ideals induced by a surjective map preserves inclusion. -/
def order_embedding_of_surjective {R : Type u} {S : Type v} [comm_ring R] [comm_ring S]
    (f : R →+* S) (hf : function.surjective ⇑f) : ideal S ↪o ideal R :=
  rel_embedding.trans (rel_iso.to_rel_embedding (rel_iso_of_surjective f hf))
    (subtype.rel_embedding LessEq fun (p : ideal R) => comap f ⊥ ≤ p)

theorem map_eq_top_or_is_maximal_of_surjective {R : Type u} {S : Type v} [comm_ring R] [comm_ring S]
    (f : R →+* S) {I : ideal R} (hf : function.surjective ⇑f) (H : is_maximal I) :
    map f I = ⊤ ∨ is_maximal (map f I) :=
  sorry

theorem comap_is_maximal_of_surjective {R : Type u} {S : Type v} [comm_ring R] [comm_ring S]
    (f : R →+* S) {K : ideal S} (hf : function.surjective ⇑f) [H : is_maximal K] :
    is_maximal (comap f K) :=
  sorry

theorem mem_quotient_iff_mem {R : Type u} [comm_ring R] {I : ideal R} {J : ideal R} (hIJ : I ≤ J)
    {x : R} : coe_fn (quotient.mk I) x ∈ map (quotient.mk I) J ↔ x ∈ J :=
  sorry

theorem comap_bot_le_of_injective {R : Type u} {S : Type v} [comm_ring R] [comm_ring S]
    (f : R →+* S) {I : ideal R} (hf : function.injective ⇑f) : comap f ⊥ ≤ I :=
  sorry

/-- Special case of the correspondence theorem for isomorphic rings -/
def rel_iso_of_bijective {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (f : R →+* S)
    (hf : function.bijective ⇑f) : ideal S ≃o ideal R :=
  rel_iso.mk (equiv.mk (comap f) (map f) sorry sorry) sorry

theorem comap_le_iff_le_map {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (f : R →+* S)
    {I : ideal R} {K : ideal S} (hf : function.bijective ⇑f) : comap f K ≤ I ↔ K ≤ map f I :=
  { mp := fun (h : comap f K ≤ I) => le_map_of_comap_le_of_surjective f (and.right hf) h,
    mpr :=
      fun (h : K ≤ map f I) =>
        equiv.right_inv (rel_iso.to_equiv (rel_iso_of_bijective f hf)) I ▸ comap_mono h }

theorem map.is_maximal {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (f : R →+* S)
    {I : ideal R} (hf : function.bijective ⇑f) (H : is_maximal I) : is_maximal (map f I) :=
  sorry

theorem ring_equiv.bot_maximal_iff {R : Type u} {S : Type v} [comm_ring R] [comm_ring S]
    (e : R ≃+* S) : is_maximal ⊥ ↔ is_maximal ⊥ :=
  sorry

/-- A proper ideal `I` is primary iff `xy ∈ I` implies `x ∈ I` or `y ∈ radical I`. -/
def is_primary {R : Type u} [comm_ring R] (I : ideal R) :=
  I ≠ ⊤ ∧ ∀ {x y : R}, x * y ∈ I → x ∈ I ∨ y ∈ radical I

theorem is_primary.to_is_prime {R : Type u} [comm_ring R] (I : ideal R) (hi : is_prime I) :
    is_primary I :=
  { left := and.left hi,
    right :=
      fun (x y : R) (hxy : x * y ∈ I) =>
        or.imp id (fun (hyi : y ∈ I) => le_radical hyi) (and.right hi x y hxy) }

theorem mem_radical_of_pow_mem {R : Type u} [comm_ring R] {I : ideal R} {x : R} {m : ℕ}
    (hx : x ^ m ∈ radical I) : x ∈ radical I :=
  radical_idem I ▸ Exists.intro m hx

theorem is_prime_radical {R : Type u} [comm_ring R] {I : ideal R} (hi : is_primary I) :
    is_prime (radical I) :=
  sorry

theorem is_primary_inf {R : Type u} [comm_ring R] {I : ideal R} {J : ideal R} (hi : is_primary I)
    (hj : is_primary J) (hij : radical I = radical J) : is_primary (I ⊓ J) :=
  sorry

end ideal


namespace ring_hom


/-- Kernel of a ring homomorphism as an ideal of the domain. -/
def ker {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (f : R →+* S) : ideal R :=
  ideal.comap f ⊥

/-- An element is in the kernel if and only if it maps to zero.-/
theorem mem_ker {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (f : R →+* S) {r : R} :
    r ∈ ker f ↔ coe_fn f r = 0 :=
  sorry

theorem ker_eq {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (f : R →+* S) :
    ↑(ker f) = is_add_group_hom.ker ⇑f :=
  rfl

theorem ker_eq_comap_bot {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (f : R →+* S) :
    ker f = ideal.comap f ⊥ :=
  rfl

theorem injective_iff_ker_eq_bot {R : Type u} {S : Type v} [comm_ring R] [comm_ring S]
    (f : R →+* S) : function.injective ⇑f ↔ ker f = ⊥ :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (function.injective ⇑f ↔ ker f = ⊥)) (propext submodule.ext'_iff)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (function.injective ⇑f ↔ ↑(ker f) = ↑⊥)) (ker_eq f)))
      (is_add_group_hom.injective_iff_trivial_ker ⇑f))

theorem ker_eq_bot_iff_eq_zero {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (f : R →+* S) :
    ker f = ⊥ ↔ ∀ (x : R), coe_fn f x = 0 → x = 0 :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (ker f = ⊥ ↔ ∀ (x : R), coe_fn f x = 0 → x = 0))
        (propext submodule.ext'_iff)))
    (eq.mpr
      (id (Eq._oldrec (Eq.refl (↑(ker f) = ↑⊥ ↔ ∀ (x : R), coe_fn f x = 0 → x = 0)) (ker_eq f)))
      (is_add_group_hom.trivial_ker_iff_eq_zero ⇑f))

/-- If the target is not the zero ring, then one is not in the kernel.-/
theorem not_one_mem_ker {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] [nontrivial S]
    (f : R →+* S) : ¬1 ∈ ker f :=
  eq.mpr (id (Eq._oldrec (Eq.refl (¬1 ∈ ker f)) (propext (mem_ker f))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (¬coe_fn f 1 = 0)) (map_one f))) one_ne_zero)

@[simp] theorem ker_coe_equiv {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (f : R ≃+* S) :
    ker ↑f = ⊥ :=
  eq.mpr (id (propext (iff.symm (injective_iff_ker_eq_bot ↑f))))
    (eq.mp (Eq.refl (function.injective ⇑f)) (ring_equiv.injective f))

/-- The kernel of a homomorphism to an integral domain is a prime ideal.-/
theorem ker_is_prime {R : Type u} {S : Type v} [comm_ring R] [integral_domain S] (f : R →+* S) :
    ideal.is_prime (ker f) :=
  sorry

end ring_hom


namespace ideal


theorem map_eq_bot_iff_le_ker {R : Type u_1} {S : Type u_2} [comm_ring R] [comm_ring S]
    {I : ideal R} (f : R →+* S) : map f I = ⊥ ↔ I ≤ ring_hom.ker f :=
  sorry

@[simp] theorem mk_ker {R : Type u_1} [comm_ring R] {I : ideal R} :
    ring_hom.ker (quotient.mk I) = I :=
  sorry

theorem ker_le_comap {R : Type u_1} {S : Type u_2} [comm_ring R] [comm_ring S] {K : ideal S}
    (f : R →+* S) : ring_hom.ker f ≤ comap f K :=
  fun (x : R) (hx : x ∈ ring_hom.ker f) =>
    iff.mpr mem_comap (Eq.symm (iff.mp (ring_hom.mem_ker f) hx) ▸ ideal.zero_mem K)

theorem map_Inf {R : Type u_1} {S : Type u_2} [comm_ring R] [comm_ring S] {A : set (ideal R)}
    {f : R →+* S} (hf : function.surjective ⇑f) :
    (∀ (J : ideal R), J ∈ A → ring_hom.ker f ≤ J) → map f (Inf A) = Inf (map f '' A) :=
  sorry

theorem map_is_prime_of_surjective {R : Type u_1} {S : Type u_2} [comm_ring R] [comm_ring S]
    {f : R →+* S} (hf : function.surjective ⇑f) {I : ideal R} [H : is_prime I]
    (hk : ring_hom.ker f ≤ I) : is_prime (map f I) :=
  sorry

theorem map_is_prime_of_equiv {R : Type u_1} {S : Type u_2} [comm_ring R] [comm_ring S]
    (f : R ≃+* S) {I : ideal R} [is_prime I] : is_prime (map (↑f) I) :=
  sorry

theorem map_radical_of_surjective {R : Type u_1} {S : Type u_2} [comm_ring R] [comm_ring S]
    {f : R →+* S} (hf : function.surjective ⇑f) {I : ideal R} (h : ring_hom.ker f ≤ I) :
    map f (radical I) = radical (map f I) :=
  sorry

@[simp] theorem bot_quotient_is_maximal_iff {R : Type u_1} [comm_ring R] (I : ideal R) :
    is_maximal ⊥ ↔ is_maximal I :=
  { mp :=
      fun (hI : is_maximal ⊥) =>
        mk_ker ▸ comap_is_maximal_of_surjective (quotient.mk I) quotient.mk_surjective,
    mpr := fun (hI : is_maximal I) => bot_is_maximal }

/-- The `R`-algebra structure on `A/I` for an `R`-algebra `A` -/
protected instance quotient.algebra (R : Type u_1) [comm_ring R] {A : Type u_3} [comm_ring A]
    [algebra R A] {I : ideal A} : algebra R (quotient I) :=
  ring_hom.to_algebra (ring_hom.comp (quotient.mk I) (algebra_map R A))

/-- The canonical morphism `A →ₐ[R] I.quotient` as morphism of `R`-algebras, for `I` an ideal of
`A`, where `A` is an `R`-algebra. -/
def quotient.mkₐ (R : Type u_1) [comm_ring R] {A : Type u_3} [comm_ring A] [algebra R A]
    (I : ideal A) : alg_hom R A (quotient I) :=
  alg_hom.mk (fun (a : A) => submodule.quotient.mk a) sorry sorry sorry sorry sorry

theorem quotient.alg_map_eq (R : Type u_1) [comm_ring R] {A : Type u_3} [comm_ring A] [algebra R A]
    (I : ideal A) :
    algebra_map R (quotient I) = ring_hom.comp (algebra_map A (quotient I)) (algebra_map R A) :=
  sorry

protected instance quotient.is_scalar_tower (R : Type u_1) [comm_ring R] {A : Type u_3}
    [comm_ring A] [algebra R A] {I : ideal A} : is_scalar_tower R A (quotient I) :=
  is_scalar_tower.of_algebra_map_eq' (quotient.alg_map_eq R I)

theorem quotient.mkₐ_to_ring_hom (R : Type u_1) [comm_ring R] {A : Type u_3} [comm_ring A]
    [algebra R A] (I : ideal A) : alg_hom.to_ring_hom (quotient.mkₐ R I) = quotient.mk I :=
  rfl

@[simp] theorem quotient.mkₐ_eq_mk (R : Type u_1) [comm_ring R] {A : Type u_3} [comm_ring A]
    [algebra R A] (I : ideal A) : ⇑(quotient.mkₐ R I) = ⇑(quotient.mk I) :=
  rfl

/-- The canonical morphism `A →ₐ[R] I.quotient` is surjective. -/
theorem quotient.mkₐ_surjective (R : Type u_1) [comm_ring R] {A : Type u_3} [comm_ring A]
    [algebra R A] (I : ideal A) : function.surjective ⇑(quotient.mkₐ R I) :=
  surjective_quot_mk setoid.r

/-- The kernel of `A →ₐ[R] I.quotient` is `I`. -/
@[simp] theorem quotient.mkₐ_ker (R : Type u_1) [comm_ring R] {A : Type u_3} [comm_ring A]
    [algebra R A] (I : ideal A) : ring_hom.ker (alg_hom.to_ring_hom (quotient.mkₐ R I)) = I :=
  mk_ker

/-- The ring hom `R/J →+* S/I` induced by a ring hom `f : R →+* S` with `J ≤ f⁻¹(I)` -/
def quotient_map {R : Type u_1} {S : Type u_2} [comm_ring R] [comm_ring S] {I : ideal R}
    (J : ideal S) (f : R →+* S) (hIJ : I ≤ comap f J) : quotient I →+* quotient J :=
  quotient.lift I (ring_hom.comp (quotient.mk J) f) sorry

@[simp] theorem quotient_map_mk {R : Type u_1} {S : Type u_2} [comm_ring R] [comm_ring S]
    {J : ideal R} {I : ideal S} {f : R →+* S} {H : J ≤ comap f I} {x : R} :
    coe_fn (quotient_map I f H) (coe_fn (quotient.mk J) x) = coe_fn (quotient.mk I) (coe_fn f x) :=
  quotient.lift_mk J (ring_hom.comp (quotient.mk I) f) (quotient_map._proof_1 I f H)

theorem quotient_map_comp_mk {R : Type u_1} {S : Type u_2} [comm_ring R] [comm_ring S] {J : ideal R}
    {I : ideal S} {f : R →+* S} (H : J ≤ comap f I) :
    ring_hom.comp (quotient_map I f H) (quotient.mk J) = ring_hom.comp (quotient.mk I) f :=
  sorry

/-- `H` and `h` are kept as seperate hypothesis since H is used in constructing the quotient map -/
theorem quotient_map_injective' {R : Type u_1} {S : Type u_2} [comm_ring R] [comm_ring S]
    {J : ideal R} {I : ideal S} {f : R →+* S} {H : J ≤ comap f I} (h : comap f I ≤ J) :
    function.injective ⇑(quotient_map I f H) :=
  sorry

/-- If we take `J = I.comap f` then `quotient_map` is injective automatically. -/
theorem quotient_map_injective {R : Type u_1} {S : Type u_2} [comm_ring R] [comm_ring S]
    {I : ideal S} {f : R →+* S} : function.injective ⇑(quotient_map I f le_rfl) :=
  quotient_map_injective' le_rfl

theorem quotient_map_surjective {R : Type u_1} {S : Type u_2} [comm_ring R] [comm_ring S]
    {J : ideal R} {I : ideal S} {f : R →+* S} {H : J ≤ comap f I} (hf : function.surjective ⇑f) :
    function.surjective ⇑(quotient_map I f H) :=
  sorry

/-- Commutativity of a square is preserved when taking quotients by an ideal. -/
theorem comp_quotient_map_eq_of_comp_eq {R : Type u_1} {S : Type u_2} [comm_ring R] [comm_ring S]
    {R' : Type u_3} {S' : Type u_4} [comm_ring R'] [comm_ring S'] {f : R →+* S} {f' : R' →+* S'}
    {g : R →+* R'} {g' : S →+* S'} (hfg : ring_hom.comp f' g = ring_hom.comp g' f) (I : ideal S') :
    ring_hom.comp (quotient_map I g' le_rfl) (quotient_map (comap g' I) f le_rfl) =
        ring_hom.comp (quotient_map I f' le_rfl)
          (quotient_map (comap f' I) g
            (le_of_eq (trans (comap_comap f g') (hfg ▸ comap_comap g f')))) :=
  sorry

protected instance quotient_algebra {R : Type u_1} {S : Type u_2} [comm_ring R] [comm_ring S]
    {J : ideal S} [algebra R S] : algebra (quotient (comap (algebra_map R S) J)) (quotient J) :=
  ring_hom.to_algebra (quotient_map J (algebra_map R S) sorry)

theorem algebra_map_quotient_injective {R : Type u_1} {S : Type u_2} [comm_ring R] [comm_ring S]
    {J : ideal S} [algebra R S] :
    function.injective ⇑(algebra_map (quotient (comap (algebra_map R S) J)) (quotient J)) :=
  sorry

end ideal


namespace submodule


-- It is even a semialgebra. But those aren't in mathlib yet.

protected instance semimodule_submodule {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M]
    [module R M] : semimodule (ideal R) (submodule R M) :=
  semimodule.mk sup_smul bot_smul

end submodule


namespace ring_hom


/-- `lift_of_surjective f hf g hg` is the unique ring homomorphism `φ`

* such that `φ.comp f = g` (`lift_of_surjective_comp`),
* where `f : A →+* B` is surjective (`hf`),
* and `g : B →+* C` satisfies `hg : f.ker ≤ g.ker`.

See `lift_of_surjective_eq` for the uniqueness lemma.

```
   A .
   |  \
 f |   \ g
   |    \
   v     \⌟
   B ----> C
      ∃!φ
```
 -/
def lift_of_surjective {A : Type u_1} {B : Type u_2} {C : Type u_3} [comm_ring A] [comm_ring B]
    [comm_ring C] (f : A →+* B) (hf : function.surjective ⇑f) (g : A →+* C) (hg : ker f ≤ ker g) :
    B →+* C :=
  mk (fun (b : B) => coe_fn g (classical.some (hf b))) sorry sorry sorry sorry

@[simp] theorem lift_of_surjective_comp_apply {A : Type u_1} {B : Type u_2} {C : Type u_3}
    [comm_ring A] [comm_ring B] [comm_ring C] (f : A →+* B) (hf : function.surjective ⇑f)
    (g : A →+* C) (hg : ker f ≤ ker g) (a : A) :
    coe_fn (lift_of_surjective f hf g hg) (coe_fn f a) = coe_fn g a :=
  add_monoid_hom.lift_of_surjective_comp_apply (to_add_monoid_hom f) hf (to_add_monoid_hom g) hg a

@[simp] theorem lift_of_surjective_comp {A : Type u_1} {B : Type u_2} {C : Type u_3} [comm_ring A]
    [comm_ring B] [comm_ring C] (f : A →+* B) (hf : function.surjective ⇑f) (g : A →+* C)
    (hg : ker f ≤ ker g) : comp (lift_of_surjective f hf g hg) f = g :=
  sorry

theorem eq_lift_of_surjective {A : Type u_1} {B : Type u_2} {C : Type u_3} [comm_ring A]
    [comm_ring B] [comm_ring C] (f : A →+* B) (hf : function.surjective ⇑f) (g : A →+* C)
    (hg : ker f ≤ ker g) (h : B →+* C) (hh : comp h f = g) : h = lift_of_surjective f hf g hg :=
  sorry

end Mathlib