/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.linear_algebra.smodeq
import Mathlib.ring_theory.ideal.operations
import Mathlib.PostPort

universes u_1 u_2 u_3 

namespace Mathlib

/-!
# Completion of a module with respect to an ideal.

In this file we define the notions of Hausdorff, precomplete, and complete for an `R`-module `M`
with respect to an ideal `I`:

## Main definitions

- `is_Hausdorff I M`: this says that the intersection of `I^n M` is `0`.
- `is_precomplete I M`: this says that every Cauchy sequence converges.
- `is_adic_complete I M`: this says that `M` is Hausdorff and precomplete.
- `Hausdorffification I M`: this is the universal Hausdorff module with a map from `M`.
- `completion I M`: if `I` is finitely generated, then this is the universal complete module (TODO)
  with a map from `M`. This map is injective iff `M` is Hausdorff and surjective iff `M` is
  precomplete.

-/

/-- A module `M` is Hausdorff with respect to an ideal `I` if `⋂ I^n M = 0`. -/
def is_Hausdorff {R : Type u_1} [comm_ring R] (I : ideal R) (M : Type u_2) [add_comm_group M]
    [module R M] :=
  ∀ (x : M), (∀ (n : ℕ), smodeq (I ^ n • ⊤) x 0) → x = 0

/-- A module `M` is precomplete with respect to an ideal `I` if every Cauchy sequence converges. -/
def is_precomplete {R : Type u_1} [comm_ring R] (I : ideal R) (M : Type u_2) [add_comm_group M]
    [module R M] :=
  ∀ (f : ℕ → M),
    (∀ {m n : ℕ}, m ≤ n → smodeq (I ^ m • ⊤) (f m) (f n)) →
      ∃ (L : M), ∀ (n : ℕ), smodeq (I ^ n • ⊤) (f n) L

/-- A module `M` is `I`-adically complete if it is Hausdorff and precomplete. -/
def is_adic_complete {R : Type u_1} [comm_ring R] (I : ideal R) (M : Type u_2) [add_comm_group M]
    [module R M] :=
  is_Hausdorff I M ∧ is_precomplete I M

/-- The Hausdorffification of a module with respect to an ideal. -/
def Hausdorffification {R : Type u_1} [comm_ring R] (I : ideal R) (M : Type u_2) [add_comm_group M]
    [module R M] :=
  submodule.quotient (infi fun (n : ℕ) => I ^ n • ⊤)

/-- The completion of a module with respect to an ideal. This is not necessarily Hausdorff.
In fact, this is only complete if the ideal is finitely generated. -/
def adic_completion {R : Type u_1} [comm_ring R] (I : ideal R) (M : Type u_2) [add_comm_group M]
    [module R M] : submodule R ((n : ℕ) → submodule.quotient (I ^ n • ⊤)) :=
  submodule.mk
    (set_of
      fun (f : (n : ℕ) → submodule.quotient (I ^ n • ⊤)) =>
        ∀ {m n : ℕ},
          m ≤ n →
            coe_fn (submodule.liftq (I ^ n • ⊤) (submodule.mkq (I ^ m • ⊤)) sorry) (f n) = f m)
    sorry sorry sorry

namespace is_Hausdorff


protected instance bot {R : Type u_1} [comm_ring R] (M : Type u_2) [add_comm_group M] [module R M] :
    is_Hausdorff ⊥ M :=
  fun (x : M) (hx : ∀ (n : ℕ), smodeq (⊥ ^ n • ⊤) x 0) =>
    eq.mpr (id (Eq.refl (x = 0)))
      (eq.mp
        (Eq.trans
          ((fun (U U_1 : submodule R M) (e_1 : U = U_1) (x x_1 : M) (e_2 : x = x_1) (y y_1 : M)
              (e_3 : y = y_1) => congr (congr (congr_arg smodeq e_1) e_2) e_3)
            (⊥ ^ 1 • ⊤) ⊥
            (Eq.trans
              ((fun (ᾰ ᾰ_1 : ideal R) (e_2 : ᾰ = ᾰ_1) (ᾰ_2 ᾰ_3 : submodule R M) (e_3 : ᾰ_2 = ᾰ_3) =>
                  congr (congr_arg has_scalar.smul e_2) e_3)
                (⊥ ^ 1) ⊥ (pow_one ⊥) ⊤ ⊤ (Eq.refl ⊤))
              (submodule.bot_smul ⊤))
            x x (Eq.refl x) 0 0 (Eq.refl 0))
          (propext smodeq.bot))
        (hx 1))

protected theorem subsingleton {R : Type u_1} [comm_ring R] {M : Type u_2} [add_comm_group M]
    [module R M] (h : is_Hausdorff ⊤ M) : subsingleton M :=
  sorry

protected instance of_subsingleton {R : Type u_1} [comm_ring R] (I : ideal R) (M : Type u_2)
    [add_comm_group M] [module R M] [subsingleton M] : is_Hausdorff I M :=
  fun (x : M) (_x : ∀ (n : ℕ), smodeq (I ^ n • ⊤) x 0) => subsingleton.elim x 0

theorem infi_pow_smul {R : Type u_1} [comm_ring R] {I : ideal R} {M : Type u_2} [add_comm_group M]
    [module R M] (h : is_Hausdorff I M) : (infi fun (n : ℕ) => I ^ n • ⊤) = ⊥ :=
  sorry

end is_Hausdorff


namespace Hausdorffification


/-- The canonical linear map to the Hausdorffification. -/
def of {R : Type u_1} [comm_ring R] (I : ideal R) (M : Type u_2) [add_comm_group M] [module R M] :
    linear_map R M (Hausdorffification I M) :=
  submodule.mkq (infi fun (n : ℕ) => I ^ n • ⊤)

theorem induction_on {R : Type u_1} [comm_ring R] {I : ideal R} {M : Type u_2} [add_comm_group M]
    [module R M] {C : Hausdorffification I M → Prop} (x : Hausdorffification I M)
    (ih : ∀ (x : M), C (coe_fn (of I M) x)) : C x :=
  quotient.induction_on' x ih

protected instance is_Hausdorff {R : Type u_1} [comm_ring R] (I : ideal R) (M : Type u_2)
    [add_comm_group M] [module R M] : is_Hausdorff I (Hausdorffification I M) :=
  sorry

/-- universal property of Hausdorffification: any linear map to a Hausdorff module extends to a
unique map from the Hausdorffification. -/
def lift {R : Type u_1} [comm_ring R] (I : ideal R) {M : Type u_2} [add_comm_group M] [module R M]
    {N : Type u_3} [add_comm_group N] [module R N] [h : is_Hausdorff I N] (f : linear_map R M N) :
    linear_map R (Hausdorffification I M) N :=
  submodule.liftq (infi fun (n : ℕ) => I ^ n • ⊤) f sorry

theorem lift_of {R : Type u_1} [comm_ring R] (I : ideal R) {M : Type u_2} [add_comm_group M]
    [module R M] {N : Type u_3} [add_comm_group N] [module R N] [h : is_Hausdorff I N]
    (f : linear_map R M N) (x : M) : coe_fn (lift I f) (coe_fn (of I M) x) = coe_fn f x :=
  rfl

theorem lift_comp_of {R : Type u_1} [comm_ring R] (I : ideal R) {M : Type u_2} [add_comm_group M]
    [module R M] {N : Type u_3} [add_comm_group N] [module R N] [h : is_Hausdorff I N]
    (f : linear_map R M N) : linear_map.comp (lift I f) (of I M) = f :=
  linear_map.ext fun (_x : M) => rfl

/-- Uniqueness of lift. -/
theorem lift_eq {R : Type u_1} [comm_ring R] (I : ideal R) {M : Type u_2} [add_comm_group M]
    [module R M] {N : Type u_3} [add_comm_group N] [module R N] [h : is_Hausdorff I N]
    (f : linear_map R M N) (g : linear_map R (Hausdorffification I M) N)
    (hg : linear_map.comp g (of I M) = f) : g = lift I f :=
  sorry

end Hausdorffification


namespace is_precomplete


protected instance bot {R : Type u_1} [comm_ring R] (M : Type u_2) [add_comm_group M] [module R M] :
    is_precomplete ⊥ M :=
  fun (f : ℕ → M) (hf : ∀ {m n : ℕ}, m ≤ n → smodeq (⊥ ^ m • ⊤) (f m) (f n)) =>
    Exists.intro (f 1)
      fun (n : ℕ) =>
        nat.cases_on n
          (eq.mpr (id (Eq._oldrec (Eq.refl (smodeq (⊥ ^ 0 • ⊤) (f 0) (f 1))) (pow_zero ⊥)))
            (eq.mpr (id (Eq._oldrec (Eq.refl (smodeq (1 • ⊤) (f 0) (f 1))) ideal.one_eq_top))
              (eq.mpr
                (id (Eq._oldrec (Eq.refl (smodeq (⊤ • ⊤) (f 0) (f 1))) (submodule.top_smul ⊤)))
                smodeq.top)))
          fun (n : ℕ) =>
            eq.mpr
              (id
                (Eq._oldrec (Eq.refl (smodeq (⊥ ^ Nat.succ n • ⊤) (f (Nat.succ n)) (f 1)))
                  (eq.mp (Eq._oldrec (Eq.refl (smodeq ⊥ (f 1) (f (n + 1)))) (propext smodeq.bot))
                    (eq.mp
                      (Eq._oldrec (Eq.refl (smodeq (⊥ • ⊤) (f 1) (f (n + 1))))
                        (submodule.bot_smul ⊤))
                      (eq.mp
                        (Eq._oldrec (Eq.refl (smodeq (⊥ ^ 1 • ⊤) (f 1) (f (n + 1)))) (pow_one ⊥))
                        (hf (nat.le_add_left 1 n)))))))
              smodeq.refl

protected instance top {R : Type u_1} [comm_ring R] (M : Type u_2) [add_comm_group M] [module R M] :
    is_precomplete ⊤ M :=
  fun (f : ℕ → M) (hf : ∀ {m n : ℕ}, m ≤ n → smodeq (⊤ ^ m • ⊤) (f m) (f n)) =>
    Exists.intro 0
      fun (n : ℕ) =>
        eq.mpr (id (Eq._oldrec (Eq.refl (smodeq (⊤ ^ n • ⊤) (f n) 0)) (ideal.top_pow R n)))
          (eq.mpr (id (Eq._oldrec (Eq.refl (smodeq (⊤ • ⊤) (f n) 0)) (submodule.top_smul ⊤)))
            smodeq.top)

protected instance of_subsingleton {R : Type u_1} [comm_ring R] (I : ideal R) (M : Type u_2)
    [add_comm_group M] [module R M] [subsingleton M] : is_precomplete I M :=
  fun (f : ℕ → M) (hf : ∀ {m n : ℕ}, m ≤ n → smodeq (I ^ m • ⊤) (f m) (f n)) =>
    Exists.intro 0
      fun (n : ℕ) =>
        eq.mpr (id (Eq._oldrec (Eq.refl (smodeq (I ^ n • ⊤) (f n) 0)) (subsingleton.elim (f n) 0)))
          smodeq.refl

end is_precomplete


namespace adic_completion


/-- The canonical linear map to the completion. -/
def of {R : Type u_1} [comm_ring R] (I : ideal R) (M : Type u_2) [add_comm_group M] [module R M] :
    linear_map R M ↥(adic_completion I M) :=
  linear_map.mk
    (fun (x : M) =>
      { val := fun (n : ℕ) => coe_fn (submodule.mkq (I ^ n • ⊤)) x, property := sorry })
    sorry sorry

@[simp] theorem of_apply {R : Type u_1} [comm_ring R] (I : ideal R) (M : Type u_2)
    [add_comm_group M] [module R M] (x : M) (n : ℕ) :
    subtype.val (coe_fn (of I M) x) n = coe_fn (submodule.mkq (I ^ n • ⊤)) x :=
  rfl

/-- Linearly evaluating a sequence in the completion at a given input. -/
def eval {R : Type u_1} [comm_ring R] (I : ideal R) (M : Type u_2) [add_comm_group M] [module R M]
    (n : ℕ) : linear_map R (↥(adic_completion I M)) (submodule.quotient (I ^ n • ⊤)) :=
  linear_map.mk (fun (f : ↥(adic_completion I M)) => subtype.val f n) sorry sorry

@[simp] theorem coe_eval {R : Type u_1} [comm_ring R] (I : ideal R) (M : Type u_2)
    [add_comm_group M] [module R M] (n : ℕ) :
    ⇑(eval I M n) = fun (f : ↥(adic_completion I M)) => subtype.val f n :=
  rfl

theorem eval_apply {R : Type u_1} [comm_ring R] (I : ideal R) (M : Type u_2) [add_comm_group M]
    [module R M] (n : ℕ) (f : ↥(adic_completion I M)) : coe_fn (eval I M n) f = subtype.val f n :=
  rfl

theorem eval_of {R : Type u_1} [comm_ring R] (I : ideal R) (M : Type u_2) [add_comm_group M]
    [module R M] (n : ℕ) (x : M) :
    coe_fn (eval I M n) (coe_fn (of I M) x) = coe_fn (submodule.mkq (I ^ n • ⊤)) x :=
  rfl

@[simp] theorem eval_comp_of {R : Type u_1} [comm_ring R] (I : ideal R) (M : Type u_2)
    [add_comm_group M] [module R M] (n : ℕ) :
    linear_map.comp (eval I M n) (of I M) = submodule.mkq (I ^ n • ⊤) :=
  rfl

@[simp] theorem range_eval {R : Type u_1} [comm_ring R] (I : ideal R) (M : Type u_2)
    [add_comm_group M] [module R M] (n : ℕ) : linear_map.range (eval I M n) = ⊤ :=
  iff.mpr linear_map.range_eq_top
    fun (x : submodule.quotient (I ^ n • ⊤)) =>
      quotient.induction_on' x fun (x : M) => Exists.intro (coe_fn (of I M) x) rfl

theorem ext {R : Type u_1} [comm_ring R] {I : ideal R} {M : Type u_2} [add_comm_group M]
    [module R M] {x : ↥(adic_completion I M)} {y : ↥(adic_completion I M)}
    (h : ∀ (n : ℕ), coe_fn (eval I M n) x = coe_fn (eval I M n) y) : x = y :=
  subtype.eq (funext h)

protected instance is_Hausdorff {R : Type u_1} [comm_ring R] (I : ideal R) (M : Type u_2)
    [add_comm_group M] [module R M] : is_Hausdorff I ↥(adic_completion I M) :=
  sorry

end adic_completion


namespace is_adic_complete


protected instance bot {R : Type u_1} [comm_ring R] (M : Type u_2) [add_comm_group M] [module R M] :
    is_adic_complete ⊥ M :=
  { left := is_Hausdorff.bot M, right := is_precomplete.bot M }

protected theorem subsingleton {R : Type u_1} [comm_ring R] (M : Type u_2) [add_comm_group M]
    [module R M] (h : is_adic_complete ⊤ M) : subsingleton M :=
  is_Hausdorff.subsingleton (and.left h)

protected instance of_subsingleton {R : Type u_1} [comm_ring R] (I : ideal R) (M : Type u_2)
    [add_comm_group M] [module R M] [subsingleton M] : is_adic_complete I M :=
  { left := is_Hausdorff.of_subsingleton I M, right := is_precomplete.of_subsingleton I M }

end Mathlib