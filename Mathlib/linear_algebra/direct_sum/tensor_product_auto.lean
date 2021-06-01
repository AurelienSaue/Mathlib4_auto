/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.linear_algebra.tensor_product
import Mathlib.linear_algebra.direct_sum_module
import Mathlib.PostPort

universes u_1 u_2 u_3 u_4 u_5 

namespace Mathlib

namespace tensor_product


/-- The linear equivalence `(⨁ i₁, M₁ i₁) ⊗ (⨁ i₂, M₂ i₂) ≃ (⨁ i₁, ⨁ i₂, M₁ i₁ ⊗ M₂ i₂)`, i.e.
"tensor product distributes over direct sum". -/
def direct_sum (R : Type u_1) [comm_ring R] (ι₁ : Type u_2) (ι₂ : Type u_3) [DecidableEq ι₁]
    [DecidableEq ι₂] (M₁ : ι₁ → Type u_4) (M₂ : ι₂ → Type u_5) [(i₁ : ι₁) → add_comm_group (M₁ i₁)]
    [(i₂ : ι₂) → add_comm_group (M₂ i₂)] [(i₁ : ι₁) → module R (M₁ i₁)]
    [(i₂ : ι₂) → module R (M₂ i₂)] :
    linear_equiv R
        (tensor_product R (direct_sum ι₁ fun (i₁ : ι₁) => M₁ i₁)
          (direct_sum ι₂ fun (i₂ : ι₂) => M₂ i₂))
        (direct_sum (ι₁ × ι₂)
          fun (i : ι₁ × ι₂) => tensor_product R (M₁ (prod.fst i)) (M₂ (prod.snd i))) :=
  linear_equiv.of_linear
    (lift
      (direct_sum.to_module R ι₁
        (linear_map R (direct_sum ι₂ fun (i₂ : ι₂) => M₂ i₂)
          (direct_sum (ι₁ × ι₂)
            fun (i : ι₁ × ι₂) => tensor_product R (M₁ (prod.fst i)) (M₂ (prod.snd i))))
        fun (i₁ : ι₁) =>
          linear_map.flip
            (direct_sum.to_module R ι₂
              (linear_map R (M₁ i₁)
                (direct_sum (ι₁ × ι₂)
                  fun (i : ι₁ × ι₂) => tensor_product R (M₁ (prod.fst i)) (M₂ (prod.snd i))))
              fun (i₂ : ι₂) =>
                linear_map.flip
                  (curry
                    (direct_sum.lof R (ι₁ × ι₂)
                      (fun (i : ι₁ × ι₂) => tensor_product R (M₁ (prod.fst i)) (M₂ (prod.snd i)))
                      (i₁, i₂))))))
    (direct_sum.to_module R (ι₁ × ι₂)
      (tensor_product R (direct_sum ι₁ fun (i₁ : ι₁) => M₁ i₁)
        (direct_sum ι₂ fun (i₂ : ι₂) => M₂ i₂))
      fun (i : ι₁ × ι₂) =>
        map (direct_sum.lof R ι₁ M₁ (prod.fst i)) (direct_sum.lof R ι₂ M₂ (prod.snd i)))
    sorry sorry

@[simp] theorem direct_sum_lof_tmul_lof (R : Type u_1) [comm_ring R] (ι₁ : Type u_2) (ι₂ : Type u_3)
    [DecidableEq ι₁] [DecidableEq ι₂] (M₁ : ι₁ → Type u_4) (M₂ : ι₂ → Type u_5)
    [(i₁ : ι₁) → add_comm_group (M₁ i₁)] [(i₂ : ι₂) → add_comm_group (M₂ i₂)]
    [(i₁ : ι₁) → module R (M₁ i₁)] [(i₂ : ι₂) → module R (M₂ i₂)] (i₁ : ι₁) (m₁ : M₁ i₁) (i₂ : ι₂)
    (m₂ : M₂ i₂) :
    coe_fn (direct_sum R ι₁ ι₂ M₁ M₂)
          (tmul R (coe_fn (direct_sum.lof R ι₁ M₁ i₁) m₁) (coe_fn (direct_sum.lof R ι₂ M₂ i₂) m₂)) =
        coe_fn
          (direct_sum.lof R (ι₁ × ι₂)
            (fun (i : ι₁ × ι₂) => tensor_product R (M₁ (prod.fst i)) (M₂ (prod.snd i))) (i₁, i₂))
          (tmul R m₁ m₂) :=
  sorry

end Mathlib