/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.multiset.powerset
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# The antidiagonal on a multiset.

The antidiagonal of a multiset `s` consists of all pairs `(t₁, t₂)`
such that `t₁ + t₂ = s`. These pairs are counted with multiplicities.
-/

namespace multiset


/-- The antidiagonal of a multiset `s` consists of all pairs `(t₁, t₂)`
    such that `t₁ + t₂ = s`. These pairs are counted with multiplicities. -/
def antidiagonal {α : Type u_1} (s : multiset α) : multiset (multiset α × multiset α) :=
  quot.lift_on s (fun (l : List α) => ↑(list.revzip (powerset_aux l))) sorry

theorem antidiagonal_coe {α : Type u_1} (l : List α) :
    antidiagonal ↑l = ↑(list.revzip (powerset_aux l)) :=
  rfl

@[simp] theorem antidiagonal_coe' {α : Type u_1} (l : List α) :
    antidiagonal ↑l = ↑(list.revzip (powerset_aux' l)) :=
  quot.sound revzip_powerset_aux_perm_aux'

/-- A pair `(t₁, t₂)` of multisets is contained in `antidiagonal s`
    if and only if `t₁ + t₂ = s`. -/
@[simp] theorem mem_antidiagonal {α : Type u_1} {s : multiset α} {x : multiset α × multiset α} :
    x ∈ antidiagonal s ↔ prod.fst x + prod.snd x = s :=
  sorry

@[simp] theorem antidiagonal_map_fst {α : Type u_1} (s : multiset α) :
    map prod.fst (antidiagonal s) = powerset s :=
  sorry

@[simp] theorem antidiagonal_map_snd {α : Type u_1} (s : multiset α) :
    map prod.snd (antidiagonal s) = powerset s :=
  sorry

@[simp] theorem antidiagonal_zero {α : Type u_1} : antidiagonal 0 = (0, 0) ::ₘ 0 := rfl

@[simp] theorem antidiagonal_cons {α : Type u_1} (a : α) (s : multiset α) :
    antidiagonal (a ::ₘ s) =
        map (prod.map id (cons a)) (antidiagonal s) + map (prod.map (cons a) id) (antidiagonal s) :=
  sorry

@[simp] theorem card_antidiagonal {α : Type u_1} (s : multiset α) :
    coe_fn card (antidiagonal s) = bit0 1 ^ coe_fn card s :=
  sorry

theorem prod_map_add {α : Type u_1} {β : Type u_2} [comm_semiring β] {s : multiset α} {f : α → β}
    {g : α → β} :
    prod (map (fun (a : α) => f a + g a) s) =
        sum
          (map
            (fun (p : multiset α × multiset α) =>
              prod (map f (prod.fst p)) * prod (map g (prod.snd p)))
            (antidiagonal s)) :=
  sorry

end Mathlib