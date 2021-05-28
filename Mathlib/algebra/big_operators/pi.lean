/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.ring.pi
import Mathlib.algebra.big_operators.basic
import Mathlib.data.fintype.basic
import Mathlib.algebra.group.prod
import Mathlib.PostPort

universes u_1 u_2 u_3 

namespace Mathlib

/-!
# Big operators for Pi Types

This file contains theorems relevant to big operators in binary and arbitrary product
of monoids and groups
-/

namespace pi


theorem list_sum_apply {α : Type u_1} {β : α → Type u_2} [(a : α) → add_monoid (β a)] (a : α) (l : List ((a : α) → β a)) : list.sum l a = list.sum (list.map (fun (f : (a : α) → β a) => f a) l) :=
  add_monoid_hom.map_list_sum (add_monoid_hom.apply β a) l

theorem multiset_sum_apply {α : Type u_1} {β : α → Type u_2} [(a : α) → add_comm_monoid (β a)] (a : α) (s : multiset ((a : α) → β a)) : multiset.sum s a = multiset.sum (multiset.map (fun (f : (a : α) → β a) => f a) s) :=
  add_monoid_hom.map_multiset_sum (add_monoid_hom.apply β a) s

end pi


@[simp] theorem finset.sum_apply {α : Type u_1} {β : α → Type u_2} {γ : Type u_3} [(a : α) → add_comm_monoid (β a)] (a : α) (s : finset γ) (g : γ → (a : α) → β a) : finset.sum s (fun (c : γ) => g c) a = finset.sum s fun (c : γ) => g c a :=
  add_monoid_hom.map_sum (add_monoid_hom.apply β a) (fun (c : γ) => g c) s

@[simp] theorem fintype.prod_apply {α : Type u_1} {β : α → Type u_2} {γ : Type u_3} [fintype γ] [(a : α) → comm_monoid (β a)] (a : α) (g : γ → (a : α) → β a) : finset.prod finset.univ (fun (c : γ) => g c) a = finset.prod finset.univ fun (c : γ) => g c a :=
  finset.prod_apply a finset.univ g

theorem prod_mk_prod {α : Type u_1} {β : Type u_2} {γ : Type u_3} [comm_monoid α] [comm_monoid β] (s : finset γ) (f : γ → α) (g : γ → β) : (finset.prod s fun (x : γ) => f x, finset.prod s fun (x : γ) => g x) = finset.prod s fun (x : γ) => (f x, g x) := sorry

-- As we only defined `single` into `add_monoid`, we only prove the `finset.sum` version here.

theorem finset.univ_sum_single {I : Type u_1} [DecidableEq I] {Z : I → Type u_2} [(i : I) → add_comm_monoid (Z i)] [fintype I] (f : (i : I) → Z i) : (finset.sum finset.univ fun (i : I) => pi.single i (f i)) = f := sorry

theorem add_monoid_hom.functions_ext {I : Type u_1} [DecidableEq I] {Z : I → Type u_2} [(i : I) → add_comm_monoid (Z i)] [fintype I] (G : Type u_3) [add_comm_monoid G] (g : ((i : I) → Z i) →+ G) (h : ((i : I) → Z i) →+ G) (w : ∀ (i : I) (x : Z i), coe_fn g (pi.single i x) = coe_fn h (pi.single i x)) : g = h := sorry

-- we need `apply`+`convert` because Lean fails to unify different `add_monoid` instances

-- on `Π i, f i`

theorem ring_hom.functions_ext {I : Type u_1} [DecidableEq I] {f : I → Type u_2} [(i : I) → semiring (f i)] [fintype I] (G : Type u_3) [semiring G] (g : ((i : I) → f i) →+* G) (h : ((i : I) → f i) →+* G) (w : ∀ (i : I) (x : f i), coe_fn g (pi.single i x) = coe_fn h (pi.single i x)) : g = h := sorry

namespace prod


theorem fst_prod {α : Type u_1} {β : Type u_2} {γ : Type u_3} [comm_monoid α] [comm_monoid β] {s : finset γ} {f : γ → α × β} : fst (finset.prod s fun (c : γ) => f c) = finset.prod s fun (c : γ) => fst (f c) :=
  monoid_hom.map_prod (monoid_hom.fst α β) f s

theorem snd_prod {α : Type u_1} {β : Type u_2} {γ : Type u_3} [comm_monoid α] [comm_monoid β] {s : finset γ} {f : γ → α × β} : snd (finset.prod s fun (c : γ) => f c) = finset.prod s fun (c : γ) => snd (f c) :=
  monoid_hom.map_prod (monoid_hom.snd α β) f s

