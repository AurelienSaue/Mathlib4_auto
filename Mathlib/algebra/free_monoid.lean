/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.equiv.basic
import Mathlib.data.list.basic
import Mathlib.algebra.star.basic
import Mathlib.PostPort

universes u_1 u_2 u_4 u_5 u_3 

namespace Mathlib

/-!
# Free monoid over a given alphabet

## Main definitions

* `free_monoid α`: free monoid over alphabet `α`; defined as a synonym for `list α`
  with multiplication given by `(++)`.
* `free_monoid.of`: embedding `α → free_monoid α` sending each element `x` to `[x]`;
* `free_monoid.lift`: natural equivalence between `α → M` and `free_monoid α →* M`
* `free_monoid.map`: embedding of `α → β` into `free_monoid α →* free_monoid β` given by `list.map`.
-/

/-- Free monoid over a given alphabet. -/
def free_add_monoid (α : Type u_1)  :=
  List α

namespace free_monoid


protected instance Mathlib.free_add_monoid.add_monoid {α : Type u_1} : add_monoid (free_add_monoid α) :=
  add_monoid.mk (fun (x y : free_add_monoid α) => x ++ y) sorry [] sorry sorry

protected instance inhabited {α : Type u_1} : Inhabited (free_monoid α) :=
  { default := 1 }

theorem one_def {α : Type u_1} : 1 = [] :=
  rfl

theorem Mathlib.free_add_monoid.add_def {α : Type u_1} (xs : List α) (ys : List α) : xs + ys = xs ++ ys :=
  rfl

/-- Embeds an element of `α` into `free_monoid α` as a singleton list. -/
def of {α : Type u_1} (x : α) : free_monoid α :=
  [x]

theorem of_def {α : Type u_1} (x : α) : of x = [x] :=
  rfl

theorem of_injective {α : Type u_1} : function.injective of :=
  fun (a b : α) => list.head_eq_of_cons_eq

/-- Recursor for `free_monoid` using `1` and `of x * xs` instead of `[]` and `x :: xs`. -/
def rec_on {α : Type u_1} {C : free_monoid α → Sort u_2} (xs : free_monoid α) (h0 : C 1) (ih : (x : α) → (xs : free_monoid α) → C xs → C (of x * xs)) : C xs :=
  list.rec_on xs h0 ih

theorem hom_eq {α : Type u_1} {M : Type u_4} [monoid M] {f : free_monoid α →* M} {g : free_monoid α →* M} (h : ∀ (x : α), coe_fn f (of x) = coe_fn g (of x)) : f = g := sorry

/-- Equivalence between maps `α → M` and monoid homomorphisms `free_monoid α →* M`. -/
def lift {α : Type u_1} {M : Type u_4} [monoid M] : (α → M) ≃ (free_monoid α →* M) :=
  equiv.mk (fun (f : α → M) => monoid_hom.mk (fun (l : free_monoid α) => list.prod (list.map f l)) sorry sorry)
    (fun (f : free_monoid α →* M) (x : α) => coe_fn f (of x)) sorry sorry

@[simp] theorem Mathlib.free_add_monoid.lift_symm_apply {α : Type u_1} {M : Type u_4} [add_monoid M] (f : free_add_monoid α →+ M) : coe_fn (equiv.symm free_add_monoid.lift) f = ⇑f ∘ free_add_monoid.of :=
  rfl

theorem lift_apply {α : Type u_1} {M : Type u_4} [monoid M] (f : α → M) (l : free_monoid α) : coe_fn (coe_fn lift f) l = list.prod (list.map f l) :=
  rfl

theorem Mathlib.free_add_monoid.lift_comp_of {α : Type u_1} {M : Type u_4} [add_monoid M] (f : α → M) : ⇑(coe_fn free_add_monoid.lift f) ∘ free_add_monoid.of = f :=
  equiv.symm_apply_apply free_add_monoid.lift f

@[simp] theorem Mathlib.free_add_monoid.lift_eval_of {α : Type u_1} {M : Type u_4} [add_monoid M] (f : α → M) (x : α) : coe_fn (coe_fn free_add_monoid.lift f) (free_add_monoid.of x) = f x :=
  congr_fun (free_add_monoid.lift_comp_of f) x

@[simp] theorem lift_restrict {α : Type u_1} {M : Type u_4} [monoid M] (f : free_monoid α →* M) : coe_fn lift (⇑f ∘ of) = f :=
  equiv.apply_symm_apply lift f

theorem comp_lift {α : Type u_1} {M : Type u_4} [monoid M] {N : Type u_5} [monoid N] (g : M →* N) (f : α → M) : monoid_hom.comp g (coe_fn lift f) = coe_fn lift (⇑g ∘ f) := sorry

theorem hom_map_lift {α : Type u_1} {M : Type u_4} [monoid M] {N : Type u_5} [monoid N] (g : M →* N) (f : α → M) (x : free_monoid α) : coe_fn g (coe_fn (coe_fn lift f) x) = coe_fn (coe_fn lift (⇑g ∘ f)) x :=
  iff.mp monoid_hom.ext_iff (comp_lift g f) x

/-- The unique monoid homomorphism `free_monoid α →* free_monoid β` that sends
each `of x` to `of (f x)`. -/
def map {α : Type u_1} {β : Type u_2} (f : α → β) : free_monoid α →* free_monoid β :=
  monoid_hom.mk (list.map f) sorry sorry

@[simp] theorem map_of {α : Type u_1} {β : Type u_2} (f : α → β) (x : α) : coe_fn (map f) (of x) = of (f x) :=
  rfl

theorem Mathlib.free_add_monoid.lift_of_comp_eq_map {α : Type u_1} {β : Type u_2} (f : α → β) : (coe_fn free_add_monoid.lift fun (x : α) => free_add_monoid.of (f x)) = free_add_monoid.map f :=
  free_add_monoid.hom_eq fun (x : α) => rfl

theorem map_comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} (g : β → γ) (f : α → β) : map (g ∘ f) = monoid_hom.comp (map g) (map f) :=
  hom_eq fun (x : α) => rfl

protected instance star_monoid {α : Type u_1} : star_monoid (free_monoid α) :=
  star_monoid.mk list.reverse_append

@[simp] theorem star_of {α : Type u_1} (x : α) : star (of x) = of x :=
  rfl

/-- Note that `star_one` is already a global simp lemma, but this one works with dsimp too -/
@[simp] theorem star_one {α : Type u_1} : star 1 = 1 :=
  rfl

