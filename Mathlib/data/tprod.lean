/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.list.nodup
import Mathlib.PostPort

universes u_1 u_2 u_3 

namespace Mathlib

/-!
# Finite products of types

This file defines the product of types over a list. For `l : list ι` and `α : ι → Type*` we define
`list.tprod α l = l.foldr (λ i β, α i × β) punit`.
This type should not be used if `Π i, α i` or `Π i ∈ l, α i` can be used instead
(in the last expression, we could also replace the list `l` by a set or a finset).
This type is used as an intermediary between binary products and finitary products.
The application of this type is finitary product measures, but it could be used in any
construction/theorem that is easier to define/prove on binary products than on finitary products.

* Once we have the construction on binary products (like binary product measures in
  `measure_theory.prod`), we can easily define a finitary version on the type `tprod l α`
  by iterating. Properties can also be easily extended from the binary case to the finitary case
  by iterating.
* Then we can use the equivalence `list.tprod.pi_equiv_tprod` below (or enhanced versions of it,
  like a `measurable_equiv` for product measures) to get the construction on `Π i : ι, α i`, at
  least when assuming `[fintype ι] [encodable ι]` (using `encodable.sorted_univ`).
  Using `local attribute [instance] fintype.encodable` we can get rid of the argument
  `[encodable ι]`.

## Main definitions

* We have the equivalence `tprod.pi_equiv_tprod : (Π i, α i) ≃ tprod α l`
  if `l` contains every element of `ι` exactly once.
* The product of sets is `set.tprod : (Π i, set (α i)) → set (tprod α l)`.
-/

namespace list


/-- The product of a family of types over a list. -/
def tprod {ι : Type u_1} (α : ι → Type u_2) (l : List ι)  :=
  foldr (fun (i : ι) (β : Type (max u_2 u_3)) => α i × β) PUnit l

namespace tprod


/-- Turning a function `f : Π i, α i` into an element of the iterated product `tprod α l`. -/
protected def mk {ι : Type u_1} {α : ι → Type u_2} (l : List ι) (f : (i : ι) → α i) : tprod α l :=
  sorry

protected instance inhabited {ι : Type u_1} {α : ι → Type u_2} {l : List ι} [(i : ι) → Inhabited (α i)] : Inhabited (tprod α l) :=
  { default := tprod.mk l fun (i : ι) => Inhabited.default }

@[simp] theorem fst_mk {ι : Type u_1} {α : ι → Type u_2} (i : ι) (l : List ι) (f : (i : ι) → α i) : prod.fst (tprod.mk (i :: l) f) = f i :=
  rfl

@[simp] theorem snd_mk {ι : Type u_1} {α : ι → Type u_2} (i : ι) (l : List ι) (f : (i : ι) → α i) : prod.snd (tprod.mk (i :: l) f) = tprod.mk l f :=
  rfl

/-- Given an element of the iterated product `l.prod α`, take a projection into direction `i`.
  If `i` appears multiple times in `l`, this chooses the first component in direction `i`. -/
protected def elim {ι : Type u_1} {α : ι → Type u_2} [DecidableEq ι] {l : List ι} (v : tprod α l) {i : ι} (hi : i ∈ l) : α i :=
  sorry

@[simp] theorem elim_self {ι : Type u_1} {α : ι → Type u_2} {i : ι} {l : List ι} [DecidableEq ι] (v : tprod α (i :: l)) : tprod.elim v (mem_cons_self i l) = prod.fst v := sorry

@[simp] theorem elim_of_ne {ι : Type u_1} {α : ι → Type u_2} {i : ι} {j : ι} {l : List ι} [DecidableEq ι] (hj : j ∈ i :: l) (hji : j ≠ i) (v : tprod α (i :: l)) : tprod.elim v hj = tprod.elim (prod.snd v) (or.resolve_left hj hji) := sorry

@[simp] theorem elim_of_mem {ι : Type u_1} {α : ι → Type u_2} {i : ι} {j : ι} {l : List ι} [DecidableEq ι] (hl : nodup (i :: l)) (hj : j ∈ l) (v : tprod α (i :: l)) : tprod.elim v (mem_cons_of_mem i hj) = tprod.elim (prod.snd v) hj := sorry

theorem elim_mk {ι : Type u_1} {α : ι → Type u_2} [DecidableEq ι] (l : List ι) (f : (i : ι) → α i) {i : ι} (hi : i ∈ l) : tprod.elim (tprod.mk l f) hi = f i := sorry

theorem ext {ι : Type u_1} {α : ι → Type u_2} [DecidableEq ι] {l : List ι} (hl : nodup l) {v : tprod α l} {w : tprod α l} (hvw : ∀ (i : ι) (hi : i ∈ l), tprod.elim v hi = tprod.elim w hi) : v = w := sorry

/-- A version of `tprod.elim` when `l` contains all elements. In this case we get a function into
  `Π i, α i`. -/
@[simp] protected def elim' {ι : Type u_1} {α : ι → Type u_2} {l : List ι} [DecidableEq ι] (h : ∀ (i : ι), i ∈ l) (v : tprod α l) (i : ι) : α i :=
  tprod.elim v (h i)

theorem mk_elim {ι : Type u_1} {α : ι → Type u_2} {l : List ι} [DecidableEq ι] (hnd : nodup l) (h : ∀ (i : ι), i ∈ l) (v : tprod α l) : tprod.mk l (tprod.elim' h v) = v := sorry

/-- Pi-types are equivalent to iterated products. -/
def pi_equiv_tprod {ι : Type u_1} {α : ι → Type u_2} {l : List ι} [DecidableEq ι] (hnd : nodup l) (h : ∀ (i : ι), i ∈ l) : ((i : ι) → α i) ≃ tprod α l :=
  equiv.mk (tprod.mk l) (tprod.elim' h) sorry sorry

end tprod


end list


namespace set


/-- A product of sets in `tprod α l`. -/
@[simp] protected def tprod {ι : Type u_1} {α : ι → Type u_2} (l : List ι) (t : (i : ι) → set (α i)) : set (list.tprod α l) :=
  sorry

theorem mk_preimage_tprod {ι : Type u_1} {α : ι → Type u_2} (l : List ι) (t : (i : ι) → set (α i)) : list.tprod.mk l ⁻¹' set.tprod l t = pi (set_of fun (i : ι) => i ∈ l) t := sorry

theorem elim_preimage_pi {ι : Type u_1} {α : ι → Type u_2} [DecidableEq ι] {l : List ι} (hnd : list.nodup l) (h : ∀ (i : ι), i ∈ l) (t : (i : ι) → set (α i)) : list.tprod.elim' h ⁻¹' pi univ t = set.tprod l t := sorry

