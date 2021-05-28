/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Simon Hudon
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.control.monad.basic
import Mathlib.data.fintype.basic
import Mathlib.PostPort

universes u_1 l u_2 

namespace Mathlib

/-!
Type class for finitely enumerable types. The property is stronger
than `fintype` in that it assigns each element a rank in a finite
enumeration.
-/

/-- `fin_enum α` means that `α` is finite and can be enumerated in some order,
  i.e. `α` has an explicit bijection with `fin n` for some n. -/
class fin_enum (α : Sort u_1) 
where
  card : ℕ
  equiv : α ≃ fin card
  dec_eq : DecidableEq α

namespace fin_enum


/-- transport a `fin_enum` instance across an equivalence -/
def of_equiv (α : Sort u_1) {β : Sort u_2} [fin_enum α] (h : β ≃ α) : fin_enum β :=
  mk (card α) (equiv.trans h (equiv α))

/-- create a `fin_enum` instance from an exhaustive list without duplicates -/
def of_nodup_list {α : Type u_1} [DecidableEq α] (xs : List α) (h : ∀ (x : α), x ∈ xs) (h' : list.nodup xs) : fin_enum α :=
  mk (list.length xs)
    (equiv.mk (fun (x : α) => { val := list.index_of x xs, property := sorry }) (fun (_x : fin (list.length xs)) => sorry)
      sorry sorry)

/-- create a `fin_enum` instance from an exhaustive list; duplicates are removed -/
def of_list {α : Type u_1} [DecidableEq α] (xs : List α) (h : ∀ (x : α), x ∈ xs) : fin_enum α :=
  of_nodup_list (list.erase_dup xs) sorry sorry

/-- create an exhaustive list of the values of a given type -/
def to_list (α : Type u_1) [fin_enum α] : List α :=
  list.map (⇑(equiv.symm (equiv α))) (list.fin_range (card α))

@[simp] theorem mem_to_list {α : Type u_1} [fin_enum α] (x : α) : x ∈ to_list α := sorry

@[simp] theorem nodup_to_list {α : Type u_1} [fin_enum α] : list.nodup (to_list α) := sorry

/-- create a `fin_enum` instance using a surjection -/
def of_surjective {α : Type u_1} {β : Type u_2} (f : β → α) [DecidableEq α] [fin_enum β] (h : function.surjective f) : fin_enum α :=
  of_list (list.map f (to_list β)) sorry

/-- create a `fin_enum` instance using an injection -/
def of_injective {α : Type u_1} {β : Type u_2} (f : α → β) [DecidableEq α] [fin_enum β] (h : function.injective f) : fin_enum α :=
  of_list (list.filter_map (function.partial_inv f) (to_list β)) sorry

protected instance pempty : fin_enum pempty :=
  of_list [] sorry

protected instance empty : fin_enum empty :=
  of_list [] sorry

protected instance punit : fin_enum PUnit :=
  of_list [PUnit.unit] sorry

protected instance prod {α : Type u_1} {β : Type u_2} [fin_enum α] [fin_enum β] : fin_enum (α × β) :=
  of_list (list.product (to_list α) (to_list β)) sorry

protected instance sum {α : Type u_1} {β : Type u_2} [fin_enum α] [fin_enum β] : fin_enum (α ⊕ β) :=
  of_list (list.map sum.inl (to_list α) ++ list.map sum.inr (to_list β)) sorry

protected instance fin {n : ℕ} : fin_enum (fin n) :=
  of_list (list.fin_range n) sorry

protected instance quotient.enum {α : Type u_1} [fin_enum α] (s : setoid α) [DecidableRel has_equiv.equiv] : fin_enum (quotient s) :=
  of_surjective quotient.mk sorry

/-- enumerate all finite sets of a given type -/
def finset.enum {α : Type u_1} [DecidableEq α] : List α → List (finset α) :=
  sorry

@[simp] theorem finset.mem_enum {α : Type u_1} [DecidableEq α] (s : finset α) (xs : List α) : s ∈ finset.enum xs ↔ ∀ (x : α), x ∈ s → x ∈ xs := sorry

protected instance finset.fin_enum {α : Type u_1} [fin_enum α] : fin_enum (finset α) :=
  of_list (finset.enum (to_list α)) sorry

protected instance subtype.fin_enum {α : Type u_1} [fin_enum α] (p : α → Prop) [decidable_pred p] : fin_enum (Subtype fun (x : α) => p x) :=
  of_list
    (list.filter_map
      (fun (x : α) => dite (p x) (fun (h : p x) => some { val := x, property := h }) fun (h : ¬p x) => none) (to_list α))
    sorry

protected instance sigma.fin_enum {α : Type u_1} (β : α → Type u_2) [fin_enum α] [(a : α) → fin_enum (β a)] : fin_enum (sigma β) :=
  of_list (list.bind (to_list α) fun (a : α) => list.map (sigma.mk a) (to_list (β a))) sorry

protected instance psigma.fin_enum {α : Type u_1} {β : α → Type u_2} [fin_enum α] [(a : α) → fin_enum (β a)] : fin_enum (psigma fun (a : α) => β a) :=
  of_equiv (sigma fun (i : α) => β i) (equiv.psigma_equiv_sigma fun (i : α) => β i)

protected instance psigma.fin_enum_prop_left {α : Prop} {β : α → Type u_1} [(a : α) → fin_enum (β a)] [Decidable α] : fin_enum (psigma fun (a : α) => β a) :=
  dite α (fun (h : α) => of_list (list.map (psigma.mk h) (to_list (β h))) sorry) fun (h : ¬α) => of_list [] sorry

protected instance psigma.fin_enum_prop_right {α : Type u_1} {β : α → Prop} [fin_enum α] [(a : α) → Decidable (β a)] : fin_enum (psigma fun (a : α) => β a) :=
  of_equiv (Subtype fun (a : α) => β a)
    (equiv.mk (fun (_x : psigma fun (a : α) => β a) => sorry) (fun (_x : Subtype fun (a : α) => β a) => sorry) sorry
      sorry)

protected instance psigma.fin_enum_prop_prop {α : Prop} {β : α → Prop} [Decidable α] [(a : α) → Decidable (β a)] : fin_enum (psigma fun (a : α) => β a) :=
  dite (∃ (a : α), β a) (fun (h : ∃ (a : α), β a) => of_list [psigma.mk sorry sorry] sorry)
    fun (h : ¬∃ (a : α), β a) => of_list [] sorry

protected instance fintype {α : Type u_1} [fin_enum α] : fintype α :=
  fintype.mk (finset.map (equiv.to_embedding (equiv.symm (equiv α))) finset.univ) sorry

/-- For `pi.cons x xs y f` create a function where every `i ∈ xs` is mapped to `f i` and
`x` is mapped to `y`  -/
def pi.cons {α : Type u_1} {β : α → Type u_2} [DecidableEq α] (x : α) (xs : List α) (y : β x) (f : (a : α) → a ∈ xs → β a) (a : α) : a ∈ x :: xs → β a :=
  sorry

/-- Given `f` a function whose domain is `x :: xs`, produce a function whose domain
is restricted to `xs`.  -/
def pi.tail {α : Type u_1} {β : α → Type u_2} {x : α} {xs : List α} (f : (a : α) → a ∈ x :: xs → β a) (a : α) : a ∈ xs → β a :=
  sorry

/-- `pi xs f` creates the list of functions `g` such that, for `x ∈ xs`, `g x ∈ f x` -/
def pi {α : Type u_1} {β : α → Type (max u_1 u_2)} [DecidableEq α] (xs : List α) : ((a : α) → List (β a)) → List ((a : α) → a ∈ xs → β a) :=
  sorry

theorem mem_pi {α : Type u_1} {β : α → Type (max u_1 u_2)} [fin_enum α] [(a : α) → fin_enum (β a)] (xs : List α) (f : (a : α) → a ∈ xs → β a) : f ∈ pi xs fun (x : α) => to_list (β x) := sorry

/-- enumerate all functions whose domain and range are finitely enumerable -/
def pi.enum {α : Type u_1} (β : α → Type (max u_1 u_2)) [fin_enum α] [(a : α) → fin_enum (β a)] : List ((a : α) → β a) :=
  list.map (fun (f : (a : α) → a ∈ to_list α → β a) (x : α) => f x (mem_to_list x))
    (pi (to_list α) fun (x : α) => to_list (β x))

theorem pi.mem_enum {α : Type u_1} {β : α → Type (max u_1 u_2)} [fin_enum α] [(a : α) → fin_enum (β a)] (f : (a : α) → β a) : f ∈ pi.enum β := sorry

protected instance pi.fin_enum {α : Type u_1} {β : α → Type (max u_1 u_2)} [fin_enum α] [(a : α) → fin_enum (β a)] : fin_enum ((a : α) → β a) :=
  of_list (pi.enum fun (a : α) => β a) sorry

protected instance pfun_fin_enum (p : Prop) [Decidable p] (α : p → Type u_1) [(hp : p) → fin_enum (α hp)] : fin_enum ((hp : p) → α hp) :=
  dite p (fun (hp : p) => of_list (list.map (fun (x : α hp) (hp' : p) => x) (to_list (α hp))) sorry)
    fun (hp : ¬p) => of_list [fun (hp' : p) => false.elim (hp hp')] sorry

