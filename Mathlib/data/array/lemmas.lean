/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.control.traversable.equiv
import Mathlib.data.vector2
import Mathlib.PostPort

universes u u_1 w v 

namespace Mathlib

namespace d_array


protected instance inhabited {n : ℕ} {α : fin n → Type u} [(i : fin n) → Inhabited (α i)] : Inhabited (d_array n α) :=
  { default := mk fun (_x : fin n) => Inhabited.default }

end d_array


namespace array


protected instance inhabited {n : ℕ} {α : Type u_1} [Inhabited α] : Inhabited (array n α) :=
  d_array.inhabited

theorem to_list_of_heq {n₁ : ℕ} {n₂ : ℕ} {α : Type u_1} {a₁ : array n₁ α} {a₂ : array n₂ α} (hn : n₁ = n₂) (ha : a₁ == a₂) : to_list a₁ = to_list a₂ := sorry

/- rev_list -/

theorem rev_list_reverse_aux {n : ℕ} {α : Type u} {a : array n α} (i : ℕ) (h : i ≤ n) (t : List α) : list.reverse_core (d_array.iterate_aux a (fun (_x : fin n) (_x : α) (_y : List α) => _x :: _y) i h []) t =
  d_array.rev_iterate_aux a (fun (_x : fin n) (_x : α) (_y : List α) => _x :: _y) i h t := sorry

@[simp] theorem rev_list_reverse {n : ℕ} {α : Type u} {a : array n α} : list.reverse (rev_list a) = to_list a :=
  rev_list_reverse_aux n d_array.iterate._proof_1 []

@[simp] theorem to_list_reverse {n : ℕ} {α : Type u} {a : array n α} : list.reverse (to_list a) = rev_list a := sorry

/- mem -/

theorem mem.def {n : ℕ} {α : Type u} {v : α} {a : array n α} : v ∈ a ↔ ∃ (i : fin n), read a i = v :=
  iff.rfl

theorem mem_rev_list_aux {n : ℕ} {α : Type u} {v : α} {a : array n α} {i : ℕ} (h : i ≤ n) : (∃ (j : fin n), ↑j < i ∧ read a j = v) ↔
  v ∈ d_array.iterate_aux a (fun (_x : fin n) (_x : α) (_y : List α) => _x :: _y) i h [] := sorry

@[simp] theorem mem_rev_list {n : ℕ} {α : Type u} {v : α} {a : array n α} : v ∈ rev_list a ↔ v ∈ a := sorry

@[simp] theorem mem_to_list {n : ℕ} {α : Type u} {v : α} {a : array n α} : v ∈ to_list a ↔ v ∈ a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (v ∈ to_list a ↔ v ∈ a)) (Eq.symm rev_list_reverse)))
    (iff.trans list.mem_reverse mem_rev_list)

/- foldr -/

theorem rev_list_foldr_aux {n : ℕ} {α : Type u} {β : Type w} {b : β} {f : α → β → β} {a : array n α} {i : ℕ} (h : i ≤ n) : list.foldr f b (d_array.iterate_aux a (fun (_x : fin n) (_x : α) (_y : List α) => _x :: _y) i h []) =
  d_array.iterate_aux a (fun (_x : fin n) => f) i h b := sorry

theorem rev_list_foldr {n : ℕ} {α : Type u} {β : Type w} {b : β} {f : α → β → β} {a : array n α} : list.foldr f b (rev_list a) = foldl a b f :=
  rev_list_foldr_aux d_array.iterate._proof_1

/- foldl -/

theorem to_list_foldl {n : ℕ} {α : Type u} {β : Type w} {b : β} {f : β → α → β} {a : array n α} : list.foldl f b (to_list a) = foldl a b (function.swap f) := sorry

/- length -/

theorem rev_list_length_aux {n : ℕ} {α : Type u} (a : array n α) (i : ℕ) (h : i ≤ n) : list.length (d_array.iterate_aux a (fun (_x : fin n) (_x : α) (_y : List α) => _x :: _y) i h []) = i := sorry

@[simp] theorem rev_list_length {n : ℕ} {α : Type u} (a : array n α) : list.length (rev_list a) = n :=
  rev_list_length_aux a n d_array.iterate._proof_1

@[simp] theorem to_list_length {n : ℕ} {α : Type u} (a : array n α) : list.length (to_list a) = n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (list.length (to_list a) = n)) (Eq.symm rev_list_reverse)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (list.length (list.reverse (rev_list a)) = n)) (list.length_reverse (rev_list a))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (list.length (rev_list a) = n)) (rev_list_length a))) (Eq.refl n)))

/- nth -/

theorem to_list_nth_le_aux {n : ℕ} {α : Type u} {a : array n α} (i : ℕ) (ih : i < n) (j : ℕ) {jh : j ≤ n} {t : List α} {h' : i < list.length (d_array.rev_iterate_aux a (fun (_x : fin n) (_x : α) (_y : List α) => _x :: _y) j jh t)} : (∀ (k : ℕ) (tl : k < list.length t), j + k = i → list.nth_le t k tl = read a { val := i, property := ih }) →
  list.nth_le (d_array.rev_iterate_aux a (fun (_x : fin n) (_x : α) (_y : List α) => _x :: _y) j jh t) i h' =
    read a { val := i, property := ih } := sorry

theorem to_list_nth_le {n : ℕ} {α : Type u} {a : array n α} (i : ℕ) (h : i < n) (h' : i < list.length (to_list a)) : list.nth_le (to_list a) i h' = read a { val := i, property := h } :=
  to_list_nth_le_aux i h n fun (k : ℕ) (tl : k < list.length []) => absurd tl (nat.not_lt_zero k)

@[simp] theorem to_list_nth_le' {n : ℕ} {α : Type u} (a : array n α) (i : fin n) (h' : ↑i < list.length (to_list a)) : list.nth_le (to_list a) (↑i) h' = read a i := sorry

theorem to_list_nth {n : ℕ} {α : Type u} {a : array n α} {i : ℕ} {v : α} : list.nth (to_list a) i = some v ↔ ∃ (h : i < n), read a { val := i, property := h } = v := sorry

theorem write_to_list {n : ℕ} {α : Type u} {a : array n α} {i : fin n} {v : α} : to_list (write a i v) = list.update_nth (to_list a) (↑i) v := sorry

/- enum -/

theorem mem_to_list_enum {n : ℕ} {α : Type u} {a : array n α} {i : ℕ} {v : α} : (i, v) ∈ list.enum (to_list a) ↔ ∃ (h : i < n), read a { val := i, property := h } = v := sorry

/- to_array -/

@[simp] theorem to_list_to_array {n : ℕ} {α : Type u} (a : array n α) : list.to_array (to_list a) == a := sorry

@[simp] theorem to_array_to_list {α : Type u} (l : List α) : to_list (list.to_array l) = l :=
  list.ext_le (to_list_length (list.to_array l))
    fun (n : ℕ) (h1 : n < list.length (to_list (list.to_array l))) (h2 : n < list.length l) => to_list_nth_le n h2 h1

/- push_back -/

theorem push_back_rev_list_aux {n : ℕ} {α : Type u} {v : α} {a : array n α} (i : ℕ) (h : i ≤ n + 1) (h' : i ≤ n) : d_array.iterate_aux (push_back a v) (fun (_x : fin (n + 1)) (_x : α) (_y : List α) => _x :: _y) i h [] =
  d_array.iterate_aux a (fun (_x : fin n) (_x : α) (_y : List α) => _x :: _y) i h' [] := sorry

@[simp] theorem push_back_rev_list {n : ℕ} {α : Type u} {v : α} {a : array n α} : rev_list (push_back a v) = v :: rev_list a := sorry

@[simp] theorem push_back_to_list {n : ℕ} {α : Type u} {v : α} {a : array n α} : to_list (push_back a v) = to_list a ++ [v] := sorry

/- foreach -/

@[simp] theorem read_foreach {n : ℕ} {α : Type u} {β : Type v} {i : fin n} {f : fin n → α → β} {a : array n α} : read (foreach a f) i = f i (read a i) :=
  rfl

/- map -/

theorem read_map {n : ℕ} {α : Type u} {β : Type v} {i : fin n} {f : α → β} {a : array n α} : read (map a f) i = f (read a i) :=
  read_foreach

/- map₂ -/

@[simp] theorem read_map₂ {n : ℕ} {α : Type u} {i : fin n} {f : α → α → α} {a₁ : array n α} {a₂ : array n α} : read (map₂ f a₁ a₂) i = f (read a₁ i) (read a₂ i) :=
  read_foreach

end array


namespace equiv


/-- The natural equivalence between length-`n` heterogeneous arrays
and dependent functions from `fin n`. -/
def d_array_equiv_fin {n : ℕ} (α : fin n → Type u_1) : d_array n α ≃ ((i : fin n) → α i) :=
  mk d_array.read d_array.mk sorry sorry

/-- The natural equivalence between length-`n` arrays and functions from `fin n`. -/
def array_equiv_fin (n : ℕ) (α : Type u_1) : array n α ≃ (fin n → α) :=
  d_array_equiv_fin fun (_x : fin n) => α

/-- The natural equivalence between length-`n` vectors and functions from `fin n`. -/
def vector_equiv_fin (α : Type u_1) (n : ℕ) : vector α n ≃ (fin n → α) :=
  mk vector.nth vector.of_fn vector.of_fn_nth sorry

/-- The natural equivalence between length-`n` vectors and length-`n` arrays. -/
def vector_equiv_array (α : Type u_1) (n : ℕ) : vector α n ≃ array n α :=
  equiv.trans (vector_equiv_fin α n) (equiv.symm (array_equiv_fin n α))

end equiv


namespace array


protected instance traversable {n : ℕ} : traversable (array n) :=
  equiv.traversable fun (α : Type u_1) => equiv.vector_equiv_array α n

protected instance is_lawful_traversable {n : ℕ} : is_lawful_traversable (array n) :=
  equiv.is_lawful_traversable fun (α : Type u_1) => equiv.vector_equiv_array α n

