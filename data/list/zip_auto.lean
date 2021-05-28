/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.list.basic
import PostPort

universes u v w z u_1 u_2 u_3 

namespace Mathlib

namespace list


/- zip & unzip -/

@[simp] theorem zip_with_cons_cons {α : Type u} {β : Type v} {γ : Type w} (f : α → β → γ) (a : α) (b : β) (l₁ : List α) (l₂ : List β) : zip_with f (a :: l₁) (b :: l₂) = f a b :: zip_with f l₁ l₂ :=
  rfl

@[simp] theorem zip_cons_cons {α : Type u} {β : Type v} (a : α) (b : β) (l₁ : List α) (l₂ : List β) : zip (a :: l₁) (b :: l₂) = (a, b) :: zip l₁ l₂ :=
  rfl

@[simp] theorem zip_with_nil_left {α : Type u} {β : Type v} {γ : Type w} (f : α → β → γ) (l : List β) : zip_with f [] l = [] :=
  rfl

@[simp] theorem zip_with_nil_right {α : Type u} {β : Type v} {γ : Type w} (f : α → β → γ) (l : List α) : zip_with f l [] = [] :=
  list.cases_on l (Eq.refl (zip_with f [] [])) fun (l_hd : α) (l_tl : List α) => Eq.refl (zip_with f (l_hd :: l_tl) [])

@[simp] theorem zip_nil_left {α : Type u} {β : Type v} (l : List α) : zip [] l = [] :=
  rfl

@[simp] theorem zip_nil_right {α : Type u} {β : Type v} (l : List α) : zip l [] = [] :=
  zip_with_nil_right Prod.mk l

@[simp] theorem zip_swap {α : Type u} {β : Type v} (l₁ : List α) (l₂ : List β) : map prod.swap (zip l₁ l₂) = zip l₂ l₁ := sorry

@[simp] theorem length_zip_with {α : Type u} {β : Type v} {γ : Type w} (f : α → β → γ) (l₁ : List α) (l₂ : List β) : length (zip_with f l₁ l₂) = min (length l₁) (length l₂) := sorry

@[simp] theorem length_zip {α : Type u} {β : Type v} (l₁ : List α) (l₂ : List β) : length (zip l₁ l₂) = min (length l₁) (length l₂) :=
  length_zip_with Prod.mk

theorem lt_length_left_of_zip_with {α : Type u} {β : Type v} {γ : Type w} {f : α → β → γ} {i : ℕ} {l : List α} {l' : List β} (h : i < length (zip_with f l l')) : i < length l :=
  and.left
    (eq.mp (Eq._oldrec (Eq.refl (i < min (length l) (length l'))) (propext lt_min_iff))
      (eq.mp (Eq._oldrec (Eq.refl (i < length (zip_with f l l'))) (length_zip_with f l l')) h))

theorem lt_length_right_of_zip_with {α : Type u} {β : Type v} {γ : Type w} {f : α → β → γ} {i : ℕ} {l : List α} {l' : List β} (h : i < length (zip_with f l l')) : i < length l' :=
  and.right
    (eq.mp (Eq._oldrec (Eq.refl (i < min (length l) (length l'))) (propext lt_min_iff))
      (eq.mp (Eq._oldrec (Eq.refl (i < length (zip_with f l l'))) (length_zip_with f l l')) h))

theorem lt_length_left_of_zip {α : Type u} {β : Type v} {i : ℕ} {l : List α} {l' : List β} (h : i < length (zip l l')) : i < length l :=
  lt_length_left_of_zip_with h

theorem lt_length_right_of_zip {α : Type u} {β : Type v} {i : ℕ} {l : List α} {l' : List β} (h : i < length (zip l l')) : i < length l' :=
  lt_length_right_of_zip_with h

theorem zip_append {α : Type u} {β : Type v} {l₁ : List α} {r₁ : List α} {l₂ : List β} {r₂ : List β} (h : length l₁ = length l₂) : zip (l₁ ++ r₁) (l₂ ++ r₂) = zip l₁ l₂ ++ zip r₁ r₂ := sorry

theorem zip_map {α : Type u} {β : Type v} {γ : Type w} {δ : Type z} (f : α → γ) (g : β → δ) (l₁ : List α) (l₂ : List β) : zip (map f l₁) (map g l₂) = map (prod.map f g) (zip l₁ l₂) := sorry

theorem zip_map_left {α : Type u} {β : Type v} {γ : Type w} (f : α → γ) (l₁ : List α) (l₂ : List β) : zip (map f l₁) l₂ = map (prod.map f id) (zip l₁ l₂) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (zip (map f l₁) l₂ = map (prod.map f id) (zip l₁ l₂))) (Eq.symm (zip_map f id l₁ l₂))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (zip (map f l₁) l₂ = zip (map f l₁) (map id l₂))) (map_id l₂)))
      (Eq.refl (zip (map f l₁) l₂)))

theorem zip_map_right {α : Type u} {β : Type v} {γ : Type w} (f : β → γ) (l₁ : List α) (l₂ : List β) : zip l₁ (map f l₂) = map (prod.map id f) (zip l₁ l₂) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (zip l₁ (map f l₂) = map (prod.map id f) (zip l₁ l₂))) (Eq.symm (zip_map id f l₁ l₂))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (zip l₁ (map f l₂) = zip (map id l₁) (map f l₂))) (map_id l₁)))
      (Eq.refl (zip l₁ (map f l₂))))

theorem zip_map' {α : Type u} {β : Type v} {γ : Type w} (f : α → β) (g : α → γ) (l : List α) : zip (map f l) (map g l) = map (fun (a : α) => (f a, g a)) l := sorry

theorem mem_zip {α : Type u} {β : Type v} {a : α} {b : β} {l₁ : List α} {l₂ : List β} : (a, b) ∈ zip l₁ l₂ → a ∈ l₁ ∧ b ∈ l₂ := sorry

theorem map_fst_zip {α : Type u} {β : Type v} (l₁ : List α) (l₂ : List β) : length l₁ ≤ length l₂ → map prod.fst (zip l₁ l₂) = l₁ := sorry

theorem map_snd_zip {α : Type u} {β : Type v} (l₁ : List α) (l₂ : List β) : length l₂ ≤ length l₁ → map prod.snd (zip l₁ l₂) = l₂ := sorry

@[simp] theorem unzip_nil {α : Type u} {β : Type v} : unzip [] = ([], []) :=
  rfl

@[simp] theorem unzip_cons {α : Type u} {β : Type v} (a : α) (b : β) (l : List (α × β)) : unzip ((a, b) :: l) = (a :: prod.fst (unzip l), b :: prod.snd (unzip l)) := sorry

theorem unzip_eq_map {α : Type u} {β : Type v} (l : List (α × β)) : unzip l = (map prod.fst l, map prod.snd l) := sorry

theorem unzip_left {α : Type u} {β : Type v} (l : List (α × β)) : prod.fst (unzip l) = map prod.fst l := sorry

theorem unzip_right {α : Type u} {β : Type v} (l : List (α × β)) : prod.snd (unzip l) = map prod.snd l := sorry

theorem unzip_swap {α : Type u} {β : Type v} (l : List (α × β)) : unzip (map prod.swap l) = prod.swap (unzip l) := sorry

theorem zip_unzip {α : Type u} {β : Type v} (l : List (α × β)) : zip (prod.fst (unzip l)) (prod.snd (unzip l)) = l := sorry

theorem unzip_zip_left {α : Type u} {β : Type v} {l₁ : List α} {l₂ : List β} : length l₁ ≤ length l₂ → prod.fst (unzip (zip l₁ l₂)) = l₁ := sorry

theorem unzip_zip_right {α : Type u} {β : Type v} {l₁ : List α} {l₂ : List β} (h : length l₂ ≤ length l₁) : prod.snd (unzip (zip l₁ l₂)) = l₂ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (prod.snd (unzip (zip l₁ l₂)) = l₂)) (Eq.symm (zip_swap l₂ l₁))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (prod.snd (unzip (map prod.swap (zip l₂ l₁))) = l₂)) (unzip_swap (zip l₂ l₁))))
      (unzip_zip_left h))

theorem unzip_zip {α : Type u} {β : Type v} {l₁ : List α} {l₂ : List β} (h : length l₁ = length l₂) : unzip (zip l₁ l₂) = (l₁, l₂) := sorry

theorem zip_of_prod {α : Type u} {β : Type v} {l : List α} {l' : List β} {lp : List (α × β)} (hl : map prod.fst lp = l) (hr : map prod.snd lp = l') : lp = zip l l' := sorry

theorem map_prod_left_eq_zip {α : Type u} {β : Type v} {l : List α} (f : α → β) : map (fun (x : α) => (x, f x)) l = zip l (map f l) := sorry

theorem map_prod_right_eq_zip {α : Type u} {β : Type v} {l : List α} (f : α → β) : map (fun (x : α) => (f x, x)) l = zip (map f l) l := sorry

@[simp] theorem length_revzip {α : Type u} (l : List α) : length (revzip l) = length l := sorry

@[simp] theorem unzip_revzip {α : Type u} (l : List α) : unzip (revzip l) = (l, reverse l) :=
  unzip_zip (Eq.symm (length_reverse l))

@[simp] theorem revzip_map_fst {α : Type u} (l : List α) : map prod.fst (revzip l) = l :=
  eq.mpr (id (Eq._oldrec (Eq.refl (map prod.fst (revzip l) = l)) (Eq.symm (unzip_left (revzip l)))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (prod.fst (unzip (revzip l)) = l)) (unzip_revzip l)))
      (Eq.refl (prod.fst (l, reverse l))))

@[simp] theorem revzip_map_snd {α : Type u} (l : List α) : map prod.snd (revzip l) = reverse l :=
  eq.mpr (id (Eq._oldrec (Eq.refl (map prod.snd (revzip l) = reverse l)) (Eq.symm (unzip_right (revzip l)))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (prod.snd (unzip (revzip l)) = reverse l)) (unzip_revzip l)))
      (Eq.refl (prod.snd (l, reverse l))))

theorem reverse_revzip {α : Type u} (l : List α) : reverse (revzip l) = revzip (reverse l) := sorry

theorem revzip_swap {α : Type u} (l : List α) : map prod.swap (revzip l) = revzip (reverse l) := sorry

theorem nth_zip_with {α : Type u_1} {β : Type u_1} {γ : Type u_1} (f : α → β → γ) (l₁ : List α) (l₂ : List β) (i : ℕ) : nth (zip_with f l₁ l₂) i = f <$> nth l₁ i <*> nth l₂ i := sorry

theorem nth_zip_with_eq_some {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : α → β → γ) (l₁ : List α) (l₂ : List β) (z : γ) (i : ℕ) : nth (zip_with f l₁ l₂) i = some z ↔ ∃ (x : α), ∃ (y : β), nth l₁ i = some x ∧ nth l₂ i = some y ∧ f x y = z := sorry

theorem nth_zip_eq_some {α : Type u} {β : Type v} (l₁ : List α) (l₂ : List β) (z : α × β) (i : ℕ) : nth (zip l₁ l₂) i = some z ↔ nth l₁ i = some (prod.fst z) ∧ nth l₂ i = some (prod.snd z) := sorry

@[simp] theorem nth_le_zip_with {α : Type u} {β : Type v} {γ : Type w} {f : α → β → γ} {l : List α} {l' : List β} {i : ℕ} {h : i < length (zip_with f l l')} : nth_le (zip_with f l l') i h =
  f (nth_le l i (lt_length_left_of_zip_with h)) (nth_le l' i (lt_length_right_of_zip_with h)) := sorry

@[simp] theorem nth_le_zip {α : Type u} {β : Type v} {l : List α} {l' : List β} {i : ℕ} {h : i < length (zip l l')} : nth_le (zip l l') i h = (nth_le l i (lt_length_left_of_zip h), nth_le l' i (lt_length_right_of_zip h)) :=
  nth_le_zip_with

theorem mem_zip_inits_tails {α : Type u} {l : List α} {init : List α} {tail : List α} : (init, tail) ∈ zip (inits l) (tails l) ↔ init ++ tail = l := sorry

