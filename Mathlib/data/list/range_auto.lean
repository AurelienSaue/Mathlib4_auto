/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau, Scott Morrison
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.list.chain
import Mathlib.data.list.nodup
import Mathlib.data.list.of_fn
import Mathlib.data.list.zip
import PostPort

universes u u_1 

namespace Mathlib

namespace list


/- iota and range(') -/

@[simp] theorem length_range' (s : ℕ) (n : ℕ) : length (range' s n) = n := sorry

@[simp] theorem range'_eq_nil {s : ℕ} {n : ℕ} : range' s n = [] ↔ n = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (range' s n = [] ↔ n = 0)) (Eq.symm (propext length_eq_zero))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (length (range' s n) = 0 ↔ n = 0)) (length_range' s n))) (iff.refl (n = 0)))

@[simp] theorem mem_range' {m : ℕ} {s : ℕ} {n : ℕ} : m ∈ range' s n ↔ s ≤ m ∧ m < s + n := sorry

theorem map_add_range' (a : ℕ) (s : ℕ) (n : ℕ) : map (Add.add a) (range' s n) = range' (a + s) n := sorry

theorem map_sub_range' (a : ℕ) (s : ℕ) (n : ℕ) (h : a ≤ s) : map (fun (x : ℕ) => x - a) (range' s n) = range' (s - a) n := sorry

theorem chain_succ_range' (s : ℕ) (n : ℕ) : chain (fun (a b : ℕ) => b = Nat.succ a) s (range' (s + 1) n) := sorry

theorem chain_lt_range' (s : ℕ) (n : ℕ) : chain Less s (range' (s + 1) n) :=
  chain.imp (fun (a b : ℕ) (e : b = Nat.succ a) => Eq.symm e ▸ nat.lt_succ_self a) (chain_succ_range' s n)

theorem pairwise_lt_range' (s : ℕ) (n : ℕ) : pairwise Less (range' s n) := sorry

theorem nodup_range' (s : ℕ) (n : ℕ) : nodup (range' s n) :=
  pairwise.imp (fun (a b : ℕ) => ne_of_lt) (pairwise_lt_range' s n)

@[simp] theorem range'_append (s : ℕ) (m : ℕ) (n : ℕ) : range' s m ++ range' (s + m) n = range' s (n + m) := sorry

theorem range'_sublist_right {s : ℕ} {m : ℕ} {n : ℕ} : range' s m <+ range' s n ↔ m ≤ n := sorry

theorem range'_subset_right {s : ℕ} {m : ℕ} {n : ℕ} : range' s m ⊆ range' s n ↔ m ≤ n := sorry

theorem nth_range' (s : ℕ) {m : ℕ} {n : ℕ} : m < n → nth (range' s n) m = some (s + m) := sorry

@[simp] theorem nth_le_range' {n : ℕ} {m : ℕ} (i : ℕ) (H : i < length (range' n m)) : nth_le (range' n m) i H = n + i := sorry

theorem range'_concat (s : ℕ) (n : ℕ) : range' s (n + 1) = range' s n ++ [s + n] :=
  eq.mpr (id (Eq._oldrec (Eq.refl (range' s (n + 1) = range' s n ++ [s + n])) (add_comm n 1)))
    (Eq.symm (range'_append s n 1))

theorem range_core_range' (s : ℕ) (n : ℕ) : range_core s (range' s n) = range' 0 (n + s) := sorry

theorem range_eq_range' (n : ℕ) : range n = range' 0 n :=
  Eq.trans (range_core_range' n 0)
    (eq.mpr (id (Eq._oldrec (Eq.refl (range' 0 (0 + n) = range' 0 n)) (zero_add n))) (Eq.refl (range' 0 n)))

theorem range_succ_eq_map (n : ℕ) : range (n + 1) = 0 :: map Nat.succ (range n) := sorry

theorem range'_eq_map_range (s : ℕ) (n : ℕ) : range' s n = map (Add.add s) (range n) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (range' s n = map (Add.add s) (range n))) (range_eq_range' n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (range' s n = map (Add.add s) (range' 0 n))) (map_add_range' s 0 n)))
      (Eq.refl (range' s n)))

@[simp] theorem length_range (n : ℕ) : length (range n) = n := sorry

@[simp] theorem range_eq_nil {n : ℕ} : range n = [] ↔ n = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (range n = [] ↔ n = 0)) (Eq.symm (propext length_eq_zero))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (length (range n) = 0 ↔ n = 0)) (length_range n))) (iff.refl (n = 0)))

theorem pairwise_lt_range (n : ℕ) : pairwise Less (range n) := sorry

theorem nodup_range (n : ℕ) : nodup (range n) := sorry

theorem range_sublist {m : ℕ} {n : ℕ} : range m <+ range n ↔ m ≤ n := sorry

theorem range_subset {m : ℕ} {n : ℕ} : range m ⊆ range n ↔ m ≤ n := sorry

@[simp] theorem mem_range {m : ℕ} {n : ℕ} : m ∈ range n ↔ m < n := sorry

@[simp] theorem not_mem_range_self {n : ℕ} : ¬n ∈ range n :=
  mt (iff.mp mem_range) (lt_irrefl n)

@[simp] theorem self_mem_range_succ (n : ℕ) : n ∈ range (n + 1) := sorry

theorem nth_range {m : ℕ} {n : ℕ} (h : m < n) : nth (range n) m = some m := sorry

theorem range_succ (n : ℕ) : range (Nat.succ n) = range n ++ [n] := sorry

@[simp] theorem range_zero : range 0 = [] :=
  rfl

theorem iota_eq_reverse_range' (n : ℕ) : iota n = reverse (range' 1 n) := sorry

@[simp] theorem length_iota (n : ℕ) : length (iota n) = n := sorry

theorem pairwise_gt_iota (n : ℕ) : pairwise gt (iota n) := sorry

theorem nodup_iota (n : ℕ) : nodup (iota n) := sorry

theorem mem_iota {m : ℕ} {n : ℕ} : m ∈ iota n ↔ 1 ≤ m ∧ m ≤ n := sorry

theorem reverse_range' (s : ℕ) (n : ℕ) : reverse (range' s n) = map (fun (i : ℕ) => s + n - 1 - i) (range n) := sorry

/-- All elements of `fin n`, from `0` to `n-1`. -/
def fin_range (n : ℕ) : List (fin n) :=
  pmap fin.mk (range n) sorry

@[simp] theorem fin_range_zero : fin_range 0 = [] :=
  rfl

@[simp] theorem mem_fin_range {n : ℕ} (a : fin n) : a ∈ fin_range n := sorry

theorem nodup_fin_range (n : ℕ) : nodup (fin_range n) :=
  nodup_pmap (fun (_x : ℕ) (_x_1 : _x < n) (_x_2 : ℕ) (_x_3 : _x_2 < n) => fin.veq_of_eq) (nodup_range n)

@[simp] theorem length_fin_range (n : ℕ) : length (fin_range n) = n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (length (fin_range n) = n)) (fin_range.equations._eqn_1 n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (length (pmap fin.mk (range n) (fin_range._proof_1 n)) = n)) length_pmap))
      (eq.mpr (id (Eq._oldrec (Eq.refl (length (range n) = n)) (length_range n))) (Eq.refl n)))

@[simp] theorem fin_range_eq_nil {n : ℕ} : fin_range n = [] ↔ n = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (fin_range n = [] ↔ n = 0)) (Eq.symm (propext length_eq_zero))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (length (fin_range n) = 0 ↔ n = 0)) (length_fin_range n))) (iff.refl (n = 0)))

theorem prod_range_succ {α : Type u} [monoid α] (f : ℕ → α) (n : ℕ) : prod (map f (range (Nat.succ n))) = prod (map f (range n)) * f n := sorry

/-- A variant of `prod_range_succ` which pulls off the first
  term in the product rather than the last.-/
theorem sum_range_succ' {α : Type u} [add_monoid α] (f : ℕ → α) (n : ℕ) : sum (map f (range (Nat.succ n))) = f 0 + sum (map (fun (i : ℕ) => f (Nat.succ i)) (range n)) := sorry

@[simp] theorem enum_from_map_fst {α : Type u} (n : ℕ) (l : List α) : map prod.fst (enum_from n l) = range' n (length l) := sorry

@[simp] theorem enum_map_fst {α : Type u} (l : List α) : map prod.fst (enum l) = range (length l) := sorry

theorem enum_eq_zip_range {α : Type u} (l : List α) : enum l = zip (range (length l)) l :=
  zip_of_prod (enum_map_fst l) (enum_map_snd l)

@[simp] theorem unzip_enum_eq_prod {α : Type u} (l : List α) : unzip (enum l) = (range (length l), l) := sorry

theorem enum_from_eq_zip_range' {α : Type u} (l : List α) {n : ℕ} : enum_from n l = zip (range' n (length l)) l :=
  zip_of_prod (enum_from_map_fst n l) (enum_from_map_snd n l)

@[simp] theorem unzip_enum_from_eq_prod {α : Type u} (l : List α) {n : ℕ} : unzip (enum_from n l) = (range' n (length l), l) := sorry

@[simp] theorem nth_le_range {n : ℕ} (i : ℕ) (H : i < length (range n)) : nth_le (range n) i H = i := sorry

@[simp] theorem nth_le_fin_range {n : ℕ} {i : ℕ} (h : i < length (fin_range n)) : nth_le (fin_range n) i h = { val := i, property := length_fin_range n ▸ h } := sorry

theorem of_fn_eq_pmap {α : Type u_1} {n : ℕ} {f : fin n → α} : of_fn f = pmap (fun (i : ℕ) (hi : i < n) => f { val := i, property := hi }) (range n) fun (_x : ℕ) => iff.mp mem_range := sorry

theorem of_fn_id (n : ℕ) : of_fn id = fin_range n :=
  of_fn_eq_pmap

theorem of_fn_eq_map {α : Type u_1} {n : ℕ} {f : fin n → α} : of_fn f = map f (fin_range n) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (of_fn f = map f (fin_range n))) (Eq.symm (of_fn_id n))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (of_fn f = map f (of_fn id))) (map_of_fn id f)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (of_fn f = of_fn (f ∘ id))) (function.right_id f))) (Eq.refl (of_fn f))))

theorem nodup_of_fn {α : Type u_1} {n : ℕ} {f : fin n → α} (hf : function.injective f) : nodup (of_fn f) := sorry

