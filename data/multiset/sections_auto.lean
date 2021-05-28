/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.multiset.basic
import PostPort

universes u_1 

namespace Mathlib

/-!
# Sections of a multiset
-/

namespace multiset


/--
The sections of a multiset of multisets `s` consists of all those multisets
which can be put in bijection with `s`, so each element is an member of the corresponding multiset.
-/
def sections {α : Type u_1} (s : multiset (multiset α)) : multiset (multiset α) :=
  multiset.rec_on s (singleton 0)
    (fun (s : multiset α) (_x c : multiset (multiset α)) => bind s fun (a : α) => map (cons a) c) sorry

@[simp] theorem sections_zero {α : Type u_1} : sections 0 = 0 ::ₘ 0 :=
  rfl

@[simp] theorem sections_cons {α : Type u_1} (s : multiset (multiset α)) (m : multiset α) : sections (m ::ₘ s) = bind m fun (a : α) => map (cons a) (sections s) :=
  rec_on_cons m s

theorem coe_sections {α : Type u_1} (l : List (List α)) : sections ↑(list.map (fun (l : List α) => ↑l) l) = ↑(list.map (fun (l : List α) => ↑l) (list.sections l)) := sorry

@[simp] theorem sections_add {α : Type u_1} (s : multiset (multiset α)) (t : multiset (multiset α)) : sections (s + t) = bind (sections s) fun (m : multiset α) => map (Add.add m) (sections t) := sorry

theorem mem_sections {α : Type u_1} {s : multiset (multiset α)} {a : multiset α} : a ∈ sections s ↔ rel (fun (s : multiset α) (a : α) => a ∈ s) s a := sorry

theorem card_sections {α : Type u_1} {s : multiset (multiset α)} : coe_fn card (sections s) = prod (map (⇑card) s) := sorry

theorem prod_map_sum {α : Type u_1} [comm_semiring α] {s : multiset (multiset α)} : prod (map sum s) = sum (map prod (sections s)) := sorry

