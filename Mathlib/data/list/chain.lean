/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau, Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.list.pairwise
import Mathlib.logic.relation
import Mathlib.PostPort

universes u v 

namespace Mathlib

namespace list


/- chain relation (conjunction of R a b ∧ R b c ∧ R c d ...) -/

theorem chain_iff {α : Type u} (R : α → α → Prop) : ∀ (ᾰ : α) (ᾰ_1 : List α),
  chain R ᾰ ᾰ_1 ↔ ᾰ_1 = [] ∨ Exists fun {b : α} => Exists fun {l : List α} => R ᾰ b ∧ chain R b l ∧ ᾰ_1 = b :: l := sorry

theorem rel_of_chain_cons {α : Type u} {R : α → α → Prop} {a : α} {b : α} {l : List α} (p : chain R a (b :: l)) : R a b :=
  and.left (iff.mp chain_cons p)

theorem chain_of_chain_cons {α : Type u} {R : α → α → Prop} {a : α} {b : α} {l : List α} (p : chain R a (b :: l)) : chain R b l :=
  and.right (iff.mp chain_cons p)

theorem chain.imp' {α : Type u} {R : α → α → Prop} {S : α → α → Prop} (HRS : ∀ {a b : α}, R a b → S a b) {a : α} {b : α} (Hab : ∀ {c : α}, R a c → S b c) {l : List α} (p : chain R a l) : chain S b l := sorry

theorem chain.imp {α : Type u} {R : α → α → Prop} {S : α → α → Prop} (H : ∀ (a b : α), R a b → S a b) {a : α} {l : List α} (p : chain R a l) : chain S a l :=
  chain.imp' H (H a) p

theorem chain.iff {α : Type u} {R : α → α → Prop} {S : α → α → Prop} (H : ∀ (a b : α), R a b ↔ S a b) {a : α} {l : List α} : chain R a l ↔ chain S a l :=
  { mp := chain.imp fun (a b : α) => iff.mp (H a b), mpr := chain.imp fun (a b : α) => iff.mpr (H a b) }

theorem chain.iff_mem {α : Type u} {R : α → α → Prop} {a : α} {l : List α} : chain R a l ↔ chain (fun (x y : α) => x ∈ a :: l ∧ y ∈ l ∧ R x y) a l := sorry

theorem chain_singleton {α : Type u} {R : α → α → Prop} {a : α} {b : α} : chain R a [b] ↔ R a b := sorry

theorem chain_split {α : Type u} {R : α → α → Prop} {a : α} {b : α} {l₁ : List α} {l₂ : List α} : chain R a (l₁ ++ b :: l₂) ↔ chain R a (l₁ ++ [b]) ∧ chain R b l₂ := sorry

theorem chain_map {α : Type u} {β : Type v} {R : α → α → Prop} (f : β → α) {b : β} {l : List β} : chain R (f b) (map f l) ↔ chain (fun (a b : β) => R (f a) (f b)) b l := sorry

theorem chain_of_chain_map {α : Type u} {β : Type v} {R : α → α → Prop} {S : β → β → Prop} (f : α → β) (H : ∀ (a b : α), S (f a) (f b) → R a b) {a : α} {l : List α} (p : chain S (f a) (map f l)) : chain R a l :=
  chain.imp H (iff.mp (chain_map f) p)

theorem chain_map_of_chain {α : Type u} {β : Type v} {R : α → α → Prop} {S : β → β → Prop} (f : α → β) (H : ∀ (a b : α), R a b → S (f a) (f b)) {a : α} {l : List α} (p : chain R a l) : chain S (f a) (map f l) :=
  iff.mpr (chain_map f) (chain.imp H p)

theorem chain_pmap_of_chain {α : Type u} {β : Type v} {R : α → α → Prop} {S : β → β → Prop} {p : α → Prop} {f : (a : α) → p a → β} (H : ∀ (a b : α) (ha : p a) (hb : p b), R a b → S (f a ha) (f b hb)) {a : α} {l : List α} (hl₁ : chain R a l) (ha : p a) (hl₂ : ∀ (a : α), a ∈ l → p a) : chain S (f a ha) (pmap f l hl₂) := sorry

theorem chain_of_chain_pmap {α : Type u} {β : Type v} {R : α → α → Prop} {S : β → β → Prop} {p : α → Prop} (f : (a : α) → p a → β) {l : List α} (hl₁ : ∀ (a : α), a ∈ l → p a) {a : α} (ha : p a) (hl₂ : chain S (f a ha) (pmap f l hl₁)) (H : ∀ (a b : α) (ha : p a) (hb : p b), S (f a ha) (f b hb) → R a b) : chain R a l := sorry

theorem chain_of_pairwise {α : Type u} {R : α → α → Prop} {a : α} {l : List α} (p : pairwise R (a :: l)) : chain R a l := sorry

theorem chain_iff_pairwise {α : Type u} {R : α → α → Prop} (tr : transitive R) {a : α} {l : List α} : chain R a l ↔ pairwise R (a :: l) := sorry

theorem chain_iff_nth_le {α : Type u} {R : α → α → Prop} {a : α} {l : List α} : chain R a l ↔
  (∀ (h : 0 < length l), R a (nth_le l 0 h)) ∧
    ∀ (i : ℕ) (h : i < length l - 1), R (nth_le l i (nat.lt_of_lt_pred h)) (nth_le l (i + 1) (iff.mp nat.lt_pred_iff h)) := sorry

theorem chain'.imp {α : Type u} {R : α → α → Prop} {S : α → α → Prop} (H : ∀ (a b : α), R a b → S a b) {l : List α} (p : chain' R l) : chain' S l :=
  list.cases_on l (fun (p : chain' R []) => trivial)
    (fun (l_hd : α) (l_tl : List α) (p : chain' R (l_hd :: l_tl)) => chain.imp H p) p

theorem chain'.iff {α : Type u} {R : α → α → Prop} {S : α → α → Prop} (H : ∀ (a b : α), R a b ↔ S a b) {l : List α} : chain' R l ↔ chain' S l :=
  { mp := chain'.imp fun (a b : α) => iff.mp (H a b), mpr := chain'.imp fun (a b : α) => iff.mpr (H a b) }

theorem chain'.iff_mem {α : Type u} {R : α → α → Prop} {l : List α} : chain' R l ↔ chain' (fun (x y : α) => x ∈ l ∧ y ∈ l ∧ R x y) l := sorry

@[simp] theorem chain'_nil {α : Type u} {R : α → α → Prop} : chain' R [] :=
  trivial

@[simp] theorem chain'_singleton {α : Type u} {R : α → α → Prop} (a : α) : chain' R [a] :=
  chain.nil

theorem chain'_split {α : Type u} {R : α → α → Prop} {a : α} {l₁ : List α} {l₂ : List α} : chain' R (l₁ ++ a :: l₂) ↔ chain' R (l₁ ++ [a]) ∧ chain' R (a :: l₂) := sorry

theorem chain'_map {α : Type u} {β : Type v} {R : α → α → Prop} (f : β → α) {l : List β} : chain' R (map f l) ↔ chain' (fun (a b : β) => R (f a) (f b)) l :=
  list.cases_on l (iff.refl (chain' R (map f []))) fun (l_hd : β) (l_tl : List β) => chain_map f

theorem chain'_of_chain'_map {α : Type u} {β : Type v} {R : α → α → Prop} {S : β → β → Prop} (f : α → β) (H : ∀ (a b : α), S (f a) (f b) → R a b) {l : List α} (p : chain' S (map f l)) : chain' R l :=
  chain'.imp H (iff.mp (chain'_map f) p)

theorem chain'_map_of_chain' {α : Type u} {β : Type v} {R : α → α → Prop} {S : β → β → Prop} (f : α → β) (H : ∀ (a b : α), R a b → S (f a) (f b)) {l : List α} (p : chain' R l) : chain' S (map f l) :=
  iff.mpr (chain'_map f) (chain'.imp H p)

theorem pairwise.chain' {α : Type u} {R : α → α → Prop} {l : List α} : pairwise R l → chain' R l := sorry

theorem chain'_iff_pairwise {α : Type u} {R : α → α → Prop} (tr : transitive R) {l : List α} : chain' R l ↔ pairwise R l :=
  list.cases_on l (idRhs (True ↔ pairwise R []) (iff.symm (iff_true_intro pairwise.nil)))
    fun (l_hd : α) (l_tl : List α) => idRhs (chain R l_hd l_tl ↔ pairwise R (l_hd :: l_tl)) (chain_iff_pairwise tr)

@[simp] theorem chain'_cons {α : Type u} {R : α → α → Prop} {x : α} {y : α} {l : List α} : chain' R (x :: y :: l) ↔ R x y ∧ chain' R (y :: l) :=
  chain_cons

theorem chain'.cons {α : Type u} {R : α → α → Prop} {x : α} {y : α} {l : List α} (h₁ : R x y) (h₂ : chain' R (y :: l)) : chain' R (x :: y :: l) :=
  iff.mpr chain'_cons { left := h₁, right := h₂ }

theorem chain'.tail {α : Type u} {R : α → α → Prop} {l : List α} (h : chain' R l) : chain' R (tail l) := sorry

theorem chain'.rel_head {α : Type u} {R : α → α → Prop} {x : α} {y : α} {l : List α} (h : chain' R (x :: y :: l)) : R x y :=
  rel_of_chain_cons h

theorem chain'.rel_head' {α : Type u} {R : α → α → Prop} {x : α} {l : List α} (h : chain' R (x :: l)) {y : α} (hy : y ∈ head' l) : R x y :=
  chain'.rel_head (eq.mp (Eq._oldrec (Eq.refl (chain' R (x :: l))) (Eq.symm (cons_head'_tail hy))) h)

theorem chain'.cons' {α : Type u} {R : α → α → Prop} {x : α} {l : List α} : chain' R l → (∀ (y : α), y ∈ head' l → R x y) → chain' R (x :: l) := sorry

theorem chain'_cons' {α : Type u} {R : α → α → Prop} {x : α} {l : List α} : chain' R (x :: l) ↔ (∀ (y : α), y ∈ head' l → R x y) ∧ chain' R l := sorry

theorem chain'.append {α : Type u} {R : α → α → Prop} {l₁ : List α} {l₂ : List α} (h₁ : chain' R l₁) (h₂ : chain' R l₂) (h : ∀ (x : α), x ∈ last' l₁ → ∀ (y : α), y ∈ head' l₂ → R x y) : chain' R (l₁ ++ l₂) := sorry

theorem chain'_pair {α : Type u} {R : α → α → Prop} {x : α} {y : α} : chain' R [x, y] ↔ R x y := sorry

theorem chain'.imp_head {α : Type u} {R : α → α → Prop} {x : α} {y : α} (h : ∀ {z : α}, R x z → R y z) {l : List α} (hl : chain' R (x :: l)) : chain' R (y :: l) :=
  chain'.cons' (chain'.tail hl) fun (z : α) (hz : z ∈ head' (tail (x :: l))) => h (chain'.rel_head' hl hz)

theorem chain'_reverse {α : Type u} {R : α → α → Prop} {l : List α} : chain' R (reverse l) ↔ chain' (flip R) l := sorry

theorem chain'_iff_nth_le {α : Type u} {R : α → α → Prop} {l : List α} : chain' R l ↔
  ∀ (i : ℕ) (h : i < length l - 1), R (nth_le l i (nat.lt_of_lt_pred h)) (nth_le l (i + 1) (iff.mp nat.lt_pred_iff h)) := sorry

/-- If `l₁ l₂` and `l₃` are lists and `l₁ ++ l₂` and `l₂ ++ l₃` both satisfy
  `chain' R`, then so does `l₁ ++ l₂ ++ l₃` provided `l₂ ≠ []` -/
theorem chain'.append_overlap {α : Type u} {R : α → α → Prop} {l₁ : List α} {l₂ : List α} {l₃ : List α} (h₁ : chain' R (l₁ ++ l₂)) (h₂ : chain' R (l₂ ++ l₃)) (hn : l₂ ≠ []) : chain' R (l₁ ++ l₂ ++ l₃) := sorry

/--
If `a` and `b` are related by the reflexive transitive closure of `r`, then there is a `r`-chain
starting from `a` and ending on `b`.
The converse of `relation_refl_trans_gen_of_exists_chain`.
-/
theorem exists_chain_of_relation_refl_trans_gen {α : Type u} {r : α → α → Prop} {a : α} {b : α} (h : relation.refl_trans_gen r a b) : ∃ (l : List α), chain r a l ∧ last (a :: l) (cons_ne_nil a l) = b := sorry

/--
Given a chain from `a` to `b`, and a predicate true at `b`, if `r x y → p y → p x` then
the predicate is true everywhere in the chain and at `a`.
That is, we can propagate the predicate up the chain.
-/
theorem chain.induction {α : Type u} {r : α → α → Prop} {a : α} {b : α} (p : α → Prop) (l : List α) (h : chain r a l) (hb : last (a :: l) (cons_ne_nil a l) = b) (carries : ∀ {x y : α}, r x y → p y → p x) (final : p b) (i : α) (H : i ∈ a :: l) : p i := sorry

/--
Given a chain from `a` to `b`, and a predicate true at `b`, if `r x y → p y → p x` then
the predicate is true at `a`.
That is, we can propagate the predicate all the way up the chain.
-/
theorem chain.induction_head {α : Type u} {r : α → α → Prop} {a : α} {b : α} (p : α → Prop) (l : List α) (h : chain r a l) (hb : last (a :: l) (cons_ne_nil a l) = b) (carries : ∀ {x y : α}, r x y → p y → p x) (final : p b) : p a :=
  chain.induction p l h hb carries final a (mem_cons_self a l)

/--
If there is an `r`-chain starting from `a` and ending at `b`, then `a` and `b` are related by the
reflexive transitive closure of `r`. The converse of `exists_chain_of_relation_refl_trans_gen`.
-/
theorem relation_refl_trans_gen_of_exists_chain {α : Type u} {r : α → α → Prop} {a : α} {b : α} (l : List α) (hl₁ : chain r a l) (hl₂ : last (a :: l) (cons_ne_nil a l) = b) : relation.refl_trans_gen r a b :=
  chain.induction_head (fun (_x : α) => relation.refl_trans_gen r _x b) l hl₁ hl₂
    (fun (x y : α) => relation.refl_trans_gen.head) relation.refl_trans_gen.refl

