/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import PrePort
import Lean3Lib.init.default
import PostPort

universes u v w 

namespace Mathlib

def stream (α : Type u)  :=
  ℕ → α

namespace stream


def cons {α : Type u} (a : α) (s : stream α) : stream α :=
  fun (i : ℕ) => sorry

infixr:67 " :: " => Mathlib.stream.cons

def head {α : Type u} (s : stream α) : α :=
  s 0

def tail {α : Type u} (s : stream α) : stream α :=
  fun (i : ℕ) => s (i + 1)

def drop {α : Type u} (n : ℕ) (s : stream α) : stream α :=
  fun (i : ℕ) => s (i + n)

def nth {α : Type u} (n : ℕ) (s : stream α) : α :=
  s n

protected theorem eta {α : Type u} (s : stream α) : head s :: tail s = s :=
  funext
    fun (i : ℕ) =>
      nat.cases_on i (Eq.refl (cons (head s) (tail s) 0)) fun (i : ℕ) => Eq.refl (cons (head s) (tail s) (Nat.succ i))

theorem nth_zero_cons {α : Type u} (a : α) (s : stream α) : nth 0 (a :: s) = a :=
  rfl

theorem head_cons {α : Type u} (a : α) (s : stream α) : head (a :: s) = a :=
  rfl

theorem tail_cons {α : Type u} (a : α) (s : stream α) : tail (a :: s) = s :=
  rfl

theorem tail_drop {α : Type u} (n : ℕ) (s : stream α) : tail (drop n s) = drop n (tail s) := sorry

theorem nth_drop {α : Type u} (n : ℕ) (m : ℕ) (s : stream α) : nth n (drop m s) = nth (n + m) s :=
  rfl

theorem tail_eq_drop {α : Type u} (s : stream α) : tail s = drop 1 s :=
  rfl

theorem drop_drop {α : Type u} (n : ℕ) (m : ℕ) (s : stream α) : drop n (drop m s) = drop (n + m) s := sorry

theorem nth_succ {α : Type u} (n : ℕ) (s : stream α) : nth (Nat.succ n) s = nth n (tail s) :=
  rfl

theorem drop_succ {α : Type u} (n : ℕ) (s : stream α) : drop (Nat.succ n) s = drop n (tail s) :=
  rfl

protected theorem ext {α : Type u} {s₁ : stream α} {s₂ : stream α} : (∀ (n : ℕ), nth n s₁ = nth n s₂) → s₁ = s₂ :=
  fun (h : ∀ (n : ℕ), nth n s₁ = nth n s₂) => funext h

def all {α : Type u} (p : α → Prop) (s : stream α)  :=
  ∀ (n : ℕ), p (nth n s)

def any {α : Type u} (p : α → Prop) (s : stream α)  :=
  ∃ (n : ℕ), p (nth n s)

theorem all_def {α : Type u} (p : α → Prop) (s : stream α) : all p s = ∀ (n : ℕ), p (nth n s) :=
  rfl

theorem any_def {α : Type u} (p : α → Prop) (s : stream α) : any p s = ∃ (n : ℕ), p (nth n s) :=
  rfl

protected def mem {α : Type u} (a : α) (s : stream α)  :=
  any (fun (b : α) => a = b) s

protected instance has_mem {α : Type u} : has_mem α (stream α) :=
  has_mem.mk stream.mem

theorem mem_cons {α : Type u} (a : α) (s : stream α) : a ∈ a :: s :=
  exists.intro 0 rfl

theorem mem_cons_of_mem {α : Type u} {a : α} {s : stream α} (b : α) : a ∈ s → a ∈ b :: s := sorry

theorem eq_or_mem_of_mem_cons {α : Type u} {a : α} {b : α} {s : stream α} : a ∈ b :: s → a = b ∨ a ∈ s := sorry

theorem mem_of_nth_eq {α : Type u} {n : ℕ} {s : stream α} {a : α} : a = nth n s → a ∈ s :=
  fun (h : a = nth n s) => exists.intro n h

def map {α : Type u} {β : Type v} (f : α → β) (s : stream α) : stream β :=
  fun (n : ℕ) => f (nth n s)

theorem drop_map {α : Type u} {β : Type v} (f : α → β) (n : ℕ) (s : stream α) : drop n (map f s) = map f (drop n s) :=
  stream.ext fun (i : ℕ) => rfl

theorem nth_map {α : Type u} {β : Type v} (f : α → β) (n : ℕ) (s : stream α) : nth n (map f s) = f (nth n s) :=
  rfl

theorem tail_map {α : Type u} {β : Type v} (f : α → β) (s : stream α) : tail (map f s) = map f (tail s) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (tail (map f s) = map f (tail s))) (tail_eq_drop (map f s))))
    (Eq.refl (drop 1 (map f s)))

theorem head_map {α : Type u} {β : Type v} (f : α → β) (s : stream α) : head (map f s) = f (head s) :=
  rfl

theorem map_eq {α : Type u} {β : Type v} (f : α → β) (s : stream α) : map f s = f (head s) :: map f (tail s) := sorry

theorem map_cons {α : Type u} {β : Type v} (f : α → β) (a : α) (s : stream α) : map f (a :: s) = f a :: map f s := sorry

theorem map_id {α : Type u} (s : stream α) : map id s = s :=
  rfl

theorem map_map {α : Type u} {β : Type v} {δ : Type w} (g : β → δ) (f : α → β) (s : stream α) : map g (map f s) = map (g ∘ f) s :=
  rfl

theorem map_tail {α : Type u} {β : Type v} (f : α → β) (s : stream α) : map f (tail s) = tail (map f s) :=
  rfl

theorem mem_map {α : Type u} {β : Type v} (f : α → β) {a : α} {s : stream α} : a ∈ s → f a ∈ map f s := sorry

theorem exists_of_mem_map {α : Type u} {β : Type v} {f : α → β} {b : β} {s : stream α} : b ∈ map f s → ∃ (a : α), a ∈ s ∧ f a = b := sorry

def zip {α : Type u} {β : Type v} {δ : Type w} (f : α → β → δ) (s₁ : stream α) (s₂ : stream β) : stream δ :=
  fun (n : ℕ) => f (nth n s₁) (nth n s₂)

theorem drop_zip {α : Type u} {β : Type v} {δ : Type w} (f : α → β → δ) (n : ℕ) (s₁ : stream α) (s₂ : stream β) : drop n (zip f s₁ s₂) = zip f (drop n s₁) (drop n s₂) :=
  stream.ext fun (i : ℕ) => rfl

theorem nth_zip {α : Type u} {β : Type v} {δ : Type w} (f : α → β → δ) (n : ℕ) (s₁ : stream α) (s₂ : stream β) : nth n (zip f s₁ s₂) = f (nth n s₁) (nth n s₂) :=
  rfl

theorem head_zip {α : Type u} {β : Type v} {δ : Type w} (f : α → β → δ) (s₁ : stream α) (s₂ : stream β) : head (zip f s₁ s₂) = f (head s₁) (head s₂) :=
  rfl

theorem tail_zip {α : Type u} {β : Type v} {δ : Type w} (f : α → β → δ) (s₁ : stream α) (s₂ : stream β) : tail (zip f s₁ s₂) = zip f (tail s₁) (tail s₂) :=
  rfl

theorem zip_eq {α : Type u} {β : Type v} {δ : Type w} (f : α → β → δ) (s₁ : stream α) (s₂ : stream β) : zip f s₁ s₂ = f (head s₁) (head s₂) :: zip f (tail s₁) (tail s₂) := sorry

def const {α : Type u} (a : α) : stream α :=
  fun (n : ℕ) => a

theorem mem_const {α : Type u} (a : α) : a ∈ const a :=
  exists.intro 0 rfl

theorem const_eq {α : Type u} (a : α) : const a = a :: const a :=
  stream.ext fun (n : ℕ) => nat.cases_on n (Eq.refl (nth 0 (const a))) fun (n : ℕ) => Eq.refl (nth (Nat.succ n) (const a))

theorem tail_const {α : Type u} (a : α) : tail (const a) = const a :=
  (fun (this : tail (a :: const a) = const a) =>
      eq.mp (Eq._oldrec (Eq.refl (tail (a :: const a) = const a)) (Eq.symm (const_eq a))) this)
    rfl

theorem map_const {α : Type u} {β : Type v} (f : α → β) (a : α) : map f (const a) = const (f a) :=
  rfl

theorem nth_const {α : Type u} (n : ℕ) (a : α) : nth n (const a) = a :=
  rfl

theorem drop_const {α : Type u} (n : ℕ) (a : α) : drop n (const a) = const a :=
  stream.ext fun (i : ℕ) => rfl

def iterate {α : Type u} (f : α → α) (a : α) : stream α :=
  fun (n : ℕ) => nat.rec_on n a fun (n : ℕ) (r : α) => f r

theorem head_iterate {α : Type u} (f : α → α) (a : α) : head (iterate f a) = a :=
  rfl

theorem tail_iterate {α : Type u} (f : α → α) (a : α) : tail (iterate f a) = iterate f (f a) := sorry

theorem iterate_eq {α : Type u} (f : α → α) (a : α) : iterate f a = a :: iterate f (f a) := sorry

theorem nth_zero_iterate {α : Type u} (f : α → α) (a : α) : nth 0 (iterate f a) = a :=
  rfl

theorem nth_succ_iterate {α : Type u} (n : ℕ) (f : α → α) (a : α) : nth (Nat.succ n) (iterate f a) = nth n (iterate f (f a)) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (nth (Nat.succ n) (iterate f a) = nth n (iterate f (f a)))) (nth_succ n (iterate f a))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (nth n (tail (iterate f a)) = nth n (iterate f (f a)))) (tail_iterate f a)))
      (Eq.refl (nth n (iterate f (f a)))))

def is_bisimulation {α : Type u} (R : stream α → stream α → Prop)  :=
  ∀ {s₁ s₂ : stream α}, R s₁ s₂ → head s₁ = head s₂ ∧ R (tail s₁) (tail s₂)

theorem nth_of_bisim {α : Type u} (R : stream α → stream α → Prop) (bisim : is_bisimulation R) {s₁ : stream α} {s₂ : stream α} (n : ℕ) : R s₁ s₂ → nth n s₁ = nth n s₂ ∧ R (drop (n + 1) s₁) (drop (n + 1) s₂) := sorry

theorem eq_of_bisim {α : Type u} (R : stream α → stream α → Prop) (bisim : is_bisimulation R) {s₁ : stream α} {s₂ : stream α} : R s₁ s₂ → s₁ = s₂ :=
  fun (r : R s₁ s₂) => stream.ext fun (n : ℕ) => and.elim_left (nth_of_bisim R bisim n r)

theorem bisim_simple {α : Type u} (s₁ : stream α) (s₂ : stream α) : head s₁ = head s₂ → s₁ = tail s₁ → s₂ = tail s₂ → s₁ = s₂ := sorry

theorem coinduction {α : Type u} {s₁ : stream α} {s₂ : stream α} : head s₁ = head s₂ → (∀ (β : Type u) (fr : stream α → β), fr s₁ = fr s₂ → fr (tail s₁) = fr (tail s₂)) → s₁ = s₂ := sorry

theorem iterate_id {α : Type u} (a : α) : iterate id a = const a := sorry

theorem map_iterate {α : Type u} (f : α → α) (a : α) : iterate f (f a) = map f (iterate f a) := sorry

def corec {α : Type u} {β : Type v} (f : α → β) (g : α → α) : α → stream β :=
  fun (a : α) => map f (iterate g a)

def corec_on {α : Type u} {β : Type v} (a : α) (f : α → β) (g : α → α) : stream β :=
  corec f g a

theorem corec_def {α : Type u} {β : Type v} (f : α → β) (g : α → α) (a : α) : corec f g a = map f (iterate g a) :=
  rfl

theorem corec_eq {α : Type u} {β : Type v} (f : α → β) (g : α → α) (a : α) : corec f g a = f a :: corec f g (g a) := sorry

theorem corec_id_id_eq_const {α : Type u} (a : α) : corec id id a = const a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (corec id id a = const a)) (corec_def id id a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (map id (iterate id a) = const a)) (map_id (iterate id a))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (iterate id a = const a)) (iterate_id a))) (Eq.refl (const a))))

theorem corec_id_f_eq_iterate {α : Type u} (f : α → α) (a : α) : corec id f a = iterate f a :=
  rfl

def corec' {α : Type u} {β : Type v} (f : α → β × α) : α → stream β :=
  corec (prod.fst ∘ f) (prod.snd ∘ f)

theorem corec'_eq {α : Type u} {β : Type v} (f : α → β × α) (a : α) : corec' f a = prod.fst (f a) :: corec' f (prod.snd (f a)) :=
  corec_eq (prod.fst ∘ f) (prod.snd ∘ f) a

-- corec is also known as unfold

def unfolds {α : Type u} {β : Type v} (g : α → β) (f : α → α) (a : α) : stream β :=
  corec g f a

theorem unfolds_eq {α : Type u} {β : Type v} (g : α → β) (f : α → α) (a : α) : unfolds g f a = g a :: unfolds g f (f a) := sorry

theorem nth_unfolds_head_tail {α : Type u} (n : ℕ) (s : stream α) : nth n (unfolds head tail s) = nth n s := sorry

theorem unfolds_head_eq {α : Type u} (s : stream α) : unfolds head tail s = s :=
  stream.ext fun (n : ℕ) => nth_unfolds_head_tail n s

def interleave {α : Type u} (s₁ : stream α) (s₂ : stream α) : stream α :=
  corec_on (s₁, s₂) (fun (_x : stream α × stream α) => sorry) fun (_x : stream α × stream α) => sorry

infixl:65 "⋈" => Mathlib.stream.interleave

theorem interleave_eq {α : Type u} (s₁ : stream α) (s₂ : stream α) : s₁⋈s₂ = head s₁ :: head s₂ :: (tail s₁⋈tail s₂) := sorry

theorem tail_interleave {α : Type u} (s₁ : stream α) (s₂ : stream α) : tail (s₁⋈s₂) = s₂⋈tail s₁ := sorry

theorem interleave_tail_tail {α : Type u} (s₁ : stream α) (s₂ : stream α) : tail s₁⋈tail s₂ = tail (tail (s₁⋈s₂)) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (tail s₁⋈tail s₂ = tail (tail (s₁⋈s₂)))) (interleave_eq s₁ s₂)))
    (Eq.refl (tail s₁⋈tail s₂))

theorem nth_interleave_left {α : Type u} (n : ℕ) (s₁ : stream α) (s₂ : stream α) : nth (bit0 1 * n) (s₁⋈s₂) = nth n s₁ := sorry

theorem nth_interleave_right {α : Type u} (n : ℕ) (s₁ : stream α) (s₂ : stream α) : nth (bit0 1 * n + 1) (s₁⋈s₂) = nth n s₂ := sorry

theorem mem_interleave_left {α : Type u} {a : α} {s₁ : stream α} (s₂ : stream α) : a ∈ s₁ → a ∈ s₁⋈s₂ := sorry

theorem mem_interleave_right {α : Type u} {a : α} {s₁ : stream α} (s₂ : stream α) : a ∈ s₂ → a ∈ s₁⋈s₂ := sorry

def even {α : Type u} (s : stream α) : stream α :=
  corec (fun (s : stream α) => head s) (fun (s : stream α) => tail (tail s)) s

def odd {α : Type u} (s : stream α) : stream α :=
  even (tail s)

theorem odd_eq {α : Type u} (s : stream α) : odd s = even (tail s) :=
  rfl

theorem head_even {α : Type u} (s : stream α) : head (even s) = head s :=
  rfl

theorem tail_even {α : Type u} (s : stream α) : tail (even s) = even (tail (tail s)) := sorry

theorem even_cons_cons {α : Type u} (a₁ : α) (a₂ : α) (s : stream α) : even (a₁ :: a₂ :: s) = a₁ :: even s := sorry

theorem even_tail {α : Type u} (s : stream α) : even (tail s) = odd s :=
  rfl

theorem even_interleave {α : Type u} (s₁ : stream α) (s₂ : stream α) : even (s₁⋈s₂) = s₁ := sorry

theorem interleave_even_odd {α : Type u} (s₁ : stream α) : even s₁⋈odd s₁ = s₁ := sorry

theorem nth_even {α : Type u} (n : ℕ) (s : stream α) : nth n (even s) = nth (bit0 1 * n) s := sorry

theorem nth_odd {α : Type u} (n : ℕ) (s : stream α) : nth n (odd s) = nth (bit0 1 * n + 1) s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (nth n (odd s) = nth (bit0 1 * n + 1) s)) (odd_eq s)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (nth n (even (tail s)) = nth (bit0 1 * n + 1) s)) (nth_even n (tail s))))
      (Eq.refl (nth (bit0 1 * n) (tail s))))

theorem mem_of_mem_even {α : Type u} (a : α) (s : stream α) : a ∈ even s → a ∈ s := sorry

theorem mem_of_mem_odd {α : Type u} (a : α) (s : stream α) : a ∈ odd s → a ∈ s := sorry

def append_stream {α : Type u} : List α → stream α → stream α :=
  sorry

theorem nil_append_stream {α : Type u} (s : stream α) : append_stream [] s = s :=
  rfl

theorem cons_append_stream {α : Type u} (a : α) (l : List α) (s : stream α) : append_stream (a :: l) s = a :: append_stream l s :=
  rfl

infixl:65 "++ₛ" => Mathlib.stream.append_stream

theorem append_append_stream {α : Type u} (l₁ : List α) (l₂ : List α) (s : stream α) : l₁ ++ l₂++ₛs = l₁++ₛ(l₂++ₛs) := sorry

theorem map_append_stream {α : Type u} {β : Type v} (f : α → β) (l : List α) (s : stream α) : map f (l++ₛs) = list.map f l++ₛmap f s := sorry

theorem drop_append_stream {α : Type u} (l : List α) (s : stream α) : drop (list.length l) (l++ₛs) = s := sorry

theorem append_stream_head_tail {α : Type u} (s : stream α) : [head s]++ₛtail s = s :=
  eq.mpr (id (Eq._oldrec (Eq.refl ([head s]++ₛtail s = s)) (cons_append_stream (head s) [] (tail s))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (head s :: ([]++ₛtail s) = s)) (nil_append_stream (tail s))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (head s :: tail s = s)) (stream.eta s))) (Eq.refl s)))

theorem mem_append_stream_right {α : Type u} {a : α} (l : List α) {s : stream α} : a ∈ s → a ∈ l++ₛs := sorry

theorem mem_append_stream_left {α : Type u} {a : α} {l : List α} (s : stream α) : a ∈ l → a ∈ l++ₛs := sorry

def approx {α : Type u} : ℕ → stream α → List α :=
  sorry

theorem approx_zero {α : Type u} (s : stream α) : approx 0 s = [] :=
  rfl

theorem approx_succ {α : Type u} (n : ℕ) (s : stream α) : approx (Nat.succ n) s = head s :: approx n (tail s) :=
  rfl

theorem nth_approx {α : Type u} (n : ℕ) (s : stream α) : list.nth (approx (Nat.succ n) s) n = some (nth n s) := sorry

theorem append_approx_drop {α : Type u} (n : ℕ) (s : stream α) : approx n s++ₛdrop n s = s := sorry

-- Take theorem reduces a proof of equality of infinite streams to an

-- induction over all their finite approximations.

theorem take_theorem {α : Type u} (s₁ : stream α) (s₂ : stream α) : (∀ (n : ℕ), approx n s₁ = approx n s₂) → s₁ = s₂ := sorry

-- auxiliary def for cycle corecursive def

-- auxiliary def for cycle corecursive def

def cycle {α : Type u} (l : List α) : l ≠ [] → stream α :=
  sorry

theorem cycle_eq {α : Type u} (l : List α) (h : l ≠ []) : cycle l h = l++ₛcycle l h := sorry

theorem mem_cycle {α : Type u} {a : α} {l : List α} (h : l ≠ []) : a ∈ l → a ∈ cycle l h :=
  fun (ainl : a ∈ l) =>
    eq.mpr (id (Eq._oldrec (Eq.refl (a ∈ cycle l h)) (cycle_eq l h))) (mem_append_stream_left (cycle l h) ainl)

theorem cycle_singleton {α : Type u} (a : α) (h : [a] ≠ []) : cycle [a] h = const a := sorry

def tails {α : Type u} (s : stream α) : stream (stream α) :=
  corec id tail (tail s)

theorem tails_eq {α : Type u} (s : stream α) : tails s = tail s :: tails (tail s) := sorry

theorem nth_tails {α : Type u} (n : ℕ) (s : stream α) : nth n (tails s) = drop n (tail s) := sorry

theorem tails_eq_iterate {α : Type u} (s : stream α) : tails s = iterate tail (tail s) :=
  rfl

def inits_core {α : Type u} (l : List α) (s : stream α) : stream (List α) :=
  corec_on (l, s) (fun (_x : List α × stream α) => sorry) fun (p : List α × stream α) => sorry

def inits {α : Type u} (s : stream α) : stream (List α) :=
  inits_core [head s] (tail s)

theorem inits_core_eq {α : Type u} (l : List α) (s : stream α) : inits_core l s = l :: inits_core (l ++ [head s]) (tail s) := sorry

theorem tail_inits {α : Type u} (s : stream α) : tail (inits s) = inits_core [head s, head (tail s)] (tail (tail s)) := sorry

theorem inits_tail {α : Type u} (s : stream α) : inits (tail s) = inits_core [head (tail s)] (tail (tail s)) :=
  rfl

theorem cons_nth_inits_core {α : Type u} (a : α) (n : ℕ) (l : List α) (s : stream α) : a :: nth n (inits_core l s) = nth n (inits_core (a :: l) s) := sorry

theorem nth_inits {α : Type u} (n : ℕ) (s : stream α) : nth n (inits s) = approx (Nat.succ n) s := sorry

theorem inits_eq {α : Type u} (s : stream α) : inits s = [head s] :: map (List.cons (head s)) (inits (tail s)) := sorry

theorem zip_inits_tails {α : Type u} (s : stream α) : zip append_stream (inits s) (tails s) = const s := sorry

def pure {α : Type u} (a : α) : stream α :=
  const a

def apply {α : Type u} {β : Type v} (f : stream (α → β)) (s : stream α) : stream β :=
  fun (n : ℕ) => nth n f (nth n s)

infixl:75 "⊛" => Mathlib.stream.apply

theorem identity {α : Type u} (s : stream α) : pure id⊛s = s :=
  rfl

theorem composition {α : Type u} {β : Type v} {δ : Type w} (g : stream (β → δ)) (f : stream (α → β)) (s : stream α) : pure function.comp⊛g⊛f⊛s = g⊛(f⊛s) :=
  rfl

theorem homomorphism {α : Type u} {β : Type v} (f : α → β) (a : α) : pure f⊛pure a = pure (f a) :=
  rfl

theorem interchange {α : Type u} {β : Type v} (fs : stream (α → β)) (a : α) : fs⊛pure a = (pure fun (f : α → β) => f a)⊛fs :=
  rfl

theorem map_eq_apply {α : Type u} {β : Type v} (f : α → β) (s : stream α) : map f s = pure f⊛s :=
  rfl

def nats : stream ℕ :=
  fun (n : ℕ) => n

theorem nth_nats (n : ℕ) : nth n nats = n :=
  rfl

theorem nats_eq : nats = 0 :: map Nat.succ nats := sorry

