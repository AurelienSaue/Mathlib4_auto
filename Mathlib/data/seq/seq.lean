/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.list.basic
import Mathlib.Lean3Lib.data.stream
import Mathlib.Lean3Lib.data.lazy_list
import Mathlib.data.seq.computation
import Mathlib.PostPort

universes u u_1 v w 

namespace Mathlib

/-
coinductive seq (α : Type u) : Type u
| nil : seq α
| cons : α → seq α → seq α
-/

/--
A stream `s : option α` is a sequence if `s.nth n = none` implies `s.nth (n + 1) = none`.
-/
def stream.is_seq {α : Type u} (s : stream (Option α)) :=
  ∀ {n : ℕ}, s n = none → s (n + 1) = none

/-- `seq α` is the type of possibly infinite lists (referred here as sequences).
  It is encoded as an infinite stream of options such that if `f n = none`, then
  `f m = none` for all `m ≥ n`. -/
def seq (α : Type u) :=
  Subtype fun (f : stream (Option α)) => stream.is_seq f

/-- `seq1 α` is the type of nonempty sequences. -/
def seq1 (α : Type u_1) :=
  α × seq α

namespace seq


/-- The empty sequence -/
def nil {α : Type u} : seq α :=
  { val := stream.const none, property := sorry }

protected instance inhabited {α : Type u} : Inhabited (seq α) :=
  { default := nil }

/-- Prepend an element to a sequence -/
def cons {α : Type u} (a : α) : seq α → seq α :=
  sorry

/-- Get the nth element of a sequence (if it exists) -/
def nth {α : Type u} : seq α → ℕ → Option α :=
  subtype.val

/-- A sequence has terminated at position `n` if the value at position `n` equals `none`. -/
def terminated_at {α : Type u} (s : seq α) (n : ℕ) :=
  nth s n = none

/-- It is decidable whether a sequence terminates at a given position. -/
protected instance terminated_at_decidable {α : Type u} (s : seq α) (n : ℕ) : Decidable (terminated_at s n) :=
  decidable_of_iff' ↥(option.is_none (nth s n)) sorry

/-- A sequence terminates if there is some position `n` at which it has terminated. -/
def terminates {α : Type u} (s : seq α) :=
  ∃ (n : ℕ), terminated_at s n

/-- Functorial action of the functor `option (α × _)` -/
@[simp] def omap {α : Type u} {β : Type v} {γ : Type w} (f : β → γ) : Option (α × β) → Option (α × γ) :=
  sorry

/-- Get the first element of a sequence -/
def head {α : Type u} (s : seq α) : Option α :=
  nth s 0

/-- Get the tail of a sequence (or `nil` if the sequence is `nil`) -/
def tail {α : Type u} : seq α → seq α :=
  sorry

protected def mem {α : Type u} (a : α) (s : seq α) :=
  some a ∈ subtype.val s

protected instance has_mem {α : Type u} : has_mem α (seq α) :=
  has_mem.mk seq.mem

theorem le_stable {α : Type u} (s : seq α) {m : ℕ} {n : ℕ} (h : m ≤ n) : nth s m = none → nth s n = none := sorry

/-- If a sequence terminated at position `n`, it also terminated at `m ≥ n `. -/
theorem terminated_stable {α : Type u} (s : seq α) {m : ℕ} {n : ℕ} (m_le_n : m ≤ n) (terminated_at_m : terminated_at s m) : terminated_at s n :=
  le_stable s m_le_n terminated_at_m

/--
If `s.nth n = some aₙ` for some value `aₙ`, then there is also some value `aₘ` such
that `s.nth = some aₘ` for `m ≤ n`.
-/
theorem ge_stable {α : Type u} (s : seq α) {aₙ : α} {n : ℕ} {m : ℕ} (m_le_n : m ≤ n) (s_nth_eq_some : nth s n = some aₙ) : ∃ (aₘ : α), nth s m = some aₘ := sorry

theorem not_mem_nil {α : Type u} (a : α) : ¬a ∈ nil := sorry

theorem mem_cons {α : Type u} (a : α) (s : seq α) : a ∈ cons a s :=
  subtype.cases_on s
    fun (s_val : stream (Option α)) (s_property : stream.is_seq s_val) =>
      idRhs (some a ∈ some a :: s_val) (stream.mem_cons (some a) s_val)

theorem mem_cons_of_mem {α : Type u} (y : α) {a : α} {s : seq α} : a ∈ s → a ∈ cons y s := sorry

theorem eq_or_mem_of_mem_cons {α : Type u} {a : α} {b : α} {s : seq α} : a ∈ cons b s → a = b ∨ a ∈ s := sorry

@[simp] theorem mem_cons_iff {α : Type u} {a : α} {b : α} {s : seq α} : a ∈ cons b s ↔ a = b ∨ a ∈ s := sorry

/-- Destructor for a sequence, resulting in either `none` (for `nil`) or
  `some (a, s)` (for `cons a s`). -/
def destruct {α : Type u} (s : seq α) : Option (seq1 α) :=
  (fun (a' : α) => (a', tail s)) <$> nth s 0

theorem destruct_eq_nil {α : Type u} {s : seq α} : destruct s = none → s = nil := sorry

theorem destruct_eq_cons {α : Type u} {s : seq α} {a : α} {s' : seq α} : destruct s = some (a, s') → s = cons a s' := sorry

@[simp] theorem destruct_nil {α : Type u} : destruct nil = none :=
  rfl

@[simp] theorem destruct_cons {α : Type u} (a : α) (s : seq α) : destruct (cons a s) = some (a, s) := sorry

theorem head_eq_destruct {α : Type u} (s : seq α) : head s = prod.fst <$> destruct s := sorry

@[simp] theorem head_nil {α : Type u} : head nil = none :=
  rfl

@[simp] theorem head_cons {α : Type u} (a : α) (s : seq α) : head (cons a s) = some a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (head (cons a s) = some a)) (head_eq_destruct (cons a s))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (prod.fst <$> destruct (cons a s) = some a)) (destruct_cons a s)))
      (Eq.refl (prod.fst <$> some (a, s))))

@[simp] theorem tail_nil {α : Type u} : tail nil = nil :=
  rfl

@[simp] theorem tail_cons {α : Type u} (a : α) (s : seq α) : tail (cons a s) = s := sorry

def cases_on {α : Type u} {C : seq α → Sort v} (s : seq α) (h1 : C nil) (h2 : (x : α) → (s : seq α) → C (cons x s)) : C s :=
  (fun (_x : Option (seq1 α)) (H : destruct s = _x) =>
      Option.rec (fun (H : destruct s = none) => eq.mpr sorry h1)
        (fun (v : seq1 α) (H : destruct s = some v) =>
          prod.cases_on v (fun (a : α) (s' : seq α) (H : destruct s = some (a, s')) => eq.mpr sorry (h2 a s')) H)
        _x H)
    (destruct s) sorry

theorem mem_rec_on {α : Type u} {C : seq α → Prop} {a : α} {s : seq α} (M : a ∈ s) (h1 : ∀ (b : α) (s' : seq α), a = b ∨ C s' → C (cons b s')) : C s := sorry

def corec.F {α : Type u} {β : Type v} (f : β → Option (α × β)) : Option β → Option α × Option β :=
  sorry

/-- Corecursor for `seq α` as a coinductive type. Iterates `f` to produce new elements
  of the sequence until `none` is obtained. -/
def corec {α : Type u} {β : Type v} (f : β → Option (α × β)) (b : β) : seq α :=
  { val := stream.corec' sorry (some b), property := sorry }

@[simp] theorem corec_eq {α : Type u} {β : Type v} (f : β → Option (α × β)) (b : β) : destruct (corec f b) = omap (corec f) (f b) := sorry

/-- Embed a list as a sequence -/
def of_list {α : Type u} (l : List α) : seq α :=
  { val := list.nth l, property := sorry }

protected instance coe_list {α : Type u} : has_coe (List α) (seq α) :=
  has_coe.mk of_list

@[simp] def bisim_o {α : Type u} (R : seq α → seq α → Prop) : Option (seq1 α) → Option (seq1 α) → Prop :=
  sorry

def is_bisimulation {α : Type u} (R : seq α → seq α → Prop) :=
  ∀ {s₁ s₂ : seq α}, R s₁ s₂ → bisim_o R (destruct s₁) (destruct s₂)

theorem eq_of_bisim {α : Type u} (R : seq α → seq α → Prop) (bisim : is_bisimulation R) {s₁ : seq α} {s₂ : seq α} (r : R s₁ s₂) : s₁ = s₂ := sorry

theorem coinduction {α : Type u} {s₁ : seq α} {s₂ : seq α} : head s₁ = head s₂ → (∀ (β : Type u) (fr : seq α → β), fr s₁ = fr s₂ → fr (tail s₁) = fr (tail s₂)) → s₁ = s₂ := sorry

theorem coinduction2 {α : Type u} {β : Type v} (s : seq α) (f : seq α → seq β) (g : seq α → seq β) (H : ∀ (s : seq α), bisim_o (fun (s1 s2 : seq β) => ∃ (s : seq α), s1 = f s ∧ s2 = g s) (destruct (f s)) (destruct (g s))) : f s = g s := sorry

/-- Embed an infinite stream as a sequence -/
def of_stream {α : Type u} (s : stream α) : seq α :=
  { val := stream.map some s, property := sorry }

protected instance coe_stream {α : Type u} : has_coe (stream α) (seq α) :=
  has_coe.mk of_stream

/-- Embed a `lazy_list α` as a sequence. Note that even though this
  is non-meta, it will produce infinite sequences if used with
  cyclic `lazy_list`s created by meta constructions. -/
def of_lazy_list {α : Type u} : lazy_list α → seq α :=
  corec fun (l : lazy_list α) => sorry

protected instance coe_lazy_list {α : Type u} : has_coe (lazy_list α) (seq α) :=
  has_coe.mk of_lazy_list

/-- Translate a sequence into a `lazy_list`. Since `lazy_list` and `list`
  are isomorphic as non-meta types, this function is necessarily meta. -/
/-- Translate a sequence to a list. This function will run forever if
  run on an infinite sequence. -/
/-- The sequence of natural numbers some 0, some 1, ... -/
def nats : seq ℕ :=
  ↑stream.nats

@[simp] theorem nats_nth (n : ℕ) : nth nats n = some n :=
  rfl

/-- Append two sequences. If `s₁` is infinite, then `s₁ ++ s₂ = s₁`,
  otherwise it puts `s₂` at the location of the `nil` in `s₁`. -/
def append {α : Type u} (s₁ : seq α) (s₂ : seq α) : seq α :=
  corec (fun (_x : seq α × seq α) => sorry) (s₁, s₂)

/-- Map a function over a sequence. -/
def map {α : Type u} {β : Type v} (f : α → β) : seq α → seq β :=
  sorry

/-- Flatten a sequence of sequences. (It is required that the
  sequences be nonempty to ensure productivity; in the case
  of an infinite sequence of `nil`, the first element is never
  generated.) -/
def join {α : Type u} : seq (seq1 α) → seq α :=
  corec fun (S : seq (seq1 α)) => sorry

/-- Remove the first `n` elements from the sequence. -/
@[simp] def drop {α : Type u} (s : seq α) : ℕ → seq α :=
  sorry

/-- Take the first `n` elements of the sequence (producing a list) -/
def take {α : Type u} : ℕ → seq α → List α :=
  sorry

/-- Split a sequence at `n`, producing a finite initial segment
  and an infinite tail. -/
def split_at {α : Type u} : ℕ → seq α → List α × seq α :=
  sorry

/-- Combine two sequences with a function -/
def zip_with {α : Type u} {β : Type v} {γ : Type w} (f : α → β → γ) : seq α → seq β → seq γ :=
  sorry

theorem zip_with_nth_some {α : Type u} {β : Type v} {γ : Type w} {s : seq α} {s' : seq β} {n : ℕ} {a : α} {b : β} (s_nth_eq_some : nth s n = some a) (s_nth_eq_some' : nth s' n = some b) (f : α → β → γ) : nth (zip_with f s s') n = some (f a b) := sorry

theorem zip_with_nth_none {α : Type u} {β : Type v} {γ : Type w} {s : seq α} {s' : seq β} {n : ℕ} (s_nth_eq_none : nth s n = none) (f : α → β → γ) : nth (zip_with f s s') n = none := sorry

theorem zip_with_nth_none' {α : Type u} {β : Type v} {γ : Type w} {s : seq α} {s' : seq β} {n : ℕ} (s'_nth_eq_none : nth s' n = none) (f : α → β → γ) : nth (zip_with f s s') n = none := sorry

/-- Pair two sequences into a sequence of pairs -/
def zip {α : Type u} {β : Type v} : seq α → seq β → seq (α × β) :=
  zip_with Prod.mk

/-- Separate a sequence of pairs into two sequences -/
def unzip {α : Type u} {β : Type v} (s : seq (α × β)) : seq α × seq β :=
  (map prod.fst s, map prod.snd s)

/-- Convert a sequence which is known to terminate into a list -/
def to_list {α : Type u} (s : seq α) (h : ∃ (n : ℕ), ¬↥(option.is_some (nth s n))) : List α :=
  take (nat.find h) s

/-- Convert a sequence which is known not to terminate into a stream -/
def to_stream {α : Type u} (s : seq α) (h : ∀ (n : ℕ), ↥(option.is_some (nth s n))) : stream α :=
  fun (n : ℕ) => option.get (h n)

/-- Convert a sequence into either a list or a stream depending on whether
  it is finite or infinite. (Without decidability of the infiniteness predicate,
  this is not constructively possible.) -/
def to_list_or_stream {α : Type u} (s : seq α) [Decidable (∃ (n : ℕ), ¬↥(option.is_some (nth s n)))] : List α ⊕ stream α :=
  dite (∃ (n : ℕ), ¬↥(option.is_some (nth s n)))
    (fun (h : ∃ (n : ℕ), ¬↥(option.is_some (nth s n))) => sum.inl (to_list s h))
    fun (h : ¬∃ (n : ℕ), ¬↥(option.is_some (nth s n))) => sum.inr (to_stream s sorry)

@[simp] theorem nil_append {α : Type u} (s : seq α) : append nil s = s := sorry

@[simp] theorem cons_append {α : Type u} (a : α) (s : seq α) (t : seq α) : append (cons a s) t = cons a (append s t) := sorry

@[simp] theorem append_nil {α : Type u} (s : seq α) : append s nil = s := sorry

@[simp] theorem append_assoc {α : Type u} (s : seq α) (t : seq α) (u : seq α) : append (append s t) u = append s (append t u) := sorry

@[simp] theorem map_nil {α : Type u} {β : Type v} (f : α → β) : map f nil = nil :=
  rfl

@[simp] theorem map_cons {α : Type u} {β : Type v} (f : α → β) (a : α) (s : seq α) : map f (cons a s) = cons (f a) (map f s) := sorry

@[simp] theorem map_id {α : Type u} (s : seq α) : map id s = s := sorry

@[simp] theorem map_tail {α : Type u} {β : Type v} (f : α → β) (s : seq α) : map f (tail s) = tail (map f s) := sorry

theorem map_comp {α : Type u} {β : Type v} {γ : Type w} (f : α → β) (g : β → γ) (s : seq α) : map (g ∘ f) s = map g (map f s) := sorry

@[simp] theorem map_append {α : Type u} {β : Type v} (f : α → β) (s : seq α) (t : seq α) : map f (append s t) = append (map f s) (map f t) := sorry

@[simp] theorem map_nth {α : Type u} {β : Type v} (f : α → β) (s : seq α) (n : ℕ) : nth (map f s) n = option.map f (nth s n) := sorry

protected instance functor : Functor seq :=
  { map := map, mapConst := fun (α β : Type u_1) => map ∘ function.const β }

protected instance is_lawful_functor : is_lawful_functor seq :=
  is_lawful_functor.mk map_id map_comp

@[simp] theorem join_nil {α : Type u} : join nil = nil :=
  destruct_eq_nil rfl

@[simp] theorem join_cons_nil {α : Type u} (a : α) (S : seq (seq1 α)) : join (cons (a, nil) S) = cons a (join S) := sorry

@[simp] theorem join_cons_cons {α : Type u} (a : α) (b : α) (s : seq α) (S : seq (seq1 α)) : join (cons (a, cons b s) S) = cons a (join (cons (b, s) S)) := sorry

@[simp] theorem join_cons {α : Type u} (a : α) (s : seq α) (S : seq (seq1 α)) : join (cons (a, s) S) = cons a (append s (join S)) := sorry

@[simp] theorem join_append {α : Type u} (S : seq (seq1 α)) (T : seq (seq1 α)) : join (append S T) = append (join S) (join T) := sorry

@[simp] theorem of_list_nil {α : Type u} : of_list [] = nil :=
  rfl

@[simp] theorem of_list_cons {α : Type u} (a : α) (l : List α) : of_list (a :: l) = cons a (of_list l) := sorry

@[simp] theorem of_stream_cons {α : Type u} (a : α) (s : stream α) : of_stream (a :: s) = cons a (of_stream s) := sorry

@[simp] theorem of_list_append {α : Type u} (l : List α) (l' : List α) : of_list (l ++ l') = append (of_list l) (of_list l') := sorry

@[simp] theorem of_stream_append {α : Type u} (l : List α) (s : stream α) : of_stream (l++ₛs) = append (of_list l) (of_stream s) := sorry

/-- Convert a sequence into a list, embedded in a computation to allow for
  the possibility of infinite sequences (in which case the computation
  never returns anything). -/
def to_list' {α : Type u_1} (s : seq α) : computation (List α) :=
  computation.corec (fun (_x : List α × seq α) => sorry) ([], s)

theorem dropn_add {α : Type u} (s : seq α) (m : ℕ) (n : ℕ) : drop s (m + n) = drop (drop s m) n := sorry

theorem dropn_tail {α : Type u} (s : seq α) (n : ℕ) : drop (tail s) n = drop s (n + 1) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (drop (tail s) n = drop s (n + 1))) (add_comm n 1))) (Eq.symm (dropn_add s 1 n))

theorem nth_tail {α : Type u} (s : seq α) (n : ℕ) : nth (tail s) n = nth s (n + 1) := sorry

protected theorem ext {α : Type u} (s : seq α) (s' : seq α) (hyp : ∀ (n : ℕ), nth s n = nth s' n) : s = s' := sorry

@[simp] theorem head_dropn {α : Type u} (s : seq α) (n : ℕ) : head (drop s n) = nth s n := sorry

theorem mem_map {α : Type u} {β : Type v} (f : α → β) {a : α} {s : seq α} : a ∈ s → f a ∈ map f s := sorry

theorem exists_of_mem_map {α : Type u} {β : Type v} {f : α → β} {b : β} {s : seq α} : b ∈ map f s → ∃ (a : α), a ∈ s ∧ f a = b := sorry

theorem of_mem_append {α : Type u} {s₁ : seq α} {s₂ : seq α} {a : α} (h : a ∈ append s₁ s₂) : a ∈ s₁ ∨ a ∈ s₂ := sorry

theorem mem_append_left {α : Type u} {s₁ : seq α} {s₂ : seq α} {a : α} (h : a ∈ s₁) : a ∈ append s₁ s₂ := sorry

end seq


namespace seq1


/-- Convert a `seq1` to a sequence. -/
def to_seq {α : Type u} : seq1 α → seq α :=
  sorry

protected instance coe_seq {α : Type u} : has_coe (seq1 α) (seq α) :=
  has_coe.mk to_seq

/-- Map a function on a `seq1` -/
def map {α : Type u} {β : Type v} (f : α → β) : seq1 α → seq1 β :=
  sorry

theorem map_id {α : Type u} (s : seq1 α) : map id s = s := sorry

/-- Flatten a nonempty sequence of nonempty sequences -/
def join {α : Type u} : seq1 (seq1 α) → seq1 α :=
  sorry

@[simp] theorem join_nil {α : Type u} (a : α) (S : seq (seq1 α)) : join ((a, seq.nil), S) = (a, seq.join S) :=
  rfl

@[simp] theorem join_cons {α : Type u} (a : α) (b : α) (s : seq α) (S : seq (seq1 α)) : join ((a, seq.cons b s), S) = (a, seq.join (seq.cons (b, s) S)) := sorry

/-- The `return` operator for the `seq1` monad,
  which produces a singleton sequence. -/
def ret {α : Type u} (a : α) : seq1 α :=
  (a, seq.nil)

protected instance inhabited {α : Type u} [Inhabited α] : Inhabited (seq1 α) :=
  { default := ret Inhabited.default }

/-- The `bind` operator for the `seq1` monad,
  which maps `f` on each element of `s` and appends the results together.
  (Not all of `s` may be evaluated, because the first few elements of `s`
  may already produce an infinite result.) -/
def bind {α : Type u} {β : Type v} (s : seq1 α) (f : α → seq1 β) : seq1 β :=
  join (map f s)

@[simp] theorem join_map_ret {α : Type u} (s : seq α) : seq.join (seq.map ret s) = s := sorry

@[simp] theorem bind_ret {α : Type u} {β : Type v} (f : α → β) (s : seq1 α) : bind s (ret ∘ f) = map f s := sorry

@[simp] theorem ret_bind {α : Type u} {β : Type v} (a : α) (f : α → seq1 β) : bind (ret a) f = f a := sorry

@[simp] theorem map_join' {α : Type u} {β : Type v} (f : α → β) (S : seq (seq1 α)) : seq.map f (seq.join S) = seq.join (seq.map (map f) S) := sorry

@[simp] theorem map_join {α : Type u} {β : Type v} (f : α → β) (S : seq1 (seq1 α)) : map f (join S) = join (map (map f) S) := sorry

@[simp] theorem join_join {α : Type u} (SS : seq (seq1 (seq1 α))) : seq.join (seq.join SS) = seq.join (seq.map join SS) := sorry

@[simp] theorem bind_assoc {α : Type u} {β : Type v} {γ : Type w} (s : seq1 α) (f : α → seq1 β) (g : β → seq1 γ) : bind (bind s f) g = bind s fun (x : α) => bind (f x) g := sorry

protected instance monad : Monad seq1 :=
  { toApplicative :=
      { toFunctor := { map := map, mapConst := fun (α β : Type u_1) => map ∘ function.const β },
        toPure := { pure := ret },
        toSeq := { seq := fun (α β : Type u_1) (f : seq1 (α → β)) (x : seq1 α) => bind f fun (_x : α → β) => map _x x },
        toSeqLeft :=
          { seqLeft :=
              fun (α β : Type u_1) (a : seq1 α) (b : seq1 β) =>
                (fun (α β : Type u_1) (f : seq1 (α → β)) (x : seq1 α) => bind f fun (_x : α → β) => map _x x) β α
                  (map (function.const β) a) b },
        toSeqRight :=
          { seqRight :=
              fun (α β : Type u_1) (a : seq1 α) (b : seq1 β) =>
                (fun (α β : Type u_1) (f : seq1 (α → β)) (x : seq1 α) => bind f fun (_x : α → β) => map _x x) β β
                  (map (function.const α id) a) b } },
    toBind := { bind := bind } }

protected instance is_lawful_monad : is_lawful_monad seq1 :=
  is_lawful_monad.mk ret_bind bind_assoc

