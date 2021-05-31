/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.seq.seq
import Mathlib.Lean3Lib.data.dlist
import Mathlib.PostPort

universes u_1 u v w 

namespace Mathlib

/-
coinductive wseq (α : Type u) : Type u
| nil : wseq α
| cons : α → wseq α → wseq α
| think : wseq α → wseq α
-/

/-- Weak sequences.

  While the `seq` structure allows for lists which may not be finite,
  a weak sequence also allows the computation of each element to
  involve an indeterminate amount of computation, including possibly
  an infinite loop. This is represented as a regular `seq` interspersed
  with `none` elements to indicate that computation is ongoing.

  This model is appropriate for Haskell style lazy lists, and is closed
  under most interesting computation patterns on infinite lists,
  but conversely it is difficult to extract elements from it. -/
def wseq (α : Type u_1) :=
  seq (Option α)

namespace wseq


/-- Turn a sequence into a weak sequence -/
def of_seq {α : Type u} : seq α → wseq α :=
  Functor.map some

/-- Turn a list into a weak sequence -/
def of_list {α : Type u} (l : List α) : wseq α :=
  of_seq ↑l

/-- Turn a stream into a weak sequence -/
def of_stream {α : Type u} (l : stream α) : wseq α :=
  of_seq ↑l

protected instance coe_seq {α : Type u} : has_coe (seq α) (wseq α) :=
  has_coe.mk of_seq

protected instance coe_list {α : Type u} : has_coe (List α) (wseq α) :=
  has_coe.mk of_list

protected instance coe_stream {α : Type u} : has_coe (stream α) (wseq α) :=
  has_coe.mk of_stream

/-- The empty weak sequence -/
def nil {α : Type u} : wseq α :=
  seq.nil

protected instance inhabited {α : Type u} : Inhabited (wseq α) :=
  { default := nil }

/-- Prepend an element to a weak sequence -/
def cons {α : Type u} (a : α) : wseq α → wseq α :=
  seq.cons (some a)

/-- Compute for one tick, without producing any elements -/
def think {α : Type u} : wseq α → wseq α :=
  seq.cons none

/-- Destruct a weak sequence, to (eventually possibly) produce either
  `none` for `nil` or `some (a, s)` if an element is produced. -/
def destruct {α : Type u} : wseq α → computation (Option (α × wseq α)) :=
  computation.corec fun (s : wseq α) => sorry

def cases_on {α : Type u} {C : wseq α → Sort v} (s : wseq α) (h1 : C nil) (h2 : (x : α) → (s : wseq α) → C (cons x s)) (h3 : (s : wseq α) → C (think s)) : C s :=
  seq.cases_on s h1 fun (o : Option α) => option.cases_on o h3 h2

protected def mem {α : Type u} (a : α) (s : wseq α) :=
  seq.mem (some a) s

protected instance has_mem {α : Type u} : has_mem α (wseq α) :=
  has_mem.mk wseq.mem

theorem not_mem_nil {α : Type u} (a : α) : ¬a ∈ nil :=
  seq.not_mem_nil ↑a

/-- Get the head of a weak sequence. This involves a possibly
  infinite computation. -/
def head {α : Type u} (s : wseq α) : computation (Option α) :=
  computation.map (Functor.map prod.fst) (destruct s)

/-- Encode a computation yielding a weak sequence into additional
  `think` constructors in a weak sequence -/
def flatten {α : Type u} : computation (wseq α) → wseq α :=
  seq.corec fun (c : computation (wseq α)) => sorry

/-- Get the tail of a weak sequence. This doesn't need a `computation`
  wrapper, unlike `head`, because `flatten` allows us to hide this
  in the construction of the weak sequence itself. -/
def tail {α : Type u} (s : wseq α) : wseq α :=
  flatten ((fun (o : Option (α × wseq α)) => option.rec_on o nil prod.snd) <$> destruct s)

/-- drop the first `n` elements from `s`. -/
@[simp] def drop {α : Type u} (s : wseq α) : ℕ → wseq α :=
  sorry

/-- Get the nth element of `s`. -/
def nth {α : Type u} (s : wseq α) (n : ℕ) : computation (Option α) :=
  head (drop s n)

/-- Convert `s` to a list (if it is finite and completes in finite time). -/
def to_list {α : Type u} (s : wseq α) : computation (List α) :=
  computation.corec (fun (_x : List α × wseq α) => sorry) ([], s)

/-- Get the length of `s` (if it is finite and completes in finite time). -/
def length {α : Type u} (s : wseq α) : computation ℕ :=
  computation.corec (fun (_x : ℕ × wseq α) => sorry) (0, s)

/-- A weak sequence is finite if `to_list s` terminates. Equivalently,
  it is a finite number of `think` and `cons` applied to `nil`. -/
def is_finite {α : Type u} (s : wseq α) :=
  computation.terminates (to_list s)

protected instance to_list_terminates {α : Type u} (s : wseq α) [h : is_finite s] : computation.terminates (to_list s) :=
  h

/-- Get the list corresponding to a finite weak sequence. -/
def get {α : Type u} (s : wseq α) [is_finite s] : List α :=
  computation.get (to_list s)

/-- A weak sequence is *productive* if it never stalls forever - there are
 always a finite number of `think`s between `cons` constructors.
 The sequence itself is allowed to be infinite though. -/
def productive {α : Type u} (s : wseq α) :=
  ∀ (n : ℕ), computation.terminates (nth s n)

protected instance nth_terminates {α : Type u} (s : wseq α) [h : productive s] (n : ℕ) : computation.terminates (nth s n) :=
  h

protected instance head_terminates {α : Type u} (s : wseq α) [h : productive s] : computation.terminates (head s) :=
  h 0

/-- Replace the `n`th element of `s` with `a`. -/
def update_nth {α : Type u} (s : wseq α) (n : ℕ) (a : α) : wseq α :=
  seq.corec (fun (_x : ℕ × wseq α) => sorry) (n + 1, s)

/-- Remove the `n`th element of `s`. -/
def remove_nth {α : Type u} (s : wseq α) (n : ℕ) : wseq α :=
  seq.corec (fun (_x : ℕ × wseq α) => sorry) (n + 1, s)

/-- Map the elements of `s` over `f`, removing any values that yield `none`. -/
def filter_map {α : Type u} {β : Type v} (f : α → Option β) : wseq α → wseq β :=
  seq.corec fun (s : wseq α) => sorry

/-- Select the elements of `s` that satisfy `p`. -/
def filter {α : Type u} (p : α → Prop) [decidable_pred p] : wseq α → wseq α :=
  filter_map fun (a : α) => ite (p a) (some a) none

-- example of infinite list manipulations

/-- Get the first element of `s` satisfying `p`. -/
def find {α : Type u} (p : α → Prop) [decidable_pred p] (s : wseq α) : computation (Option α) :=
  head (filter p s)

/-- Zip a function over two weak sequences -/
def zip_with {α : Type u} {β : Type v} {γ : Type w} (f : α → β → γ) (s1 : wseq α) (s2 : wseq β) : wseq γ :=
  seq.corec (fun (_x : wseq α × wseq β) => sorry) (s1, s2)

/-- Zip two weak sequences into a single sequence of pairs -/
def zip {α : Type u} {β : Type v} : wseq α → wseq β → wseq (α × β) :=
  zip_with Prod.mk

/-- Get the list of indexes of elements of `s` satisfying `p` -/
def find_indexes {α : Type u} (p : α → Prop) [decidable_pred p] (s : wseq α) : wseq ℕ :=
  filter_map (fun (_x : α × ℕ) => sorry) (zip s ↑stream.nats)

/-- Get the index of the first element of `s` satisfying `p` -/
def find_index {α : Type u} (p : α → Prop) [decidable_pred p] (s : wseq α) : computation ℕ :=
  (fun (o : Option ℕ) => option.get_or_else o 0) <$> head (find_indexes p s)

/-- Get the index of the first occurrence of `a` in `s` -/
def index_of {α : Type u} [DecidableEq α] (a : α) : wseq α → computation ℕ :=
  find_index (Eq a)

/-- Get the indexes of occurrences of `a` in `s` -/
def indexes_of {α : Type u} [DecidableEq α] (a : α) : wseq α → wseq ℕ :=
  find_indexes (Eq a)

/-- `union s1 s2` is a weak sequence which interleaves `s1` and `s2` in
  some order (nondeterministically). -/
def union {α : Type u} (s1 : wseq α) (s2 : wseq α) : wseq α :=
  seq.corec (fun (_x : wseq α × wseq α) => sorry) (s1, s2)

/-- Returns `tt` if `s` is `nil` and `ff` if `s` has an element -/
def is_empty {α : Type u} (s : wseq α) : computation Bool :=
  computation.map option.is_none (head s)

/-- Calculate one step of computation -/
def compute {α : Type u} (s : wseq α) : wseq α :=
  sorry

/-- Get the first `n` elements of a weak sequence -/
def take {α : Type u} (s : wseq α) (n : ℕ) : wseq α :=
  seq.corec (fun (_x : ℕ × wseq α) => sorry) (n, s)

/-- Split the sequence at position `n` into a finite initial segment
  and the weak sequence tail -/
def split_at {α : Type u} (s : wseq α) (n : ℕ) : computation (List α × wseq α) :=
  computation.corec (fun (_x : ℕ × List α × wseq α) => sorry) (n, [], s)

/-- Returns `tt` if any element of `s` satisfies `p` -/
def any {α : Type u} (s : wseq α) (p : α → Bool) : computation Bool :=
  computation.corec (fun (s : wseq α) => sorry) s

/-- Returns `tt` if every element of `s` satisfies `p` -/
def all {α : Type u} (s : wseq α) (p : α → Bool) : computation Bool :=
  computation.corec (fun (s : wseq α) => sorry) s

/-- Apply a function to the elements of the sequence to produce a sequence
  of partial results. (There is no `scanr` because this would require
  working from the end of the sequence, which may not exist.) -/
def scanl {α : Type u} {β : Type v} (f : α → β → α) (a : α) (s : wseq β) : wseq α :=
  cons a (seq.corec (fun (_x : α × wseq β) => sorry) (a, s))

/-- Get the weak sequence of initial segments of the input sequence -/
def inits {α : Type u} (s : wseq α) : wseq (List α) :=
  cons [] (seq.corec (fun (_x : dlist α × wseq α) => sorry) (dlist.empty, s))

/-- Like take, but does not wait for a result. Calculates `n` steps of
  computation and returns the sequence computed so far -/
def collect {α : Type u} (s : wseq α) (n : ℕ) : List α :=
  list.filter_map id (seq.take n s)

/-- Append two weak sequences. As with `seq.append`, this may not use
  the second sequence if the first one takes forever to compute -/
def append {α : Type u} : wseq α → wseq α → wseq α :=
  seq.append

/-- Map a function over a weak sequence -/
def map {α : Type u} {β : Type v} (f : α → β) : wseq α → wseq β :=
  seq.map (option.map f)

/-- Flatten a sequence of weak sequences. (Note that this allows
  empty sequences, unlike `seq.join`.) -/
def join {α : Type u} (S : wseq (wseq α)) : wseq α :=
  seq.join ((fun (o : Option (wseq α)) => sorry) <$> S)

/-- Monadic bind operator for weak sequences -/
def bind {α : Type u} {β : Type v} (s : wseq α) (f : α → wseq β) : wseq β :=
  join (map f s)

@[simp] def lift_rel_o {α : Type u} {β : Type v} (R : α → β → Prop) (C : wseq α → wseq β → Prop) : Option (α × wseq α) → Option (β × wseq β) → Prop :=
  sorry

theorem lift_rel_o.imp {α : Type u} {β : Type v} {R : α → β → Prop} {S : α → β → Prop} {C : wseq α → wseq β → Prop} {D : wseq α → wseq β → Prop} (H1 : ∀ (a : α) (b : β), R a b → S a b) (H2 : ∀ (s : wseq α) (t : wseq β), C s t → D s t) {o : Option (α × wseq α)} {p : Option (β × wseq β)} : lift_rel_o R C o p → lift_rel_o S D o p := sorry

theorem lift_rel_o.imp_right {α : Type u} {β : Type v} (R : α → β → Prop) {C : wseq α → wseq β → Prop} {D : wseq α → wseq β → Prop} (H : ∀ (s : wseq α) (t : wseq β), C s t → D s t) {o : Option (α × wseq α)} {p : Option (β × wseq β)} : lift_rel_o R C o p → lift_rel_o R D o p :=
  lift_rel_o.imp (fun (_x : α) (_x_1 : β) => id) H

@[simp] def bisim_o {α : Type u} (R : wseq α → wseq α → Prop) : Option (α × wseq α) → Option (α × wseq α) → Prop :=
  lift_rel_o Eq R

theorem bisim_o.imp {α : Type u} {R : wseq α → wseq α → Prop} {S : wseq α → wseq α → Prop} (H : ∀ (s t : wseq α), R s t → S s t) {o : Option (α × wseq α)} {p : Option (α × wseq α)} : bisim_o R o p → bisim_o S o p :=
  lift_rel_o.imp_right Eq H

/-- Two weak sequences are `lift_rel R` related if they are either both empty,
  or they are both nonempty and the heads are `R` related and the tails are
  `lift_rel R` related. (This is a coinductive definition.) -/
def lift_rel {α : Type u} {β : Type v} (R : α → β → Prop) (s : wseq α) (t : wseq β) :=
  ∃ (C : wseq α → wseq β → Prop),
    C s t ∧ ∀ {s : wseq α} {t : wseq β}, C s t → computation.lift_rel (lift_rel_o R C) (destruct s) (destruct t)

/-- If two sequences are equivalent, then they have the same values and
  the same computational behavior (i.e. if one loops forever then so does
  the other), although they may differ in the number of `think`s needed to
  arrive at the answer. -/
def equiv {α : Type u} : wseq α → wseq α → Prop :=
  lift_rel Eq

theorem lift_rel_destruct {α : Type u} {β : Type v} {R : α → β → Prop} {s : wseq α} {t : wseq β} : lift_rel R s t → computation.lift_rel (lift_rel_o R (lift_rel R)) (destruct s) (destruct t) := sorry

theorem lift_rel_destruct_iff {α : Type u} {β : Type v} {R : α → β → Prop} {s : wseq α} {t : wseq β} : lift_rel R s t ↔ computation.lift_rel (lift_rel_o R (lift_rel R)) (destruct s) (destruct t) := sorry

infixl:50 " ~ " => Mathlib.wseq.equiv

theorem destruct_congr {α : Type u} {s : wseq α} {t : wseq α} : s ~ t → computation.lift_rel (bisim_o equiv) (destruct s) (destruct t) :=
  lift_rel_destruct

theorem destruct_congr_iff {α : Type u} {s : wseq α} {t : wseq α} : s ~ t ↔ computation.lift_rel (bisim_o equiv) (destruct s) (destruct t) :=
  lift_rel_destruct_iff

theorem lift_rel.refl {α : Type u} (R : α → α → Prop) (H : reflexive R) : reflexive (lift_rel R) := sorry

theorem lift_rel_o.swap {α : Type u} {β : Type v} (R : α → β → Prop) (C : wseq α → wseq β → Prop) : function.swap (lift_rel_o R C) = lift_rel_o (function.swap R) (function.swap C) := sorry

theorem lift_rel.swap_lem {α : Type u} {β : Type v} {R : α → β → Prop} {s1 : wseq α} {s2 : wseq β} (h : lift_rel R s1 s2) : lift_rel (function.swap R) s2 s1 := sorry

theorem lift_rel.swap {α : Type u} {β : Type v} (R : α → β → Prop) : function.swap (lift_rel R) = lift_rel (function.swap R) :=
  funext fun (x : wseq β) => funext fun (y : wseq α) => propext { mp := lift_rel.swap_lem, mpr := lift_rel.swap_lem }

theorem lift_rel.symm {α : Type u} (R : α → α → Prop) (H : symmetric R) : symmetric (lift_rel R) := sorry

theorem lift_rel.trans {α : Type u} (R : α → α → Prop) (H : transitive R) : transitive (lift_rel R) := sorry

theorem lift_rel.equiv {α : Type u} (R : α → α → Prop) : equivalence R → equivalence (lift_rel R) := sorry

theorem equiv.refl {α : Type u} (s : wseq α) : s ~ s :=
  lift_rel.refl Eq Eq.refl

theorem equiv.symm {α : Type u} {s : wseq α} {t : wseq α} : s ~ t → t ~ s :=
  lift_rel.symm Eq Eq.symm

theorem equiv.trans {α : Type u} {s : wseq α} {t : wseq α} {u : wseq α} : s ~ t → t ~ u → s ~ u :=
  lift_rel.trans Eq Eq.trans

theorem equiv.equivalence {α : Type u} : equivalence equiv :=
  { left := equiv.refl, right := { left := equiv.symm, right := equiv.trans } }

@[simp] theorem destruct_nil {α : Type u} : destruct nil = computation.return none :=
  computation.destruct_eq_ret rfl

@[simp] theorem destruct_cons {α : Type u} (a : α) (s : wseq α) : destruct (cons a s) = computation.return (some (a, s)) := sorry

@[simp] theorem destruct_think {α : Type u} (s : wseq α) : destruct (think s) = computation.think (destruct s) := sorry

@[simp] theorem seq_destruct_nil {α : Type u} : seq.destruct nil = none :=
  seq.destruct_nil

@[simp] theorem seq_destruct_cons {α : Type u} (a : α) (s : wseq α) : seq.destruct (cons a s) = some (some a, s) :=
  seq.destruct_cons (some a) s

@[simp] theorem seq_destruct_think {α : Type u} (s : wseq α) : seq.destruct (think s) = some (none, s) :=
  seq.destruct_cons none s

@[simp] theorem head_nil {α : Type u} : head nil = computation.return none := sorry

@[simp] theorem head_cons {α : Type u} (a : α) (s : wseq α) : head (cons a s) = computation.return (some a) := sorry

@[simp] theorem head_think {α : Type u} (s : wseq α) : head (think s) = computation.think (head s) := sorry

@[simp] theorem flatten_ret {α : Type u} (s : wseq α) : flatten (computation.return s) = s := sorry

@[simp] theorem flatten_think {α : Type u} (c : computation (wseq α)) : flatten (computation.think c) = think (flatten c) := sorry

@[simp] theorem destruct_flatten {α : Type u} (c : computation (wseq α)) : destruct (flatten c) = c >>= destruct := sorry

theorem head_terminates_iff {α : Type u} (s : wseq α) : computation.terminates (head s) ↔ computation.terminates (destruct s) :=
  computation.terminates_map_iff (Functor.map prod.fst) (destruct s)

@[simp] theorem tail_nil {α : Type u} : tail nil = nil := sorry

@[simp] theorem tail_cons {α : Type u} (a : α) (s : wseq α) : tail (cons a s) = s := sorry

@[simp] theorem tail_think {α : Type u} (s : wseq α) : tail (think s) = think (tail s) := sorry

@[simp] theorem dropn_nil {α : Type u} (n : ℕ) : drop nil n = nil := sorry

@[simp] theorem dropn_cons {α : Type u} (a : α) (s : wseq α) (n : ℕ) : drop (cons a s) (n + 1) = drop s n := sorry

@[simp] theorem dropn_think {α : Type u} (s : wseq α) (n : ℕ) : drop (think s) n = think (drop s n) := sorry

theorem dropn_add {α : Type u} (s : wseq α) (m : ℕ) (n : ℕ) : drop s (m + n) = drop (drop s m) n := sorry

theorem dropn_tail {α : Type u} (s : wseq α) (n : ℕ) : drop (tail s) n = drop s (n + 1) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (drop (tail s) n = drop s (n + 1))) (add_comm n 1))) (Eq.symm (dropn_add s 1 n))

theorem nth_add {α : Type u} (s : wseq α) (m : ℕ) (n : ℕ) : nth s (m + n) = nth (drop s m) n :=
  congr_arg head (dropn_add s m n)

theorem nth_tail {α : Type u} (s : wseq α) (n : ℕ) : nth (tail s) n = nth s (n + 1) :=
  congr_arg head (dropn_tail s n)

@[simp] theorem join_nil {α : Type u} : join nil = nil :=
  seq.join_nil

@[simp] theorem join_think {α : Type u} (S : wseq (wseq α)) : join (think S) = think (join S) := sorry

@[simp] theorem join_cons {α : Type u} (s : wseq α) (S : wseq (wseq α)) : join (cons s S) = think (append s (join S)) := sorry

@[simp] theorem nil_append {α : Type u} (s : wseq α) : append nil s = s :=
  seq.nil_append s

@[simp] theorem cons_append {α : Type u} (a : α) (s : wseq α) (t : wseq α) : append (cons a s) t = cons a (append s t) :=
  seq.cons_append (some a) s t

@[simp] theorem think_append {α : Type u} (s : wseq α) (t : wseq α) : append (think s) t = think (append s t) :=
  seq.cons_append none s t

@[simp] theorem append_nil {α : Type u} (s : wseq α) : append s nil = s :=
  seq.append_nil s

@[simp] theorem append_assoc {α : Type u} (s : wseq α) (t : wseq α) (u : wseq α) : append (append s t) u = append s (append t u) :=
  seq.append_assoc s t u

@[simp] def tail.aux {α : Type u} : Option (α × wseq α) → computation (Option (α × wseq α)) :=
  sorry

theorem destruct_tail {α : Type u} (s : wseq α) : destruct (tail s) = destruct s >>= tail.aux := sorry

@[simp] def drop.aux {α : Type u} : ℕ → Option (α × wseq α) → computation (Option (α × wseq α)) :=
  sorry

theorem drop.aux_none {α : Type u} (n : ℕ) : drop.aux n none = computation.return none := sorry

theorem destruct_dropn {α : Type u} (s : wseq α) (n : ℕ) : destruct (drop s n) = destruct s >>= drop.aux n := sorry

theorem head_terminates_of_head_tail_terminates {α : Type u} (s : wseq α) [T : computation.terminates (head (tail s))] : computation.terminates (head s) := sorry

theorem destruct_some_of_destruct_tail_some {α : Type u} {s : wseq α} {a : α × wseq α} (h : some a ∈ destruct (tail s)) : ∃ (a' : α × wseq α), some a' ∈ destruct s := sorry

theorem head_some_of_head_tail_some {α : Type u} {s : wseq α} {a : α} (h : some a ∈ head (tail s)) : ∃ (a' : α), some a' ∈ head s := sorry

theorem head_some_of_nth_some {α : Type u} {s : wseq α} {a : α} {n : ℕ} (h : some a ∈ nth s n) : ∃ (a' : α), some a' ∈ head s := sorry

protected instance productive_tail {α : Type u} (s : wseq α) [productive s] : productive (tail s) :=
  fun (n : ℕ) =>
    eq.mpr (id (Eq._oldrec (Eq.refl (computation.terminates (nth (tail s) n))) (nth_tail s n)))
      (wseq.nth_terminates s (n + 1))

protected instance productive_dropn {α : Type u} (s : wseq α) [productive s] (n : ℕ) : productive (drop s n) :=
  fun (m : ℕ) =>
    eq.mpr (id (Eq._oldrec (Eq.refl (computation.terminates (nth (drop s n) m))) (Eq.symm (nth_add s n m))))
      (wseq.nth_terminates s (n + m))

/-- Given a productive weak sequence, we can collapse all the `think`s to
  produce a sequence. -/
def to_seq {α : Type u} (s : wseq α) [productive s] : seq α :=
  { val := fun (n : ℕ) => computation.get (nth s n), property := sorry }

theorem nth_terminates_le {α : Type u} {s : wseq α} {m : ℕ} {n : ℕ} (h : m ≤ n) : computation.terminates (nth s n) → computation.terminates (nth s m) := sorry

theorem head_terminates_of_nth_terminates {α : Type u} {s : wseq α} {n : ℕ} : computation.terminates (nth s n) → computation.terminates (head s) :=
  nth_terminates_le (nat.zero_le n)

theorem destruct_terminates_of_nth_terminates {α : Type u} {s : wseq α} {n : ℕ} (T : computation.terminates (nth s n)) : computation.terminates (destruct s) :=
  iff.mp (head_terminates_iff s) (head_terminates_of_nth_terminates T)

theorem mem_rec_on {α : Type u} {C : wseq α → Prop} {a : α} {s : wseq α} (M : a ∈ s) (h1 : ∀ (b : α) (s' : wseq α), a = b ∨ C s' → C (cons b s')) (h2 : ∀ (s : wseq α), C s → C (think s)) : C s := sorry

@[simp] theorem mem_think {α : Type u} (s : wseq α) (a : α) : a ∈ think s ↔ a ∈ s := sorry

theorem eq_or_mem_iff_mem {α : Type u} {s : wseq α} {a : α} {a' : α} {s' : wseq α} : some (a', s') ∈ destruct s → (a ∈ s ↔ a = a' ∨ a ∈ s') := sorry

@[simp] theorem mem_cons_iff {α : Type u} (s : wseq α) (b : α) {a : α} : a ∈ cons b s ↔ a = b ∨ a ∈ s := sorry

theorem mem_cons_of_mem {α : Type u} {s : wseq α} (b : α) {a : α} (h : a ∈ s) : a ∈ cons b s :=
  iff.mpr (mem_cons_iff s b) (Or.inr h)

theorem mem_cons {α : Type u} (s : wseq α) (a : α) : a ∈ cons a s :=
  iff.mpr (mem_cons_iff s a) (Or.inl rfl)

theorem mem_of_mem_tail {α : Type u} {s : wseq α} {a : α} : a ∈ tail s → a ∈ s := sorry

theorem mem_of_mem_dropn {α : Type u} {s : wseq α} {a : α} {n : ℕ} : a ∈ drop s n → a ∈ s := sorry

theorem nth_mem {α : Type u} {s : wseq α} {a : α} {n : ℕ} : some a ∈ nth s n → a ∈ s := sorry

theorem exists_nth_of_mem {α : Type u} {s : wseq α} {a : α} (h : a ∈ s) : ∃ (n : ℕ), some a ∈ nth s n := sorry

theorem exists_dropn_of_mem {α : Type u} {s : wseq α} {a : α} (h : a ∈ s) : ∃ (n : ℕ), ∃ (s' : wseq α), some (a, s') ∈ destruct (drop s n) := sorry

theorem lift_rel_dropn_destruct {α : Type u} {β : Type v} {R : α → β → Prop} {s : wseq α} {t : wseq β} (H : lift_rel R s t) (n : ℕ) : computation.lift_rel (lift_rel_o R (lift_rel R)) (destruct (drop s n)) (destruct (drop t n)) := sorry

theorem exists_of_lift_rel_left {α : Type u} {β : Type v} {R : α → β → Prop} {s : wseq α} {t : wseq β} (H : lift_rel R s t) {a : α} (h : a ∈ s) : Exists fun {b : β} => b ∈ t ∧ R a b := sorry

theorem exists_of_lift_rel_right {α : Type u} {β : Type v} {R : α → β → Prop} {s : wseq α} {t : wseq β} (H : lift_rel R s t) {b : β} (h : b ∈ t) : Exists fun {a : α} => a ∈ s ∧ R a b :=
  exists_of_lift_rel_left
    (eq.mp (Eq._oldrec (Eq.refl (lift_rel R s t)) (Eq.symm (lift_rel.swap fun (x : β) (y : α) => R y x))) H) h

theorem head_terminates_of_mem {α : Type u} {s : wseq α} {a : α} (h : a ∈ s) : computation.terminates (head s) := sorry

theorem of_mem_append {α : Type u} {s₁ : wseq α} {s₂ : wseq α} {a : α} : a ∈ append s₁ s₂ → a ∈ s₁ ∨ a ∈ s₂ :=
  seq.of_mem_append

theorem mem_append_left {α : Type u} {s₁ : wseq α} {s₂ : wseq α} {a : α} : a ∈ s₁ → a ∈ append s₁ s₂ :=
  seq.mem_append_left

theorem exists_of_mem_map {α : Type u} {β : Type v} {f : α → β} {b : β} {s : wseq α} : b ∈ map f s → ∃ (a : α), a ∈ s ∧ f a = b := sorry

@[simp] theorem lift_rel_nil {α : Type u} {β : Type v} (R : α → β → Prop) : lift_rel R nil nil := sorry

@[simp] theorem lift_rel_cons {α : Type u} {β : Type v} (R : α → β → Prop) (a : α) (b : β) (s : wseq α) (t : wseq β) : lift_rel R (cons a s) (cons b t) ↔ R a b ∧ lift_rel R s t := sorry

@[simp] theorem lift_rel_think_left {α : Type u} {β : Type v} (R : α → β → Prop) (s : wseq α) (t : wseq β) : lift_rel R (think s) t ↔ lift_rel R s t := sorry

@[simp] theorem lift_rel_think_right {α : Type u} {β : Type v} (R : α → β → Prop) (s : wseq α) (t : wseq β) : lift_rel R s (think t) ↔ lift_rel R s t := sorry

theorem cons_congr {α : Type u} {s : wseq α} {t : wseq α} (a : α) (h : s ~ t) : cons a s ~ cons a t := sorry

theorem think_equiv {α : Type u} (s : wseq α) : think s ~ s :=
  eq.mpr (id (congr_fun (congr_fun equiv.equations._eqn_1 (think s)) s))
    (eq.mpr (id (propext (lift_rel_think_left Eq s s))) (equiv.refl s))

theorem think_congr {α : Type u} {s : wseq α} {t : wseq α} (a : α) (h : s ~ t) : think s ~ think t :=
  eq.mpr (id (congr_fun (congr_fun equiv.equations._eqn_1 (think s)) (think t)))
    (eq.mpr (id (Eq.trans (propext (lift_rel_think_right Eq (think s) t)) (propext (lift_rel_think_left Eq s t)))) h)

theorem head_congr {α : Type u} {s : wseq α} {t : wseq α} : s ~ t → head s ~ head t := sorry

theorem flatten_equiv {α : Type u} {c : computation (wseq α)} {s : wseq α} (h : s ∈ c) : flatten c ~ s := sorry

theorem lift_rel_flatten {α : Type u} {β : Type v} {R : α → β → Prop} {c1 : computation (wseq α)} {c2 : computation (wseq β)} (h : computation.lift_rel (lift_rel R) c1 c2) : lift_rel R (flatten c1) (flatten c2) := sorry

theorem flatten_congr {α : Type u} {c1 : computation (wseq α)} {c2 : computation (wseq α)} : computation.lift_rel equiv c1 c2 → flatten c1 ~ flatten c2 :=
  lift_rel_flatten

theorem tail_congr {α : Type u} {s : wseq α} {t : wseq α} (h : s ~ t) : tail s ~ tail t := sorry

theorem dropn_congr {α : Type u} {s : wseq α} {t : wseq α} (h : s ~ t) (n : ℕ) : drop s n ~ drop t n := sorry

theorem nth_congr {α : Type u} {s : wseq α} {t : wseq α} (h : s ~ t) (n : ℕ) : nth s n ~ nth t n :=
  head_congr (dropn_congr h n)

theorem mem_congr {α : Type u} {s : wseq α} {t : wseq α} (h : s ~ t) (a : α) : a ∈ s ↔ a ∈ t := sorry

theorem productive_congr {α : Type u} {s : wseq α} {t : wseq α} (h : s ~ t) : productive s ↔ productive t :=
  forall_congr fun (n : ℕ) => computation.terminates_congr (nth_congr h n)

theorem equiv.ext {α : Type u} {s : wseq α} {t : wseq α} (h : ∀ (n : ℕ), nth s n ~ nth t n) : s ~ t := sorry

theorem length_eq_map {α : Type u} (s : wseq α) : length s = computation.map list.length (to_list s) := sorry

@[simp] theorem of_list_nil {α : Type u} : of_list [] = nil :=
  rfl

@[simp] theorem of_list_cons {α : Type u} (a : α) (l : List α) : of_list (a :: l) = cons a (of_list l) := sorry

@[simp] theorem to_list'_nil {α : Type u} (l : List α) : computation.corec to_list._match_2 (l, nil) = computation.return (list.reverse l) :=
  computation.destruct_eq_ret rfl

@[simp] theorem to_list'_cons {α : Type u} (l : List α) (s : wseq α) (a : α) : computation.corec to_list._match_2 (l, cons a s) = computation.think (computation.corec to_list._match_2 (a :: l, s)) := sorry

@[simp] theorem to_list'_think {α : Type u} (l : List α) (s : wseq α) : computation.corec to_list._match_2 (l, think s) = computation.think (computation.corec to_list._match_2 (l, s)) := sorry

theorem to_list'_map {α : Type u} (l : List α) (s : wseq α) : computation.corec to_list._match_2 (l, s) = append (list.reverse l) <$> to_list s := sorry

@[simp] theorem to_list_cons {α : Type u} (a : α) (s : wseq α) : to_list (cons a s) = computation.think (List.cons a <$> to_list s) := sorry

@[simp] theorem to_list_nil {α : Type u} : to_list nil = computation.return [] :=
  computation.destruct_eq_ret rfl

theorem to_list_of_list {α : Type u} (l : List α) : l ∈ to_list (of_list l) := sorry

@[simp] theorem destruct_of_seq {α : Type u} (s : seq α) : destruct (of_seq s) = computation.return (option.map (fun (a : α) => (a, of_seq (seq.tail s))) (seq.head s)) := sorry

@[simp] theorem head_of_seq {α : Type u} (s : seq α) : head (of_seq s) = computation.return (seq.head s) := sorry

@[simp] theorem tail_of_seq {α : Type u} (s : seq α) : tail (of_seq s) = of_seq (seq.tail s) := sorry

@[simp] theorem dropn_of_seq {α : Type u} (s : seq α) (n : ℕ) : drop (of_seq s) n = of_seq (seq.drop s n) := sorry

theorem nth_of_seq {α : Type u} (s : seq α) (n : ℕ) : nth (of_seq s) n = computation.return (seq.nth s n) := sorry

protected instance productive_of_seq {α : Type u} (s : seq α) : productive (of_seq s) :=
  fun (n : ℕ) =>
    eq.mpr (id (Eq._oldrec (Eq.refl (computation.terminates (nth (of_seq s) n))) (nth_of_seq s n)))
      (computation.ret_terminates (seq.nth s n))

theorem to_seq_of_seq {α : Type u} (s : seq α) : to_seq (of_seq s) = s := sorry

/-- The monadic `return a` is a singleton list containing `a`. -/
def ret {α : Type u} (a : α) : wseq α :=
  of_list [a]

@[simp] theorem map_nil {α : Type u} {β : Type v} (f : α → β) : map f nil = nil :=
  rfl

@[simp] theorem map_cons {α : Type u} {β : Type v} (f : α → β) (a : α) (s : wseq α) : map f (cons a s) = cons (f a) (map f s) :=
  seq.map_cons (option.map f) (some a) s

@[simp] theorem map_think {α : Type u} {β : Type v} (f : α → β) (s : wseq α) : map f (think s) = think (map f s) :=
  seq.map_cons (option.map f) none s

@[simp] theorem map_id {α : Type u} (s : wseq α) : map id s = s := sorry

@[simp] theorem map_ret {α : Type u} {β : Type v} (f : α → β) (a : α) : map f (ret a) = ret (f a) := sorry

@[simp] theorem map_append {α : Type u} {β : Type v} (f : α → β) (s : wseq α) (t : wseq α) : map f (append s t) = append (map f s) (map f t) :=
  seq.map_append (option.map f) s t

theorem map_comp {α : Type u} {β : Type v} {γ : Type w} (f : α → β) (g : β → γ) (s : wseq α) : map (g ∘ f) s = map g (map f s) := sorry

theorem mem_map {α : Type u} {β : Type v} (f : α → β) {a : α} {s : wseq α} : a ∈ s → f a ∈ map f s :=
  seq.mem_map (option.map f)

-- The converse is not true without additional assumptions

theorem exists_of_mem_join {α : Type u} {a : α} {S : wseq (wseq α)} : a ∈ join S → ∃ (s : wseq α), s ∈ S ∧ a ∈ s := sorry

theorem exists_of_mem_bind {α : Type u} {β : Type v} {s : wseq α} {f : α → wseq β} {b : β} (h : b ∈ bind s f) : ∃ (a : α), ∃ (H : a ∈ s), b ∈ f a := sorry

theorem destruct_map {α : Type u} {β : Type v} (f : α → β) (s : wseq α) : destruct (map f s) = computation.map (option.map (prod.map f (map f))) (destruct s) := sorry

theorem lift_rel_map {α : Type u} {β : Type v} {γ : Type w} {δ : Type u_1} (R : α → β → Prop) (S : γ → δ → Prop) {s1 : wseq α} {s2 : wseq β} {f1 : α → γ} {f2 : β → δ} (h1 : lift_rel R s1 s2) (h2 : ∀ {a : α} {b : β}, R a b → S (f1 a) (f2 b)) : lift_rel S (map f1 s1) (map f2 s2) := sorry

theorem map_congr {α : Type u} {β : Type v} (f : α → β) {s : wseq α} {t : wseq α} (h : s ~ t) : map f s ~ map f t :=
  lift_rel_map Eq Eq h fun (_x _x_1 : α) => congr_arg fun (_x : α) => f _x

@[simp] def destruct_append.aux {α : Type u} (t : wseq α) : Option (α × wseq α) → computation (Option (α × wseq α)) :=
  sorry

theorem destruct_append {α : Type u} (s : wseq α) (t : wseq α) : destruct (append s t) = computation.bind (destruct s) (destruct_append.aux t) := sorry

@[simp] def destruct_join.aux {α : Type u} : Option (wseq α × wseq (wseq α)) → computation (Option (α × wseq α)) :=
  sorry

theorem destruct_join {α : Type u} (S : wseq (wseq α)) : destruct (join S) = computation.bind (destruct S) destruct_join.aux := sorry

theorem lift_rel_append {α : Type u} {β : Type v} (R : α → β → Prop) {s1 : wseq α} {s2 : wseq α} {t1 : wseq β} {t2 : wseq β} (h1 : lift_rel R s1 t1) (h2 : lift_rel R s2 t2) : lift_rel R (append s1 s2) (append t1 t2) := sorry

theorem lift_rel_join.lem {α : Type u} {β : Type v} (R : α → β → Prop) {S : wseq (wseq α)} {T : wseq (wseq β)} {U : wseq α → wseq β → Prop} (ST : lift_rel (lift_rel R) S T) (HU : ∀ (s1 : wseq α) (s2 : wseq β),
  (∃ (s : wseq α),
      ∃ (t : wseq β),
        ∃ (S : wseq (wseq α)),
          ∃ (T : wseq (wseq β)),
            s1 = append s (join S) ∧ s2 = append t (join T) ∧ lift_rel R s t ∧ lift_rel (lift_rel R) S T) →
    U s1 s2) {a : Option (α × wseq α)} (ma : a ∈ destruct (join S)) : Exists fun {b : Option (β × wseq β)} => b ∈ destruct (join T) ∧ lift_rel_o R U a b := sorry

theorem lift_rel_join {α : Type u} {β : Type v} (R : α → β → Prop) {S : wseq (wseq α)} {T : wseq (wseq β)} (h : lift_rel (lift_rel R) S T) : lift_rel R (join S) (join T) := sorry

theorem join_congr {α : Type u} {S : wseq (wseq α)} {T : wseq (wseq α)} (h : lift_rel equiv S T) : join S ~ join T :=
  lift_rel_join Eq h

theorem lift_rel_bind {α : Type u} {β : Type v} {γ : Type w} {δ : Type u_1} (R : α → β → Prop) (S : γ → δ → Prop) {s1 : wseq α} {s2 : wseq β} {f1 : α → wseq γ} {f2 : β → wseq δ} (h1 : lift_rel R s1 s2) (h2 : ∀ {a : α} {b : β}, R a b → lift_rel S (f1 a) (f2 b)) : lift_rel S (bind s1 f1) (bind s2 f2) :=
  lift_rel_join S (lift_rel_map R (lift_rel S) h1 h2)

theorem bind_congr {α : Type u} {β : Type v} {s1 : wseq α} {s2 : wseq α} {f1 : α → wseq β} {f2 : α → wseq β} (h1 : s1 ~ s2) (h2 : ∀ (a : α), f1 a ~ f2 a) : bind s1 f1 ~ bind s2 f2 :=
  lift_rel_bind Eq Eq h1
    fun (a b : α) (h : a = b) => eq.mpr (id (Eq._oldrec (Eq.refl (lift_rel Eq (f1 a) (f2 b))) h)) (h2 b)

@[simp] theorem join_ret {α : Type u} (s : wseq α) : join (ret s) ~ s := sorry

@[simp] theorem join_map_ret {α : Type u} (s : wseq α) : join (map ret s) ~ s := sorry

@[simp] theorem join_append {α : Type u} (S : wseq (wseq α)) (T : wseq (wseq α)) : join (append S T) ~ append (join S) (join T) := sorry

@[simp] theorem bind_ret {α : Type u} {β : Type v} (f : α → β) (s : wseq α) : bind s (ret ∘ f) ~ map f s :=
  id (eq.mpr (id (Eq._oldrec (Eq.refl (join (map (ret ∘ f) s) ~ map f s)) (map_comp f ret s))) (join_map_ret (map f s)))

@[simp] theorem ret_bind {α : Type u} {β : Type v} (a : α) (f : α → wseq β) : bind (ret a) f ~ f a := sorry

@[simp] theorem map_join {α : Type u} {β : Type v} (f : α → β) (S : wseq (wseq α)) : map f (join S) = join (map (map f) S) := sorry

@[simp] theorem join_join {α : Type u} (SS : wseq (wseq (wseq α))) : join (join SS) ~ join (map join SS) := sorry

@[simp] theorem bind_assoc {α : Type u} {β : Type v} {γ : Type w} (s : wseq α) (f : α → wseq β) (g : β → wseq γ) : bind (bind s f) g ~ bind s fun (x : α) => bind (f x) g := sorry

protected instance monad : Monad wseq :=
  { toApplicative :=
      { toFunctor := { map := map, mapConst := fun (α β : Type u_1) => map ∘ function.const β },
        toPure := { pure := ret },
        toSeq := { seq := fun (α β : Type u_1) (f : wseq (α → β)) (x : wseq α) => bind f fun (_x : α → β) => map _x x },
        toSeqLeft :=
          { seqLeft :=
              fun (α β : Type u_1) (a : wseq α) (b : wseq β) =>
                (fun (α β : Type u_1) (f : wseq (α → β)) (x : wseq α) => bind f fun (_x : α → β) => map _x x) β α
                  (map (function.const β) a) b },
        toSeqRight :=
          { seqRight :=
              fun (α β : Type u_1) (a : wseq α) (b : wseq β) =>
                (fun (α β : Type u_1) (f : wseq (α → β)) (x : wseq α) => bind f fun (_x : α → β) => map _x x) β β
                  (map (function.const α id) a) b } },
    toBind := { bind := bind } }

