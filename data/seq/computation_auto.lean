/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

Coinductive formalization of unbounded computations.
-/
import PrePort
import Lean3Lib.init.default
import Lean3Lib.data.stream
import Mathlib.tactic.basic
import PostPort

universes u u_1 v w 

namespace Mathlib

/-
coinductive computation (α : Type u) : Type u
| return : α → computation α
| think : computation α → computation α
-/

/-- `computation α` is the type of unbounded computations returning `α`.
  An element of `computation α` is an infinite sequence of `option α` such
  that if `f n = some a` for some `n` then it is constantly `some a` after that. -/
def computation (α : Type u)  :=
  Subtype fun (f : stream (Option α)) => ∀ {n : ℕ} {a : α}, f n = some a → f (n + 1) = some a

namespace computation


-- constructors

/-- `return a` is the computation that immediately terminates with result `a`. -/
def return {α : Type u} (a : α) : computation α :=
  { val := stream.const (some a), property := sorry }

protected instance has_coe_t {α : Type u} : has_coe_t α (computation α) :=
  has_coe_t.mk return

/-- `think c` is the computation that delays for one "tick" and then performs
  computation `c`. -/
def think {α : Type u} (c : computation α) : computation α :=
  { val := none :: subtype.val c, property := sorry }

/-- `thinkN c n` is the computation that delays for `n` ticks and then performs
  computation `c`. -/
def thinkN {α : Type u} (c : computation α) : ℕ → computation α :=
  sorry

-- check for immediate result

/-- `head c` is the first step of computation, either `some a` if `c = return a`
  or `none` if `c = think c'`. -/
def head {α : Type u} (c : computation α) : Option α :=
  stream.head (subtype.val c)

-- one step of computation

/-- `tail c` is the remainder of computation, either `c` if `c = return a`
  or `c'` if `c = think c'`. -/
def tail {α : Type u} (c : computation α) : computation α :=
  { val := stream.tail (subtype.val c), property := sorry }

/-- `empty α` is the computation that never returns, an infinite sequence of
  `think`s. -/
def empty (α : Type u_1) : computation α :=
  { val := stream.const none, property := sorry }

protected instance inhabited {α : Type u} : Inhabited (computation α) :=
  { default := empty α }

/-- `run_for c n` evaluates `c` for `n` steps and returns the result, or `none`
  if it did not terminate after `n` steps. -/
def run_for {α : Type u} : computation α → ℕ → Option α :=
  subtype.val

/-- `destruct c` is the destructor for `computation α` as a coinductive type.
  It returns `inl a` if `c = return a` and `inr c'` if `c = think c'`. -/
def destruct {α : Type u} (c : computation α) : α ⊕ computation α :=
  sorry

/-- `run c` is an unsound meta function that runs `c` to completion, possibly
  resulting in an infinite loop in the VM. -/
theorem destruct_eq_ret {α : Type u} {s : computation α} {a : α} : destruct s = sum.inl a → s = return a := sorry

theorem destruct_eq_think {α : Type u} {s : computation α} {s' : computation α} : destruct s = sum.inr s' → s = think s' := sorry

@[simp] theorem destruct_ret {α : Type u} (a : α) : destruct (return a) = sum.inl a :=
  rfl

@[simp] theorem destruct_think {α : Type u} (s : computation α) : destruct (think s) = sum.inr s := sorry

@[simp] theorem destruct_empty {α : Type u} : destruct (empty α) = sum.inr (empty α) :=
  rfl

@[simp] theorem head_ret {α : Type u} (a : α) : head (return a) = some a :=
  rfl

@[simp] theorem head_think {α : Type u} (s : computation α) : head (think s) = none :=
  rfl

@[simp] theorem head_empty {α : Type u} : head (empty α) = none :=
  rfl

@[simp] theorem tail_ret {α : Type u} (a : α) : tail (return a) = return a :=
  rfl

@[simp] theorem tail_think {α : Type u} (s : computation α) : tail (think s) = s := sorry

@[simp] theorem tail_empty {α : Type u} : tail (empty α) = empty α :=
  rfl

theorem think_empty {α : Type u} : empty α = think (empty α) :=
  destruct_eq_think destruct_empty

def cases_on {α : Type u} {C : computation α → Sort v} (s : computation α) (h1 : (a : α) → C (return a)) (h2 : (s : computation α) → C (think s)) : C s :=
  (fun (_x : α ⊕ computation α) (H : destruct s = _x) =>
      sum.rec (fun (v : α) (H : destruct s = sum.inl v) => eq.mpr sorry (h1 v))
        (fun (v : computation α) (H : destruct s = sum.inr v) =>
          subtype.cases_on v
            (fun (a : stream (Option α)) (s' : ∀ {n : ℕ} {a_1 : α}, a n = some a_1 → a (n + 1) = some a_1)
              (H : destruct s = sum.inr { val := a, property := s' }) => eq.mpr sorry (h2 { val := a, property := s' }))
            H)
        _x H)
    (destruct s) sorry

def corec.F {α : Type u} {β : Type v} (f : β → α ⊕ β) : α ⊕ β → Option α × (α ⊕ β) :=
  sorry

/-- `corec f b` is the corecursor for `computation α` as a coinductive type.
  If `f b = inl a` then `corec f b = return a`, and if `f b = inl b'` then
  `corec f b = think (corec f b')`. -/
def corec {α : Type u} {β : Type v} (f : β → α ⊕ β) (b : β) : computation α :=
  { val := stream.corec' sorry (sum.inr b), property := sorry }

/-- left map of `⊕` -/
@[simp] def lmap {α : Type u} {β : Type v} {γ : Type w} (f : α → β) : α ⊕ γ → β ⊕ γ :=
  sorry

/-- right map of `⊕` -/
@[simp] def rmap {α : Type u} {β : Type v} {γ : Type w} (f : β → γ) : α ⊕ β → α ⊕ γ :=
  sorry

@[simp] theorem corec_eq {α : Type u} {β : Type v} (f : β → α ⊕ β) (b : β) : destruct (corec f b) = rmap (corec f) (f b) := sorry

@[simp] def bisim_o {α : Type u} (R : computation α → computation α → Prop) : α ⊕ computation α → α ⊕ computation α → Prop :=
  sorry

def is_bisimulation {α : Type u} (R : computation α → computation α → Prop)  :=
  ∀ {s₁ s₂ : computation α}, R s₁ s₂ → bisim_o R (destruct s₁) (destruct s₂)

theorem eq_of_bisim {α : Type u} (R : computation α → computation α → Prop) (bisim : is_bisimulation R) {s₁ : computation α} {s₂ : computation α} (r : R s₁ s₂) : s₁ = s₂ := sorry

-- It's more of a stretch to use ∈ for this relation, but it

-- asserts that the computation limits to the given value.

protected def mem {α : Type u} (a : α) (s : computation α)  :=
  some a ∈ subtype.val s

protected instance has_mem {α : Type u} : has_mem α (computation α) :=
  has_mem.mk computation.mem

theorem le_stable {α : Type u} (s : computation α) {a : α} {m : ℕ} {n : ℕ} (h : m ≤ n) : subtype.val s m = some a → subtype.val s n = some a := sorry

theorem mem_unique {α : Type u} : relator.left_unique has_mem.mem := sorry

/-- `terminates s` asserts that the computation `s` eventually terminates with some value. -/
def terminates {α : Type u} (s : computation α)  :=
  ∃ (a : α), a ∈ s

theorem terminates_of_mem {α : Type u} {s : computation α} {a : α} : a ∈ s → terminates s :=
  exists.intro a

theorem terminates_def {α : Type u} (s : computation α) : terminates s ↔ ∃ (n : ℕ), ↥(option.is_some (subtype.val s n)) := sorry

theorem ret_mem {α : Type u} (a : α) : a ∈ return a :=
  exists.intro 0 rfl

theorem eq_of_ret_mem {α : Type u} {a : α} {a' : α} (h : a' ∈ return a) : a' = a :=
  mem_unique h (ret_mem a)

protected instance ret_terminates {α : Type u} (a : α) : terminates (return a) :=
  terminates_of_mem (ret_mem a)

theorem think_mem {α : Type u} {s : computation α} {a : α} : a ∈ s → a ∈ think s := sorry

protected instance think_terminates {α : Type u} (s : computation α) [terminates s] : terminates (think s) :=
  sorry

theorem of_think_mem {α : Type u} {s : computation α} {a : α} : a ∈ think s → a ∈ s := sorry

theorem of_think_terminates {α : Type u} {s : computation α} : terminates (think s) → terminates s :=
  fun (ᾰ : terminates (think s)) =>
    Exists.dcases_on ᾰ
      fun (ᾰ_w : α) (ᾰ_h : ᾰ_w ∈ think s) => idRhs (∃ (a : α), a ∈ s) (Exists.intro ᾰ_w (of_think_mem ᾰ_h))

theorem not_mem_empty {α : Type u} (a : α) : ¬a ∈ empty α := sorry

theorem not_terminates_empty {α : Type u} : ¬terminates (empty α) := sorry

theorem eq_empty_of_not_terminates {α : Type u} {s : computation α} (H : ¬terminates s) : s = empty α := sorry

theorem thinkN_mem {α : Type u} {s : computation α} {a : α} (n : ℕ) : a ∈ thinkN s n ↔ a ∈ s := sorry

protected instance thinkN_terminates {α : Type u} (s : computation α) [terminates s] (n : ℕ) : terminates (thinkN s n) :=
  sorry

theorem of_thinkN_terminates {α : Type u} (s : computation α) (n : ℕ) : terminates (thinkN s n) → terminates s :=
  fun (ᾰ : terminates (thinkN s n)) =>
    Exists.dcases_on ᾰ
      fun (ᾰ_w : α) (ᾰ_h : ᾰ_w ∈ thinkN s n) => idRhs (∃ (a : α), a ∈ s) (Exists.intro ᾰ_w (iff.mp (thinkN_mem n) ᾰ_h))

/-- `promises s a`, or `s ~> a`, asserts that although the computation `s`
  may not terminate, if it does, then the result is `a`. -/
def promises {α : Type u} (s : computation α) (a : α)  :=
  ∀ {a' : α}, a' ∈ s → a = a'

infixl:50 " ~> " => Mathlib.computation.promises

theorem mem_promises {α : Type u} {s : computation α} {a : α} : a ∈ s → s ~> a :=
  fun (h : a ∈ s) (a' : α) => mem_unique h

theorem empty_promises {α : Type u} (a : α) : empty α ~> a :=
  fun (a' : α) (h : a' ∈ empty α) => absurd h (not_mem_empty a')

/-- `length s` gets the number of steps of a terminating computation -/
def length {α : Type u} (s : computation α) [h : terminates s] : ℕ :=
  nat.find sorry

/-- `get s` returns the result of a terminating computation -/
def get {α : Type u} (s : computation α) [h : terminates s] : α :=
  option.get sorry

theorem get_mem {α : Type u} (s : computation α) [h : terminates s] : get s ∈ s :=
  exists.intro (length s) (Eq.symm (option.eq_some_of_is_some (get._proof_2 s)))

theorem get_eq_of_mem {α : Type u} (s : computation α) [h : terminates s] {a : α} : a ∈ s → get s = a :=
  mem_unique (get_mem s)

theorem mem_of_get_eq {α : Type u} (s : computation α) [h : terminates s] {a : α} : get s = a → a ∈ s :=
  fun (h_1 : get s = a) => eq.mpr (id (Eq._oldrec (Eq.refl (a ∈ s)) (Eq.symm h_1))) (get_mem s)

@[simp] theorem get_think {α : Type u} (s : computation α) [h : terminates s] : get (think s) = get s := sorry

@[simp] theorem get_thinkN {α : Type u} (s : computation α) [h : terminates s] (n : ℕ) : get (thinkN s n) = get s :=
  get_eq_of_mem (thinkN s n) (iff.mpr (thinkN_mem n) (get_mem s))

theorem get_promises {α : Type u} (s : computation α) [h : terminates s] : s ~> get s :=
  fun (a : α) => get_eq_of_mem s

theorem mem_of_promises {α : Type u} (s : computation α) [h : terminates s] {a : α} (p : s ~> a) : a ∈ s :=
  Exists.dcases_on h fun (a' : α) (h : a' ∈ s) => eq.mpr (id (Eq._oldrec (Eq.refl (a ∈ s)) (p h))) h

theorem get_eq_of_promises {α : Type u} (s : computation α) [h : terminates s] {a : α} : s ~> a → get s = a :=
  get_eq_of_mem s ∘ mem_of_promises s

/-- `results s a n` completely characterizes a terminating computation:
  it asserts that `s` terminates after exactly `n` steps, with result `a`. -/
def results {α : Type u} (s : computation α) (a : α) (n : ℕ)  :=
  ∃ (h : a ∈ s), length s = n

theorem results_of_terminates {α : Type u} (s : computation α) [T : terminates s] : results s (get s) (length s) :=
  Exists.intro (get_mem s) rfl

theorem results_of_terminates' {α : Type u} (s : computation α) [T : terminates s] {a : α} (h : a ∈ s) : results s a (length s) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (results s a (length s))) (Eq.symm (get_eq_of_mem s h)))) (results_of_terminates s)

theorem results.mem {α : Type u} {s : computation α} {a : α} {n : ℕ} : results s a n → a ∈ s :=
  fun (ᾰ : results s a n) => Exists.dcases_on ᾰ fun (ᾰ_w : a ∈ s) (ᾰ_h : length s = n) => idRhs (a ∈ s) ᾰ_w

theorem results.terminates {α : Type u} {s : computation α} {a : α} {n : ℕ} (h : results s a n) : terminates s :=
  terminates_of_mem (results.mem h)

theorem results.length {α : Type u} {s : computation α} {a : α} {n : ℕ} [T : terminates s] : results s a n → length s = n :=
  fun (ᾰ : results s a n) => Exists.dcases_on ᾰ fun (ᾰ_w : a ∈ s) (ᾰ_h : length s = n) => idRhs (length s = n) ᾰ_h

theorem results.val_unique {α : Type u} {s : computation α} {a : α} {b : α} {m : ℕ} {n : ℕ} (h1 : results s a m) (h2 : results s b n) : a = b :=
  mem_unique (results.mem h1) (results.mem h2)

theorem results.len_unique {α : Type u} {s : computation α} {a : α} {b : α} {m : ℕ} {n : ℕ} (h1 : results s a m) (h2 : results s b n) : m = n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (m = n)) (Eq.symm (results.length h1))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (length s = n)) (results.length h2))) (Eq.refl n))

theorem exists_results_of_mem {α : Type u} {s : computation α} {a : α} (h : a ∈ s) : ∃ (n : ℕ), results s a n :=
  Exists.intro (length s) (results_of_terminates' s h)

@[simp] theorem get_ret {α : Type u} (a : α) : get (return a) = a :=
  get_eq_of_mem (return a) (Exists.intro 0 rfl)

@[simp] theorem length_ret {α : Type u} (a : α) : length (return a) = 0 :=
  let h : terminates (return a) := computation.ret_terminates a;
  nat.eq_zero_of_le_zero (nat.find_min' (iff.mp (terminates_def (return a)) h) rfl)

theorem results_ret {α : Type u} (a : α) : results (return a) a 0 :=
  Exists.intro (ret_mem a) (length_ret a)

@[simp] theorem length_think {α : Type u} (s : computation α) [h : terminates s] : length (think s) = length s + 1 := sorry

theorem results_think {α : Type u} {s : computation α} {a : α} {n : ℕ} (h : results s a n) : results (think s) a (n + 1) :=
  Exists.intro (think_mem (results.mem h))
    (eq.mpr (id (Eq._oldrec (Eq.refl (length (think s) = n + 1)) (length_think s)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (length s + 1 = n + 1)) (results.length h))) (Eq.refl (n + 1))))

theorem of_results_think {α : Type u} {s : computation α} {a : α} {n : ℕ} (h : results (think s) a n) : ∃ (m : ℕ), results s a m ∧ n = m + 1 :=
  Exists.intro (length s)
    { left := results_of_terminates' s (of_think_mem (results.mem h)),
      right := results.len_unique h (results_think (results_of_terminates' s (of_think_mem (results.mem h)))) }

@[simp] theorem results_think_iff {α : Type u} {s : computation α} {a : α} {n : ℕ} : results (think s) a (n + 1) ↔ results s a n := sorry

theorem results_thinkN {α : Type u} {s : computation α} {a : α} {m : ℕ} (n : ℕ) : results s a m → results (thinkN s n) a (m + n) := sorry

theorem results_thinkN_ret {α : Type u} (a : α) (n : ℕ) : results (thinkN (return a) n) a n :=
  eq.mp (Eq._oldrec (Eq.refl (results (thinkN (return a) n) a (0 + n))) (nat.zero_add n))
    (results_thinkN n (results_ret a))

@[simp] theorem length_thinkN {α : Type u} (s : computation α) [h : terminates s] (n : ℕ) : length (thinkN s n) = length s + n :=
  results.length (results_thinkN n (results_of_terminates s))

theorem eq_thinkN {α : Type u} {s : computation α} {a : α} {n : ℕ} (h : results s a n) : s = thinkN (return a) n := sorry

theorem eq_thinkN' {α : Type u} (s : computation α) [h : terminates s] : s = thinkN (return (get s)) (length s) :=
  eq_thinkN (results_of_terminates s)

def mem_rec_on {α : Type u} {C : computation α → Sort v} {a : α} {s : computation α} (M : a ∈ s) (h1 : C (return a)) (h2 : (s : computation α) → C s → C (think s)) : C s :=
  eq.mpr sorry
    (eq.mpr sorry (Nat.rec h1 (fun (n : ℕ) (IH : C (thinkN (return a) n)) => h2 (thinkN (return a) n) IH) (length s)))

def terminates_rec_on {α : Type u} {C : computation α → Sort v} (s : computation α) [terminates s] (h1 : (a : α) → C (return a)) (h2 : (s : computation α) → C s → C (think s)) : C s :=
  mem_rec_on (get_mem s) (h1 (get s)) h2

/-- Map a function on the result of a computation. -/
def map {α : Type u} {β : Type v} (f : α → β) : computation α → computation β :=
  sorry

def bind.G {α : Type u} {β : Type v} : β ⊕ computation β → β ⊕ computation α ⊕ computation β :=
  sorry

def bind.F {α : Type u} {β : Type v} (f : α → computation β) : computation α ⊕ computation β → β ⊕ computation α ⊕ computation β :=
  sorry

/-- Compose two computations into a monadic `bind` operation. -/
def bind {α : Type u} {β : Type v} (c : computation α) (f : α → computation β) : computation β :=
  corec sorry (sum.inl c)

protected instance has_bind : Bind computation :=
  { bind := bind }

theorem has_bind_eq_bind {α : Type u} {β : Type u} (c : computation α) (f : α → computation β) : c >>= f = bind c f :=
  rfl

/-- Flatten a computation of computations into a single computation. -/
def join {α : Type u} (c : computation (computation α)) : computation α :=
  c >>= id

@[simp] theorem map_ret {α : Type u} {β : Type v} (f : α → β) (a : α) : map f (return a) = return (f a) :=
  rfl

@[simp] theorem map_think {α : Type u} {β : Type v} (f : α → β) (s : computation α) : map f (think s) = think (map f s) := sorry

@[simp] theorem destruct_map {α : Type u} {β : Type v} (f : α → β) (s : computation α) : destruct (map f s) = lmap f (rmap (map f) (destruct s)) := sorry

@[simp] theorem map_id {α : Type u} (s : computation α) : map id s = s := sorry

theorem map_comp {α : Type u} {β : Type v} {γ : Type w} (f : α → β) (g : β → γ) (s : computation α) : map (g ∘ f) s = map g (map f s) := sorry

@[simp] theorem ret_bind {α : Type u} {β : Type v} (a : α) (f : α → computation β) : bind (return a) f = f a := sorry

@[simp] theorem think_bind {α : Type u} {β : Type v} (c : computation α) (f : α → computation β) : bind (think c) f = think (bind c f) := sorry

@[simp] theorem bind_ret {α : Type u} {β : Type v} (f : α → β) (s : computation α) : bind s (return ∘ f) = map f s := sorry

@[simp] theorem bind_ret' {α : Type u} (s : computation α) : bind s return = s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (bind s return = s)) (bind_ret (fun (x : α) => x) s)))
    (id (eq.mpr (id (Eq._oldrec (Eq.refl (map id s = s)) (map_id s))) (Eq.refl s)))

@[simp] theorem bind_assoc {α : Type u} {β : Type v} {γ : Type w} (s : computation α) (f : α → computation β) (g : β → computation γ) : bind (bind s f) g = bind s fun (x : α) => bind (f x) g := sorry

theorem results_bind {α : Type u} {β : Type v} {s : computation α} {f : α → computation β} {a : α} {b : β} {m : ℕ} {n : ℕ} (h1 : results s a m) (h2 : results (f a) b n) : results (bind s f) b (n + m) := sorry

theorem mem_bind {α : Type u} {β : Type v} {s : computation α} {f : α → computation β} {a : α} {b : β} (h1 : a ∈ s) (h2 : b ∈ f a) : b ∈ bind s f := sorry

protected instance terminates_bind {α : Type u} {β : Type v} (s : computation α) (f : α → computation β) [terminates s] [terminates (f (get s))] : terminates (bind s f) :=
  terminates_of_mem (mem_bind (get_mem s) (get_mem (f (get s))))

@[simp] theorem get_bind {α : Type u} {β : Type v} (s : computation α) (f : α → computation β) [terminates s] [terminates (f (get s))] : get (bind s f) = get (f (get s)) :=
  get_eq_of_mem (bind s f) (mem_bind (get_mem s) (get_mem (f (get s))))

@[simp] theorem length_bind {α : Type u} {β : Type v} (s : computation α) (f : α → computation β) [T1 : terminates s] [T2 : terminates (f (get s))] : length (bind s f) = length (f (get s)) + length s :=
  results.len_unique (results_of_terminates (bind s f))
    (results_bind (results_of_terminates s) (results_of_terminates (f (get s))))

theorem of_results_bind {α : Type u} {β : Type v} {s : computation α} {f : α → computation β} {b : β} {k : ℕ} : results (bind s f) b k → ∃ (a : α), ∃ (m : ℕ), ∃ (n : ℕ), results s a m ∧ results (f a) b n ∧ k = n + m := sorry

theorem exists_of_mem_bind {α : Type u} {β : Type v} {s : computation α} {f : α → computation β} {b : β} (h : b ∈ bind s f) : ∃ (a : α), ∃ (H : a ∈ s), b ∈ f a := sorry

theorem bind_promises {α : Type u} {β : Type v} {s : computation α} {f : α → computation β} {a : α} {b : β} (h1 : s ~> a) (h2 : f a ~> b) : bind s f ~> b := sorry

protected instance monad : Monad computation :=
  { toApplicative :=
      { toFunctor := { map := map, mapConst := fun (α β : Type u_1) => map ∘ function.const β },
        toPure := { pure := return },
        toSeq :=
          { seq :=
              fun (α β : Type u_1) (f : computation (α → β)) (x : computation α) => bind f fun (_x : α → β) => map _x x },
        toSeqLeft :=
          { seqLeft :=
              fun (α β : Type u_1) (a : computation α) (b : computation β) =>
                (fun (α β : Type u_1) (f : computation (α → β)) (x : computation α) =>
                    bind f fun (_x : α → β) => map _x x)
                  β α (map (function.const β) a) b },
        toSeqRight :=
          { seqRight :=
              fun (α β : Type u_1) (a : computation α) (b : computation β) =>
                (fun (α β : Type u_1) (f : computation (α → β)) (x : computation α) =>
                    bind f fun (_x : α → β) => map _x x)
                  β β (map (function.const α id) a) b } },
    toBind := { bind := bind } }

protected instance is_lawful_monad : is_lawful_monad computation :=
  is_lawful_monad.mk ret_bind bind_assoc

theorem has_map_eq_map {α : Type u} {β : Type u} (f : α → β) (c : computation α) : f <$> c = map f c :=
  rfl

@[simp] theorem return_def {α : Type u} (a : α) : return a = return a :=
  rfl

@[simp] theorem map_ret' {α : Type u_1} {β : Type u_1} (f : α → β) (a : α) : f <$> return a = return (f a) :=
  map_ret

@[simp] theorem map_think' {α : Type u_1} {β : Type u_1} (f : α → β) (s : computation α) : f <$> think s = think (f <$> s) :=
  map_think

theorem mem_map {α : Type u} {β : Type v} (f : α → β) {a : α} {s : computation α} (m : a ∈ s) : f a ∈ map f s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (f a ∈ map f s)) (Eq.symm (bind_ret f s)))) (mem_bind m (ret_mem (f a)))

theorem exists_of_mem_map {α : Type u} {β : Type v} {f : α → β} {b : β} {s : computation α} (h : b ∈ map f s) : ∃ (a : α), a ∈ s ∧ f a = b := sorry

protected instance terminates_map {α : Type u} {β : Type v} (f : α → β) (s : computation α) [terminates s] : terminates (map f s) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (terminates (map f s))) (Eq.symm (bind_ret f s))))
    (computation.terminates_bind s (return ∘ f))

theorem terminates_map_iff {α : Type u} {β : Type v} (f : α → β) (s : computation α) : terminates (map f s) ↔ terminates s := sorry

-- Parallel computation

/-- `c₁ <|> c₂` calculates `c₁` and `c₂` simultaneously, returning
  the first one that gives a result. -/
def orelse {α : Type u} (c₁ : computation α) (c₂ : computation α) : computation α :=
  corec (fun (_x : computation α × computation α) => sorry) (c₁, c₂)

protected instance alternative : alternative computation :=
  alternative.mk empty

@[simp] theorem ret_orelse {α : Type u} (a : α) (c₂ : computation α) : (return a <|> c₂) = return a := sorry

@[simp] theorem orelse_ret {α : Type u} (c₁ : computation α) (a : α) : (think c₁ <|> return a) = return a := sorry

@[simp] theorem orelse_think {α : Type u} (c₁ : computation α) (c₂ : computation α) : (think c₁ <|> think c₂) = think (c₁ <|> c₂) := sorry

@[simp] theorem empty_orelse {α : Type u} (c : computation α) : (empty α <|> c) = c := sorry

@[simp] theorem orelse_empty {α : Type u} (c : computation α) : (c <|> empty α) = c := sorry

/-- `c₁ ~ c₂` asserts that `c₁` and `c₂` either both terminate with the same result,
  or both loop forever. -/
def equiv {α : Type u} (c₁ : computation α) (c₂ : computation α)  :=
  ∀ (a : α), a ∈ c₁ ↔ a ∈ c₂

infixl:50 " ~ " => Mathlib.computation.equiv

theorem equiv.refl {α : Type u} (s : computation α) : s ~ s :=
  fun (_x : α) => iff.rfl

theorem equiv.symm {α : Type u} {s : computation α} {t : computation α} : s ~ t → t ~ s :=
  fun (h : s ~ t) (a : α) => iff.symm (h a)

theorem equiv.trans {α : Type u} {s : computation α} {t : computation α} {u : computation α} : s ~ t → t ~ u → s ~ u :=
  fun (h1 : s ~ t) (h2 : t ~ u) (a : α) => iff.trans (h1 a) (h2 a)

theorem equiv.equivalence {α : Type u} : equivalence equiv :=
  { left := equiv.refl, right := { left := equiv.symm, right := equiv.trans } }

theorem equiv_of_mem {α : Type u} {s : computation α} {t : computation α} {a : α} (h1 : a ∈ s) (h2 : a ∈ t) : s ~ t :=
  fun (a' : α) =>
    { mp := fun (ma : a' ∈ s) => eq.mpr (id (Eq._oldrec (Eq.refl (a' ∈ t)) (mem_unique ma h1))) h2,
      mpr := fun (ma : a' ∈ t) => eq.mpr (id (Eq._oldrec (Eq.refl (a' ∈ s)) (mem_unique ma h2))) h1 }

theorem terminates_congr {α : Type u} {c₁ : computation α} {c₂ : computation α} (h : c₁ ~ c₂) : terminates c₁ ↔ terminates c₂ :=
  exists_congr h

theorem promises_congr {α : Type u} {c₁ : computation α} {c₂ : computation α} (h : c₁ ~ c₂) (a : α) : c₁ ~> a ↔ c₂ ~> a :=
  forall_congr fun (a' : α) => imp_congr (h a') iff.rfl

theorem get_equiv {α : Type u} {c₁ : computation α} {c₂ : computation α} (h : c₁ ~ c₂) [terminates c₁] [terminates c₂] : get c₁ = get c₂ :=
  get_eq_of_mem c₁ (iff.mpr (h (get c₂)) (get_mem c₂))

theorem think_equiv {α : Type u} (s : computation α) : think s ~ s :=
  fun (a : α) => { mp := of_think_mem, mpr := think_mem }

theorem thinkN_equiv {α : Type u} (s : computation α) (n : ℕ) : thinkN s n ~ s :=
  fun (a : α) => thinkN_mem n

theorem bind_congr {α : Type u} {β : Type v} {s1 : computation α} {s2 : computation α} {f1 : α → computation β} {f2 : α → computation β} (h1 : s1 ~ s2) (h2 : ∀ (a : α), f1 a ~ f2 a) : bind s1 f1 ~ bind s2 f2 := sorry

theorem equiv_ret_of_mem {α : Type u} {s : computation α} {a : α} (h : a ∈ s) : s ~ return a :=
  equiv_of_mem h (ret_mem a)

/-- `lift_rel R ca cb` is a generalization of `equiv` to relations other than
  equality. It asserts that if `ca` terminates with `a`, then `cb` terminates with
  some `b` such that `R a b`, and if `cb` terminates with `b` then `ca` terminates
  with some `a` such that `R a b`. -/
def lift_rel {α : Type u} {β : Type v} (R : α → β → Prop) (ca : computation α) (cb : computation β)  :=
  (∀ {a : α}, a ∈ ca → Exists fun {b : β} => b ∈ cb ∧ R a b) ∧ ∀ {b : β}, b ∈ cb → Exists fun {a : α} => a ∈ ca ∧ R a b

theorem lift_rel.swap {α : Type u} {β : Type v} (R : α → β → Prop) (ca : computation α) (cb : computation β) : lift_rel (function.swap R) cb ca ↔ lift_rel R ca cb :=
  and_comm (∀ {a : β}, a ∈ cb → Exists fun {b : α} => b ∈ ca ∧ function.swap R a b)
    (∀ {b : α}, b ∈ ca → Exists fun {a : β} => a ∈ cb ∧ function.swap R a b)

theorem lift_eq_iff_equiv {α : Type u} (c₁ : computation α) (c₂ : computation α) : lift_rel Eq c₁ c₂ ↔ c₁ ~ c₂ := sorry

theorem lift_rel.refl {α : Type u} (R : α → α → Prop) (H : reflexive R) : reflexive (lift_rel R) :=
  fun (s : computation α) =>
    { left := fun (a : α) (as : a ∈ s) => Exists.intro a { left := as, right := H a },
      right := fun (b : α) (bs : b ∈ s) => Exists.intro b { left := bs, right := H b } }

theorem lift_rel.symm {α : Type u} (R : α → α → Prop) (H : symmetric R) : symmetric (lift_rel R) := sorry

theorem lift_rel.trans {α : Type u} (R : α → α → Prop) (H : transitive R) : transitive (lift_rel R) := sorry

theorem lift_rel.equiv {α : Type u} (R : α → α → Prop) : equivalence R → equivalence (lift_rel R) := sorry

theorem lift_rel.imp {α : Type u} {β : Type v} {R : α → β → Prop} {S : α → β → Prop} (H : ∀ {a : α} {b : β}, R a b → S a b) (s : computation α) (t : computation β) : lift_rel R s t → lift_rel S s t := sorry

theorem terminates_of_lift_rel {α : Type u} {β : Type v} {R : α → β → Prop} {s : computation α} {t : computation β} : lift_rel R s t → (terminates s ↔ terminates t) := sorry

theorem rel_of_lift_rel {α : Type u} {β : Type v} {R : α → β → Prop} {ca : computation α} {cb : computation β} : lift_rel R ca cb → ∀ {a : α} {b : β}, a ∈ ca → b ∈ cb → R a b := sorry

theorem lift_rel_of_mem {α : Type u} {β : Type v} {R : α → β → Prop} {a : α} {b : β} {ca : computation α} {cb : computation β} (ma : a ∈ ca) (mb : b ∈ cb) (ab : R a b) : lift_rel R ca cb := sorry

theorem exists_of_lift_rel_left {α : Type u} {β : Type v} {R : α → β → Prop} {ca : computation α} {cb : computation β} (H : lift_rel R ca cb) {a : α} (h : a ∈ ca) : Exists fun {b : β} => b ∈ cb ∧ R a b :=
  and.left H a h

theorem exists_of_lift_rel_right {α : Type u} {β : Type v} {R : α → β → Prop} {ca : computation α} {cb : computation β} (H : lift_rel R ca cb) {b : β} (h : b ∈ cb) : Exists fun {a : α} => a ∈ ca ∧ R a b :=
  and.right H b h

theorem lift_rel_def {α : Type u} {β : Type v} {R : α → β → Prop} {ca : computation α} {cb : computation β} : lift_rel R ca cb ↔ (terminates ca ↔ terminates cb) ∧ ∀ {a : α} {b : β}, a ∈ ca → b ∈ cb → R a b := sorry

theorem lift_rel_bind {α : Type u} {β : Type v} {γ : Type w} {δ : Type u_1} (R : α → β → Prop) (S : γ → δ → Prop) {s1 : computation α} {s2 : computation β} {f1 : α → computation γ} {f2 : β → computation δ} (h1 : lift_rel R s1 s2) (h2 : ∀ {a : α} {b : β}, R a b → lift_rel S (f1 a) (f2 b)) : lift_rel S (bind s1 f1) (bind s2 f2) := sorry

@[simp] theorem lift_rel_return_left {α : Type u} {β : Type v} (R : α → β → Prop) (a : α) (cb : computation β) : lift_rel R (return a) cb ↔ Exists fun {b : β} => b ∈ cb ∧ R a b := sorry

@[simp] theorem lift_rel_return_right {α : Type u} {β : Type v} (R : α → β → Prop) (ca : computation α) (b : β) : lift_rel R ca (return b) ↔ Exists fun {a : α} => a ∈ ca ∧ R a b := sorry

@[simp] theorem lift_rel_return {α : Type u} {β : Type v} (R : α → β → Prop) (a : α) (b : β) : lift_rel R (return a) (return b) ↔ R a b := sorry

@[simp] theorem lift_rel_think_left {α : Type u} {β : Type v} (R : α → β → Prop) (ca : computation α) (cb : computation β) : lift_rel R (think ca) cb ↔ lift_rel R ca cb := sorry

@[simp] theorem lift_rel_think_right {α : Type u} {β : Type v} (R : α → β → Prop) (ca : computation α) (cb : computation β) : lift_rel R ca (think cb) ↔ lift_rel R ca cb := sorry

theorem lift_rel_mem_cases {α : Type u} {β : Type v} {R : α → β → Prop} {ca : computation α} {cb : computation β} (Ha : ∀ (a : α), a ∈ ca → lift_rel R ca cb) (Hb : ∀ (b : β), b ∈ cb → lift_rel R ca cb) : lift_rel R ca cb :=
  { left := fun (a : α) (ma : a ∈ ca) => and.left (Ha a ma) a ma,
    right := fun (b : β) (mb : b ∈ cb) => and.right (Hb b mb) b mb }

theorem lift_rel_congr {α : Type u} {β : Type v} {R : α → β → Prop} {ca : computation α} {ca' : computation α} {cb : computation β} {cb' : computation β} (ha : ca ~ ca') (hb : cb ~ cb') : lift_rel R ca cb ↔ lift_rel R ca' cb' :=
  and_congr (forall_congr fun (a : α) => imp_congr (ha a) (exists_congr fun (b : β) => and_congr (hb b) iff.rfl))
    (forall_congr fun (b : β) => imp_congr (hb b) (exists_congr fun (a : α) => and_congr (ha a) iff.rfl))

theorem lift_rel_map {α : Type u} {β : Type v} {γ : Type w} {δ : Type u_1} (R : α → β → Prop) (S : γ → δ → Prop) {s1 : computation α} {s2 : computation β} {f1 : α → γ} {f2 : β → δ} (h1 : lift_rel R s1 s2) (h2 : ∀ {a : α} {b : β}, R a b → S (f1 a) (f2 b)) : lift_rel S (map f1 s1) (map f2 s2) := sorry

theorem map_congr {α : Type u} {β : Type v} (R : α → α → Prop) (S : β → β → Prop) {s1 : computation α} {s2 : computation α} {f : α → β} (h1 : s1 ~ s2) : map f s1 ~ map f s2 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (map f s1 ~ map f s2)) (Eq.symm (propext (lift_eq_iff_equiv (map f s1) (map f s2))))))
    (lift_rel_map Eq Eq (iff.mpr (lift_eq_iff_equiv s1 s2) h1) fun (a b : α) => congr_arg fun (a : α) => f a)

@[simp] def lift_rel_aux {α : Type u} {β : Type v} (R : α → β → Prop) (C : computation α → computation β → Prop) : α ⊕ computation α → β ⊕ computation β → Prop :=
  sorry

@[simp] theorem lift_rel_aux.ret_left {α : Type u} {β : Type v} (R : α → β → Prop) (C : computation α → computation β → Prop) (a : α) (cb : computation β) : lift_rel_aux R C (sum.inl a) (destruct cb) ↔ Exists fun {b : β} => b ∈ cb ∧ R a b := sorry

theorem lift_rel_aux.swap {α : Type u} {β : Type v} (R : α → β → Prop) (C : computation α → computation β → Prop) (a : α ⊕ computation α) (b : β ⊕ computation β) : lift_rel_aux (function.swap R) (function.swap C) b a = lift_rel_aux R C a b := sorry

@[simp] theorem lift_rel_aux.ret_right {α : Type u} {β : Type v} (R : α → β → Prop) (C : computation α → computation β → Prop) (b : β) (ca : computation α) : lift_rel_aux R C (destruct ca) (sum.inl b) ↔ Exists fun {a : α} => a ∈ ca ∧ R a b := sorry

theorem lift_rel_rec.lem {α : Type u} {β : Type v} {R : α → β → Prop} (C : computation α → computation β → Prop) (H : ∀ {ca : computation α} {cb : computation β}, C ca cb → lift_rel_aux R C (destruct ca) (destruct cb)) (ca : computation α) (cb : computation β) (Hc : C ca cb) (a : α) (ha : a ∈ ca) : lift_rel R ca cb := sorry

theorem lift_rel_rec {α : Type u} {β : Type v} {R : α → β → Prop} (C : computation α → computation β → Prop) (H : ∀ {ca : computation α} {cb : computation β}, C ca cb → lift_rel_aux R C (destruct ca) (destruct cb)) (ca : computation α) (cb : computation β) (Hc : C ca cb) : lift_rel R ca cb :=
  lift_rel_mem_cases sorry fun (b : β) (hb : b ∈ cb) => iff.mpr (lift_rel.swap (fun (x : β) (y : α) => R y x) cb ca) sorry

