/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Simon Hudon
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.control.uliftable
import Mathlib.Lean3Lib.system.random
import Mathlib.system.random.basic
import Mathlib.PostPort

universes u u_1 v 

namespace Mathlib

/-!
# `gen` Monad

This monad is used to formulate randomized computations with a parameter
to specify the desired size of the result.

This is a port of the Haskell QuickCheck library.

## Main definitions
  * `gen` monad

## Local notation

 * `i .. j` : `Icc i j`, the set of values between `i` and `j` inclusively;

## Tags

random testing

## References

  * https://hackage.haskell.org/package/QuickCheck

-/

namespace slim_check


/-- Monad to generate random examples to test properties with.
It has a `nat` parameter so that the caller can decide on the
size of the examples. -/
def gen (α : Type u) := reader_t (ulift ℕ) rand α

/-- Execute a `gen` inside the `io` monad using `i` as the example
size and with a fresh random number generator. -/
def io.run_gen {α : Type} (x : gen α) (i : ℕ) : io α := io.run_rand (reader_t.run x (ulift.up i))

namespace gen


/-- Lift `random.random` to the `gen` monad. -/
def choose_any (α : Type u) [random α] : gen α := reader_t.mk fun (_x : ulift ℕ) => rand.random α

/-- Lift `random.random_r` to the `gen` monad. -/
def choose {α : Type u} [preorder α] [bounded_random α] (x : α) (y : α) (p : x ≤ y) :
    gen ↥(set.Icc x y) :=
  reader_t.mk fun (_x : ulift ℕ) => rand.random_r x y p

/-- Generate a `nat` example between `x` and `y`. -/
def choose_nat (x : ℕ) (y : ℕ) (p : x ≤ y) : gen ↥(set.Icc x y) := choose x y p

/-- Generate a `nat` example between `x` and `y`. -/
def choose_nat' (x : ℕ) (y : ℕ) (p : x < y) : gen ↥(set.Ico x y) :=
  (fun (this : ∀ (i : ℕ), x < i → i ≤ y → Nat.pred i < y) =>
      subtype.map Nat.pred sorry <$> choose (x + 1) y p)
    sorry

protected instance uliftable : uliftable gen gen :=
  reader_t.uliftable' (equiv.trans equiv.ulift (equiv.symm equiv.ulift))

protected instance has_orelse : has_orelse gen :=
  has_orelse.mk
    fun (α : Type u) (x y : gen α) =>
      do 
        let b ← uliftable.up (choose_any Bool)
        ite (↥(ulift.down b)) x y

/-- Get access to the size parameter of the `gen` monad. For
reasons of universe polymorphism, it is specified in
continuation passing style. -/
def sized {α : Type u} (cmd : ℕ → gen α) : gen α := reader_t.mk fun (_x : ulift ℕ) => sorry

/-- Apply a function to the size parameter. -/
def resize {α : Type u} (f : ℕ → ℕ) (cmd : gen α) : gen α := reader_t.mk fun (_x : ulift ℕ) => sorry

/-- Create `n` examples using `cmd`. -/
def vector_of {α : Type u} (n : ℕ) (cmd : gen α) : gen (vector α n) := sorry

/-- Create a list of examples using `cmd`. The size is controlled
by the size parameter of `gen`. -/
def list_of {α : Type u} (cmd : gen α) : gen (List α) :=
  sized
    fun (sz : ℕ) =>
      do 
        uliftable.up (choose_nat 0 (sz + 1) sorry)
        sorry

/-- Given a list of example generators, choose one to create an example. -/
def one_of {α : Type u} (xs : List (gen α)) (pos : 0 < list.length xs) : gen α :=
  do 
    uliftable.up (choose_nat' 0 (list.length xs) pos)
    sorry

/-- Given a list of example generators, choose one to create an example. -/
def elements {α : Type u} (xs : List α) (pos : 0 < list.length xs) : gen α :=
  do 
    uliftable.up (choose_nat' 0 (list.length xs) pos)
    sorry

/--
`freq_aux xs i _` takes a weighted list of generator and a number meant to select one of the generators.

If we consider `freq_aux [(1, gena), (3, genb), (5, genc)] 4 _`, we choose a generator by splitting
the interval 1-9 into 1-1, 2-4, 5-9 so that the width of each interval corresponds to one of the
number in the list of generators. Then, we check which interval 4 falls into: it selects `genb`.
-/
def freq_aux {α : Type u} (xs : List (ℕ+ × gen α)) (i : ℕ) :
    i < list.sum (list.map (subtype.val ∘ prod.fst) xs) → gen α :=
  sorry

/--
`freq [(1, gena), (3, genb), (5, genc)] _` will choose one of `gena`, `genb`, `genc` with
probabiities proportional to the number accompanying them. In this example, the sum of
those numbers is 9, `gena` will be chosen with probability ~1/9, `genb` with ~3/9 (i.e. 1/3)
and `genc` with probability 5/9.
-/
def freq {α : Type u} (xs : List (ℕ+ × gen α)) (pos : 0 < list.length xs) : gen α :=
  let s : ℕ := list.sum (list.map (subtype.val ∘ prod.fst) xs);
  (fun (ha : 1 ≤ s) =>
      (fun (this : 0 ≤ s - 1) =>
          uliftable.adapt_up gen gen (choose_nat 0 (s - 1) this)
            fun (i : ↥(set.Icc 0 (s - 1))) => freq_aux xs (subtype.val i) sorry)
        sorry)
    sorry

/-- Generate a random permutation of a given list. -/
def permutation_of {α : Type u} (xs : List α) : gen (Subtype (list.perm xs)) := sorry

end Mathlib