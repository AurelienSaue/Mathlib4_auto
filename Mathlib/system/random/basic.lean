/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Simon Hudon
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.group_power.default
import Mathlib.control.uliftable
import Mathlib.control.monad.basic
import Mathlib.data.bitvec.basic
import Mathlib.data.list.basic
import Mathlib.data.set.intervals.basic
import Mathlib.data.stream.basic
import Mathlib.data.fin
import Mathlib.tactic.cache
import Mathlib.tactic.interactive
import Mathlib.tactic.norm_num
import Mathlib.Lean3Lib.system.io
import Mathlib.Lean3Lib.system.random
import Mathlib.PostPort

universes u u_1 v l 

namespace Mathlib

/-!
# Rand Monad and Random Class

This module provides tools for formulating computations guided by randomness and for
defining objects that can be created randomly.

## Main definitions
  * `rand` monad for computations guided by randomness;
  * `random` class for objects that can be generated randomly;
    * `random` to generate one object;
    * `random_r` to generate one object inside a range;
    * `random_series` to generate an infinite series of objects;
    * `random_series_r` to generate an infinite series of objects inside a range;
  * `io.mk_generator` to create a new random number generator;
  * `io.run_rand` to run a randomized computation inside the `io` monad;
  * `tactic.run_rand` to run a randomized computation inside the `tactic` monad

## Local notation

 * `i .. j` : `Icc i j`, the set of values between `i` and `j` inclusively;

## Tags

random monad io

## References

  * Similar library in Haskell: https://hackage.haskell.org/package/MonadRandom

-/

/-- A monad to generate random objects using the generator type `g` -/
def rand_g (g : Type) (α : Type u)  :=
  state (ulift g) α

/-- A monad to generate random objects using the generator type `std_gen` -/
def rand (α : Type u_1)  :=
  rand_g std_gen

protected instance rand_g.uliftable (g : Type) : uliftable (rand_g g) (rand_g g) :=
  state_t.uliftable' (equiv.trans equiv.ulift (equiv.symm equiv.ulift))

/-- Generate one more `ℕ` -/
def rand_g.next {g : Type} [random_gen g] : rand_g g ℕ :=
  state_t.mk (prod.map id ulift.up ∘ random_gen.next ∘ ulift.down)

/-- `bounded_random α` gives us machinery to generate values of type `α` between certain bounds -/
class bounded_random (α : Type u) [preorder α] 
where
  random_r : (g : Type) → [_inst_1_1 : random_gen g] → (x y : α) → x ≤ y → rand_g g ↥(set.Icc x y)

/-- `random α` gives us machinery to generate values of type `α` -/
class random (α : Type u) 
where
  random : (g : Type) → [_inst_1 : random_gen g] → rand_g g α

/-- shift_31_left = 2^31; multiplying by it shifts the binary
representation of a number left by 31 bits, dividing by it shifts it
right by 31 bits -/
def shift_31_left : ℕ :=
  bit0
    (bit0
      (bit0
        (bit0
          (bit0
            (bit0
              (bit0
                (bit0
                  (bit0
                    (bit0
                      (bit0
                        (bit0
                          (bit0
                            (bit0
                              (bit0
                                (bit0
                                  (bit0
                                    (bit0
                                      (bit0
                                        (bit0
                                          (bit0
                                            (bit0
                                              (bit0
                                                (bit0
                                                  (bit0
                                                    (bit0 (bit0 (bit0 (bit0 (bit0 (bit0 1))))))))))))))))))))))))))))))

namespace rand


/-- create a new random number generator distinct from the one stored in the state -/
def split (g : Type) [random_gen g] : rand_g g g :=
  state_t.mk (prod.map id ulift.up ∘ random_gen.split ∘ ulift.down)

/-- Generate a random value of type `α`. -/
def random (α : Type u) {g : Type} [random_gen g] [random α] : rand_g g α :=
  random α g

/-- generate an infinite series of random values of type `α` -/
def random_series (α : Type u) {g : Type} [random_gen g] [random α] : rand_g g (stream α) :=
  do 
    let gen ← uliftable.up (split g)
    pure (stream.corec_state (random α g) gen)

/-- Generate a random value between `x` and `y` inclusive. -/
def random_r {α : Type u} {g : Type} [random_gen g] [preorder α] [bounded_random α] (x : α) (y : α) (h : x ≤ y) : rand_g g ↥(set.Icc x y) :=
  bounded_random.random_r g x y h

/-- generate an infinite series of random values of type `α` between `x` and `y` inclusive. -/
def random_series_r {α : Type u} {g : Type} [random_gen g] [preorder α] [bounded_random α] (x : α) (y : α) (h : x ≤ y) : rand_g g (stream ↥(set.Icc x y)) :=
  do 
    let gen ← uliftable.up (split g)
    pure (stream.corec_state (bounded_random.random_r g x y h) gen)

end rand


namespace io


/-- create and a seed a random number generator -/
def mk_generator : io std_gen :=
  do 
    let seed ← rand 0 shift_31_left 
    return (mk_std_gen seed)

/-- Run `cmd` using a randomly seeded random number generator -/
def run_rand {α : Type} (cmd : rand α) : io α :=
  do 
    let g ← mk_generator 
    return (prod.fst (state_t.run cmd (ulift.up g)))

/-- Run `cmd` using the provided seed. -/
def run_rand_with {α : Type} (seed : ℕ) (cmd : rand α) : io α :=
  return (prod.fst (state_t.run cmd (ulift.up (mk_std_gen seed))))

/-- randomly generate a value of type α -/
def random {α : Type} [random α] : io α :=
  run_rand (rand.random α)

/-- randomly generate an infinite series of value of type α -/
def random_series {α : Type} [random α] : io (stream α) :=
  run_rand (rand.random_series α)

/-- randomly generate a value of type α between `x` and `y` -/
def random_r {α : Type} [preorder α] [bounded_random α] (x : α) (y : α) (p : x ≤ y) : io ↥(set.Icc x y) :=
  run_rand (bounded_random.random_r std_gen x y p)

/-- randomly generate an infinite series of value of type α between `x` and `y` -/
def random_series_r {α : Type} [preorder α] [bounded_random α] (x : α) (y : α) (h : x ≤ y) : io (stream ↥(set.Icc x y)) :=
  run_rand (rand.random_series_r x y h)

end io


namespace tactic


/-- create a seeded random number generator in the `tactic` monad -/
/-- run `cmd` using the a randomly seeded random number generator
in the tactic monad -/
/-- Generate a random value between `x` and `y` inclusive. -/
/-- Generate an infinite series of random values of type `α` between `x` and `y` inclusive. -/
/-- randomly generate a value of type α -/
end tactic


namespace fin


/-- generate a `fin` randomly -/
protected def random {g : Type} [random_gen g] {n : ℕ} [fact (0 < n)] : rand_g g (fin n) :=
  state_t.mk fun (_x : ulift g) => sorry

end fin


protected instance nat_bounded_random : bounded_random ℕ :=
  bounded_random.mk
    fun (g : Type) (inst : random_gen g) (x y : ℕ) (hxy : x ≤ y) =>
      do 
        let z ← fin.random 
        pure { val := subtype.val z + x, property := sorry }

/-- This `bounded_random` interval generates integers between `x` and
`y` by first generating a natural number between `0` and `y - x` and
shifting the result appropriately. -/
protected instance int_bounded_random : bounded_random ℤ :=
  bounded_random.mk
    fun (g : Type) (inst : random_gen g) (x y : ℤ) (hxy : x ≤ y) =>
      do 
        bounded_random.random_r g 0 (int.nat_abs (y - x)) sorry 
        sorry

protected instance fin_random (n : ℕ) [fact (0 < n)] : random (fin n) :=
  random.mk fun (g : Type) (inst : random_gen g) => fin.random

protected instance fin_bounded_random (n : ℕ) : bounded_random (fin n) :=
  bounded_random.mk
    fun (g : Type) (inst : random_gen g) (x y : fin n) (p : x ≤ y) =>
      do 
        rand.random_r (subtype.val x) (subtype.val y) p 
        sorry

/-- A shortcut for creating a `random (fin n)` instance from
a proof that `0 < n` rather than on matching on `fin (succ n)`  -/
def random_fin_of_pos {n : ℕ} (h : 0 < n) : random (fin n) :=
  sorry

theorem bool_of_nat_mem_Icc_of_mem_Icc_to_nat (x : Bool) (y : Bool) (n : ℕ) : n ∈ set.Icc (bool.to_nat x) (bool.to_nat y) → bool.of_nat n ∈ set.Icc x y := sorry

protected instance bool.random : random Bool :=
  random.mk fun (g : Type) (inst : random_gen g) => (bool.of_nat ∘ subtype.val) <$> bounded_random.random_r g 0 1 sorry

protected instance bool.bounded_random : bounded_random Bool :=
  bounded_random.mk
    fun (g : Type) (_inst : random_gen g) (x y : Bool) (p : x ≤ y) =>
      subtype.map bool.of_nat (bool_of_nat_mem_Icc_of_mem_Icc_to_nat x y) <$>
        bounded_random.random_r g (bool.to_nat x) (bool.to_nat y) (bool.to_nat_le_to_nat p)

/-- generate a random bit vector of length `n` -/
def bitvec.random {g : Type} [random_gen g] (n : ℕ) : rand_g g (bitvec n) :=
  bitvec.of_fin <$> rand.random (fin (bit0 1 ^ n))

/-- generate a random bit vector of length `n` -/
def bitvec.random_r {g : Type} [random_gen g] {n : ℕ} (x : bitvec n) (y : bitvec n) (h : x ≤ y) : rand_g g ↥(set.Icc x y) :=
  (fun (h' : ∀ (a : fin (bit0 1 ^ n)), a ∈ set.Icc (bitvec.to_fin x) (bitvec.to_fin y) → bitvec.of_fin a ∈ set.Icc x y) =>
      subtype.map bitvec.of_fin h' <$>
        rand.random_r (bitvec.to_fin x) (bitvec.to_fin y) (bitvec.to_fin_le_to_fin_of_le h))
    sorry

protected instance random_bitvec (n : ℕ) : random (bitvec n) :=
  random.mk fun (_x : Type) (inst : random_gen _x) => bitvec.random n

protected instance bounded_random_bitvec (n : ℕ) : bounded_random (bitvec n) :=
  bounded_random.mk fun (_x : Type) (inst : random_gen _x) (x y : bitvec n) (p : x ≤ y) => bitvec.random_r x y p

