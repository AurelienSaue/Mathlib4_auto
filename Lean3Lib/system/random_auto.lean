/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import PrePort
import Lean3Lib.init.default
import PostPort

universes u l 

namespace Mathlib

/-
Basic random number generator support based on the one
available on the Haskell library
-/

/- Interface for random number generators. -/

/- `range` returns the range of values returned by
class random_gen (g : Type u) 
where
  range : g → ℕ × ℕ
  next : g → ℕ × g
  split : g → g × g

    the generator. -/

/- `next` operation returns a natural number that is uniformly distributed
    the range returned by `range` (including both end points),
   and a new generator. -/

/-
  The 'split' operation allows one to obtain two distinct random number
  generators. This is very useful in functional programs (for example, when
  passing a random number generator down to recursive calls). -/

/- "Standard" random number generator. -/

structure std_gen 
where
  s1 : ℕ
  s2 : ℕ

def std_range : ℕ × ℕ :=
  (1,
  bit0
    (bit1
      (bit0
        (bit1
          (bit0
            (bit1
              (bit0
                (bit1
                  (bit1
                    (bit1
                      (bit1
                        (bit1
                          (bit1
                            (bit1
                              (bit1
                                (bit1
                                  (bit1
                                    (bit1
                                      (bit1
                                        (bit1
                                          (bit1
                                            (bit1
                                              (bit1
                                                (bit1 (bit1 (bit1 (bit1 (bit1 (bit1 (bit1 1))))))))))))))))))))))))))))))

protected instance std_gen.has_repr : has_repr std_gen :=
  has_repr.mk fun (_x : std_gen) => sorry

def std_next : std_gen → ℕ × std_gen :=
  sorry

def std_split : std_gen → std_gen × std_gen :=
  sorry

protected instance std_gen.random_gen : random_gen std_gen :=
  random_gen.mk (fun (_x : std_gen) => std_range) std_next std_split

/-- Return a standard number generator. -/
def mk_std_gen (s : optParam ℕ 0) : std_gen := sorry

/-
Auxiliary function for random_nat_val.
Generate random values until we exceed the target magnitude.
`gen_lo` and `gen_mag` are the generator lower bound and magnitude.
The parameter `r` is the "remaining" magnitude.
-/

/-- Generate a random natural number in the interval [lo, hi]. -/
def rand_nat {gen : Type u} [random_gen gen] (g : gen) (lo : ℕ) (hi : ℕ) : ℕ × gen :=
  let lo' : ℕ := ite (lo > hi) hi lo;
  let hi' : ℕ := ite (lo > hi) lo hi;
  sorry

/-- Generate a random Boolean. -/
def rand_bool {gen : Type u} [random_gen gen] (g : gen) : Bool × gen :=
  sorry

