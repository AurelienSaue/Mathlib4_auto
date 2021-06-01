/-
Copyright (c) 2019 Keeley Hoek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keeley Hoek
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.norm_num
import Mathlib.PostPort

namespace Mathlib

namespace tactic


namespace local_cache


namespace internal


-- We maintain two separate caches with different scopes:

-- one local to `begin ... end` or `by` blocks, and another

-- for entire `def`/`lemma`s.

-- Returns the name of the def used to store the contents of is cache,

-- making a new one and recording this in private state if neccesary.

-- Same as above but fails instead of making a new name, and never

-- mutates state.

-- Asks whether the namespace `ns` currently has a value-in-cache

-- Clear cache associated to namespace `ns`

namespace block_local


-- `mk_new` gives a way to generate a new name if no current one

-- exists.

-- Like `get_name`, but fail if `ns` does not have a cached

-- decl name (we create a new one above).

end block_local


namespace def_local


-- Fowler-Noll-Vo hash function (FNV-1a)

def FNV_OFFSET_BASIS : ℕ := sorry

def FNV_PRIME : ℕ := sorry

def RADIX : ℕ := sorry

def hash_byte (seed : ℕ) (c : char) : ℕ :=
  let n : ℕ := char.to_nat c;
  nat.lxor seed n * FNV_PRIME % RADIX

def hash_string (s : string) : ℕ := list.foldl hash_byte FNV_OFFSET_BASIS (string.to_list s)

end Mathlib