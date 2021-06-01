/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Chris Hughes
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.ring_theory.coprime
import Mathlib.ring_theory.ideal.basic
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Lemmas about Euclidean domains

Various about Euclidean domains are proved; all of them seem to be true
more generally for principal ideal domains, so these lemmas should
probably be reproved in more generality and this file perhaps removed?

## Tags

euclidean domain
-/

-- TODO -- this should surely be proved for PIDs instead?

theorem span_gcd {α : Type u_1} [euclidean_domain α] (x : α) (y : α) :
    ideal.span (singleton (euclidean_domain.gcd x y)) = ideal.span (insert x (singleton y)) :=
  sorry

-- this should be proved for PIDs?

theorem gcd_is_unit_iff {α : Type u_1} [euclidean_domain α] {x : α} {y : α} :
    is_unit (euclidean_domain.gcd x y) ↔ is_coprime x y :=
  sorry

-- this should be proved for UFDs surely?

theorem is_coprime_of_dvd {α : Type u_1} [euclidean_domain α] {x : α} {y : α} (z : ¬(x = 0 ∧ y = 0))
    (H : ∀ (z : α), z ∈ nonunits α → z ≠ 0 → z ∣ x → ¬z ∣ y) : is_coprime x y :=
  sorry

-- this should be proved for UFDs surely?

theorem dvd_or_coprime {α : Type u_1} [euclidean_domain α] (x : α) (y : α) (h : irreducible x) :
    x ∣ y ∨ is_coprime x y :=
  sorry

end Mathlib