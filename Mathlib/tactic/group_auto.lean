/-
Copyright (c) 2020. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Patrick Massot
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.tactic.ring
import Mathlib.tactic.doc_commands
import PostPort

universes u_1 

namespace Mathlib

/-!
# `group`

Normalizes expressions in the language of groups. The basic idea is to use the simplifier
to put everything into a product of group powers (`gpow` which takes a group element and an
integer), then simplify the exponents using the `ring` tactic. The process needs to be repeated
since `ring` can normalize an exponent to zero, leading to a factor that can be removed
before collecting exponents again. The simplifier step also uses some extra lemmas to avoid
some `ring` invocations.

## Tags

group_theory
-/

-- The next four lemmas are not general purpose lemmas, they are intended for use only by

-- the `group` tactic.

theorem tactic.group.gpow_trick {G : Type u_1} [group G] (a : G) (b : G) (n : ℤ) (m : ℤ) : a * b ^ n * b ^ m = a * b ^ (n + m) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a * b ^ n * b ^ m = a * b ^ (n + m))) (mul_assoc a (b ^ n) (b ^ m))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * (b ^ n * b ^ m) = a * b ^ (n + m))) (Eq.symm (gpow_add b n m))))
      (Eq.refl (a * b ^ (n + m))))

theorem tactic.group.gpow_trick_one {G : Type u_1} [group G] (a : G) (b : G) (m : ℤ) : a * b * b ^ m = a * b ^ (m + 1) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a * b * b ^ m = a * b ^ (m + 1))) (mul_assoc a b (b ^ m))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * (b * b ^ m) = a * b ^ (m + 1))) (mul_self_gpow b m)))
      (Eq.refl (a * b ^ (m + 1))))

theorem tactic.group.gpow_trick_one' {G : Type u_1} [group G] (a : G) (b : G) (n : ℤ) : a * b ^ n * b = a * b ^ (n + 1) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a * b ^ n * b = a * b ^ (n + 1))) (mul_assoc a (b ^ n) b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * (b ^ n * b) = a * b ^ (n + 1))) (mul_gpow_self b n)))
      (Eq.refl (a * b ^ (n + 1))))

theorem tactic.group.gpow_trick_sub {G : Type u_1} [group G] (a : G) (b : G) (n : ℤ) (m : ℤ) : a * b ^ n * b ^ (-m) = a * b ^ (n - m) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a * b ^ n * b ^ (-m) = a * b ^ (n - m))) (mul_assoc a (b ^ n) (b ^ (-m)))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * (b ^ n * b ^ (-m)) = a * b ^ (n - m))) (Eq.symm (gpow_add b n (-m)))))
      (Eq.refl (a * b ^ (n + -m))))

namespace tactic


/-- Auxilliary tactic for the `group` tactic. Calls the simplifier only. -/
/-- Auxilliary tactic for the `group` tactic. Calls `ring` to normalize exponents. -/
end tactic


namespace tactic.interactive


/--
Tactic for normalizing expressions in multiplicative groups, without assuming
commutativity, using only the group axioms without any information about which group
is manipulated.

(For additive commutative groups, use the `abel` tactic instead.)

Example:
```lean
example {G : Type} [group G] (a b c d : G) (h : c = (a*b^2)*((b*b)⁻¹*a⁻¹)*d) : a*c*d⁻¹ = a :=
begin
  group at h, -- normalizes `h` which becomes `h : c = d`
  rw h,       -- the goal is now `a*d*d⁻¹ = a`
  group,      -- which then normalized and closed
end
```
-/
end tactic.interactive


