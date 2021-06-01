/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau, Robert Y. Lewis
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.group.basic
import Mathlib.PostPort

universes u l 

namespace Mathlib

/-!
# Eckmann-Hilton argument

The Eckmann-Hilton argument says that if a type carries two monoid structures that distribute
over one another, then they are equal, and in addition commutative.
The main application lies in proving that higher homotopy groups (`πₙ` for `n ≥ 2`) are commutative.

## Main declarations

* `eckmann_hilton.comm_monoid`: If a type carries two unital binary operations that distribute
  over each other, then these operations are equal, and form a commutative monoid structure.
* `eckmann_hilton.comm_group`: If a type carries a group structure that distributes
  over a unital binary operation, then the group is commutative.

-/

namespace eckmann_hilton


/-- `is_unital m e` expresses that `e : X` is a left and right unit
for the binary operation `m : X → X → X`. -/
class is_unital {X : Type u} (m : X → X → X) (e : X) where
  one_mul : ∀ (x : X), m e x = x
  mul_one : ∀ (x : X), m x e = x

theorem Mathlib.add_group.is_unital {X : Type u} [G : add_group X] : is_unital Add.add 0 :=
  is_unital.mk add_group.zero_add add_group.add_zero

/-- If a type carries two unital binary operations that distribute over each other,
then they have the same unit elements.

In fact, the two operations are the same, and give a commutative monoid structure,
see `eckmann_hilton.comm_monoid`. -/
theorem one {X : Type u} {m₁ : X → X → X} {m₂ : X → X → X} {e₁ : X} {e₂ : X} (h₁ : is_unital m₁ e₁)
    (h₂ : is_unital m₂ e₂)
    (distrib : ∀ (a b c d : X), m₁ (m₂ a b) (m₂ c d) = m₂ (m₁ a c) (m₁ b d)) : e₁ = e₂ :=
  sorry

/-- If a type carries two unital binary operations that distribute over each other,
then these operations are equal.

In fact, they give a commutative monoid structure, see `eckmann_hilton.comm_monoid`. -/
theorem mul {X : Type u} {m₁ : X → X → X} {m₂ : X → X → X} {e₁ : X} {e₂ : X} (h₁ : is_unital m₁ e₁)
    (h₂ : is_unital m₂ e₂)
    (distrib : ∀ (a b c d : X), m₁ (m₂ a b) (m₂ c d) = m₂ (m₁ a c) (m₁ b d)) : m₁ = m₂ :=
  sorry

/-- If a type carries two unital binary operations that distribute over each other,
then these operations are commutative.

In fact, they give a commutative monoid structure, see `eckmann_hilton.comm_monoid`. -/
theorem mul_comm {X : Type u} {m₁ : X → X → X} {m₂ : X → X → X} {e₁ : X} {e₂ : X}
    (h₁ : is_unital m₁ e₁) (h₂ : is_unital m₂ e₂)
    (distrib : ∀ (a b c d : X), m₁ (m₂ a b) (m₂ c d) = m₂ (m₁ a c) (m₁ b d)) :
    is_commutative X m₂ :=
  sorry

/-- If a type carries two unital binary operations that distribute over each other,
then these operations are associative.

In fact, they give a commutative monoid structure, see `eckmann_hilton.comm_monoid`. -/
theorem mul_assoc {X : Type u} {m₁ : X → X → X} {m₂ : X → X → X} {e₁ : X} {e₂ : X}
    (h₁ : is_unital m₁ e₁) (h₂ : is_unital m₂ e₂)
    (distrib : ∀ (a b c d : X), m₁ (m₂ a b) (m₂ c d) = m₂ (m₁ a c) (m₁ b d)) :
    is_associative X m₂ :=
  sorry

/-- If a type carries two unital binary operations that distribute over each other,
then these operations are equal, and form a commutative monoid structure. -/
def comm_monoid {X : Type u} {m₁ : X → X → X} {m₂ : X → X → X} {e₁ : X} {e₂ : X}
    (h₁ : is_unital m₁ e₁) (h₂ : is_unital m₂ e₂)
    (distrib : ∀ (a b c d : X), m₁ (m₂ a b) (m₂ c d) = m₂ (m₁ a c) (m₁ b d)) : comm_monoid X :=
  comm_monoid.mk m₂ sorry e₂ is_unital.one_mul is_unital.mul_one sorry

/-- If a type carries a group structure that distributes over a unital binary operation,
then the group is commutative. -/
def comm_group {X : Type u} {m₁ : X → X → X} {e₁ : X} (h₁ : is_unital m₁ e₁) [G : group X]
    (distrib : ∀ (a b c d : X), m₁ (a * b) (c * d) = m₁ a c * m₁ b d) : comm_group X :=
  comm_group.mk group.mul group.mul_assoc group.one group.one_mul group.mul_one group.inv group.div
    group.mul_left_inv sorry

end Mathlib