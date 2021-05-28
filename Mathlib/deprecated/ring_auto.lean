/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.deprecated.group
import PostPort

universes u v l u_1 u_2 

namespace Mathlib

/-!
# Unbundled semiring and ring homomorphisms (deprecated)

This file defines typeclasses for unbundled semiring and ring homomorphisms. Though these classes are
deprecated, they are still widely used in mathlib, and probably will not go away before Lean 4
because Lean 3 often fails to coerce a bundled homomorphism to a function.

## main definitions

is_semiring_hom (deprecated), is_ring_hom (deprecated)

## Tags

is_semiring_hom, is_ring_hom

-/

/-- Predicate for semiring homomorphisms (deprecated -- use the bundled `ring_hom` version). -/
class is_semiring_hom {α : Type u} {β : Type v} [semiring α] [semiring β] (f : α → β) 
where
  map_zero : f 0 = 0
  map_one : f 1 = 1
  map_add : ∀ {x y : α}, f (x + y) = f x + f y
  map_mul : ∀ {x y : α}, f (x * y) = f x * f y

namespace is_semiring_hom


/-- The identity map is a semiring homomorphism. -/
protected instance id {α : Type u} [semiring α] : is_semiring_hom id :=
  mk (Eq.refl (id 0)) (Eq.refl (id 1)) (fun (x y : α) => Eq.refl (id (x + y))) fun (x y : α) => Eq.refl (id (x * y))

/-- The composition of two semiring homomorphisms is a semiring homomorphism. -/
-- see Note [no instance on morphisms]

theorem comp {α : Type u} {β : Type v} [semiring α] [semiring β] (f : α → β) [is_semiring_hom f] {γ : Type u_1} [semiring γ] (g : β → γ) [is_semiring_hom g] : is_semiring_hom (g ∘ f) := sorry

/-- A semiring homomorphism is an additive monoid homomorphism. -/
protected instance is_add_monoid_hom {α : Type u} {β : Type v} [semiring α] [semiring β] (f : α → β) [is_semiring_hom f] : is_add_monoid_hom f :=
  is_add_monoid_hom.mk (map_zero f)

/-- A semiring homomorphism is a monoid homomorphism. -/
protected instance is_monoid_hom {α : Type u} {β : Type v} [semiring α] [semiring β] (f : α → β) [is_semiring_hom f] : is_monoid_hom f :=
  is_monoid_hom.mk (map_one f)

end is_semiring_hom


/-- Predicate for ring homomorphisms (deprecated -- use the bundled `ring_hom` version). -/
class is_ring_hom {α : Type u} {β : Type v} [ring α] [ring β] (f : α → β) 
where
  map_one : f 1 = 1
  map_mul : ∀ {x y : α}, f (x * y) = f x * f y
  map_add : ∀ {x y : α}, f (x + y) = f x + f y

namespace is_ring_hom


/-- A map of rings that is a semiring homomorphism is also a ring homomorphism. -/
theorem of_semiring {α : Type u} {β : Type v} [ring α] [ring β] (f : α → β) [H : is_semiring_hom f] : is_ring_hom f :=
  mk (is_semiring_hom.map_one f) (is_semiring_hom.map_mul f) (is_semiring_hom.map_add f)

/-- Ring homomorphisms map zero to zero. -/
theorem map_zero {α : Type u} {β : Type v} [ring α] [ring β] (f : α → β) [is_ring_hom f] : f 0 = 0 := sorry

/-- Ring homomorphisms preserve additive inverses. -/
theorem map_neg {α : Type u} {β : Type v} [ring α] [ring β] (f : α → β) [is_ring_hom f] {x : α} : f (-x) = -f x := sorry

/-- Ring homomorphisms preserve subtraction. -/
theorem map_sub {α : Type u} {β : Type v} [ring α] [ring β] (f : α → β) [is_ring_hom f] {x : α} {y : α} : f (x - y) = f x - f y := sorry

/-- The identity map is a ring homomorphism. -/
protected instance id {α : Type u} [ring α] : is_ring_hom id :=
  mk (Eq.refl (id 1)) (fun (x y : α) => Eq.refl (id (x * y))) fun (x y : α) => Eq.refl (id (x + y))

/-- The composition of two ring homomorphisms is a ring homomorphism. -/
-- see Note [no instance on morphisms]

theorem comp {α : Type u} {β : Type v} [ring α] [ring β] (f : α → β) [is_ring_hom f] {γ : Type u_1} [ring γ] (g : β → γ) [is_ring_hom g] : is_ring_hom (g ∘ f) := sorry

/-- A ring homomorphism is also a semiring homomorphism. -/
protected instance is_semiring_hom {α : Type u} {β : Type v} [ring α] [ring β] (f : α → β) [is_ring_hom f] : is_semiring_hom f :=
  is_semiring_hom.mk (map_zero f) (map_one f) (map_add f) (map_mul f)

protected instance is_add_group_hom {α : Type u} {β : Type v} [ring α] [ring β] (f : α → β) [is_ring_hom f] : is_add_group_hom f :=
  is_add_group_hom.mk

end is_ring_hom


namespace ring_hom


/-- Interpret `f : α → β` with `is_semiring_hom f` as a ring homomorphism. -/
def of {α : Type u} {β : Type v} [rα : semiring α] [rβ : semiring β] (f : α → β) [is_semiring_hom f] : α →+* β :=
  mk f sorry sorry sorry sorry

@[simp] theorem coe_of {α : Type u} {β : Type v} [rα : semiring α] [rβ : semiring β] (f : α → β) [is_semiring_hom f] : ⇑(of f) = f :=
  rfl

protected instance is_semiring_hom {α : Type u} {β : Type v} [rα : semiring α] [rβ : semiring β] (f : α →+* β) : is_semiring_hom ⇑f :=
  is_semiring_hom.mk (map_zero f) (map_one f) (map_add f) (map_mul f)

protected instance is_ring_hom {α : Type u_1} {γ : Type u_2} [ring α] [ring γ] (g : α →+* γ) : is_ring_hom ⇑g :=
  is_ring_hom.of_semiring ⇑g

