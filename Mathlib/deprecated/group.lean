/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.group.type_tags
import Mathlib.algebra.group.units_hom
import Mathlib.algebra.ring.basic
import Mathlib.data.equiv.mul_add
import Mathlib.PostPort

universes u_1 u_2 l u v 

namespace Mathlib

/-!
# Unbundled monoid and group homomorphisms (deprecated)

This file defines typeclasses for unbundled monoid and group homomorphisms. Though these classes are
deprecated, they are still widely used in mathlib, and probably will not go away before Lean 4
because Lean 3 often fails to coerce a bundled homomorphism to a function.

## main definitions

is_monoid_hom (deprecated), is_group_hom (deprecated)

## implementation notes

There's a coercion from bundled homs to fun, and the canonical
notation is to use the bundled hom as a function via this coercion.

There is no `group_hom` -- the idea is that `monoid_hom` is used.
The constructor for `monoid_hom` needs a proof of `map_one` as well
as `map_mul`; a separate constructor `monoid_hom.mk'` will construct
group homs (i.e. monoid homs between groups) given only a proof
that multiplication is preserved,

## Tags

is_group_hom, is_monoid_hom, monoid_hom

-/

/--
We have lemmas stating that the composition of two morphisms is again a morphism.
Since composition is reducible, type class inference will always succeed in applying these instances.
For example when the goal is just `⊢ is_mul_hom f` the instance `is_mul_hom.comp`
will still succeed, unifying `f` with `f ∘ (λ x, x)`.  This causes type class inference to loop.
To avoid this, we do not make these lemmas instances.
-/
/-- Predicate for maps which preserve an addition. -/
class is_add_hom {α : Type u_1} {β : Type u_2} [Add α] [Add β] (f : α → β) 
where
  map_add : ∀ (x y : α), f (x + y) = f x + f y

/-- Predicate for maps which preserve a multiplication. -/
class is_mul_hom {α : Type u_1} {β : Type u_2} [Mul α] [Mul β] (f : α → β) 
where
  map_mul : ∀ (x y : α), f (x * y) = f x * f y

namespace is_mul_hom


/-- The identity map preserves multiplication. -/
protected instance Mathlib.is_add_hom.id {α : Type u} [Add α] : is_add_hom id :=
  is_add_hom.mk fun (_x _x_1 : α) => rfl

/-- The composition of maps which preserve multiplication, also preserves multiplication. -/
-- see Note [no instance on morphisms]

theorem comp {α : Type u} {β : Type v} [Mul α] [Mul β] {γ : Type u_1} [Mul γ] (f : α → β) (g : β → γ) [is_mul_hom f] [hg : is_mul_hom g] : is_mul_hom (g ∘ f) := sorry

/-- A product of maps which preserve multiplication,
preserves multiplication when the target is commutative. -/
instance mul {α : Type u_1} {β : Type u_2} [semigroup α] [comm_semigroup β] (f : α → β) (g : α → β) [is_mul_hom f] [is_mul_hom g] : is_mul_hom fun (a : α) => f a * g a := sorry

/-- The inverse of a map which preserves multiplication,
preserves multiplication when the target is commutative. -/
instance inv {α : Type u_1} {β : Type u_2} [Mul α] [comm_group β] (f : α → β) [is_mul_hom f] : is_mul_hom fun (a : α) => f a⁻¹ :=
  mk fun (a b : α) => Eq.symm (map_mul f a b) ▸ mul_inv (f a) (f b)

end is_mul_hom


/-- Predicate for add_monoid homomorphisms (deprecated -- use the bundled `monoid_hom` version). -/
class is_add_monoid_hom {α : Type u} {β : Type v} [add_monoid α] [add_monoid β] (f : α → β) 
extends is_add_hom f
where
  map_zero : f 0 = 0

/-- Predicate for monoid homomorphisms (deprecated -- use the bundled `monoid_hom` version). -/
class is_monoid_hom {α : Type u} {β : Type v} [monoid α] [monoid β] (f : α → β) 
extends is_mul_hom f
where
  map_one : f 1 = 1

namespace monoid_hom


/-!
Throughout this section, some `monoid` arguments are specified with `{}` instead of `[]`.
See note [implicit instance arguments].
-/

/-- Interpret a map `f : M → N` as a homomorphism `M →* N`. -/
def Mathlib.add_monoid_hom.of {M : Type u_1} {N : Type u_2} [mM : add_monoid M] [mN : add_monoid N] (f : M → N) [h : is_add_monoid_hom f] : M →+ N :=
  add_monoid_hom.mk f (is_add_monoid_hom.map_zero f) sorry

@[simp] theorem Mathlib.add_monoid_hom.coe_of {M : Type u_1} {N : Type u_2} {mM : add_monoid M} {mN : add_monoid N} (f : M → N) [is_add_monoid_hom f] : ⇑(add_monoid_hom.of f) = f :=
  rfl

protected instance is_monoid_hom {M : Type u_1} {N : Type u_2} {mM : monoid M} {mN : monoid N} (f : M →* N) : is_monoid_hom ⇑f :=
  is_monoid_hom.mk (map_one f)

end monoid_hom


namespace mul_equiv


/-- A multiplicative isomorphism preserves multiplication (deprecated). -/
protected instance Mathlib.add_equiv.is_add_hom {M : Type u_1} {N : Type u_2} [add_monoid M] [add_monoid N] (h : M ≃+ N) : is_add_hom ⇑h :=
  is_add_hom.mk (add_equiv.map_add h)

/-- A multiplicative bijection between two monoids is a monoid hom
  (deprecated -- use to_monoid_hom). -/
protected instance Mathlib.add_equiv.is_add_monoid_hom {M : Type u_1} {N : Type u_2} [add_monoid M] [add_monoid N] (h : M ≃+ N) : is_add_monoid_hom ⇑h :=
  is_add_monoid_hom.mk (add_equiv.map_zero h)

end mul_equiv


namespace is_monoid_hom


/-- A monoid homomorphism preserves multiplication. -/
theorem Mathlib.is_add_monoid_hom.map_add {α : Type u} {β : Type v} [add_monoid α] [add_monoid β] (f : α → β) [is_add_monoid_hom f] (x : α) (y : α) : f (x + y) = f x + f y :=
  is_add_hom.map_add f x y

end is_monoid_hom


/-- A map to a group preserving multiplication is a monoid homomorphism. -/
theorem is_monoid_hom.of_mul {α : Type u} {β : Type v} [monoid α] [group β] (f : α → β) [is_mul_hom f] : is_monoid_hom f := sorry

namespace is_monoid_hom


/-- The identity map is a monoid homomorphism. -/
protected instance Mathlib.is_add_monoid_hom.id {α : Type u} [add_monoid α] : is_add_monoid_hom id :=
  is_add_monoid_hom.mk rfl

/-- The composite of two monoid homomorphisms is a monoid homomorphism. -/
theorem Mathlib.is_add_monoid_hom.comp {α : Type u} {β : Type v} [add_monoid α] [add_monoid β] (f : α → β) [is_add_monoid_hom f] {γ : Type u_1} [add_monoid γ] (g : β → γ) [is_add_monoid_hom g] : is_add_monoid_hom (g ∘ f) := sorry

end is_monoid_hom


namespace is_add_monoid_hom


/-- Left multiplication in a ring is an additive monoid morphism. -/
protected instance is_add_monoid_hom_mul_left {γ : Type u_1} [semiring γ] (x : γ) : is_add_monoid_hom fun (y : γ) => x * y :=
  mk (mul_zero x)

/-- Right multiplication in a ring is an additive monoid morphism. -/
protected instance is_add_monoid_hom_mul_right {γ : Type u_1} [semiring γ] (x : γ) : is_add_monoid_hom fun (y : γ) => y * x :=
  mk (zero_mul x)

end is_add_monoid_hom


/-- Predicate for additive group homomorphism (deprecated -- use bundled `monoid_hom`). -/
class is_add_group_hom {α : Type u} {β : Type v} [add_group α] [add_group β] (f : α → β) 
extends is_add_hom f
where

/-- Predicate for group homomorphisms (deprecated -- use bundled `monoid_hom`). -/
class is_group_hom {α : Type u} {β : Type v} [group α] [group β] (f : α → β) 
extends is_mul_hom f
where

protected instance monoid_hom.is_group_hom {G : Type u_1} {H : Type u_2} {_x : group G} : ∀ {_x_1 : group H} (f : G →* H), is_group_hom ⇑f :=
  fun (f : G →* H) => is_group_hom.mk

protected instance mul_equiv.is_group_hom {G : Type u_1} {H : Type u_2} {_x : group G} : ∀ {_x_1 : group H} (h : G ≃* H), is_group_hom ⇑h :=
  fun (h : G ≃* H) => is_group_hom.mk

/-- Construct `is_group_hom` from its only hypothesis. The default constructor tries to get
`is_mul_hom` from class instances, and this makes some proofs fail. -/
theorem is_group_hom.mk' {α : Type u} {β : Type v} [group α] [group β] {f : α → β} (hf : ∀ (x y : α), f (x * y) = f x * f y) : is_group_hom f :=
  is_group_hom.mk

namespace is_group_hom


/-- A group homomorphism is a monoid homomorphism. -/
protected instance Mathlib.is_add_group_hom.to_is_add_monoid_hom {α : Type u} {β : Type v} [add_group α] [add_group β] (f : α → β) [is_add_group_hom f] : is_add_monoid_hom f :=
  is_add_monoid_hom.of_add f

/-- A group homomorphism sends 1 to 1. -/
theorem map_one {α : Type u} {β : Type v} [group α] [group β] (f : α → β) [is_group_hom f] : f 1 = 1 :=
  is_monoid_hom.map_one f

/-- A group homomorphism sends inverses to inverses. -/
theorem Mathlib.is_add_group_hom.map_neg {α : Type u} {β : Type v} [add_group α] [add_group β] (f : α → β) [is_add_group_hom f] (a : α) : f (-a) = -f a := sorry

/-- The identity is a group homomorphism. -/
protected instance id {α : Type u} [group α] : is_group_hom id :=
  mk

/-- The composition of two group homomorphisms is a group homomorphism. -/
theorem comp {α : Type u} {β : Type v} [group α] [group β] (f : α → β) [is_group_hom f] {γ : Type u_1} [group γ] (g : β → γ) [is_group_hom g] : is_group_hom (g ∘ f) :=
  mk

/-- A group homomorphism is injective iff its kernel is trivial. -/
theorem Mathlib.is_add_group_hom.injective_iff {α : Type u} {β : Type v} [add_group α] [add_group β] (f : α → β) [is_add_group_hom f] : function.injective f ↔ ∀ (a : α), f a = 0 → a = 0 := sorry

/-- The product of group homomorphisms is a group homomorphism if the target is commutative. -/
instance Mathlib.is_add_group_hom.add {α : Type u_1} {β : Type u_2} [add_group α] [add_comm_group β] (f : α → β) (g : α → β) [is_add_group_hom f] [is_add_group_hom g] : is_add_group_hom fun (a : α) => f a + g a :=
  is_add_group_hom.mk

/-- The inverse of a group homomorphism is a group homomorphism if the target is commutative. -/
instance Mathlib.is_add_group_hom.neg {α : Type u_1} {β : Type u_2} [add_group α] [add_comm_group β] (f : α → β) [is_add_group_hom f] : is_add_group_hom fun (a : α) => -f a :=
  is_add_group_hom.mk

end is_group_hom


namespace ring_hom


/-!
These instances look redundant, because `deprecated.ring` provides `is_ring_hom` for a `→+*`.
Nevertheless these are harmless, and helpful for stripping out dependencies on `deprecated.ring`.
-/

protected instance is_monoid_hom {R : Type u_1} {S : Type u_2} [semiring R] [semiring S] (f : R →+* S) : is_monoid_hom ⇑f :=
  is_monoid_hom.mk (map_one f)

protected instance is_add_monoid_hom {R : Type u_1} {S : Type u_2} [semiring R] [semiring S] (f : R →+* S) : is_add_monoid_hom ⇑f :=
  is_add_monoid_hom.mk (map_zero f)

protected instance is_add_group_hom {R : Type u_1} {S : Type u_2} [ring R] [ring S] (f : R →+* S) : is_add_group_hom ⇑f :=
  is_add_group_hom.mk

end ring_hom


/-- Inversion is a group homomorphism if the group is commutative. -/
instance inv.is_group_hom {α : Type u} [comm_group α] : is_group_hom has_inv.inv :=
  is_group_hom.mk

namespace is_add_group_hom


/-- Additive group homomorphisms commute with subtraction. -/
theorem map_sub {α : Type u} {β : Type v} [add_group α] [add_group β] (f : α → β) [is_add_group_hom f] (a : α) (b : α) : f (a - b) = f a - f b := sorry

end is_add_group_hom


/-- The difference of two additive group homomorphisms is an additive group
homomorphism if the target is commutative. -/
instance is_add_group_hom.sub {α : Type u_1} {β : Type u_2} [add_group α] [add_comm_group β] (f : α → β) (g : α → β) [is_add_group_hom f] [is_add_group_hom g] : is_add_group_hom fun (a : α) => f a - g a := sorry

namespace units


/-- The group homomorphism on units induced by a multiplicative morphism. -/
def map' {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] (f : M → N) [is_monoid_hom f] : units M →* units N :=
  map (monoid_hom.of f)

@[simp] theorem coe_map' {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] (f : M → N) [is_monoid_hom f] (x : units M) : ↑(coe_fn (map' f) x) = f ↑x :=
  rfl

protected instance coe_is_monoid_hom {M : Type u_1} [monoid M] : is_monoid_hom coe :=
  monoid_hom.is_monoid_hom (coe_hom M)

end units


namespace is_unit


theorem map' {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] (f : M → N) {x : M} (h : is_unit x) [is_monoid_hom f] : is_unit (f x) :=
  map (monoid_hom.of f) h

end is_unit


theorem additive.is_add_hom {α : Type u} {β : Type v} [Mul α] [Mul β] (f : α → β) [is_mul_hom f] : is_add_hom f :=
  is_add_hom.mk (is_mul_hom.map_mul f)

theorem multiplicative.is_mul_hom {α : Type u} {β : Type v} [Add α] [Add β] (f : α → β) [is_add_hom f] : is_mul_hom f :=
  is_mul_hom.mk (is_add_hom.map_add f)

theorem additive.is_add_monoid_hom {α : Type u} {β : Type v} [monoid α] [monoid β] (f : α → β) [is_monoid_hom f] : is_add_monoid_hom f :=
  is_add_monoid_hom.mk (is_monoid_hom.map_one f)

theorem multiplicative.is_monoid_hom {α : Type u} {β : Type v} [add_monoid α] [add_monoid β] (f : α → β) [is_add_monoid_hom f] : is_monoid_hom f :=
  is_monoid_hom.mk (is_add_monoid_hom.map_zero f)

theorem additive.is_add_group_hom {α : Type u} {β : Type v} [group α] [group β] (f : α → β) [is_group_hom f] : is_add_group_hom f :=
  is_add_group_hom.mk

theorem multiplicative.is_group_hom {α : Type u} {β : Type v} [add_group α] [add_group β] (f : α → β) [is_add_group_hom f] : is_group_hom f :=
  is_group_hom.mk

