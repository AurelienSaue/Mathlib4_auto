/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Free abelian groups as abelianization of free groups.

-- TODO: rewrite in terms of finsupp
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.group.pi
import Mathlib.group_theory.free_group
import Mathlib.group_theory.abelianization
import Mathlib.PostPort

universes u v u_1 u_2 u_3 

namespace Mathlib

def free_abelian_group (α : Type u)  :=
  additive (abelianization (free_group α))

protected instance free_abelian_group.add_comm_group (α : Type u) : add_comm_group (free_abelian_group α) :=
  additive.add_comm_group

protected instance free_abelian_group.inhabited (α : Type u) : Inhabited (free_abelian_group α) :=
  { default := 0 }

namespace free_abelian_group


def of {α : Type u} (x : α) : free_abelian_group α :=
  coe_fn abelianization.of (free_group.of x)

def lift {α : Type u} {β : Type v} [add_comm_group β] (f : α → β) : free_abelian_group α →+ β :=
  coe_fn monoid_hom.to_additive (abelianization.lift (monoid_hom.of ⇑(free_group.to_group f)))

namespace lift


@[simp] protected theorem add {α : Type u} {β : Type v} [add_comm_group β] (f : α → β) (x : free_abelian_group α) (y : free_abelian_group α) : coe_fn (lift f) (x + y) = coe_fn (lift f) x + coe_fn (lift f) y :=
  is_add_hom.map_add (⇑(lift f)) x y

@[simp] protected theorem neg {α : Type u} {β : Type v} [add_comm_group β] (f : α → β) (x : free_abelian_group α) : coe_fn (lift f) (-x) = -coe_fn (lift f) x :=
  is_add_group_hom.map_neg (⇑(lift f)) x

@[simp] protected theorem sub {α : Type u} {β : Type v} [add_comm_group β] (f : α → β) (x : free_abelian_group α) (y : free_abelian_group α) : coe_fn (lift f) (x - y) = coe_fn (lift f) x - coe_fn (lift f) y := sorry

@[simp] protected theorem zero {α : Type u} {β : Type v} [add_comm_group β] (f : α → β) : coe_fn (lift f) 0 = 0 :=
  is_add_group_hom.map_zero ⇑(lift f)

@[simp] protected theorem of {α : Type u} {β : Type v} [add_comm_group β] (f : α → β) (x : α) : coe_fn (lift f) (of x) = f x := sorry

protected theorem unique {α : Type u} {β : Type v} [add_comm_group β] (f : α → β) (g : free_abelian_group α →+ β) (hg : ∀ (x : α), coe_fn g (of x) = f x) {x : free_abelian_group α} : coe_fn g x = coe_fn (lift f) x :=
  abelianization.lift.unique (monoid_hom.of ⇑(free_group.to_group f)) (coe_fn add_monoid_hom.to_multiplicative g)
    fun (x : free_group α) =>
      free_group.to_group.unique (monoid_hom.comp (coe_fn add_monoid_hom.to_multiplicative' g) abelianization.of) hg

/-- See note [partially-applied ext lemmas]. -/
protected theorem ext {α : Type u} {β : Type v} [add_comm_group β] (g : free_abelian_group α →+ β) (h : free_abelian_group α →+ β) (H : ∀ (x : α), coe_fn g (of x) = coe_fn h (of x)) : g = h := sorry

theorem map_hom {α : Type u_1} {β : Type u_2} {γ : Type u_3} [add_comm_group β] [add_comm_group γ] (a : free_abelian_group α) (f : α → β) (g : β →+ γ) : coe_fn g (coe_fn (lift f) a) = coe_fn (lift (⇑g ∘ f)) a := sorry

end lift


theorem of_injective {α : Type u} : function.injective of := sorry

/-- The bijection underlying the free-forgetful adjunction for abelian groups.-/
def hom_equiv (X : Type u_1) (G : Type u_2) [add_comm_group G] : (free_abelian_group X →+ G) ≃ (X → G) :=
  equiv.mk (fun (f : free_abelian_group X →+ G) => add_monoid_hom.to_fun f ∘ of)
    (fun (f : X → G) => add_monoid_hom.of ⇑(lift f)) sorry sorry

@[simp] theorem hom_equiv_apply (X : Type u_1) (G : Type u_2) [add_comm_group G] (f : free_abelian_group X →+ G) (x : X) : coe_fn (hom_equiv X G) f x = coe_fn f (of x) :=
  rfl

@[simp] theorem hom_equiv_symm_apply (X : Type u_1) (G : Type u_2) [add_comm_group G] (f : X → G) (x : free_abelian_group X) : coe_fn (coe_fn (equiv.symm (hom_equiv X G)) f) x = coe_fn (lift f) x :=
  rfl

protected theorem induction_on {α : Type u} {C : free_abelian_group α → Prop} (z : free_abelian_group α) (C0 : C 0) (C1 : ∀ (x : α), C (of x)) (Cn : ∀ (x : α), C (of x) → C (-of x)) (Cp : ∀ (x y : free_abelian_group α), C x → C y → C (x + y)) : C z := sorry

theorem lift.add' {α : Type u_1} {β : Type u_2} [add_comm_group β] (a : free_abelian_group α) (f : α → β) (g : α → β) : coe_fn (lift (f + g)) a = coe_fn (lift f) a + coe_fn (lift g) a := sorry

protected instance is_add_group_hom_lift' {α : Type u_1} (β : Type u_2) [add_comm_group β] (a : free_abelian_group α) : is_add_group_hom fun (f : α → β) => coe_fn (lift f) a :=
  is_add_group_hom.mk

protected instance monad : Monad free_abelian_group := sorry

protected theorem induction_on' {α : Type u} {C : free_abelian_group α → Prop} (z : free_abelian_group α) (C0 : C 0) (C1 : ∀ (x : α), C (pure x)) (Cn : ∀ (x : α), C (pure x) → C (-pure x)) (Cp : ∀ (x y : free_abelian_group α), C x → C y → C (x + y)) : C z :=
  free_abelian_group.induction_on z C0 C1 Cn Cp

@[simp] theorem map_pure {α : Type u} {β : Type u} (f : α → β) (x : α) : f <$> pure x = pure (f x) :=
  lift.of (of ∘ f) x

@[simp] theorem map_zero {α : Type u} {β : Type u} (f : α → β) : f <$> 0 = 0 :=
  lift.zero (of ∘ f)

@[simp] theorem map_add {α : Type u} {β : Type u} (f : α → β) (x : free_abelian_group α) (y : free_abelian_group α) : f <$> (x + y) = f <$> x + f <$> y :=
  lift.add (of ∘ f) x y

@[simp] theorem map_neg {α : Type u} {β : Type u} (f : α → β) (x : free_abelian_group α) : f <$> (-x) = -f <$> x :=
  lift.neg (of ∘ f) x

@[simp] theorem map_sub {α : Type u} {β : Type u} (f : α → β) (x : free_abelian_group α) (y : free_abelian_group α) : f <$> (x - y) = f <$> x - f <$> y :=
  lift.sub (of ∘ f) x y

@[simp] theorem map_of {α : Type u} {β : Type u} (f : α → β) (y : α) : f <$> of y = of (f y) :=
  rfl

/-- The additive group homomorphism `free_abelian_group α →+ free_abelian_group β` induced from a
  map `α → β` -/
def map {α : Type u} {β : Type u} (f : α → β) : free_abelian_group α →+ free_abelian_group β :=
  add_monoid_hom.mk' (fun (x : free_abelian_group α) => f <$> x) (map_add f)

theorem lift_comp {α : Type u_1} {β : Type u_1} {γ : Type u_2} [add_comm_group γ] (f : α → β) (g : β → γ) (x : free_abelian_group α) : coe_fn (lift (g ∘ f)) x = coe_fn (lift g) (f <$> x) := sorry

@[simp] theorem pure_bind {α : Type u} {β : Type u} (f : α → free_abelian_group β) (x : α) : pure x >>= f = f x :=
  lift.of f x

@[simp] theorem zero_bind {α : Type u} {β : Type u} (f : α → free_abelian_group β) : 0 >>= f = 0 :=
  lift.zero f

@[simp] theorem add_bind {α : Type u} {β : Type u} (f : α → free_abelian_group β) (x : free_abelian_group α) (y : free_abelian_group α) : x + y >>= f = (x >>= f) + (y >>= f) :=
  lift.add f x y

@[simp] theorem neg_bind {α : Type u} {β : Type u} (f : α → free_abelian_group β) (x : free_abelian_group α) : -x >>= f = -(x >>= f) :=
  lift.neg f x

@[simp] theorem sub_bind {α : Type u} {β : Type u} (f : α → free_abelian_group β) (x : free_abelian_group α) (y : free_abelian_group α) : x - y >>= f = (x >>= f) - (y >>= f) :=
  lift.sub f x y

@[simp] theorem pure_seq {α : Type u} {β : Type u} (f : α → β) (x : free_abelian_group α) : pure f <*> x = f <$> x :=
  pure_bind
    (fun (_x : α → β) => (fun (α β : Type u) (f : α → β) (x : free_abelian_group α) => coe_fn (lift (of ∘ f)) x) α β _x x)
    f

@[simp] theorem zero_seq {α : Type u} {β : Type u} (x : free_abelian_group α) : 0 <*> x = 0 :=
  zero_bind
    fun (_x : α → β) => (fun (α β : Type u) (f : α → β) (x : free_abelian_group α) => coe_fn (lift (of ∘ f)) x) α β _x x

@[simp] theorem add_seq {α : Type u} {β : Type u} (f : free_abelian_group (α → β)) (g : free_abelian_group (α → β)) (x : free_abelian_group α) : f + g <*> x = (f <*> x) + (g <*> x) :=
  add_bind
    (fun (_x : α → β) => (fun (α β : Type u) (f : α → β) (x : free_abelian_group α) => coe_fn (lift (of ∘ f)) x) α β _x x)
    f g

@[simp] theorem neg_seq {α : Type u} {β : Type u} (f : free_abelian_group (α → β)) (x : free_abelian_group α) : -f <*> x = -(f <*> x) :=
  neg_bind
    (fun (_x : α → β) => (fun (α β : Type u) (f : α → β) (x : free_abelian_group α) => coe_fn (lift (of ∘ f)) x) α β _x x)
    f

@[simp] theorem sub_seq {α : Type u} {β : Type u} (f : free_abelian_group (α → β)) (g : free_abelian_group (α → β)) (x : free_abelian_group α) : f - g <*> x = (f <*> x) - (g <*> x) :=
  sub_bind
    (fun (_x : α → β) => (fun (α β : Type u) (f : α → β) (x : free_abelian_group α) => coe_fn (lift (of ∘ f)) x) α β _x x)
    f g

protected instance is_add_group_hom_seq {α : Type u} {β : Type u} (f : free_abelian_group (α → β)) : is_add_group_hom (Seq.seq f) :=
  is_add_group_hom.mk

@[simp] theorem seq_zero {α : Type u} {β : Type u} (f : free_abelian_group (α → β)) : f <*> 0 = 0 :=
  is_add_group_hom.map_zero (Seq.seq f)

@[simp] theorem seq_add {α : Type u} {β : Type u} (f : free_abelian_group (α → β)) (x : free_abelian_group α) (y : free_abelian_group α) : f <*> x + y = (f <*> x) + (f <*> y) :=
  is_add_hom.map_add (Seq.seq f) x y

@[simp] theorem seq_neg {α : Type u} {β : Type u} (f : free_abelian_group (α → β)) (x : free_abelian_group α) : f <*> -x = -(f <*> x) :=
  is_add_group_hom.map_neg (Seq.seq f) x

@[simp] theorem seq_sub {α : Type u} {β : Type u} (f : free_abelian_group (α → β)) (x : free_abelian_group α) (y : free_abelian_group α) : f <*> x - y = (f <*> x) - (f <*> y) :=
  is_add_group_hom.map_sub (Seq.seq f) x y

protected instance is_lawful_monad : is_lawful_monad free_abelian_group := sorry

protected instance is_comm_applicative : is_comm_applicative free_abelian_group := sorry

protected instance semigroup (α : Type u) [monoid α] : semigroup (free_abelian_group α) :=
  semigroup.mk (fun (x : free_abelian_group α) => ⇑(lift fun (x₂ : α) => coe_fn (lift fun (x₁ : α) => of (x₁ * x₂)) x))
    sorry

theorem mul_def (α : Type u) [monoid α] (x : free_abelian_group α) (y : free_abelian_group α) : x * y = coe_fn (lift fun (x₂ : α) => coe_fn (lift fun (x₁ : α) => of (x₁ * x₂)) x) y :=
  rfl

theorem of_mul_of (α : Type u) [monoid α] (x : α) (y : α) : of x * of y = of (x * y) :=
  rfl

theorem of_mul (α : Type u) [monoid α] (x : α) (y : α) : of (x * y) = of x * of y :=
  rfl

protected instance ring (α : Type u) [monoid α] : ring (free_abelian_group α) :=
  ring.mk add_comm_group.add sorry add_comm_group.zero sorry sorry add_comm_group.neg add_comm_group.sub sorry sorry
    semigroup.mul sorry (of 1) sorry sorry sorry sorry

theorem one_def (α : Type u) [monoid α] : 1 = of 1 :=
  rfl

theorem of_one (α : Type u) [monoid α] : of 1 = 1 :=
  rfl

protected instance comm_ring (α : Type u) [comm_monoid α] : comm_ring (free_abelian_group α) :=
  comm_ring.mk ring.add sorry ring.zero sorry sorry ring.neg ring.sub sorry sorry ring.mul sorry ring.one sorry sorry
    sorry sorry sorry

