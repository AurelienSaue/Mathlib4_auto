/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.equiv.basic
import Mathlib.control.applicative
import Mathlib.control.traversable.basic
import Mathlib.PostPort

universes u l v u_1 

namespace Mathlib

/-!
# Free constructions

## Main definitions

* `free_magma α`: free magma (structure with binary operation without any axioms) over alphabet `α`,
  defined inductively, with traversable instance and decidable equality.
* `magma.free_semigroup α`: free semigroup over magma `α`.
* `free_semigroup α`: free semigroup over alphabet `α`, defined as a synonym for `α × list α`
  (i.e. nonempty lists), with traversable instance and decidable equality.
* `free_semigroup_free_magma α`: isomorphism between `magma.free_semigroup (free_magma α)` and
  `free_semigroup α`.
-/

/-- Free magma over a given alphabet. -/
inductive free_magma (α : Type u) 
where
| of : α → free_magma α
| mul : free_magma α → free_magma α → free_magma α

/-- Free nonabelian additive magma over a given alphabet. -/
inductive free_add_magma (α : Type u) 
where
| of : α → free_add_magma α
| add : free_add_magma α → free_add_magma α → free_add_magma α

namespace free_magma


protected instance Mathlib.free_add_magma.inhabited {α : Type u} [Inhabited α] : Inhabited (free_add_magma α) :=
  { default := free_add_magma.of Inhabited.default }

protected instance Mathlib.free_add_magma.has_add {α : Type u} : Add (free_add_magma α) :=
  { add := free_add_magma.add }

@[simp] theorem Mathlib.free_add_magma.add_eq {α : Type u} (x : free_add_magma α) (y : free_add_magma α) : free_add_magma.add x y = x + y :=
  rfl

/-- Recursor for `free_magma` using `x * y` instead of `free_magma.mul x y`. -/
def Mathlib.free_add_magma.rec_on' {α : Type u} {C : free_add_magma α → Sort l} (x : free_add_magma α) (ih1 : (x : α) → C (free_add_magma.of x)) (ih2 : (x y : free_add_magma α) → C x → C y → C (x + y)) : C x :=
  free_add_magma.rec_on x ih1 ih2

end free_magma


/-- Lifts a function `α → β` to a magma homomorphism `free_magma α → β` given a magma `β`. -/
def free_magma.lift {α : Type u} {β : Type v} [Mul β] (f : α → β) : free_magma α → β :=
  sorry

/-- Lifts a function `α → β` to an additive magma homomorphism `free_add_magma α → β` given
an additive magma `β`. -/
def free_add_magma.lift {α : Type u} {β : Type v} [Add β] (f : α → β) : free_add_magma α → β :=
  sorry

namespace free_magma


@[simp] theorem Mathlib.free_add_magma.lift_of {α : Type u} {β : Type v} [Add β] (f : α → β) (x : α) : free_add_magma.lift f (free_add_magma.of x) = f x :=
  rfl

@[simp] theorem lift_mul {α : Type u} {β : Type v} [Mul β] (f : α → β) (x : free_magma α) (y : free_magma α) : lift f (x * y) = lift f x * lift f y :=
  rfl

theorem lift_unique {α : Type u} {β : Type v} [Mul β] (f : free_magma α → β) (hf : ∀ (x y : free_magma α), f (x * y) = f x * f y) : f = lift (f ∘ of) := sorry

end free_magma


/-- The unique magma homomorphism `free_magma α → free_magma β` that sends
each `of x` to `of (f x)`. -/
def free_magma.map {α : Type u} {β : Type v} (f : α → β) : free_magma α → free_magma β :=
  sorry

/-- The unique additive magma homomorphism `free_add_magma α → free_add_magma β` that sends
each `of x` to `of (f x)`. -/
def free_add_magma.map {α : Type u} {β : Type v} (f : α → β) : free_add_magma α → free_add_magma β :=
  sorry

namespace free_magma


@[simp] theorem Mathlib.free_add_magma.map_of {α : Type u} {β : Type v} (f : α → β) (x : α) : free_add_magma.map f (free_add_magma.of x) = free_add_magma.of (f x) :=
  rfl

@[simp] theorem Mathlib.free_add_magma.map_add {α : Type u} {β : Type v} (f : α → β) (x : free_add_magma α) (y : free_add_magma α) : free_add_magma.map f (x + y) = free_add_magma.map f x + free_add_magma.map f y :=
  rfl

protected instance Mathlib.free_add_magma.monad : Monad free_add_magma := sorry

/-- Recursor on `free_magma` using `pure` instead of `of`. -/
protected def Mathlib.free_add_magma.rec_on'' {α : Type u} {C : free_add_magma α → Sort l} (x : free_add_magma α) (ih1 : (x : α) → C (pure x)) (ih2 : (x y : free_add_magma α) → C x → C y → C (x + y)) : C x :=
  free_add_magma.rec_on' x ih1 ih2

@[simp] theorem Mathlib.free_add_magma.map_pure {α : Type u} {β : Type u} (f : α → β) (x : α) : f <$> pure x = pure (f x) :=
  rfl

@[simp] theorem Mathlib.free_add_magma.map_add' {α : Type u} {β : Type u} (f : α → β) (x : free_add_magma α) (y : free_add_magma α) : f <$> (x + y) = f <$> x + f <$> y :=
  rfl

@[simp] theorem Mathlib.free_add_magma.pure_bind {α : Type u} {β : Type u} (f : α → free_add_magma β) (x : α) : pure x >>= f = f x :=
  rfl

@[simp] theorem mul_bind {α : Type u} {β : Type u} (f : α → free_magma β) (x : free_magma α) (y : free_magma α) : x * y >>= f = (x >>= f) * (y >>= f) :=
  rfl

@[simp] theorem Mathlib.free_add_magma.pure_seq {α : Type u} {β : Type u} {f : α → β} {x : free_add_magma α} : pure f <*> x = f <$> x :=
  rfl

@[simp] theorem mul_seq {α : Type u} {β : Type u} {f : free_magma (α → β)} {g : free_magma (α → β)} {x : free_magma α} : f * g <*> x = (f <*> x) * (g <*> x) :=
  rfl

protected instance Mathlib.free_add_magma.is_lawful_monad : is_lawful_monad free_add_magma := sorry

end free_magma


/-- `free_magma` is traversable. -/
protected def free_magma.traverse {m : Type u → Type u} [Applicative m] {α : Type u} {β : Type u} (F : α → m β) : free_magma α → m (free_magma β) :=
  sorry

/-- `free_add_magma` is traversable. -/
protected def free_add_magma.traverse {m : Type u → Type u} [Applicative m] {α : Type u} {β : Type u} (F : α → m β) : free_add_magma α → m (free_add_magma β) :=
  sorry

namespace free_magma


protected instance Mathlib.free_add_magma.traversable : traversable free_add_magma :=
  traversable.mk free_add_magma.traverse

@[simp] theorem Mathlib.free_add_magma.traverse_pure {α : Type u} {β : Type u} {m : Type u → Type u} [Applicative m] (F : α → m β) (x : α) : traverse F (pure x) = pure <$> F x :=
  rfl

@[simp] theorem Mathlib.free_add_magma.traverse_pure' {α : Type u} {β : Type u} {m : Type u → Type u} [Applicative m] (F : α → m β) : traverse F ∘ pure = fun (x : α) => pure <$> F x :=
  rfl

@[simp] theorem Mathlib.free_add_magma.traverse_add {α : Type u} {β : Type u} {m : Type u → Type u} [Applicative m] (F : α → m β) (x : free_add_magma α) (y : free_add_magma α) : traverse F (x + y) = Add.add <$> traverse F x <*> traverse F y :=
  rfl

@[simp] theorem Mathlib.free_add_magma.traverse_add' {α : Type u} {β : Type u} {m : Type u → Type u} [Applicative m] (F : α → m β) : function.comp (traverse F) ∘ Add.add = fun (x y : free_add_magma α) => Add.add <$> traverse F x <*> traverse F y :=
  rfl

@[simp] theorem Mathlib.free_add_magma.traverse_eq {α : Type u} {β : Type u} {m : Type u → Type u} [Applicative m] (F : α → m β) (x : free_add_magma α) : free_add_magma.traverse F x = traverse F x :=
  rfl

@[simp] theorem mul_map_seq {α : Type u} (x : free_magma α) (y : free_magma α) : Mul.mul <$> x <*> y = x * y :=
  rfl

protected instance Mathlib.free_add_magma.is_lawful_traversable : is_lawful_traversable free_add_magma :=
  is_lawful_traversable.mk sorry sorry sorry sorry

end free_magma


/-- Representation of an element of a free magma. -/
protected def free_magma.repr {α : Type u} [has_repr α] : free_magma α → string :=
  sorry

/-- Representation of an element of a free additive magma. -/
protected def free_add_magma.repr {α : Type u} [has_repr α] : free_add_magma α → string :=
  sorry

protected instance free_add_magma.has_repr {α : Type u} [has_repr α] : has_repr (free_add_magma α) :=
  has_repr.mk free_add_magma.repr

/-- Length of an element of a free magma. -/
def free_magma.length {α : Type u} : free_magma α → ℕ :=
  sorry

/-- Length of an element of a free additive magma. -/
def free_add_magma.length {α : Type u} : free_add_magma α → ℕ :=
  sorry

/-- Associativity relations for a magma. -/
inductive magma.free_semigroup.r (α : Type u) [Mul α] : α → α → Prop
where
| intro : ∀ (x y z : α), magma.free_semigroup.r α (x * y * z) (x * (y * z))
| left : ∀ (w x y z : α), magma.free_semigroup.r α (w * (x * y * z)) (w * (x * (y * z)))

/-- Associativity relations for an additive magma. -/
inductive add_magma.free_add_semigroup.r (α : Type u) [Add α] : α → α → Prop
where
| intro : ∀ (x y z : α), add_magma.free_add_semigroup.r α (x + y + z) (x + (y + z))
| left : ∀ (w x y z : α), add_magma.free_add_semigroup.r α (w + (x + y + z)) (w + (x + (y + z)))

namespace magma


/-- Free semigroup over a magma. -/
def free_semigroup (α : Type u) [Mul α] :=
  Quot sorry

namespace free_semigroup


/-- Embedding from magma to its free semigroup. -/
def Mathlib.add_magma.free_add_semigroup.of {α : Type u} [Add α] : α → add_magma.free_add_semigroup α :=
  Quot.mk (add_magma.free_add_semigroup.r α)

protected instance Mathlib.add_magma.free_add_semigroup.inhabited {α : Type u} [Add α] [Inhabited α] : Inhabited (add_magma.free_add_semigroup α) :=
  { default := add_magma.free_add_semigroup.of Inhabited.default }

protected theorem Mathlib.add_magma.free_add_semigroup.induction_on {α : Type u} [Add α] {C : add_magma.free_add_semigroup α → Prop} (x : add_magma.free_add_semigroup α) (ih : ∀ (x : α), C (add_magma.free_add_semigroup.of x)) : C x :=
  quot.induction_on x ih

theorem of_mul_assoc {α : Type u} [Mul α] (x : α) (y : α) (z : α) : of (x * y * z) = of (x * (y * z)) :=
  quot.sound (r.intro x y z)

theorem of_mul_assoc_left {α : Type u} [Mul α] (w : α) (x : α) (y : α) (z : α) : of (w * (x * y * z)) = of (w * (x * (y * z))) :=
  quot.sound (r.left w x y z)

theorem of_mul_assoc_right {α : Type u} [Mul α] (w : α) (x : α) (y : α) (z : α) : of (w * x * y * z) = of (w * (x * y) * z) := sorry

protected instance semigroup {α : Type u} [Mul α] : semigroup (free_semigroup α) :=
  semigroup.mk
    (fun (x y : free_semigroup α) =>
      quot.lift_on x (fun (p : α) => quot.lift_on y (fun (q : α) => Quot.mk (r α) (p * q)) sorry) sorry)
    sorry

theorem Mathlib.add_magma.free_add_semigroup.of_add {α : Type u} [Add α] (x : α) (y : α) : add_magma.free_add_semigroup.of (x + y) = add_magma.free_add_semigroup.of x + add_magma.free_add_semigroup.of y :=
  rfl

/-- Lifts a magma homomorphism `α → β` to a semigroup homomorphism `magma.free_semigroup α → β`
given a semigroup `β`. -/
def lift {α : Type u} [Mul α] {β : Type v} [semigroup β] (f : α → β) (hf : ∀ (x y : α), f (x * y) = f x * f y) : free_semigroup α → β :=
  Quot.lift f sorry

@[simp] theorem lift_of {α : Type u} [Mul α] {β : Type v} [semigroup β] (f : α → β) {hf : ∀ (x y : α), f (x * y) = f x * f y} (x : α) : lift f hf (of x) = f x :=
  rfl

@[simp] theorem lift_mul {α : Type u} [Mul α] {β : Type v} [semigroup β] (f : α → β) {hf : ∀ (x y : α), f (x * y) = f x * f y} (x : free_semigroup α) (y : free_semigroup α) : lift f hf (x * y) = lift f hf x * lift f hf y :=
  quot.induction_on x fun (p : α) => quot.induction_on y fun (q : α) => hf p q

theorem Mathlib.add_magma.free_add_semigroup.lift_unique {α : Type u} [Add α] {β : Type v} [add_semigroup β] (f : add_magma.free_add_semigroup α → β) (hf : ∀ (x y : add_magma.free_add_semigroup α), f (x + y) = f x + f y) : f =
  add_magma.free_add_semigroup.lift (f ∘ add_magma.free_add_semigroup.of)
    fun (p q : α) => hf (add_magma.free_add_semigroup.of p) (add_magma.free_add_semigroup.of q) :=
  funext fun (x : add_magma.free_add_semigroup α) => quot.induction_on x fun (p : α) => rfl

/-- From a magma homomorphism `α → β` to a semigroup homomorphism
`magma.free_semigroup α → magma.free_semigroup β`. -/
def Mathlib.add_magma.free_add_semigroup.map {α : Type u} [Add α] {β : Type v} [Add β] (f : α → β) (hf : ∀ (x y : α), f (x + y) = f x + f y) : add_magma.free_add_semigroup α → add_magma.free_add_semigroup β :=
  add_magma.free_add_semigroup.lift (add_magma.free_add_semigroup.of ∘ f) sorry

@[simp] theorem Mathlib.add_magma.free_add_semigroup.map_of {α : Type u} [Add α] {β : Type v} [Add β] (f : α → β) {hf : ∀ (x y : α), f (x + y) = f x + f y} (x : α) : add_magma.free_add_semigroup.map f hf (add_magma.free_add_semigroup.of x) = add_magma.free_add_semigroup.of (f x) :=
  rfl

@[simp] theorem map_mul {α : Type u} [Mul α] {β : Type v} [Mul β] (f : α → β) {hf : ∀ (x y : α), f (x * y) = f x * f y} (x : free_semigroup α) (y : free_semigroup α) : map f hf (x * y) = map f hf x * map f hf y :=
  lift_mul (of ∘ f) x y

end free_semigroup


end magma


/-- Free semigroup over a given alphabet.
(Note: In this definition, the free semigroup does not contain the empty word.) -/
def free_semigroup (α : Type u) :=
  α × List α

namespace free_semigroup


protected instance semigroup {α : Type u} : semigroup (free_semigroup α) :=
  semigroup.mk (fun (L1 L2 : free_semigroup α) => (prod.fst L1, prod.snd L1 ++ prod.fst L2 :: prod.snd L2)) sorry

/-- The embedding `α → free_semigroup α`. -/
def Mathlib.free_add_semigroup.of {α : Type u} (x : α) : free_add_semigroup α :=
  (x, [])

protected instance Mathlib.free_add_semigroup.inhabited {α : Type u} [Inhabited α] : Inhabited (free_add_semigroup α) :=
  { default := free_add_semigroup.of Inhabited.default }

/-- Recursor for free semigroup using `of` and `*`. -/
protected def Mathlib.free_add_semigroup.rec_on {α : Type u} {C : free_add_semigroup α → Sort l} (x : free_add_semigroup α) (ih1 : (x : α) → C (free_add_semigroup.of x)) (ih2 : (x : α) → (y : free_add_semigroup α) → C (free_add_semigroup.of x) → C y → C (free_add_semigroup.of x + y)) : C x :=
  prod.rec_on x
    fun (f : α) (s : List α) =>
      list.rec_on s ih1
        (fun (hd : α) (tl : List α) (ih : (_a : α) → C (_a, tl)) (f : α) => ih2 f (hd, tl) (ih1 f) (ih hd)) f

end free_semigroup


/-- Auxiliary function for `free_semigroup.lift`. -/
def free_semigroup.lift' {α : Type u} {β : Type v} [semigroup β] (f : α → β) : α → List α → β :=
  sorry

/-- Auxiliary function for `free_semigroup.lift`. -/
def free_add_semigroup.lift' {α : Type u} {β : Type v} [add_semigroup β] (f : α → β) : α → List α → β :=
  sorry

namespace free_semigroup


/-- Lifts a function `α → β` to a semigroup homomorphism `free_semigroup α → β` given
a semigroup `β`. -/
def lift {α : Type u} {β : Type v} [semigroup β] (f : α → β) (x : free_semigroup α) : β :=
  lift' f (prod.fst x) (prod.snd x)

@[simp] theorem lift_of {α : Type u} {β : Type v} [semigroup β] (f : α → β) (x : α) : lift f (of x) = f x :=
  rfl

theorem lift_of_mul {α : Type u} {β : Type v} [semigroup β] (f : α → β) (x : α) (y : free_semigroup α) : lift f (of x * y) = f x * lift f y :=
  rfl

@[simp] theorem Mathlib.free_add_semigroup.lift_add {α : Type u} {β : Type v} [add_semigroup β] (f : α → β) (x : free_add_semigroup α) (y : free_add_semigroup α) : free_add_semigroup.lift f (x + y) = free_add_semigroup.lift f x + free_add_semigroup.lift f y := sorry

theorem Mathlib.free_add_semigroup.lift_unique {α : Type u} {β : Type v} [add_semigroup β] (f : free_add_semigroup α → β) (hf : ∀ (x y : free_add_semigroup α), f (x + y) = f x + f y) : f = free_add_semigroup.lift (f ∘ free_add_semigroup.of) := sorry

/-- The unique semigroup homomorphism that sends `of x` to `of (f x)`. -/
def Mathlib.free_add_semigroup.map {α : Type u} {β : Type v} (f : α → β) : free_add_semigroup α → free_add_semigroup β :=
  free_add_semigroup.lift (free_add_semigroup.of ∘ f)

@[simp] theorem Mathlib.free_add_semigroup.map_of {α : Type u} {β : Type v} (f : α → β) (x : α) : free_add_semigroup.map f (free_add_semigroup.of x) = free_add_semigroup.of (f x) :=
  rfl

@[simp] theorem Mathlib.free_add_semigroup.map_add {α : Type u} {β : Type v} (f : α → β) (x : free_add_semigroup α) (y : free_add_semigroup α) : free_add_semigroup.map f (x + y) = free_add_semigroup.map f x + free_add_semigroup.map f y :=
  free_add_semigroup.lift_add (free_add_semigroup.of ∘ f) x y

protected instance Mathlib.free_add_semigroup.monad : Monad free_add_semigroup := sorry

/-- Recursor that uses `pure` instead of `of`. -/
def rec_on' {α : Type u} {C : free_semigroup α → Sort l} (x : free_semigroup α) (ih1 : (x : α) → C (pure x)) (ih2 : (x : α) → (y : free_semigroup α) → C (pure x) → C y → C (pure x * y)) : C x :=
  free_semigroup.rec_on x ih1 ih2

@[simp] theorem map_pure {α : Type u} {β : Type u} (f : α → β) (x : α) : f <$> pure x = pure (f x) :=
  rfl

@[simp] theorem map_mul' {α : Type u} {β : Type u} (f : α → β) (x : free_semigroup α) (y : free_semigroup α) : f <$> (x * y) = f <$> x * f <$> y :=
  map_mul f x y

@[simp] theorem pure_bind {α : Type u} {β : Type u} (f : α → free_semigroup β) (x : α) : pure x >>= f = f x :=
  rfl

@[simp] theorem mul_bind {α : Type u} {β : Type u} (f : α → free_semigroup β) (x : free_semigroup α) (y : free_semigroup α) : x * y >>= f = (x >>= f) * (y >>= f) :=
  lift_mul f x y

@[simp] theorem Mathlib.free_add_semigroup.pure_seq {α : Type u} {β : Type u} {f : α → β} {x : free_add_semigroup α} : pure f <*> x = f <$> x :=
  rfl

@[simp] theorem mul_seq {α : Type u} {β : Type u} {f : free_semigroup (α → β)} {g : free_semigroup (α → β)} {x : free_semigroup α} : f * g <*> x = (f <*> x) * (g <*> x) :=
  mul_bind (fun (_x : α → β) => (fun (α β : Type u) (f : α → β) (x : free_semigroup α) => lift (of ∘ f) x) α β _x x) f g

protected instance Mathlib.free_add_semigroup.is_lawful_monad : is_lawful_monad free_add_semigroup := sorry

/-- `free_semigroup` is traversable. -/
protected def Mathlib.free_add_semigroup.traverse {m : Type u → Type u} [Applicative m] {α : Type u} {β : Type u} (F : α → m β) (x : free_add_semigroup α) : m (free_add_semigroup β) :=
  free_add_semigroup.rec_on' x (fun (x : α) => pure <$> F x)
    fun (x : α) (y : free_add_semigroup α) (ihx ihy : m (free_add_semigroup β)) => Add.add <$> ihx <*> ihy

protected instance Mathlib.free_add_semigroup.traversable : traversable free_add_semigroup :=
  traversable.mk free_add_semigroup.traverse

@[simp] theorem traverse_pure {α : Type u} {β : Type u} {m : Type u → Type u} [Applicative m] (F : α → m β) (x : α) : traverse F (pure x) = pure <$> F x :=
  rfl

@[simp] theorem Mathlib.free_add_semigroup.traverse_pure' {α : Type u} {β : Type u} {m : Type u → Type u} [Applicative m] (F : α → m β) : traverse F ∘ pure = fun (x : α) => pure <$> F x :=
  rfl

@[simp] theorem Mathlib.free_add_semigroup.traverse_add {α : Type u} {β : Type u} {m : Type u → Type u} [Applicative m] (F : α → m β) [is_lawful_applicative m] (x : free_add_semigroup α) (y : free_add_semigroup α) : traverse F (x + y) = Add.add <$> traverse F x <*> traverse F y := sorry

@[simp] theorem Mathlib.free_add_semigroup.traverse_add' {α : Type u} {β : Type u} {m : Type u → Type u} [Applicative m] (F : α → m β) [is_lawful_applicative m] : function.comp (traverse F) ∘ Add.add = fun (x y : free_add_semigroup α) => Add.add <$> traverse F x <*> traverse F y :=
  funext fun (x : free_add_semigroup α) => funext fun (y : free_add_semigroup α) => free_add_semigroup.traverse_add F x y

@[simp] theorem Mathlib.free_add_semigroup.traverse_eq {α : Type u} {β : Type u} {m : Type u → Type u} [Applicative m] (F : α → m β) (x : free_add_semigroup α) : free_add_semigroup.traverse F x = traverse F x :=
  rfl

@[simp] theorem Mathlib.free_add_semigroup.add_map_seq {α : Type u} (x : free_add_semigroup α) (y : free_add_semigroup α) : Add.add <$> x <*> y = x + y :=
  rfl

protected instance Mathlib.free_add_semigroup.is_lawful_traversable : is_lawful_traversable free_add_semigroup :=
  is_lawful_traversable.mk sorry sorry sorry sorry

protected instance Mathlib.free_add_semigroup.decidable_eq {α : Type u} [DecidableEq α] : DecidableEq (free_add_semigroup α) :=
  prod.decidable_eq

end free_semigroup


/-- Isomorphism between `magma.free_semigroup (free_magma α)` and `free_semigroup α`. -/
def free_add_semigroup_free_add_magma (α : Type u) : add_magma.free_add_semigroup (free_add_magma α) ≃ free_add_semigroup α :=
  equiv.mk (add_magma.free_add_semigroup.lift (free_add_magma.lift free_add_semigroup.of) sorry)
    (free_add_semigroup.lift (add_magma.free_add_semigroup.of ∘ free_add_magma.of)) sorry sorry

@[simp] theorem free_semigroup_free_magma_mul {α : Type u} (x : magma.free_semigroup (free_magma α)) (y : magma.free_semigroup (free_magma α)) : coe_fn (free_semigroup_free_magma α) (x * y) =
  coe_fn (free_semigroup_free_magma α) x * coe_fn (free_semigroup_free_magma α) y :=
  magma.free_semigroup.lift_mul (free_magma.lift free_semigroup.of) x y

