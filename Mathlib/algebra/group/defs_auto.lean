/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Simon Hudon, Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.group.to_additive
import Mathlib.tactic.basic
import Mathlib.PostPort

universes u l 

namespace Mathlib

/-!
# Typeclasses for (semi)groups and monoid

In this file we define typeclasses for algebraic structures with one binary operation.
The classes are named `(add_)?(comm_)?(semigroup|monoid|group)`, where `add_` means that
the class uses additive notation and `comm_` means that the class assumes that the binary
operation is commutative.

The file does not contain any lemmas except for

* axioms of typeclasses restated in the root namespace;
* lemmas required for instances.

For basic lemmas about these classes see `algebra.group.basic`.
-/

/- Additive "sister" structures.
   Example, add_semigroup mirrors semigroup.
   These structures exist just to help automation.
   In an alternative design, we could have the binary operation as an
   extra argument for semigroup, monoid, group, etc. However, the lemmas
   would be hard to index since they would not contain any constant.
   For example, mul_assoc would be

   lemma mul_assoc {α : Type u} {op : α → α → α} [semigroup α op] :
                   ∀ a b c : α, op (op a b) c = op a (op b c) :=
    semigroup.mul_assoc

   The simplifier cannot effectively use this lemma since the pattern for
   the left-hand-side would be

        ?op (?op ?a ?b) ?c

   Remark: we use a tactic for transporting theorems from the multiplicative fragment
   to the additive one.
-/

/-- `left_mul g` denotes left multiplication by `g` -/
def left_add {G : Type u} [Add G] : G → G → G := fun (g x : G) => g + x

/-- `right_mul g` denotes right multiplication by `g` -/
def right_mul {G : Type u} [Mul G] : G → G → G := fun (g x : G) => x * g

/-- A semigroup is a type with an associative `(*)`. -/
class semigroup (G : Type u) extends Mul G where
  mul_assoc : ∀ (a b c : G), a * b * c = a * (b * c)

/-- An additive semigroup is a type with an associative `(+)`. -/
class add_semigroup (G : Type u) extends Add G where
  add_assoc : ∀ (a b c : G), a + b + c = a + (b + c)

theorem mul_assoc {G : Type u} [semigroup G] (a : G) (b : G) (c : G) : a * b * c = a * (b * c) :=
  semigroup.mul_assoc

protected instance add_semigroup.to_is_associative {G : Type u} [add_semigroup G] :
    is_associative G Add.add :=
  is_associative.mk add_assoc

/-- A commutative semigroup is a type with an associative commutative `(*)`. -/
class comm_semigroup (G : Type u) extends semigroup G where
  mul_comm : ∀ (a b : G), a * b = b * a

/-- A commutative additive semigroup is a type with an associative commutative `(+)`. -/
class add_comm_semigroup (G : Type u) extends add_semigroup G where
  add_comm : ∀ (a b : G), a + b = b + a

theorem mul_comm {G : Type u} [comm_semigroup G] (a : G) (b : G) : a * b = b * a :=
  comm_semigroup.mul_comm

protected instance comm_semigroup.to_is_commutative {G : Type u} [comm_semigroup G] :
    is_commutative G Mul.mul :=
  is_commutative.mk mul_comm

/-- A `left_cancel_semigroup` is a semigroup such that `a * b = a * c` implies `b = c`. -/
class left_cancel_semigroup (G : Type u) extends semigroup G where
  mul_left_cancel : ∀ (a b c : G), a * b = a * c → b = c

/-- An `add_left_cancel_semigroup` is an additive semigroup such that
`a + b = a + c` implies `b = c`. -/
class add_left_cancel_semigroup (G : Type u) extends add_semigroup G where
  add_left_cancel : ∀ (a b c : G), a + b = a + c → b = c

theorem mul_left_cancel {G : Type u} [left_cancel_semigroup G] {a : G} {b : G} {c : G} :
    a * b = a * c → b = c :=
  left_cancel_semigroup.mul_left_cancel a b c

theorem mul_left_cancel_iff {G : Type u} [left_cancel_semigroup G] {a : G} {b : G} {c : G} :
    a * b = a * c ↔ b = c :=
  { mp := mul_left_cancel, mpr := congr_arg fun {b : G} => a * b }

theorem mul_right_injective {G : Type u} [left_cancel_semigroup G] (a : G) :
    function.injective (Mul.mul a) :=
  fun (b c : G) => mul_left_cancel

@[simp] theorem add_right_inj {G : Type u} [add_left_cancel_semigroup G] (a : G) {b : G} {c : G} :
    a + b = a + c ↔ b = c :=
  function.injective.eq_iff (add_right_injective a)

/-- A `right_cancel_semigroup` is a semigroup such that `a * b = c * b` implies `a = c`. -/
class right_cancel_semigroup (G : Type u) extends semigroup G where
  mul_right_cancel : ∀ (a b c : G), a * b = c * b → a = c

/-- An `add_right_cancel_semigroup` is an additive semigroup such that
`a + b = c + b` implies `a = c`. -/
class add_right_cancel_semigroup (G : Type u) extends add_semigroup G where
  add_right_cancel : ∀ (a b c : G), a + b = c + b → a = c

theorem mul_right_cancel {G : Type u} [right_cancel_semigroup G] {a : G} {b : G} {c : G} :
    a * b = c * b → a = c :=
  right_cancel_semigroup.mul_right_cancel a b c

theorem add_right_cancel_iff {G : Type u} [add_right_cancel_semigroup G] {a : G} {b : G} {c : G} :
    b + a = c + a ↔ b = c :=
  { mp := add_right_cancel, mpr := congr_arg fun {b : G} => b + a }

theorem add_left_injective {G : Type u} [add_right_cancel_semigroup G] (a : G) :
    function.injective fun (x : G) => x + a :=
  fun (b c : G) => add_right_cancel

@[simp] theorem add_left_inj {G : Type u} [add_right_cancel_semigroup G] (a : G) {b : G} {c : G} :
    b + a = c + a ↔ b = c :=
  function.injective.eq_iff (add_left_injective a)

/-- A `monoid` is a `semigroup` with an element `1` such that `1 * a = a * 1 = a`. -/
class monoid (M : Type u) extends semigroup M, HasOne M where
  one_mul : ∀ (a : M), 1 * a = a
  mul_one : ∀ (a : M), a * 1 = a

/-- An `add_monoid` is an `add_semigroup` with an element `0` such that `0 + a = a + 0 = a`. -/
class add_monoid (M : Type u) extends HasZero M, add_semigroup M where
  zero_add : ∀ (a : M), 0 + a = a
  add_zero : ∀ (a : M), a + 0 = a

@[simp] theorem one_mul {M : Type u} [monoid M] (a : M) : 1 * a = a := monoid.one_mul

@[simp] theorem add_zero {M : Type u} [add_monoid M] (a : M) : a + 0 = a := add_monoid.add_zero

protected instance monoid_to_is_left_id {M : Type u} [monoid M] : is_left_id M Mul.mul 1 :=
  is_left_id.mk monoid.one_mul

protected instance add_monoid_to_is_right_id {M : Type u} [add_monoid M] :
    is_right_id M Add.add 0 :=
  is_right_id.mk add_monoid.add_zero

theorem left_neg_eq_right_neg {M : Type u} [add_monoid M] {a : M} {b : M} {c : M} (hba : b + a = 0)
    (hac : a + c = 0) : b = c :=
  sorry

/-- A commutative monoid is a monoid with commutative `(*)`. -/
class comm_monoid (M : Type u) extends comm_semigroup M, monoid M where

/-- An additive commutative monoid is an additive monoid with commutative `(+)`. -/
class add_comm_monoid (M : Type u) extends add_comm_semigroup M, add_monoid M where

/-- An additive monoid in which addition is left-cancellative.
Main examples are `ℕ` and groups. This is the right typeclass for many sum lemmas, as having a zero
is useful to define the sum over the empty set, so `add_left_cancel_semigroup` is not enough. -/
-- TODO: I found 1 (one) lemma assuming `[add_left_cancel_monoid]`.

class add_left_cancel_monoid (M : Type u) extends add_left_cancel_semigroup M, add_monoid M where

-- Should we port more lemmas to this typeclass?

/-- A monoid in which multiplication is left-cancellative. -/
class left_cancel_monoid (M : Type u) extends left_cancel_semigroup M, monoid M where

/-- Commutative version of add_left_cancel_monoid. -/
class add_left_cancel_comm_monoid (M : Type u) extends add_left_cancel_monoid M, add_comm_monoid M
    where

/-- Commutative version of left_cancel_monoid. -/
class left_cancel_comm_monoid (M : Type u) extends left_cancel_monoid M, comm_monoid M where

/-- An additive monoid in which addition is right-cancellative.
Main examples are `ℕ` and groups. This is the right typeclass for many sum lemmas, as having a zero
is useful to define the sum over the empty set, so `add_right_cancel_semigroup` is not enough. -/
class add_right_cancel_monoid (M : Type u) extends add_monoid M, add_right_cancel_semigroup M where

/-- A monoid in which multiplication is right-cancellative. -/
class right_cancel_monoid (M : Type u) extends right_cancel_semigroup M, monoid M where

/-- Commutative version of add_right_cancel_monoid. -/
class add_right_cancel_comm_monoid (M : Type u) extends add_right_cancel_monoid M, add_comm_monoid M
    where

/-- Commutative version of right_cancel_monoid. -/
class right_cancel_comm_monoid (M : Type u) extends right_cancel_monoid M, comm_monoid M where

/-- An additive monoid in which addition is cancellative on both sides.
Main examples are `ℕ` and groups. This is the right typeclass for many sum lemmas, as having a zero
is useful to define the sum over the empty set, so `add_right_cancel_semigroup` is not enough. -/
class add_cancel_monoid (M : Type u) extends add_left_cancel_monoid M, add_right_cancel_monoid M
    where

/-- A monoid in which multiplication is cancellative. -/
class cancel_monoid (M : Type u) extends left_cancel_monoid M, right_cancel_monoid M where

/-- Commutative version of add_cancel_monoid. -/
class add_cancel_comm_monoid (M : Type u)
    extends add_left_cancel_comm_monoid M, add_right_cancel_comm_monoid M where

/-- Commutative version of cancel_monoid. -/
class cancel_comm_monoid (M : Type u) extends right_cancel_comm_monoid M, left_cancel_comm_monoid M
    where

/-- `try_refl_tac` solves goals of the form `∀ a b, f a b = g a b`,
if they hold by definition. -/
/-- A `div_inv_monoid` is a `monoid` with operations `/` and `⁻¹` satisfying
`div_eq_mul_inv : ∀ a b, a / b = a * b⁻¹`.

This is the immediate common ancestor of `group` and `group_with_zero`,
in order to deduplicate the name `div_eq_mul_inv`.
The default for `div` is such that `a / b = a * b⁻¹` holds by definition.

Adding `div` as a field rather than defining `a / b := a * b⁻¹` allows us to
avoid certain classes of unification failures, for example:
Let `foo X` be a type with a `∀ X, has_div (foo X)` instance but no
`∀ X, has_inv (foo X)`, e.g. when `foo X` is a `euclidean_domain`. Suppose we
also have an instance `∀ X [cromulent X], group_with_zero (foo X)`. Then the
`(/)` coming from `group_with_zero_has_div` cannot be definitionally equal to
the `(/)` coming from `foo.has_div`.
-/
class div_inv_monoid (G : Type u) extends Div G, monoid G, has_inv G where
  div_eq_mul_inv :
    autoParam (∀ (a b : G), a / b = a * (b⁻¹))
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.try_refl_tac")
        (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "try_refl_tac") [])

/-- A `sub_neg_monoid` is an `add_monoid` with unary `-` and binary `-` operations
satisfying `sub_eq_add_neg : ∀ a b, a - b = a + -b`.

The default for `sub` is such that `a - b = a + -b` holds by definition.

Adding `sub` as a field rather than defining `a - b := a + -b` allows us to
avoid certain classes of unification failures, for example:
Let `foo X` be a type with a `∀ X, has_sub (foo X)` instance but no
`∀ X, has_neg (foo X)`. Suppose we also have an instance
`∀ X [cromulent X], add_group (foo X)`. Then the `(-)` coming from
`add_group.has_sub` cannot be definitionally equal to the `(-)` coming from
`foo.has_sub`.
-/
class sub_neg_monoid (G : Type u) extends Sub G, Neg G, add_monoid G where
  sub_eq_add_neg :
    autoParam (∀ (a b : G), a - b = a + -b)
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.try_refl_tac")
        (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "try_refl_tac") [])

theorem sub_eq_add_neg {G : Type u} [sub_neg_monoid G] (a : G) (b : G) : a - b = a + -b :=
  sub_neg_monoid.sub_eq_add_neg

/-- A `group` is a `monoid` with an operation `⁻¹` satisfying `a⁻¹ * a = 1`.

There is also a division operation `/` such that `a / b = a * b⁻¹`,
with a default so that `a / b = a * b⁻¹` holds by definition.
-/
class group (G : Type u) extends div_inv_monoid G where
  mul_left_inv : ∀ (a : G), a⁻¹ * a = 1

/-- An `add_group` is an `add_monoid` with a unary `-` satisfying `-a + a = 0`.

There is also a binary operation `-` such that `a - b = a + -b`,
with a default so that `a - b = a + -b` holds by definition.
-/
class add_group (A : Type u) extends sub_neg_monoid A where
  add_left_neg : ∀ (a : A), -a + a = 0

/-- Abbreviation for `@div_inv_monoid.to_monoid _ (@group.to_div_inv_monoid _ _)`.

Useful because it corresponds to the fact that `Grp` is a subcategory of `Mon`.
Not an instance since it duplicates `@div_inv_monoid.to_monoid _ (@group.to_div_inv_monoid _ _)`.
-/
def group.to_monoid (G : Type u) [group G] : monoid G := div_inv_monoid.to_monoid G

@[simp] theorem mul_left_inv {G : Type u} [group G] (a : G) : a⁻¹ * a = 1 := group.mul_left_inv

theorem inv_mul_self {G : Type u} [group G] (a : G) : a⁻¹ * a = 1 := mul_left_inv a

@[simp] theorem neg_add_cancel_left {G : Type u} [add_group G] (a : G) (b : G) : -a + (a + b) = b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (-a + (a + b) = b)) (Eq.symm (add_assoc (-a) a b))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (-a + a + b = b)) (add_left_neg a)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (0 + b = b)) (zero_add b))) (Eq.refl b)))

@[simp] theorem inv_eq_of_mul_eq_one {G : Type u} [group G] {a : G} {b : G} (h : a * b = 1) :
    a⁻¹ = b :=
  left_inv_eq_right_inv (inv_mul_self a) h

@[simp] theorem inv_inv {G : Type u} [group G] (a : G) : a⁻¹⁻¹ = a :=
  inv_eq_of_mul_eq_one (mul_left_inv a)

@[simp] theorem add_right_neg {G : Type u} [add_group G] (a : G) : a + -a = 0 :=
  (fun (this : --a + -a = 0) => eq.mp (Eq._oldrec (Eq.refl ( --a + -a = 0)) (neg_neg a)) this)
    (add_left_neg (-a))

theorem add_neg_self {G : Type u} [add_group G] (a : G) : a + -a = 0 := add_right_neg a

@[simp] theorem mul_inv_cancel_right {G : Type u} [group G] (a : G) (b : G) : a * b * (b⁻¹) = a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a * b * (b⁻¹) = a)) (mul_assoc a b (b⁻¹))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * (b * (b⁻¹)) = a)) (mul_right_inv b)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a * 1 = a)) (mul_one a))) (Eq.refl a)))

protected instance add_group.to_cancel_add_monoid {G : Type u} [add_group G] :
    add_cancel_monoid G :=
  add_cancel_monoid.mk add_group.add add_group.add_assoc sorry add_group.zero add_group.zero_add
    add_group.add_zero sorry

/-- A commutative group is a group with commutative `(*)`. -/
/-- An additive commutative group is an additive group with commutative `(+)`. -/
class comm_group (G : Type u) extends group G, comm_monoid G where

class add_comm_group (G : Type u) extends add_group G, add_comm_monoid G where

protected instance comm_group.to_cancel_comm_monoid {G : Type u} [comm_group G] :
    cancel_comm_monoid G :=
  cancel_comm_monoid.mk comm_group.mul comm_group.mul_assoc sorry comm_group.one comm_group.one_mul
    comm_group.mul_one comm_group.mul_comm sorry

end Mathlib