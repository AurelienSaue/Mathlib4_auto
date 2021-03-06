/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

notation, basic datatypes and type classes
-/
import Mathlib.PrePort

universes u l v w u_1 u_2 u₁ u₂ u₃ 

namespace Mathlib

/- Reserving notation. We do this so that the precedence of all of the operators
can be seen in one place and to prevent core notation being accidentally overloaded later.  -/

/- Notation for logical operations and relations -/

/- types and type constructors -/

/- arithmetic operations -/

/- boolean operations -/

/- set operations -/

/- other symbols -/

/--
The kernel definitional equality test (t =?= s) has special support for id_delta applications.
It implements the following rules

   1)   (id_delta t) =?= t
   2)   t =?= (id_delta t)
   3)   (id_delta t) =?= s  IF (unfold_of t) =?= s
   4)   t =?= id_delta s    IF t =?= (unfold_of s)

This is mechanism for controlling the delta reduction (aka unfolding) used in the kernel.

We use id_delta applications to address performance problems when type checking
lemmas generated by the equation compiler.
-/
def id_delta {α : Sort u} (a : α) : α :=
  a

/-- Gadget for optional parameter support. -/
def opt_param (α : Sort u) (default : α) :=
  α

/-- Gadget for marking output parameters in type classes. -/
def out_param (α : Sort u) :=
  α

/-
  id_rhs is an auxiliary declaration used in the equation compiler to address performance
  issues when proving equational lemmas. The equation compiler uses it as a marker.
-/

def id_rhs (α : Sort u) (a : α) : α :=
  a

/-- An abbreviation for `punit.{0}`, its most common instantiation.
    This type should be preferred over `punit` where possible to avoid
    unnecessary universe parameters. -/
def unit :=
  PUnit

def unit.star : Unit :=
  PUnit.unit

/--
Gadget for defining thunks, thunk parameters have special treatment.
Example: given
      def f (s : string) (t : thunk nat) : nat
an application
     f "hello" 10
 is converted into
     f "hello" (λ _, 10)
-/
def thunk (α : Type u) :=
  Unit → α

inductive empty 
where

/--
Logical not.

`not P`, with notation `¬ P`, is the `Prop` which is true if and only if `P` is false. It is
internally represented as `P → false`, so one way to prove a goal `⊢ ¬ P` is to use `intro h`,
which gives you a new hypothesis `h : P` and the goal `⊢ false`.

A hypothesis `h : ¬ P` can be used in term mode as a function, so if `w : P` then `h w : false`.

Related mathlib tactic: `contrapose`.
-/
def not (a : Prop) :=
  a → False

prefix:40 "¬" => Mathlib.not

/-
Initialize the quotient module, which effectively adds the following definitions:

constant quot {α : Sort u} (r : α → α → Prop) : Sort u

constant quot.mk {α : Sort u} (r : α → α → Prop) (a : α) : quot r

constant quot.lift {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β) :
  (∀ a b : α, r a b → eq (f a) (f b)) → quot r → β

constant quot.ind {α : Sort u} {r : α → α → Prop} {β : quot r → Prop} :
  (∀ a : α, β (quot.mk r a)) → ∀ q : quot r, β q

Also the reduction rule:

quot.lift f _ (quot.mk a) ~~> f a

-/

/--
Heterogeneous equality.

Its purpose is to write down equalities between terms whose types are not definitionally equal.
For example, given `x : vector α n` and `y : vector α (0+n)`, `x = y` doesn't typecheck but `x == y` does.

If you have a goal `⊢ x == y`, 
your first instinct should be to ask (either yourself, or on [zulip](https://leanprover.zulipchat.com/))
if something has gone wrong already.
If you really do need to follow this route, 
you may find the lemmas `eq_rec_heq` and `eq_mpr_heq` useful.
-/
/-- Similar to `prod`, but α and β can be propositions.
   We use this type internally to automatically generate the brec_on recursor. -/
/--
Logical and.

`and P Q`, with notation `P ∧ Q`, is the `Prop` which is true precisely when `P` and `Q` are
both true. 

To prove a goal `⊢ P ∧ Q`, you can use the tactic `split`,
which gives two separate goals `⊢ P` and `⊢ Q`.

Given a hypothesis `h : P ∧ Q`, you can use the tactic `cases h with hP hQ`
to obtain two new hypotheses `hP : P` and `hQ : Q`. See also the `obtain` or `rcases` tactics in
mathlib.
-/
def and.elim_left {a : Prop} {b : Prop} (h : a ∧ b) : a :=
  and.left h

def and.elim_right {a : Prop} {b : Prop} (h : a ∧ b) : b :=
  and.right h

infixl:50 " = " => Mathlib.eq

/- eq basic support -/

def rfl {α : Sort u} {a : α} : a = a :=
  Eq.refl a

theorem eq.subst {α : Sort u} {P : α → Prop} {a : α} {b : α} (h₁ : a = b) (h₂ : P a) : P b :=
  Eq._oldrec h₂ h₁

infixr:75 " ▸ " => Mathlib.eq.subst

theorem eq.trans {α : Sort u} {a : α} {b : α} {c : α} (h₁ : a = b) (h₂ : b = c) : a = c :=
  h₂ ▸ h₁

theorem eq.symm {α : Sort u} {a : α} {b : α} (h : a = b) : b = a :=
  h ▸ rfl

infixl:50 " == " => Mathlib.heq

def heq.rfl {α : Sort u} {a : α} : a == a :=
  HEq.refl a

theorem eq_of_heq {α : Sort u} {a : α} {a' : α} (h : a == a') : a = a' :=
  (fun (this : ∀ (α' : Sort u) (a' : α'), a == a' → ∀ (h₂ : α = α'), eq.rec_on h₂ a = a') =>
      (fun (this : eq.rec_on (Eq.refl α) a = a') => this) (this α a' h (Eq.refl α)))
    fun (α' : Sort u) (a' : α') (h₁ : a == a') => heq.rec_on h₁ fun (h₂ : α = α) => rfl

/- The following four lemmas could not be automatically generated when the
   structures were declared, so we prove them manually here. -/

theorem prod.mk.inj {α : Type u} {β : Type v} {x₁ : α} {y₁ : β} {x₂ : α} {y₂ : β} : (x₁, y₁) = (x₂, y₂) → x₁ = x₂ ∧ y₁ = y₂ :=
  fun (h : (x₁, y₁) = (x₂, y₂)) => prod.no_confusion h fun (h₁ : x₁ = x₂) (h₂ : y₁ = y₂) => { left := h₁, right := h₂ }

theorem prod.mk.inj_arrow {α : Type u} {β : Type v} {x₁ : α} {y₁ : β} {x₂ : α} {y₂ : β} : (x₁, y₁) = (x₂, y₂) → {P : Sort w} → (x₁ = x₂ → y₁ = y₂ → P) → P :=
  fun (h₁ : (x₁, y₁) = (x₂, y₂)) (_x : Sort w) (h₂ : x₁ = x₂ → y₁ = y₂ → _x) => prod.no_confusion h₁ h₂

theorem pprod.mk.inj {α : Sort u} {β : Sort v} {x₁ : α} {y₁ : β} {x₂ : α} {y₂ : β} : { fst := x₁, snd := y₁ } = { fst := x₂, snd := y₂ } → x₁ = x₂ ∧ y₁ = y₂ :=
  fun (h : { fst := x₁, snd := y₁ } = { fst := x₂, snd := y₂ }) =>
    pprod.no_confusion h fun (h₁ : x₁ = x₂) (h₂ : y₁ = y₂) => { left := h₁, right := h₂ }

theorem pprod.mk.inj_arrow {α : Type u} {β : Type v} {x₁ : α} {y₁ : β} {x₂ : α} {y₂ : β} : (x₁, y₁) = (x₂, y₂) → {P : Sort w} → (x₁ = x₂ → y₁ = y₂ → P) → P :=
  fun (h₁ : (x₁, y₁) = (x₂, y₂)) (_x : Sort w) (h₂ : x₁ = x₂ → y₁ = y₂ → _x) => prod.no_confusion h₁ h₂

inductive sum (α : Type u) (β : Type v) 
where
| inl : α → sum α β
| inr : β → sum α β

inductive psum (α : Sort u) (β : Sort v) 
where
| inl : α → psum α β
| inr : β → psum α β

/--
Logical or.

`or P Q`, with notation `P ∨ Q`, is the proposition which is true if and only if `P` or `Q` is
true.

To prove a goal `⊢ P ∨ Q`, if you know which alternative you want to prove,
you can use the tactics `left` (which gives the goal `⊢ P`)
or `right` (which gives the goal `⊢ Q`).

Given a hypothesis `h : P ∨ Q` and goal `⊢ R`,
the tactic `cases h` will give you two copies of the goal `⊢ R`,
with the hypothesis `h : P` in the first, and the hypothesis `h : Q` in the second.
-/
def or.intro_left {a : Prop} (b : Prop) (ha : a) : a ∨ b :=
  Or.inl ha

def or.intro_right (a : Prop) {b : Prop} (hb : b) : a ∨ b :=
  Or.inr hb

structure sigma {α : Type u} (β : α → Type v) 
where
  fst : α
  snd : β fst

structure psigma {α : Sort u} (β : α → Sort v) 
where
  fst : α
  snd : β fst

/- Remark: subtype must take a Sort instead of Type because of the axiom strong_indefinite_description. -/

def decidable_pred {α : Sort u} (r : α → Prop) :=
  (a : α) → Decidable (r a)

def decidable_rel {α : Sort u} (r : α → α → Prop) :=
  (a b : α) → Decidable (r a b)

def decidable_eq (α : Sort u) :=
  DecidableRel Eq

infixr:67 " :: " => Mathlib.list.cons

structure unification_constraint 
where
  α : Type u
  lhs : α
  rhs : α

infixl:50 " ≟ " => Mathlib.unification_constraint.mk

infixl:50 " =?= " => Mathlib.unification_constraint.mk

structure unification_hint 
where
  pattern : unification_constraint
  constraints : List unification_constraint

/- Declare builtin and reserved notation -/

class has_inv (α : Type u) 
where
  inv : α → α

class has_dvd (α : Type u) 
where
  dvd : α → α → Prop

class has_andthen (α : Type u) (β : Type v) (σ : outParam (Type w)) 
where
  andthen : α → β → σ

class has_union (α : Type u) 
where
  union : α → α → α

class has_inter (α : Type u) 
where
  inter : α → α → α

class has_sdiff (α : Type u) 
where
  sdiff : α → α → α

class has_equiv (α : Sort u) 
where
  equiv : α → α → Prop

class has_subset (α : Type u) 
where
  subset : α → α → Prop

/- Type classes has_emptyc and has_insert are
class has_ssubset (α : Type u) 
where
  ssubset : α → α → Prop

   used to implement polymorphic notation for collections.
   Example: {a, b, c}. -/

class has_emptyc (α : Type u) 
where
  emptyc : α

class has_insert (α : outParam (Type u)) (γ : Type v) 
where
  insert : α → γ → γ

/- Type class used to implement the notation { a ∈ c | p a } -/

class has_singleton (α : outParam (Type u)) (β : Type v) 
where
  singleton : α → β

class has_sep (α : outParam (Type u)) (γ : Type v) 
where
  sep : (α → Prop) → γ → γ

/- Type class for set-like membership -/

class has_mem (α : outParam (Type u)) (γ : Type v) 
where
  mem : α → γ → Prop

class has_pow (α : Type u) (β : Type v) 
where
  pow : α → β → α

infixl:50 " ∈ " => Mathlib.has_mem.mem

infixl:65 " + " => Mathlib.has_add.add

infixl:70 " * " => Mathlib.has_mul.mul

infixl:65 " - " => Mathlib.has_sub.sub

infixl:70 " / " => Mathlib.has_div.div

infixl:50 " ∣ " => Mathlib.has_dvd.dvd

infixl:70 " % " => Mathlib.has_mod.mod

prefix:75 "-" => Mathlib.has_neg.neg

infixl:50 " <= " => Mathlib.has_le.le

infixl:50 " ≤ " => Mathlib.has_le.le

infixl:50 " < " => Mathlib.has_lt.lt

infixl:65 " ++ " => Mathlib.has_append.append

infixl:1 "; " => Mathlib.has_andthen.andthen

notation:1024 "∅" => Mathlib.has_emptyc.emptyc

infixl:65 " ∪ " => Mathlib.has_union.union

infixl:70 " ∩ " => Mathlib.has_inter.inter

infixl:50 " ⊆ " => Mathlib.has_subset.subset

infixl:50 " ⊂ " => Mathlib.has_ssubset.ssubset

infixl:70 " \ " => Mathlib.has_sdiff.sdiff

infixl:50 " ≈ " => Mathlib.has_equiv.equiv

infixr:80 " ^ " => Mathlib.has_pow.pow

def ge {α : Type u} [HasLessEq α] (a : α) (b : α) :=
  b ≤ a

def gt {α : Type u} [HasLess α] (a : α) (b : α) :=
  b < a

infixl:50 " >= " => Mathlib.ge

infixl:50 " ≥ " => Mathlib.ge

infixl:50 " > " => Mathlib.gt

def superset {α : Type u} [has_subset α] (a : α) (b : α) :=
  b ⊆ a

def ssuperset {α : Type u} [has_ssubset α] (a : α) (b : α) :=
  b ⊂ a

infixl:50 " ⊇ " => Mathlib.superset

infixl:50 " ⊃ " => Mathlib.ssuperset

def bit0 {α : Type u} [s : Add α] (a : α) : α :=
  a + a

def bit1 {α : Type u} [s₁ : HasOne α] [s₂ : Add α] (a : α) : α :=
  bit0 a + 1

class is_lawful_singleton (α : Type u) (β : Type v) [has_emptyc β] [has_insert α β] [has_singleton α β] 
where
  insert_emptyc_eq : ∀ (x : α), insert x ∅ = has_singleton.singleton x

/- nat basic instances -/

namespace nat


protected def add : Nat → Nat → Nat :=
  Nat.add

end nat


protected instance nat.has_zero : HasZero Nat :=
  { zero := 0 }

protected instance nat.has_one : HasOne Nat :=
  { one := 1 }

protected instance nat.has_add : Add Nat :=
  { add := Nat.add }

def std.priority.default : Nat :=
  bit0 (bit0 (bit0 (bit1 (bit0 (bit1 (bit1 (bit1 (bit1 1))))))))

def std.priority.max : Nat :=
  bit1
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
                                    (bit1
                                      (bit1
                                        (bit1
                                          (bit1
                                            (bit1
                                              (bit1
                                                (bit1
                                                  (bit1
                                                    (bit1 (bit1 (bit1 (bit1 (bit1 (bit1 1))))))))))))))))))))))))))))))

namespace nat


end nat


protected def nat.prio : Nat :=
  std.priority.default + bit0 (bit0 (bit1 (bit0 (bit0 (bit1 1)))))

/-
  Global declarations of right binding strength

  If a module reassigns these, it will be incompatible with other modules that adhere to these
  conventions.

  When hovering over a symbol, use "C-c C-k" to see how to input it.
-/

def std.prec.max : Nat :=
  bit0 (bit0 (bit0 (bit0 (bit0 (bit0 (bit0 (bit0 (bit0 (bit0 1)))))))))

def std.prec.arrow : Nat :=
  bit1 (bit0 (bit0 (bit1 1)))

/-
The next def is "max + 10". It can be used e.g. for postfix operations that should
be stronger than application.
-/

def std.prec.max_plus : Nat :=
  std.prec.max + bit0 (bit1 (bit0 1))

postfix:0 "⁻¹" => Mathlib.has_inv.inv

infixr:35 " × " => Mathlib.prod

-- notation for n-ary tuples

/- sizeof -/

def sizeof {α : Sort u} [s : SizeOf α] : α → Nat :=
  has_sizeof.sizeof

/-
Declare sizeof instances and lemmas for types declared before has_sizeof.
From now on, the inductive compiler will automatically generate sizeof instances and lemmas.
-/

/- Every type `α` has a default has_sizeof instance that just returns 0 for every element of `α` -/

protected def default.sizeof (α : Sort u) : α → Nat :=
  sorry

protected instance default_has_sizeof (α : Sort u) : SizeOf α :=
  { sizeOf := default.sizeof α }

protected def nat.sizeof : Nat → Nat :=
  sorry

protected instance nat.has_sizeof : SizeOf Nat :=
  { sizeOf := nat.sizeof }

protected def prod.sizeof {α : Type u} {β : Type v} [SizeOf α] [SizeOf β] : α × β → Nat :=
  sorry

protected instance prod.has_sizeof (α : Type u) (β : Type v) [SizeOf α] [SizeOf β] : SizeOf (α × β) :=
  { sizeOf := prod.sizeof }

protected def sum.sizeof {α : Type u} {β : Type v} [SizeOf α] [SizeOf β] : sum α β → Nat :=
  sorry

protected instance sum.has_sizeof (α : Type u) (β : Type v) [SizeOf α] [SizeOf β] : SizeOf (sum α β) :=
  { sizeOf := sum.sizeof }

protected def psum.sizeof {α : Type u} {β : Type v} [SizeOf α] [SizeOf β] : psum α β → Nat :=
  sorry

protected instance psum.has_sizeof (α : Type u) (β : Type v) [SizeOf α] [SizeOf β] : SizeOf (psum α β) :=
  { sizeOf := psum.sizeof }

protected def sigma.sizeof {α : Type u} {β : α → Type v} [SizeOf α] [(a : α) → SizeOf (β a)] : sigma β → Nat :=
  sorry

protected instance sigma.has_sizeof (α : Type u) (β : α → Type v) [SizeOf α] [(a : α) → SizeOf (β a)] : SizeOf (sigma β) :=
  { sizeOf := sigma.sizeof }

protected def psigma.sizeof {α : Type u} {β : α → Type v} [SizeOf α] [(a : α) → SizeOf (β a)] : psigma β → Nat :=
  sorry

protected instance psigma.has_sizeof (α : Type u) (β : α → Type v) [SizeOf α] [(a : α) → SizeOf (β a)] : SizeOf (psigma β) :=
  { sizeOf := psigma.sizeof }

protected def punit.sizeof : PUnit → Nat :=
  sorry

protected instance punit.has_sizeof : SizeOf PUnit :=
  { sizeOf := punit.sizeof }

protected def bool.sizeof : Bool → Nat :=
  sorry

protected instance bool.has_sizeof : SizeOf Bool :=
  { sizeOf := bool.sizeof }

protected def option.sizeof {α : Type u} [SizeOf α] : Option α → Nat :=
  sorry

protected instance option.has_sizeof (α : Type u) [SizeOf α] : SizeOf (Option α) :=
  { sizeOf := option.sizeof }

protected def list.sizeof {α : Type u} [SizeOf α] : List α → Nat :=
  sorry

protected instance list.has_sizeof (α : Type u) [SizeOf α] : SizeOf (List α) :=
  { sizeOf := list.sizeof }

protected def subtype.sizeof {α : Type u} [SizeOf α] {p : α → Prop} : Subtype p → Nat :=
  sorry

protected instance subtype.has_sizeof {α : Type u} [SizeOf α] (p : α → Prop) : SizeOf (Subtype p) :=
  { sizeOf := subtype.sizeof }

theorem nat_add_zero (n : Nat) : n + 0 = n :=
  rfl

/- Combinator calculus -/

namespace combinator


def I {α : Type u₁} (a : α) : α :=
  a

def K {α : Type u₁} {β : Type u₂} (a : α) (b : β) : α :=
  a

end combinator


def combinator.S {α : Type u₁} {β : Type u₂} {γ : Type u₃} (x : α → β → γ) (y : α → β) (z : α) : γ :=
  x z (y z)

/-- Auxiliary datatype for #[ ... ] notation.
    #[1, 2, 3, 4] is notation for

    bin_tree.node
      (bin_tree.node (bin_tree.leaf 1) (bin_tree.leaf 2))
      (bin_tree.node (bin_tree.leaf 3) (bin_tree.leaf 4))

    We use this notation to input long sequences without exhausting the system stack space.
    Later, we define a coercion from `bin_tree` into `list`.
-/
inductive bin_tree (α : Type u) 
where
| empty : bin_tree α
| leaf : α → bin_tree α
| node : bin_tree α → bin_tree α → bin_tree α

/- Basic unification hints -/

def add_succ_defeq_succ_add_hint (x : Nat) (y : Nat) (z : Nat) : unification_hint :=
  unification_hint.mk (x + Nat.succ y =?= Nat.succ z) [z =?= x + y]

/-- Like `by apply_instance`, but not dependent on the tactic framework. -/
def infer_instance {α : Sort u} [i : α] : α :=
  i

