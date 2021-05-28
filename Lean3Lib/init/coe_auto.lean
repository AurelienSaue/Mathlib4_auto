/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import PrePort
import Lean3Lib.init.data.list.basic
import Lean3Lib.init.data.subtype.basic
import Lean3Lib.init.data.prod
import PostPort

universes u v l u₁ u₂ u₃ ua₁ ua₂ ub₁ ub₂ ua ub 

namespace Mathlib

/-
The elaborator tries to insert coercions automatically.
Only instances of has_coe type class are considered in the process.

Lean also provides a "lifting" operator: ↑a.
It uses all instances of has_lift type class.
Every has_coe instance is also a has_lift instance.

We recommend users only use has_coe for coercions that do not produce a lot
of ambiguity.

All coercions and lifts can be identified with the constant coe.

We use the has_coe_to_fun type class for encoding coercions from
a type to a function space.

We use the has_coe_to_sort type class for encoding coercions from
a type to a sort.
-/

/-- Can perform a lifting operation `↑a`. -/
class has_lift (a : Sort u) (b : Sort v) 
where
  lift : a → b

/-- Auxiliary class that contains the transitive closure of has_lift. -/
class has_lift_t (a : Sort u) (b : Sort v) 
where
  lift : a → b

class has_coe (a : Sort u) (b : Sort v) 
where
  coe : a → b

/-- Auxiliary class that contains the transitive closure of has_coe. -/
class has_coe_t (a : Sort u) (b : Sort v) 
where
  coe : a → b

class has_coe_to_fun (a : Sort u) 
where
  F : a → Sort v
  coe : (x : a) → F x

class has_coe_to_sort (a : Sort u) 
where
  S : Sort v
  coe : a → S

def lift {a : Sort u} {b : Sort v} [has_lift a b] : a → b :=
  has_lift.lift

def lift_t {a : Sort u} {b : Sort v} [has_lift_t a b] : a → b :=
  has_lift_t.lift

def coe_b {a : Sort u} {b : Sort v} [has_coe a b] : a → b :=
  has_coe.coe

def coe_t {a : Sort u} {b : Sort v} [has_coe_t a b] : a → b :=
  has_coe_t.coe

def coe_fn_b {a : Sort u} [has_coe_to_fun a] (x : a) : has_coe_to_fun.F x :=
  has_coe_to_fun.coe

/- User level coercion operators -/

def coe {a : Sort u} {b : Sort v} [has_lift_t a b] : a → b :=
  lift_t

def coe_fn {a : Sort u} [has_coe_to_fun a] (x : a) : has_coe_to_fun.F x :=
  has_coe_to_fun.coe

def coe_sort {a : Sort u} [has_coe_to_sort a] : a → has_coe_to_sort.S a :=
  has_coe_to_sort.coe

prefix:1024 "↑" => Mathlib.coe

prefix:1024 "⇑" => Mathlib.coe_fn

prefix:1024 "↥" => Mathlib.coe_sort

/- Notation -/

/- Transitive closure for has_lift, has_coe, has_coe_to_fun -/

protected instance lift_trans {a : Sort u₁} {b : Sort u₂} {c : Sort u₃} [has_lift_t b c] [has_lift a b] : has_lift_t a c :=
  has_lift_t.mk fun (x : a) => lift_t (lift x)

protected instance lift_base {a : Sort u} {b : Sort v} [has_lift a b] : has_lift_t a b :=
  has_lift_t.mk lift

protected instance coe_trans {a : Sort u₁} {b : Sort u₂} {c : Sort u₃} [has_coe_t b c] [has_coe a b] : has_coe_t a c :=
  has_coe_t.mk fun (x : a) => coe_t (coe_b x)

protected instance coe_base {a : Sort u} {b : Sort v} [has_coe a b] : has_coe_t a b :=
  has_coe_t.mk coe_b

/- We add this instance directly into has_coe_t to avoid non-termination.

   Suppose coe_option had type (has_coe a (option a)).
   Then, we can loop when searching a coercion from α to β (has_coe_t α β)
   1- coe_trans at (has_coe_t α β)
          (has_coe α ?b₁) and (has_coe_t ?b₁ c)
   2- coe_option at (has_coe α ?b₁)
          ?b₁ := option α
   3- coe_trans at (has_coe_t (option α) β)
          (has_coe (option α) ?b₂) and (has_coe_t ?b₂ β)
   4- coe_option at (has_coe (option α) ?b₂)
          ?b₂ := option (option α))
   ...
-/

protected instance coe_option {a : Type u} : has_coe_t a (Option a) :=
  has_coe_t.mk fun (x : a) => some x

/- Auxiliary transitive closure for has_coe which does not contain
   instances such as coe_option.

   They would produce non-termination when combined with coe_fn_trans and coe_sort_trans.
-/

class has_coe_t_aux (a : Sort u) (b : Sort v) 
where
  coe : a → b

protected instance coe_trans_aux {a : Sort u₁} {b : Sort u₂} {c : Sort u₃} [has_coe_t_aux b c] [has_coe a b] : has_coe_t_aux a c :=
  has_coe_t_aux.mk fun (x : a) => has_coe_t_aux.coe (coe_b x)

protected instance coe_base_aux {a : Sort u} {b : Sort v} [has_coe a b] : has_coe_t_aux a b :=
  has_coe_t_aux.mk coe_b

protected instance coe_fn_trans {a : Sort u₁} {b : Sort u₂} [has_coe_to_fun b] [has_coe_t_aux a b] : has_coe_to_fun a :=
  has_coe_to_fun.mk (fun (x : a) => has_coe_to_fun.F (has_coe_t_aux.coe x)) fun (x : a) => ⇑(has_coe_t_aux.coe x)

protected instance coe_sort_trans {a : Sort u₁} {b : Sort u₂} [has_coe_to_sort b] [has_coe_t_aux a b] : has_coe_to_sort a :=
  has_coe_to_sort.mk (has_coe_to_sort.S b) fun (x : a) => ↥(has_coe_t_aux.coe x)

/- Every coercion is also a lift -/

protected instance coe_to_lift {a : Sort u} {b : Sort v} [has_coe_t a b] : has_lift_t a b :=
  has_lift_t.mk coe_t

/- basic coercions -/

protected instance coe_bool_to_Prop : has_coe Bool Prop :=
  has_coe.mk fun (y : Bool) => y = tt

/- Tactics such as the simplifier only unfold reducible constants when checking whether two terms are definitionally
   equal or a term is a proposition. The motivation is performance.
   In particular, when simplifying `p -> q`, the tactic `simp` only visits `p` if it can establish that it is a proposition.
   Thus, we mark the following instance as @[reducible], otherwise `simp` will not visit `↑p` when simplifying `↑p -> q`.
-/

protected instance coe_sort_bool : has_coe_to_sort Bool :=
  has_coe_to_sort.mk Prop fun (y : Bool) => y = tt

protected instance coe_decidable_eq (x : Bool) : Decidable ↑x :=
  (fun (this : Decidable (x = tt)) => this) (bool.decidable_eq x tt)

protected instance coe_subtype {a : Sort u} {p : a → Prop} : has_coe (Subtype fun (x : a) => p x) a :=
  has_coe.mk subtype.val

/- basic lifts -/

/- Remark: we can't use [has_lift_t a₂ a₁] since it will produce non-termination whenever a type class resolution
   problem does not have a solution. -/

protected instance lift_fn {a₁ : Sort ua₁} {a₂ : Sort ua₂} {b₁ : Sort ub₁} {b₂ : Sort ub₂} [has_lift a₂ a₁] [has_lift_t b₁ b₂] : has_lift (a₁ → b₁) (a₂ → b₂) :=
  has_lift.mk fun (f : a₁ → b₁) (x : a₂) => ↑(f ↑x)

protected instance lift_fn_range {a : Sort ua} {b₁ : Sort ub₁} {b₂ : Sort ub₂} [has_lift_t b₁ b₂] : has_lift (a → b₁) (a → b₂) :=
  has_lift.mk fun (f : a → b₁) (x : a) => ↑(f x)

protected instance lift_fn_dom {a₁ : Sort ua₁} {a₂ : Sort ua₂} {b : Sort ub} [has_lift a₂ a₁] : has_lift (a₁ → b) (a₂ → b) :=
  has_lift.mk fun (f : a₁ → b) (x : a₂) => f ↑x

protected instance lift_pair {a₁ : Type ua₁} {a₂ : Type ub₂} {b₁ : Type ub₁} {b₂ : Type ub₂} [has_lift_t a₁ a₂] [has_lift_t b₁ b₂] : has_lift (a₁ × b₁) (a₂ × b₂) :=
  has_lift.mk fun (p : a₁ × b₁) => prod.cases_on p fun (x : a₁) (y : b₁) => (↑x, ↑y)

protected instance lift_pair₁ {a₁ : Type ua₁} {a₂ : Type ua₂} {b : Type ub} [has_lift_t a₁ a₂] : has_lift (a₁ × b) (a₂ × b) :=
  has_lift.mk fun (p : a₁ × b) => prod.cases_on p fun (x : a₁) (y : b) => (↑x, y)

protected instance lift_pair₂ {a : Type ua} {b₁ : Type ub₁} {b₂ : Type ub₂} [has_lift_t b₁ b₂] : has_lift (a × b₁) (a × b₂) :=
  has_lift.mk fun (p : a × b₁) => prod.cases_on p fun (x : a) (y : b₁) => (x, ↑y)

protected instance lift_list {a : Type u} {b : Type v} [has_lift_t a b] : has_lift (List a) (List b) :=
  has_lift.mk fun (l : List a) => list.map coe l

