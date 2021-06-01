/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.logic
import Mathlib.Lean3Lib.init.data.ordering.basic

universes u v l 

namespace Mathlib

class is_symm_op (α : Type u) (β : outParam (Type v)) (op : α → α → β) where
  symm_op : ∀ (a b : α), op a b = op b a

class is_commutative (α : Type u) (op : α → α → α) where
  comm : ∀ (a b : α), op a b = op b a

protected instance is_symm_op_of_is_commutative (α : Type u) (op : α → α → α)
    [is_commutative α op] : is_symm_op α α op :=
  is_symm_op.mk is_commutative.comm

class is_associative (α : Type u) (op : α → α → α) where
  assoc : ∀ (a b c : α), op (op a b) c = op a (op b c)

class is_left_id (α : Type u) (op : α → α → α) (o : outParam α) where
  left_id : ∀ (a : α), op o a = a

class is_right_id (α : Type u) (op : α → α → α) (o : outParam α) where
  right_id : ∀ (a : α), op a o = a

class is_left_null (α : Type u) (op : α → α → α) (o : outParam α) where
  left_null : ∀ (a : α), op o a = o

class is_right_null (α : Type u) (op : α → α → α) (o : outParam α) where
  right_null : ∀ (a : α), op a o = o

class is_left_cancel (α : Type u) (op : α → α → α) where
  left_cancel : ∀ (a b c : α), op a b = op a c → b = c

class is_right_cancel (α : Type u) (op : α → α → α) where
  right_cancel : ∀ (a b c : α), op a b = op c b → a = c

class is_idempotent (α : Type u) (op : α → α → α) where
  idempotent : ∀ (a : α), op a a = a

class is_left_distrib (α : Type u) (op₁ : α → α → α) (op₂ : outParam (α → α → α)) where
  left_distrib : ∀ (a b c : α), op₁ a (op₂ b c) = op₂ (op₁ a b) (op₁ a c)

class is_right_distrib (α : Type u) (op₁ : α → α → α) (op₂ : outParam (α → α → α)) where
  right_distrib : ∀ (a b c : α), op₁ (op₂ a b) c = op₂ (op₁ a c) (op₁ b c)

class is_left_inv (α : Type u) (op : α → α → α) (inv : outParam (α → α)) (o : outParam α) where
  left_inv : ∀ (a : α), op (inv a) a = o

class is_right_inv (α : Type u) (op : α → α → α) (inv : outParam (α → α)) (o : outParam α) where
  right_inv : ∀ (a : α), op a (inv a) = o

class is_cond_left_inv (α : Type u) (op : α → α → α) (inv : outParam (α → α)) (o : outParam α)
    (p : outParam (α → Prop))
    where
  left_inv : ∀ (a : α), p a → op (inv a) a = o

class is_cond_right_inv (α : Type u) (op : α → α → α) (inv : outParam (α → α)) (o : outParam α)
    (p : outParam (α → Prop))
    where
  right_inv : ∀ (a : α), p a → op a (inv a) = o

class is_distinct (α : Type u) (a : α) (b : α) where
  distinct : a ≠ b

/-
-- The following type class doesn't seem very useful, a regular simp lemma should work for this.

-- The following type class doesn't seem very useful, a regular simp lemma should work for this.
class is_inv (α : Type u) (β : Type v) (f : α → β) (g : out β → α) : Prop :=
(inv : ∀ a, g (f a) = a)

-- The following one can also be handled using a regular simp lemma

-- The following one can also be handled using a regular simp lemma
class is_idempotent (α : Type u) (f : α → α) : Prop :=
(idempotent : ∀ a, f (f a) = f a)
-/

/-- `is_irrefl X r` means the binary relation `r` on `X` is irreflexive (that is, `r x x` never
holds). -/
class is_irrefl (α : Type u) (r : α → α → Prop) where
  irrefl : ∀ (a : α), ¬r a a

/-- `is_refl X r` means the binary relation `r` on `X` is reflexive. -/
class is_refl (α : Type u) (r : α → α → Prop) where
  refl : ∀ (a : α), r a a

/-- `is_symm X r` means the binary relation `r` on `X` is symmetric. -/
class is_symm (α : Type u) (r : α → α → Prop) where
  symm : ∀ (a b : α), r a b → r b a

/-- The opposite of a symmetric relation is symmetric. -/
protected instance is_symm_op_of_is_symm (α : Type u) (r : α → α → Prop) [is_symm α r] :
    is_symm_op α Prop r :=
  is_symm_op.mk fun (a b : α) => propext { mp := is_symm.symm a b, mpr := is_symm.symm b a }

/-- `is_asymm X r` means that the binary relation `r` on `X` is asymmetric, that is,
`r a b → ¬ r b a`. -/
class is_asymm (α : Type u) (r : α → α → Prop) where
  asymm : ∀ (a b : α), r a b → ¬r b a

/-- `is_antisymm X r` means the binary relation `r` on `X` is antisymmetric. -/
class is_antisymm (α : Type u) (r : α → α → Prop) where
  antisymm : ∀ (a b : α), r a b → r b a → a = b

/-- `is_trans X r` means the binary relation `r` on `X` is transitive. -/
class is_trans (α : Type u) (r : α → α → Prop) where
  trans : ∀ (a b c : α), r a b → r b c → r a c

/-- `is_total X r` means that the binary relation `r` on `X` is total, that is, that for any
`x y : X` we have `r x y` or `r y x`.-/
class is_total (α : Type u) (r : α → α → Prop) where
  total : ∀ (a b : α), r a b ∨ r b a

/-- `is_preorder X r` means that the binary relation `r` on `X` is a pre-order, that is, reflexive
and transitive. -/
class is_preorder (α : Type u) (r : α → α → Prop) extends is_refl α r, is_trans α r where

/-- `is_total_preorder X r` means that the binary relation `r` on `X` is total and a preorder. -/
class is_total_preorder (α : Type u) (r : α → α → Prop) extends is_trans α r, is_total α r where

/-- Every total pre-order is a pre-order. -/
protected instance is_total_preorder_is_preorder (α : Type u) (r : α → α → Prop)
    [s : is_total_preorder α r] : is_preorder α r :=
  is_preorder.mk

class is_partial_order (α : Type u) (r : α → α → Prop) extends is_antisymm α r, is_preorder α r
    where

class is_linear_order (α : Type u) (r : α → α → Prop) extends is_total α r, is_partial_order α r
    where

class is_equiv (α : Type u) (r : α → α → Prop) extends is_symm α r, is_preorder α r where

class is_per (α : Type u) (r : α → α → Prop) extends is_symm α r, is_trans α r where

class is_strict_order (α : Type u) (r : α → α → Prop) extends is_trans α r, is_irrefl α r where

class is_incomp_trans (α : Type u) (lt : α → α → Prop) where
  incomp_trans : ∀ (a b c : α), ¬lt a b ∧ ¬lt b a → ¬lt b c ∧ ¬lt c b → ¬lt a c ∧ ¬lt c a

class is_strict_weak_order (α : Type u) (lt : α → α → Prop)
    extends is_incomp_trans α lt, is_strict_order α lt where

class is_trichotomous (α : Type u) (lt : α → α → Prop) where
  trichotomous : ∀ (a b : α), lt a b ∨ a = b ∨ lt b a

class is_strict_total_order (α : Type u) (lt : α → α → Prop)
    extends is_strict_weak_order α lt, is_trichotomous α lt where

protected instance eq_is_equiv (α : Type u) : is_equiv α Eq := is_equiv.mk

theorem irrefl {α : Type u} {r : α → α → Prop} [is_irrefl α r] (a : α) : ¬r a a :=
  is_irrefl.irrefl a

theorem refl {α : Type u} {r : α → α → Prop} [is_refl α r] (a : α) : r a a := is_refl.refl a

theorem trans {α : Type u} {r : α → α → Prop} [is_trans α r] {a : α} {b : α} {c : α} :
    r a b → r b c → r a c :=
  is_trans.trans a b c

theorem symm {α : Type u} {r : α → α → Prop} [is_symm α r] {a : α} {b : α} : r a b → r b a :=
  is_symm.symm a b

theorem antisymm {α : Type u} {r : α → α → Prop} [is_antisymm α r] {a : α} {b : α} :
    r a b → r b a → a = b :=
  is_antisymm.antisymm a b

theorem asymm {α : Type u} {r : α → α → Prop} [is_asymm α r] {a : α} {b : α} : r a b → ¬r b a :=
  is_asymm.asymm a b

theorem trichotomous {α : Type u} {r : α → α → Prop} [is_trichotomous α r] (a : α) (b : α) :
    r a b ∨ a = b ∨ r b a :=
  is_trichotomous.trichotomous

theorem incomp_trans {α : Type u} {r : α → α → Prop} [is_incomp_trans α r] {a : α} {b : α} {c : α} :
    ¬r a b ∧ ¬r b a → ¬r b c ∧ ¬r c b → ¬r a c ∧ ¬r c a :=
  is_incomp_trans.incomp_trans a b c

protected instance is_asymm_of_is_trans_of_is_irrefl {α : Type u} {r : α → α → Prop} [is_trans α r]
    [is_irrefl α r] : is_asymm α r :=
  is_asymm.mk fun (a b : α) (h₁ : r a b) (h₂ : r b a) => absurd (trans h₁ h₂) (irrefl a)

theorem irrefl_of {α : Type u} (r : α → α → Prop) [is_irrefl α r] (a : α) : ¬r a a := irrefl a

theorem refl_of {α : Type u} (r : α → α → Prop) [is_refl α r] (a : α) : r a a := refl a

theorem trans_of {α : Type u} (r : α → α → Prop) [is_trans α r] {a : α} {b : α} {c : α} :
    r a b → r b c → r a c :=
  trans

theorem symm_of {α : Type u} (r : α → α → Prop) [is_symm α r] {a : α} {b : α} : r a b → r b a :=
  symm

theorem asymm_of {α : Type u} (r : α → α → Prop) [is_asymm α r] {a : α} {b : α} : r a b → ¬r b a :=
  asymm

theorem total_of {α : Type u} (r : α → α → Prop) [is_total α r] (a : α) (b : α) : r a b ∨ r b a :=
  is_total.total a b

theorem trichotomous_of {α : Type u} (r : α → α → Prop) [is_trichotomous α r] (a : α) (b : α) :
    r a b ∨ a = b ∨ r b a :=
  trichotomous

theorem incomp_trans_of {α : Type u} (r : α → α → Prop) [is_incomp_trans α r] {a : α} {b : α}
    {c : α} : ¬r a b ∧ ¬r b a → ¬r b c ∧ ¬r c b → ¬r a c ∧ ¬r c a :=
  incomp_trans

namespace strict_weak_order


def equiv {α : Type u} {r : α → α → Prop} (a : α) (b : α) := ¬r a b ∧ ¬r b a

theorem erefl {α : Type u} {r : α → α → Prop} [is_strict_weak_order α r] (a : α) : equiv a a :=
  { left := irrefl a, right := irrefl a }

theorem esymm {α : Type u} {r : α → α → Prop} [is_strict_weak_order α r] {a : α} {b : α} :
    equiv a b → equiv b a :=
  sorry

theorem etrans {α : Type u} {r : α → α → Prop} [is_strict_weak_order α r] {a : α} {b : α} {c : α} :
    equiv a b → equiv b c → equiv a c :=
  incomp_trans

theorem not_lt_of_equiv {α : Type u} {r : α → α → Prop} [is_strict_weak_order α r] {a : α} {b : α} :
    equiv a b → ¬r a b :=
  fun (h : equiv a b) => and.left h

theorem not_lt_of_equiv' {α : Type u} {r : α → α → Prop} [is_strict_weak_order α r] {a : α}
    {b : α} : equiv a b → ¬r b a :=
  fun (h : equiv a b) => and.right h

protected instance is_equiv {α : Type u} {r : α → α → Prop} [is_strict_weak_order α r] :
    is_equiv α equiv :=
  is_equiv.mk

/- Notation for the equivalence relation induced by lt -/

end strict_weak_order


theorem is_strict_weak_order_of_is_total_preorder {α : Type u} {le : α → α → Prop}
    {lt : α → α → Prop} [DecidableRel le] [s : is_total_preorder α le]
    (h : ∀ (a b : α), lt a b ↔ ¬le b a) : is_strict_weak_order α lt :=
  is_strict_weak_order.mk

theorem lt_of_lt_of_incomp {α : Type u} {lt : α → α → Prop} [is_strict_weak_order α lt]
    [DecidableRel lt] {a : α} {b : α} {c : α} : lt a b → ¬lt b c ∧ ¬lt c b → lt a c :=
  sorry

theorem lt_of_incomp_of_lt {α : Type u} {lt : α → α → Prop} [is_strict_weak_order α lt]
    [DecidableRel lt] {a : α} {b : α} {c : α} : ¬lt a b ∧ ¬lt b a → lt b c → lt a c :=
  sorry

theorem eq_of_incomp {α : Type u} {lt : α → α → Prop} [is_trichotomous α lt] {a : α} {b : α} :
    ¬lt a b ∧ ¬lt b a → a = b :=
  sorry

theorem eq_of_eqv_lt {α : Type u} {lt : α → α → Prop} [is_trichotomous α lt] {a : α} {b : α} :
    strict_weak_order.equiv a b → a = b :=
  eq_of_incomp

theorem incomp_iff_eq {α : Type u} {lt : α → α → Prop} [is_trichotomous α lt] [is_irrefl α lt]
    (a : α) (b : α) : ¬lt a b ∧ ¬lt b a ↔ a = b :=
  { mp := eq_of_incomp,
    mpr := fun (hab : a = b) => hab ▸ { left := irrefl_of lt a, right := irrefl_of lt a } }

theorem eqv_lt_iff_eq {α : Type u} {lt : α → α → Prop} [is_trichotomous α lt] [is_irrefl α lt]
    (a : α) (b : α) : strict_weak_order.equiv a b ↔ a = b :=
  incomp_iff_eq a b

theorem not_lt_of_lt {α : Type u} {lt : α → α → Prop} [is_strict_order α lt] {a : α} {b : α} :
    lt a b → ¬lt b a :=
  fun (h₁ : lt a b) (h₂ : lt b a) => absurd (trans_of lt h₁ h₂) (irrefl_of lt a)

end Mathlib