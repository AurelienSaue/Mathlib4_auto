/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import PrePort
import Lean3Lib.init.data.ordering.default
import PostPort

universes u l v 

namespace Mathlib

inductive rbnode (α : Type u) 
where
| leaf : rbnode α
| red_node : rbnode α → α → rbnode α → rbnode α
| black_node : rbnode α → α → rbnode α → rbnode α

namespace rbnode


inductive color 
where
| red : color
| black : color

protected instance color.decidable_eq : DecidableEq color :=
  fun (a b : color) =>
    color.cases_on a (color.cases_on b (is_true rfl) (isFalse sorry)) (color.cases_on b (isFalse sorry) (is_true rfl))

def depth {α : Type u} (f : ℕ → ℕ → ℕ) : rbnode α → ℕ :=
  sorry

protected def min {α : Type u} : rbnode α → Option α :=
  sorry

protected def max {α : Type u} : rbnode α → Option α :=
  sorry

def fold {α : Type u} {β : Type v} (f : α → β → β) : rbnode α → β → β :=
  sorry

def rev_fold {α : Type u} {β : Type v} (f : α → β → β) : rbnode α → β → β :=
  sorry

def balance1 {α : Type u} : rbnode α → α → rbnode α → α → rbnode α → rbnode α :=
  sorry

def balance1_node {α : Type u} : rbnode α → α → rbnode α → rbnode α :=
  sorry

def balance2 {α : Type u} : rbnode α → α → rbnode α → α → rbnode α → rbnode α :=
  sorry

def balance2_node {α : Type u} : rbnode α → α → rbnode α → rbnode α :=
  sorry

def get_color {α : Type u} : rbnode α → color :=
  sorry

def ins {α : Type u} (lt : α → α → Prop) [DecidableRel lt] : rbnode α → α → rbnode α :=
  sorry

def mk_insert_result {α : Type u} : color → rbnode α → rbnode α :=
  sorry

def insert {α : Type u} (lt : α → α → Prop) [DecidableRel lt] (t : rbnode α) (x : α) : rbnode α :=
  mk_insert_result (get_color t) (ins lt t x)

def mem {α : Type u} (lt : α → α → Prop) : α → rbnode α → Prop :=
  sorry

def mem_exact {α : Type u} : α → rbnode α → Prop :=
  sorry

def find {α : Type u} (lt : α → α → Prop) [DecidableRel lt] : rbnode α → α → Option α :=
  sorry

inductive well_formed {α : Type u} (lt : α → α → Prop) : rbnode α → Prop
where
| leaf_wff : well_formed lt leaf
| insert_wff : ∀ {n n' : rbnode α} {x : α} [_inst_1 : DecidableRel lt], well_formed lt n → n' = insert lt n x → well_formed lt n'

end rbnode


def rbtree (α : Type u) (lt : autoParam (α → α → Prop)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.rbtree.default_lt")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "rbtree") "default_lt") []))  :=
  Subtype fun (t : rbnode α) => rbnode.well_formed lt t

def mk_rbtree (α : Type u) (lt : autoParam (α → α → Prop)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.rbtree.default_lt")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "rbtree") "default_lt") [])) : rbtree α :=
  { val := rbnode.leaf, property := rbnode.well_formed.leaf_wff }

namespace rbtree


protected def mem {α : Type u} {lt : α → α → Prop} (a : α) (t : rbtree α)  :=
  rbnode.mem lt a (subtype.val t)

protected instance has_mem {α : Type u} {lt : α → α → Prop} : has_mem α (rbtree α) :=
  has_mem.mk rbtree.mem

def mem_exact {α : Type u} {lt : α → α → Prop} (a : α) (t : rbtree α)  :=
  rbnode.mem_exact a (subtype.val t)

def depth {α : Type u} {lt : α → α → Prop} (f : ℕ → ℕ → ℕ) (t : rbtree α) : ℕ :=
  rbnode.depth f (subtype.val t)

def fold {α : Type u} {β : Type v} {lt : α → α → Prop} (f : α → β → β) : rbtree α → β → β :=
  sorry

def rev_fold {α : Type u} {β : Type v} {lt : α → α → Prop} (f : α → β → β) : rbtree α → β → β :=
  sorry

def empty {α : Type u} {lt : α → α → Prop} : rbtree α → Bool :=
  sorry

def to_list {α : Type u} {lt : α → α → Prop} : rbtree α → List α :=
  sorry

protected def min {α : Type u} {lt : α → α → Prop} : rbtree α → Option α :=
  sorry

protected def max {α : Type u} {lt : α → α → Prop} : rbtree α → Option α :=
  sorry

protected instance has_repr {α : Type u} {lt : α → α → Prop} [has_repr α] : has_repr (rbtree α) := sorry

def insert {α : Type u} {lt : α → α → Prop} [DecidableRel lt] : rbtree α → α → rbtree α :=
  sorry

def find {α : Type u} {lt : α → α → Prop} [DecidableRel lt] : rbtree α → α → Option α :=
  sorry

def contains {α : Type u} {lt : α → α → Prop} [DecidableRel lt] (t : rbtree α) (a : α) : Bool :=
  option.is_some (find t a)

def from_list {α : Type u} (l : List α) (lt : autoParam (α → α → Prop)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.rbtree.default_lt")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "rbtree") "default_lt") [])) [DecidableRel lt] : rbtree α :=
  list.foldl insert (mk_rbtree α) l

end rbtree


def rbtree_of {α : Type u} (l : List α) (lt : autoParam (α → α → Prop)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.rbtree.default_lt")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "rbtree") "default_lt") [])) [DecidableRel lt] : rbtree α :=
  rbtree.from_list l

