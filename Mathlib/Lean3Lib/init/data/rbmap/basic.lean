/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.data.rbtree.basic
 

universes u v w 

namespace Mathlib

def rbmap_lt {α : Type u} {β : Type v} (lt : α → α → Prop) (a : α × β) (b : α × β) :=
  lt (prod.fst a) (prod.fst b)

def rbmap (α : Type u) (β : Type v) (lt : autoParam (α → α → Prop)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.rbtree.default_lt")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "rbtree") "default_lt") [])) :=
  rbtree (α × β)

def mk_rbmap (α : Type u) (β : Type v) (lt : autoParam (α → α → Prop)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.rbtree.default_lt")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "rbtree") "default_lt") [])) : rbmap α β :=
  mk_rbtree (α × β)

namespace rbmap


def empty {α : Type u} {β : Type v} {lt : α → α → Prop} (m : rbmap α β) : Bool :=
  rbtree.empty m

def to_list {α : Type u} {β : Type v} {lt : α → α → Prop} (m : rbmap α β) : List (α × β) :=
  rbtree.to_list m

def min {α : Type u} {β : Type v} {lt : α → α → Prop} (m : rbmap α β) : Option (α × β) :=
  rbtree.min m

def max {α : Type u} {β : Type v} {lt : α → α → Prop} (m : rbmap α β) : Option (α × β) :=
  rbtree.max m

def fold {α : Type u} {β : Type v} {δ : Type w} {lt : α → α → Prop} (f : α → β → δ → δ) (m : rbmap α β) (d : δ) : δ :=
  rbtree.fold (fun (e : α × β) => f (prod.fst e) (prod.snd e)) m d

def rev_fold {α : Type u} {β : Type v} {δ : Type w} {lt : α → α → Prop} (f : α → β → δ → δ) (m : rbmap α β) (d : δ) : δ :=
  rbtree.rev_fold (fun (e : α × β) => f (prod.fst e) (prod.snd e)) m d

/-
We don't assume β is inhabited when in membership predicate `mem` and
function find_entry to make this module more convenient to use.
If we had assumed β to be inhabited we could use the following simpler
definition: (k, default β) ∈ m
-/

protected def mem {α : Type u} {β : Type v} {lt : α → α → Prop} (k : α) (m : rbmap α β) :=
  sorry

protected instance has_mem {α : Type u} {β : Type v} {lt : α → α → Prop} : has_mem α (rbmap α β) :=
  has_mem.mk rbmap.mem

protected instance has_repr {α : Type u} {β : Type v} {lt : α → α → Prop} [has_repr α] [has_repr β] : has_repr (rbmap α β) :=
  has_repr.mk
    fun (t : rbmap α β) =>
      string.str
          (string.str
            (string.str
              (string.str
                (string.str
                  (string.str
                    (string.str
                      (string.str (string.str string.empty (char.of_nat (bit0 (bit1 (bit0 (bit0 (bit1 (bit1 1))))))))
                        (char.of_nat (bit0 (bit1 (bit0 (bit0 (bit0 (bit1 1))))))))
                      (char.of_nat (bit1 (bit0 (bit1 (bit1 (bit0 (bit1 1))))))))
                    (char.of_nat (bit1 (bit0 (bit0 (bit0 (bit0 (bit1 1))))))))
                  (char.of_nat (bit0 (bit0 (bit0 (bit0 (bit1 (bit1 1))))))))
                (char.of_nat (bit1 (bit1 (bit1 (bit1 (bit1 (bit0 1))))))))
              (char.of_nat (bit1 (bit1 (bit1 (bit1 (bit0 (bit1 1))))))))
            (char.of_nat (bit0 (bit1 (bit1 (bit0 (bit0 (bit1 1))))))))
          (char.of_nat (bit0 (bit0 (bit0 (bit0 (bit0 1)))))) ++
        repr (to_list t)

def rbmap_lt_dec {α : Type u} {β : Type v} {lt : α → α → Prop} [h : DecidableRel lt] : DecidableRel (rbmap_lt lt) :=
  fun (a b : α × β) => h (prod.fst a) (prod.fst b)

def insert {α : Type u} {β : Type v} {lt : α → α → Prop} [DecidableRel lt] (m : rbmap α β) (k : α) (v : β) : rbmap α β :=
  rbtree.insert m (k, v)

def find_entry {α : Type u} {β : Type v} {lt : α → α → Prop} [DecidableRel lt] (m : rbmap α β) (k : α) : Option (α × β) :=
  sorry

def to_value {α : Type u} {β : Type v} : Option (α × β) → Option β :=
  sorry

def find {α : Type u} {β : Type v} {lt : α → α → Prop} [DecidableRel lt] (m : rbmap α β) (k : α) : Option β :=
  to_value (find_entry m k)

def contains {α : Type u} {β : Type v} {lt : α → α → Prop} [DecidableRel lt] (m : rbmap α β) (k : α) : Bool :=
  option.is_some (find_entry m k)

def from_list {α : Type u} {β : Type v} (l : List (α × β)) (lt : autoParam (α → α → Prop)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.rbtree.default_lt")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "rbtree") "default_lt") [])) [DecidableRel lt] : rbmap α β :=
  list.foldl (fun (m : rbmap α β) (p : α × β) => insert m (prod.fst p) (prod.snd p)) (mk_rbmap α β) l

end rbmap


def rbmap_of {α : Type u} {β : Type v} (l : List (α × β)) (lt : autoParam (α → α → Prop)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.rbtree.default_lt")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "rbtree") "default_lt") [])) [DecidableRel lt] : rbmap α β :=
  rbmap.from_list l

