/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.order.conditionally_complete_lattice
import Mathlib.PostPort

universes u 

namespace Mathlib

/-!
# Tooling to make copies of lattice structures

Sometimes it is useful to make a copy of a lattice structure
where one replaces the data parts with provably equal definitions
that have better definitional properties.
-/

/-- A function to create a provable equal copy of a bounded lattice
with possibly different definitional equalities. -/
def bounded_lattice.copy {α : Type u} (c : bounded_lattice α) (le : α → α → Prop) (eq_le : le = bounded_lattice.le) (top : α) (eq_top : top = bounded_lattice.top) (bot : α) (eq_bot : bot = bounded_lattice.bot) (sup : α → α → α) (eq_sup : sup = bounded_lattice.sup) (inf : α → α → α) (eq_inf : inf = bounded_lattice.inf) : bounded_lattice α :=
  bounded_lattice.mk sup le (lattice.lt._default le) sorry sorry sorry sorry sorry sorry inf sorry sorry sorry top sorry
    bot sorry

/-- A function to create a provable equal copy of a distributive lattice
with possibly different definitional equalities. -/
def distrib_lattice.copy {α : Type u} (c : distrib_lattice α) (le : α → α → Prop) (eq_le : le = distrib_lattice.le) (sup : α → α → α) (eq_sup : sup = distrib_lattice.sup) (inf : α → α → α) (eq_inf : inf = distrib_lattice.inf) : distrib_lattice α :=
  distrib_lattice.mk sup le (lattice.lt._default le) sorry sorry sorry sorry sorry sorry inf sorry sorry sorry sorry

/-- A function to create a provable equal copy of a complete lattice
with possibly different definitional equalities. -/
def complete_lattice.copy {α : Type u} (c : complete_lattice α) (le : α → α → Prop) (eq_le : le = complete_lattice.le) (top : α) (eq_top : top = complete_lattice.top) (bot : α) (eq_bot : bot = complete_lattice.bot) (sup : α → α → α) (eq_sup : sup = complete_lattice.sup) (inf : α → α → α) (eq_inf : inf = complete_lattice.inf) (Sup : set α → α) (eq_Sup : Sup = complete_lattice.Sup) (Inf : set α → α) (eq_Inf : Inf = complete_lattice.Inf) : complete_lattice α :=
  complete_lattice.mk sup le bounded_lattice.lt sorry sorry sorry sorry sorry sorry inf sorry sorry sorry top sorry bot
    sorry Sup Inf sorry sorry sorry sorry

/-- A function to create a provable equal copy of a complete distributive lattice
with possibly different definitional equalities. -/
def complete_distrib_lattice.copy {α : Type u} (c : complete_distrib_lattice α) (le : α → α → Prop) (eq_le : le = complete_distrib_lattice.le) (top : α) (eq_top : top = complete_distrib_lattice.top) (bot : α) (eq_bot : bot = complete_distrib_lattice.bot) (sup : α → α → α) (eq_sup : sup = complete_distrib_lattice.sup) (inf : α → α → α) (eq_inf : inf = complete_distrib_lattice.inf) (Sup : set α → α) (eq_Sup : Sup = complete_distrib_lattice.Sup) (Inf : set α → α) (eq_Inf : Inf = complete_distrib_lattice.Inf) : complete_distrib_lattice α :=
  complete_distrib_lattice.mk sup le complete_lattice.lt sorry sorry sorry sorry sorry sorry inf sorry sorry sorry top
    sorry bot sorry Sup Inf sorry sorry sorry sorry sorry sorry

/-- A function to create a provable equal copy of a conditionally complete lattice
with possibly different definitional equalities. -/
def conditionally_complete_lattice.copy {α : Type u} (c : conditionally_complete_lattice α) (le : α → α → Prop) (eq_le : le = conditionally_complete_lattice.le) (sup : α → α → α) (eq_sup : sup = conditionally_complete_lattice.sup) (inf : α → α → α) (eq_inf : inf = conditionally_complete_lattice.inf) (Sup : set α → α) (eq_Sup : Sup = conditionally_complete_lattice.Sup) (Inf : set α → α) (eq_Inf : Inf = conditionally_complete_lattice.Inf) : conditionally_complete_lattice α :=
  conditionally_complete_lattice.mk sup le (lattice.lt._default le) sorry sorry sorry sorry sorry sorry inf sorry sorry
    sorry Sup Inf sorry sorry sorry sorry

