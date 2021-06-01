/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.fintype.basic
import Mathlib.category_theory.discrete_category
import Mathlib.PostPort

universes u_1 v l 

namespace Mathlib

/-!
# Finite categories

A category is finite in this sense if it has finitely many objects, and finitely many morphisms.

## Implementation

We also ask for decidable equality of objects and morphisms, but it may be reasonable to just
go classical in future.
-/

namespace category_theory


protected instance discrete_fintype {α : Type u_1} [fintype α] : fintype (discrete α) := id _inst_1

protected instance discrete_hom_fintype {α : Type u_1} [DecidableEq α] (X : discrete α)
    (Y : discrete α) : fintype (X ⟶ Y) :=
  ulift.fintype (plift (X = Y))

/-- A category with a `fintype` of objects, and a `fintype` for each morphism space. -/
class fin_category (J : Type v) [small_category J] where
  decidable_eq_obj :
    autoParam (DecidableEq J)
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.tactic.apply_instance")
        (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "tactic")
          "apply_instance")
        [])
  fintype_obj :
    autoParam (fintype J)
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.tactic.apply_instance")
        (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "tactic")
          "apply_instance")
        [])
  decidable_eq_hom :
    autoParam ((j j' : J) → DecidableEq (j ⟶ j'))
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.tactic.apply_instance")
        (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "tactic")
          "apply_instance")
        [])
  fintype_hom :
    autoParam ((j j' : J) → fintype (j ⟶ j'))
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.tactic.apply_instance")
        (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "tactic")
          "apply_instance")
        [])

-- We need a `decidable_eq` instance here to construct `fintype` on the morphism spaces.

protected instance fin_category_discrete_of_decidable_fintype (J : Type v) [DecidableEq J]
    [fintype J] : fin_category (discrete J) :=
  fin_category.mk

end Mathlib