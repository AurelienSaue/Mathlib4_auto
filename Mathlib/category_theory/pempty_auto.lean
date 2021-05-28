/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta.
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.discrete_category
import PostPort

universes v u 

namespace Mathlib

/-!
# The empty category

Defines a category structure on `pempty`, and the unique functor `pempty ⥤ C` for any category `C`.
-/

namespace category_theory


namespace functor


/-- The canonical functor out of the empty category. -/
def empty (C : Type u) [category C] : discrete pempty ⥤ C :=
  discrete.functor pempty.elim

/-- Any two functors out of the empty category are isomorphic. -/
def empty_ext {C : Type u} [category C] (F : discrete pempty ⥤ C) (G : discrete pempty ⥤ C) : F ≅ G :=
  discrete.nat_iso fun (x : discrete pempty) => pempty.elim x

/--
Any functor out of the empty category is isomorphic to the canonical functor from the empty
category.
-/
def unique_from_empty {C : Type u} [category C] (F : discrete pempty ⥤ C) : F ≅ empty C :=
  empty_ext F (empty C)

/--
Any two functors out of the empty category are *equal*. You probably want to use
`empty_ext` instead of this.
-/
theorem empty_ext' {C : Type u} [category C] (F : discrete pempty ⥤ C) (G : discrete pempty ⥤ C) : F = G :=
  ext (fun (x : discrete pempty) => pempty.elim x) fun (x _x : discrete pempty) (_x_1 : x ⟶ _x) => pempty.elim x

