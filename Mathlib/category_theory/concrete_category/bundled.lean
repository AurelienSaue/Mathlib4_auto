/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl, Reid Barton, Sean Leather
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.category.default
import Mathlib.PostPort

universes u v l 

namespace Mathlib

/-!
# Bundled types

`bundled c` provides a uniform structure for bundling a type equipped with a type class.

We provide `category` instances for these in `category_theory/unbundled_hom.lean`
(for categories with unbundled homs, e.g. topological spaces)
and in `category_theory/bundled_hom.lean` (for categories with bundled homs, e.g. monoids).
-/

namespace category_theory


/-- `bundled` is a type bundled with a type class instance for that type. Only
the type class is exposed as a parameter. -/
structure bundled (c : Type u → Type v) 
where
  α : Type u
  str : autoParam (c α)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.tactic.apply_instance")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "tactic") "apply_instance") [])

namespace bundled


/-- A generic function for lifting a type equipped with an instance to a bundled object. -/
-- Usually explicit instances will provide their own version of this, e.g. `Mon.of` and `Top.of`.

def of {c : Type u → Type v} (α : Type u) [str : c α] : bundled c :=
  mk α

protected instance has_coe_to_sort {c : Type u → Type v} : has_coe_to_sort (bundled c) :=
  has_coe_to_sort.mk (Type u) α

@[simp] theorem coe_mk {c : Type u → Type v} (α : Type u) (str : autoParam (c α)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.tactic.apply_instance")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "tactic") "apply_instance") [])) : ↥(mk α) = α :=
  rfl

/-
`bundled.map` is reducible so that, if we define a category

  def Ring : Type (u+1) := induced_category SemiRing (bundled.map @ring.to_semiring)

instance search is able to "see" that a morphism R ⟶ S in Ring is really
a (semi)ring homomorphism from R.α to S.α, and not merely from
`(bundled.map @ring.to_semiring R).α` to `(bundled.map @ring.to_semiring S).α`.
-/

/-- Map over the bundled structure -/
def map {c : Type u → Type v} {d : Type u → Type v} (f : {α : Type u} → c α → d α) (b : bundled c) : bundled d :=
  mk ↥b

