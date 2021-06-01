/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.abelian.pseudoelements
import Mathlib.PostPort

universes v u 

namespace Mathlib

/-!
# The four lemma

Consider the following commutative diagram with exact rows in an abelian category:

A ---f--> B ---g--> C ---h--> D
|         |         |         |
α         β         γ         δ
|         |         |         |
v         v         v         v
A' --f'-> B' --g'-> C' --h'-> D'

We prove the "mono" version of the four lemma: if α is an epimorphism and β and δ are monomorphisms,
then γ is a monomorphism.

## Future work

The "epi" four lemma and the five lemma, which is then an easy corollary.

## Tags

four lemma, diagram lemma, diagram chase
-/

namespace category_theory.abelian


/-- The four lemma, mono version. For names of objects and morphisms, consider the following
    diagram:

```
A ---f--> B ---g--> C ---h--> D
|         |         |         |
α         β         γ         δ
|         |         |         |
v         v         v         v
A' --f'-> B' --g'-> C' --h'-> D'
```
-/
theorem mono_of_epi_of_mono_of_mono {V : Type u} [category V] [abelian V] {A : V} {B : V} {C : V}
    {D : V} {A' : V} {B' : V} {C' : V} {D' : V} {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D} {f' : A' ⟶ B'}
    {g' : B' ⟶ C'} {h' : C' ⟶ D'} {α : A ⟶ A'} {β : B ⟶ B'} {γ : C ⟶ C'} {δ : D ⟶ D'} [exact f g]
    [exact g h] [exact f' g'] (comm₁ : α ≫ f' = f ≫ β) (comm₂ : β ≫ g' = g ≫ γ)
    (comm₃ : γ ≫ h' = h ≫ δ) (hα : epi α) (hβ : mono β) (hδ : mono δ) : mono γ :=
  sorry

end Mathlib