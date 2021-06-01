/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.limits.shapes.terminal
import Mathlib.category_theory.limits.shapes.binary_products
import Mathlib.PostPort

universes v₁ u₁ 

namespace Mathlib

/-!
# Subterminal objects

Subterminal objects are the objects which can be thought of as subobjects of the terminal object.
In fact, the definition can be constructed to not require a terminal object, by defining `A` to be
subterminal iff for any `Z`, there is at most one morphism `Z ⟶ A`.
An alternate definition is that the diagonal morphism `A ⟶ A ⨯ A` is an isomorphism.
In this file we define subterminal objects and show the equivalence of these three definitions.

We also construct the subcategory of subterminal objects.

## TODO

* Define exponential ideals, and show this subcategory is an exponential ideal.
* Define subobject lattices in general, show that `subterminals C` is equivalent to the subobject
category of a terminal object.
* Use both the above to show that in a locally cartesian closed category, every subobject lattice
  is cartesian closed (equivalently, a Heyting algebra).

-/

namespace category_theory


/-- An object `A` is subterminal iff for any `Z`, there is at most one morphism `Z ⟶ A`. -/
def is_subterminal {C : Type u₁} [category C] (A : C) := ∀ {Z : C} (f g : Z ⟶ A), f = g

theorem is_subterminal.def {C : Type u₁} [category C] {A : C} :
    is_subterminal A ↔ ∀ {Z : C} (f g : Z ⟶ A), f = g :=
  iff.rfl

/--
If `A` is subterminal, the unique morphism from it to a terminal object is a monomorphism.
The converse of `is_subterminal_of_mono_is_terminal_from`.
-/
theorem is_subterminal.mono_is_terminal_from {C : Type u₁} [category C] {A : C}
    (hA : is_subterminal A) {T : C} (hT : limits.is_terminal T) :
    mono (limits.is_terminal.from hT A) :=
  mono.mk
    fun (Z : C) (g h : Z ⟶ A)
      (_x : g ≫ limits.is_terminal.from hT A = h ≫ limits.is_terminal.from hT A) => hA g h

/--
If `A` is subterminal, the unique morphism from it to the terminal object is a monomorphism.
The converse of `is_subterminal_of_mono_terminal_from`.
-/
theorem is_subterminal.mono_terminal_from {C : Type u₁} [category C] {A : C} [limits.has_terminal C]
    (hA : is_subterminal A) : mono (limits.terminal.from A) :=
  is_subterminal.mono_is_terminal_from hA limits.terminal_is_terminal

/--
If the unique morphism from `A` to a terminal object is a monomorphism, `A` is subterminal.
The converse of `is_subterminal.mono_is_terminal_from`.
-/
theorem is_subterminal_of_mono_is_terminal_from {C : Type u₁} [category C] {A : C} {T : C}
    (hT : limits.is_terminal T) [mono (limits.is_terminal.from hT A)] : is_subterminal A :=
  fun (Z : C) (f g : Z ⟶ A) =>
    eq.mpr
      (id
        (Eq._oldrec (Eq.refl (f = g))
          (Eq.symm (propext (cancel_mono (limits.is_terminal.from hT A))))))
      (limits.is_terminal.hom_ext hT (f ≫ limits.is_terminal.from hT A)
        (g ≫ limits.is_terminal.from hT A))

/--
If the unique morphism from `A` to the terminal object is a monomorphism, `A` is subterminal.
The converse of `is_subterminal.mono_terminal_from`.
-/
theorem is_subterminal_of_mono_terminal_from {C : Type u₁} [category C] {A : C}
    [limits.has_terminal C] [mono (limits.terminal.from A)] : is_subterminal A :=
  fun (Z : C) (f g : Z ⟶ A) =>
    eq.mpr
      (id (Eq._oldrec (Eq.refl (f = g)) (Eq.symm (propext (cancel_mono (limits.terminal.from A))))))
      (subsingleton.elim (f ≫ limits.terminal.from A) (g ≫ limits.terminal.from A))

theorem is_subterminal_of_is_terminal {C : Type u₁} [category C] {T : C}
    (hT : limits.is_terminal T) : is_subterminal T :=
  fun (Z : C) (f g : Z ⟶ T) => limits.is_terminal.hom_ext hT f g

theorem is_subterminal_of_terminal {C : Type u₁} [category C] [limits.has_terminal C] :
    is_subterminal (⊤_C) :=
  fun (Z : C) (f g : Z ⟶ ⊤_C) => subsingleton.elim f g

/--
If `A` is subterminal, its diagonal morphism is an isomorphism.
The converse of `is_subterminal_of_is_iso_diag`.
-/
def is_subterminal.is_iso_diag {C : Type u₁} [category C] {A : C} (hA : is_subterminal A)
    [limits.has_binary_product A A] : is_iso (limits.diag A) :=
  is_iso.mk limits.prod.fst

/--
If the diagonal morphism of `A` is an isomorphism, then it is subterminal.
The converse of `is_subterminal.is_iso_diag`.
-/
theorem is_subterminal_of_is_iso_diag {C : Type u₁} [category C] {A : C}
    [limits.has_binary_product A A] [is_iso (limits.diag A)] : is_subterminal A :=
  sorry

/-- If `A` is subterminal, it is isomorphic to `A ⨯ A`. -/
@[simp] theorem is_subterminal.iso_diag_hom {C : Type u₁} [category C] {A : C}
    (hA : is_subterminal A) [limits.has_binary_product A A] :
    iso.hom (is_subterminal.iso_diag hA) = inv (limits.diag A) :=
  Eq.refl (inv (limits.diag A))

/--
The (full sub)category of subterminal objects.
TODO: If `C` is the category of sheaves on a topological space `X`, this category is equivalent
to the lattice of open subsets of `X`. More generally, if `C` is a topos, this is the lattice of
"external truth values".
-/
def subterminals (C : Type u₁) [category C] := Subtype fun (A : C) => is_subterminal A

protected instance subterminals.inhabited (C : Type u₁) [category C] [limits.has_terminal C] :
    Inhabited (subterminals C) :=
  { default := { val := ⊤_C, property := is_subterminal_of_terminal } }

/-- The inclusion of the subterminal objects into the original category. -/
def subterminal_inclusion (C : Type u₁) [category C] : subterminals C ⥤ C :=
  full_subcategory_inclusion fun (A : C) => is_subterminal A

end Mathlib