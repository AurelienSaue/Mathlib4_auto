/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.int.basic
import Mathlib.category_theory.graded_object
import Mathlib.category_theory.differential_object
import Mathlib.PostPort

universes v u u_1 

namespace Mathlib

/-!
# Chain complexes

We define a chain complex in `V` as a differential `ℤ`-graded object in `V`.

This is fancy language for the obvious definition,
and it seems we can use it straightforwardly:

```
example (C : chain_complex V) : C.X 5 ⟶ C.X 6 := C.d 5
```

-/

/--
A `homological_complex V b` for `b : β` is a (co)chain complex graded by `β`,
with differential in grading `b`.

(We use the somewhat cumbersome `homological_complex` to avoid the name conflict with `ℂ`.)
-/
def homological_complex (V : Type u) [category_theory.category V]
    [category_theory.limits.has_zero_morphisms V] {β : Type} [add_comm_group β] (b : β) :=
  category_theory.differential_object (category_theory.graded_object_with_shift b V)

/--
A chain complex in `V` is "just" a differential `ℤ`-graded object in `V`,
with differential graded `-1`.
-/
def chain_complex (V : Type u) [category_theory.category V]
    [category_theory.limits.has_zero_morphisms V] :=
  homological_complex V (-1)

/--
A cochain complex in `V` is "just" a differential `ℤ`-graded object in `V`,
with differential graded `+1`.
-/
def cochain_complex (V : Type u) [category_theory.category V]
    [category_theory.limits.has_zero_morphisms V] :=
  homological_complex V 1

-- The chain groups of a chain complex `C` are accessed as `C.X i`,

-- and the differentials as `C.d i : C.X i ⟶ C.X (i-1)`.

namespace homological_complex


@[simp] theorem d_squared {V : Type u} [category_theory.category V]
    [category_theory.limits.has_zero_morphisms V] {β : Type} [add_comm_group β] {b : β}
    (C : homological_complex V b) (i : β) :
    category_theory.differential_object.d C i ≫ category_theory.differential_object.d C (i + b) =
        0 :=
  sorry

/--
A convenience lemma for morphisms of cochain complexes,
picking out one component of the commutation relation.
-/
-- I haven't been able to get this to work with projection notation: `f.comm_at i`

@[simp] theorem comm_at {V : Type u} [category_theory.category V]
    [category_theory.limits.has_zero_morphisms V] {β : Type} [add_comm_group β] {b : β}
    {C : homological_complex V b} {D : homological_complex V b} (f : C ⟶ D) (i : β) :
    category_theory.differential_object.d C i ≫
          category_theory.differential_object.hom.f f (i + b) =
        category_theory.differential_object.hom.f f i ≫ category_theory.differential_object.d D i :=
  sorry

@[simp] theorem comm {V : Type u} [category_theory.category V]
    [category_theory.limits.has_zero_morphisms V] {β : Type} [add_comm_group β] {b : β}
    {C : homological_complex V b} {D : homological_complex V b} (f : C ⟶ D) :
    category_theory.differential_object.d C ≫
          category_theory.functor.map
            (category_theory.equivalence.functor
              (category_theory.shift (category_theory.graded_object_with_shift b V) ^ 1))
            (category_theory.differential_object.hom.f f) =
        category_theory.differential_object.hom.f f ≫ category_theory.differential_object.d D :=
  category_theory.differential_object.hom.comm (category_theory.graded_object_with_shift b V)
    (category_theory.graded_object.category_of_graded_objects β)
    (category_theory.graded_object.has_zero_morphisms β) (category_theory.graded_object.has_shift b)
    C D f

/-- The forgetful functor from cochain complexes to graded objects, forgetting the differential. -/
def forget (V : Type u) [category_theory.category V] [category_theory.limits.has_zero_morphisms V]
    {β : Type} [add_comm_group β] {b : β} :
    homological_complex V b ⥤ category_theory.graded_object β V :=
  category_theory.differential_object.forget (category_theory.graded_object_with_shift b V)

protected instance inhabited {β : Type} [add_comm_group β] {b : β} :
    Inhabited (homological_complex (category_theory.discrete PUnit) b) :=
  { default := 0 }

end Mathlib