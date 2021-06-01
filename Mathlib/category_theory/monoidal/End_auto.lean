/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.monoidal.functor
import Mathlib.PostPort

universes u v 

namespace Mathlib

/-!
# Endofunctors as a monoidal category.

We give the monoidal category structure on `C ⥤ C`,
and show that when `C` itself is monoidal, it embeds via a monoidal functor into `C ⥤ C`.

## TODO

Can we use this to show coherence results, e.g. a cheap proof that `λ_ (𝟙_ C) = ρ_ (𝟙_ C)`?
I suspect this is harder than is usually made out.
-/

namespace category_theory


/--
The category of endofunctors of any category is a monoidal category,
with tensor product given by composition of functors
(and horizontal composition of natural transformations).
-/
def endofunctor_monoidal_category (C : Type u) [category C] : monoidal_category (C ⥤ C) :=
  monoidal_category.mk (fun (F G : C ⥤ C) => F ⋙ G)
    (fun (F G F' G' : C ⥤ C) (α : F ⟶ G) (β : F' ⟶ G') => α ◫ β) 𝟭
    (fun (F G H : C ⥤ C) => functor.associator F G H) (fun (F : C ⥤ C) => functor.left_unitor F)
    fun (F : C ⥤ C) => functor.right_unitor F

/--
Tensoring on the right gives a monoidal functor from `C` into endofunctors of `C`.
-/
@[simp] theorem tensoring_right_monoidal_to_lax_monoidal_functor_to_functor (C : Type u)
    [category C] [monoidal_category C] :
    lax_monoidal_functor.to_functor
          (monoidal_functor.to_lax_monoidal_functor (tensoring_right_monoidal C)) =
        monoidal_category.tensoring_right C :=
  Eq.refl
    (lax_monoidal_functor.to_functor
      (monoidal_functor.to_lax_monoidal_functor (tensoring_right_monoidal C)))

end Mathlib