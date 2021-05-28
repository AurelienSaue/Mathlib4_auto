/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.limits.preserves.limits
import Mathlib.category_theory.limits.shapes.default
import Mathlib.PostPort

universes u₁ u₂ v 

namespace Mathlib

/-!
# Preserving terminal object

Constructions to relate the notions of preserving terminal objects and reflecting terminal objects
to concrete objects.

In particular, we show that `terminal_comparison G` is an isomorphism iff `G` preserves terminal
objects.
-/

namespace category_theory.limits


/--
The map of an empty cone is a limit iff the mapped object is terminal.
-/
def is_limit_map_cone_empty_cone_equiv {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) (X : C) : is_limit (functor.map_cone G (as_empty_cone X)) ≃ is_terminal (functor.obj G X) :=
  equiv.trans
    (equiv.symm
      (is_limit.postcompose_hom_equiv (functor.empty_ext (functor.empty C ⋙ G) (functor.empty D))
        (functor.map_cone G (as_empty_cone X))))
    (is_limit.equiv_iso_limit
      (cones.ext
        (iso.refl
          (cone.X
            (functor.obj (cones.postcompose (iso.hom (functor.empty_ext (functor.empty C ⋙ G) (functor.empty D))))
              (functor.map_cone G (as_empty_cone X)))))
        sorry))

/-- The property of preserving terminal objects expressed in terms of `is_terminal`. -/
def is_terminal_obj_of_is_terminal {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) (X : C) [preserves_limit (functor.empty C) G] (l : is_terminal X) : is_terminal (functor.obj G X) :=
  coe_fn (is_limit_map_cone_empty_cone_equiv G X) (preserves_limit.preserves l)

/-- The property of reflecting terminal objects expressed in terms of `is_terminal`. -/
def is_terminal_of_is_terminal_obj {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) (X : C) [reflects_limit (functor.empty C) G] (l : is_terminal (functor.obj G X)) : is_terminal X :=
  reflects_limit.reflects (coe_fn (equiv.symm (is_limit_map_cone_empty_cone_equiv G X)) l)

/--
If `G` preserves the terminal object and `C` has a terminal object, then the image of the terminal
object is terminal.
-/
def is_limit_of_has_terminal_of_preserves_limit {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) [has_terminal C] [preserves_limit (functor.empty C) G] : is_terminal (functor.obj G (⊤_C)) :=
  is_terminal_obj_of_is_terminal G (⊤_C) terminal_is_terminal

/--
If `C` has a terminal object and `G` preserves terminal objects, then `D` has a terminal object
also.
Note this property is somewhat unique to (co)limits of the empty diagram: for general `J`, if `C`
has limits of shape `J` and `G` preserves them, then `D` does not necessarily have limits of shape
`J`.
-/
theorem has_terminal_of_has_terminal_of_preserves_limit {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) [has_terminal C] [preserves_limit (functor.empty C) G] : has_terminal D :=
  has_limits_of_shape.mk fun (F : discrete pempty ⥤ D) => has_limit_of_iso (iso.symm (functor.unique_from_empty F))

/--
If the terminal comparison map for `G` is an isomorphism, then `G` preserves terminal objects.
-/
def preserves_terminal.of_iso_comparison {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) [has_terminal C] [has_terminal D] [i : is_iso (terminal_comparison G)] : preserves_limit (functor.empty C) G :=
  preserves_limit_of_preserves_limit_cone terminal_is_terminal
    (coe_fn (equiv.symm (is_limit_map_cone_empty_cone_equiv G (⊤_C)))
      (is_limit.of_point_iso (limit.is_limit (functor.empty D))))

/-- If there is any isomorphism `G.obj ⊤ ⟶ ⊤`, then `G` preserves terminal objects. -/
def preserves_terminal_of_is_iso {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) [has_terminal C] [has_terminal D] (f : functor.obj G (⊤_C) ⟶ ⊤_D) [i : is_iso f] : preserves_limit (functor.empty C) G :=
  preserves_terminal.of_iso_comparison G

/-- If there is any isomorphism `G.obj ⊤ ≅ ⊤`, then `G` preserves terminal objects. -/
def preserves_terminal_of_iso {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) [has_terminal C] [has_terminal D] (f : functor.obj G (⊤_C) ≅ ⊤_D) : preserves_limit (functor.empty C) G :=
  preserves_terminal_of_is_iso G (iso.hom f)

/-- If `G` preserves terminal objects, then the terminal comparison map for `G` an isomorphism. -/
def preserves_terminal.iso {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) [has_terminal C] [has_terminal D] [preserves_limit (functor.empty C) G] : functor.obj G (⊤_C) ≅ ⊤_D :=
  is_limit.cone_point_unique_up_to_iso (is_limit_of_has_terminal_of_preserves_limit G) (limit.is_limit (functor.empty D))

@[simp] theorem preserves_terminal.iso_hom {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) [has_terminal C] [has_terminal D] [preserves_limit (functor.empty C) G] : iso.hom (preserves_terminal.iso G) = terminal_comparison G :=
  rfl

protected instance terminal_comparison.category_theory.is_iso {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) [has_terminal C] [has_terminal D] [preserves_limit (functor.empty C) G] : is_iso (terminal_comparison G) :=
  eq.mpr sorry (is_iso.of_iso (preserves_terminal.iso G))

