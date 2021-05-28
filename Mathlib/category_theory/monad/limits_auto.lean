/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.monad.adjunction
import Mathlib.category_theory.adjunction.limits
import Mathlib.category_theory.limits.preserves.shapes.terminal
import PostPort

universes u₁ v₁ u₂ 

namespace Mathlib

namespace category_theory


namespace monad


namespace forget_creates_limits


/-- (Impl) The natural transformation used to define the new cone -/
@[simp] theorem γ_app {C : Type u₁} [category C] {T : C ⥤ C} [monad T] {J : Type v₁} [small_category J] (D : J ⥤ algebra T) (j : J) : nat_trans.app (γ D) j = algebra.a (functor.obj D j) :=
  Eq.refl (nat_trans.app (γ D) j)

/-- (Impl) This new cone is used to construct the algebra structure -/
@[simp] theorem new_cone_X {C : Type u₁} [category C] {T : C ⥤ C} [monad T] {J : Type v₁} [small_category J] (D : J ⥤ algebra T) (c : limits.cone (D ⋙ forget T)) : limits.cone.X (new_cone D c) = functor.obj T (limits.cone.X c) :=
  Eq.refl (limits.cone.X (new_cone D c))

/-- The algebra structure which will be the apex of the new limit cone for `D`. -/
@[simp] theorem cone_point_A {C : Type u₁} [category C] {T : C ⥤ C} [monad T] {J : Type v₁} [small_category J] (D : J ⥤ algebra T) (c : limits.cone (D ⋙ forget T)) (t : limits.is_limit c) : algebra.A (cone_point D c t) = limits.cone.X c :=
  Eq.refl (algebra.A (cone_point D c t))

/-- (Impl) Construct the lifted cone in `algebra T` which will be limiting. -/
@[simp] theorem lifted_cone_X {C : Type u₁} [category C] {T : C ⥤ C} [monad T] {J : Type v₁} [small_category J] (D : J ⥤ algebra T) (c : limits.cone (D ⋙ forget T)) (t : limits.is_limit c) : limits.cone.X (lifted_cone D c t) = cone_point D c t :=
  Eq.refl (limits.cone.X (lifted_cone D c t))

/-- (Impl) Prove that the lifted cone is limiting. -/
def lifted_cone_is_limit {C : Type u₁} [category C] {T : C ⥤ C} [monad T] {J : Type v₁} [small_category J] (D : J ⥤ algebra T) (c : limits.cone (D ⋙ forget T)) (t : limits.is_limit c) : limits.is_limit (lifted_cone D c t) :=
  limits.is_limit.mk fun (s : limits.cone D) => algebra.hom.mk (limits.is_limit.lift t (functor.map_cone (forget T) s))

end forget_creates_limits


-- Theorem 5.6.5 from [Riehl][riehl2017]

/-- The forgetful functor from the Eilenberg-Moore category creates limits. -/
protected instance forget_creates_limits {C : Type u₁} [category C] {T : C ⥤ C} [monad T] : creates_limits (forget T) :=
  creates_limits.mk
    fun (J : Type v₁) (𝒥 : small_category J) =>
      creates_limits_of_shape.mk
        fun (D : J ⥤ algebra T) =>
          creates_limit_of_reflects_iso
            fun (c : limits.cone (D ⋙ forget T)) (t : limits.is_limit c) =>
              lifts_to_limit.mk
                (liftable_cone.mk sorry
                  (limits.cones.ext (iso.refl (limits.cone.X (functor.map_cone (forget T) sorry))) sorry))
                sorry

/-- `D ⋙ forget T` has a limit, then `D` has a limit. -/
theorem has_limit_of_comp_forget_has_limit {C : Type u₁} [category C] {T : C ⥤ C} [monad T] {J : Type v₁} [small_category J] (D : J ⥤ algebra T) [limits.has_limit (D ⋙ forget T)] : limits.has_limit D :=
  has_limit_of_created D (forget T)

namespace forget_creates_colimits


-- Let's hide the implementation details in a namespace

-- We have a diagram D of shape J in the category of algebras, and we assume that we are given a

-- colimit for its image D ⋙ forget T under the forgetful functor, say its apex is L.

-- We'll construct a colimiting coalgebra for D, whose carrier will also be L.

-- To do this, we must find a map TL ⟶ L. Since T preserves colimits, TL is also a colimit.

-- In particular, it is a colimit for the diagram `(D ⋙ forget T) ⋙ T`

-- so to construct a map TL ⟶ L it suffices to show that L is the apex of a cocone for this diagram.

-- In other words, we need a natural transformation from const L to `(D ⋙ forget T) ⋙ T`.

-- But we already know that L is the apex of a cocone for the diagram `D ⋙ forget T`, so it

-- suffices to give a natural transformation `((D ⋙ forget T) ⋙ T) ⟶ (D ⋙ forget T)`:

/--
(Impl)
The natural transformation given by the algebra structure maps, used to construct a cocone `c` with
apex `colimit (D ⋙ forget T)`.
 -/
@[simp] theorem γ_app {C : Type u₁} [category C] {T : C ⥤ C} [monad T] {J : Type v₁} [small_category J] {D : J ⥤ algebra T} (j : J) : nat_trans.app γ j = algebra.a (functor.obj D j) :=
  Eq.refl (nat_trans.app γ j)

/--
(Impl)
A cocone for the diagram `(D ⋙ forget T) ⋙ T` found by composing the natural transformation `γ`
with the colimiting cocone for `D ⋙ forget T`.
-/
@[simp] theorem new_cocone_X {C : Type u₁} [category C] {T : C ⥤ C} [monad T] {J : Type v₁} [small_category J] {D : J ⥤ algebra T} (c : limits.cocone (D ⋙ forget T)) : limits.cocone.X (new_cocone c) = limits.cocone.X c :=
  Eq.refl (limits.cocone.X (new_cocone c))

/--
(Impl)
Define the map `λ : TL ⟶ L`, which will serve as the structure of the coalgebra on `L`, and
we will show is the colimiting object. We use the cocone constructed by `c` and the fact that
`T` preserves colimits to produce this morphism.
-/
def lambda {C : Type u₁} [category C] {T : C ⥤ C} [monad T] {J : Type v₁} [small_category J] {D : J ⥤ algebra T} (c : limits.cocone (D ⋙ forget T)) (t : limits.is_colimit c) [limits.preserves_colimit (D ⋙ forget T) T] : limits.cocone.X (functor.map_cocone T c) ⟶ limits.cocone.X c :=
  limits.is_colimit.desc (limits.preserves_colimit.preserves t) (new_cocone c)

/-- (Impl) The key property defining the map `λ : TL ⟶ L`. -/
theorem commuting {C : Type u₁} [category C] {T : C ⥤ C} [monad T] {J : Type v₁} [small_category J] {D : J ⥤ algebra T} (c : limits.cocone (D ⋙ forget T)) (t : limits.is_colimit c) [limits.preserves_colimit (D ⋙ forget T) T] (j : J) : functor.map T (nat_trans.app (limits.cocone.ι c) j) ≫ lambda c t =
  algebra.a (functor.obj D j) ≫ nat_trans.app (limits.cocone.ι c) j :=
  limits.is_colimit.fac (limits.preserves_colimit.preserves t) (new_cocone c) j

/--
(Impl)
Construct the colimiting algebra from the map `λ : TL ⟶ L` given by `lambda`. We are required to
show it satisfies the two algebra laws, which follow from the algebra laws for the image of `D` and
our `commuting` lemma.
-/
@[simp] theorem cocone_point_A {C : Type u₁} [category C] {T : C ⥤ C} [monad T] {J : Type v₁} [small_category J] {D : J ⥤ algebra T} (c : limits.cocone (D ⋙ forget T)) (t : limits.is_colimit c) [limits.preserves_colimit (D ⋙ forget T) T] [limits.preserves_colimit ((D ⋙ forget T) ⋙ T) T] : algebra.A (cocone_point c t) = limits.cocone.X c :=
  Eq.refl (algebra.A (cocone_point c t))

/-- (Impl) Construct the lifted cocone in `algebra T` which will be colimiting. -/
@[simp] theorem lifted_cocone_X {C : Type u₁} [category C] {T : C ⥤ C} [monad T] {J : Type v₁} [small_category J] {D : J ⥤ algebra T} (c : limits.cocone (D ⋙ forget T)) (t : limits.is_colimit c) [limits.preserves_colimit (D ⋙ forget T) T] [limits.preserves_colimit ((D ⋙ forget T) ⋙ T) T] : limits.cocone.X (lifted_cocone c t) = cocone_point c t :=
  Eq.refl (limits.cocone.X (lifted_cocone c t))

/-- (Impl) Prove that the lifted cocone is colimiting. -/
@[simp] theorem lifted_cocone_is_colimit_desc_f {C : Type u₁} [category C] {T : C ⥤ C} [monad T] {J : Type v₁} [small_category J] {D : J ⥤ algebra T} (c : limits.cocone (D ⋙ forget T)) (t : limits.is_colimit c) [limits.preserves_colimit (D ⋙ forget T) T] [limits.preserves_colimit ((D ⋙ forget T) ⋙ T) T] (s : limits.cocone D) : algebra.hom.f (limits.is_colimit.desc (lifted_cocone_is_colimit c t) s) =
  limits.is_colimit.desc t (functor.map_cocone (forget T) s) :=
  Eq.refl (algebra.hom.f (limits.is_colimit.desc (lifted_cocone_is_colimit c t) s))

end forget_creates_colimits


-- TODO: the converse of this is true as well

/--
The forgetful functor from the Eilenberg-Moore category for a monad creates any colimit
which the monad itself preserves.
-/
protected instance forget_creates_colimit {C : Type u₁} [category C] {T : C ⥤ C} [monad T] {J : Type v₁} [small_category J] (D : J ⥤ algebra T) [limits.preserves_colimit (D ⋙ forget T) T] [limits.preserves_colimit ((D ⋙ forget T) ⋙ T) T] : creates_colimit D (forget T) :=
  creates_colimit_of_reflects_iso
    fun (c : limits.cocone (D ⋙ forget T)) (t : limits.is_colimit c) =>
      lifts_to_colimit.mk
        (liftable_cocone.mk
          (limits.cocone.mk (forget_creates_colimits.cocone_point c t)
            (nat_trans.mk fun (j : J) => algebra.hom.mk (nat_trans.app (limits.cocone.ι c) j)))
          (limits.cocones.ext
            (iso.refl
              (limits.cocone.X
                (functor.map_cocone (forget T)
                  (limits.cocone.mk (forget_creates_colimits.cocone_point c t)
                    (nat_trans.mk fun (j : J) => algebra.hom.mk (nat_trans.app (limits.cocone.ι c) j))))))
            sorry))
        (forget_creates_colimits.lifted_cocone_is_colimit c t)

protected instance forget_creates_colimits_of_shape {C : Type u₁} [category C] {T : C ⥤ C} [monad T] {J : Type v₁} [small_category J] [limits.preserves_colimits_of_shape J T] : creates_colimits_of_shape J (forget T) :=
  creates_colimits_of_shape.mk fun (K : J ⥤ algebra T) => monad.forget_creates_colimit K

protected instance forget_creates_colimits {C : Type u₁} [category C] {T : C ⥤ C} [monad T] [limits.preserves_colimits T] : creates_colimits (forget T) :=
  creates_colimits.mk fun (J : Type v₁) (𝒥₁ : small_category J) => monad.forget_creates_colimits_of_shape

/--
For `D : J ⥤ algebra T`, `D ⋙ forget T` has a colimit, then `D` has a colimit provided colimits
of shape `J` are preserved by `T`.
-/
theorem forget_creates_colimits_of_monad_preserves {C : Type u₁} [category C] {T : C ⥤ C} [monad T] {J : Type v₁} [small_category J] [limits.preserves_colimits_of_shape J T] (D : J ⥤ algebra T) [limits.has_colimit (D ⋙ forget T)] : limits.has_colimit D :=
  has_colimit_of_created D (forget T)

end monad


protected instance comp_comparison_forget_has_limit {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v₁} [small_category J] (F : J ⥤ D) (R : D ⥤ C) [monadic_right_adjoint R] [limits.has_limit (F ⋙ R)] : limits.has_limit ((F ⋙ monad.comparison R) ⋙ monad.forget (left_adjoint R ⋙ R)) :=
  limits.has_limit_of_iso (iso_whisker_left F (iso.symm (monad.comparison_forget R)))

protected instance comp_comparison_has_limit {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v₁} [small_category J] (F : J ⥤ D) (R : D ⥤ C) [monadic_right_adjoint R] [limits.has_limit (F ⋙ R)] : limits.has_limit (F ⋙ monad.comparison R) :=
  monad.has_limit_of_comp_forget_has_limit (F ⋙ monad.comparison R)

/-- Any monadic functor creates limits. -/
def monadic_creates_limits {C : Type u₁} [category C] {D : Type u₂} [category D] (R : D ⥤ C) [monadic_right_adjoint R] : creates_limits R :=
  creates_limits_of_nat_iso (monad.comparison_forget R)

/--
The forgetful functor from the Eilenberg-Moore category for a monad creates any colimit
which the monad itself preserves.
-/
def monadic_creates_colimit_of_preserves_colimit {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v₁} [small_category J] (R : D ⥤ C) (K : J ⥤ D) [monadic_right_adjoint R] [limits.preserves_colimit (K ⋙ R) (left_adjoint R ⋙ R)] [limits.preserves_colimit ((K ⋙ R) ⋙ left_adjoint R ⋙ R) (left_adjoint R ⋙ R)] : creates_colimit K R :=
  creates_colimit_of_nat_iso (monad.comparison_forget R)

/-- A monadic functor creates any colimits of shapes it preserves. -/
def monadic_creates_colimits_of_shape_of_preserves_colimits_of_shape {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v₁} [small_category J] (R : D ⥤ C) [monadic_right_adjoint R] [limits.preserves_colimits_of_shape J R] : creates_colimits_of_shape J R :=
  creates_colimits_of_shape_of_nat_iso (monad.comparison_forget R)

/-- A monadic functor creates colimits if it preserves colimits. -/
def monadic_creates_colimits_of_preserves_colimits {C : Type u₁} [category C] {D : Type u₂} [category D] (R : D ⥤ C) [monadic_right_adjoint R] [limits.preserves_colimits R] : creates_colimits R :=
  creates_colimits.mk
    fun (J : Type v₁) (𝒥₁ : small_category J) => monadic_creates_colimits_of_shape_of_preserves_colimits_of_shape R

theorem has_limit_of_reflective {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v₁} [small_category J] (F : J ⥤ D) (R : D ⥤ C) [limits.has_limit (F ⋙ R)] [reflective R] : limits.has_limit F :=
  has_limit_of_created F R

/-- If `C` has limits of shape `J` then any reflective subcategory has limits of shape `J`. -/
theorem has_limits_of_shape_of_reflective {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v₁} [small_category J] [limits.has_limits_of_shape J C] (R : D ⥤ C) [reflective R] : limits.has_limits_of_shape J D :=
  limits.has_limits_of_shape.mk fun (F : J ⥤ D) => has_limit_of_reflective F R

/-- If `C` has limits then any reflective subcategory has limits. -/
theorem has_limits_of_reflective {C : Type u₁} [category C] {D : Type u₂} [category D] (R : D ⥤ C) [limits.has_limits C] [reflective R] : limits.has_limits D :=
  limits.has_limits.mk fun (J : Type v₁) (𝒥₁ : small_category J) => has_limits_of_shape_of_reflective R

/--
The reflector always preserves terminal objects. Note this in general doesn't apply to any other
limit.
-/
def left_adjoint_preserves_terminal_of_reflective {C : Type u₁} [category C] {D : Type u₂} [category D] (R : D ⥤ C) [reflective R] [limits.has_terminal C] : limits.preserves_limits_of_shape (discrete pempty) (left_adjoint R) :=
  limits.preserves_limits_of_shape.mk
    fun (K : discrete pempty ⥤ C) =>
      let _inst : limits.has_terminal D := sorry;
      let _inst_3 : creates_limits R := monadic_creates_limits R;
      let _inst_6 : limits.preserves_limit (functor.empty D) R :=
        category_theory.preserves_limit_of_creates_limit_and_has_limit (functor.empty D) R;
      let _inst_7 : limits.preserves_limit (functor.empty C) (left_adjoint R) :=
        limits.preserves_terminal_of_iso (left_adjoint R)
          (functor.map_iso (left_adjoint R) (iso.symm (limits.preserves_terminal.iso R)) ≪≫
            as_iso (nat_trans.app (adjunction.counit (adjunction.of_right_adjoint R)) (⊤_D)));
      limits.preserves_limit_of_iso_diagram (left_adjoint R) (iso.symm (functor.unique_from_empty K))

