/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.comma
import Mathlib.PostPort

universes v u l u₁ u₂ v₁ v₂ 

namespace Mathlib

/-!
# The category of arrows

The category of arrows, with morphisms commutative squares.
We set this up as a specialization of the comma category `comma L R`,
where `L` and `R` are both the identity functor.

We also define the typeclass `has_lift`, representing a choice of a lift
of a commutative square (that is, a diagonal morphism making the two triangles commute).

## Tags

comma, arrow
-/

namespace category_theory


/-- The arrow category of `T` has as objects all morphisms in `T` and as morphisms commutative
     squares in `T`. -/
def arrow (T : Type u) [category T]  :=
  comma 𝟭 𝟭

-- Satisfying the inhabited linter

protected instance arrow.inhabited (T : Type u) [category T] [Inhabited T] : Inhabited (arrow T) :=
  { default := (fun (this : comma 𝟭 𝟭) => this) Inhabited.default }

namespace arrow


@[simp] theorem id_left {T : Type u} [category T] (f : arrow T) : comma_morphism.left 𝟙 = 𝟙 :=
  rfl

@[simp] theorem id_right {T : Type u} [category T] (f : arrow T) : comma_morphism.right 𝟙 = 𝟙 :=
  rfl

/-- An object in the arrow category is simply a morphism in `T`. -/
@[simp] theorem mk_left {T : Type u} [category T] {X : T} {Y : T} (f : X ⟶ Y) : comma.left (mk f) = X :=
  Eq.refl (comma.left (mk f))

/-- A morphism in the arrow category is a commutative square connecting two objects of the arrow
    category. -/
def hom_mk {T : Type u} [category T] {f : arrow T} {g : arrow T} {u : comma.left f ⟶ comma.left g} {v : comma.right f ⟶ comma.right g} (w : u ≫ comma.hom g = comma.hom f ≫ v) : f ⟶ g :=
  comma_morphism.mk

/-- We can also build a morphism in the arrow category out of any commutative square in `T`. -/
@[simp] theorem hom_mk'_right {T : Type u} [category T] {X : T} {Y : T} {f : X ⟶ Y} {P : T} {Q : T} {g : P ⟶ Q} {u : X ⟶ P} {v : Y ⟶ Q} (w : u ≫ g = f ≫ v) : comma_morphism.right (hom_mk' w) = v :=
  Eq.refl (comma_morphism.right (hom_mk' w))

@[simp] theorem w_assoc {T : Type u} [category T] {f : arrow T} {g : arrow T} (sq : f ⟶ g) {X' : autoParam T
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])} (f' : functor.obj 𝟭 (comma.right g) ⟶ X') : comma_morphism.left sq ≫ comma.hom g ≫ f' = comma.hom f ≫ comma_morphism.right sq ≫ f' := sorry

/-- A lift of a commutative square is a diagonal morphism making the two triangles commute. -/
structure lift_struct {T : Type u} [category T] {f : arrow T} {g : arrow T} (sq : f ⟶ g) 
where
  lift : comma.right f ⟶ comma.left g
  fac_left : comma.hom f ≫ lift = comma_morphism.left sq
  fac_right : lift ≫ comma.hom g = comma_morphism.right sq

protected instance lift_struct_inhabited {T : Type u} [category T] {X : T} : Inhabited (lift_struct 𝟙) :=
  { default := lift_struct.mk 𝟙 sorry sorry }

/-- `has_lift sq` says that there is some `lift_struct sq`, i.e., that it is possible to find a
    diagonal morphism making the two triangles commute. -/
class has_lift {T : Type u} [category T] {f : arrow T} {g : arrow T} (sq : f ⟶ g) 
  mk' ::
where (exists_lift : Nonempty (lift_struct sq))

theorem has_lift.mk {T : Type u} [category T] {f : arrow T} {g : arrow T} {sq : f ⟶ g} (s : lift_struct sq) : has_lift sq :=
  has_lift.mk' (Nonempty.intro s)

@[simp] theorem lift_struct.fac_right_assoc {T : Type u} [category T] {f : arrow T} {g : arrow T} {sq : f ⟶ g} (c : lift_struct sq) {X' : autoParam T
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])} (f' : functor.obj 𝟭 (comma.right g) ⟶ X') : lift_struct.lift c ≫ comma.hom g ≫ f' = comma_morphism.right sq ≫ f' := sorry

/-- Given `has_lift sq`, obtain a lift. -/
def has_lift.struct {T : Type u} [category T] {f : arrow T} {g : arrow T} (sq : f ⟶ g) [has_lift sq] : lift_struct sq :=
  Classical.choice has_lift.exists_lift

/-- If there is a lift of a commutative square `sq`, we can access it by saying `lift sq`. -/
def lift {T : Type u} [category T] {f : arrow T} {g : arrow T} (sq : f ⟶ g) [has_lift sq] : comma.right f ⟶ comma.left g :=
  lift_struct.lift (has_lift.struct sq)

theorem lift.fac_left {T : Type u} [category T] {f : arrow T} {g : arrow T} (sq : f ⟶ g) [has_lift sq] : comma.hom f ≫ lift sq = comma_morphism.left sq := sorry

theorem lift.fac_right {T : Type u} [category T] {f : arrow T} {g : arrow T} (sq : f ⟶ g) [has_lift sq] : lift sq ≫ comma.hom g = comma_morphism.right sq := sorry

@[simp] theorem lift_mk'_left {T : Type u} [category T] {X : T} {Y : T} {P : T} {Q : T} {f : X ⟶ Y} {g : P ⟶ Q} {u : X ⟶ P} {v : Y ⟶ Q} (h : u ≫ g = f ≫ v) [has_lift (hom_mk' h)] : f ≫ lift (hom_mk' h) = u := sorry

@[simp] theorem lift_mk'_right_assoc {T : Type u} [category T] {X : T} {Y : T} {P : T} {Q : T} {f : X ⟶ Y} {g : P ⟶ Q} {u : X ⟶ P} {v : Y ⟶ Q} (h : u ≫ g = f ≫ v) [has_lift (hom_mk' h)] {X' : autoParam T
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])} (f' : Q ⟶ X') : lift (hom_mk' h) ≫ g ≫ f' = v ≫ f' := sorry

protected instance subsingleton_lift_struct_of_epi {T : Type u} [category T] {f : arrow T} {g : arrow T} (sq : f ⟶ g) [epi (comma.hom f)] : subsingleton (lift_struct sq) :=
  subsingleton.intro
    fun (a b : lift_struct sq) =>
      lift_struct.ext a b
        (iff.mp (cancel_epi (comma.hom f))
          (eq.mpr
            (id
              (Eq.trans
                ((fun (a a_1 : functor.obj 𝟭 (comma.left f) ⟶ comma.left g) (e_1 : a = a_1)
                    (ᾰ ᾰ_1 : functor.obj 𝟭 (comma.left f) ⟶ comma.left g) (e_2 : ᾰ = ᾰ_1) => congr (congr_arg Eq e_1) e_2)
                  (comma.hom f ≫ lift_struct.lift a) (comma_morphism.left sq) (lift_struct.fac_left a)
                  (comma.hom f ≫ lift_struct.lift b) (comma_morphism.left sq) (lift_struct.fac_left b))
                (propext (eq_self_iff_true (comma_morphism.left sq)))))
            trivial))

protected instance subsingleton_lift_struct_of_mono {T : Type u} [category T] {f : arrow T} {g : arrow T} (sq : f ⟶ g) [mono (comma.hom g)] : subsingleton (lift_struct sq) :=
  subsingleton.intro
    fun (a b : lift_struct sq) =>
      lift_struct.ext a b
        (iff.mp (cancel_mono (comma.hom g))
          (eq.mpr
            (id
              (Eq.trans
                ((fun (a a_1 : comma.right f ⟶ functor.obj 𝟭 (comma.right g)) (e_1 : a = a_1)
                    (ᾰ ᾰ_1 : comma.right f ⟶ functor.obj 𝟭 (comma.right g)) (e_2 : ᾰ = ᾰ_1) =>
                    congr (congr_arg Eq e_1) e_2)
                  (lift_struct.lift a ≫ comma.hom g) (comma_morphism.right sq) (lift_struct.fac_right a)
                  (lift_struct.lift b ≫ comma.hom g) (comma_morphism.right sq) (lift_struct.fac_right b))
                (propext (eq_self_iff_true (comma_morphism.right sq)))))
            trivial))

end arrow


namespace functor


/-- A functor `C ⥤ D` induces a functor between the corresponding arrow categories. -/
@[simp] theorem map_arrow_map_right {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) (a : arrow C) (b : arrow C) (f : a ⟶ b) : comma_morphism.right (map (map_arrow F) f) = map F (comma_morphism.right f) :=
  Eq.refl (comma_morphism.right (map (map_arrow F) f))

