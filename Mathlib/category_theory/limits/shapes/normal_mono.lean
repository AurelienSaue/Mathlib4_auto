/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.limits.shapes.regular_mono
import Mathlib.category_theory.limits.shapes.kernels
import Mathlib.PostPort

universes v₁ u₁ l u₂ 

namespace Mathlib

/-!
# Definitions and basic properties of normal monomorphisms and epimorphisms.

A normal monomorphism is a morphism that is the kernel of some other morphism.

We give the construction `normal_mono → regular_mono` (`category_theory.normal_mono.regular_mono`)
as well as the dual construction for normal epimorphisms. We show equivalences reflect normal
monomorphisms (`category_theory.equivalence_reflects_normal_mono`), and that the pullback of a
normal monomorphism is normal (`category_theory.normal_of_is_pullback_snd_of_normal`).
-/

namespace category_theory


/-- A normal monomorphism is a morphism which is the kernel of some morphism. -/
class normal_mono {C : Type u₁} [category C] {X : C} {Y : C} [limits.has_zero_morphisms C] (f : X ⟶ Y) 
where
  Z : C
  g : Y ⟶ Z
  w : f ≫ g = 0
  is_limit : limits.is_limit (limits.kernel_fork.of_ι f w)

/-- If `F` is an equivalence and `F.map f` is a normal mono, then `f` is a normal mono. -/
def equivalence_reflects_normal_mono {C : Type u₁} [category C] [limits.has_zero_morphisms C] {D : Type u₂} [category D] [limits.has_zero_morphisms D] (F : C ⥤ D) [is_equivalence F] {X : C} {Y : C} {f : X ⟶ Y} (hf : normal_mono (functor.map F f)) : normal_mono f :=
  normal_mono.mk (functor.obj_preimage F (normal_mono.Z (functor.map F f)))
    (full.preimage (normal_mono.g ≫ iso.inv (functor.obj_obj_preimage_iso F (normal_mono.Z (functor.map F f))))) sorry
    (limits.reflects_limit.reflects
      (coe_fn (limits.is_limit.of_cone_equiv (limits.cones.postcompose_equivalence (limits.comp_nat_iso F)))
        (limits.is_limit.of_iso_limit
          (limits.is_limit.of_iso_limit
            (limits.is_kernel.of_comp_iso normal_mono.g
              (functor.map F
                (full.preimage
                  (normal_mono.g ≫ iso.inv (functor.obj_obj_preimage_iso F (normal_mono.Z (functor.map F f))))))
              (functor.obj_obj_preimage_iso F (normal_mono.Z (functor.map F f))) sorry normal_mono.is_limit)
            (limits.of_ι_congr sorry))
          (iso.symm
            (limits.iso_of_ι
              (functor.obj (equivalence.functor (limits.cones.postcompose_equivalence (limits.comp_nat_iso F)))
                (functor.map_cone F (limits.kernel_fork.of_ι f sorry))))))))

/-- Every normal monomorphism is a regular monomorphism. -/
protected instance normal_mono.regular_mono {C : Type u₁} [category C] {X : C} {Y : C} [limits.has_zero_morphisms C] (f : X ⟶ Y) [I : normal_mono f] : regular_mono f :=
  regular_mono.mk (normal_mono.Z f) normal_mono.g 0 sorry normal_mono.is_limit

/-- If `f` is a normal mono, then any map `k : W ⟶ Y` such that `k ≫ normal_mono.g = 0` induces
    a morphism `l : W ⟶ X` such that `l ≫ f = k`. -/
def normal_mono.lift' {C : Type u₁} [category C] {X : C} {Y : C} [limits.has_zero_morphisms C] {W : C} (f : X ⟶ Y) [normal_mono f] (k : W ⟶ Y) (h : k ≫ normal_mono.g = 0) : Subtype fun (l : W ⟶ X) => l ≫ f = k :=
  limits.kernel_fork.is_limit.lift' normal_mono.is_limit k h

/--
The second leg of a pullback cone is a normal monomorphism if the right component is too.

See also `pullback.snd_of_mono` for the basic monomorphism version, and
`normal_of_is_pullback_fst_of_normal` for the flipped version.
-/
def normal_of_is_pullback_snd_of_normal {C : Type u₁} [category C] [limits.has_zero_morphisms C] {P : C} {Q : C} {R : C} {S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S} [hn : normal_mono h] (comm : f ≫ h = g ≫ k) (t : limits.is_limit (limits.pullback_cone.mk f g comm)) : normal_mono g :=
  normal_mono.mk (normal_mono.Z h) (k ≫ normal_mono.g) sorry
    (let gr : regular_mono g := regular_of_is_pullback_snd_of_regular comm t;
    eq.mpr sorry regular_mono.is_limit)

/--
The first leg of a pullback cone is a normal monomorphism if the left component is too.

See also `pullback.fst_of_mono` for the basic monomorphism version, and
`normal_of_is_pullback_snd_of_normal` for the flipped version.
-/
def normal_of_is_pullback_fst_of_normal {C : Type u₁} [category C] [limits.has_zero_morphisms C] {P : C} {Q : C} {R : C} {S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S} [hn : normal_mono k] (comm : f ≫ h = g ≫ k) (t : limits.is_limit (limits.pullback_cone.mk f g comm)) : normal_mono f :=
  normal_of_is_pullback_snd_of_normal sorry (limits.pullback_cone.flip_is_limit t)

/-- A normal epimorphism is a morphism which is the cokernel of some morphism. -/
class normal_epi {C : Type u₁} [category C] {X : C} {Y : C} [limits.has_zero_morphisms C] (f : X ⟶ Y) 
where
  W : C
  g : W ⟶ X
  w : g ≫ f = 0
  is_colimit : limits.is_colimit (limits.cokernel_cofork.of_π f w)

/-- If `F` is an equivalence and `F.map f` is a normal epi, then `f` is a normal epi. -/
def equivalence_reflects_normal_epi {C : Type u₁} [category C] [limits.has_zero_morphisms C] {D : Type u₂} [category D] [limits.has_zero_morphisms D] (F : C ⥤ D) [is_equivalence F] {X : C} {Y : C} {f : X ⟶ Y} (hf : normal_epi (functor.map F f)) : normal_epi f := sorry

/-- Every normal epimorphism is a regular epimorphism. -/
protected instance normal_epi.regular_epi {C : Type u₁} [category C] {X : C} {Y : C} [limits.has_zero_morphisms C] (f : X ⟶ Y) [I : normal_epi f] : regular_epi f :=
  regular_epi.mk (normal_epi.W f) normal_epi.g 0 sorry normal_epi.is_colimit

/-- If `f` is a normal epi, then every morphism `k : X ⟶ W` satisfying `normal_epi.g ≫ k = 0`
    induces `l : Y ⟶ W` such that `f ≫ l = k`. -/
def normal_epi.desc' {C : Type u₁} [category C] {X : C} {Y : C} [limits.has_zero_morphisms C] {W : C} (f : X ⟶ Y) [normal_epi f] (k : X ⟶ W) (h : normal_epi.g ≫ k = 0) : Subtype fun (l : Y ⟶ W) => f ≫ l = k :=
  limits.cokernel_cofork.is_colimit.desc' normal_epi.is_colimit k h

/--
The second leg of a pushout cocone is a normal epimorphism if the right component is too.

See also `pushout.snd_of_epi` for the basic epimorphism version, and
`normal_of_is_pushout_fst_of_normal` for the flipped version.
-/
def normal_of_is_pushout_snd_of_normal {C : Type u₁} [category C] [limits.has_zero_morphisms C] {P : C} {Q : C} {R : C} {S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S} [gn : normal_epi g] (comm : f ≫ h = g ≫ k) (t : limits.is_colimit (limits.pushout_cocone.mk h k comm)) : normal_epi h :=
  normal_epi.mk (normal_epi.W g) (normal_epi.g ≫ f) sorry
    (let hn : regular_epi h := regular_of_is_pushout_snd_of_regular comm t;
    eq.mpr sorry regular_epi.is_colimit)

/--
The first leg of a pushout cocone is a normal epimorphism if the left component is too.

See also `pushout.fst_of_epi` for the basic epimorphism version, and
`normal_of_is_pushout_snd_of_normal` for the flipped version.
-/
def normal_of_is_pushout_fst_of_normal {C : Type u₁} [category C] [limits.has_zero_morphisms C] {P : C} {Q : C} {R : C} {S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S} [hn : normal_epi f] (comm : f ≫ h = g ≫ k) (t : limits.is_colimit (limits.pushout_cocone.mk h k comm)) : normal_epi k :=
  normal_of_is_pushout_snd_of_normal sorry (limits.pushout_cocone.flip_is_colimit t)

