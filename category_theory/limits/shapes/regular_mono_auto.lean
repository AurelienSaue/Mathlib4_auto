/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.limits.preserves.basic
import Mathlib.category_theory.limits.shapes.equalizers
import Mathlib.category_theory.limits.shapes.strong_epi
import Mathlib.category_theory.limits.shapes.pullbacks
import PostPort

universes v₁ u₁ l 

namespace Mathlib

/-!
# Definitions and basic properties of regular monomorphisms and epimorphisms.

A regular monomorphism is a morphism that is the equalizer of some parallel pair.

We give the constructions
* `split_mono → regular_mono` and
* `regular_mono → mono`
as well as the dual constructions for regular epimorphisms. Additionally, we give the
construction
* `regular_epi ⟶ strong_epi`.

-/

namespace category_theory


/-- A regular monomorphism is a morphism which is the equalizer of some parallel pair. -/
class regular_mono {C : Type u₁} [category C] {X : C} {Y : C} (f : X ⟶ Y) 
where
  Z : C
  left : Y ⟶ Z
  right : Y ⟶ Z
  w : f ≫ left = f ≫ right
  is_limit : limits.is_limit (limits.fork.of_ι f w)

theorem regular_mono.w_assoc {C : Type u₁} [category C] {X : C} {Y : C} {f : X ⟶ Y} [c : regular_mono f] {X' : C} (f' : regular_mono.Z f ⟶ X') : f ≫ regular_mono.left ≫ f' = f ≫ regular_mono.right ≫ f' := sorry

/-- Every regular monomorphism is a monomorphism. -/
protected instance regular_mono.mono {C : Type u₁} [category C] {X : C} {Y : C} (f : X ⟶ Y) [regular_mono f] : mono f :=
  limits.mono_of_is_limit_parallel_pair regular_mono.is_limit

protected instance equalizer_regular {C : Type u₁} [category C] {X : C} {Y : C} (g : X ⟶ Y) (h : X ⟶ Y) [limits.has_limit (limits.parallel_pair g h)] : regular_mono (limits.equalizer.ι g h) :=
  regular_mono.mk Y g h (limits.equalizer.condition g h)
    (limits.fork.is_limit.mk (limits.fork.of_ι (limits.equalizer.ι g h) (limits.equalizer.condition g h))
      (fun (s : limits.fork g h) => limits.limit.lift (limits.parallel_pair g h) s) sorry sorry)

/-- Every split monomorphism is a regular monomorphism. -/
protected instance regular_mono.of_split_mono {C : Type u₁} [category C] {X : C} {Y : C} (f : X ⟶ Y) [split_mono f] : regular_mono f :=
  regular_mono.mk Y 𝟙 (retraction f ≫ f) (limits.cone_of_split_mono._proof_1 f) (limits.split_mono_equalizes f)

/-- If `f` is a regular mono, then any map `k : W ⟶ Y` equalizing `regular_mono.left` and
    `regular_mono.right` induces a morphism `l : W ⟶ X` such that `l ≫ f = k`. -/
def regular_mono.lift' {C : Type u₁} [category C] {X : C} {Y : C} {W : C} (f : X ⟶ Y) [regular_mono f] (k : W ⟶ Y) (h : k ≫ regular_mono.left = k ≫ regular_mono.right) : Subtype fun (l : W ⟶ X) => l ≫ f = k :=
  limits.fork.is_limit.lift' regular_mono.is_limit k h

/--
The second leg of a pullback cone is a regular monomorphism if the right component is too.

See also `pullback.snd_of_mono` for the basic monomorphism version, and
`regular_of_is_pullback_fst_of_regular` for the flipped version.
-/
def regular_of_is_pullback_snd_of_regular {C : Type u₁} [category C] {P : C} {Q : C} {R : C} {S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S} [hr : regular_mono h] (comm : f ≫ h = g ≫ k) (t : limits.is_limit (limits.pullback_cone.mk f g comm)) : regular_mono g := sorry

/--
The first leg of a pullback cone is a regular monomorphism if the left component is too.

See also `pullback.fst_of_mono` for the basic monomorphism version, and
`regular_of_is_pullback_snd_of_regular` for the flipped version.
-/
def regular_of_is_pullback_fst_of_regular {C : Type u₁} [category C] {P : C} {Q : C} {R : C} {S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S} [hr : regular_mono k] (comm : f ≫ h = g ≫ k) (t : limits.is_limit (limits.pullback_cone.mk f g comm)) : regular_mono f :=
  regular_of_is_pullback_snd_of_regular sorry (limits.pullback_cone.flip_is_limit t)

/-- A regular monomorphism is an isomorphism if it is an epimorphism. -/
def is_iso_of_regular_mono_of_epi {C : Type u₁} [category C] {X : C} {Y : C} (f : X ⟶ Y) [regular_mono f] [e : epi f] : is_iso f :=
  limits.is_iso_limit_cone_parallel_pair_of_epi regular_mono.is_limit

/-- A regular epimorphism is a morphism which is the coequalizer of some parallel pair. -/
class regular_epi {C : Type u₁} [category C] {X : C} {Y : C} (f : X ⟶ Y) 
where
  W : C
  left : W ⟶ X
  right : W ⟶ X
  w : left ≫ f = right ≫ f
  is_colimit : limits.is_colimit (limits.cofork.of_π f w)

theorem regular_epi.w_assoc {C : Type u₁} [category C] {X : C} {Y : C} {f : X ⟶ Y} [c : regular_epi f] {X' : C} (f' : Y ⟶ X') : regular_epi.left ≫ f ≫ f' = regular_epi.right ≫ f ≫ f' := sorry

/-- Every regular epimorphism is an epimorphism. -/
protected instance regular_epi.epi {C : Type u₁} [category C] {X : C} {Y : C} (f : X ⟶ Y) [regular_epi f] : epi f :=
  limits.epi_of_is_colimit_parallel_pair regular_epi.is_colimit

protected instance coequalizer_regular {C : Type u₁} [category C] {X : C} {Y : C} (g : X ⟶ Y) (h : X ⟶ Y) [limits.has_colimit (limits.parallel_pair g h)] : regular_epi (limits.coequalizer.π g h) :=
  regular_epi.mk X g h (limits.coequalizer.condition g h)
    (limits.cofork.is_colimit.mk (limits.cofork.of_π (limits.coequalizer.π g h) (limits.coequalizer.condition g h))
      (fun (s : limits.cofork g h) => limits.colimit.desc (limits.parallel_pair g h) s) sorry sorry)

/-- Every split epimorphism is a regular epimorphism. -/
protected instance regular_epi.of_split_epi {C : Type u₁} [category C] {X : C} {Y : C} (f : X ⟶ Y) [split_epi f] : regular_epi f :=
  regular_epi.mk X 𝟙 (f ≫ section_ f) (limits.cocone_of_split_epi._proof_1 f) (limits.split_epi_coequalizes f)

/-- If `f` is a regular epi, then every morphism `k : X ⟶ W` coequalizing `regular_epi.left` and
    `regular_epi.right` induces `l : Y ⟶ W` such that `f ≫ l = k`. -/
def regular_epi.desc' {C : Type u₁} [category C] {X : C} {Y : C} {W : C} (f : X ⟶ Y) [regular_epi f] (k : X ⟶ W) (h : regular_epi.left ≫ k = regular_epi.right ≫ k) : Subtype fun (l : Y ⟶ W) => f ≫ l = k :=
  limits.cofork.is_colimit.desc' regular_epi.is_colimit k h

/--
The second leg of a pushout cocone is a regular epimorphism if the right component is too.

See also `pushout.snd_of_epi` for the basic epimorphism version, and
`regular_of_is_pushout_fst_of_regular` for the flipped version.
-/
def regular_of_is_pushout_snd_of_regular {C : Type u₁} [category C] {P : C} {Q : C} {R : C} {S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S} [gr : regular_epi g] (comm : f ≫ h = g ≫ k) (t : limits.is_colimit (limits.pushout_cocone.mk h k comm)) : regular_epi h := sorry

/--
The first leg of a pushout cocone is a regular epimorphism if the left component is too.

See also `pushout.fst_of_epi` for the basic epimorphism version, and
`regular_of_is_pushout_snd_of_regular` for the flipped version.
-/
def regular_of_is_pushout_fst_of_regular {C : Type u₁} [category C] {P : C} {Q : C} {R : C} {S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S} [fr : regular_epi f] (comm : f ≫ h = g ≫ k) (t : limits.is_colimit (limits.pushout_cocone.mk h k comm)) : regular_epi k :=
  regular_of_is_pushout_snd_of_regular sorry (limits.pushout_cocone.flip_is_colimit t)

/-- A regular epimorphism is an isomorphism if it is a monomorphism. -/
def is_iso_of_regular_epi_of_mono {C : Type u₁} [category C] {X : C} {Y : C} (f : X ⟶ Y) [regular_epi f] [m : mono f] : is_iso f :=
  limits.is_iso_limit_cocone_parallel_pair_of_epi regular_epi.is_colimit

protected instance strong_epi_of_regular_epi {C : Type u₁} [category C] {X : C} {Y : C} (f : X ⟶ Y) [regular_epi f] : strong_epi f := sorry

