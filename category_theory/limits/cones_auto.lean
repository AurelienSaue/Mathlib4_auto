/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison, Floris van Doorn
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.const
import Mathlib.category_theory.discrete_category
import Mathlib.category_theory.yoneda
import Mathlib.category_theory.reflects_isomorphisms
import PostPort

universes v u l u' 

namespace Mathlib

namespace category_theory


namespace functor


/--
`F.cones` is the functor assigning to an object `X` the type of
natural transformations from the constant functor with value `X` to `F`.
An object representing this functor is a limit of `F`.
-/
def cones {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) : Cᵒᵖ ⥤ Type v :=
  functor.op (const J) ⋙ obj yoneda F

/--
`F.cocones` is the functor assigning to an object `X` the type of
natural transformations from `F` to the constant functor with value `X`.
An object corepresenting this functor is a colimit of `F`.
-/
@[simp] theorem cocones_obj {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) (X : C) : obj (cocones F) X = (F ⟶ obj (const J) X) :=
  Eq.refl (F ⟶ obj (const J) X)

end functor


/--
Functorially associated to each functor `J ⥤ C`, we have the `C`-presheaf consisting of
cones with a given cone point.
-/
@[simp] theorem cones_map (J : Type v) [small_category J] (C : Type u) [category C] (F : J ⥤ C) (G : J ⥤ C) (f : F ⟶ G) : functor.map (cones J C) f = whisker_left (functor.op (functor.const J)) (functor.map yoneda f) :=
  Eq.refl (functor.map (cones J C) f)

/--
Contravariantly associated to each functor `J ⥤ C`, we have the `C`-copresheaf consisting of
cocones with a given cocone point.
-/
@[simp] theorem cocones_obj (J : Type v) [small_category J] (C : Type u) [category C] (F : J ⥤ Cᵒᵖ) : functor.obj (cocones J C) F = functor.cocones (opposite.unop F) :=
  Eq.refl (functor.obj (cocones J C) F)

namespace limits


/--
A `c : cone F` is:
* an object `c.X` and
* a natural transformation `c.π : c.X ⟶ F` from the constant `c.X` functor to `F`.

`cone F` is equivalent, via `cone.equiv` below, to `Σ X, F.cones.obj X`.
-/
structure cone {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) 
where
  X : C
  π : functor.obj (functor.const J) X ⟶ F

protected instance inhabited_cone {C : Type u} [category C] (F : discrete PUnit ⥤ C) : Inhabited (cone F) :=
  { default := cone.mk (functor.obj F PUnit.unit) (nat_trans.mk fun (X : discrete PUnit) => sorry) }

@[simp] theorem cone.w {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} (c : cone F) {j : J} {j' : J} (f : j ⟶ j') : nat_trans.app (cone.π c) j ≫ functor.map F f = nat_trans.app (cone.π c) j' := sorry

/--
A `c : cocone F` is
* an object `c.X` and
* a natural transformation `c.ι : F ⟶ c.X` from `F` to the constant `c.X` functor.

`cocone F` is equivalent, via `cone.equiv` below, to `Σ X, F.cocones.obj X`.
-/
structure cocone {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) 
where
  X : C
  ι : F ⟶ functor.obj (functor.const J) X

protected instance inhabited_cocone {C : Type u} [category C] (F : discrete PUnit ⥤ C) : Inhabited (cocone F) :=
  { default := cocone.mk (functor.obj F PUnit.unit) (nat_trans.mk fun (X : discrete PUnit) => sorry) }

@[simp] theorem cocone.w_assoc {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} (c : cocone F) {j : J} {j' : J} (f : j ⟶ j') {X' : C} (f' : functor.obj (functor.obj (functor.const J) (cocone.X c)) j' ⟶ X') : functor.map F f ≫ nat_trans.app (cocone.ι c) j' ≫ f' = nat_trans.app (cocone.ι c) j ≫ f' := sorry

namespace cone


/-- The isomorphism between a cone on `F` and an element of the functor `F.cones`. -/
def equiv {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) : cone F ≅ sigma fun (X : Cᵒᵖ) => functor.obj (functor.cones F) X :=
  iso.mk (fun (c : cone F) => sigma.mk (opposite.op (X c)) (π c))
    fun (c : sigma fun (X : Cᵒᵖ) => functor.obj (functor.cones F) X) => mk (opposite.unop (sigma.fst c)) (sigma.snd c)

/-- A map to the vertex of a cone naturally induces a cone by composition. -/
@[simp] def extensions {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} (c : cone F) : functor.obj yoneda (X c) ⟶ functor.cones F :=
  nat_trans.mk fun (X : Cᵒᵖ) (f : functor.obj (functor.obj yoneda (X c)) X) => functor.map (functor.const J) f ≫ π c

/-- A map to the vertex of a cone induces a cone by composition. -/
@[simp] def extend {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} (c : cone F) {X : C} (f : X ⟶ X c) : cone F :=
  mk X (nat_trans.app (extensions c) (opposite.op X) f)

@[simp] theorem extend_π {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} (c : cone F) {X : Cᵒᵖ} (f : opposite.unop X ⟶ X c) : π (extend c f) = nat_trans.app (extensions c) X f :=
  rfl

/-- Whisker a cone by precomposition of a functor. -/
def whisker {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {K : Type v} [small_category K] (E : K ⥤ J) (c : cone F) : cone (E ⋙ F) :=
  mk (X c) (whisker_left E (π c))

end cone


namespace cocone


/-- The isomorphism between a cocone on `F` and an element of the functor `F.cocones`. -/
def equiv {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) : cocone F ≅ sigma fun (X : C) => functor.obj (functor.cocones F) X :=
  iso.mk (fun (c : cocone F) => sigma.mk (X c) (ι c))
    fun (c : sigma fun (X : C) => functor.obj (functor.cocones F) X) => mk (sigma.fst c) (sigma.snd c)

/-- A map from the vertex of a cocone naturally induces a cocone by composition. -/
@[simp] def extensions {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} (c : cocone F) : functor.obj coyoneda (opposite.op (X c)) ⟶ functor.cocones F :=
  nat_trans.mk
    fun (X : C) (f : functor.obj (functor.obj coyoneda (opposite.op (X c))) X) => ι c ≫ functor.map (functor.const J) f

/-- A map from the vertex of a cocone induces a cocone by composition. -/
@[simp] def extend {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} (c : cocone F) {X : C} (f : X c ⟶ X) : cocone F :=
  mk X (nat_trans.app (extensions c) X f)

@[simp] theorem extend_ι {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} (c : cocone F) {X : C} (f : X c ⟶ X) : ι (extend c f) = nat_trans.app (extensions c) X f :=
  rfl

/--
Whisker a cocone by precomposition of a functor. See `whiskering` for a functorial
version.
-/
@[simp] theorem whisker_ι {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {K : Type v} [small_category K] (E : K ⥤ J) (c : cocone F) : ι (whisker E c) = whisker_left E (ι c) :=
  Eq.refl (ι (whisker E c))

end cocone


/-- A cone morphism between two cones for the same diagram is a morphism of the cone points which
commutes with the cone legs. -/
structure cone_morphism {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} (A : cone F) (B : cone F) 
where
  hom : cone.X A ⟶ cone.X B
  w' : autoParam (∀ (j : J), hom ≫ nat_trans.app (cone.π B) j = nat_trans.app (cone.π A) j)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

@[simp] theorem cone_morphism.w {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {A : cone F} {B : cone F} (c : cone_morphism A B) (j : J) : cone_morphism.hom c ≫ nat_trans.app (cone.π B) j = nat_trans.app (cone.π A) j := sorry

@[simp] theorem cone_morphism.w_assoc {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {A : cone F} {B : cone F} (c : cone_morphism A B) (j : J) {X' : C} (f' : functor.obj F j ⟶ X') : cone_morphism.hom c ≫ nat_trans.app (cone.π B) j ≫ f' = nat_trans.app (cone.π A) j ≫ f' := sorry

protected instance inhabited_cone_morphism {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} (A : cone F) : Inhabited (cone_morphism A A) :=
  { default := cone_morphism.mk 𝟙 }

/-- The category of cones on a given diagram. -/
protected instance cone.category {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} : category (cone F) :=
  category.mk

namespace cones


/-- To give an isomorphism between cones, it suffices to give an
  isomorphism between their vertices which commutes with the cone
  maps. -/
def ext {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {c : cone F} {c' : cone F} (φ : cone.X c ≅ cone.X c') (w : ∀ (j : J), nat_trans.app (cone.π c) j = iso.hom φ ≫ nat_trans.app (cone.π c') j) : c ≅ c' :=
  iso.mk (cone_morphism.mk (iso.hom φ)) (cone_morphism.mk (iso.inv φ))

/--
Given a cone morphism whose object part is an isomorphism, produce an
isomorphism of cones.
-/
def cone_iso_of_hom_iso {J : Type v} [small_category J] {C : Type u} [category C] {K : J ⥤ C} {c : cone K} {d : cone K} (f : c ⟶ d) [i : is_iso (cone_morphism.hom f)] : is_iso f :=
  is_iso.mk (cone_morphism.mk (inv (cone_morphism.hom f)))

/--
Functorially postcompose a cone for `F` by a natural transformation `F ⟶ G` to give a cone for `G`.
-/
@[simp] theorem postcompose_map_hom {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {G : J ⥤ C} (α : F ⟶ G) (c₁ : cone F) (c₂ : cone F) (f : c₁ ⟶ c₂) : cone_morphism.hom (functor.map (postcompose α) f) = cone_morphism.hom f :=
  Eq.refl (cone_morphism.hom (functor.map (postcompose α) f))

/-- Postcomposing a cone by the composite natural transformation `α ≫ β` is the same as
postcomposing by `α` and then by `β`. -/
def postcompose_comp {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {G : J ⥤ C} {H : J ⥤ C} (α : F ⟶ G) (β : G ⟶ H) : postcompose (α ≫ β) ≅ postcompose α ⋙ postcompose β :=
  nat_iso.of_components (fun (s : cone F) => ext (iso.refl (cone.X (functor.obj (postcompose (α ≫ β)) s))) sorry) sorry

/-- Postcomposing by the identity does not change the cone up to isomorphism. -/
def postcompose_id {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} : postcompose 𝟙 ≅ 𝟭 :=
  nat_iso.of_components (fun (s : cone F) => ext (iso.refl (cone.X (functor.obj (postcompose 𝟙) s))) sorry) sorry

/--
If `F` and `G` are naturally isomorphic functors, then they have equivalent categories of
cones.
-/
@[simp] theorem postcompose_equivalence_unit_iso {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {G : J ⥤ C} (α : F ≅ G) : equivalence.unit_iso (postcompose_equivalence α) =
  nat_iso.of_components
    (fun (s : cone F) => ext (iso.refl (cone.X (functor.obj 𝟭 s))) (postcompose_equivalence._proof_1 α s))
    (postcompose_equivalence._proof_2 α) :=
  Eq.refl (equivalence.unit_iso (postcompose_equivalence α))

/--
Whiskering on the left by `E : K ⥤ J` gives a functor from `cone F` to `cone (E ⋙ F)`.
-/
@[simp] theorem whiskering_obj {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {K : Type v} [small_category K] (E : K ⥤ J) (c : cone F) : functor.obj (whiskering E) c = cone.whisker E c :=
  Eq.refl (functor.obj (whiskering E) c)

/--
Whiskering by an equivalence gives an equivalence between categories of cones.
-/
@[simp] theorem whiskering_equivalence_inverse {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {K : Type v} [small_category K] (e : K ≌ J) : equivalence.inverse (whiskering_equivalence e) =
  whiskering (equivalence.inverse e) ⋙
    postcompose
      (iso.inv (functor.associator (equivalence.inverse e) (equivalence.functor e) F) ≫
        whisker_right (iso.hom (equivalence.counit_iso e)) F ≫ iso.hom (functor.left_unitor F)) :=
  Eq.refl (equivalence.inverse (whiskering_equivalence e))

/--
The categories of cones over `F` and `G` are equivalent if `F` and `G` are naturally isomorphic
(possibly after changing the indexing category by an equivalence).
-/
def equivalence_of_reindexing {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {K : Type v} [small_category K] {G : K ⥤ C} (e : K ≌ J) (α : equivalence.functor e ⋙ F ≅ G) : cone F ≌ cone G :=
  equivalence.trans (whiskering_equivalence e) (postcompose_equivalence α)

/-- Forget the cone structure and obtain just the cone point. -/
def forget {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) : cone F ⥤ C :=
  functor.mk (fun (t : cone F) => cone.X t) fun (s t : cone F) (f : s ⟶ t) => cone_morphism.hom f

/-- A functor `G : C ⥤ D` sends cones over `F` to cones over `F ⋙ G` functorially. -/
@[simp] theorem functoriality_obj_π_app {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) {D : Type u'} [category D] (G : C ⥤ D) (A : cone F) (j : J) : nat_trans.app (cone.π (functor.obj (functoriality F G) A)) j = functor.map G (nat_trans.app (cone.π A) j) :=
  Eq.refl (nat_trans.app (cone.π (functor.obj (functoriality F G) A)) j)

protected instance functoriality_full {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) {D : Type u'} [category D] (G : C ⥤ D) [full G] [faithful G] : full (functoriality F G) :=
  full.mk
    fun (X Y : cone F) (t : functor.obj (functoriality F G) X ⟶ functor.obj (functoriality F G) Y) =>
      cone_morphism.mk (functor.preimage G (cone_morphism.hom t))

protected instance functoriality_faithful {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) {D : Type u'} [category D] (G : C ⥤ D) [faithful G] : faithful (functoriality F G) :=
  faithful.mk

/--
If `e : C ≌ D` is an equivalence of categories, then `functoriality F e.functor` induces an
equivalence between cones over `F` and cones over `F ⋙ e.functor`.
-/
@[simp] theorem functoriality_equivalence_counit_iso {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) {D : Type u'} [category D] (e : C ≌ D) : equivalence.counit_iso (functoriality_equivalence F e) =
  nat_iso.of_components
    (fun (c : cone (F ⋙ equivalence.functor e)) =>
      ext (iso.app (equivalence.counit_iso e) (cone.X c)) (functoriality_equivalence._proof_3 F e c))
    (functoriality_equivalence._proof_4 F e) :=
  Eq.refl (equivalence.counit_iso (functoriality_equivalence F e))

/--
If `F` reflects isomorphisms, then `cones.functoriality F` reflects isomorphisms
as well.
-/
protected instance reflects_cone_isomorphism {J : Type v} [small_category J] {C : Type u} [category C] {D : Type u'} [category D] (F : C ⥤ D) [reflects_isomorphisms F] (K : J ⥤ C) : reflects_isomorphisms (functoriality K F) :=
  reflects_isomorphisms.mk
    fun (A B : cone K) (f : A ⟶ B) (_inst_3_1 : is_iso (functor.map (functoriality K F) f)) => cone_iso_of_hom_iso f

end cones


/-- A cocone morphism between two cocones for the same diagram is a morphism of the cocone points
which commutes with the cocone legs. -/
structure cocone_morphism {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} (A : cocone F) (B : cocone F) 
where
  hom : cocone.X A ⟶ cocone.X B
  w' : autoParam (∀ (j : J), nat_trans.app (cocone.ι A) j ≫ hom = nat_trans.app (cocone.ι B) j)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

protected instance inhabited_cocone_morphism {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} (A : cocone F) : Inhabited (cocone_morphism A A) :=
  { default := cocone_morphism.mk 𝟙 }

@[simp] theorem cocone_morphism.w {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {A : cocone F} {B : cocone F} (c : cocone_morphism A B) (j : J) : nat_trans.app (cocone.ι A) j ≫ cocone_morphism.hom c = nat_trans.app (cocone.ι B) j := sorry

@[simp] theorem cocone_morphism.w_assoc {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {A : cocone F} {B : cocone F} (c : cocone_morphism A B) (j : J) {X' : C} (f' : cocone.X B ⟶ X') : nat_trans.app (cocone.ι A) j ≫ cocone_morphism.hom c ≫ f' = nat_trans.app (cocone.ι B) j ≫ f' := sorry

@[simp] theorem cocone.category_to_category_struct_id_hom {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} (B : cocone F) : cocone_morphism.hom 𝟙 = 𝟙 :=
  Eq.refl (cocone_morphism.hom 𝟙)

namespace cocones


/-- To give an isomorphism between cocones, it suffices to give an
  isomorphism between their vertices which commutes with the cocone
  maps. -/
@[simp] theorem ext_inv_hom {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {c : cocone F} {c' : cocone F} (φ : cocone.X c ≅ cocone.X c') (w : ∀ (j : J), nat_trans.app (cocone.ι c) j ≫ iso.hom φ = nat_trans.app (cocone.ι c') j) : cocone_morphism.hom (iso.inv (ext φ w)) = iso.inv φ :=
  Eq.refl (cocone_morphism.hom (iso.inv (ext φ w)))

/--
Given a cocone morphism whose object part is an isomorphism, produce an
isomorphism of cocones.
-/
def cocone_iso_of_hom_iso {J : Type v} [small_category J] {C : Type u} [category C] {K : J ⥤ C} {c : cocone K} {d : cocone K} (f : c ⟶ d) [i : is_iso (cocone_morphism.hom f)] : is_iso f :=
  is_iso.mk (cocone_morphism.mk (inv (cocone_morphism.hom f)))

/--
Functorially precompose a cocone for `F` by a natural transformation `G ⟶ F` to give a cocone for `G`.
-/
def precompose {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {G : J ⥤ C} (α : G ⟶ F) : cocone F ⥤ cocone G :=
  functor.mk (fun (c : cocone F) => cocone.mk (cocone.X c) (α ≫ cocone.ι c))
    fun (c₁ c₂ : cocone F) (f : c₁ ⟶ c₂) => cocone_morphism.mk (cocone_morphism.hom f)

/-- Precomposing a cocone by the composite natural transformation `α ≫ β` is the same as
precomposing by `β` and then by `α`. -/
def precompose_comp {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {G : J ⥤ C} {H : J ⥤ C} (α : F ⟶ G) (β : G ⟶ H) : precompose (α ≫ β) ≅ precompose β ⋙ precompose α :=
  nat_iso.of_components (fun (s : cocone H) => ext (iso.refl (cocone.X (functor.obj (precompose (α ≫ β)) s))) sorry) sorry

/-- Precomposing by the identity does not change the cocone up to isomorphism. -/
def precompose_id {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} : precompose 𝟙 ≅ 𝟭 :=
  nat_iso.of_components (fun (s : cocone F) => ext (iso.refl (cocone.X (functor.obj (precompose 𝟙) s))) sorry) sorry

/--
If `F` and `G` are naturally isomorphic functors, then they have equivalent categories of
cocones.
-/
@[simp] theorem precompose_equivalence_functor {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {G : J ⥤ C} (α : G ≅ F) : equivalence.functor (precompose_equivalence α) = precompose (iso.hom α) :=
  Eq.refl (equivalence.functor (precompose_equivalence α))

/--
Whiskering on the left by `E : K ⥤ J` gives a functor from `cocone F` to `cocone (E ⋙ F)`.
-/
def whiskering {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {K : Type v} [small_category K] (E : K ⥤ J) : cocone F ⥤ cocone (E ⋙ F) :=
  functor.mk (fun (c : cocone F) => cocone.whisker E c)
    fun (c c' : cocone F) (f : c ⟶ c') => cocone_morphism.mk (cocone_morphism.hom f)

/--
Whiskering by an equivalence gives an equivalence between categories of cones.
-/
def whiskering_equivalence {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {K : Type v} [small_category K] (e : K ≌ J) : cocone F ≌ cocone (equivalence.functor e ⋙ F) :=
  equivalence.mk' (whiskering (equivalence.functor e))
    (whiskering (equivalence.inverse e) ⋙
      precompose
        (iso.inv (functor.left_unitor F) ≫
          whisker_right (iso.inv (equivalence.counit_iso e)) F ≫
            iso.inv (functor.associator (equivalence.inverse e) (equivalence.functor e) F)))
    (nat_iso.of_components (fun (s : cocone F) => ext (iso.refl (cocone.X (functor.obj 𝟭 s))) sorry) sorry)
    (nat_iso.of_components
      (fun (s : cocone (equivalence.functor e ⋙ F)) =>
        ext
          (iso.refl
            (cocone.X
              (functor.obj
                ((whiskering (equivalence.inverse e) ⋙
                    precompose
                      (iso.inv (functor.left_unitor F) ≫
                        whisker_right (iso.inv (equivalence.counit_iso e)) F ≫
                          iso.inv (functor.associator (equivalence.inverse e) (equivalence.functor e) F))) ⋙
                  whiskering (equivalence.functor e))
                s)))
          sorry)
      sorry)

/--
The categories of cocones over `F` and `G` are equivalent if `F` and `G` are naturally isomorphic
(possibly after changing the indexing category by an equivalence).
-/
@[simp] theorem equivalence_of_reindexing_functor_obj {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {K : Type v} [small_category K] {G : K ⥤ C} (e : K ≌ J) (α : equivalence.functor e ⋙ F ≅ G) (X : cocone F) : functor.obj (equivalence.functor (equivalence_of_reindexing e α)) X =
  functor.obj (precompose (iso.inv α)) (cocone.whisker (equivalence.functor e) X) :=
  Eq.refl (functor.obj (precompose (iso.inv α)) (cocone.whisker (equivalence.functor e) X))

/-- Forget the cocone structure and obtain just the cocone point. -/
@[simp] theorem forget_map {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) (s : cocone F) (t : cocone F) (f : s ⟶ t) : functor.map (forget F) f = cocone_morphism.hom f :=
  Eq.refl (functor.map (forget F) f)

/-- A functor `G : C ⥤ D` sends cocones over `F` to cocones over `F ⋙ G` functorially. -/
@[simp] theorem functoriality_map_hom {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) {D : Type u'} [category D] (G : C ⥤ D) (_x : cocone F) : ∀ (_x_1 : cocone F) (f : _x ⟶ _x_1),
  cocone_morphism.hom (functor.map (functoriality F G) f) = functor.map G (cocone_morphism.hom f) :=
  fun (_x_1 : cocone F) (f : _x ⟶ _x_1) => Eq.refl (cocone_morphism.hom (functor.map (functoriality F G) f))

protected instance functoriality_full {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) {D : Type u'} [category D] (G : C ⥤ D) [full G] [faithful G] : full (functoriality F G) :=
  full.mk
    fun (X Y : cocone F) (t : functor.obj (functoriality F G) X ⟶ functor.obj (functoriality F G) Y) =>
      cocone_morphism.mk (functor.preimage G (cocone_morphism.hom t))

protected instance functoriality_faithful {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) {D : Type u'} [category D] (G : C ⥤ D) [faithful G] : faithful (functoriality F G) :=
  faithful.mk

/--
If `e : C ≌ D` is an equivalence of categories, then `functoriality F e.functor` induces an
equivalence between cocones over `F` and cocones over `F ⋙ e.functor`.
-/
@[simp] theorem functoriality_equivalence_functor {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) {D : Type u'} [category D] (e : C ≌ D) : equivalence.functor (functoriality_equivalence F e) = functoriality F (equivalence.functor e) :=
  Eq.refl (equivalence.functor (functoriality_equivalence F e))

/--
If `F` reflects isomorphisms, then `cocones.functoriality F` reflects isomorphisms
as well.
-/
protected instance reflects_cocone_isomorphism {J : Type v} [small_category J] {C : Type u} [category C] {D : Type u'} [category D] (F : C ⥤ D) [reflects_isomorphisms F] (K : J ⥤ C) : reflects_isomorphisms (functoriality K F) :=
  reflects_isomorphisms.mk
    fun (A B : cocone K) (f : A ⟶ B) (_inst_3_1 : is_iso (functor.map (functoriality K F) f)) => cocone_iso_of_hom_iso f

end cocones


end limits


namespace functor


/-- The image of a cone in C under a functor G : C ⥤ D is a cone in D. -/
/-- The image of a cocone in C under a functor G : C ⥤ D is a cocone in D. -/
@[simp] theorem map_cone_X {J : Type v} [small_category J] {C : Type u} [category C] {D : Type u'} [category D] {F : J ⥤ C} (H : C ⥤ D) (c : limits.cone F) : limits.cone.X (map_cone H c) = obj H (limits.cone.X c) :=
  Eq.refl (obj H (limits.cone.X c))

@[simp] theorem map_cocone_ι_app {J : Type v} [small_category J] {C : Type u} [category C] {D : Type u'} [category D] {F : J ⥤ C} (H : C ⥤ D) (c : limits.cocone F) (j : J) : nat_trans.app (limits.cocone.ι (map_cocone H c)) j = map H (nat_trans.app (limits.cocone.ι c) j) :=
  Eq.refl (map H (nat_trans.app (limits.cocone.ι c) j))

/-- Given a cone morphism `c ⟶ c'`, construct a cone morphism on the mapped cones functorially.  -/
def map_cone_morphism {J : Type v} [small_category J] {C : Type u} [category C] {D : Type u'} [category D] {F : J ⥤ C} (H : C ⥤ D) {c : limits.cone F} {c' : limits.cone F} (f : c ⟶ c') : map_cone H c ⟶ map_cone H c' :=
  map (limits.cones.functoriality F H) f

/-- Given a cocone morphism `c ⟶ c'`, construct a cocone morphism on the mapped cocones functorially.  -/
def map_cocone_morphism {J : Type v} [small_category J] {C : Type u} [category C] {D : Type u'} [category D] {F : J ⥤ C} (H : C ⥤ D) {c : limits.cocone F} {c' : limits.cocone F} (f : c ⟶ c') : map_cocone H c ⟶ map_cocone H c' :=
  map (limits.cocones.functoriality F H) f

/-- If `H` is an equivalence, we invert `H.map_cone` and get a cone for `F` from a cone
for `F ⋙ H`.-/
def map_cone_inv {J : Type v} [small_category J] {C : Type u} [category C] {D : Type u'} [category D] {F : J ⥤ C} (H : C ⥤ D) [is_equivalence H] (c : limits.cone (F ⋙ H)) : limits.cone F :=
  obj (equivalence.inverse (limits.cones.functoriality_equivalence F (as_equivalence H))) c

/-- `map_cone` is the left inverse to `map_cone_inv`. -/
def map_cone_map_cone_inv {J : Type v} [small_category J] {C : Type u} [category C] {D : Type u'} [category D] {F : J ⥤ D} (H : D ⥤ C) [is_equivalence H] (c : limits.cone (F ⋙ H)) : map_cone H (map_cone_inv H c) ≅ c :=
  iso.app (equivalence.counit_iso (limits.cones.functoriality_equivalence F (as_equivalence H))) c

/-- `map_cone` is the right inverse to `map_cone_inv`. -/
def map_cone_inv_map_cone {J : Type v} [small_category J] {C : Type u} [category C] {D : Type u'} [category D] {F : J ⥤ D} (H : D ⥤ C) [is_equivalence H] (c : limits.cone F) : map_cone_inv H (map_cone H c) ≅ c :=
  iso.app (iso.symm (equivalence.unit_iso (limits.cones.functoriality_equivalence F (as_equivalence H)))) c

/-- If `H` is an equivalence, we invert `H.map_cone` and get a cone for `F` from a cone
for `F ⋙ H`.-/
def map_cocone_inv {J : Type v} [small_category J] {C : Type u} [category C] {D : Type u'} [category D] {F : J ⥤ C} (H : C ⥤ D) [is_equivalence H] (c : limits.cocone (F ⋙ H)) : limits.cocone F :=
  obj (equivalence.inverse (limits.cocones.functoriality_equivalence F (as_equivalence H))) c

/-- `map_cocone` is the left inverse to `map_cocone_inv`. -/
def map_cocone_map_cocone_inv {J : Type v} [small_category J] {C : Type u} [category C] {D : Type u'} [category D] {F : J ⥤ D} (H : D ⥤ C) [is_equivalence H] (c : limits.cocone (F ⋙ H)) : map_cocone H (map_cocone_inv H c) ≅ c :=
  iso.app (equivalence.counit_iso (limits.cocones.functoriality_equivalence F (as_equivalence H))) c

/-- `map_cocone` is the right inverse to `map_cocone_inv`. -/
def map_cocone_inv_map_cocone {J : Type v} [small_category J] {C : Type u} [category C] {D : Type u'} [category D] {F : J ⥤ D} (H : D ⥤ C) [is_equivalence H] (c : limits.cocone F) : map_cocone_inv H (map_cocone H c) ≅ c :=
  iso.app (iso.symm (equivalence.unit_iso (limits.cocones.functoriality_equivalence F (as_equivalence H)))) c

/-- `functoriality F _ ⋙ postcompose (whisker_left F _)` simplifies to `functoriality F _`. -/
@[simp] theorem functoriality_comp_postcompose_inv_app_hom {J : Type v} [small_category J] {C : Type u} [category C] {D : Type u'} [category D] {F : J ⥤ C} {H : C ⥤ D} {H' : C ⥤ D} (α : H ≅ H') (X : limits.cone F) : limits.cone_morphism.hom (nat_trans.app (iso.inv (functoriality_comp_postcompose α)) X) =
  nat_trans.app (iso.inv α) (limits.cone.X X) :=
  Eq.refl (nat_trans.app (iso.inv α) (limits.cone.X X))

/--
For `F : J ⥤ C`, given a cone `c : cone F`, and a natural isomorphism `α : H ≅ H'` for functors
`H H' : C ⥤ D`, the postcomposition of the cone `H.map_cone` using the isomorphism `α` is
isomorphic to the cone `H'.map_cone`.
-/
def postcompose_whisker_left_map_cone {J : Type v} [small_category J] {C : Type u} [category C] {D : Type u'} [category D] {F : J ⥤ C} {H : C ⥤ D} {H' : C ⥤ D} (α : H ≅ H') (c : limits.cone F) : obj (limits.cones.postcompose (whisker_left F (iso.hom α))) (map_cone H c) ≅ map_cone H' c :=
  iso.app (functoriality_comp_postcompose α) c

/--
`map_cone` commutes with `postcompose`. In particular, for `F : J ⥤ C`, given a cone `c : cone F`, a
natural transformation `α : F ⟶ G` and a functor `H : C ⥤ D`, we have two obvious ways of producing
a cone over `G ⋙ H`, and they are both isomorphic.
-/
@[simp] theorem map_cone_postcompose_inv_hom {J : Type v} [small_category J] {C : Type u} [category C] {D : Type u'} [category D] {F : J ⥤ C} {G : J ⥤ C} (H : C ⥤ D) {α : F ⟶ G} {c : limits.cone F} : limits.cone_morphism.hom (iso.inv (map_cone_postcompose H)) = 𝟙 :=
  Eq.refl 𝟙

/--
`map_cone` commutes with `postcompose_equivalence`
-/
@[simp] theorem map_cone_postcompose_equivalence_functor_hom_hom {J : Type v} [small_category J] {C : Type u} [category C] {D : Type u'} [category D] {F : J ⥤ C} {G : J ⥤ C} (H : C ⥤ D) {α : F ≅ G} {c : limits.cone F} : limits.cone_morphism.hom (iso.hom (map_cone_postcompose_equivalence_functor H)) = 𝟙 :=
  Eq.refl 𝟙

/-- `functoriality F _ ⋙ precompose (whisker_left F _)` simplifies to `functoriality F _`. -/
@[simp] theorem functoriality_comp_precompose_inv_app_hom {J : Type v} [small_category J] {C : Type u} [category C] {D : Type u'} [category D] {F : J ⥤ C} {H : C ⥤ D} {H' : C ⥤ D} (α : H ≅ H') (X : limits.cocone F) : limits.cocone_morphism.hom (nat_trans.app (iso.inv (functoriality_comp_precompose α)) X) =
  nat_trans.app (iso.inv α) (limits.cocone.X X) :=
  Eq.refl (nat_trans.app (iso.inv α) (limits.cocone.X X))

/--
For `F : J ⥤ C`, given a cocone `c : cocone F`, and a natural isomorphism `α : H ≅ H'` for functors
`H H' : C ⥤ D`, the precomposition of the cocone `H.map_cocone` using the isomorphism `α` is
isomorphic to the cocone `H'.map_cocone`.
-/
def precompose_whisker_left_map_cocone {J : Type v} [small_category J] {C : Type u} [category C] {D : Type u'} [category D] {F : J ⥤ C} {H : C ⥤ D} {H' : C ⥤ D} (α : H ≅ H') (c : limits.cocone F) : obj (limits.cocones.precompose (whisker_left F (iso.inv α))) (map_cocone H c) ≅ map_cocone H' c :=
  iso.app (functoriality_comp_precompose α) c

/--
`map_cocone` commutes with `precompose`. In particular, for `F : J ⥤ C`, given a cocone
`c : cocone F`, a natural transformation `α : F ⟶ G` and a functor `H : C ⥤ D`, we have two obvious
ways of producing a cocone over `G ⋙ H`, and they are both isomorphic.
-/
@[simp] theorem map_cocone_precompose_hom_hom {J : Type v} [small_category J] {C : Type u} [category C] {D : Type u'} [category D] {F : J ⥤ C} {G : J ⥤ C} (H : C ⥤ D) {α : F ⟶ G} {c : limits.cocone G} : limits.cocone_morphism.hom (iso.hom (map_cocone_precompose H)) = 𝟙 :=
  Eq.refl 𝟙

/--
`map_cocone` commutes with `precompose_equivalence`
-/
@[simp] theorem map_cocone_precompose_equivalence_functor_inv_hom {J : Type v} [small_category J] {C : Type u} [category C] {D : Type u'} [category D] {F : J ⥤ C} {G : J ⥤ C} (H : C ⥤ D) {α : F ≅ G} {c : limits.cocone G} : limits.cocone_morphism.hom (iso.inv (map_cocone_precompose_equivalence_functor H)) = 𝟙 :=
  Eq.refl 𝟙

/--
`map_cone` commutes with `whisker`
-/
@[simp] theorem map_cone_whisker_inv_hom {J : Type v} [small_category J] {C : Type u} [category C] {D : Type u'} [category D] {F : J ⥤ C} (H : C ⥤ D) {K : Type v} [small_category K] {E : K ⥤ J} {c : limits.cone F} : limits.cone_morphism.hom (iso.inv (map_cone_whisker H)) = 𝟙 :=
  Eq.refl 𝟙

/--
`map_cocone` commutes with `whisker`
-/
@[simp] theorem map_cocone_whisker_inv_hom {J : Type v} [small_category J] {C : Type u} [category C] {D : Type u'} [category D] {F : J ⥤ C} (H : C ⥤ D) {K : Type v} [small_category K] {E : K ⥤ J} {c : limits.cocone F} : limits.cocone_morphism.hom (iso.inv (map_cocone_whisker H)) = 𝟙 :=
  Eq.refl 𝟙

end functor


end category_theory


namespace category_theory.limits


/-- Change a `cocone F` into a `cone F.op`. -/
@[simp] theorem cocone.op_X {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} (c : cocone F) : cone.X (cocone.op c) = opposite.op (cocone.X c) :=
  Eq.refl (cone.X (cocone.op c))

/-- Change a `cone F` into a `cocone F.op`. -/
def cone.op {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} (c : cone F) : cocone (functor.op F) :=
  cocone.mk (opposite.op (cone.X c))
    (nat_trans.mk fun (j : Jᵒᵖ) => has_hom.hom.op (nat_trans.app (cone.π c) (opposite.unop j)))

/-- Change a `cocone F.op` into a `cone F`. -/
def cocone.unop {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} (c : cocone (functor.op F)) : cone F :=
  cone.mk (opposite.unop (cocone.X c))
    (nat_trans.mk fun (j : J) => has_hom.hom.unop (nat_trans.app (cocone.ι c) (opposite.op j)))

/-- Change a `cone F.op` into a `cocone F`. -/
@[simp] theorem cone.unop_X {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} (c : cone (functor.op F)) : cocone.X (cone.unop c) = opposite.unop (cone.X c) :=
  Eq.refl (cocone.X (cone.unop c))

/--
The category of cocones on `F`
is equivalent to the opposite category of
the category of cones on the opposite of `F`.
-/
@[simp] theorem cocone_equivalence_op_cone_op_unit_iso {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) : equivalence.unit_iso (cocone_equivalence_op_cone_op F) =
  nat_iso.of_components
    (fun (c : cocone F) =>
      cocones.ext (iso.refl (cocone.X (functor.obj 𝟭 c))) (cocone_equivalence_op_cone_op._proof_7 F c))
    (cocone_equivalence_op_cone_op._proof_8 F) :=
  Eq.refl (equivalence.unit_iso (cocone_equivalence_op_cone_op F))

/-- Change a cocone on `F.left_op : Jᵒᵖ ⥤ C` to a cocone on `F : J ⥤ Cᵒᵖ`. -/
-- Here and below we only automatically generate the `@[simp]` lemma for the `X` field,

-- as we can write a simpler `rfl` lemma for the components of the natural transformation by hand.

def cone_of_cocone_left_op {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ (Cᵒᵖ)} (c : cocone (functor.left_op F)) : cone F :=
  cone.mk (opposite.op (cocone.X c))
    (nat_trans.remove_left_op (cocone.ι c ≫ iso.hom (functor.const.op_obj_unop (opposite.op (cocone.X c)))))

/-- Change a cone on `F : J ⥤ Cᵒᵖ` to a cocone on `F.left_op : Jᵒᵖ ⥤ C`. -/
def cocone_left_op_of_cone {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ (Cᵒᵖ)} (c : cone F) : cocone (functor.left_op F) :=
  cocone.mk (opposite.unop (cone.X c)) (nat_trans.left_op (cone.π c))

/-- Change a cone on `F.left_op : Jᵒᵖ ⥤ C` to a cocone on `F : J ⥤ Cᵒᵖ`. -/
/- When trying use `@[simps]` to generate the `ι_app` field of this definition, `@[simps]` tries to
  reduce the RHS using `expr.dsimp` and `expr.simp`, but for some reason the expression is not
  being simplified properly. -/

def cocone_of_cone_left_op {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ (Cᵒᵖ)} (c : cone (functor.left_op F)) : cocone F :=
  cocone.mk (opposite.op (cone.X c))
    (nat_trans.remove_left_op (iso.hom (functor.const.op_obj_unop (opposite.op (cone.X c))) ≫ cone.π c))

@[simp] theorem cocone_of_cone_left_op_ι_app {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ (Cᵒᵖ)} (c : cone (functor.left_op F)) (j : J) : nat_trans.app (cocone.ι (cocone_of_cone_left_op c)) j = has_hom.hom.op (nat_trans.app (cone.π c) (opposite.op j)) := sorry

/-- Change a cocone on `F : J ⥤ Cᵒᵖ` to a cone on `F.left_op : Jᵒᵖ ⥤ C`. -/
def cone_left_op_of_cocone {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ (Cᵒᵖ)} (c : cocone F) : cone (functor.left_op F) :=
  cone.mk (opposite.unop (cocone.X c)) (nat_trans.left_op (cocone.ι c))

end category_theory.limits


namespace category_theory.functor


/-- The opposite cocone of the image of a cone is the image of the opposite cocone. -/
def map_cone_op {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {D : Type u'} [category D] (G : C ⥤ D) (t : limits.cone F) : limits.cone.op (map_cone G t) ≅ map_cocone (functor.op G) (limits.cone.op t) :=
  limits.cocones.ext (iso.refl (limits.cocone.X (limits.cone.op (map_cone G t)))) sorry

/-- The opposite cone of the image of a cocone is the image of the opposite cone. -/
def map_cocone_op {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {D : Type u'} [category D] (G : C ⥤ D) {t : limits.cocone F} : limits.cocone.op (map_cocone G t) ≅ map_cone (functor.op G) (limits.cocone.op t) :=
  limits.cones.ext (iso.refl (limits.cone.X (limits.cocone.op (map_cocone G t)))) sorry

