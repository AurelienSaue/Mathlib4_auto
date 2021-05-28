/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.category.Top.basic
import Mathlib.category_theory.eq_to_hom
import Mathlib.PostPort

universes u u_1 

namespace Mathlib

/-!
# The category of open sets in a topological space.

We define `to_Top : opens X ⥤ Top` and
`map (f : X ⟶ Y) : opens Y ⥤ opens X`, given by taking preimages of open sets.

Unfortunately `opens` isn't (usefully) a functor `Top ⥤ Cat`.
(One can in fact define such a functor,
but using it results in unresolvable `eq.rec` terms in goals.)

Really it's a 2-functor from (spaces, continuous functions, equalities)
to (categories, functors, natural isomorphisms).
We don't attempt to set up the full theory here, but do provide the natural isomorphisms
`map_id : map (𝟙 X) ≅ 𝟭 (opens X)` and
`map_comp : map (f ≫ g) ≅ map g ⋙ map f`.

Beyond that, there's a collection of simp lemmas for working with these constructions.
-/

namespace topological_space.opens


/-!
Since `opens X` has a partial order, it automatically receives a `category` instance.
Unfortunately, because we do not allow morphisms in `Prop`,
the morphisms `U ⟶ V` are not just proofs `U ≤ V`, but rather
`ulift (plift (U ≤ V))`.
-/

protected instance opens_hom_has_coe_to_fun {X : Top} {U : opens ↥X} {V : opens ↥X} : has_coe_to_fun (U ⟶ V) :=
  has_coe_to_fun.mk (fun (f : U ⟶ V) => ↥U → ↥V) fun (f : U ⟶ V) (x : ↥U) => { val := ↑x, property := sorry }

/-!
We now construct as morphisms various inclusions of open sets.
-/

-- This is tedious, but necessary because we decided not to allow Prop as morphisms in a category...

/--
The inclusion `U ⊓ V ⟶ U` as a morphism in the category of open sets.
-/
def inf_le_left {X : Top} (U : opens ↥X) (V : opens ↥X) : U ⊓ V ⟶ U :=
  category_theory.hom_of_le sorry

/--
The inclusion `U ⊓ V ⟶ V` as a morphism in the category of open sets.
-/
def inf_le_right {X : Top} (U : opens ↥X) (V : opens ↥X) : U ⊓ V ⟶ V :=
  category_theory.hom_of_le sorry

/--
The inclusion `U i ⟶ supr U` as a morphism in the category of open sets.
-/
def le_supr {X : Top} {ι : Type u_1} (U : ι → opens ↥X) (i : ι) : U i ⟶ supr U :=
  category_theory.hom_of_le sorry

/--
The inclusion `⊥ ⟶ U` as a morphism in the category of open sets.
-/
def bot_le {X : Top} (U : opens ↥X) : ⊥ ⟶ U :=
  category_theory.hom_of_le sorry

/--
The inclusion `U ⟶ ⊤` as a morphism in the category of open sets.
-/
def le_top {X : Top} (U : opens ↥X) : U ⟶ ⊤ :=
  category_theory.hom_of_le sorry

-- We do not mark this as a simp lemma because it breaks open `x`.

-- Nevertheless, it is useful in `sheaf_of_functions`.

theorem inf_le_left_apply {X : Top} (U : opens ↥X) (V : opens ↥X) (x : ↥(U ⊓ V)) : coe_fn (inf_le_left U V) x = { val := subtype.val x, property := inf_le_left (subtype.val x) (subtype.property x) } :=
  rfl

@[simp] theorem inf_le_left_apply_mk {X : Top} (U : opens ↥X) (V : opens ↥X) (x : ↥X) (m : x ∈ has_coe_t_aux.coe (U ⊓ V)) : coe_fn (inf_le_left U V) { val := x, property := m } = { val := x, property := inf_le_left x m } :=
  rfl

@[simp] theorem le_supr_apply_mk {X : Top} {ι : Type u_1} (U : ι → opens ↥X) (i : ι) (x : ↥X) (m : x ∈ has_coe_t_aux.coe (U i)) : coe_fn (le_supr U i) { val := x, property := m } = { val := x, property := le_supr U i x m } :=
  rfl

/--
The functor from open sets in `X` to `Top`,
realising each open set as a topological space itself.
-/
def to_Top (X : Top) : opens ↥X ⥤ Top :=
  category_theory.functor.mk (fun (U : opens ↥X) => category_theory.bundled.mk ↥(subtype.val U))
    fun (U V : opens ↥X) (i : U ⟶ V) =>
      continuous_map.mk
        fun (x : ↥(category_theory.bundled.mk ↥(subtype.val U))) => { val := subtype.val x, property := sorry }

@[simp] theorem to_Top_map (X : Top) {U : opens ↥X} {V : opens ↥X} {f : U ⟶ V} {x : ↥X} {h : x ∈ subtype.val U} : coe_fn (category_theory.functor.map (to_Top X) f) { val := x, property := h } =
  { val := x, property := category_theory.le_of_hom f x h } :=
  rfl

/--
The inclusion map from an open subset to the whole space, as a morphism in `Top`.
-/
@[simp] theorem inclusion_to_fun {X : Top} (U : opens ↥X) : ∀ (ᾰ : Subtype fun (x : ↥X) => x ∈ subtype.val U), coe_fn (inclusion U) ᾰ = ↑ᾰ :=
  fun (ᾰ : Subtype fun (x : ↥X) => x ∈ subtype.val U) => Eq.refl (coe_fn (inclusion U) ᾰ)

theorem inclusion_open_embedding {X : Top} (U : opens ↥X) : open_embedding ⇑(inclusion U) :=
  is_open.open_embedding_subtype_coe (subtype.property U)

/-- `opens.map f` gives the functor from open sets in Y to open set in X,
    given by taking preimages under f. -/
def map {X : Top} {Y : Top} (f : X ⟶ Y) : opens ↥Y ⥤ opens ↥X :=
  category_theory.functor.mk (fun (U : opens ↥Y) => { val := ⇑f ⁻¹' subtype.val U, property := sorry })
    fun (U V : opens ↥Y) (i : U ⟶ V) => ulift.up (plift.up sorry)

@[simp] theorem map_obj {X : Top} {Y : Top} (f : X ⟶ Y) (U : set ↥Y) (p : is_open U) : category_theory.functor.obj (map f) { val := U, property := p } =
  { val := ⇑f ⁻¹' U, property := is_open.preimage (continuous_map.continuous f) p } :=
  rfl

@[simp] theorem map_id_obj {X : Top} (U : opens ↥X) : category_theory.functor.obj (map 𝟙) U = U :=
  ext (set.ext fun (x : ↥X) => iff.refl (x ∈ ↑(category_theory.functor.obj (map 𝟙) U)))

@[simp] theorem map_id_obj' {X : Top} (U : set ↥X) (p : is_open U) : category_theory.functor.obj (map 𝟙) { val := U, property := p } = { val := U, property := p } :=
  rfl

@[simp] theorem map_id_obj_unop {X : Top} (U : opens ↥Xᵒᵖ) : category_theory.functor.obj (map 𝟙) (opposite.unop U) = opposite.unop U := sorry

@[simp] theorem op_map_id_obj {X : Top} (U : opens ↥Xᵒᵖ) : category_theory.functor.obj (category_theory.functor.op (map 𝟙)) U = U := sorry

/--
The inclusion `U ⟶ (map f).obj ⊤` as a morphism in the category of open sets.
-/
def le_map_top {X : Top} {Y : Top} (f : X ⟶ Y) (U : opens ↥X) : U ⟶ category_theory.functor.obj (map f) ⊤ :=
  category_theory.hom_of_le sorry

@[simp] theorem map_comp_obj {X : Top} {Y : Top} {Z : Top} (f : X ⟶ Y) (g : Y ⟶ Z) (U : opens ↥Z) : category_theory.functor.obj (map (f ≫ g)) U =
  category_theory.functor.obj (map f) (category_theory.functor.obj (map g) U) :=
  ext (set.ext fun (x : ↥X) => iff.refl (x ∈ ↑(category_theory.functor.obj (map (f ≫ g)) U)))

@[simp] theorem map_comp_obj' {X : Top} {Y : Top} {Z : Top} (f : X ⟶ Y) (g : Y ⟶ Z) (U : set ↥Z) (p : is_open U) : category_theory.functor.obj (map (f ≫ g)) { val := U, property := p } =
  category_theory.functor.obj (map f) (category_theory.functor.obj (map g) { val := U, property := p }) :=
  rfl

@[simp] theorem map_comp_map {X : Top} {Y : Top} {Z : Top} (f : X ⟶ Y) (g : Y ⟶ Z) {U : opens ↥Z} {V : opens ↥Z} (i : U ⟶ V) : category_theory.functor.map (map (f ≫ g)) i =
  category_theory.functor.map (map f) (category_theory.functor.map (map g) i) :=
  rfl

@[simp] theorem map_comp_obj_unop {X : Top} {Y : Top} {Z : Top} (f : X ⟶ Y) (g : Y ⟶ Z) (U : opens ↥Zᵒᵖ) : category_theory.functor.obj (map (f ≫ g)) (opposite.unop U) =
  category_theory.functor.obj (map f) (category_theory.functor.obj (map g) (opposite.unop U)) :=
  map_comp_obj f g (opposite.unop U)

@[simp] theorem op_map_comp_obj {X : Top} {Y : Top} {Z : Top} (f : X ⟶ Y) (g : Y ⟶ Z) (U : opens ↥Zᵒᵖ) : category_theory.functor.obj (category_theory.functor.op (map (f ≫ g))) U =
  category_theory.functor.obj (category_theory.functor.op (map f))
    (category_theory.functor.obj (category_theory.functor.op (map g)) U) := sorry

/--
The functor `opens X ⥤ opens X` given by taking preimages under the identity function
is naturally isomorphic to the identity functor.
-/
@[simp] theorem map_id_hom_app (X : Top) (U : opens ↥X) : category_theory.nat_trans.app (category_theory.iso.hom (map_id X)) U = category_theory.eq_to_hom (map_id_obj U) :=
  Eq.refl (category_theory.nat_trans.app (category_theory.iso.hom (map_id X)) U)

/--
The natural isomorphism between taking preimages under `f ≫ g`, and the composite
of taking preimages under `g`, then preimages under `f`.
-/
@[simp] theorem map_comp_hom_app {X : Top} {Y : Top} {Z : Top} (f : X ⟶ Y) (g : Y ⟶ Z) (U : opens ↥Z) : category_theory.nat_trans.app (category_theory.iso.hom (map_comp f g)) U =
  category_theory.eq_to_hom (map_comp_obj f g U) :=
  Eq.refl (category_theory.nat_trans.app (category_theory.iso.hom (map_comp f g)) U)

/--
If two continuous maps `f g : X ⟶ Y` are equal,
then the functors `opens Y ⥤ opens X` they induce are isomorphic.
-/
-- We could make `f g` implicit here, but it's nice to be able to see when

-- they are the identity (often!)

def map_iso {X : Top} {Y : Top} (f : X ⟶ Y) (g : X ⟶ Y) (h : f = g) : map f ≅ map g :=
  category_theory.nat_iso.of_components (fun (U : opens ↥Y) => category_theory.eq_to_iso sorry) sorry

@[simp] theorem map_iso_refl {X : Top} {Y : Top} (f : X ⟶ Y) (h : f = f) : map_iso f f h = category_theory.iso.refl (map f) :=
  rfl

@[simp] theorem map_iso_hom_app {X : Top} {Y : Top} (f : X ⟶ Y) (g : X ⟶ Y) (h : f = g) (U : opens ↥Y) : category_theory.nat_trans.app (category_theory.iso.hom (map_iso f g h)) U =
  category_theory.eq_to_hom (congr_fun (congr_arg category_theory.functor.obj (congr_arg map h)) U) :=
  rfl

@[simp] theorem map_iso_inv_app {X : Top} {Y : Top} (f : X ⟶ Y) (g : X ⟶ Y) (h : f = g) (U : opens ↥Y) : category_theory.nat_trans.app (category_theory.iso.inv (map_iso f g h)) U =
  category_theory.eq_to_hom (congr_fun (congr_arg category_theory.functor.obj (congr_arg map (Eq.symm h))) U) :=
  rfl

end topological_space.opens


/--
An open map `f : X ⟶ Y` induces a functor `opens X ⥤ opens Y`.
-/
@[simp] theorem is_open_map.functor_obj_coe {X : Top} {Y : Top} {f : X ⟶ Y} (hf : is_open_map ⇑f) (U : topological_space.opens ↥X) : ↑(category_theory.functor.obj (is_open_map.functor hf) U) = ⇑f '' ↑U :=
  Eq.refl ↑(category_theory.functor.obj (is_open_map.functor hf) U)

/--
An open map `f : X ⟶ Y` induces an adjunction between `opens X` and `opens Y`.
-/
def is_open_map.adjunction {X : Top} {Y : Top} {f : X ⟶ Y} (hf : is_open_map ⇑f) : is_open_map.functor hf ⊣ topological_space.opens.map f :=
  category_theory.adjunction.mk_of_unit_counit
    (category_theory.adjunction.core_unit_counit.mk
      (category_theory.nat_trans.mk fun (U : topological_space.opens ↥X) => category_theory.hom_of_le sorry)
      (category_theory.nat_trans.mk fun (V : topological_space.opens ↥Y) => category_theory.hom_of_le sorry))

