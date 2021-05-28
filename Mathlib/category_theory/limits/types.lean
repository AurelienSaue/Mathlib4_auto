/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Reid Barton
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.limits.shapes.images
import Mathlib.category_theory.filtered
import Mathlib.tactic.equiv_rw
import Mathlib.PostPort

universes u 

namespace Mathlib

namespace category_theory.limits.types


/--
(internal implementation) the limit cone of a functor,
implemented as flat sections of a pi type
-/
def limit_cone {J : Type u} [small_category J] (F : J ⥤ Type u) : cone F :=
  cone.mk (↥(functor.sections F))
    (nat_trans.mk
      fun (j : J) (u : functor.obj (functor.obj (functor.const J) ↥(functor.sections F)) j) => subtype.val u j)

/-- (internal implementation) the fact that the proposed limit cone is the limit -/
def limit_cone_is_limit {J : Type u} [small_category J] (F : J ⥤ Type u) : is_limit (limit_cone F) :=
  is_limit.mk fun (s : cone F) (v : cone.X s) => { val := fun (j : J) => nat_trans.app (cone.π s) j v, property := sorry }

/--
The category of types has all limits.

See https://stacks.math.columbia.edu/tag/002U.
-/
protected instance sort.category_theory.limits.has_limits : has_limits (Type u) :=
  has_limits.mk
    fun (J : Type u) (𝒥 : small_category J) =>
      has_limits_of_shape.mk fun (F : J ⥤ Type u) => has_limit.mk (limit_cone.mk (limit_cone F) (limit_cone_is_limit F))

/--
The equivalence between a limiting cone of `F` in `Type u` and the "concrete" definition as the
sections of `F`.
-/
def is_limit_equiv_sections {J : Type u} [small_category J] {F : J ⥤ Type u} {c : cone F} (t : is_limit c) : cone.X c ≃ ↥(functor.sections F) :=
  iso.to_equiv (is_limit.cone_point_unique_up_to_iso t (limit_cone_is_limit F))

@[simp] theorem is_limit_equiv_sections_apply {J : Type u} [small_category J] {F : J ⥤ Type u} {c : cone F} (t : is_limit c) (j : J) (x : cone.X c) : coe (coe_fn (is_limit_equiv_sections t) x) j = nat_trans.app (cone.π c) j x :=
  rfl

@[simp] theorem is_limit_equiv_sections_symm_apply {J : Type u} [small_category J] {F : J ⥤ Type u} {c : cone F} (t : is_limit c) (x : ↥(functor.sections F)) (j : J) : nat_trans.app (cone.π c) j (coe_fn (equiv.symm (is_limit_equiv_sections t)) x) = coe x j := sorry

/--
The equivalence between the abstract limit of `F` in `Type u`
and the "concrete" definition as the sections of `F`.
-/
def limit_equiv_sections {J : Type u} [small_category J] (F : J ⥤ Type u) : limit F ≃ ↥(functor.sections F) :=
  is_limit_equiv_sections (limit.is_limit F)

@[simp] theorem limit_equiv_sections_apply {J : Type u} [small_category J] (F : J ⥤ Type u) (x : limit F) (j : J) : coe (coe_fn (limit_equiv_sections F) x) j = limit.π F j x :=
  rfl

@[simp] theorem limit_equiv_sections_symm_apply {J : Type u} [small_category J] (F : J ⥤ Type u) (x : ↥(functor.sections F)) (j : J) : limit.π F j (coe_fn (equiv.symm (limit_equiv_sections F)) x) = coe x j :=
  is_limit_equiv_sections_symm_apply (limit.is_limit F) x j

/--
Construct a term of `limit F : Type u` from a family of terms `x : Π j, F.obj j`
which are "coherent": `∀ (j j') (f : j ⟶ j'), F.map f (x j) = x j'`.
-/
def limit.mk {J : Type u} [small_category J] (F : J ⥤ Type u) (x : (j : J) → functor.obj F j) (h : ∀ (j j' : J) (f : j ⟶ j'), functor.map F f (x j) = x j') : limit F :=
  coe_fn (equiv.symm (limit_equiv_sections F)) { val := x, property := h }

@[simp] theorem limit.π_mk {J : Type u} [small_category J] (F : J ⥤ Type u) (x : (j : J) → functor.obj F j) (h : ∀ (j j' : J) (f : j ⟶ j'), functor.map F f (x j) = x j') (j : J) : limit.π F j (limit.mk F x h) = x j := sorry

-- PROJECT: prove this for concrete categories where the forgetful functor preserves limits

theorem limit_ext {J : Type u} [small_category J] (F : J ⥤ Type u) (x : limit F) (y : limit F) (w : ∀ (j : J), limit.π F j x = limit.π F j y) : x = y := sorry

theorem limit_ext_iff {J : Type u} [small_category J] (F : J ⥤ Type u) (x : limit F) (y : limit F) : x = y ↔ ∀ (j : J), limit.π F j x = limit.π F j y :=
  { mp := fun (t : x = y) (_x : J) => t ▸ rfl, mpr := limit_ext F x y }

-- TODO: are there other limits lemmas that should have `_apply` versions?

-- Can we generate these like with `@[reassoc]`?

-- PROJECT: prove these for any concrete category where the forgetful functor preserves limits?

@[simp] theorem limit.w_apply {J : Type u} [small_category J] {F : J ⥤ Type u} {j : J} {j' : J} {x : limit F} (f : j ⟶ j') : functor.map F f (limit.π F j x) = limit.π F j' x :=
  congr_fun (limit.w F f) x

@[simp] theorem limit.lift_π_apply {J : Type u} [small_category J] (F : J ⥤ Type u) (s : cone F) (j : J) (x : cone.X s) : limit.π F j (limit.lift F s x) = nat_trans.app (cone.π s) j x :=
  congr_fun (limit.lift_π s j) x

@[simp] theorem limit.map_π_apply {J : Type u} [small_category J] {F : J ⥤ Type u} {G : J ⥤ Type u} (α : F ⟶ G) (j : J) (x : limit F) : limit.π G j (lim_map α x) = nat_trans.app α j (limit.π F j x) :=
  congr_fun (lim_map_π α j) x

/--
The relation defining the quotient type which implements the colimit of a functor `F : J ⥤ Type u`.
See `category_theory.limits.types.quot`.
-/
def quot.rel {J : Type u} [small_category J] (F : J ⥤ Type u) : (sigma fun (j : J) => functor.obj F j) → (sigma fun (j : J) => functor.obj F j) → Prop :=
  fun (p p' : sigma fun (j : J) => functor.obj F j) =>
    ∃ (f : sigma.fst p ⟶ sigma.fst p'), sigma.snd p' = functor.map F f (sigma.snd p)

/--
A quotient type implementing the colimit of a functor `F : J ⥤ Type u`,
as pairs `⟨j, x⟩` where `x : F.obj j`, modulo the equivalence relation generated by
`⟨j, x⟩ ~ ⟨j', x'⟩` whenever there is a morphism `f : j ⟶ j'` so `F.map f x = x'`.
-/
def quot {J : Type u} [small_category J] (F : J ⥤ Type u)  :=
  Quot sorry

/--
(internal implementation) the colimit cocone of a functor,
implemented as a quotient of a sigma type
-/
def colimit_cocone {J : Type u} [small_category J] (F : J ⥤ Type u) : cocone F :=
  cocone.mk (quot F) (nat_trans.mk fun (j : J) (x : functor.obj F j) => Quot.mk (quot.rel F) (sigma.mk j x))

/-- (internal implementation) the fact that the proposed colimit cocone is the colimit -/
def colimit_cocone_is_colimit {J : Type u} [small_category J] (F : J ⥤ Type u) : is_colimit (colimit_cocone F) :=
  is_colimit.mk
    fun (s : cocone F) =>
      Quot.lift (fun (p : sigma fun (j : J) => functor.obj F j) => nat_trans.app (cocone.ι s) (sigma.fst p) (sigma.snd p))
        sorry

/--
The category of types has all colimits.

See https://stacks.math.columbia.edu/tag/002U.
-/
protected instance sort.category_theory.limits.has_colimits : has_colimits (Type u) :=
  has_colimits.mk
    fun (J : Type u) (𝒥 : small_category J) =>
      has_colimits_of_shape.mk
        fun (F : J ⥤ Type u) => has_colimit.mk (colimit_cocone.mk (colimit_cocone F) (colimit_cocone_is_colimit F))

/--
The equivalence between the abstract colimit of `F` in `Type u`
and the "concrete" definition as a quotient.
-/
def colimit_equiv_quot {J : Type u} [small_category J] (F : J ⥤ Type u) : colimit F ≃ quot F :=
  iso.to_equiv (is_colimit.cocone_point_unique_up_to_iso (colimit.is_colimit F) (colimit_cocone_is_colimit F))

@[simp] theorem colimit_equiv_quot_symm_apply {J : Type u} [small_category J] (F : J ⥤ Type u) (j : J) (x : functor.obj F j) : coe_fn (equiv.symm (colimit_equiv_quot F)) (Quot.mk (quot.rel F) (sigma.mk j x)) = colimit.ι F j x :=
  rfl

@[simp] theorem colimit_equiv_quot_apply {J : Type u} [small_category J] (F : J ⥤ Type u) (j : J) (x : functor.obj F j) : coe_fn (colimit_equiv_quot F) (colimit.ι F j x) = Quot.mk (quot.rel F) (sigma.mk j x) := sorry

@[simp] theorem colimit.w_apply {J : Type u} [small_category J] {F : J ⥤ Type u} {j : J} {j' : J} {x : functor.obj F j} (f : j ⟶ j') : colimit.ι F j' (functor.map F f x) = colimit.ι F j x :=
  congr_fun (colimit.w F f) x

@[simp] theorem colimit.ι_desc_apply {J : Type u} [small_category J] (F : J ⥤ Type u) (s : cocone F) (j : J) (x : functor.obj F j) : colimit.desc F s (colimit.ι F j x) = nat_trans.app (cocone.ι s) j x :=
  congr_fun (colimit.ι_desc s j) x

@[simp] theorem colimit.ι_map_apply {J : Type u} [small_category J] {F : J ⥤ Type u} {G : J ⥤ Type u} (α : F ⟶ G) (j : J) (x : functor.obj F j) : functor.map colim α (colimit.ι F j x) = colimit.ι G j (nat_trans.app α j x) :=
  congr_fun (colimit.ι_map α j) x

theorem colimit_sound {J : Type u} [small_category J] {F : J ⥤ Type u} {j : J} {j' : J} {x : functor.obj F j} {x' : functor.obj F j'} (f : j ⟶ j') (w : functor.map F f x = x') : colimit.ι F j x = colimit.ι F j' x' := sorry

theorem colimit_sound' {J : Type u} [small_category J] {F : J ⥤ Type u} {j : J} {j' : J} {x : functor.obj F j} {x' : functor.obj F j'} {j'' : J} (f : j ⟶ j'') (f' : j' ⟶ j'') (w : functor.map F f x = functor.map F f' x') : colimit.ι F j x = colimit.ι F j' x' := sorry

theorem colimit_eq {J : Type u} [small_category J] {F : J ⥤ Type u} {j : J} {j' : J} {x : functor.obj F j} {x' : functor.obj F j'} (w : colimit.ι F j x = colimit.ι F j' x') : eqv_gen (quot.rel F) (sigma.mk j x) (sigma.mk j' x') := sorry

theorem jointly_surjective {J : Type u} [small_category J] (F : J ⥤ Type u) {t : cocone F} (h : is_colimit t) (x : cocone.X t) : ∃ (j : J), ∃ (y : functor.obj F j), nat_trans.app (cocone.ι t) j y = x := sorry

/-- A variant of `jointly_surjective` for `x : colimit F`. -/
theorem jointly_surjective' {J : Type u} [small_category J] {F : J ⥤ Type u} (x : colimit F) : ∃ (j : J), ∃ (y : functor.obj F j), colimit.ι F j y = x :=
  jointly_surjective F (colimit.is_colimit F) x

namespace filtered_colimit


/- For filtered colimits of types, we can give an explicit description
  of the equivalence relation generated by the relation used to form
  the colimit.  -/

/--
An alternative relation on `Σ j, F.obj j`,
which generates the same equivalence relation as we use to define the colimit in `Type` above,
but that is more convenient when working with filtered colimits.

Elements in `F.obj j` and `F.obj j'` are equivalent if there is some `k : J` to the right
where their images are equal.
-/
protected def r {J : Type u} [small_category J] (F : J ⥤ Type u) (x : sigma fun (j : J) => functor.obj F j) (y : sigma fun (j : J) => functor.obj F j)  :=
  ∃ (k : J),
    ∃ (f : sigma.fst x ⟶ k), ∃ (g : sigma.fst y ⟶ k), functor.map F f (sigma.snd x) = functor.map F g (sigma.snd y)

protected theorem r_ge {J : Type u} [small_category J] (F : J ⥤ Type u) (x : sigma fun (j : J) => functor.obj F j) (y : sigma fun (j : J) => functor.obj F j) : (∃ (f : sigma.fst x ⟶ sigma.fst y), sigma.snd y = functor.map F f (sigma.snd x)) → filtered_colimit.r F x y := sorry

/-- Recognizing filtered colimits of types. -/
def is_colimit_of {J : Type u} [small_category J] (F : J ⥤ Type u) (t : cocone F) (hsurj : ∀ (x : cocone.X t), ∃ (i : J), ∃ (xi : functor.obj F i), x = nat_trans.app (cocone.ι t) i xi) (hinj : ∀ (i j : J) (xi : functor.obj F i) (xj : functor.obj F j),
  nat_trans.app (cocone.ι t) i xi = nat_trans.app (cocone.ι t) j xj →
    ∃ (k : J), ∃ (f : i ⟶ k), ∃ (g : j ⟶ k), functor.map F f xi = functor.map F g xj) : is_colimit t :=
  is_colimit.of_iso_colimit (colimit.is_colimit F)
    (cocones.ext (equiv.to_iso (equiv.of_bijective (colimit.desc F t) sorry)) sorry)

-- Strategy: Prove that the map from "the" colimit of F (defined above) to t.X

-- is a bijection.

protected theorem r_equiv {J : Type u} [small_category J] (F : J ⥤ Type u) [is_filtered_or_empty J] : equivalence (filtered_colimit.r F) := sorry

protected theorem r_eq {J : Type u} [small_category J] (F : J ⥤ Type u) [is_filtered_or_empty J] : filtered_colimit.r F =
  eqv_gen
    fun (x y : sigma fun (j : J) => functor.obj F j) =>
      ∃ (f : sigma.fst x ⟶ sigma.fst y), sigma.snd y = functor.map F f (sigma.snd x) := sorry

theorem colimit_eq_iff_aux {J : Type u} [small_category J] (F : J ⥤ Type u) [is_filtered_or_empty J] {i : J} {j : J} {xi : functor.obj F i} {xj : functor.obj F j} : nat_trans.app (cocone.ι (colimit_cocone F)) i xi = nat_trans.app (cocone.ι (colimit_cocone F)) j xj ↔
  ∃ (k : J), ∃ (f : i ⟶ k), ∃ (g : j ⟶ k), functor.map F f xi = functor.map F g xj := sorry

theorem is_colimit_eq_iff {J : Type u} [small_category J] (F : J ⥤ Type u) {t : cocone F} [is_filtered_or_empty J] (ht : is_colimit t) {i : J} {j : J} {xi : functor.obj F i} {xj : functor.obj F j} : nat_trans.app (cocone.ι t) i xi = nat_trans.app (cocone.ι t) j xj ↔
  ∃ (k : J), ∃ (f : i ⟶ k), ∃ (g : j ⟶ k), functor.map F f xi = functor.map F g xj := sorry

theorem colimit_eq_iff {J : Type u} [small_category J] (F : J ⥤ Type u) [is_filtered_or_empty J] {i : J} {j : J} {xi : functor.obj F i} {xj : functor.obj F j} : colimit.ι F i xi = colimit.ι F j xj ↔ ∃ (k : J), ∃ (f : i ⟶ k), ∃ (g : j ⟶ k), functor.map F f xi = functor.map F g xj :=
  is_colimit_eq_iff F (colimit.is_colimit F)

end filtered_colimit


/-- the image of a morphism in Type is just `set.range f` -/
def image {α : Type u} {β : Type u} (f : α ⟶ β)  :=
  ↥(set.range f)

protected instance image.inhabited {α : Type u} {β : Type u} (f : α ⟶ β) [Inhabited α] : Inhabited (image f) :=
  { default := { val := f Inhabited.default, property := sorry } }

/-- the inclusion of `image f` into the target -/
def image.ι {α : Type u} {β : Type u} (f : α ⟶ β) : image f ⟶ β :=
  subtype.val

protected instance image.ι.category_theory.mono {α : Type u} {β : Type u} (f : α ⟶ β) : mono (image.ι f) :=
  iff.mpr (mono_iff_injective (image.ι f)) subtype.val_injective

/-- the universal property for the image factorisation -/
def image.lift {α : Type u} {β : Type u} {f : α ⟶ β} (F' : mono_factorisation f) : image f ⟶ mono_factorisation.I F' :=
  fun (x : image f) =>
    mono_factorisation.e F'
      (subtype.val (classical.indefinite_description (fun (x_1 : α) => f x_1 = subtype.val x) sorry))

theorem image.lift_fac {α : Type u} {β : Type u} {f : α ⟶ β} (F' : mono_factorisation f) : image.lift F' ≫ mono_factorisation.m F' = image.ι f := sorry

/-- the factorisation of any morphism in Type through a mono. -/
def mono_factorisation {α : Type u} {β : Type u} (f : α ⟶ β) : mono_factorisation f :=
  mono_factorisation.mk (image f) (image.ι f) (set.range_factorization f)

/-- the facorisation through a mono has the universal property of the image. -/
def is_image {α : Type u} {β : Type u} (f : α ⟶ β) : is_image (mono_factorisation f) :=
  is_image.mk image.lift

protected instance category_theory.limits.has_image {α : Type u} {β : Type u} (f : α ⟶ β) : has_image f :=
  has_image.mk (image_factorisation.mk (mono_factorisation f) (is_image f))

protected instance sort.category_theory.limits.has_images : has_images (Type u) :=
  has_images.mk sorry

protected instance sort.category_theory.limits.has_image_maps : has_image_maps (Type u) :=
  has_image_maps.mk sorry

