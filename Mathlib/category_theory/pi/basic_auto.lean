/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.natural_isomorphism
import Mathlib.category_theory.eq_to_hom
import Mathlib.PostPort

universes u₁ v₁ w₀ w₁ w₂ 

namespace Mathlib

/-!
# Categories of indexed families of objects.

We define the pointwise category structure on indexed families of objects in a category
(and also the dependent generalization).

-/

namespace category_theory


/--
`pi C` gives the cartesian product of an indexed family of categories.
-/
protected instance pi {I : Type w₀} (C : I → Type u₁) [(i : I) → category (C i)] :
    category ((i : I) → C i) :=
  category.mk

/--
This provides some assistance to typeclass search in a common situation,
which otherwise fails. (Without this `category_theory.pi.has_limit_of_has_limit_comp_eval` fails.)
-/
instance pi' {I : Type v₁} (C : I → Type u₁) [(i : I) → category (C i)] :
    category ((i : I) → C i) :=
  category_theory.pi C

namespace pi


@[simp] theorem id_apply {I : Type w₀} (C : I → Type u₁) [(i : I) → category (C i)]
    (X : (i : I) → C i) (i : I) : 𝟙 = 𝟙 :=
  rfl

@[simp] theorem comp_apply {I : Type w₀} (C : I → Type u₁) [(i : I) → category (C i)]
    {X : (i : I) → C i} {Y : (i : I) → C i} {Z : (i : I) → C i} (f : X ⟶ Y) (g : Y ⟶ Z) (i : I) :
    category_struct.comp f g i = f i ≫ g i :=
  rfl

/--
The evaluation functor at `i : I`, sending an `I`-indexed family of objects to the object over `i`.
-/
@[simp] theorem eval_map {I : Type w₀} (C : I → Type u₁) [(i : I) → category (C i)] (i : I)
    (f : (i : I) → C i) (g : (i : I) → C i) (α : f ⟶ g) : functor.map (eval C i) α = α i :=
  Eq.refl (functor.map (eval C i) α)

/--
Pull back an `I`-indexed family of objects to an `J`-indexed family, along a function `J → I`.
-/
@[simp] theorem comap_map {I : Type w₀} (C : I → Type u₁) [(i : I) → category (C i)] {J : Type w₁}
    (h : J → I) (f : (i : I) → C i) (g : (i : I) → C i) (α : f ⟶ g) (i : J) :
    functor.map (comap C h) α i = α (h i) :=
  Eq.refl (functor.map (comap C h) α i)

/--
The natural isomorphism between
pulling back a grading along the identity function,
and the identity functor. -/
def comap_id (I : Type w₀) (C : I → Type u₁) [(i : I) → category (C i)] : comap C id ≅ 𝟭 :=
  iso.mk (nat_trans.mk fun (X : (i : I) → C i) => 𝟙) (nat_trans.mk fun (X : (i : I) → C i) => 𝟙)

/--
The natural isomorphism comparing between
pulling back along two successive functions, and
pulling back along their composition
-/
def comap_comp {I : Type w₀} (C : I → Type u₁) [(i : I) → category (C i)] {J : Type w₁}
    {K : Type w₂} (f : K → J) (g : J → I) : comap C g ⋙ comap (C ∘ g) f ≅ comap C (g ∘ f) :=
  iso.mk (nat_trans.mk fun (X : (i : I) → C i) (b : K) => 𝟙)
    (nat_trans.mk fun (X : (i : I) → C i) (b : K) => 𝟙)

/-- The natural isomorphism between pulling back then evaluating, and just evaluating. -/
def comap_eval_iso_eval {I : Type w₀} (C : I → Type u₁) [(i : I) → category (C i)] {J : Type w₁}
    (h : J → I) (j : J) : comap C h ⋙ eval (C ∘ h) j ≅ eval C (h j) :=
  nat_iso.of_components
    (fun (f : (i : I) → C i) => iso.refl (functor.obj (comap C h ⋙ eval (C ∘ h) j) f)) sorry

protected instance sum_elim_category {I : Type w₀} (C : I → Type u₁) [(i : I) → category (C i)]
    {J : Type w₀} {D : J → Type u₁} [(j : J) → category (D j)] (s : I ⊕ J) :
    category (sum.elim C D s) :=
  sorry

/--
The bifunctor combining an `I`-indexed family of objects with a `J`-indexed family of objects
to obtain an `I ⊕ J`-indexed family of objects.
-/
@[simp] theorem sum_obj_obj {I : Type w₀} (C : I → Type u₁) [(i : I) → category (C i)] {J : Type w₀}
    {D : J → Type u₁} [(j : J) → category (D j)] (f : (i : I) → C i) (g : (j : J) → D j)
    (s : I ⊕ J) : functor.obj (functor.obj (sum C) f) g s = sum.rec f g s :=
  Eq.refl (functor.obj (functor.obj (sum C) f) g s)

end pi


namespace functor


/--
Assemble an `I`-indexed family of functors into a functor between the pi types.
-/
def pi {I : Type w₀} {C : I → Type u₁} [(i : I) → category (C i)] {D : I → Type u₁}
    [(i : I) → category (D i)] (F : (i : I) → C i ⥤ D i) : ((i : I) → C i) ⥤ ((i : I) → D i) :=
  mk (fun (f : (i : I) → C i) (i : I) => obj (F i) (f i))
    fun (f g : (i : I) → C i) (α : f ⟶ g) (i : I) => map (F i) (α i)

-- One could add some natural isomorphisms showing

-- how `functor.pi` commutes with `pi.eval` and `pi.comap`.

end functor


namespace nat_trans


/--
Assemble an `I`-indexed family of natural transformations into a single natural transformation.
-/
def pi {I : Type w₀} {C : I → Type u₁} [(i : I) → category (C i)] {D : I → Type u₁}
    [(i : I) → category (D i)] {F : (i : I) → C i ⥤ D i} {G : (i : I) → C i ⥤ D i}
    (α : (i : I) → F i ⟶ G i) : functor.pi F ⟶ functor.pi G :=
  mk fun (f : (i : I) → C i) (i : I) => app (α i) (f i)

end Mathlib