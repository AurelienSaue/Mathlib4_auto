/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.sites.canonical
import Mathlib.category_theory.sites.sheaf_of_types
import Mathlib.PostPort

universes u u_1 

namespace Mathlib

/-!
# Grothendieck Topology and Sheaves on the Category of Types

In this file we define a Grothendieck topology on the category of types,
and construct the canonical functor that sends a type to a sheaf over
the category of types, and make this an equivalence of categories.

Then we prove that the topology defined is the canonical topology.
-/

namespace category_theory


/-- A Grothendieck topology associated to the category of all types.
A sieve is a covering iff it is jointly surjective. -/
def types_grothendieck_topology : grothendieck_topology (Type u) :=
  grothendieck_topology.mk (fun (α : Type u) (S : sieve α) => ∀ (x : α), coe_fn S PUnit fun (_x : PUnit) => x) sorry sorry
    sorry

/-- The discrete sieve on a type, which only includes arrows whose image is a subsingleton. -/
@[simp] theorem discrete_sieve_apply (α : Type u) (β : Type u) (f : β ⟶ α) : coe_fn (discrete_sieve α) β f = ∃ (x : α), ∀ (y : β), f y = x :=
  Eq.refl (coe_fn (discrete_sieve α) β f)

theorem discrete_sieve_mem (α : Type u) : discrete_sieve α ∈ coe_fn types_grothendieck_topology α :=
  fun (x : α) => Exists.intro x fun (y : PUnit) => rfl

/-- The discrete presieve on a type, which only includes arrows whose domain is a singleton. -/
def discrete_presieve (α : Type u) : presieve α :=
  fun (β : Type u) (f : β ⟶ α) => ∃ (x : β), ∀ (y : β), y = x

theorem generate_discrete_presieve_mem (α : Type u) : sieve.generate (discrete_presieve α) ∈ coe_fn types_grothendieck_topology α := sorry

theorem is_sheaf_yoneda' {α : Type u} : presieve.is_sheaf types_grothendieck_topology (functor.obj yoneda α) := sorry

/-- The yoneda functor that sends a type to a sheaf over the category of types -/
@[simp] theorem yoneda'_map (α : Type u) (β : Type u) (f : α ⟶ β) : functor.map yoneda' f = functor.map yoneda f :=
  Eq.refl (functor.map yoneda' f)

@[simp] theorem yoneda'_comp : yoneda' ⋙ induced_functor subtype.val = yoneda :=
  rfl

/-- Given a presheaf `P` on the category of types, construct
a map `P(α) → (α → P(*))` for all type `α`. -/
def eval (P : Type uᵒᵖ ⥤ Type u) (α : Type u) (s : functor.obj P (opposite.op α)) (x : α) : functor.obj P (opposite.op PUnit) :=
  functor.map P (has_hom.hom.op (↾fun (_x : PUnit) => x)) s

/-- Given a sheaf `S` on the category of types, construct a map
`(α → S(*)) → S(α)` that is inverse to `eval`. -/
def types_glue (S : Type uᵒᵖ ⥤ Type u) (hs : presieve.is_sheaf types_grothendieck_topology S) (α : Type u) (f : α → functor.obj S (opposite.op PUnit)) : functor.obj S (opposite.op α) :=
  presieve.is_sheaf_for.amalgamate sorry
    (fun (β : Type u) (g : β ⟶ α) (hg : discrete_presieve α g) =>
      functor.map S (has_hom.hom.op (↾fun (x : β) => PUnit.unit)) (f (g (classical.some hg))))
    sorry

theorem eval_types_glue {S : Type uᵒᵖ ⥤ Type u} {hs : presieve.is_sheaf types_grothendieck_topology S} {α : Type u} (f : α → functor.obj S (opposite.op PUnit)) : eval S α (types_glue S hs α f) = f := sorry

theorem types_glue_eval {S : Type uᵒᵖ ⥤ Type u} {hs : presieve.is_sheaf types_grothendieck_topology S} {α : Type u} (s : functor.obj S (opposite.op α)) : types_glue S hs α (eval S α s) = s := sorry

/-- Given a sheaf `S`, construct an equivalence `S(α) ≃ (α → S(*))`. -/
def eval_equiv (S : Type uᵒᵖ ⥤ Type u) (hs : presieve.is_sheaf types_grothendieck_topology S) (α : Type u) : functor.obj S (opposite.op α) ≃ (α → functor.obj S (opposite.op PUnit)) :=
  equiv.mk (eval S α) (types_glue S hs α) types_glue_eval eval_types_glue

theorem eval_map (S : Type uᵒᵖ ⥤ Type u) (α : Type u) (β : Type u) (f : β ⟶ α) (s : functor.obj S (opposite.op α)) (x : β) : eval S β (functor.map S (has_hom.hom.op f) s) x = eval S α s (f x) := sorry

/-- Given a sheaf `S`, construct an isomorphism `S ≅ [-, S(*)]`. -/
def equiv_yoneda (S : Type uᵒᵖ ⥤ Type u) (hs : presieve.is_sheaf types_grothendieck_topology S) : S ≅ functor.obj yoneda (functor.obj S (opposite.op PUnit)) :=
  nat_iso.of_components (fun (α : Type uᵒᵖ) => equiv.to_iso (eval_equiv S hs (opposite.unop α))) sorry

/-- Given a sheaf `S`, construct an isomorphism `S ≅ [-, S(*)]`. -/
@[simp] theorem equiv_yoneda'_inv (S : SheafOfTypes types_grothendieck_topology) : iso.inv (equiv_yoneda' S) = iso.inv (equiv_yoneda (subtype.val S) (equiv_yoneda'._proof_1 S)) :=
  Eq.refl (iso.inv (equiv_yoneda' S))

theorem eval_app (S₁ : SheafOfTypes types_grothendieck_topology) (S₂ : SheafOfTypes types_grothendieck_topology) (f : S₁ ⟶ S₂) (α : Type u) (s : functor.obj (subtype.val S₁) (opposite.op α)) (x : α) : eval (subtype.val S₂) α (nat_trans.app f (opposite.op α) s) x =
  nat_trans.app f (opposite.op PUnit) (eval (subtype.val S₁) α s x) :=
  Eq.symm (congr_fun (nat_trans.naturality' f (has_hom.hom.op (↾fun (_x : PUnit) => x))) s)

/-- `yoneda'` induces an equivalence of category between `Type u` and
`Sheaf types_grothendieck_topology`. -/
@[simp] theorem type_equiv_inverse_obj (X : SheafOfTypes types_grothendieck_topology) : functor.obj (equivalence.inverse type_equiv) X = functor.obj (↑X) (opposite.op PUnit) :=
  Eq.refl (functor.obj (↑X) (opposite.op PUnit))

theorem subcanonical_types_grothendieck_topology : sheaf.subcanonical types_grothendieck_topology :=
  sheaf.subcanonical.of_yoneda_is_sheaf types_grothendieck_topology fun (X : Type u) => is_sheaf_yoneda'

theorem types_grothendieck_topology_eq_canonical : types_grothendieck_topology = sheaf.canonical_topology (Type u) := sorry

