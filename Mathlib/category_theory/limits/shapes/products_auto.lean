/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.limits.limits
import Mathlib.category_theory.discrete_category
import PostPort

universes v u u_1 u₂ 

namespace Mathlib

namespace category_theory.limits


-- We don't need an analogue of `pair` (for binary products), `parallel_pair` (for equalizers),

-- or `(co)span`, since we already have `discrete.functor`.

/-- A fan over `f : β → C` consists of a collection of maps from an object `P` to every `f b`. -/
/-- A cofan over `f : β → C` consists of a collection of maps from every `f b` to an object `P`. -/
def fan {β : Type v} {C : Type u} [category C] (f : β → C)  :=
  cone (discrete.functor f)

def cofan {β : Type v} {C : Type u} [category C] (f : β → C)  :=
  cocone (discrete.functor f)

/-- A fan over `f : β → C` consists of a collection of maps from an object `P` to every `f b`. -/
@[simp] theorem fan.mk_X {β : Type v} {C : Type u} [category C] {f : β → C} (P : C) (p : (b : β) → P ⟶ f b) : cone.X (fan.mk P p) = P :=
  Eq.refl (cone.X (fan.mk P p))

/-- A cofan over `f : β → C` consists of a collection of maps from every `f b` to an object `P`. -/
@[simp] theorem cofan.mk_X {β : Type v} {C : Type u} [category C] {f : β → C} (P : C) (p : (b : β) → f b ⟶ P) : cocone.X (cofan.mk P p) = P :=
  Eq.refl (cocone.X (cofan.mk P p))

/-- An abbreviation for `has_limit (discrete.functor f)`. -/
def has_product {β : Type v} {C : Type u} [category C] (f : β → C)  :=
  has_limit (discrete.functor f)

/-- An abbreviation for `has_colimit (discrete.functor f)`. -/
def has_coproduct {β : Type v} {C : Type u} [category C] (f : β → C)  :=
  has_colimit (discrete.functor f)

/-- An abbreviation for `has_limits_of_shape (discrete f)`. -/
/-- An abbreviation for `has_colimits_of_shape (discrete f)`. -/
def has_products_of_shape (β : Type v) (C : Type u_1) [category C]  :=
  has_limits_of_shape (discrete β)

def has_coproducts_of_shape (β : Type v) (C : Type u_1) [category C]  :=
  has_colimits_of_shape (discrete β)

/-- `pi_obj f` computes the product of a family of elements `f`. (It is defined as an abbreviation
   for `limit (discrete.functor f)`, so for most facts about `pi_obj f`, you will just use general facts
   about limits.) -/
/-- `sigma_obj f` computes the coproduct of a family of elements `f`. (It is defined as an abbreviation
def pi_obj {β : Type v} {C : Type u} [category C] (f : β → C) [has_product f] : C :=
  limit (discrete.functor f)

   for `colimit (discrete.functor f)`, so for most facts about `sigma_obj f`, you will just use general facts
   about colimits.) -/
def sigma_obj {β : Type v} {C : Type u} [category C] (f : β → C) [has_coproduct f] : C :=
  colimit (discrete.functor f)

prefix:20 "∏ " => Mathlib.category_theory.limits.pi_obj

prefix:20 "∐ " => Mathlib.category_theory.limits.sigma_obj

/-- The `b`-th projection from the pi object over `f` has the form `∏ f ⟶ f b`. -/
def pi.π {β : Type v} {C : Type u} [category C] (f : β → C) [has_product f] (b : β) : ∏ f ⟶ f b :=
  limit.π (discrete.functor f) b

/-- The `b`-th inclusion into the sigma object over `f` has the form `f b ⟶ ∐ f`. -/
def sigma.ι {β : Type v} {C : Type u} [category C] (f : β → C) [has_coproduct f] (b : β) : f b ⟶ ∐ f :=
  colimit.ι (discrete.functor f) b

/-- The fan constructed of the projections from the product is limiting. -/
def product_is_product {β : Type v} {C : Type u} [category C] (f : β → C) [has_product f] : is_limit (fan.mk (∏ f) (pi.π f)) :=
  is_limit.of_iso_limit (limit.is_limit (discrete.functor f))
    (cones.ext (iso.refl (cone.X (limit.cone (discrete.functor fun (b : β) => f b)))) sorry)

/-- A collection of morphisms `P ⟶ f b` induces a morphism `P ⟶ ∏ f`. -/
def pi.lift {β : Type v} {C : Type u} [category C] {f : β → C} [has_product f] {P : C} (p : (b : β) → P ⟶ f b) : P ⟶ ∏ f :=
  limit.lift (discrete.functor fun (b : β) => f b) (fan.mk P p)

/-- A collection of morphisms `f b ⟶ P` induces a morphism `∐ f ⟶ P`. -/
def sigma.desc {β : Type v} {C : Type u} [category C] {f : β → C} [has_coproduct f] {P : C} (p : (b : β) → f b ⟶ P) : ∐ f ⟶ P :=
  colimit.desc (discrete.functor fun (b : β) => f b) (cofan.mk P p)

/--
Construct a morphism between categorical products (indexed by the same type)
from a family of morphisms between the factors.
-/
def pi.map {β : Type v} {C : Type u} [category C] {f : β → C} {g : β → C} [has_product f] [has_product g] (p : (b : β) → f b ⟶ g b) : ∏ f ⟶ ∏ g :=
  lim_map (discrete.nat_trans p)

/--
Construct an isomorphism between categorical products (indexed by the same type)
from a family of isomorphisms between the factors.
-/
def pi.map_iso {β : Type v} {C : Type u} [category C] {f : β → C} {g : β → C} [has_products_of_shape β C] (p : (b : β) → f b ≅ g b) : ∏ f ≅ ∏ g :=
  functor.map_iso lim (discrete.nat_iso p)

/--
Construct a morphism between categorical coproducts (indexed by the same type)
from a family of morphisms between the factors.
-/
def sigma.map {β : Type v} {C : Type u} [category C] {f : β → C} {g : β → C} [has_coproduct f] [has_coproduct g] (p : (b : β) → f b ⟶ g b) : ∐ f ⟶ ∐ g :=
  colim_map (discrete.nat_trans p)

/--
Construct an isomorphism between categorical coproducts (indexed by the same type)
from a family of isomorphisms between the factors.
-/
def sigma.map_iso {β : Type v} {C : Type u} [category C] {f : β → C} {g : β → C} [has_coproducts_of_shape β C] (p : (b : β) → f b ≅ g b) : ∐ f ≅ ∐ g :=
  functor.map_iso colim (discrete.nat_iso p)

-- TODO: show this is an iso iff G preserves the product of f.

/-- The comparison morphism for the product of `f`. -/
def pi_comparison {β : Type v} {C : Type u} [category C] {D : Type u₂} [category D] (G : C ⥤ D) (f : β → C) [has_product f] [has_product fun (b : β) => functor.obj G (f b)] : functor.obj G (∏ f) ⟶ ∏ fun (b : β) => functor.obj G (f b) :=
  pi.lift fun (b : β) => functor.map G (pi.π f b)

@[simp] theorem pi_comparison_comp_π_assoc {β : Type v} {C : Type u} [category C] {D : Type u₂} [category D] (G : C ⥤ D) (f : β → C) [has_product f] [has_product fun (b : β) => functor.obj G (f b)] (b : β) {X' : D} (f' : functor.obj G (f b) ⟶ X') : pi_comparison G f ≫ pi.π (fun (b : β) => functor.obj G (f b)) b ≫ f' = functor.map G (pi.π f b) ≫ f' := sorry

@[simp] theorem map_lift_pi_comparison_assoc {β : Type v} {C : Type u} [category C] {D : Type u₂} [category D] (G : C ⥤ D) (f : β → C) [has_product f] [has_product fun (b : β) => functor.obj G (f b)] (P : C) (g : (j : β) → P ⟶ f j) {X' : D} (f' : (∏ fun (b : β) => functor.obj G (f b)) ⟶ X') : functor.map G (pi.lift g) ≫ pi_comparison G f ≫ f' = (pi.lift fun (j : β) => functor.map G (g j)) ≫ f' := sorry

-- TODO: show this is an iso iff G preserves the coproduct of f.

/-- The comparison morphism for the coproduct of `f`. -/
def sigma_comparison {β : Type v} {C : Type u} [category C] {D : Type u₂} [category D] (G : C ⥤ D) (f : β → C) [has_coproduct f] [has_coproduct fun (b : β) => functor.obj G (f b)] : (∐ fun (b : β) => functor.obj G (f b)) ⟶ functor.obj G (∐ f) :=
  sigma.desc fun (b : β) => functor.map G (sigma.ι f b)

@[simp] theorem ι_comp_sigma_comparison_assoc {β : Type v} {C : Type u} [category C] {D : Type u₂} [category D] (G : C ⥤ D) (f : β → C) [has_coproduct f] [has_coproduct fun (b : β) => functor.obj G (f b)] (b : β) {X' : D} (f' : functor.obj G (∐ f) ⟶ X') : sigma.ι (fun (b : β) => functor.obj G (f b)) b ≫ sigma_comparison G f ≫ f' = functor.map G (sigma.ι f b) ≫ f' := sorry

@[simp] theorem sigma_comparison_map_desc {β : Type v} {C : Type u} [category C] {D : Type u₂} [category D] (G : C ⥤ D) (f : β → C) [has_coproduct f] [has_coproduct fun (b : β) => functor.obj G (f b)] (P : C) (g : (j : β) → f j ⟶ P) : sigma_comparison G f ≫ functor.map G (sigma.desc g) = sigma.desc fun (j : β) => functor.map G (g j) := sorry

/-- An abbreviation for `Π J, has_limits_of_shape (discrete J) C` -/
/-- An abbreviation for `Π J, has_colimits_of_shape (discrete J) C` -/
def has_products (C : Type u) [category C]  :=
  ∀ (J : Type v), has_limits_of_shape (discrete J) C

def has_coproducts (C : Type u) [category C]  :=
  ∀ (J : Type v), has_colimits_of_shape (discrete J) C

