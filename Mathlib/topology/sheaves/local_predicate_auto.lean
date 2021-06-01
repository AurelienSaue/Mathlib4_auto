/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison, Adam Topaz
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.sheaves.sheaf_of_functions
import Mathlib.topology.sheaves.stalks
import Mathlib.PostPort

universes v l 

namespace Mathlib

/-!
# Functions satisfying a local predicate form a sheaf.

At this stage, in `topology/sheaves/sheaf_of_functions.lean`
we've proved that not-necessarily-continuous functions from a topological space
into some type (or type family) form a sheaf.

Why do the continuous functions form a sheaf?
The point is just that continuity is a local condition,
so one can use the lifting condition for functions to provide a candidate lift,
then verify that the lift is actually continuous by using the factorisation condition for the lift
(which guarantees that on each open set it agrees with the functions being lifted,
which were assumed to be continuous).

This file abstracts this argument to work for
any collection of dependent functions on a topological space
satisfying a "local predicate".

As an application, we check that continuity is a local predicate in this sense, and provide
* `Top.sheaf_condition.to_Top`: continuous functions into a topological space form a sheaf

A sheaf constructed in this way has a natural map `stalk_to_fiber` from the stalks
to the types in the ambient type family.

We give conditions sufficient to show that this map is injective and/or surjective.
-/

namespace Top


/--
Given a topological space `X : Top` and a type family `T : X → Type`,
a `P : prelocal_predicate T` consists of:
* a family of predicates `P.pred`, one for each `U : opens X`, of the form `(Π x : U, T x) → Prop`
* a proof that if `f : Π x : V, T x` satisfies the predicate on `V : opens X`, then
  the restriction of `f` to any open subset `U` also satisfies the predicate.
-/
structure prelocal_predicate {X : Top} (T : ↥X → Type v) where
  pred : {U : topological_space.opens ↥X} → ((x : ↥U) → T ↑x) → Prop
  res :
    ∀ {U V : topological_space.opens ↥X} (i : U ⟶ V) (f : (x : ↥V) → T ↑x),
      pred f → pred fun (x : ↥U) => f (coe_fn i x)

/--
Continuity is a "prelocal" predicate on functions to a fixed topological space `T`.
-/
@[simp] theorem continuous_prelocal_pred (X : Top) (T : Top) (U : topological_space.opens ↥X)
    (f : ↥U → ↥T) : prelocal_predicate.pred (continuous_prelocal X T) f = continuous f :=
  Eq.refl (prelocal_predicate.pred (continuous_prelocal X T) f)

/-- Satisfying the inhabited linter. -/
protected instance inhabited_prelocal_predicate (X : Top) (T : Top) :
    Inhabited (prelocal_predicate fun (x : ↥X) => ↥T) :=
  { default := continuous_prelocal X T }

/--
Given a topological space `X : Top` and a type family `T : X → Type`,
a `P : local_predicate T` consists of:
* a family of predicates `P.pred`, one for each `U : opens X`, of the form `(Π x : U, T x) → Prop`
* a proof that if `f : Π x : V, T x` satisfies the predicate on `V : opens X`, then
  the restriction of `f` to any open subset `U` also satisfies the predicate, and
* a proof that given some `f : Π x : U, T x`,
  if for every `x : U` we can find an open set `x ∈ V ≤ U`
  so that the restriction of `f` to `V` satisfies the predicate,
  then `f` itself satisfies the predicate.
-/
structure local_predicate {X : Top} (T : ↥X → Type v) extends prelocal_predicate T where
  locality :
    ∀ {U : topological_space.opens ↥X} (f : (x : ↥U) → T ↑x),
      (∀ (x : ↥U),
          ∃ (V : topological_space.opens ↥X),
            ∃ (m : subtype.val x ∈ V),
              ∃ (i : V ⟶ U),
                prelocal_predicate.pred _to_prelocal_predicate fun (x : ↥V) => f (coe_fn i x)) →
        prelocal_predicate.pred _to_prelocal_predicate f

/--
Continuity is a "local" predicate on functions to a fixed topological space `T`.
-/
def continuous_local (X : Top) (T : Top) : local_predicate fun (x : ↥X) => ↥T :=
  local_predicate.mk
    (prelocal_predicate.mk (prelocal_predicate.pred (continuous_prelocal X T)) sorry) sorry

/-- Satisfying the inhabited linter. -/
protected instance inhabited_local_predicate (X : Top) (T : Top) :
    Inhabited (local_predicate fun (x : ↥X) => ↥T) :=
  { default := continuous_local X T }

/--
Given a `P : prelocal_predicate`, we can always construct a `local_predicate`
by asking that the condition from `P` holds locally near every point.
-/
def prelocal_predicate.sheafify {X : Top} {T : ↥X → Type v} (P : prelocal_predicate T) :
    local_predicate T :=
  local_predicate.mk
    (prelocal_predicate.mk
      (fun (U : topological_space.opens ↥X) (f : (x : ↥U) → T ↑x) =>
        ∀ (x : ↥U),
          ∃ (V : topological_space.opens ↥X),
            ∃ (m : subtype.val x ∈ V),
              ∃ (i : V ⟶ U), prelocal_predicate.pred P fun (x : ↥V) => f (coe_fn i x))
      sorry)
    sorry

theorem prelocal_predicate.sheafify_of {X : Top} {T : ↥X → Type v} {P : prelocal_predicate T}
    {U : topological_space.opens ↥X} {f : (x : ↥U) → T ↑x} (h : prelocal_predicate.pred P f) :
    prelocal_predicate.pred (local_predicate.to_prelocal_predicate (prelocal_predicate.sheafify P))
        f :=
  sorry

/--
The subpresheaf of dependent functions on `X` satisfying the "pre-local" predicate `P`.
-/
def subpresheaf_to_Types {X : Top} {T : ↥X → Type v} (P : prelocal_predicate T) :
    presheaf (Type v) X :=
  category_theory.functor.mk
    (fun (U : topological_space.opens ↥Xᵒᵖ) =>
      Subtype fun (f : (x : ↥(opposite.unop U)) → T ↑x) => prelocal_predicate.pred P f)
    fun (U V : topological_space.opens ↥Xᵒᵖ) (i : U ⟶ V)
      (f : Subtype fun (f : (x : ↥(opposite.unop U)) → T ↑x) => prelocal_predicate.pred P f) =>
      { val :=
          fun (x : ↥(opposite.unop V)) =>
            subtype.val f (coe_fn (category_theory.has_hom.hom.unop i) x),
        property := sorry }

namespace subpresheaf_to_Types


/--
The natural transformation including the subpresheaf of functions satisfying a local predicate
into the presheaf of all functions.
-/
def subtype {X : Top} {T : ↥X → Type v} (P : prelocal_predicate T) :
    subpresheaf_to_Types P ⟶ presheaf_to_Types X T :=
  category_theory.nat_trans.mk
    fun (U : topological_space.opens ↥Xᵒᵖ)
      (f : category_theory.functor.obj (subpresheaf_to_Types P) U) => subtype.val f

/--
The natural transformation
from the sheaf condition diagram for functions satisfying a local predicate
to the sheaf condition diagram for arbitrary functions,
given by forgetting that the local predicate holds.
-/
def diagram_subtype {X : Top} {T : ↥X → Type v} (P : prelocal_predicate T) {ι : Type v}
    (U : ι → topological_space.opens ↥X) :
    presheaf.sheaf_condition_equalizer_products.diagram (subpresheaf_to_Types P) U ⟶
        presheaf.sheaf_condition_equalizer_products.diagram (presheaf_to_Types X T) U :=
  category_theory.nat_trans.mk
    fun (j : category_theory.limits.walking_parallel_pair) =>
      category_theory.limits.walking_parallel_pair.rec_on j
        (category_theory.limits.pi.map
          fun (i : ι)
            (f : category_theory.functor.obj (subpresheaf_to_Types P) (opposite.op (U i))) =>
            subtype.val f)
        (category_theory.limits.pi.map
          fun (p : ι × ι)
            (f :
            category_theory.functor.obj (subpresheaf_to_Types P)
              (opposite.op (U (prod.fst p) ⊓ U (prod.snd p)))) =>
            subtype.val f)

-- auxilliary lemma for `sheaf_condition` below

theorem sheaf_condition_fac {X : Top} {T : ↥X → Type v} {P : local_predicate T} {ι : Type v}
    {U : ι → topological_space.opens ↥X}
    {s :
      category_theory.limits.fork
        (presheaf.sheaf_condition_equalizer_products.left_res
          (subpresheaf_to_Types (local_predicate.to_prelocal_predicate P)) U)
        (presheaf.sheaf_condition_equalizer_products.right_res
          (subpresheaf_to_Types (local_predicate.to_prelocal_predicate P)) U)}
    (i : ι) (f : category_theory.limits.cone.X s)
    (h :
      prelocal_predicate.pred (local_predicate.to_prelocal_predicate P)
        (category_theory.limits.is_limit.lift (presheaf.to_Types X T U)
          (category_theory.functor.obj
            (category_theory.limits.cones.postcompose
              (diagram_subtype (local_predicate.to_prelocal_predicate P) U))
            s)
          f)) :
    category_theory.limits.limit.π
          (category_theory.discrete.functor
            fun (i : ι) =>
              Subtype
                fun (f : (x : ↥(opposite.unop (opposite.op (U i)))) → T ↑x) =>
                  prelocal_predicate.pred (local_predicate.to_prelocal_predicate P) f)
          i
          (presheaf.sheaf_condition_equalizer_products.res
            (subpresheaf_to_Types (local_predicate.to_prelocal_predicate P)) U
            { val :=
                category_theory.limits.is_limit.lift (presheaf.to_Types X T U)
                  (category_theory.functor.obj
                    (category_theory.limits.cones.postcompose
                      (diagram_subtype (local_predicate.to_prelocal_predicate P) U))
                    s)
                  f,
              property := h }) =
        category_theory.limits.limit.π
          (category_theory.discrete.functor
            fun (i : ι) =>
              Subtype
                fun (f : (x : ↥(opposite.unop (opposite.op (U i)))) → T ↑x) =>
                  prelocal_predicate.pred (local_predicate.to_prelocal_predicate P) f)
          i (category_theory.limits.fork.ι s f) :=
  sorry

-- auxilliary lemma for `sheaf_condition` below

theorem sheaf_condition_uniq {X : Top} {T : ↥X → Type v} {P : local_predicate T} {ι : Type v}
    {U : ι → topological_space.opens ↥X}
    {s :
      category_theory.limits.fork
        (presheaf.sheaf_condition_equalizer_products.left_res
          (subpresheaf_to_Types (local_predicate.to_prelocal_predicate P)) U)
        (presheaf.sheaf_condition_equalizer_products.right_res
          (subpresheaf_to_Types (local_predicate.to_prelocal_predicate P)) U)}
    (m :
      category_theory.limits.cone.X s ⟶
        category_theory.limits.cone.X
          (presheaf.sheaf_condition_equalizer_products.fork
            (subpresheaf_to_Types (local_predicate.to_prelocal_predicate P)) U))
    (w :
      ∀ (j : category_theory.limits.walking_parallel_pair),
        m ≫
            category_theory.nat_trans.app
              (category_theory.limits.cone.π
                (presheaf.sheaf_condition_equalizer_products.fork
                  (subpresheaf_to_Types (local_predicate.to_prelocal_predicate P)) U))
              j =
          category_theory.nat_trans.app (category_theory.limits.cone.π s) j)
    (f : category_theory.limits.cone.X s)
    (h :
      prelocal_predicate.pred (local_predicate.to_prelocal_predicate P)
        (category_theory.limits.is_limit.lift (presheaf.to_Types X T U)
          (category_theory.functor.obj
            (category_theory.limits.cones.postcompose
              (diagram_subtype (local_predicate.to_prelocal_predicate P) U))
            s)
          f)) :
    m f =
        { val :=
            category_theory.limits.is_limit.lift (presheaf.to_Types X T U)
              (category_theory.functor.obj
                (category_theory.limits.cones.postcompose
                  (diagram_subtype (local_predicate.to_prelocal_predicate P) U))
                s)
              f,
          property := h } :=
  sorry

/--
The functions satisfying a local predicate satisfy the sheaf condition.
-/
def sheaf_condition {X : Top} {T : ↥X → Type v} (P : local_predicate T) :
    presheaf.sheaf_condition (subpresheaf_to_Types (local_predicate.to_prelocal_predicate P)) :=
  sorry

end subpresheaf_to_Types


/--
The subsheaf of the sheaf of all dependently typed functions satisfying the local predicate `P`.
-/
def subsheaf_to_Types {X : Top} {T : ↥X → Type v} (P : local_predicate T) : sheaf (Type v) X :=
  sheaf.mk (subpresheaf_to_Types (local_predicate.to_prelocal_predicate P))
    (subpresheaf_to_Types.sheaf_condition P)

/--
There is a canonical map from the stalk to the original fiber, given by evaluating sections.
-/
def stalk_to_fiber {X : Top} {T : ↥X → Type v} (P : local_predicate T) (x : ↥X) :
    presheaf.stalk (sheaf.presheaf (subsheaf_to_Types P)) x ⟶ T x :=
  category_theory.limits.colimit.desc
    (category_theory.functor.obj
      (category_theory.functor.obj
        (category_theory.whiskering_left (topological_space.open_nhds xᵒᵖ)
          (topological_space.opens ↥Xᵒᵖ) (Type v))
        (category_theory.functor.op (topological_space.open_nhds.inclusion x)))
      (sheaf.presheaf (subsheaf_to_Types P)))
    (category_theory.limits.cocone.mk (T x)
      (category_theory.nat_trans.mk
        fun (U : topological_space.open_nhds xᵒᵖ)
          (f :
          category_theory.functor.obj
            (category_theory.functor.obj
              (category_theory.functor.obj
                (category_theory.whiskering_left (topological_space.open_nhds xᵒᵖ)
                  (topological_space.opens ↥Xᵒᵖ) (Type v))
                (category_theory.functor.op (topological_space.open_nhds.inclusion x)))
              (sheaf.presheaf (subsheaf_to_Types P)))
            U) =>
          subtype.val f { val := x, property := sorry }))

@[simp] theorem stalk_to_fiber_germ {X : Top} {T : ↥X → Type v} (P : local_predicate T)
    (U : topological_space.opens ↥X) (x : ↥U)
    (f : category_theory.functor.obj (sheaf.presheaf (subsheaf_to_Types P)) (opposite.op U)) :
    stalk_to_fiber P (↑x) (presheaf.germ (sheaf.presheaf (subsheaf_to_Types P)) x f) =
        subtype.val f x :=
  sorry

/--
The `stalk_to_fiber` map is surjective at `x` if
every point in the fiber `T x` has an allowed section passing through it.
-/
theorem stalk_to_fiber_surjective {X : Top} {T : ↥X → Type v} (P : local_predicate T) (x : ↥X)
    (w :
      ∀ (t : T x),
        ∃ (U : topological_space.open_nhds x),
          ∃ (f : (y : ↥(subtype.val U)) → T ↑y),
            ∃ (h : prelocal_predicate.pred (local_predicate.to_prelocal_predicate P) f),
              f { val := x, property := subtype.property U } = t) :
    function.surjective (stalk_to_fiber P x) :=
  sorry

/--
The `stalk_to_fiber` map is injective at `x` if any two allowed sections which agree at `x`
agree on some neighborhood of `x`.
-/
theorem stalk_to_fiber_injective {X : Top} {T : ↥X → Type v} (P : local_predicate T) (x : ↥X)
    (w :
      ∀ (U V : topological_space.open_nhds x) (fU : (y : ↥(subtype.val U)) → T ↑y),
        prelocal_predicate.pred (local_predicate.to_prelocal_predicate P) fU →
          ∀ (fV : (y : ↥(subtype.val V)) → T ↑y),
            prelocal_predicate.pred (local_predicate.to_prelocal_predicate P) fV →
              fU { val := x, property := subtype.property U } =
                  fV { val := x, property := subtype.property V } →
                ∃ (W : topological_space.open_nhds x),
                  ∃ (iU : W ⟶ U),
                    ∃ (iV : W ⟶ V), ∀ (w : ↥(subtype.val W)), fU (coe_fn iU w) = fV (coe_fn iV w)) :
    function.injective (stalk_to_fiber P x) :=
  sorry

/--
Some repackaging:
the presheaf of functions satisfying `continuous_prelocal` is just the same thing as
the presheaf of continuous functions.
-/
def subpresheaf_continuous_prelocal_iso_presheaf_to_Top {X : Top} (T : Top) :
    subpresheaf_to_Types (continuous_prelocal X T) ≅ presheaf_to_Top X T :=
  sorry

/--
The sheaf of continuous functions on `X` with values in a space `T`.
-/
def sheaf_to_Top {X : Top} (T : Top) : sheaf (Type v) X :=
  sheaf.mk (presheaf_to_Top X T)
    (coe_fn
      (presheaf.sheaf_condition_equiv_of_iso
        (subpresheaf_continuous_prelocal_iso_presheaf_to_Top T))
      (subpresheaf_to_Types.sheaf_condition (continuous_local X T)))

end Mathlib