/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.monad.types
import Mathlib.category_theory.monad.limits
import Mathlib.category_theory.equivalence
import Mathlib.topology.category.CompHaus
import Mathlib.data.set.constructions
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!

# Compacta and Compact Hausdorff Spaces

Recall that, given a monad `M` on `Type*`, an *algebra* for `M` consists of the following data:
- A type `X : Type*`
- A "structure" map `M X → X`.
This data must also satisfy a distributivity and unit axiom, and algebras for `M` form a category
in an evident way.

See the file `category_theory.monad.algebra` for a general version, as well as the following link.
https://ncatlab.org/nlab/show/monad

This file proves the equivalence between the category of *compact Hausdorff topological spaces*
and the category of algebras for the *ultrafilter monad*.

## Notation:

Here are the main objects introduced in this file.
- `Compactum` is the type of compacta, which we define as algebras for the ultrafilter monad.
- `Compactum_to_CompHaus` is the functor `Compactum ⥤ CompHaus`. Here `CompHaus` is the usual
  category of compact Hausdorff spaces.
- `Compactum_to_CompHaus.is_equivalence` is a term of type `is_equivalence Compactum_to_CompHaus`.

The proof of this equivalence is a bit technical. But the idea is quite simply that the structure
map `ultrafilter X → X` for an algebra `X` of the ultrafilter monad should be considered as the map
sending an ultrafilter to its limit in `X`. The topology on `X` is then defined by mimicking the
characterization of open sets in terms of ultrafilters.

Any `X : Compactum` is endowed with a coercion to `Type*`, as well as the following instances:
- `topological_space X`.
- `compact_space X`.
- `t2_space X`.

Any morphism `f : X ⟶ Y` of is endowed with a coercion to a function `X → Y`, which is shown to
be continuous in `continuous_of_hom`.

The function `Compactum.of_topological_space` can be used to construct a `Compactum` from a
topological space which satisfies `compact_space` and `t2_space`.

We also add wrappers around structures which already exist. Here are the main ones, all in the
`Compactum` namespace:

- `forget : Compactum ⥤ Type*` is the forgetful functor, which induces a `concrete_category`
  instance for `Compactum`.
- `free : Type* ⥤ Compactum` is the left adjoint to `forget`, and the adjunction is in `adj`.
- `str : ultrafilter X → X` is the structure map for `X : Compactum`.
  The notation `X.str` is preferred.
- `join : ultrafilter (ultrafilter X) → ultrafilter X` is the monadic join for `X : Compactum`.
  Again, the notation `X.join` is preferred.
- `incl : X → ultrafilter X` is the unit for `X : Compactum`. The notation `X.incl` is preferred.

## References

- E. Manes, Algebraic Theories, Graduate Texts in Mathematics 26, Springer-Verlag, 1976.
- https://ncatlab.org/nlab/show/ultrafilter

-/

/-- The type `Compactum` of Compacta, defined as algebras for the ultrafilter monad. -/
def Compactum :=
  category_theory.monad.algebra (category_theory.of_type_functor ultrafilter)

namespace Compactum


/-- The forgetful functor to Type* -/
def forget : Compactum ⥤ Type u_1 :=
  category_theory.monad.forget (category_theory.of_type_functor ultrafilter)

/-- The "free" Compactum functor. -/
def free : Type u_1 ⥤ Compactum :=
  category_theory.monad.free (category_theory.of_type_functor ultrafilter)

/-- The adjunction between `free` and `forget`. -/
def adj : free ⊣ forget :=
  category_theory.monad.adj (category_theory.of_type_functor ultrafilter)

-- Basic instances

protected instance category_theory.concrete_category : category_theory.concrete_category Compactum :=
  category_theory.concrete_category.mk forget

protected instance has_coe_to_sort : has_coe_to_sort Compactum :=
  has_coe_to_sort.mk (Type u_1) (category_theory.functor.obj forget)

protected instance category_theory.has_hom.hom.has_coe_to_fun {X : Compactum} {Y : Compactum} : has_coe_to_fun (X ⟶ Y) :=
  has_coe_to_fun.mk (fun (f : X ⟶ Y) => ↥X → ↥Y) fun (f : X ⟶ Y) => category_theory.monad.algebra.hom.f f

protected instance category_theory.limits.has_limits : category_theory.limits.has_limits Compactum :=
  category_theory.has_limits_of_has_limits_creates_limits forget

/-- The structure map for a compactum, essentially sending an ultrafilter to its limit. -/
def str (X : Compactum) : ultrafilter ↥X → ↥X :=
  category_theory.monad.algebra.a X

/-- The monadic join. -/
def join (X : Compactum) : ultrafilter (ultrafilter ↥X) → ultrafilter ↥X :=
  category_theory.nat_trans.app μ_ ↥X

/-- The inclusion of `X` into `ultrafilter X`. -/
def incl (X : Compactum) : ↥X → ultrafilter ↥X :=
  category_theory.nat_trans.app η_ (category_theory.functor.obj forget X)

@[simp] theorem str_incl (X : Compactum) (x : ↥X) : str X (incl X x) = x := sorry

@[simp] theorem str_hom_commute (X : Compactum) (Y : Compactum) (f : X ⟶ Y) (xs : ultrafilter ↥X) : coe_fn f (str X xs) = str Y (ultrafilter.map (⇑f) xs) := sorry

@[simp] theorem join_distrib (X : Compactum) (uux : ultrafilter (ultrafilter ↥X)) : str X (join X uux) = str X (ultrafilter.map (str X) uux) := sorry

protected instance topological_space {X : Compactum} : topological_space ↥X :=
  topological_space.mk (fun (U : set ↥X) => ∀ (F : ultrafilter ↥X), str X F ∈ U → U ∈ F) sorry sorry sorry

theorem is_closed_iff {X : Compactum} (S : set ↥X) : is_closed S ↔ ∀ (F : ultrafilter ↥X), S ∈ F → str X F ∈ S := sorry

protected instance compact_space {X : Compactum} : compact_space ↥X :=
  compact_space.mk
    (eq.mpr (id (Eq._oldrec (Eq.refl (is_compact set.univ)) (propext compact_iff_ultrafilter_le_nhds)))
      fun (F : ultrafilter ↥X) (h : ↑F ≤ filter.principal set.univ) =>
        Exists.intro (str X F)
          (Exists.intro trivial
            (eq.mpr (id (Eq._oldrec (Eq.refl (↑F ≤ nhds (str X F))) (propext le_nhds_iff)))
              fun (S : set ↥X) (h1 : str X F ∈ S) (h2 : is_open S) => h2 F h1)))

/-- A local definition used only in the proofs. -/
/-- A local definition used only in the proofs. -/
theorem is_closed_cl {X : Compactum} (A : set ↥X) : is_closed (cl A) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_closed (cl A))) (propext (is_closed_iff (cl A)))))
    fun (F : ultrafilter ↥X) (hF : cl A ∈ F) => cl_cl A (Exists.intro F { left := hF, right := rfl })

theorem str_eq_of_le_nhds {X : Compactum} (F : ultrafilter ↥X) (x : ↥X) : ↑F ≤ nhds x → str X F = x := sorry

theorem le_nhds_of_str_eq {X : Compactum} (F : ultrafilter ↥X) (x : ↥X) : str X F = x → ↑F ≤ nhds x :=
  fun (h : str X F = x) =>
    iff.mpr le_nhds_iff
      fun (s : set ↥X) (hx : x ∈ s) (hs : is_open s) => hs F (eq.mpr (id (Eq._oldrec (Eq.refl (str X F ∈ s)) h)) hx)

-- All the hard work above boils down to this t2_space instance.

protected instance t2_space {X : Compactum} : t2_space ↥X :=
  eq.mpr (id (Eq._oldrec (Eq.refl (t2_space ↥X)) (propext t2_iff_ultrafilter)))
    fun (x y : ↥X) (F : ultrafilter ↥X) (hx : ↑F ≤ nhds x) (hy : ↑F ≤ nhds y) =>
      eq.mpr (id (Eq._oldrec (Eq.refl (x = y)) (Eq.symm (str_eq_of_le_nhds F x hx))))
        (eq.mpr (id (Eq._oldrec (Eq.refl (str X F = y)) (Eq.symm (str_eq_of_le_nhds F y hy)))) (Eq.refl (str X F)))

/-- The structure map of a compactum actually computes limits. -/
theorem Lim_eq_str {X : Compactum} (F : ultrafilter ↥X) : ultrafilter.Lim F = str X F :=
  eq.mpr (id (Eq._oldrec (Eq.refl (ultrafilter.Lim F = str X F)) (propext ultrafilter.Lim_eq_iff_le_nhds)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑F ≤ nhds (str X F))) (propext le_nhds_iff)))
      fun (s : set ↥X) (ᾰ : str X F ∈ s) (ᾰ_1 : is_open s) => ᾰ_1 F ᾰ)

theorem cl_eq_closure {X : Compactum} (A : set ↥X) : cl A = closure A := sorry

/-- Any morphism of compacta is continuous. -/
theorem continuous_of_hom {X : Compactum} {Y : Compactum} (f : X ⟶ Y) : continuous ⇑f := sorry

/-- Given any compact Hausdorff space, we construct a Compactum. -/
def of_topological_space (X : Type u_1) [topological_space X] [compact_space X] [t2_space X] : Compactum :=
  category_theory.monad.algebra.mk X ultrafilter.Lim

/-- Any continuous map between Compacta is a morphism of compacta. -/
def hom_of_continuous {X : Compactum} {Y : Compactum} (f : ↥X → ↥Y) (cont : continuous f) : X ⟶ Y :=
  category_theory.monad.algebra.hom.mk f

end Compactum


/-- The functor functor from Compactum to CompHaus. -/
def Compactum_to_CompHaus : Compactum ⥤ CompHaus :=
  category_theory.functor.mk (fun (X : Compactum) => CompHaus.mk (category_theory.bundled.mk ↥X))
    fun (X Y : Compactum) (f : X ⟶ Y) => continuous_map.mk ⇑f

namespace Compactum_to_CompHaus


/-- The functor Compactum_to_CompHaus is full. -/
def full : category_theory.full Compactum_to_CompHaus :=
  category_theory.full.mk
    fun (X Y : Compactum)
      (f : category_theory.functor.obj Compactum_to_CompHaus X ⟶ category_theory.functor.obj Compactum_to_CompHaus Y) =>
      Compactum.hom_of_continuous (continuous_map.to_fun f) sorry

/-- The functor Compactum_to_CompHaus is faithful. -/
theorem faithful : category_theory.faithful Compactum_to_CompHaus :=
  category_theory.faithful.mk

/-- This definition is used to prove essential surjectivity of Compactum_to_CompHaus. -/
def iso_of_topological_space {D : CompHaus} : category_theory.functor.obj Compactum_to_CompHaus (Compactum.of_topological_space ↥D) ≅ D :=
  category_theory.iso.mk (continuous_map.mk id) (continuous_map.mk id)

/-- The functor Compactum_to_CompHaus is essentially surjective. -/
theorem ess_surj : category_theory.ess_surj Compactum_to_CompHaus :=
  category_theory.ess_surj.mk
    fun (X : CompHaus) => Exists.intro (Compactum.of_topological_space ↥X) (Nonempty.intro iso_of_topological_space)

/-- The functor Compactum_to_CompHaus is an equivalence of categories. -/
def is_equivalence : category_theory.is_equivalence Compactum_to_CompHaus :=
  category_theory.equivalence.equivalence_of_fully_faithfully_ess_surj Compactum_to_CompHaus

