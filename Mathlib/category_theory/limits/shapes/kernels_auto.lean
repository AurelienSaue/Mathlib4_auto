/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Markus Himmel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.limits.shapes.zero
import Mathlib.PostPort

universes v u u' l 

namespace Mathlib

/-!
# Kernels and cokernels

In a category with zero morphisms, the kernel of a morphism `f : X ⟶ Y` is
the equalizer of `f` and `0 : X ⟶ Y`. (Similarly the cokernel is the coequalizer.)

The basic definitions are
* `kernel : (X ⟶ Y) → C`
* `kernel.ι : kernel f ⟶ X`
* `kernel.condition : kernel.ι f ≫ f = 0` and
* `kernel.lift (k : W ⟶ X) (h : k ≫ f = 0) : W ⟶ kernel f` (as well as the dual versions)

## Main statements

Besides the definition and lifts, we prove
* `kernel.ι_zero_is_iso`: a kernel map of a zero morphism is an isomorphism
* `kernel.eq_zero_of_epi_kernel`: if `kernel.ι f` is an epimorphism, then `f = 0`
* `kernel.of_mono`: the kernel of a monomorphism is the zero object
* `kernel.lift_mono`: the lift of a monomorphism `k : W ⟶ X` such that `k ≫ f = 0`
  is still a monomorphism
* `kernel.is_limit_cone_zero_cone`: if our category has a zero object, then the map from the zero
  obect is a kernel map of any monomorphism
* `kernel.ι_of_zero`: `kernel.ι (0 : X ⟶ Y)` is an isomorphism

and the corresponding dual statements.

## Future work
* TODO: connect this with existing working in the group theory and ring theory libraries.

## Implementation notes
As with the other special shapes in the limits library, all the definitions here are given as
`abbreviation`s of the general statements for limits, so all the `simp` lemmas and theorems about
general limits can be used.

## References

* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]
-/

namespace category_theory.limits


/-- A morphism `f` has a kernel if the functor `parallel_pair f 0` has a limit. -/
/-- A morphism `f` has a cokernel if the functor `parallel_pair f 0` has a colimit. -/
def has_kernel {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C} (f : X ⟶ Y) :=
  has_limit (parallel_pair f 0)

def has_cokernel {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C} (f : X ⟶ Y) :=
  has_colimit (parallel_pair f 0)

/-- A kernel fork is just a fork where the second morphism is a zero morphism. -/
def kernel_fork {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C} (f : X ⟶ Y) :=
  fork f 0

@[simp] theorem kernel_fork.condition_assoc {C : Type u} [category C] [has_zero_morphisms C] {X : C}
    {Y : C} {f : X ⟶ Y} (s : kernel_fork f) {X' : C} (f' : Y ⟶ X') : fork.ι s ≫ f ≫ f' = 0 ≫ f' :=
  sorry

@[simp] theorem kernel_fork.app_one {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C}
    {f : X ⟶ Y} (s : kernel_fork f) : nat_trans.app (cone.π s) walking_parallel_pair.one = 0 :=
  sorry

/-- A morphism `ι` satisfying `ι ≫ f = 0` determines a kernel fork over `f`. -/
def kernel_fork.of_ι {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C} {f : X ⟶ Y}
    {Z : C} (ι : Z ⟶ X) (w : ι ≫ f = 0) : kernel_fork f :=
  fork.of_ι ι sorry

@[simp] theorem kernel_fork.ι_of_ι {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C}
    {P : C} (f : X ⟶ Y) (ι : P ⟶ X) (w : ι ≫ f = 0) : fork.ι (kernel_fork.of_ι ι w) = ι :=
  rfl

/-- Every kernel fork `s` is isomorphic (actually, equal) to `fork.of_ι (fork.ι s) _`. -/
def iso_of_ι {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C} {f : X ⟶ Y}
    (s : fork f 0) : s ≅ fork.of_ι (fork.ι s) (iso_of_ι._proof_1 s) :=
  cones.ext (iso.refl (cone.X s)) sorry

/-- If `ι = ι'`, then `fork.of_ι ι _` and `fork.of_ι ι' _` are isomorphic. -/
def of_ι_congr {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C} {f : X ⟶ Y} {P : C}
    {ι : P ⟶ X} {ι' : P ⟶ X} {w : ι ≫ f = 0} (h : ι = ι') :
    kernel_fork.of_ι ι w ≅ kernel_fork.of_ι ι' (of_ι_congr._proof_1 h) :=
  cones.ext (iso.refl (cone.X (kernel_fork.of_ι ι w))) sorry

/-- If `F` is an equivalence, then applying `F` to a diagram indexing a (co)kernel of `f` yields
    the diagram indexing the (co)kernel of `F.map f`. -/
def comp_nat_iso {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C} {f : X ⟶ Y}
    {D : Type u'} [category D] [has_zero_morphisms D] (F : C ⥤ D) [is_equivalence F] :
    parallel_pair f 0 ⋙ F ≅ parallel_pair (functor.map F f) 0 :=
  nat_iso.of_components (fun (j : walking_parallel_pair) => sorry) sorry

/-- If `s` is a limit kernel fork and `k : W ⟶ X` satisfies ``k ≫ f = 0`, then there is some
    `l : W ⟶ s.X` such that `l ≫ fork.ι s = k`. -/
def kernel_fork.is_limit.lift' {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C}
    {f : X ⟶ Y} {s : kernel_fork f} (hs : is_limit s) {W : C} (k : W ⟶ X) (h : k ≫ f = 0) :
    Subtype fun (l : W ⟶ cone.X s) => l ≫ fork.ι s = k :=
  { val := is_limit.lift hs (kernel_fork.of_ι k h), property := sorry }

/-- This is a slightly more convenient method to verify that a kernel fork is a limit cone. It
    only asks for a proof of facts that carry any mathematical content -/
def is_limit_aux {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C} {f : X ⟶ Y}
    (t : kernel_fork f) (lift : (s : kernel_fork f) → cone.X s ⟶ cone.X t)
    (fac : ∀ (s : kernel_fork f), lift s ≫ fork.ι t = fork.ι s)
    (uniq : ∀ (s : kernel_fork f) (m : cone.X s ⟶ cone.X t), m ≫ fork.ι t = fork.ι s → m = lift s) :
    is_limit t :=
  is_limit.mk lift

/--
This is a more convenient formulation to show that a `kernel_fork` constructed using
`kernel_fork.of_ι` is a limit cone.
-/
def is_limit.of_ι {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C} {f : X ⟶ Y}
    {W : C} (g : W ⟶ X) (eq : g ≫ f = 0) (lift : {W' : C} → (g' : W' ⟶ X) → g' ≫ f = 0 → (W' ⟶ W))
    (fac : ∀ {W' : C} (g' : W' ⟶ X) (eq' : g' ≫ f = 0), lift g' eq' ≫ g = g')
    (uniq :
      ∀ {W' : C} (g' : W' ⟶ X) (eq' : g' ≫ f = 0) (m : W' ⟶ W), m ≫ g = g' → m = lift g' eq') :
    is_limit (kernel_fork.of_ι g eq) :=
  is_limit_aux (kernel_fork.of_ι g eq)
    (fun (s : kernel_fork f) => lift (fork.ι s) (kernel_fork.condition s)) sorry sorry

/-- The kernel of a morphism, expressed as the equalizer with the 0 morphism. -/
def kernel {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C} (f : X ⟶ Y)
    [has_kernel f] : C :=
  equalizer f 0

/-- The map from `kernel f` into the source of `f`. -/
def kernel.ι {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C} (f : X ⟶ Y)
    [has_kernel f] : kernel f ⟶ X :=
  equalizer.ι f 0

@[simp] theorem equalizer_as_kernel {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C}
    (f : X ⟶ Y) [has_kernel f] : equalizer.ι f 0 = kernel.ι f :=
  rfl

@[simp] theorem kernel.condition_assoc {C : Type u} [category C] [has_zero_morphisms C] {X : C}
    {Y : C} (f : X ⟶ Y) [has_kernel f] {X' : C} (f' : Y ⟶ X') : kernel.ι f ≫ f ≫ f' = 0 ≫ f' :=
  sorry

/-- Given any morphism `k : W ⟶ X` satisfying `k ≫ f = 0`, `k` factors through `kernel.ι f`
    via `kernel.lift : W ⟶ kernel f`. -/
def kernel.lift {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C} (f : X ⟶ Y)
    [has_kernel f] {W : C} (k : W ⟶ X) (h : k ≫ f = 0) : W ⟶ kernel f :=
  limit.lift (parallel_pair f 0) (kernel_fork.of_ι k h)

@[simp] theorem kernel.lift_ι {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C}
    (f : X ⟶ Y) [has_kernel f] {W : C} (k : W ⟶ X) (h : k ≫ f = 0) :
    kernel.lift f k h ≫ kernel.ι f = k :=
  limit.lift_π (kernel_fork.of_ι k h) walking_parallel_pair.zero

@[simp] theorem kernel.lift_zero {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C}
    (f : X ⟶ Y) [has_kernel f] {W : C} {h : 0 ≫ f = 0} : kernel.lift f 0 h = 0 :=
  sorry

protected instance kernel.lift_mono {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C}
    (f : X ⟶ Y) [has_kernel f] {W : C} (k : W ⟶ X) (h : k ≫ f = 0) [mono k] :
    mono (kernel.lift f k h) :=
  sorry

/-- Any morphism `k : W ⟶ X` satisfying `k ≫ f = 0` induces a morphism `l : W ⟶ kernel f` such that
    `l ≫ kernel.ι f = k`. -/
def kernel.lift' {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C} (f : X ⟶ Y)
    [has_kernel f] {W : C} (k : W ⟶ X) (h : k ≫ f = 0) :
    Subtype fun (l : W ⟶ kernel f) => l ≫ kernel.ι f = k :=
  { val := kernel.lift f k h, property := kernel.lift_ι f k h }

/-- Every kernel of the zero morphism is an isomorphism -/
protected instance kernel.ι_zero_is_iso {C : Type u} [category C] [has_zero_morphisms C] {X : C}
    {Y : C} : is_iso (kernel.ι 0) :=
  equalizer.ι_of_self 0

theorem eq_zero_of_epi_kernel {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C}
    (f : X ⟶ Y) [has_kernel f] [epi (kernel.ι f)] : f = 0 :=
  sorry

/-- The kernel of a zero morphism is isomorphic to the source. -/
def kernel_zero_iso_source {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C} :
    kernel 0 ≅ X :=
  equalizer.iso_source_of_self 0

@[simp] theorem kernel_zero_iso_source_hom {C : Type u} [category C] [has_zero_morphisms C] {X : C}
    {Y : C} : iso.hom kernel_zero_iso_source = kernel.ι 0 :=
  rfl

@[simp] theorem kernel_zero_iso_source_inv {C : Type u} [category C] [has_zero_morphisms C] {X : C}
    {Y : C} :
    iso.inv kernel_zero_iso_source =
        kernel.lift 0 𝟙
          (eq.mpr
            (id
              (Eq.trans
                ((fun (a a_1 : X ⟶ Y) (e_1 : a = a_1) (ᾰ ᾰ_1 : X ⟶ Y) (e_2 : ᾰ = ᾰ_1) =>
                    congr (congr_arg Eq e_1) e_2)
                  (𝟙 ≫ 0) 0 comp_zero 0 0 (Eq.refl 0))
                (propext (eq_self_iff_true 0))))
            trivial) :=
  rfl

/-- If two morphisms are known to be equal, then their kernels are isomorphic. -/
def kernel_iso_of_eq {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C} {f : X ⟶ Y}
    {g : X ⟶ Y} [has_kernel f] [has_kernel g] (h : f = g) : kernel f ≅ kernel g :=
  has_limit.iso_of_nat_iso (eq.mpr sorry (iso.refl (parallel_pair g 0)))

@[simp] theorem kernel_iso_of_eq_refl {C : Type u} [category C] [has_zero_morphisms C] {X : C}
    {Y : C} (f : X ⟶ Y) [has_kernel f] {h : f = f} : kernel_iso_of_eq h = iso.refl (kernel f) :=
  sorry

@[simp] theorem kernel_iso_of_eq_trans {C : Type u} [category C] [has_zero_morphisms C] {X : C}
    {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} {h : X ⟶ Y} [has_kernel f] [has_kernel g] [has_kernel h]
    (w₁ : f = g) (w₂ : g = h) :
    kernel_iso_of_eq w₁ ≪≫ kernel_iso_of_eq w₂ = kernel_iso_of_eq (Eq.trans w₁ w₂) :=
  sorry

theorem kernel_not_epi_of_nonzero {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C}
    {f : X ⟶ Y} [has_kernel f] (w : f ≠ 0) : ¬epi (kernel.ι f) :=
  fun (I : epi (kernel.ι f)) => w (eq_zero_of_epi_kernel f)

theorem kernel_not_iso_of_nonzero {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C}
    {f : X ⟶ Y} [has_kernel f] (w : f ≠ 0) : is_iso (kernel.ι f) → False :=
  fun (I : is_iso (kernel.ι f)) =>
    kernel_not_epi_of_nonzero w (category_theory.epi_of_strong_epi (kernel.ι f))

/--
When `g` is an isomorphism, the kernel of `f ≫ g` is isomorphic to the kernel of `f`.
-/
def kernel_comp_is_iso {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C} {Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) [has_kernel (f ≫ g)] [has_kernel f] [is_iso g] :
    kernel (f ≫ g) ≅ kernel f :=
  iso.mk (kernel.lift f (kernel.ι (f ≫ g)) sorry) (kernel.lift (f ≫ g) (kernel.ι f) sorry)

@[simp] theorem kernel_comp_is_iso_hom_comp_kernel_ι {C : Type u} [category C]
    [has_zero_morphisms C] {X : C} {Y : C} {Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [has_kernel (f ≫ g)]
    [has_kernel f] [is_iso g] : iso.hom (kernel_comp_is_iso f g) ≫ kernel.ι f = kernel.ι (f ≫ g) :=
  sorry

@[simp] theorem kernel_comp_is_iso_inv_comp_kernel_ι {C : Type u} [category C]
    [has_zero_morphisms C] {X : C} {Y : C} {Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [has_kernel (f ≫ g)]
    [has_kernel f] [is_iso g] : iso.inv (kernel_comp_is_iso f g) ≫ kernel.ι (f ≫ g) = kernel.ι f :=
  sorry

/--
When `f` is an isomorphism, the kernel of `f ≫ g` is isomorphic to the kernel of `g`.
-/
def kernel_is_iso_comp {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C} {Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) [has_kernel (f ≫ g)] [is_iso f] [has_kernel g] :
    kernel (f ≫ g) ≅ kernel g :=
  iso.mk (kernel.lift g (kernel.ι (f ≫ g) ≫ f) sorry)
    (kernel.lift (f ≫ g) (kernel.ι g ≫ inv f) sorry)

@[simp] theorem kernel_is_iso_comp_hom_comp_kernel_ι {C : Type u} [category C]
    [has_zero_morphisms C] {X : C} {Y : C} {Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [has_kernel (f ≫ g)]
    [is_iso f] [has_kernel g] :
    iso.hom (kernel_is_iso_comp f g) ≫ kernel.ι g = kernel.ι (f ≫ g) ≫ f :=
  sorry

@[simp] theorem kernel_is_iso_comp_inv_comp_kernel_ι {C : Type u} [category C]
    [has_zero_morphisms C] {X : C} {Y : C} {Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [has_kernel (f ≫ g)]
    [is_iso f] [has_kernel g] :
    iso.inv (kernel_is_iso_comp f g) ≫ kernel.ι (f ≫ g) = kernel.ι g ≫ inv f :=
  sorry

/-- The morphism from the zero object determines a cone on a kernel diagram -/
def kernel.zero_cone {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C} (f : X ⟶ Y)
    [has_zero_object C] : cone (parallel_pair f 0) :=
  cone.mk 0 (nat_trans.mk fun (j : walking_parallel_pair) => 0)

/-- The map from the zero object is a kernel of a monomorphism -/
def kernel.is_limit_cone_zero_cone {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C}
    (f : X ⟶ Y) [has_zero_object C] [mono f] : is_limit (kernel.zero_cone f) :=
  fork.is_limit.mk (kernel.zero_cone f) (fun (s : fork f 0) => 0) sorry sorry

/-- The kernel of a monomorphism is isomorphic to the zero object -/
def kernel.of_mono {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C} (f : X ⟶ Y)
    [has_zero_object C] [has_kernel f] [mono f] : kernel f ≅ 0 :=
  functor.map_iso (cones.forget (parallel_pair f 0))
    (is_limit.unique_up_to_iso (limit.is_limit (parallel_pair f 0))
      (kernel.is_limit_cone_zero_cone f))

/-- The kernel morphism of a monomorphism is a zero morphism -/
theorem kernel.ι_of_mono {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C}
    (f : X ⟶ Y) [has_zero_object C] [has_kernel f] [mono f] : kernel.ι f = 0 :=
  zero_of_source_iso_zero (kernel.ι f) (kernel.of_mono f)

/-- If `i` is an isomorphism such that `l ≫ i.hom = f`, then any kernel of `f` is a kernel of `l`.-/
def is_kernel.of_comp_iso {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C}
    (f : X ⟶ Y) {Z : C} (l : X ⟶ Z) (i : Z ≅ Y) (h : l ≫ iso.hom i = f) {s : kernel_fork f}
    (hs : is_limit s) :
    is_limit (kernel_fork.of_ι (fork.ι s) (is_kernel.of_comp_iso._proof_1 f l i h)) :=
  fork.is_limit.mk (kernel_fork.of_ι (fork.ι s) sorry)
    (fun (s_1 : fork l 0) => is_limit.lift hs (kernel_fork.of_ι (fork.ι s_1) sorry)) sorry sorry

/-- If `i` is an isomorphism such that `l ≫ i.hom = f`, then the kernel of `f` is a kernel of `l`.-/
def kernel.of_comp_iso {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C} (f : X ⟶ Y)
    [has_kernel f] {Z : C} (l : X ⟶ Z) (i : Z ≅ Y) (h : l ≫ iso.hom i = f) :
    is_limit (kernel_fork.of_ι (kernel.ι f) (kernel.of_comp_iso._proof_1 f l i h)) :=
  is_kernel.of_comp_iso f l i h (limit.is_limit (parallel_pair f 0))

/-- If `s` is any limit kernel cone over `f` and if  `i` is an isomorphism such that
    `i.hom ≫ s.ι  = l`, then `l` is a kernel of `f`. -/
def is_kernel.iso_kernel {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C}
    (f : X ⟶ Y) {Z : C} (l : Z ⟶ X) {s : kernel_fork f} (hs : is_limit s) (i : Z ≅ cone.X s)
    (h : iso.hom i ≫ fork.ι s = l) :
    is_limit (kernel_fork.of_ι l (is_kernel.iso_kernel._proof_1 f l i h)) :=
  is_limit.of_iso_limit hs (cones.ext (iso.symm i) sorry)

/-- If `i` is an isomorphism such that `i.hom ≫ kernel.ι f = l`, then `l` is a kernel of `f`. -/
def kernel.iso_kernel {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C} (f : X ⟶ Y)
    [has_kernel f] {Z : C} (l : Z ⟶ X) (i : Z ≅ kernel f) (h : iso.hom i ≫ kernel.ι f = l) :
    is_limit (kernel_fork.of_ι l (kernel.iso_kernel._proof_1 f l i h)) :=
  is_kernel.iso_kernel f l (limit.is_limit (parallel_pair f 0)) i h

/-- The kernel morphism of a zero morphism is an isomorphism -/
def kernel.ι_of_zero {C : Type u} [category C] [has_zero_morphisms C] (X : C) (Y : C) :
    is_iso (kernel.ι 0) :=
  equalizer.ι_of_self 0

/-- A cokernel cofork is just a cofork where the second morphism is a zero morphism. -/
def cokernel_cofork {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C} (f : X ⟶ Y) :=
  cofork f 0

@[simp] theorem cokernel_cofork.condition {C : Type u} [category C] [has_zero_morphisms C] {X : C}
    {Y : C} {f : X ⟶ Y} (s : cokernel_cofork f) : f ≫ cofork.π s = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (f ≫ cofork.π s = 0)) (cofork.condition s)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (0 ≫ cofork.π s = 0)) zero_comp)) (Eq.refl 0))

@[simp] theorem cokernel_cofork.app_zero {C : Type u} [category C] [has_zero_morphisms C] {X : C}
    {Y : C} {f : X ⟶ Y} (s : cokernel_cofork f) :
    nat_trans.app (cocone.ι s) walking_parallel_pair.zero = 0 :=
  sorry

/-- A morphism `π` satisfying `f ≫ π = 0` determines a cokernel cofork on `f`. -/
def cokernel_cofork.of_π {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C}
    {f : X ⟶ Y} {Z : C} (π : Y ⟶ Z) (w : f ≫ π = 0) : cokernel_cofork f :=
  cofork.of_π π sorry

@[simp] theorem cokernel_cofork.π_of_π {C : Type u} [category C] [has_zero_morphisms C] {X : C}
    {Y : C} {P : C} (f : X ⟶ Y) (π : Y ⟶ P) (w : f ≫ π = 0) :
    cofork.π (cokernel_cofork.of_π π w) = π :=
  rfl

/-- Every cokernel cofork `s` is isomorphic (actually, equal) to `cofork.of_π (cofork.π s) _`. -/
def iso_of_π {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C} {f : X ⟶ Y}
    (s : cofork f 0) : s ≅ cofork.of_π (cofork.π s) (iso_of_π._proof_1 s) :=
  cocones.ext (iso.refl (cocone.X s)) sorry

/-- If `π = π'`, then `cokernel_cofork.of_π π _` and `cokernel_cofork.of_π π' _` are isomorphic. -/
def of_π_congr {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C} {f : X ⟶ Y} {P : C}
    {π : Y ⟶ P} {π' : Y ⟶ P} {w : f ≫ π = 0} (h : π = π') :
    cokernel_cofork.of_π π w ≅ cokernel_cofork.of_π π' (of_π_congr._proof_1 h) :=
  cocones.ext (iso.refl (cocone.X (cokernel_cofork.of_π π w))) sorry

/-- If `s` is a colimit cokernel cofork, then every `k : Y ⟶ W` satisfying `f ≫ k = 0` induces
    `l : s.X ⟶ W` such that `cofork.π s ≫ l = k`. -/
def cokernel_cofork.is_colimit.desc' {C : Type u} [category C] [has_zero_morphisms C] {X : C}
    {Y : C} {f : X ⟶ Y} {s : cokernel_cofork f} (hs : is_colimit s) {W : C} (k : Y ⟶ W)
    (h : f ≫ k = 0) : Subtype fun (l : cocone.X s ⟶ W) => cofork.π s ≫ l = k :=
  { val := is_colimit.desc hs (cokernel_cofork.of_π k h), property := sorry }

/--
This is a slightly more convenient method to verify that a cokernel cofork is a colimit cocone.
It only asks for a proof of facts that carry any mathematical content -/
def is_colimit_aux {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C} {f : X ⟶ Y}
    (t : cokernel_cofork f) (desc : (s : cokernel_cofork f) → cocone.X t ⟶ cocone.X s)
    (fac : ∀ (s : cokernel_cofork f), cofork.π t ≫ desc s = cofork.π s)
    (uniq :
      ∀ (s : cokernel_cofork f) (m : cocone.X t ⟶ cocone.X s),
        cofork.π t ≫ m = cofork.π s → m = desc s) :
    is_colimit t :=
  is_colimit.mk desc

/--
This is a more convenient formulation to show that a `cokernel_cofork` constructed using
`cokernel_cofork.of_π` is a limit cone.
-/
def is_colimit.of_π {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C} {f : X ⟶ Y}
    {Z : C} (g : Y ⟶ Z) (eq : f ≫ g = 0) (desc : {Z' : C} → (g' : Y ⟶ Z') → f ≫ g' = 0 → (Z ⟶ Z'))
    (fac : ∀ {Z' : C} (g' : Y ⟶ Z') (eq' : f ≫ g' = 0), g ≫ desc g' eq' = g')
    (uniq :
      ∀ {Z' : C} (g' : Y ⟶ Z') (eq' : f ≫ g' = 0) (m : Z ⟶ Z'), g ≫ m = g' → m = desc g' eq') :
    is_colimit (cokernel_cofork.of_π g eq) :=
  is_colimit_aux (cokernel_cofork.of_π g eq)
    (fun (s : cokernel_cofork f) => desc (cofork.π s) (cokernel_cofork.condition s)) sorry sorry

/-- The cokernel of a morphism, expressed as the coequalizer with the 0 morphism. -/
def cokernel {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C} (f : X ⟶ Y)
    [has_cokernel f] : C :=
  coequalizer f 0

/-- The map from the target of `f` to `cokernel f`. -/
def cokernel.π {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C} (f : X ⟶ Y)
    [has_cokernel f] : Y ⟶ cokernel f :=
  coequalizer.π f 0

@[simp] theorem coequalizer_as_cokernel {C : Type u} [category C] [has_zero_morphisms C] {X : C}
    {Y : C} (f : X ⟶ Y) [has_cokernel f] : coequalizer.π f 0 = cokernel.π f :=
  rfl

@[simp] theorem cokernel.condition {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C}
    (f : X ⟶ Y) [has_cokernel f] : f ≫ cokernel.π f = 0 :=
  cokernel_cofork.condition (colimit.cocone (parallel_pair f 0))

/-- Given any morphism `k : Y ⟶ W` such that `f ≫ k = 0`, `k` factors through `cokernel.π f`
    via `cokernel.desc : cokernel f ⟶ W`. -/
def cokernel.desc {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C} (f : X ⟶ Y)
    [has_cokernel f] {W : C} (k : Y ⟶ W) (h : f ≫ k = 0) : cokernel f ⟶ W :=
  colimit.desc (parallel_pair f 0) (cokernel_cofork.of_π k h)

@[simp] theorem cokernel.π_desc {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C}
    (f : X ⟶ Y) [has_cokernel f] {W : C} (k : Y ⟶ W) (h : f ≫ k = 0) :
    cokernel.π f ≫ cokernel.desc f k h = k :=
  colimit.ι_desc (cokernel_cofork.of_π k h) walking_parallel_pair.one

@[simp] theorem cokernel.desc_zero {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C}
    (f : X ⟶ Y) [has_cokernel f] {W : C} {h : f ≫ 0 = 0} : cokernel.desc f 0 h = 0 :=
  sorry

protected instance cokernel.desc_epi {C : Type u} [category C] [has_zero_morphisms C] {X : C}
    {Y : C} (f : X ⟶ Y) [has_cokernel f] {W : C} (k : Y ⟶ W) (h : f ≫ k = 0) [epi k] :
    epi (cokernel.desc f k h) :=
  epi.mk
    fun (Z : C) (g g' : W ⟶ Z) (w : cokernel.desc f k h ≫ g = cokernel.desc f k h ≫ g') =>
      iff.mp (cancel_epi k)
        (eq.mp
          ((fun (a a_1 : Y ⟶ Z) (e_1 : a = a_1) (ᾰ ᾰ_1 : Y ⟶ Z) (e_2 : ᾰ = ᾰ_1) =>
              congr (congr_arg Eq e_1) e_2)
            (cokernel.π f ≫ cokernel.desc f k h ≫ g) (k ≫ g) (cokernel.π_desc_assoc f k h g)
            (cokernel.π f ≫ cokernel.desc f k h ≫ g') (k ≫ g') (cokernel.π_desc_assoc f k h g'))
          (cokernel.π f ≫= w))

/-- Any morphism `k : Y ⟶ W` satisfying `f ≫ k = 0` induces `l : cokernel f ⟶ W` such that
    `cokernel.π f ≫ l = k`. -/
def cokernel.desc' {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C} (f : X ⟶ Y)
    [has_cokernel f] {W : C} (k : Y ⟶ W) (h : f ≫ k = 0) :
    Subtype fun (l : cokernel f ⟶ W) => cokernel.π f ≫ l = k :=
  { val := cokernel.desc f k h, property := cokernel.π_desc f k h }

/-- The cokernel of the zero morphism is an isomorphism -/
protected instance cokernel.π_zero_is_iso {C : Type u} [category C] [has_zero_morphisms C] {X : C}
    {Y : C} : is_iso (cokernel.π 0) :=
  coequalizer.π_of_self 0

theorem eq_zero_of_mono_cokernel {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C}
    (f : X ⟶ Y) [has_cokernel f] [mono (cokernel.π f)] : f = 0 :=
  sorry

/-- The cokernel of a zero morphism is isomorphic to the target. -/
def cokernel_zero_iso_target {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C} :
    cokernel 0 ≅ Y :=
  coequalizer.iso_target_of_self 0

@[simp] theorem cokernel_zero_iso_target_hom {C : Type u} [category C] [has_zero_morphisms C]
    {X : C} {Y : C} :
    iso.hom cokernel_zero_iso_target =
        cokernel.desc 0 𝟙
          (eq.mpr
            (id
              (Eq.trans
                ((fun (a a_1 : X ⟶ Y) (e_1 : a = a_1) (ᾰ ᾰ_1 : X ⟶ Y) (e_2 : ᾰ = ᾰ_1) =>
                    congr (congr_arg Eq e_1) e_2)
                  (0 ≫ 𝟙) 0 zero_comp 0 0 (Eq.refl 0))
                (propext (eq_self_iff_true 0))))
            trivial) :=
  rfl

@[simp] theorem cokernel_zero_iso_target_inv {C : Type u} [category C] [has_zero_morphisms C]
    {X : C} {Y : C} : iso.inv cokernel_zero_iso_target = cokernel.π 0 :=
  rfl

/-- If two morphisms are known to be equal, then their cokernels are isomorphic. -/
def cokernel_iso_of_eq {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C} {f : X ⟶ Y}
    {g : X ⟶ Y} [has_cokernel f] [has_cokernel g] (h : f = g) : cokernel f ≅ cokernel g :=
  has_colimit.iso_of_nat_iso (eq.mpr sorry (iso.refl (parallel_pair g 0)))

@[simp] theorem cokernel_iso_of_eq_refl {C : Type u} [category C] [has_zero_morphisms C] {X : C}
    {Y : C} (f : X ⟶ Y) [has_cokernel f] {h : f = f} :
    cokernel_iso_of_eq h = iso.refl (cokernel f) :=
  sorry

@[simp] theorem cokernel_iso_of_eq_trans {C : Type u} [category C] [has_zero_morphisms C] {X : C}
    {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} {h : X ⟶ Y} [has_cokernel f] [has_cokernel g] [has_cokernel h]
    (w₁ : f = g) (w₂ : g = h) :
    cokernel_iso_of_eq w₁ ≪≫ cokernel_iso_of_eq w₂ = cokernel_iso_of_eq (Eq.trans w₁ w₂) :=
  sorry

theorem cokernel_not_mono_of_nonzero {C : Type u} [category C] [has_zero_morphisms C] {X : C}
    {Y : C} {f : X ⟶ Y} [has_cokernel f] (w : f ≠ 0) : ¬mono (cokernel.π f) :=
  fun (I : mono (cokernel.π f)) => w (eq_zero_of_mono_cokernel f)

theorem cokernel_not_iso_of_nonzero {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C}
    {f : X ⟶ Y} [has_cokernel f] (w : f ≠ 0) : is_iso (cokernel.π f) → False :=
  fun (I : is_iso (cokernel.π f)) => cokernel_not_mono_of_nonzero w (split_mono.mono (cokernel.π f))

/--
When `g` is an isomorphism, the cokernel of `f ≫ g` is isomorphic to the cokernel of `f`.
-/
def cokernel_comp_is_iso {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C} {Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) [has_cokernel (f ≫ g)] [has_cokernel f] [is_iso g] :
    cokernel (f ≫ g) ≅ cokernel f :=
  iso.mk (cokernel.desc (f ≫ g) (inv g ≫ cokernel.π f) sorry)
    (cokernel.desc f (g ≫ cokernel.π (f ≫ g)) sorry)

@[simp] theorem cokernel_π_comp_cokernel_comp_is_iso_hom {C : Type u} [category C]
    [has_zero_morphisms C] {X : C} {Y : C} {Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [has_cokernel (f ≫ g)]
    [has_cokernel f] [is_iso g] :
    cokernel.π (f ≫ g) ≫ iso.hom (cokernel_comp_is_iso f g) = inv g ≫ cokernel.π f :=
  sorry

@[simp] theorem cokernel_π_comp_cokernel_comp_is_iso_inv {C : Type u} [category C]
    [has_zero_morphisms C] {X : C} {Y : C} {Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [has_cokernel (f ≫ g)]
    [has_cokernel f] [is_iso g] :
    cokernel.π f ≫ iso.inv (cokernel_comp_is_iso f g) = g ≫ cokernel.π (f ≫ g) :=
  sorry

/--
When `f` is an isomorphism, the cokernel of `f ≫ g` is isomorphic to the cokernel of `g`.
-/
def cokernel_is_iso_comp {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C} {Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) [has_cokernel (f ≫ g)] [is_iso f] [has_cokernel g] :
    cokernel (f ≫ g) ≅ cokernel g :=
  iso.mk (cokernel.desc (f ≫ g) (cokernel.π g) sorry) (cokernel.desc g (cokernel.π (f ≫ g)) sorry)

@[simp] theorem cokernel_π_comp_cokernel_is_iso_comp_hom {C : Type u} [category C]
    [has_zero_morphisms C] {X : C} {Y : C} {Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [has_cokernel (f ≫ g)]
    [is_iso f] [has_cokernel g] :
    cokernel.π (f ≫ g) ≫ iso.hom (cokernel_is_iso_comp f g) = cokernel.π g :=
  sorry

@[simp] theorem cokernel_π_comp_cokernel_is_iso_comp_inv {C : Type u} [category C]
    [has_zero_morphisms C] {X : C} {Y : C} {Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [has_cokernel (f ≫ g)]
    [is_iso f] [has_cokernel g] :
    cokernel.π g ≫ iso.inv (cokernel_is_iso_comp f g) = cokernel.π (f ≫ g) :=
  sorry

/-- The morphism to the zero object determines a cocone on a cokernel diagram -/
def cokernel.zero_cocone {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C}
    (f : X ⟶ Y) [has_zero_object C] : cocone (parallel_pair f 0) :=
  cocone.mk 0 (nat_trans.mk fun (j : walking_parallel_pair) => 0)

/-- The morphism to the zero object is a cokernel of an epimorphism -/
def cokernel.is_colimit_cocone_zero_cocone {C : Type u} [category C] [has_zero_morphisms C] {X : C}
    {Y : C} (f : X ⟶ Y) [has_zero_object C] [epi f] : is_colimit (cokernel.zero_cocone f) :=
  cofork.is_colimit.mk (cokernel.zero_cocone f) (fun (s : cofork f 0) => 0) sorry sorry

/-- The cokernel of an epimorphism is isomorphic to the zero object -/
def cokernel.of_epi {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C} (f : X ⟶ Y)
    [has_zero_object C] [has_cokernel f] [epi f] : cokernel f ≅ 0 :=
  functor.map_iso (cocones.forget (parallel_pair f 0))
    (is_colimit.unique_up_to_iso (colimit.is_colimit (parallel_pair f 0))
      (cokernel.is_colimit_cocone_zero_cocone f))

/-- The cokernel morphism of an epimorphism is a zero morphism -/
theorem cokernel.π_of_epi {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C}
    (f : X ⟶ Y) [has_zero_object C] [has_cokernel f] [epi f] : cokernel.π f = 0 :=
  zero_of_target_iso_zero (cokernel.π f) (cokernel.of_epi f)

/--
The cokernel of the image inclusion of a morphism `f` is isomorphic to the cokernel of `f`.

(This result requires that the factorisation through the image is an epimorphism.
This holds in any category with equalizers.)
-/
@[simp] theorem cokernel_image_ι_inv {C : Type u} [category C] [has_zero_morphisms C] {X : C}
    {Y : C} (f : X ⟶ Y) [has_image f] [has_cokernel (image.ι f)] [has_cokernel f]
    [epi (factor_thru_image f)] :
    iso.inv (cokernel_image_ι f) =
        cokernel.desc f (cokernel.π (image.ι f)) (cokernel_image_ι._proof_2 f) :=
  Eq.refl (iso.inv (cokernel_image_ι f))

/-- The cokernel of a zero morphism is an isomorphism -/
def cokernel.π_of_zero {C : Type u} [category C] [has_zero_morphisms C] (X : C) (Y : C) :
    is_iso (cokernel.π 0) :=
  coequalizer.π_of_self 0

/-- The kernel of the cokernel of an epimorphism is an isomorphism -/
protected instance kernel.of_cokernel_of_epi {C : Type u} [category C] [has_zero_morphisms C]
    {X : C} {Y : C} (f : X ⟶ Y) [has_zero_object C] [has_cokernel f] [has_kernel (cokernel.π f)]
    [epi f] : is_iso (kernel.ι (cokernel.π f)) :=
  equalizer.ι_of_eq (cokernel.π_of_epi f)

/-- The cokernel of the kernel of a monomorphism is an isomorphism -/
protected instance cokernel.of_kernel_of_mono {C : Type u} [category C] [has_zero_morphisms C]
    {X : C} {Y : C} (f : X ⟶ Y) [has_zero_object C] [has_kernel f] [has_cokernel (kernel.ι f)]
    [mono f] : is_iso (cokernel.π (kernel.ι f)) :=
  coequalizer.π_of_eq (kernel.ι_of_mono f)

/-- If `i` is an isomorphism such that `i.hom ≫ l = f`, then any cokernel of `f` is a cokernel of
    `l`. -/
def is_cokernel.of_iso_comp {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C}
    (f : X ⟶ Y) {Z : C} (l : Z ⟶ Y) (i : X ≅ Z) (h : iso.hom i ≫ l = f) {s : cokernel_cofork f}
    (hs : is_colimit s) :
    is_colimit (cokernel_cofork.of_π (cofork.π s) (is_cokernel.of_iso_comp._proof_1 f l i h)) :=
  cofork.is_colimit.mk (cokernel_cofork.of_π (cofork.π s) sorry)
    (fun (s_1 : cofork l 0) => is_colimit.desc hs (cokernel_cofork.of_π (cofork.π s_1) sorry)) sorry
    sorry

/-- If `i` is an isomorphism such that `i.hom ≫ l = f`, then the cokernel of `f` is a cokernel of
    `l`. -/
def cokernel.of_iso_comp {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C}
    (f : X ⟶ Y) [has_cokernel f] {Z : C} (l : Z ⟶ Y) (i : X ≅ Z) (h : iso.hom i ≫ l = f) :
    is_colimit (cokernel_cofork.of_π (cokernel.π f) (cokernel.of_iso_comp._proof_1 f l i h)) :=
  is_cokernel.of_iso_comp f l i h (colimit.is_colimit (parallel_pair f 0))

/-- If `s` is any colimit cokernel cocone over `f` and `i` is an isomorphism such that
    `s.π ≫ i.hom = l`, then `l` is a cokernel of `f`. -/
def is_cokernel.cokernel_iso {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C}
    (f : X ⟶ Y) {Z : C} (l : Y ⟶ Z) {s : cokernel_cofork f} (hs : is_colimit s) (i : cocone.X s ≅ Z)
    (h : cofork.π s ≫ iso.hom i = l) :
    is_colimit (cokernel_cofork.of_π l (is_cokernel.cokernel_iso._proof_1 f l i h)) :=
  is_colimit.of_iso_colimit hs (cocones.ext i sorry)

/-- If `i` is an isomorphism such that `cokernel.π f ≫ i.hom = l`, then `l` is a cokernel of `f`. -/
def cokernel.cokernel_iso {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C}
    (f : X ⟶ Y) [has_cokernel f] {Z : C} (l : Y ⟶ Z) (i : cokernel f ≅ Z)
    (h : cokernel.π f ≫ iso.hom i = l) :
    is_colimit (cokernel_cofork.of_π l (cokernel.cokernel_iso._proof_1 f l i h)) :=
  is_cokernel.cokernel_iso f l (colimit.is_colimit (parallel_pair f 0)) i h

end category_theory.limits


namespace category_theory.limits


/-- `has_kernels` represents the existence of kernels for every morphism. -/
class has_kernels (C : Type u) [category C] [has_zero_morphisms C] where
  has_limit : ∀ {X Y : C} (f : X ⟶ Y), has_kernel f

/-- `has_cokernels` represents the existence of cokernels for every morphism. -/
class has_cokernels (C : Type u) [category C] [has_zero_morphisms C] where
  has_colimit : ∀ {X Y : C} (f : X ⟶ Y), has_cokernel f

protected instance has_kernels_of_has_equalizers (C : Type u) [category C] [has_zero_morphisms C]
    [has_equalizers C] : has_kernels C :=
  has_kernels.mk
    fun {X Y : C} (f : X ⟶ Y) => limits.has_limit_of_has_limits_of_shape (parallel_pair f 0)

protected instance has_cokernels_of_has_coequalizers (C : Type u) [category C]
    [has_zero_morphisms C] [has_coequalizers C] : has_cokernels C :=
  has_cokernels.mk
    fun {X Y : C} (f : X ⟶ Y) => limits.has_colimit_of_has_colimits_of_shape (parallel_pair f 0)

end Mathlib