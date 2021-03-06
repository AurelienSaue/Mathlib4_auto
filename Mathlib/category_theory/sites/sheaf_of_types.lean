/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.sites.pretopology
import Mathlib.category_theory.limits.shapes.types
import Mathlib.category_theory.full_subcategory
import Mathlib.PostPort

universes v u 

namespace Mathlib

/-!
# Sheaves of types on a Grothendieck topology

Defines the notion of a sheaf of types (usually called a sheaf of sets by mathematicians)
on a category equipped with a Grothendieck topology, as well as a range of equivalent
conditions useful in different situations.

First define what it means for a presheaf `P : Cᵒᵖ ⥤ Type v` to be a sheaf *for* a particular
presieve `R` on `X`:
* A *family of elements* `x` for `P` at `R` is an element `x_f` of `P Y` for every `f : Y ⟶ X` in
  `R`. See `family_of_elements`.
* The family `x` is *compatible* if, for any `f₁ : Y₁ ⟶ X` and `f₂ : Y₂ ⟶ X` both in `R`,
  and any `g₁ : Z ⟶ Y₁` and `g₂ : Z ⟶ Y₂` such that `g₁ ≫ f₁ = g₂ ≫ f₂`, the restriction of
  `x_f₁` along `g₁` agrees with the restriction of `x_f₂` along `g₂`.
  See `family_of_elements.compatible`.
* An *amalgamation* `t` for the family is an element of `P X` such that for every `f : Y ⟶ X` in
  `R`, the restriction of `t` on `f` is `x_f`.
  See `family_of_elements.is_amalgamation`.
We then say `P` is *separated* for `R` if every compatible family has at most one amalgamation,
and it is a *sheaf* for `R` if every compatible family has a unique amalgamation.
See `is_separated_for` and `is_sheaf_for`.

In the special case where `R` is a sieve, the compatibility condition can be simplified:
* The family `x` is *compatible* if, for any `f : Y ⟶ X` in `R` and `g : Z ⟶ Y`, the restriction of
  `x_f` along `g` agrees with `x_(g ≫ f)` (which is well defined since `g ≫ f` is in `R`).
See `family_of_elements.sieve_compatible` and `compatible_iff_sieve_compatible`.

In the special case where `C` has pullbacks, the compatibility condition can be simplified:
* The family `x` is *compatible* if, for any `f : Y ⟶ X` and `g : Z ⟶ X` both in `R`,
  the restriction of `x_f` along `π₁ : pullback f g ⟶ Y` agrees with the restriction of `x_g`
  along `π₂ : pullback f g ⟶ Z`.
See `family_of_elements.pullback_compatible` and `pullback_compatible_iff`.

Now given a Grothendieck topology `J`, `P` is a sheaf if it is a sheaf for every sieve in the
topology. See `is_sheaf`.

In the case where the topology is generated by a basis, it suffices to check `P` is a sheaf for
every sieve in the pretopology. See `is_sheaf_pretopology`.

We also provide equivalent conditions to satisfy alternate definitions given in the literature.

* Stacks: In `equalizer.presieve.sheaf_condition`, the sheaf condition at a presieve is shown to be
  equivalent to that of https://stacks.math.columbia.edu/tag/00VM (and combined with
  `is_sheaf_pretopology`, this shows the notions of `is_sheaf` are exactly equivalent.)

  The condition of https://stacks.math.columbia.edu/tag/00Z8 is virtually identical to the
  statement of `yoneda_condition_iff_sheaf_condition` (since the bijection described there carries
  the same information as the unique existence.)

* Maclane-Moerdijk [MM92]: Using `compatible_iff_sieve_compatible`, the definitions of `is_sheaf`
  are equivalent. There are also alternate definitions given:
  - Yoneda condition: Defined in `yoneda_sheaf_condition` and equivalence in
    `yoneda_condition_iff_sheaf_condition`.
  - Equalizer condition (Equation 3): Defined in the `equalizer.sieve` namespace, and equivalence
    in `equalizer.sieve.sheaf_condition`.
  - Matching family for presieves with pullback: `pullback_compatible_iff`.
  - Sheaf for a pretopology (Prop 1): `is_sheaf_pretopology` combined with the previous.
  - Sheaf for a pretopology as equalizer (Prop 1, bis): `equalizer.presieve.sheaf_condition`
    combined with the previous.

## Implementation

The sheaf condition is given as a proposition, rather than a subsingleton in `Type (max u v)`.
This doesn't seem to make a big difference, other than making a couple of definitions noncomputable,
but it means that equivalent conditions can be given as `↔` statements rather than `≃` statements,
which can be convenient.

## References

* [MM92]: *Sheaves in geometry and logic*, Saunders MacLane, and Ieke Moerdijk:
  Chapter III, Section 4.
* [Elephant]: *Sketches of an Elephant*, P. T. Johnstone: C2.1.
* https://stacks.math.columbia.edu/tag/00VL (sheaves on a pretopology or site)
* https://stacks.math.columbia.edu/tag/00ZB (sheaves on a topology)

-/

namespace category_theory


namespace presieve


/--
A family of elements for a presheaf `P` given a collection of arrows `R` with fixed codomain `X`
consists of an element of `P Y` for every `f : Y ⟶ X` in `R`.
A presheaf is a sheaf (resp, separated) if every *compatible* family of elements has exactly one
(resp, at most one) amalgamation.

This data is referred to as a `family` in [MM92], Chapter III, Section 4. It is also a concrete
version of the elements of the middle object in https://stacks.math.columbia.edu/tag/00VM which is
more useful for direct calculations. It is also used implicitly in Definition C2.1.2 in [Elephant].
-/
def family_of_elements {C : Type u} [category C] {X : C} (P : Cᵒᵖ ⥤ Type v) (R : presieve X) :=
  {Y : C} → (f : Y ⟶ X) → R f → functor.obj P (opposite.op Y)

protected instance family_of_elements.inhabited {C : Type u} [category C] {P : Cᵒᵖ ⥤ Type v} {X : C} : Inhabited (family_of_elements P ⊥) :=
  { default := fun (Y : C) (f : Y ⟶ X) => false.elim }

/--
A family of elements for a presheaf on the presieve `R₂` can be restricted to a smaller presieve
`R₁`.
-/
def family_of_elements.restrict {C : Type u} [category C] {P : Cᵒᵖ ⥤ Type v} {X : C} {R₁ : presieve X} {R₂ : presieve X} (h : R₁ ≤ R₂) : family_of_elements P R₂ → family_of_elements P R₁ :=
  fun (x : family_of_elements P R₂) (Y : C) (f : Y ⟶ X) (hf : R₁ f) => x f (h Y hf)

/--
A family of elements for the arrow set `R` is *compatible* if for any `f₁ : Y₁ ⟶ X` and
`f₂ : Y₂ ⟶ X` in `R`, and any `g₁ : Z ⟶ Y₁` and `g₂ : Z ⟶ Y₂`, if the square `g₁ ≫ f₁ = g₂ ≫ f₂`
commutes then the elements of `P Z` obtained by restricting the element of `P Y₁` along `g₁` and
restricting the element of `P Y₂` along `g₂` are the same.

In special cases, this condition can be simplified, see `pullback_compatible_iff` and
`compatible_iff_sieve_compatible`.

This is referred to as a "compatible family" in Definition C2.1.2 of [Elephant], and on nlab:
https://ncatlab.org/nlab/show/sheaf#GeneralDefinitionInComponents
-/
def family_of_elements.compatible {C : Type u} [category C] {P : Cᵒᵖ ⥤ Type v} {X : C} {R : presieve X} (x : family_of_elements P R) :=
  ∀ {Y₁ Y₂ Z : C} (g₁ : Z ⟶ Y₁) (g₂ : Z ⟶ Y₂) {f₁ : Y₁ ⟶ X} {f₂ : Y₂ ⟶ X} (h₁ : R f₁) (h₂ : R f₂),
    g₁ ≫ f₁ = g₂ ≫ f₂ → functor.map P (has_hom.hom.op g₁) (x f₁ h₁) = functor.map P (has_hom.hom.op g₂) (x f₂ h₂)

/--
If the category `C` has pullbacks, this is an alternative condition for a family of elements to be
compatible: For any `f : Y ⟶ X` and `g : Z ⟶ X` in the presieve `R`, the restriction of the
given elements for `f` and `g` to the pullback agree.
This is equivalent to being compatible (provided `C` has pullbacks), shown in
`pullback_compatible_iff`.

This is the definition for a "matching" family given in [MM92], Chapter III, Section 4,
Equation (5). Viewing the type `family_of_elements` as the middle object of the fork in
https://stacks.math.columbia.edu/tag/00VM, this condition expresses that `pr₀* (x) = pr₁* (x)`,
using the notation defined there.
-/
def family_of_elements.pullback_compatible {C : Type u} [category C] {P : Cᵒᵖ ⥤ Type v} {X : C} {R : presieve X} (x : family_of_elements P R) [limits.has_pullbacks C] :=
  ∀ {Y₁ Y₂ : C} {f₁ : Y₁ ⟶ X} {f₂ : Y₂ ⟶ X} (h₁ : R f₁) (h₂ : R f₂),
    functor.map P (has_hom.hom.op limits.pullback.fst) (x f₁ h₁) =
      functor.map P (has_hom.hom.op limits.pullback.snd) (x f₂ h₂)

theorem pullback_compatible_iff {C : Type u} [category C] {P : Cᵒᵖ ⥤ Type v} {X : C} {R : presieve X} (x : family_of_elements P R) [limits.has_pullbacks C] : family_of_elements.compatible x ↔ family_of_elements.pullback_compatible x := sorry

/-- The restriction of a compatible family is compatible. -/
theorem family_of_elements.compatible.restrict {C : Type u} [category C] {P : Cᵒᵖ ⥤ Type v} {X : C} {R₁ : presieve X} {R₂ : presieve X} (h : R₁ ≤ R₂) {x : family_of_elements P R₂} : family_of_elements.compatible x → family_of_elements.compatible (family_of_elements.restrict h x) :=
  fun (q : family_of_elements.compatible x) (Y₁ Y₂ Z : C) (g₁ : Z ⟶ Y₁) (g₂ : Z ⟶ Y₂) (f₁ : Y₁ ⟶ X) (f₂ : Y₂ ⟶ X)
    (h₁ : R₁ f₁) (h₂ : R₁ f₂) (comm : g₁ ≫ f₁ = g₂ ≫ f₂) => q g₁ g₂ (h Y₁ h₁) (h Y₂ h₂) comm

/--
Extend a family of elements to the sieve generated by an arrow set.
This is the construction described as "easy" in Lemma C2.1.3 of [Elephant].
-/
def family_of_elements.sieve_extend {C : Type u} [category C] {P : Cᵒᵖ ⥤ Type v} {X : C} {R : presieve X} (x : family_of_elements P R) : family_of_elements P ⇑(sieve.generate R) :=
  fun (Z : C) (f : Z ⟶ X) (hf : coe_fn (sieve.generate R) Z f) =>
    functor.map P (has_hom.hom.op (classical.some sorry)) (x (classical.some sorry) sorry)

/-- The extension of a compatible family to the generated sieve is compatible. -/
theorem family_of_elements.compatible.sieve_extend {C : Type u} [category C] {P : Cᵒᵖ ⥤ Type v} {X : C} {R : presieve X} (x : family_of_elements P R) (hx : family_of_elements.compatible x) : family_of_elements.compatible (family_of_elements.sieve_extend x) := sorry

/-- The extension of a family agrees with the original family. -/
theorem extend_agrees {C : Type u} [category C] {P : Cᵒᵖ ⥤ Type v} {X : C} {Y : C} {R : presieve X} {x : family_of_elements P R} (t : family_of_elements.compatible x) {f : Y ⟶ X} (hf : R f) : family_of_elements.sieve_extend x f
    (Exists.intro Y (Exists.intro 𝟙 (Exists.intro f { left := hf, right := category.id_comp f }))) =
  x f hf := sorry

/-- The restriction of an extension is the original. -/
@[simp] theorem restrict_extend {C : Type u} [category C] {P : Cᵒᵖ ⥤ Type v} {X : C} {R : presieve X} {x : family_of_elements P R} (t : family_of_elements.compatible x) : family_of_elements.restrict (sieve.le_generate R) (family_of_elements.sieve_extend x) = x :=
  funext fun (Y : C) => funext fun (f : Y ⟶ X) => funext fun (hf : R f) => extend_agrees t hf

/--
If the arrow set for a family of elements is actually a sieve (i.e. it is downward closed) then the
consistency condition can be simplified.
This is an equivalent condition, see `compatible_iff_sieve_compatible`.

This is the notion of "matching" given for families on sieves given in [MM92], Chapter III,
Section 4, Equation 1, and nlab: https://ncatlab.org/nlab/show/matching+family.
See also the discussion before Lemma C2.1.4 of [Elephant].
-/
def family_of_elements.sieve_compatible {C : Type u} [category C] {P : Cᵒᵖ ⥤ Type v} {X : C} {S : sieve X} (x : family_of_elements P ⇑S) :=
  ∀ {Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) (hf : coe_fn S Y f),
    x (g ≫ f) (sieve.downward_closed S hf g) = functor.map P (has_hom.hom.op g) (x f hf)

theorem compatible_iff_sieve_compatible {C : Type u} [category C] {P : Cᵒᵖ ⥤ Type v} {X : C} {S : sieve X} (x : family_of_elements P ⇑S) : family_of_elements.compatible x ↔ family_of_elements.sieve_compatible x := sorry

theorem family_of_elements.compatible.to_sieve_compatible {C : Type u} [category C] {P : Cᵒᵖ ⥤ Type v} {X : C} {S : sieve X} {x : family_of_elements P ⇑S} (t : family_of_elements.compatible x) : family_of_elements.sieve_compatible x :=
  iff.mp (compatible_iff_sieve_compatible x) t

/--
Two compatible families on the sieve generated by a presieve `R` are equal if and only if they are
equal when restricted to `R`.
-/
theorem restrict_inj {C : Type u} [category C] {P : Cᵒᵖ ⥤ Type v} {X : C} {R : presieve X} {x₁ : family_of_elements P ⇑(sieve.generate R)} {x₂ : family_of_elements P ⇑(sieve.generate R)} (t₁ : family_of_elements.compatible x₁) (t₂ : family_of_elements.compatible x₂) : family_of_elements.restrict (sieve.le_generate R) x₁ = family_of_elements.restrict (sieve.le_generate R) x₂ → x₁ = x₂ := sorry

/--
Given a family of elements `x` for the sieve `S` generated by a presieve `R`, if `x` is restricted
to `R` and then extended back up to `S`, the resulting extension equals `x`.
-/
@[simp] theorem extend_restrict {C : Type u} [category C] {P : Cᵒᵖ ⥤ Type v} {X : C} {R : presieve X} {x : family_of_elements P ⇑(sieve.generate R)} (t : family_of_elements.compatible x) : family_of_elements.sieve_extend (family_of_elements.restrict (sieve.le_generate R) x) = x := sorry

/--
The given element `t` of `P.obj (op X)` is an *amalgamation* for the family of elements `x` if every
restriction `P.map f.op t = x_f` for every arrow `f` in the presieve `R`.

This is the definition given in  https://ncatlab.org/nlab/show/sheaf#GeneralDefinitionInComponents,
and https://ncatlab.org/nlab/show/matching+family, as well as [MM92], Chapter III, Section 4,
equation (2).
-/
def family_of_elements.is_amalgamation {C : Type u} [category C] {P : Cᵒᵖ ⥤ Type v} {X : C} {R : presieve X} (x : family_of_elements P R) (t : functor.obj P (opposite.op X)) :=
  ∀ {Y : C} (f : Y ⟶ X) (h : R f), functor.map P (has_hom.hom.op f) t = x f h

theorem is_compatible_of_exists_amalgamation {C : Type u} [category C] {P : Cᵒᵖ ⥤ Type v} {X : C} {R : presieve X} (x : family_of_elements P R) (h : ∃ (t : functor.obj P (opposite.op X)), family_of_elements.is_amalgamation x t) : family_of_elements.compatible x := sorry

theorem is_amalgamation_restrict {C : Type u} [category C] {P : Cᵒᵖ ⥤ Type v} {X : C} {R₁ : presieve X} {R₂ : presieve X} (h : R₁ ≤ R₂) (x : family_of_elements P R₂) (t : functor.obj P (opposite.op X)) (ht : family_of_elements.is_amalgamation x t) : family_of_elements.is_amalgamation (family_of_elements.restrict h x) t :=
  fun (Y : C) (f : Y ⟶ X) (hf : R₁ f) => ht f (h Y hf)

theorem is_amalgamation_sieve_extend {C : Type u} [category C] {P : Cᵒᵖ ⥤ Type v} {X : C} {R : presieve X} (x : family_of_elements P R) (t : functor.obj P (opposite.op X)) (ht : family_of_elements.is_amalgamation x t) : family_of_elements.is_amalgamation (family_of_elements.sieve_extend x) t := sorry

/-- A presheaf is separated for a presieve if there is at most one amalgamation. -/
def is_separated_for {C : Type u} [category C] {X : C} (P : Cᵒᵖ ⥤ Type v) (R : presieve X) :=
  ∀ (x : family_of_elements P R) (t₁ t₂ : functor.obj P (opposite.op X)),
    family_of_elements.is_amalgamation x t₁ → family_of_elements.is_amalgamation x t₂ → t₁ = t₂

theorem is_separated_for.ext {C : Type u} [category C] {P : Cᵒᵖ ⥤ Type v} {X : C} {R : presieve X} (hR : is_separated_for P R) {t₁ : functor.obj P (opposite.op X)} {t₂ : functor.obj P (opposite.op X)} (h : ∀ {Y : C} {f : Y ⟶ X}, R f → functor.map P (has_hom.hom.op f) t₁ = functor.map P (has_hom.hom.op f) t₂) : t₁ = t₂ :=
  hR (fun (Y : C) (f : Y ⟶ X) (hf : R f) => functor.map P (has_hom.hom.op f) t₂) t₁ t₂
    (fun (Y : C) (f : Y ⟶ X) (hf : R f) => h hf) fun (Y : C) (f : Y ⟶ X) (hf : R f) => rfl

theorem is_separated_for_iff_generate {C : Type u} [category C] {P : Cᵒᵖ ⥤ Type v} {X : C} {R : presieve X} : is_separated_for P R ↔ is_separated_for P ⇑(sieve.generate R) := sorry

theorem is_separated_for_top {C : Type u} [category C] {X : C} (P : Cᵒᵖ ⥤ Type v) : is_separated_for P ⊤ := sorry

/--
We define `P` to be a sheaf for the presieve `R` if every compatible family has a unique
amalgamation.

This is the definition of a sheaf for the given presieve given in C2.1.2 of [Elephant], and
https://ncatlab.org/nlab/show/sheaf#GeneralDefinitionInComponents. Using `compatible_iff_sieve_compatible`,
this is equivalent to the definition of a sheaf in [MM92], Chapter III, Section 4.
-/
def is_sheaf_for {C : Type u} [category C] {X : C} (P : Cᵒᵖ ⥤ Type v) (R : presieve X) :=
  ∀ (x : family_of_elements P R),
    family_of_elements.compatible x →
      exists_unique fun (t : functor.obj P (opposite.op X)) => family_of_elements.is_amalgamation x t

/--
This is an equivalent condition to be a sheaf, which is useful for the abstraction to local
operators on elementary toposes. However this definition is defined only for sieves, not presieves.
The equivalence between this and `is_sheaf_for` is given in `yoneda_condition_iff_sheaf_condition`.
This version is also useful to establish that being a sheaf is preserved under isomorphism of
presheaves.

See the discussion before Equation (3) of [MM92], Chapter III, Section 4. See also C2.1.4 of
[Elephant]. This is also a direct reformulation of https://stacks.math.columbia.edu/tag/00Z8.
-/
def yoneda_sheaf_condition {C : Type u} [category C] {X : C} (P : Cᵒᵖ ⥤ Type v) (S : sieve X) :=
  ∀ (f : sieve.functor S ⟶ P), exists_unique fun (g : functor.obj yoneda X ⟶ P) => sieve.functor_inclusion S ≫ g = f

/--
(Implementation). This is a (primarily internal) equivalence between natural transformations
and compatible families.

Cf the discussion after Lemma 7.47.10 in https://stacks.math.columbia.edu/tag/00YW. See also
the proof of C2.1.4 of [Elephant], and the discussion in [MM92], Chapter III, Section 4.
-/
def nat_trans_equiv_compatible_family {C : Type u} [category C] {P : Cᵒᵖ ⥤ Type v} {X : C} {S : sieve X} : (sieve.functor S ⟶ P) ≃ Subtype fun (x : family_of_elements P ⇑S) => family_of_elements.compatible x :=
  equiv.mk
    (fun (α : sieve.functor S ⟶ P) =>
      { val :=
          fun (Y : C) (f : Y ⟶ X) (hf : coe_fn S Y f) => nat_trans.app α (opposite.op Y) { val := f, property := hf },
        property := sorry })
    (fun (t : Subtype fun (x : family_of_elements P ⇑S) => family_of_elements.compatible x) =>
      nat_trans.mk
        fun (Y : Cᵒᵖ) (f : functor.obj (sieve.functor S) Y) => subtype.val t (opposite.unop Y) (subtype.val f) sorry)
    sorry sorry

/-- (Implementation). A lemma useful to prove `yoneda_condition_iff_sheaf_condition`. -/
theorem extension_iff_amalgamation {C : Type u} [category C] {P : Cᵒᵖ ⥤ Type v} {X : C} {S : sieve X} (x : sieve.functor S ⟶ P) (g : functor.obj yoneda X ⟶ P) : sieve.functor_inclusion S ≫ g = x ↔
  family_of_elements.is_amalgamation (subtype.val (coe_fn nat_trans_equiv_compatible_family x)) (coe_fn yoneda_equiv g) := sorry

/--
The yoneda version of the sheaf condition is equivalent to the sheaf condition.

C2.1.4 of [Elephant].
-/
theorem is_sheaf_for_iff_yoneda_sheaf_condition {C : Type u} [category C] {P : Cᵒᵖ ⥤ Type v} {X : C} {S : sieve X} : is_sheaf_for P ⇑S ↔ yoneda_sheaf_condition P S := sorry

/--
If `P` is a sheaf for the sieve `S` on `X`, a natural transformation from `S` (viewed as a functor)
to `P` can be (uniquely) extended to all of `yoneda.obj X`.

      f
   S  →  P
   ↓  ↗
   yX

-/
def is_sheaf_for.extend {C : Type u} [category C] {P : Cᵒᵖ ⥤ Type v} {X : C} {S : sieve X} (h : is_sheaf_for P ⇑S) (f : sieve.functor S ⟶ P) : functor.obj yoneda X ⟶ P :=
  classical.some sorry

/--
Show that the extension of `f : S.functor ⟶ P` to all of `yoneda.obj X` is in fact an extension, ie
that the triangle below commutes, provided `P` is a sheaf for `S`

      f
   S  →  P
   ↓  ↗
   yX

-/
@[simp] theorem is_sheaf_for.functor_inclusion_comp_extend {C : Type u} [category C] {P : Cᵒᵖ ⥤ Type v} {X : C} {S : sieve X} (h : is_sheaf_for P ⇑S) (f : sieve.functor S ⟶ P) : sieve.functor_inclusion S ≫ is_sheaf_for.extend h f = f :=
  classical.some_spec (exists_unique.exists (iff.mp is_sheaf_for_iff_yoneda_sheaf_condition h f))

/-- The extension of `f` to `yoneda.obj X` is unique. -/
theorem is_sheaf_for.unique_extend {C : Type u} [category C] {P : Cᵒᵖ ⥤ Type v} {X : C} {S : sieve X} (h : is_sheaf_for P ⇑S) {f : sieve.functor S ⟶ P} (t : functor.obj yoneda X ⟶ P) (ht : sieve.functor_inclusion S ≫ t = f) : t = is_sheaf_for.extend h f :=
  exists_unique.unique (iff.mp is_sheaf_for_iff_yoneda_sheaf_condition h f) ht
    (is_sheaf_for.functor_inclusion_comp_extend h f)

/--
If `P` is a sheaf for the sieve `S` on `X`, then if two natural transformations from `yoneda.obj X`
to `P` agree when restricted to the subfunctor given by `S`, they are equal.
-/
theorem is_sheaf_for.hom_ext {C : Type u} [category C] {P : Cᵒᵖ ⥤ Type v} {X : C} {S : sieve X} (h : is_sheaf_for P ⇑S) (t₁ : functor.obj yoneda X ⟶ P) (t₂ : functor.obj yoneda X ⟶ P) (ht : sieve.functor_inclusion S ≫ t₁ = sieve.functor_inclusion S ≫ t₂) : t₁ = t₂ :=
  Eq.trans (is_sheaf_for.unique_extend h t₁ ht) (Eq.symm (is_sheaf_for.unique_extend h t₂ rfl))

/-- `P` is a sheaf for `R` iff it is separated for `R` and there exists an amalgamation. -/
theorem is_separated_for_and_exists_is_amalgamation_iff_sheaf_for {C : Type u} [category C] {P : Cᵒᵖ ⥤ Type v} {X : C} {R : presieve X} : (is_separated_for P R ∧
    ∀ (x : family_of_elements P R),
      family_of_elements.compatible x → ∃ (t : functor.obj P (opposite.op X)), family_of_elements.is_amalgamation x t) ↔
  is_sheaf_for P R := sorry

/--
If `P` is separated for `R` and every family has an amalgamation, then `P` is a sheaf for `R`.
-/
theorem is_separated_for.is_sheaf_for {C : Type u} [category C] {P : Cᵒᵖ ⥤ Type v} {X : C} {R : presieve X} (t : is_separated_for P R) : (∀ (x : family_of_elements P R),
    family_of_elements.compatible x → ∃ (t : functor.obj P (opposite.op X)), family_of_elements.is_amalgamation x t) →
  is_sheaf_for P R := sorry

/-- If `P` is a sheaf for `R`, it is separated for `R`. -/
theorem is_sheaf_for.is_separated_for {C : Type u} [category C] {P : Cᵒᵖ ⥤ Type v} {X : C} {R : presieve X} : is_sheaf_for P R → is_separated_for P R :=
  fun (q : is_sheaf_for P R) => and.left (iff.mpr is_separated_for_and_exists_is_amalgamation_iff_sheaf_for q)

/-- Get the amalgamation of the given compatible family, provided we have a sheaf. -/
def is_sheaf_for.amalgamate {C : Type u} [category C] {P : Cᵒᵖ ⥤ Type v} {X : C} {R : presieve X} (t : is_sheaf_for P R) (x : family_of_elements P R) (hx : family_of_elements.compatible x) : functor.obj P (opposite.op X) :=
  classical.some sorry

theorem is_sheaf_for.is_amalgamation {C : Type u} [category C] {P : Cᵒᵖ ⥤ Type v} {X : C} {R : presieve X} (t : is_sheaf_for P R) {x : family_of_elements P R} (hx : family_of_elements.compatible x) : family_of_elements.is_amalgamation x (is_sheaf_for.amalgamate t x hx) :=
  classical.some_spec (exists_unique.exists (t x hx))

@[simp] theorem is_sheaf_for.valid_glue {C : Type u} [category C] {P : Cᵒᵖ ⥤ Type v} {X : C} {Y : C} {R : presieve X} (t : is_sheaf_for P R) {x : family_of_elements P R} (hx : family_of_elements.compatible x) (f : Y ⟶ X) (Hf : R f) : functor.map P (has_hom.hom.op f) (is_sheaf_for.amalgamate t x hx) = x f Hf :=
  is_sheaf_for.is_amalgamation t hx f Hf

/-- C2.1.3 in [Elephant] -/
theorem is_sheaf_for_iff_generate {C : Type u} [category C] {P : Cᵒᵖ ⥤ Type v} {X : C} (R : presieve X) : is_sheaf_for P R ↔ is_sheaf_for P ⇑(sieve.generate R) := sorry

/--
Every presheaf is a sheaf for the family {𝟙 X}.

[Elephant] C2.1.5(i)
-/
theorem is_sheaf_for_singleton_iso {C : Type u} [category C] {X : C} (P : Cᵒᵖ ⥤ Type v) : is_sheaf_for P (singleton 𝟙) := sorry

/--
Every presheaf is a sheaf for the maximal sieve.

[Elephant] C2.1.5(ii)
-/
theorem is_sheaf_for_top_sieve {C : Type u} [category C] {X : C} (P : Cᵒᵖ ⥤ Type v) : is_sheaf_for P ⇑⊤ := sorry

/--
If `P` is a sheaf for `S`, and it is iso to `P'`, then `P'` is a sheaf for `S`. This shows that
"being a sheaf for a presieve" is a mathematical or hygenic property.
-/
theorem is_sheaf_for_iso {C : Type u} [category C] {P : Cᵒᵖ ⥤ Type v} {X : C} {R : presieve X} {P' : Cᵒᵖ ⥤ Type v} (i : P ≅ P') : is_sheaf_for P R → is_sheaf_for P' R := sorry

/--
If a presieve `R` on `X` has a subsieve `S` such that:

* `P` is a sheaf for `S`.
* For every `f` in `R`, `P` is separated for the pullback of `S` along `f`,

then `P` is a sheaf for `R`.

This is closely related to [Elephant] C2.1.6(i).
-/
theorem is_sheaf_for_subsieve_aux {C : Type u} [category C] {X : C} (P : Cᵒᵖ ⥤ Type v) {S : sieve X} {R : presieve X} (h : ⇑S ≤ R) (hS : is_sheaf_for P ⇑S) (trans : ∀ {Y : C} {f : Y ⟶ X}, R f → is_separated_for P ⇑(sieve.pullback f S)) : is_sheaf_for P R := sorry

/--
If `P` is a sheaf for every pullback of the sieve `S`, then `P` is a sheaf for any presieve which
contains `S`.
This is closely related to [Elephant] C2.1.6.
-/
theorem is_sheaf_for_subsieve {C : Type u} [category C] {X : C} (P : Cᵒᵖ ⥤ Type v) {S : sieve X} {R : presieve X} (h : ⇑S ≤ R) (trans : ∀ {Y : C} (f : Y ⟶ X), is_sheaf_for P ⇑(sieve.pullback f S)) : is_sheaf_for P R := sorry

/-- A presheaf is separated for a topology if it is separated for every sieve in the topology. -/
def is_separated {C : Type u} [category C] (J : grothendieck_topology C) (P : Cᵒᵖ ⥤ Type v) :=
  ∀ {X : C} (S : sieve X), S ∈ coe_fn J X → is_separated_for P ⇑S

/--
A presheaf is a sheaf for a topology if it is a sheaf for every sieve in the topology.

If the given topology is given by a pretopology, `is_sheaf_for_pretopology` shows it suffices to
check the sheaf condition at presieves in the pretopology.
-/
def is_sheaf {C : Type u} [category C] (J : grothendieck_topology C) (P : Cᵒᵖ ⥤ Type v) :=
  ∀ {X : C} (S : sieve X), S ∈ coe_fn J X → is_sheaf_for P ⇑S

theorem is_sheaf.is_sheaf_for {C : Type u} [category C] {X : C} (J : grothendieck_topology C) {P : Cᵒᵖ ⥤ Type v} (hp : is_sheaf J P) (R : presieve X) (hr : sieve.generate R ∈ coe_fn J X) : is_sheaf_for P R :=
  iff.mpr (is_sheaf_for_iff_generate R) (hp (sieve.generate R) hr)

theorem is_sheaf_of_le {C : Type u} [category C] (P : Cᵒᵖ ⥤ Type v) {J₁ : grothendieck_topology C} {J₂ : grothendieck_topology C} : J₁ ≤ J₂ → is_sheaf J₂ P → is_sheaf J₁ P :=
  fun (h : J₁ ≤ J₂) (t : is_sheaf J₂ P) (X : C) (S : sieve X) (hS : S ∈ coe_fn J₁ X) => t S (h X hS)

theorem is_separated_of_is_sheaf {C : Type u} [category C] (J : grothendieck_topology C) (P : Cᵒᵖ ⥤ Type v) (h : is_sheaf J P) : is_separated J P :=
  fun (X : C) (S : sieve X) (hS : S ∈ coe_fn J X) => is_sheaf_for.is_separated_for (h S hS)

/-- The property of being a sheaf is preserved by isomorphism. -/
theorem is_sheaf_iso {C : Type u} [category C] {P : Cᵒᵖ ⥤ Type v} (J : grothendieck_topology C) {P' : Cᵒᵖ ⥤ Type v} (i : P ≅ P') (h : is_sheaf J P) : is_sheaf J P' :=
  fun (X : C) (S : sieve X) (hS : S ∈ coe_fn J X) => is_sheaf_for_iso i (h S hS)

theorem is_sheaf_of_yoneda {C : Type u} [category C] {P : Cᵒᵖ ⥤ Type v} (J : grothendieck_topology C) (h : ∀ {X : C} (S : sieve X), S ∈ coe_fn J X → yoneda_sheaf_condition P S) : is_sheaf J P :=
  fun (X : C) (S : sieve X) (hS : S ∈ coe_fn J X) => iff.mpr is_sheaf_for_iff_yoneda_sheaf_condition (h S hS)

/--
For a topology generated by a basis, it suffices to check the sheaf condition on the basis
presieves only.
-/
theorem is_sheaf_pretopology {C : Type u} [category C] {P : Cᵒᵖ ⥤ Type v} [limits.has_pullbacks C] (K : pretopology C) : is_sheaf (pretopology.to_grothendieck C K) P ↔ ∀ {X : C} (R : presieve X), R ∈ coe_fn K X → is_sheaf_for P R := sorry

/-- Any presheaf is a sheaf for the bottom (trivial) grothendieck topology. -/
theorem is_sheaf_bot {C : Type u} [category C] {P : Cᵒᵖ ⥤ Type v} : is_sheaf ⊥ P := sorry

end presieve


namespace equalizer


/--
The middle object of the fork diagram given in Equation (3) of [MM92], as well as the fork diagram
of https://stacks.math.columbia.edu/tag/00VM.
-/
def first_obj {C : Type v} [small_category C] (P : Cᵒᵖ ⥤ Type v) {X : C} (R : presieve X) :=
  ∏ fun (f : sigma fun (Y : C) => Subtype fun (f : Y ⟶ X) => R f) => functor.obj P (opposite.op (sigma.fst f))

/-- Show that `first_obj` is isomorphic to `family_of_elements`. -/
def first_obj_eq_family {C : Type v} [small_category C] (P : Cᵒᵖ ⥤ Type v) {X : C} (R : presieve X) : first_obj P R ≅ presieve.family_of_elements P R :=
  iso.mk
    (fun (t : first_obj P R) (Y : C) (f : Y ⟶ X) (hf : R f) =>
      limits.pi.π
        (fun (f : sigma fun (Y : C) => Subtype fun (f : Y ⟶ X) => R f) => functor.obj P (opposite.op (sigma.fst f)))
        (sigma.mk Y { val := f, property := hf }) t)
    (limits.pi.lift
      fun (f : sigma fun (Y : C) => Subtype fun (f : Y ⟶ X) => R f) (x : presieve.family_of_elements P R) =>
        x (subtype.val (sigma.snd f)) sorry)

protected instance first_obj.inhabited {C : Type v} [small_category C] (P : Cᵒᵖ ⥤ Type v) {X : C} : Inhabited (first_obj P ⊥) :=
  equiv.inhabited (iso.to_equiv (first_obj_eq_family P ⊥))

/--
The left morphism of the fork diagram given in Equation (3) of [MM92], as well as the fork diagram
of https://stacks.math.columbia.edu/tag/00VM.
-/
def fork_map {C : Type v} [small_category C] (P : Cᵒᵖ ⥤ Type v) {X : C} (R : presieve X) : functor.obj P (opposite.op X) ⟶ first_obj P R :=
  limits.pi.lift
    fun (f : sigma fun (Y : C) => Subtype fun (f : Y ⟶ X) => R f) =>
      functor.map P (has_hom.hom.op (subtype.val (sigma.snd f)))

/-!
This section establishes the equivalence between the sheaf condition of Equation (3) [MM92] and
the definition of `is_sheaf_for`.
-/

namespace sieve


/--
The rightmost object of the fork diagram of Equation (3) [MM92], which contains the data used
to check a family is compatible.
-/
def second_obj {C : Type v} [small_category C] (P : Cᵒᵖ ⥤ Type v) {X : C} (S : sieve X) :=
  ∏
    fun
      (f :
      sigma fun (Y : C) => sigma fun (Z : C) => sigma fun (g : Z ⟶ Y) => Subtype fun (f' : Y ⟶ X) => coe_fn S Y f') =>
      functor.obj P (opposite.op (sigma.fst (sigma.snd f)))

/-- The map `p` of Equations (3,4) [MM92]. -/
def first_map {C : Type v} [small_category C] (P : Cᵒᵖ ⥤ Type v) {X : C} (S : sieve X) : first_obj P ⇑S ⟶ second_obj P S :=
  limits.pi.lift
    fun
      (fg :
      sigma fun (Y : C) => sigma fun (Z : C) => sigma fun (g : Z ⟶ Y) => Subtype fun (f' : Y ⟶ X) => coe_fn S Y f') =>
      limits.pi.π
        (fun (f : sigma fun (Y : C) => Subtype fun (f : Y ⟶ X) => coe_fn S Y f) =>
          functor.obj P (opposite.op (sigma.fst f)))
        (sigma.mk (sigma.fst (sigma.snd fg))
          { val := sigma.fst (sigma.snd (sigma.snd fg)) ≫ subtype.val (sigma.snd (sigma.snd (sigma.snd fg))),
            property := sorry })

protected instance second_obj.inhabited {C : Type v} [small_category C] (P : Cᵒᵖ ⥤ Type v) {X : C} : Inhabited (second_obj P ⊥) :=
  { default := first_map P ⊥ Inhabited.default }

/-- The map `a` of Equations (3,4) [MM92]. -/
def second_map {C : Type v} [small_category C] (P : Cᵒᵖ ⥤ Type v) {X : C} (S : sieve X) : first_obj P ⇑S ⟶ second_obj P S :=
  limits.pi.lift
    fun
      (fg :
      sigma fun (Y : C) => sigma fun (Z : C) => sigma fun (g : Z ⟶ Y) => Subtype fun (f' : Y ⟶ X) => coe_fn S Y f') =>
      limits.pi.π
          (fun (f : sigma fun (Y : C) => Subtype fun (f : Y ⟶ X) => coe_fn S Y f) =>
            functor.obj P (opposite.op (sigma.fst f)))
          (sigma.mk (sigma.fst fg) (sigma.snd (sigma.snd (sigma.snd fg)))) ≫
        functor.map P (has_hom.hom.op (sigma.fst (sigma.snd (sigma.snd fg))))

theorem w {C : Type v} [small_category C] (P : Cᵒᵖ ⥤ Type v) {X : C} (S : sieve X) : fork_map P ⇑S ≫ first_map P S = fork_map P ⇑S ≫ second_map P S := sorry

/--
The family of elements given by `x : first_obj P S` is compatible iff `first_map` and `second_map`
map it to the same point.
-/
theorem compatible_iff {C : Type v} [small_category C] (P : Cᵒᵖ ⥤ Type v) {X : C} (S : sieve X) (x : first_obj P ⇑S) : presieve.family_of_elements.compatible (iso.hom (first_obj_eq_family P ⇑S) x) ↔ first_map P S x = second_map P S x := sorry

/-- `P` is a sheaf for `S`, iff the fork given by `w` is an equalizer. -/
theorem equalizer_sheaf_condition {C : Type v} [small_category C] (P : Cᵒᵖ ⥤ Type v) {X : C} (S : sieve X) : presieve.is_sheaf_for P ⇑S ↔ Nonempty (limits.is_limit (limits.fork.of_ι (fork_map P ⇑S) (w P S))) := sorry

end sieve


/-!
This section establishes the equivalence between the sheaf condition of
https://stacks.math.columbia.edu/tag/00VM and the definition of `is_sheaf_for`.
-/

namespace presieve


/--
The rightmost object of the fork diagram of https://stacks.math.columbia.edu/tag/00VM, which
contains the data used to check a family of elements for a presieve is compatible.
-/
def second_obj {C : Type v} [small_category C] (P : Cᵒᵖ ⥤ Type v) {X : C} (R : presieve X) [limits.has_pullbacks C] :=
  ∏
    fun
      (fg :
      (sigma fun (Y : C) => Subtype fun (f : Y ⟶ X) => R f) × sigma fun (Y : C) => Subtype fun (f : Y ⟶ X) => R f) =>
      functor.obj P
        (opposite.op (limits.pullback (subtype.val (sigma.snd (prod.fst fg))) (subtype.val (sigma.snd (prod.snd fg)))))

/-- The map `pr₀*` of https://stacks.math.columbia.edu/tag/00VL. -/
def first_map {C : Type v} [small_category C] (P : Cᵒᵖ ⥤ Type v) {X : C} (R : presieve X) [limits.has_pullbacks C] : first_obj P R ⟶ second_obj P R :=
  limits.pi.lift
    fun
      (fg :
      (sigma fun (Y : C) => Subtype fun (f : Y ⟶ X) => R f) × sigma fun (Y : C) => Subtype fun (f : Y ⟶ X) => R f) =>
      limits.pi.π
          (fun (f : sigma fun (Y : C) => Subtype fun (f : Y ⟶ X) => R f) => functor.obj P (opposite.op (sigma.fst f)))
          (prod.fst fg) ≫
        functor.map P (has_hom.hom.op limits.pullback.fst)

protected instance second_obj.inhabited {C : Type v} [small_category C] (P : Cᵒᵖ ⥤ Type v) {X : C} [limits.has_pullbacks C] : Inhabited (second_obj P ⊥) :=
  { default := first_map P ⊥ Inhabited.default }

/-- The map `pr₁*` of https://stacks.math.columbia.edu/tag/00VL. -/
def second_map {C : Type v} [small_category C] (P : Cᵒᵖ ⥤ Type v) {X : C} (R : presieve X) [limits.has_pullbacks C] : first_obj P R ⟶ second_obj P R :=
  limits.pi.lift
    fun
      (fg :
      (sigma fun (Y : C) => Subtype fun (f : Y ⟶ X) => R f) × sigma fun (Y : C) => Subtype fun (f : Y ⟶ X) => R f) =>
      limits.pi.π
          (fun (f : sigma fun (Y : C) => Subtype fun (f : Y ⟶ X) => R f) => functor.obj P (opposite.op (sigma.fst f)))
          (prod.snd fg) ≫
        functor.map P (has_hom.hom.op limits.pullback.snd)

theorem w {C : Type v} [small_category C] (P : Cᵒᵖ ⥤ Type v) {X : C} (R : presieve X) [limits.has_pullbacks C] : fork_map P R ≫ first_map P R = fork_map P R ≫ second_map P R := sorry

/--
The family of elements given by `x : first_obj P S` is compatible iff `first_map` and `second_map`
map it to the same point.
-/
theorem compatible_iff {C : Type v} [small_category C] (P : Cᵒᵖ ⥤ Type v) {X : C} (R : presieve X) [limits.has_pullbacks C] (x : first_obj P R) : presieve.family_of_elements.compatible (iso.hom (first_obj_eq_family P R) x) ↔ first_map P R x = second_map P R x := sorry

/--
`P` is a sheaf for `R`, iff the fork given by `w` is an equalizer.
See https://stacks.math.columbia.edu/tag/00VM.
-/
theorem sheaf_condition {C : Type v} [small_category C] (P : Cᵒᵖ ⥤ Type v) {X : C} (R : presieve X) [limits.has_pullbacks C] : presieve.is_sheaf_for P R ↔ Nonempty (limits.is_limit (limits.fork.of_ι (fork_map P R) (w P R))) := sorry

end presieve


end equalizer


/-- The category of sheaves on a grothendieck topology. -/
def SheafOfTypes {C : Type u} [category C] (J : grothendieck_topology C) :=
  Subtype fun (P : Cᵒᵖ ⥤ Type v) => presieve.is_sheaf J P

/-- The inclusion functor from sheaves to presheaves. -/
@[simp] theorem SheafOfTypes_to_presheaf_obj {C : Type u} [category C] (J : grothendieck_topology C) (c : Subtype fun (X : Cᵒᵖ ⥤ Type v) => presieve.is_sheaf J X) : functor.obj (SheafOfTypes_to_presheaf J) c = ↑c :=
  Eq.refl ↑c

/--
The category of sheaves on the bottom (trivial) grothendieck topology is equivalent to the category
of presheaves.
-/
@[simp] theorem SheafOfTypes_bot_equiv_functor {C : Type u} [category C] : equivalence.functor SheafOfTypes_bot_equiv = SheafOfTypes_to_presheaf ⊥ :=
  Eq.refl (equivalence.functor SheafOfTypes_bot_equiv)

protected instance SheafOfTypes.inhabited {C : Type u} [category C] : Inhabited (SheafOfTypes ⊥) :=
  { default := functor.obj (equivalence.inverse SheafOfTypes_bot_equiv) (functor.obj (functor.const (Cᵒᵖ)) PUnit) }

