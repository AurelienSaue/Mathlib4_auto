/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.abelian.exact
import Mathlib.category_theory.over
import PostPort

universes v u 

namespace Mathlib

/-!
# Pseudoelements in abelian categories

A *pseudoelement* of an object `X` in an abelian category `C` is an equivalence class of arrows
ending in `X`, where two arrows are considered equivalent if we can find two epimorphisms with a
common domain making a commutative square with the two arrows. While the construction shows that
pseudoelements are actually subobjects of `X` rather than "elements", it is possible to chase these
pseudoelements through commutative diagrams in an abelian category to prove exactness properties.
This is done using some "diagram-chasing metatheorems" proved in this file. In many cases, a proof
in the category of abelian groups can more or less directly be converted into a proof using
pseudoelements.

A classic application of pseudoelements are diagram lemmas like the four lemma or the snake lemma.

Pseudoelements are in some ways weaker than actual elements in a concrete category. The most
important limitation is that there is no extensionality principle: If `f g : X ⟶ Y`, then
`∀ x ∈ X, f x = g x` does not necessarily imply that `f = g` (however, if `f = 0` or `g = 0`,
it does). A corollary of this is that we can not define arrows in abelian categories by dictating
their action on pseudoelements. Thus, a usual style of proofs in abelian categories is this:
First, we construct some morphism using universal properties, and then we use diagram chasing
of pseudoelements to verify that is has some desirable property such as exactness.

It should be noted that the Freyd-Mitchell embedding theorem gives a vastly stronger notion of
pseudoelement (in particular one that gives extensionality). However, this theorem is quite
difficult to prove and probably out of reach for a formal proof for the time being.

## Main results

We define the type of pseudoelements of an object and, in particular, the zero pseudoelement.

We prove that every morphism maps the zero pseudoelement to the zero pseudoelement (`apply_zero`)
and that a zero morphism maps every pseudoelement to the zero pseudoelement (`zero_apply`)

Here are the metatheorems we provide:
* A morphism `f` is zero if and only if it is the zero function on pseudoelements.
* A morphism `f` is an epimorphism if and only if it is surjective on pseudoelements.
* A morphism `f` is a monomorphism if and only if it is injective on pseudoelements
  if and only if `∀ a, f a = 0 → f = 0`.
* A sequence `f, g` of morphisms is exact if and only if
  `∀ a, g (f a) = 0` and `∀ b, g b = 0 → ∃ a, f a = b`.
* If `f` is a morphism and `a, a'` are such that `f a = f a'`, then there is some
  pseudoelement `a''` such that `f a'' = 0` and for every `g` we have
  `g a' = 0 → g a = g a''`. We can think of `a''` as `a - a'`, but don't get too carried away
  by that: pseudoelements of an object do not form an abelian group.

## Notations

We introduce coercions from an object of an abelian category to the set of its pseudoelements
and from a morphism to the function it induces on pseudoelements.

These coercions must be explicitly enabled via local instances:
`local attribute [instance] object_to_sort hom_to_fun`

## Implementation notes

It appears that sometimes the coercion from morphisms to functions does not work, i.e.,
writing `g a` raises a "function expected" error. This error can be fixed by writing
`(g : X ⟶ Y) a`.

## References

* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]
-/

namespace category_theory.abelian


/-- This is just composition of morphisms in `C`. Another way to express this would be
    `(over.map f).obj a`, but our definition has nicer definitional properties. -/
def app {C : Type u} [category C] {P : C} {Q : C} (f : P ⟶ Q) (a : over P) : over Q :=
  ↑(comma.hom a ≫ f)

@[simp] theorem app_hom {C : Type u} [category C] {P : C} {Q : C} (f : P ⟶ Q) (a : over P) : comma.hom (app f a) = comma.hom a ≫ f :=
  rfl

/-- Two arrows `f : X ⟶ P` and `g : Y ⟶ P are called pseudo-equal if there is some object
    `R` and epimorphisms `p : R ⟶ X` and `q : R ⟶ Y` such that `p ≫ f = q ≫ g`. -/
def pseudo_equal {C : Type u} [category C] (P : C) (f : over P) (g : over P)  :=
  ∃ (R : C), ∃ (p : R ⟶ comma.left f), ∃ (q : R ⟶ comma.left g), Exists (Exists (p ≫ comma.hom f = q ≫ comma.hom g))

theorem pseudo_equal_refl {C : Type u} [category C] {P : C} : reflexive (pseudo_equal P) := sorry

theorem pseudo_equal_symm {C : Type u} [category C] {P : C} : symmetric (pseudo_equal P) := sorry

/-- Pseudoequality is transitive: Just take the pullback. The pullback morphisms will
    be epimorphisms since in an abelian category, pullbacks of epimorphisms are epimorphisms. -/
theorem pseudo_equal_trans {C : Type u} [category C] [abelian C] {P : C} : transitive (pseudo_equal P) := sorry

/-- The arrows with codomain `P` equipped with the equivalence relation of being pseudo-equal. -/
def pseudoelement.setoid {C : Type u} [category C] [abelian C] (P : C) : setoid (over P) :=
  setoid.mk (pseudo_equal P) sorry

/-- A `pseudoelement` of `P` is just an equivalence class of arrows ending in `P` by being
    pseudo-equal. -/
def pseudoelement {C : Type u} [category C] [abelian C] (P : C)  :=
  quotient sorry

namespace pseudoelement


/-- A coercion from an object of an abelian category to its pseudoelements. -/
def object_to_sort {C : Type u} [category C] [abelian C] : has_coe_to_sort C :=
  has_coe_to_sort.mk (Type (max u v)) fun (P : C) => pseudoelement P

/-- A coercion from an arrow with codomain `P` to its associated pseudoelement. -/
def over_to_sort {C : Type u} [category C] [abelian C] {P : C} : has_coe (over P) (pseudoelement P) :=
  has_coe.mk (Quot.mk (pseudo_equal P))

theorem over_coe_def {C : Type u} [category C] [abelian C] {P : C} {Q : C} (a : Q ⟶ P) : ↑a = quotient.mk ↑a :=
  rfl

/-- If two elements are pseudo-equal, then their composition with a morphism is, too. -/
theorem pseudo_apply_aux {C : Type u} [category C] [abelian C] {P : C} {Q : C} (f : P ⟶ Q) (a : over P) (b : over P) : a ≈ b → app f a ≈ app f b := sorry

/-- A morphism `f` induces a function `pseudo_apply f` on pseudoelements. -/
def pseudo_apply {C : Type u} [category C] [abelian C] {P : C} {Q : C} (f : P ⟶ Q) : ↥P → ↥Q :=
  quotient.map (fun (g : over P) => app f g) (pseudo_apply_aux f)

/-- A coercion from morphisms to functions on pseudoelements -/
def hom_to_fun {C : Type u} [category C] [abelian C] {P : C} {Q : C} : has_coe_to_fun (P ⟶ Q) :=
  has_coe_to_fun.mk (fun (x : P ⟶ Q) => ↥P → ↥Q) pseudo_apply

theorem pseudo_apply_mk {C : Type u} [category C] [abelian C] {P : C} {Q : C} (f : P ⟶ Q) (a : over P) : coe_fn f (quotient.mk a) = quotient.mk ↑(comma.hom a ≫ f) :=
  rfl

/-- Applying a pseudoelement to a composition of morphisms is the same as composing
    with each morphism. Sadly, this is not a definitional equality, but at least it is
    true. -/
theorem comp_apply {C : Type u} [category C] [abelian C] {P : C} {Q : C} {R : C} (f : P ⟶ Q) (g : Q ⟶ R) (a : ↥P) : coe_fn (f ≫ g) a = coe_fn g (coe_fn f a) := sorry

/-- Composition of functions on pseudoelements is composition of morphisms. -/
theorem comp_comp {C : Type u} [category C] [abelian C] {P : C} {Q : C} {R : C} (f : P ⟶ Q) (g : Q ⟶ R) : ⇑g ∘ ⇑f = ⇑(f ≫ g) :=
  funext fun (x : ↥P) => Eq.symm (comp_apply f g x)

/-!
In this section we prove that for every `P` there is an equivalence class that contains
precisely all the zero morphisms ending in `P` and use this to define *the* zero
pseudoelement.
-/

/-- The arrows pseudo-equal to a zero morphism are precisely the zero morphisms -/
theorem pseudo_zero_aux {C : Type u} [category C] [abelian C] {P : C} (Q : C) (f : over P) : f ≈ ↑0 ↔ comma.hom f = 0 := sorry

theorem zero_eq_zero' {C : Type u} [category C] [abelian C] {P : C} {Q : C} {R : C} : quotient.mk ↑0 = quotient.mk ↑0 :=
  quotient.sound (iff.mpr (pseudo_zero_aux R ↑0) rfl)

/-- The zero pseudoelement is the class of a zero morphism -/
def pseudo_zero {C : Type u} [category C] [abelian C] {P : C} : ↥P :=
  quotient.mk ↑0

protected instance has_zero {C : Type u} [category C] [abelian C] {P : C} : HasZero ↥P :=
  { zero := pseudo_zero }

protected instance inhabited {C : Type u} [category C] [abelian C] {P : C} : Inhabited (pseudoelement P) :=
  { default := 0 }

theorem pseudo_zero_def {C : Type u} [category C] [abelian C] {P : C} : 0 = quotient.mk ↑0 :=
  rfl

@[simp] theorem zero_eq_zero {C : Type u} [category C] [abelian C] {P : C} {Q : C} : quotient.mk ↑0 = 0 :=
  zero_eq_zero'

/-- The pseudoelement induced by an arrow is zero precisely when that arrow is zero -/
theorem pseudo_zero_iff {C : Type u} [category C] [abelian C] {P : C} (a : over P) : ↑a = 0 ↔ comma.hom a = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑a = 0 ↔ comma.hom a = 0)) (Eq.symm (propext (pseudo_zero_aux P a))))) quotient.eq

/-- Morphisms map the zero pseudoelement to the zero pseudoelement -/
@[simp] theorem apply_zero {C : Type u} [category C] [abelian C] {P : C} {Q : C} (f : P ⟶ Q) : coe_fn f 0 = 0 := sorry

/-- The zero morphism maps every pseudoelement to 0. -/
@[simp] theorem zero_apply {C : Type u} [category C] [abelian C] {P : C} (Q : C) (a : ↥P) : coe_fn 0 a = 0 := sorry

/-- An extensionality lemma for being the zero arrow. -/
theorem zero_morphism_ext {C : Type u} [category C] [abelian C] {P : C} {Q : C} (f : P ⟶ Q) : (∀ (a : ↥P), coe_fn f a = 0) → f = 0 :=
  fun (h : ∀ (a : ↥P), coe_fn f a = 0) =>
    eq.mpr (id (Eq._oldrec (Eq.refl (f = 0)) (Eq.symm (category.id_comp f)))) (iff.mp (pseudo_zero_iff ↑(𝟙 ≫ f)) (h ↑𝟙))

theorem zero_morphism_ext' {C : Type u} [category C] [abelian C] {P : C} {Q : C} (f : P ⟶ Q) : (∀ (a : ↥P), coe_fn f a = 0) → 0 = f :=
  Eq.symm ∘ zero_morphism_ext f

theorem eq_zero_iff {C : Type u} [category C] [abelian C] {P : C} {Q : C} (f : P ⟶ Q) : f = 0 ↔ ∀ (a : ↥P), coe_fn f a = 0 := sorry

/-- A monomorphism is injective on pseudoelements. -/
theorem pseudo_injective_of_mono {C : Type u} [category C] [abelian C] {P : C} {Q : C} (f : P ⟶ Q) [mono f] : function.injective ⇑f := sorry

/-- A morphism that is injective on pseudoelements only maps the zero element to zero. -/
theorem zero_of_map_zero {C : Type u} [category C] [abelian C] {P : C} {Q : C} (f : P ⟶ Q) : function.injective ⇑f → ∀ (a : ↥P), coe_fn f a = 0 → a = 0 :=
  fun (h : function.injective ⇑f) (a : ↥P) (ha : coe_fn f a = 0) =>
    h (eq.mp (Eq._oldrec (Eq.refl (coe_fn f a = 0)) (Eq.symm (apply_zero f))) ha)

/-- A morphism that only maps the zero pseudoelement to zero is a monomorphism. -/
theorem mono_of_zero_of_map_zero {C : Type u} [category C] [abelian C] {P : C} {Q : C} (f : P ⟶ Q) : (∀ (a : ↥P), coe_fn f a = 0 → a = 0) → mono f := sorry

/-- An epimorphism is surjective on pseudoelements. -/
theorem pseudo_surjective_of_epi {C : Type u} [category C] [abelian C] {P : C} {Q : C} (f : P ⟶ Q) [epi f] : function.surjective ⇑f := sorry

/-- A morphism that is surjective on pseudoelements is an epimorphism. -/
theorem epi_of_pseudo_surjective {C : Type u} [category C] [abelian C] {P : C} {Q : C} (f : P ⟶ Q) : function.surjective ⇑f → epi f := sorry

/-- Two morphisms in an exact sequence are exact on pseudoelements. -/
theorem pseudo_exact_of_exact {C : Type u} [category C] [abelian C] {P : C} {Q : C} {R : C} {f : P ⟶ Q} {g : Q ⟶ R} [exact f g] : (∀ (a : ↥P), coe_fn g (coe_fn f a) = 0) ∧ ∀ (b : ↥Q), coe_fn g b = 0 → ∃ (a : ↥P), coe_fn f a = b := sorry

theorem apply_eq_zero_of_comp_eq_zero {C : Type u} [category C] [abelian C] {P : C} {Q : C} {R : C} (f : Q ⟶ R) (a : P ⟶ Q) : a ≫ f = 0 → coe_fn f ↑a = 0 := sorry

/-- If two morphisms are exact on pseudoelements, they are exact. -/
theorem exact_of_pseudo_exact {C : Type u} [category C] [abelian C] {P : C} {Q : C} {R : C} (f : P ⟶ Q) (g : Q ⟶ R) : ((∀ (a : ↥P), coe_fn g (coe_fn f a) = 0) ∧ ∀ (b : ↥Q), coe_fn g b = 0 → ∃ (a : ↥P), coe_fn f a = b) → exact f g := sorry

/-- If two pseudoelements `x` and `y` have the same image under some morphism `f`, then we can form
    their "difference" `z`. This pseudoelement has the properties that `f z = 0` and for all
    morphisms `g`, if `g y = 0` then `g z = g x`. -/
theorem sub_of_eq_image {C : Type u} [category C] [abelian C] {P : C} {Q : C} (f : P ⟶ Q) (x : ↥P) (y : ↥P) : coe_fn f x = coe_fn f y → ∃ (z : ↥P), coe_fn f z = 0 ∧ ∀ (R : C) (g : P ⟶ R), coe_fn g y = 0 → coe_fn g z = coe_fn g x := sorry

/-- If `f : P ⟶ R` and `g : Q ⟶ R` are morphisms and `p : P` and `q : Q` are pseudoelements such
    that `f p = g q`, then there is some `s : pullback f g` such that `fst s = p` and `snd s = q`.

    Remark: Borceux claims that `s` is unique. I was unable to transform his proof sketch into
    a pen-and-paper proof of this fact, so naturally I was not able to formalize the proof. -/
theorem pseudo_pullback {C : Type u} [category C] [abelian C] [limits.has_pullbacks C] {P : C} {Q : C} {R : C} {f : P ⟶ R} {g : Q ⟶ R} {p : ↥P} {q : ↥Q} : coe_fn f p = coe_fn g q →
  ∃ (s : ↥(limits.pullback f g)), coe_fn limits.pullback.fst s = p ∧ coe_fn limits.pullback.snd s = q := sorry

