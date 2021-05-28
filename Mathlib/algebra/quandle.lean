/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.zmod.basic
import Mathlib.data.equiv.mul_add
import Mathlib.tactic.group
import Mathlib.PostPort

universes u l u_1 u_2 u_3 

namespace Mathlib

/-!
# Racks and Quandles

This file defines racks and quandles, algebraic structures for sets
that bijectively act on themselves with a self-distributivity
property.  If `R` is a rack and `act : R → (R ≃ R)` is the self-action,
then the self-distributivity is, equivalently, that
```
act (act x y) = act x * act y * (act x)⁻¹
```
where multiplication is composition in `R ≃ R` as a group.
Quandles are racks such that `act x x = x` for all `x`.

One example of a quandle (not yet in mathlib) is the action of a Lie
algebra on itself, defined by `act x y = Ad (exp x) y`.

Quandles and racks were independently developed by multiple
mathematicians.  David Joyce introduced quandles in his thesis
[Joyce1982] to define an algebraic invariant of knot and link
complements that is analogous to the fundamental group of the
exterior, and he showed that the quandle associated to an oriented
knot is invariant up to orientation-reversed mirror image.  Racks were
used by Fenn and Rourke for framed codimension-2 knots and
links.[FennRourke1992]

The name "rack" came from wordplay by Conway and Wraith for the "wrack
and ruin" of forgetting everything but the conjugation operation for a
group.

## Main definitions

* `shelf` is a type with a self-distributive action
* `rack` is a shelf whose action for each element is invertible
* `quandle` is a rack whose action for an element fixes that element
* `quandle.conj` defines a quandle of a group acting on itself by conjugation.
* `shelf_hom` is homomorphisms of shelves, racks, and quandles.
* `rack.envel_group` gives the universal group the rack maps to as a conjugation quandle.
* `rack.opp` gives the rack with the action replaced by its inverse.

## Main statements
* `rack.envel_group` is left adjoint to `quandle.conj` (`to_envel_group.map`).
  The universality statements are `to_envel_group.univ` and `to_envel_group.univ_uniq`.

## Notation

The following notation is localized in `quandles`:

* `x ◃ y` is `shelf.act x y`
* `x ◃⁻¹ y` is `rack.inv_act x y`
* `S →◃ S'` is `shelf_hom S S'`

Use `open_locale quandles` to use these.

## Todo

* If g is the Lie algebra of a Lie group G, then (x ◃ y) = Ad (exp x) x forms a quandle
* If X is a symmetric space, then each point has a corresponding involution that acts on X, forming a quandle.
* Alexander quandle with `a ◃ b = t * b + (1 - t) * b`, with `a` and `b` elements of a module over Z[t,t⁻¹].
* If G is a group, H a subgroup, and z in H, then there is a quandle `(G/H;z)` defined by
  `yH ◃ xH = yzy⁻¹xH`.  Every homogeneous quandle (i.e., a quandle Q whose automorphism group acts
  transitively on Q as a set) is isomorphic to such a quandle.
  There is a generalization to this arbitrary quandles in [Joyce's paper (Theorem 7.2)][Joyce1982].

## Tags

rack, quandle
-/

/--
A *shelf* is a structure with a self-distributive binary operation.
The binary operation is regarded as a left action of the type on itself.
-/
class shelf (α : Type u) 
where
  act : α → α → α
  self_distrib : ∀ {x y z : α}, act x (act y z) = act (act x y) (act x z)

/--
The type of homomorphisms between shelves.
This is also the notion of rack and quandle homomorphisms.
-/
structure shelf_hom (S₁ : Type u_1) (S₂ : Type u_2) [shelf S₁] [shelf S₂] 
where
  to_fun : S₁ → S₂
  map_act' : ∀ {x y : S₁}, to_fun (shelf.act x y) = shelf.act (to_fun x) (to_fun y)

/--
A *rack* is an automorphic set (a set with an action on itself by
bijections) that is self-distributive.  It is a shelf such that each
element's action is invertible.

The notations `x ◃ y` and `x ◃⁻¹ y` denote the action and the
inverse action, respectively, and they are right associative.
-/
class rack (α : Type u) 
extends shelf α
where
  inv_act : α → α → α
  left_inv : ∀ (x : α), function.left_inverse (inv_act x) (shelf.act x)
  right_inv : ∀ (x : α), function.right_inverse (inv_act x) (shelf.act x)

namespace rack


theorem self_distrib {R : Type u_1} [rack R] {x : R} {y : R} {z : R} : shelf.act x (shelf.act y z) = shelf.act (shelf.act x y) (shelf.act x z) :=
  shelf.self_distrib

/--
A rack acts on itself by equivalences.
-/
def act {R : Type u_1} [rack R] (x : R) : R ≃ R :=
  equiv.mk (shelf.act x) (inv_act x) (left_inv x) (right_inv x)

@[simp] theorem act_apply {R : Type u_1} [rack R] (x : R) (y : R) : coe_fn (act x) y = shelf.act x y :=
  rfl

@[simp] theorem act_symm_apply {R : Type u_1} [rack R] (x : R) (y : R) : coe_fn (equiv.symm (act x)) y = inv_act x y :=
  rfl

@[simp] theorem inv_act_apply {R : Type u_1} [rack R] (x : R) (y : R) : coe_fn (act x⁻¹) y = inv_act x y :=
  rfl

@[simp] theorem inv_act_act_eq {R : Type u_1} [rack R] (x : R) (y : R) : inv_act x (shelf.act x y) = y :=
  left_inv x y

@[simp] theorem act_inv_act_eq {R : Type u_1} [rack R] (x : R) (y : R) : shelf.act x (inv_act x y) = y :=
  right_inv x y

theorem left_cancel {R : Type u_1} [rack R] (x : R) {y : R} {y' : R} : shelf.act x y = shelf.act x y' ↔ y = y' :=
  { mp := equiv.injective (act x), mpr := fun (ᾰ : y = y') => Eq._oldrec (Eq.refl (shelf.act x y)) ᾰ }

theorem left_cancel_inv {R : Type u_1} [rack R] (x : R) {y : R} {y' : R} : inv_act x y = inv_act x y' ↔ y = y' :=
  { mp := equiv.injective (equiv.symm (act x)), mpr := fun (ᾰ : y = y') => Eq._oldrec (Eq.refl (inv_act x y)) ᾰ }

theorem self_distrib_inv {R : Type u_1} [rack R] {x : R} {y : R} {z : R} : inv_act x (inv_act y z) = inv_act (inv_act x y) (inv_act x z) := sorry

/--
The *adjoint action* of a rack on itself is `op'`, and the adjoint
action of `x ◃ y` is the conjugate of the action of `y` by the action
of `x`. It is another way to understand the self-distributivity axiom.

This is used in the natural rack homomorphism `to_conj` from `R` to
`conj (R ≃ R)` defined by `op'`.
-/
theorem ad_conj {R : Type u_1} [rack R] (x : R) (y : R) : act (shelf.act x y) = act x * act y * (act x⁻¹) := sorry

/--
The opposite rack, swapping the roles of `◃` and `◃⁻¹`.
-/
protected instance opposite_rack {R : Type u_1} [rack R] : rack (Rᵒᵖ) :=
  mk (fun (x y : Rᵒᵖ) => opposite.op (shelf.act (opposite.unop x) (opposite.unop y))) sorry sorry

@[simp] theorem op_act_op_eq {R : Type u_1} [rack R] {x : R} {y : R} : shelf.act (opposite.op x) (opposite.op y) = opposite.op (inv_act x y) :=
  rfl

@[simp] theorem op_inv_act_op_eq {R : Type u_1} [rack R] {x : R} {y : R} : inv_act (opposite.op x) (opposite.op y) = opposite.op (shelf.act x y) :=
  rfl

@[simp] theorem self_act_act_eq {R : Type u_1} [rack R] {x : R} {y : R} : shelf.act (shelf.act x x) y = shelf.act x y := sorry

@[simp] theorem self_inv_act_inv_act_eq {R : Type u_1} [rack R] {x : R} {y : R} : inv_act (inv_act x x) y = inv_act x y := sorry

@[simp] theorem self_act_inv_act_eq {R : Type u_1} [rack R] {x : R} {y : R} : inv_act (shelf.act x x) y = inv_act x y := sorry

@[simp] theorem self_inv_act_act_eq {R : Type u_1} [rack R] {x : R} {y : R} : shelf.act (inv_act x x) y = shelf.act x y := sorry

theorem self_act_eq_iff_eq {R : Type u_1} [rack R] {x : R} {y : R} : shelf.act x x = shelf.act y y ↔ x = y := sorry

theorem self_inv_act_eq_iff_eq {R : Type u_1} [rack R] {x : R} {y : R} : inv_act x x = inv_act y y ↔ x = y := sorry

/--
The map `x ↦ x ◃ x` is a bijection.  (This has applications for the
regular isotopy version of the Reidemeister I move for knot diagrams.)
-/
def self_apply_equiv (R : Type u_1) [rack R] : R ≃ R :=
  equiv.mk (fun (x : R) => shelf.act x x) (fun (x : R) => inv_act x x) sorry sorry

/--
An involutory rack is one for which `rack.op R x` is an involution for every x.
-/
def is_involutory (R : Type u_1) [rack R]  :=
  ∀ (x : R), function.involutive (shelf.act x)

theorem involutory_inv_act_eq_act {R : Type u_1} [rack R] (h : is_involutory R) (x : R) (y : R) : inv_act x y = shelf.act x y :=
  eq.mpr (id (Eq._oldrec (Eq.refl (inv_act x y = shelf.act x y)) (Eq.symm (propext (left_cancel x)))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (shelf.act x (inv_act x y) = shelf.act x (shelf.act x y))) (right_inv x y)))
      (Eq.symm (function.involutive.left_inverse (h x) y)))

/--
An abelian rack is one for which the mediality axiom holds.
-/
def is_abelian (R : Type u_1) [rack R]  :=
  ∀ (x y z w : R), shelf.act (shelf.act x y) (shelf.act z w) = shelf.act (shelf.act x z) (shelf.act y w)

/--
Associative racks are uninteresting.
-/
theorem assoc_iff_id {R : Type u_1} [rack R] {x : R} {y : R} {z : R} : shelf.act x (shelf.act y z) = shelf.act (shelf.act x y) z ↔ shelf.act x z = z := sorry

end rack


namespace shelf_hom


protected instance has_coe_to_fun {S₁ : Type u_1} {S₂ : Type u_2} [shelf S₁] [shelf S₂] : has_coe_to_fun (shelf_hom S₁ S₂) :=
  has_coe_to_fun.mk (fun (x : shelf_hom S₁ S₂) => S₁ → S₂) to_fun

@[simp] theorem to_fun_eq_coe {S₁ : Type u_1} {S₂ : Type u_2} [shelf S₁] [shelf S₂] (f : shelf_hom S₁ S₂) : to_fun f = ⇑f :=
  rfl

@[simp] theorem map_act {S₁ : Type u_1} {S₂ : Type u_2} [shelf S₁] [shelf S₂] (f : shelf_hom S₁ S₂) {x : S₁} {y : S₁} : coe_fn f (shelf.act x y) = shelf.act (coe_fn f x) (coe_fn f y) :=
  map_act' f

/-- The identity homomorphism -/
def id (S : Type u_1) [shelf S] : shelf_hom S S :=
  mk id sorry

protected instance inhabited (S : Type u_1) [shelf S] : Inhabited (shelf_hom S S) :=
  { default := id S }

/-- The composition of shelf homomorphisms -/
def comp {S₁ : Type u_1} {S₂ : Type u_2} {S₃ : Type u_3} [shelf S₁] [shelf S₂] [shelf S₃] (g : shelf_hom S₂ S₃) (f : shelf_hom S₁ S₂) : shelf_hom S₁ S₃ :=
  mk (to_fun g ∘ to_fun f) sorry

@[simp] theorem comp_apply {S₁ : Type u_1} {S₂ : Type u_2} {S₃ : Type u_3} [shelf S₁] [shelf S₂] [shelf S₃] (g : shelf_hom S₂ S₃) (f : shelf_hom S₁ S₂) (x : S₁) : coe_fn (comp g f) x = coe_fn g (coe_fn f x) :=
  rfl

end shelf_hom


/--
A quandle is a rack such that each automorphism fixes its corresponding element.
-/
class quandle (α : Type u_1) 
extends rack α
where
  fix : ∀ {x : α}, shelf.act x x = x

namespace quandle


@[simp] theorem fix_inv {Q : Type u_1} [quandle Q] {x : Q} : rack.inv_act x x = x := sorry

protected instance opposite_quandle {Q : Type u_1} [quandle Q] : quandle (Qᵒᵖ) :=
  mk sorry

/--
The conjugation quandle of a group.  Each element of the group acts by
the corresponding inner automorphism.
-/
def conj (G : Type u_1)  :=
  G

protected instance conj.quandle (G : Type u_1) [group G] : quandle (conj G) :=
  mk sorry

@[simp] theorem conj_act_eq_conj {G : Type u_1} [group G] (x : conj G) (y : conj G) : shelf.act x y = x * y * (x⁻¹) :=
  rfl

theorem conj_swap {G : Type u_1} [group G] (x : conj G) (y : conj G) : shelf.act x y = y ↔ shelf.act y x = x := sorry

/--
`conj` is functorial
-/
def conj.map {G : Type u_1} {H : Type u_2} [group G] [group H] (f : G →* H) : shelf_hom (conj G) (conj H) :=
  shelf_hom.mk ⇑f sorry

protected instance shelf_hom.has_lift {G : Type u_1} {H : Type u_2} [group G] [group H] : has_lift (G →* H) (shelf_hom (conj G) (conj H)) :=
  has_lift.mk conj.map

/--
The dihedral quandle. This is the conjugation quandle of the dihedral group restrict to flips.

Used for Fox n-colorings of knots.
-/
def dihedral (n : ℕ)  :=
  zmod n

/--
The operation for the dihedral quandle.  It does not need to be an equivalence
because it is an involution (see `dihedral_act.inv`).
-/
def dihedral_act (n : ℕ) (a : zmod n) : zmod n → zmod n :=
  fun (b : zmod n) => bit0 1 * a - b

theorem dihedral_act.inv (n : ℕ) (a : zmod n) : function.involutive (dihedral_act n a) := sorry

protected instance dihedral.quandle (n : ℕ) : quandle (dihedral n) :=
  mk sorry

end quandle


namespace rack


/--
This is the natural rack homomorphism to the conjugation quandle of the group `R ≃ R`
that acts on the rack.
-/
def to_conj (R : Type u_1) [rack R] : shelf_hom R (quandle.conj (R ≃ R)) :=
  shelf_hom.mk act ad_conj

/-!
### Universal enveloping group of a rack

The universal enveloping group `envel_group R` of a rack `R` is the
universal group such that every rack homomorphism `R →◃ conj G` is
induced by a unique group homomorphism `envel_group R →* G`.
For quandles, Joyce called this group `AdConj R`.

The `envel_group` functor is left adjoint to the `conj` forgetful
functor, and the way we construct the enveloping group is via a
technique that should work for left adjoints of forgetful functors in
general.  It involves thinking a little about 2-categories, but the
payoff is that the map `envel_group R →* G` has a nice description.

Let's think of a group as being a one-object category.  The first step
is to define `pre_envel_group`, which gives formal expressions for all
the 1-morphisms and includes the unit element, elements of `R`,
multiplication, and inverses.  To introduce relations, the second step
is to define `pre_envel_group_rel'`, which gives formal expressions
for all 2-morphisms between the 1-morphisms.  The 2-morphisms include
associativity, multiplication by the unit, multiplication by inverses,
compatibility with multiplication and inverses (`congr_mul` and
`congr_inv`), the axioms for an equivalence relation, and,
importantly, the relationship between conjugation and the rack action
(see `rack.ad_conj`).

None of this forms a 2-category yet, for example due to lack of
associativity of `trans`.  The `pre_envel_group_rel` relation is a
`Prop`-valued version of `pre_envel_group_rel'`, and making it
`Prop`-valued essentially introduces enough 3-isomorphisms so that
every pair of compatible 2-morphisms is isomorphic.  Now, while
composition in `pre_envel_group` does not strictly satisfy the category
axioms, `pre_envel_group` and `pre_envel_group_rel'` do form a weak
2-category.

Since we just want a 1-category, the last step is to quotient
`pre_envel_group` by `pre_envel_group_rel'`, and the result is the
group `envel_group`.

For a homomorphism `f : R →◃ conj G`, how does
`envel_group.map f : envel_group R →* G` work?  Let's think of `G` as
being a 2-category with one object, a 1-morphism per element of `G`,
and a single 2-morphism called `eq.refl` for each 1-morphism.  We
define the map using a "higher `quotient.lift`" -- not only do we
evaluate elements of `pre_envel_group` as expressions in `G` (this is
`to_envel_group.map_aux`), but we evaluate elements of
`pre_envel_group'` as expressions of 2-morphisms of `G` (this is
`to_envel_group.map_aux.well_def`).  That is to say,
`to_envel_group.map_aux.well_def` recursively evaluates formal
expressions of 2-morphisms as equality proofs in `G`.  Now that all
morphisms are accounted for, the map descends to a homomorphism
`envel_group R →* G`.

Note: `Type`-valued relations are not common.  The fact it is
`Type`-valued is what makes `to_envel_group.map_aux.well_def` have
well-founded recursion.
-/

/--
Free generators of the enveloping group.
-/
inductive pre_envel_group (R : Type u) 
where
| unit : pre_envel_group R
| incl : R → pre_envel_group R
| mul : pre_envel_group R → pre_envel_group R → pre_envel_group R
| inv : pre_envel_group R → pre_envel_group R

protected instance pre_envel_group.inhabited (R : Type u) : Inhabited (pre_envel_group R) :=
  { default := pre_envel_group.unit }

/--
Relations for the enveloping group. This is a type-valued relation because
`to_envel_group.map_aux.well_def` inducts on it to show `to_envel_group.map`
is well-defined.  The relation `pre_envel_group_rel` is the `Prop`-valued version,
which is used to define `envel_group` itself.
-/
inductive pre_envel_group_rel' (R : Type u) [rack R] : pre_envel_group R → pre_envel_group R → Type u
where
| refl : {a : pre_envel_group R} → pre_envel_group_rel' R a a
| symm : {a b : pre_envel_group R} → pre_envel_group_rel' R a b → pre_envel_group_rel' R b a
| trans : {a b c : pre_envel_group R} → pre_envel_group_rel' R a b → pre_envel_group_rel' R b c → pre_envel_group_rel' R a c
| congr_mul : {a b a' b' : pre_envel_group R} →
  pre_envel_group_rel' R a a' →
    pre_envel_group_rel' R b b' → pre_envel_group_rel' R (pre_envel_group.mul a b) (pre_envel_group.mul a' b')
| congr_inv : {a a' : pre_envel_group R} →
  pre_envel_group_rel' R a a' → pre_envel_group_rel' R (pre_envel_group.inv a) (pre_envel_group.inv a')
| assoc : (a b c : pre_envel_group R) →
  pre_envel_group_rel' R (pre_envel_group.mul (pre_envel_group.mul a b) c)
    (pre_envel_group.mul a (pre_envel_group.mul b c))
| one_mul : (a : pre_envel_group R) → pre_envel_group_rel' R (pre_envel_group.mul pre_envel_group.unit a) a
| mul_one : (a : pre_envel_group R) → pre_envel_group_rel' R (pre_envel_group.mul a pre_envel_group.unit) a
| mul_left_inv : (a : pre_envel_group R) → pre_envel_group_rel' R (pre_envel_group.mul (pre_envel_group.inv a) a) pre_envel_group.unit
| act_incl : (x y : R) →
  pre_envel_group_rel' R
    (pre_envel_group.mul (pre_envel_group.mul (pre_envel_group.incl x) (pre_envel_group.incl y))
      (pre_envel_group.inv (pre_envel_group.incl x)))
    (pre_envel_group.incl (shelf.act x y))

protected instance pre_envel_group_rel'.inhabited (R : Type u) [rack R] : Inhabited (pre_envel_group_rel' R pre_envel_group.unit pre_envel_group.unit) :=
  { default := pre_envel_group_rel'.refl }

/--
The `pre_envel_group_rel` relation as a `Prop`.  Used as the relation for `pre_envel_group.setoid`.
-/
inductive pre_envel_group_rel (R : Type u) [rack R] : pre_envel_group R → pre_envel_group R → Prop
where
| rel : ∀ {a b : pre_envel_group R}, pre_envel_group_rel' R a b → pre_envel_group_rel R a b

/--
A quick way to convert a `pre_envel_group_rel'` to a `pre_envel_group_rel`.
-/
theorem pre_envel_group_rel'.rel {R : Type u} [rack R] {a : pre_envel_group R} {b : pre_envel_group R} : pre_envel_group_rel' R a b → pre_envel_group_rel R a b :=
  pre_envel_group_rel.rel

theorem pre_envel_group_rel.refl {R : Type u} [rack R] {a : pre_envel_group R} : pre_envel_group_rel R a a :=
  pre_envel_group_rel.rel pre_envel_group_rel'.refl

theorem pre_envel_group_rel.symm {R : Type u} [rack R] {a : pre_envel_group R} {b : pre_envel_group R} : pre_envel_group_rel R a b → pre_envel_group_rel R b a := sorry

theorem pre_envel_group_rel.trans {R : Type u} [rack R] {a : pre_envel_group R} {b : pre_envel_group R} {c : pre_envel_group R} : pre_envel_group_rel R a b → pre_envel_group_rel R b c → pre_envel_group_rel R a c := sorry

protected instance pre_envel_group.setoid (R : Type u_1) [rack R] : setoid (pre_envel_group R) :=
  setoid.mk (pre_envel_group_rel R) sorry

/--
The universal enveloping group for the rack R.
-/
def envel_group (R : Type u_1) [rack R]  :=
  quotient (pre_envel_group.setoid R)

-- Define the `group` instances in two steps so `inv` can be inferred correctly.

-- TODO: is there a non-invasive way of defining the instance directly?

protected instance envel_group.div_inv_monoid (R : Type u_1) [rack R] : div_inv_monoid (envel_group R) :=
  div_inv_monoid.mk
    (fun (a b : envel_group R) =>
      quotient.lift_on₂ a b (fun (a b : pre_envel_group R) => quotient.mk (pre_envel_group.mul a b)) sorry)
    sorry (quotient.mk pre_envel_group.unit) sorry sorry
    (fun (a : envel_group R) =>
      quotient.lift_on a (fun (a : pre_envel_group R) => quotient.mk (pre_envel_group.inv a)) sorry)
    fun (a b : envel_group R) =>
      quotient.lift_on₂ a (quotient.lift_on b (fun (a : pre_envel_group R) => quotient.mk (pre_envel_group.inv a)) sorry)
        (fun (a b : pre_envel_group R) => quotient.mk (pre_envel_group.mul a b)) sorry

protected instance envel_group.group (R : Type u_1) [rack R] : group (envel_group R) :=
  group.mk div_inv_monoid.mul sorry div_inv_monoid.one sorry sorry div_inv_monoid.inv div_inv_monoid.div sorry

protected instance envel_group.inhabited (R : Type u_1) [rack R] : Inhabited (envel_group R) :=
  { default := 1 }

/--
The canonical homomorphism from a rack to its enveloping group.
Satisfies universal properties given by `to_envel_group.map` and `to_envel_group.univ`.
-/
def to_envel_group (R : Type u_1) [rack R] : shelf_hom R (quandle.conj (envel_group R)) :=
  shelf_hom.mk (fun (x : R) => quotient.mk (pre_envel_group.incl x)) sorry

/--
The preliminary definition of the induced map from the enveloping group.
See `to_envel_group.map`.
-/
def to_envel_group.map_aux {R : Type u_1} [rack R] {G : Type u_2} [group G] (f : shelf_hom R (quandle.conj G)) : pre_envel_group R → G :=
  sorry

namespace to_envel_group.map_aux


/--
Show that `to_envel_group.map_aux` sends equivalent expressions to equal terms.
-/
theorem well_def {R : Type u_1} [rack R] {G : Type u_2} [group G] (f : shelf_hom R (quandle.conj G)) {a : pre_envel_group R} {b : pre_envel_group R} : pre_envel_group_rel' R a b → map_aux f a = map_aux f b := sorry

end to_envel_group.map_aux


/--
Given a map from a rack to a group, lift it to being a map from the enveloping group.
More precisely, the `envel_group` functor is left adjoint to `quandle.conj`.
-/
def to_envel_group.map {R : Type u_1} [rack R] {G : Type u_2} [group G] : shelf_hom R (quandle.conj G) ≃ (envel_group R →* G) :=
  equiv.mk
    (fun (f : shelf_hom R (quandle.conj G)) =>
      monoid_hom.mk (fun (x : envel_group R) => quotient.lift_on x (to_envel_group.map_aux f) sorry) sorry sorry)
    (fun (F : envel_group R →* G) => shelf_hom.comp (quandle.conj.map F) (to_envel_group R)) sorry sorry

/--
Given a homomorphism from a rack to a group, it factors through the enveloping group.
-/
theorem to_envel_group.univ (R : Type u_1) [rack R] (G : Type u_2) [group G] (f : shelf_hom R (quandle.conj G)) : shelf_hom.comp (quandle.conj.map (coe_fn to_envel_group.map f)) (to_envel_group R) = f :=
  equiv.symm_apply_apply to_envel_group.map f

/--
The homomorphism `to_envel_group.map f` is the unique map that fits into the commutative
triangle in `to_envel_group.univ`.
-/
theorem to_envel_group.univ_uniq (R : Type u_1) [rack R] (G : Type u_2) [group G] (f : shelf_hom R (quandle.conj G)) (g : envel_group R →* G) (h : f = shelf_hom.comp (quandle.conj.map g) (to_envel_group R)) : g = coe_fn to_envel_group.map f :=
  Eq.symm h ▸ Eq.symm (equiv.apply_symm_apply to_envel_group.map g)

/--
The induced group homomorphism from the enveloping group into bijections of the rack,
using `rack.to_conj`. Satisfies the property `envel_action_prop`.

This gives the rack `R` the structure of an augmented rack over `envel_group R`.
-/
def envel_action {R : Type u_1} [rack R] : envel_group R →* R ≃ R :=
  coe_fn to_envel_group.map (to_conj R)

@[simp] theorem envel_action_prop {R : Type u_1} [rack R] (x : R) (y : R) : coe_fn (coe_fn envel_action (coe_fn (to_envel_group R) x)) y = shelf.act x y :=
  rfl

