/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Bryan Gin-ge Chen
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.order.galois_connection
import PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Equivalence relations

This file defines the complete lattice of equivalence relations on a type, results about the
inductively defined equivalence closure of a binary relation, and the analogues of some isomorphism
theorems for quotients of arbitrary types.

## Implementation notes

The function `rel` and lemmas ending in ' make it easier to talk about different
equivalence relations on the same type.

The complete lattice instance for equivalence relations could have been defined by lifting
the Galois insertion of equivalence relations on α into binary relations on α, and then using
`complete_lattice.copy` to define a complete lattice instance with more appropriate
definitional equalities (a similar example is `filter.complete_lattice` in
`order/filter/basic.lean`). This does not save space, however, and is less clear.

Partitions are not defined as a separate structure here; users are encouraged to
reason about them using the existing `setoid` and its infrastructure.

## Tags

setoid, equivalence, iseqv, relation, equivalence relation
-/

/-- A version of `setoid.r` that takes the equivalence relation as an explicit argument. -/
def setoid.rel {α : Type u_1} (r : setoid α) : α → α → Prop :=
  setoid.r

/-- A version of `quotient.eq'` compatible with `setoid.rel`, to make rewriting possible. -/
theorem quotient.eq_rel {α : Type u_1} {r : setoid α} {x : α} {y : α} : quotient.mk x = quotient.mk y ↔ setoid.rel r x y :=
  quotient.eq'

namespace setoid


theorem ext' {α : Type u_1} {r : setoid α} {s : setoid α} (H : ∀ (a b : α), rel r a b ↔ rel s a b) : r = s :=
  ext H

theorem ext_iff {α : Type u_1} {r : setoid α} {s : setoid α} : r = s ↔ ∀ (a b : α), rel r a b ↔ rel s a b :=
  { mp := fun (h : r = s) (a b : α) => h ▸ iff.rfl, mpr := ext' }

/-- Two equivalence relations are equal iff their underlying binary operations are equal. -/
theorem eq_iff_rel_eq {α : Type u_1} {r₁ : setoid α} {r₂ : setoid α} : r₁ = r₂ ↔ rel r₁ = rel r₂ :=
  { mp := fun (h : r₁ = r₂) => h ▸ rfl, mpr := fun (h : rel r₁ = rel r₂) => ext' fun (x y : α) => h ▸ iff.rfl }

/-- Defining `≤` for equivalence relations. -/
protected instance has_le {α : Type u_1} : HasLessEq (setoid α) :=
  { LessEq := fun (r s : setoid α) => ∀ {x y : α}, rel r x y → rel s x y }

theorem le_def {α : Type u_1} {r : setoid α} {s : setoid α} : r ≤ s ↔ ∀ {x y : α}, rel r x y → rel s x y :=
  iff.rfl

theorem refl' {α : Type u_1} (r : setoid α) (x : α) : rel r x x :=
  and.left iseqv x

theorem symm' {α : Type u_1} (r : setoid α) {x : α} {y : α} : rel r x y → rel r y x :=
  fun (h : rel r _x✝ _x) => and.left (and.right iseqv) _x✝ _x h

theorem trans' {α : Type u_1} (r : setoid α) {x : α} {y : α} {z : α} : rel r x y → rel r y z → rel r x z :=
  fun (hx : rel r _x✝¹ _x✝) => and.right (and.right iseqv) _x✝¹ _x✝ _x hx

/-- The kernel of a function is an equivalence relation. -/
def ker {α : Type u_1} {β : Type u_2} (f : α → β) : setoid α :=
  mk (fun (x y : α) => f x = f y) sorry

/-- The kernel of the quotient map induced by an equivalence relation r equals r. -/
@[simp] theorem ker_mk_eq {α : Type u_1} (r : setoid α) : ker quotient.mk = r :=
  ext' fun (x y : α) => quotient.eq

theorem ker_def {α : Type u_1} {β : Type u_2} {f : α → β} {x : α} {y : α} : rel (ker f) x y ↔ f x = f y :=
  iff.rfl

/-- Given types `α`, `β`, the product of two equivalence relations `r` on `α` and `s` on `β`:
    `(x₁, x₂), (y₁, y₂) ∈ α × β` are related by `r.prod s` iff `x₁` is related to `y₁`
    by `r` and `x₂` is related to `y₂` by `s`. -/
protected def prod {α : Type u_1} {β : Type u_2} (r : setoid α) (s : setoid β) : setoid (α × β) :=
  mk (fun (x y : α × β) => rel r (prod.fst x) (prod.fst y) ∧ rel s (prod.snd x) (prod.snd y)) sorry

/-- The infimum of two equivalence relations. -/
protected instance has_inf {α : Type u_1} : has_inf (setoid α) :=
  has_inf.mk fun (r s : setoid α) => mk (fun (x y : α) => rel r x y ∧ rel s x y) sorry

/-- The infimum of 2 equivalence relations r and s is the same relation as the infimum
    of the underlying binary operations. -/
theorem inf_def {α : Type u_1} {r : setoid α} {s : setoid α} : rel (r ⊓ s) = rel r ⊓ rel s :=
  rfl

theorem inf_iff_and {α : Type u_1} {r : setoid α} {s : setoid α} {x : α} {y : α} : rel (r ⊓ s) x y ↔ rel r x y ∧ rel s x y :=
  iff.rfl

/-- The infimum of a set of equivalence relations. -/
protected instance has_Inf {α : Type u_1} : has_Inf (setoid α) :=
  has_Inf.mk fun (S : set (setoid α)) => mk (fun (x y : α) => ∀ (r : setoid α), r ∈ S → rel r x y) sorry

/-- The underlying binary operation of the infimum of a set of equivalence relations
    is the infimum of the set's image under the map to the underlying binary operation. -/
theorem Inf_def {α : Type u_1} {s : set (setoid α)} : rel (Inf s) = Inf (rel '' s) := sorry

protected instance partial_order {α : Type u_1} : partial_order (setoid α) :=
  partial_order.mk LessEq (fun (r s : setoid α) => r ≤ s ∧ ¬s ≤ r) sorry sorry sorry

/-- The complete lattice of equivalence relations on a type, with bottom element `=`
    and top element the trivial equivalence relation. -/
protected instance complete_lattice {α : Type u_1} : complete_lattice (setoid α) :=
  complete_lattice.mk complete_lattice.sup complete_lattice.le complete_lattice.lt sorry sorry sorry sorry sorry sorry
    has_inf.inf sorry sorry sorry (mk (fun (_x _x : α) => True) sorry) sorry (mk Eq sorry) sorry complete_lattice.Sup
    complete_lattice.Inf sorry sorry sorry sorry

/-- The inductively defined equivalence closure of a binary relation r is the infimum
    of the set of all equivalence relations containing r. -/
theorem eqv_gen_eq {α : Type u_1} (r : α → α → Prop) : eqv_gen.setoid r = Inf (set_of fun (s : setoid α) => ∀ {x y : α}, r x y → rel s x y) := sorry

/-- The supremum of two equivalence relations r and s is the equivalence closure of the binary
    relation `x is related to y by r or s`. -/
theorem sup_eq_eqv_gen {α : Type u_1} (r : setoid α) (s : setoid α) : r ⊔ s = eqv_gen.setoid fun (x y : α) => rel r x y ∨ rel s x y := sorry

/-- The supremum of 2 equivalence relations r and s is the equivalence closure of the
    supremum of the underlying binary operations. -/
theorem sup_def {α : Type u_1} {r : setoid α} {s : setoid α} : r ⊔ s = eqv_gen.setoid (rel r ⊔ rel s) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (r ⊔ s = eqv_gen.setoid (rel r ⊔ rel s))) (sup_eq_eqv_gen r s)))
    (Eq.refl (eqv_gen.setoid fun (x y : α) => rel r x y ∨ rel s x y))

/-- The supremum of a set S of equivalence relations is the equivalence closure of the binary
    relation `there exists r ∈ S relating x and y`. -/
theorem Sup_eq_eqv_gen {α : Type u_1} (S : set (setoid α)) : Sup S = eqv_gen.setoid fun (x y : α) => ∃ (r : setoid α), r ∈ S ∧ rel r x y := sorry

/-- The supremum of a set of equivalence relations is the equivalence closure of the
    supremum of the set's image under the map to the underlying binary operation. -/
theorem Sup_def {α : Type u_1} {s : set (setoid α)} : Sup s = eqv_gen.setoid (Sup (rel '' s)) := sorry

/-- The equivalence closure of an equivalence relation r is r. -/
@[simp] theorem eqv_gen_of_setoid {α : Type u_1} (r : setoid α) : eqv_gen.setoid r = r :=
  le_antisymm (eq.mpr (id (Eq._oldrec (Eq.refl (eqv_gen.setoid r ≤ r)) (eqv_gen_eq r))) (Inf_le fun (_x _x_1 : α) => id))
    eqv_gen.rel

/-- Equivalence closure is idempotent. -/
@[simp] theorem eqv_gen_idem {α : Type u_1} (r : α → α → Prop) : eqv_gen.setoid (rel (eqv_gen.setoid r)) = eqv_gen.setoid r :=
  eqv_gen_of_setoid (eqv_gen.setoid r)

/-- The equivalence closure of a binary relation r is contained in any equivalence
    relation containing r. -/
theorem eqv_gen_le {α : Type u_1} {r : α → α → Prop} {s : setoid α} (h : ∀ (x y : α), r x y → rel s x y) : eqv_gen.setoid r ≤ s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (eqv_gen.setoid r ≤ s)) (eqv_gen_eq r))) (Inf_le h)

/-- Equivalence closure of binary relations is monotonic. -/
theorem eqv_gen_mono {α : Type u_1} {r : α → α → Prop} {s : α → α → Prop} (h : ∀ (x y : α), r x y → s x y) : eqv_gen.setoid r ≤ eqv_gen.setoid s :=
  eqv_gen_le fun (_x _x_1 : α) (hr : r _x _x_1) => eqv_gen.rel _x _x_1 (h _x _x_1 hr)

/-- There is a Galois insertion of equivalence relations on α into binary relations
    on α, with equivalence closure the lower adjoint. -/
def gi {α : Type u_1} : galois_insertion eqv_gen.setoid rel :=
  galois_insertion.mk (fun (r : α → α → Prop) (h : rel (eqv_gen.setoid r) ≤ r) => eqv_gen.setoid r) sorry sorry sorry

/-- A function from α to β is injective iff its kernel is the bottom element of the complete lattice
    of equivalence relations on α. -/
theorem injective_iff_ker_bot {α : Type u_1} {β : Type u_2} (f : α → β) : function.injective f ↔ ker f = ⊥ :=
  iff.symm eq_bot_iff

/-- The elements related to x ∈ α by the kernel of f are those in the preimage of f(x) under f. -/
theorem ker_iff_mem_preimage {α : Type u_1} {β : Type u_2} {f : α → β} {x : α} {y : α} : rel (ker f) x y ↔ x ∈ f ⁻¹' singleton (f y) :=
  iff.rfl

/-- Equivalence between functions `α → β` such that `r x y → f x = f y` and functions
`quotient r → β`. -/
def lift_equiv {α : Type u_1} {β : Type u_2} (r : setoid α) : (Subtype fun (f : α → β) => r ≤ ker f) ≃ (quotient r → β) :=
  equiv.mk (fun (f : Subtype fun (f : α → β) => r ≤ ker f) => quotient.lift ↑f sorry)
    (fun (f : quotient r → β) => { val := f ∘ quotient.mk, property := sorry }) sorry sorry

/-- The uniqueness part of the universal property for quotients of an arbitrary type. -/
theorem lift_unique {α : Type u_1} {β : Type u_2} {r : setoid α} {f : α → β} (H : r ≤ ker f) (g : quotient r → β) (Hg : f = g ∘ quotient.mk) : quotient.lift f H = g := sorry

/-- Given a map f from α to β, the natural map from the quotient of α by the kernel of f is
    injective. -/
theorem ker_lift_injective {α : Type u_1} {β : Type u_2} (f : α → β) : function.injective (quotient.lift f fun (_x _x_1 : α) (h : _x ≈ _x_1) => h) := sorry

/-- Given a map f from α to β, the kernel of f is the unique equivalence relation on α whose
    induced map from the quotient of α to β is injective. -/
theorem ker_eq_lift_of_injective {α : Type u_1} {β : Type u_2} {r : setoid α} (f : α → β) (H : ∀ (x y : α), rel r x y → f x = f y) (h : function.injective (quotient.lift f H)) : ker f = r := sorry

/-- The first isomorphism theorem for sets: the quotient of α by the kernel of a function f
    bijects with f's image. -/
def quotient_ker_equiv_range {α : Type u_1} {β : Type u_2} (f : α → β) : quotient (ker f) ≃ ↥(set.range f) :=
  equiv.of_bijective (quotient.lift (fun (x : α) => { val := f x, property := set.mem_range_self x }) sorry) sorry

/-- The quotient of α by the kernel of a surjective function f bijects with f's codomain. -/
def quotient_ker_equiv_of_surjective {α : Type u_1} {β : Type u_2} (f : α → β) (hf : function.surjective f) : quotient (ker f) ≃ β :=
  equiv.trans (quotient_ker_equiv_range f) (equiv.subtype_univ_equiv hf)

/-- Given a function `f : α → β` and equivalence relation `r` on `α`, the equivalence
    closure of the relation on `f`'s image defined by '`x ≈ y` iff the elements of `f⁻¹(x)` are
    related to the elements of `f⁻¹(y)` by `r`.' -/
def map {α : Type u_1} {β : Type u_2} (r : setoid α) (f : α → β) : setoid β :=
  eqv_gen.setoid fun (x y : β) => ∃ (a : α), ∃ (b : α), f a = x ∧ f b = y ∧ rel r a b

/-- Given a surjective function f whose kernel is contained in an equivalence relation r, the
    equivalence relation on f's codomain defined by x ≈ y ↔ the elements of f⁻¹(x) are related to
    the elements of f⁻¹(y) by r. -/
def map_of_surjective {α : Type u_1} {β : Type u_2} (r : setoid α) (f : α → β) (h : ker f ≤ r) (hf : function.surjective f) : setoid β :=
  mk (fun (x y : β) => ∃ (a : α), ∃ (b : α), f a = x ∧ f b = y ∧ rel r a b) sorry

/-- A special case of the equivalence closure of an equivalence relation r equalling r. -/
theorem map_of_surjective_eq_map {α : Type u_1} {β : Type u_2} {r : setoid α} {f : α → β} (h : ker f ≤ r) (hf : function.surjective f) : map r f = map_of_surjective r f h hf := sorry

/-- Given a function `f : α → β`, an equivalence relation `r` on `β` induces an equivalence
    relation on `α` defined by '`x ≈ y` iff `f(x)` is related to `f(y)` by `r`'. -/
def comap {α : Type u_1} {β : Type u_2} (f : α → β) (r : setoid β) : setoid α :=
  mk (fun (x y : α) => rel r (f x) (f y)) sorry

/-- Given a map `f : N → M` and an equivalence relation `r` on `β`, the equivalence relation
    induced on `α` by `f` equals the kernel of `r`'s quotient map composed with `f`. -/
theorem comap_eq {α : Type u_1} {β : Type u_2} {f : α → β} {r : setoid β} : comap f r = ker (quotient.mk ∘ f) := sorry

/-- The second isomorphism theorem for sets. -/
def comap_quotient_equiv {α : Type u_1} {β : Type u_2} (f : α → β) (r : setoid β) : quotient (comap f r) ≃ ↥(set.range (quotient.mk ∘ f)) :=
  equiv.trans (quotient.congr_right sorry) (quotient_ker_equiv_range (quotient.mk ∘ f))

/-- The third isomorphism theorem for sets. -/
def quotient_quotient_equiv_quotient {α : Type u_1} (r : setoid α) (s : setoid α) (h : r ≤ s) : quotient (ker (quot.map_right h)) ≃ quotient s :=
  equiv.mk
    (fun (x : quotient (ker (quot.map_right h))) =>
      quotient.lift_on' x (fun (w : Quot fun (x y : α) => rel r x y) => quotient.lift_on' w quotient.mk sorry) sorry)
    (fun (x : quotient s) => quotient.lift_on' x (fun (w : α) => quotient.mk (quotient.mk w)) sorry) sorry sorry

/-- Given an equivalence relation `r` on `α`, the order-preserving bijection between the set of
equivalence relations containing `r` and the equivalence relations on the quotient of `α` by `r`. -/
def correspondence {α : Type u_1} (r : setoid α) : (Subtype fun (s : setoid α) => r ≤ s) ≃o setoid (quotient r) :=
  rel_iso.mk
    (equiv.mk
      (fun (s : Subtype fun (s : setoid α) => r ≤ s) =>
        map_of_surjective (subtype.val s) quotient.mk sorry quotient.exists_rep)
      (fun (s : setoid (quotient r)) => { val := comap quotient.mk s, property := sorry }) sorry sorry)
    sorry

