/-
Copyright (c) 2020 Kyle Miller All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kyle Miller.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.linarith.default
import Mathlib.data.sym
import Mathlib.PostPort

universes u u_1 u_2 u_3 

namespace Mathlib

/-!
# The symmetric square

This file defines the symmetric square, which is `α × α` modulo
swapping.  This is also known as the type of unordered pairs.

More generally, the symmetric square is the second symmetric power
(see `data.sym`). The equivalence is `sym2.equiv_sym`.

From the point of view that an unordered pair is equivalent to a
multiset of cardinality two (see `sym2.equiv_multiset`), there is a
`has_mem` instance `sym2.mem`, which is a `Prop`-valued membership
test.  Given `h : a ∈ z` for `z : sym2 α`, then `h.other` is the other
element of the pair, defined using `classical.choice`.  If `α` has
decidable equality, then `h.other'` computably gives the other element.

Recall that an undirected graph (allowing self loops, but no multiple
edges) is equivalent to a symmetric relation on the vertex type `α`.
Given a symmetric relation on `α`, the corresponding edge set is
constructed by `sym2.from_rel`.

## Notation

The symmetric square has a setoid instance, so `⟦(a, b)⟧` denotes a
term of the symmetric square.

## Tags

symmetric square, unordered pairs, symmetric powers
-/

namespace sym2


/--
This is the relation capturing the notion of pairs equivalent up to permutations.
-/
inductive rel (α : Type u) : α × α → α × α → Prop where
| refl : ∀ (x y : α), rel α (x, y) (x, y)
| swap : ∀ (x y : α), rel α (x, y) (y, x)

theorem rel.symm {α : Type u} {x : α × α} {y : α × α} : rel α x y → rel α y x := sorry

theorem rel.trans {α : Type u} {x : α × α} {y : α × α} {z : α × α} :
    rel α x y → rel α y z → rel α x z :=
  sorry

theorem rel.is_equivalence {α : Type u} : equivalence (rel α) := sorry

protected instance rel.setoid (α : Type u) : setoid (α × α) := setoid.mk (rel α) rel.is_equivalence

end sym2


/--
`sym2 α` is the symmetric square of `α`, which, in other words, is the
type of unordered pairs.

It is equivalent in a natural way to multisets of cardinality 2 (see
`sym2.equiv_multiset`).
-/
def sym2 (α : Type u) := quotient sorry

namespace sym2


theorem eq_swap {α : Type u} {a : α} {b : α} : quotient.mk (a, b) = quotient.mk (b, a) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (quotient.mk (a, b) = quotient.mk (b, a))) (propext quotient.eq)))
    (rel.swap a b)

theorem congr_right {α : Type u} {a : α} {b : α} {c : α} :
    quotient.mk (a, b) = quotient.mk (a, c) ↔ b = c :=
  sorry

theorem congr_left {α : Type u} {a : α} {b : α} {c : α} :
    quotient.mk (b, a) = quotient.mk (c, a) ↔ b = c :=
  sorry

/--
The functor `sym2` is functorial, and this function constructs the induced maps.
-/
def map {α : Type u_1} {β : Type u_2} (f : α → β) : sym2 α → sym2 β :=
  quotient.map (prod.map f f) sorry

@[simp] theorem map_id {α : Type u} : map id = id := sorry

theorem map_comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} {g : β → γ} {f : α → β} :
    map (g ∘ f) = map g ∘ map f :=
  sorry

@[simp] theorem map_pair_eq {α : Type u_1} {β : Type u_2} (f : α → β) (x : α) (y : α) :
    map f (quotient.mk (x, y)) = quotient.mk (f x, f y) :=
  sorry

/-! ### Declarations about membership -/

/--
This is a predicate that determines whether a given term is a member of a term of the
symmetric square.  From this point of view, the symmetric square is the subtype of
cardinality-two multisets on `α`.
-/
def mem {α : Type u} (x : α) (z : sym2 α) := ∃ (y : α), z = quotient.mk (x, y)

protected instance has_mem {α : Type u} : has_mem α (sym2 α) := has_mem.mk mem

theorem mk_has_mem {α : Type u} (x : α) (y : α) : x ∈ quotient.mk (x, y) := Exists.intro y rfl

theorem mk_has_mem_right {α : Type u} (x : α) (y : α) : y ∈ quotient.mk (x, y) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (y ∈ quotient.mk (x, y))) eq_swap)) (mk_has_mem y x)

/--
Given an element of the unordered pair, give the other element using `classical.some`.
See also `mem.other'` for the computable version.
-/
def mem.other {α : Type u} {a : α} {z : sym2 α} (h : a ∈ z) : α := classical.some h

@[simp] theorem mem_other_spec {α : Type u} {a : α} {z : sym2 α} (h : a ∈ z) :
    quotient.mk (a, mem.other h) = z :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (quotient.mk (a, mem.other h) = z)) (Eq.symm (classical.some_spec h))))
    (Eq.refl z)

theorem eq_iff {α : Type u} {x : α} {y : α} {z : α} {w : α} :
    quotient.mk (x, y) = quotient.mk (z, w) ↔ x = z ∧ y = w ∨ x = w ∧ y = z :=
  sorry

@[simp] theorem mem_iff {α : Type u} {a : α} {b : α} {c : α} :
    a ∈ quotient.mk (b, c) ↔ a = b ∨ a = c :=
  sorry

theorem mem_other_mem {α : Type u} {a : α} {z : sym2 α} (h : a ∈ z) : mem.other h ∈ z := sorry

theorem elems_iff_eq {α : Type u} {x : α} {y : α} {z : sym2 α} (hne : x ≠ y) :
    x ∈ z ∧ y ∈ z ↔ z = quotient.mk (x, y) :=
  sorry

theorem sym2_ext {α : Type u} (z : sym2 α) (z' : sym2 α) (h : ∀ (x : α), x ∈ z ↔ x ∈ z') : z = z' :=
  sorry

protected instance mem.decidable {α : Type u} [DecidableEq α] (x : α) (z : sym2 α) :
    Decidable (x ∈ z) :=
  quotient.rec_on_subsingleton z fun (_x : α × α) => sorry

/--
A type `α` is naturally included in the diagonal of `α × α`, and this function gives the image
of this diagonal in `sym2 α`.
-/
def diag {α : Type u} (x : α) : sym2 α := quotient.mk (x, x)

/--
A predicate for testing whether an element of `sym2 α` is on the diagonal.
-/
def is_diag {α : Type u} (z : sym2 α) := z ∈ set.range diag

@[simp] theorem diag_is_diag {α : Type u} (a : α) : is_diag (diag a) :=
  Exists.intro a (id (Eq.refl (diag a)))

@[simp] theorem is_diag_iff_proj_eq {α : Type u} (z : α × α) :
    is_diag (quotient.mk z) ↔ prod.fst z = prod.snd z :=
  sorry

protected instance is_diag.decidable_pred (α : Type u) [DecidableEq α] : decidable_pred is_diag :=
  fun (z : sym2 α) =>
    quotient.rec_on_subsingleton z
      fun (a : α × α) => eq.mpr sorry (_inst_1 (prod.fst a) (prod.snd a))

theorem mem_other_ne {α : Type u} {a : α} {z : sym2 α} (hd : ¬is_diag z) (h : a ∈ z) :
    mem.other h ≠ a :=
  sorry

/-! ### Declarations about symmetric relations -/

/--
Symmetric relations define a set on `sym2 α` by taking all those pairs
of elements that are related.
-/
def from_rel {α : Type u} {r : α → α → Prop} (sym : symmetric r) : set (sym2 α) :=
  quotient.lift (function.uncurry r) sorry

@[simp] theorem from_rel_proj_prop {α : Type u} {r : α → α → Prop} {sym : symmetric r} {z : α × α} :
    quotient.mk z ∈ from_rel sym ↔ r (prod.fst z) (prod.snd z) :=
  iff.rfl

@[simp] theorem from_rel_prop {α : Type u} {r : α → α → Prop} {sym : symmetric r} {a : α} {b : α} :
    quotient.mk (a, b) ∈ from_rel sym ↔ r a b :=
  sorry

theorem from_rel_irreflexive {α : Type u} {r : α → α → Prop} {sym : symmetric r} :
    irreflexive r ↔ ∀ {z : sym2 α}, z ∈ from_rel sym → ¬is_diag z :=
  sorry

theorem mem_from_rel_irrefl_other_ne {α : Type u} {r : α → α → Prop} {sym : symmetric r}
    (irrefl : irreflexive r) {a : α} {z : sym2 α} (hz : z ∈ from_rel sym) (h : a ∈ z) :
    mem.other h ≠ a :=
  mem_other_ne (iff.mp from_rel_irreflexive irrefl z hz) h

protected instance from_rel.decidable_pred {α : Type u} {r : α → α → Prop} (sym : symmetric r)
    [h : DecidableRel r] : decidable_pred (from_rel sym) :=
  fun (z : sym2 α) => quotient.rec_on_subsingleton z fun (x : α × α) => h (prod.fst x) (prod.snd x)

/-! ### Equivalence to the second symmetric power -/

/--
The symmetric square is equivalent to length-2 vectors up to permutations.
-/
def sym2_equiv_sym' {α : Type u_1} : sym2 α ≃ sym.sym' α (bit0 1) :=
  equiv.mk
    (quotient.map (fun (x : α × α) => { val := [prod.fst x, prod.snd x], property := sorry }) sorry)
    (quotient.map from_vector sorry) sorry sorry

/--
The symmetric square is equivalent to the second symmetric power.
-/
def equiv_sym (α : Type u_1) : sym2 α ≃ sym α (bit0 1) :=
  equiv.trans sym2_equiv_sym' (equiv.symm sym.sym_equiv_sym')

/--
The symmetric square is equivalent to multisets of cardinality
two. (This is currently a synonym for `equiv_sym`, but it's provided
in case the definition for `sym` changes.)
-/
def equiv_multiset (α : Type u_1) :
    sym2 α ≃ Subtype fun (s : multiset α) => coe_fn multiset.card s = bit0 1 :=
  equiv_sym α

/--
An algorithm for computing `sym2.rel`.
-/
def rel_bool {α : Type u} [DecidableEq α] (x : α × α) (y : α × α) : Bool :=
  ite (prod.fst x = prod.fst y) (to_bool (prod.snd x = prod.snd y))
    (ite (prod.fst x = prod.snd y) (to_bool (prod.snd x = prod.fst y)) false)

theorem rel_bool_spec {α : Type u} [DecidableEq α] (x : α × α) (y : α × α) :
    ↥(rel_bool x y) ↔ rel α x y :=
  sorry

/--
Given `[decidable_eq α]` and `[fintype α]`, the following instance gives `fintype (sym2 α)`.
-/
protected instance rel.decidable_rel (α : Type u_1) [DecidableEq α] : DecidableRel (rel α) :=
  fun (x y : α × α) => decidable_of_bool (rel_bool x y) sorry

/--
A function that gives the other element of a pair given one of the elements.  Used in `mem.other'`.
-/
/--
Get the other element of the unordered pair using the decidable equality.
This is the computable version of `mem.other`.
-/
def mem.other' {α : Type u} [DecidableEq α] {a : α} {z : sym2 α} (h : a ∈ z) : α :=
  quot.rec (fun (x : α × α) (h' : a ∈ Quot.mk setoid.r x) => pair_other a x) sorry z h

@[simp] theorem mem_other_spec' {α : Type u} [DecidableEq α] {a : α} {z : sym2 α} (h : a ∈ z) :
    quotient.mk (a, mem.other' h) = z :=
  sorry

@[simp] theorem other_eq_other' {α : Type u} [DecidableEq α] {a : α} {z : sym2 α} (h : a ∈ z) :
    mem.other h = mem.other' h :=
  eq.mpr (id (Eq._oldrec (Eq.refl (mem.other h = mem.other' h)) (Eq.symm (propext congr_right))))
    (eq.mpr
      (id
        (Eq._oldrec (Eq.refl (quotient.mk (a, mem.other h) = quotient.mk (a, mem.other' h)))
          (mem_other_spec' h)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (quotient.mk (a, mem.other h) = z)) (mem_other_spec h)))
        (Eq.refl z)))

theorem mem_other_mem' {α : Type u} [DecidableEq α] {a : α} {z : sym2 α} (h : a ∈ z) :
    mem.other' h ∈ z :=
  eq.mpr (id (Eq._oldrec (Eq.refl (mem.other' h ∈ z)) (Eq.symm (other_eq_other' h))))
    (mem_other_mem h)

theorem other_invol' {α : Type u} [DecidableEq α] {a : α} {z : sym2 α} (ha : a ∈ z)
    (hb : mem.other' ha ∈ z) : mem.other' hb = a :=
  sorry

theorem other_invol {α : Type u} {a : α} {z : sym2 α} (ha : a ∈ z) (hb : mem.other ha ∈ z) :
    mem.other hb = a :=
  sorry

end Mathlib