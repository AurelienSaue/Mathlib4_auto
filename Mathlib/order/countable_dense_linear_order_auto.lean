/-
Copyright (c) 2020 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.order.ideal
import Mathlib.data.finset.default
import PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# The back and forth method and countable dense linear orders

## Results

Suppose `α β` are linear orders, with `α` countable and `β` dense, nonempty, without endpoints.
Then there is an order embedding `α ↪ β`. If in addition `α` is dense, nonempty, without
endpoints and `β` is countable, then we can upgrade this to an order isomorhpism `α ≃ β`.

The idea for both results is to consider "partial isomorphisms", which
identify a finite subset of `α` with a finite subset of `β`, and prove that
for any such partial isomorphism `f` and `a : α`, we can extend `f` to
include `a` in its domain.

## References

https://en.wikipedia.org/wiki/Back-and-forth_method

## Tags

back and forth, dense, countable, order

-/

namespace order


/-- Suppose `α` is a nonempty dense linear order without endpoints, and
    suppose `lo`, `hi`, are finite subssets with all of `lo` strictly
    before `hi`. Then there is an element of `α` strictly between `lo`
    and `hi`. -/
theorem exists_between_finsets {α : Type u_1} [linear_order α] [densely_ordered α] [no_bot_order α] [no_top_order α] [nonem : Nonempty α] (lo : finset α) (hi : finset α) (lo_lt_hi : ∀ (x : α), x ∈ lo → ∀ (y : α), y ∈ hi → x < y) : ∃ (m : α), (∀ (x : α), x ∈ lo → x < m) ∧ ∀ (y : α), y ∈ hi → m < y := sorry

/-- The type of partial order isomorphisms between `α` and `β` defined on finite subsets.
    A partial order isomorphism is encoded as a finite subset of `α × β`, consisting
    of pairs which should be identified. -/
def partial_iso (α : Type u_1) (β : Type u_2) [linear_order α] [linear_order β]  :=
  Subtype
    fun (f : finset (α × β)) =>
      ∀ (p q : α × β), p ∈ f → q ∈ f → cmp (prod.fst p) (prod.fst q) = cmp (prod.snd p) (prod.snd q)

namespace partial_iso


protected instance inhabited (α : Type u_1) (β : Type u_2) [linear_order α] [linear_order β] : Inhabited (partial_iso α β) :=
  { default := { val := ∅, property := sorry } }

protected instance preorder (α : Type u_1) (β : Type u_2) [linear_order α] [linear_order β] : preorder (partial_iso α β) :=
  subtype.preorder
    fun (f : finset (α × β)) =>
      ∀ (p q : α × β), p ∈ f → q ∈ f → cmp (prod.fst p) (prod.fst q) = cmp (prod.snd p) (prod.snd q)

/-- For each `a`, we can find a `b` in the codomain, such that `a`'s relation to
the domain of `f` is `b`'s relation to the image of `f`.

Thus, if `a` is not already in `f`, then we can extend `f` by sending `a` to `b`.
-/
theorem exists_across {α : Type u_1} {β : Type u_2} [linear_order α] [linear_order β] [densely_ordered β] [no_bot_order β] [no_top_order β] [Nonempty β] (f : partial_iso α β) (a : α) : ∃ (b : β), ∀ (p : α × β), p ∈ subtype.val f → cmp (prod.fst p) a = cmp (prod.snd p) b := sorry

/-- A partial isomorphism between `α` and `β` is also a partial isomorphism between `β` and `α`. -/
protected def comm {α : Type u_1} {β : Type u_2} [linear_order α] [linear_order β] : partial_iso α β → partial_iso β α :=
  subtype.map (finset.image ⇑(equiv.prod_comm α β)) sorry

/-- The set of partial isomorphisms defined at `a : α`, together with a proof that any
    partial isomorphism can be extended to one defined at `a`. -/
def defined_at_left {α : Type u_1} (β : Type u_2) [linear_order α] [linear_order β] [densely_ordered β] [no_bot_order β] [no_top_order β] [Nonempty β] (a : α) : cofinal (partial_iso α β) :=
  cofinal.mk (fun (f : partial_iso α β) => ∃ (b : β), (a, b) ∈ subtype.val f) sorry

/-- The set of partial isomorphisms defined at `b : β`, together with a proof that any
    partial isomorphism can be extended to include `b`. We prove this by symmetry. -/
def defined_at_right (α : Type u_1) {β : Type u_2} [linear_order α] [linear_order β] [densely_ordered α] [no_bot_order α] [no_top_order α] [Nonempty α] (b : β) : cofinal (partial_iso α β) :=
  cofinal.mk (fun (f : partial_iso α β) => ∃ (a : α), (a, b) ∈ subtype.val f) sorry

/-- Given an ideal which intersects `defined_at_left β a`, pick `b : β` such that
    some partial function in the ideal maps `a` to `b`. -/
def fun_of_ideal {α : Type u_1} {β : Type u_2} [linear_order α] [linear_order β] [densely_ordered β] [no_bot_order β] [no_top_order β] [Nonempty β] (a : α) (I : ideal (partial_iso α β)) : (∃ (f : partial_iso α β), f ∈ defined_at_left β a ∧ f ∈ I) →
  Subtype
    fun (b : β) =>
      ∃ (f :
        Subtype
          fun (f : finset (α × β)) =>
            ∀ (p q : α × β), p ∈ f → q ∈ f → cmp (prod.fst p) (prod.fst q) = cmp (prod.snd p) (prod.snd q)),
        ∃ (H : f ∈ I), (a, b) ∈ subtype.val f :=
  (classical.indefinite_description
      fun (x : β) =>
        ∃ (f :
          Subtype
            fun (f : finset (α × β)) =>
              ∀ (p q : α × β), p ∈ f → q ∈ f → cmp (prod.fst p) (prod.fst q) = cmp (prod.snd p) (prod.snd q)),
          ∃ (H : f ∈ I), (a, x) ∈ subtype.val f) ∘
    sorry

/-- Given an ideal which intersects `defined_at_right α b`, pick `a : α` such that
    some partial function in the ideal maps `a` to `b`. -/
def inv_of_ideal {α : Type u_1} {β : Type u_2} [linear_order α] [linear_order β] [densely_ordered α] [no_bot_order α] [no_top_order α] [Nonempty α] (b : β) (I : ideal (partial_iso α β)) : (∃ (f : partial_iso α β), f ∈ defined_at_right α b ∧ f ∈ I) →
  Subtype
    fun (a : α) =>
      ∃ (f :
        Subtype
          fun (f : finset (α × β)) =>
            ∀ (p q : α × β), p ∈ f → q ∈ f → cmp (prod.fst p) (prod.fst q) = cmp (prod.snd p) (prod.snd q)),
        ∃ (H : f ∈ I), (a, b) ∈ subtype.val f :=
  (classical.indefinite_description
      fun (x : α) =>
        ∃ (f :
          Subtype
            fun (f : finset (α × β)) =>
              ∀ (p q : α × β), p ∈ f → q ∈ f → cmp (prod.fst p) (prod.fst q) = cmp (prod.snd p) (prod.snd q)),
          ∃ (H : f ∈ I), (x, b) ∈ subtype.val f) ∘
    sorry

end partial_iso


/-- Any countable linear order embeds in any nonempty dense linear order without endpoints. -/
def embedding_from_countable_to_dense (α : Type u_1) (β : Type u_2) [linear_order α] [linear_order β] [encodable α] [densely_ordered β] [no_bot_order β] [no_top_order β] [Nonempty β] : α ↪o β :=
  let our_ideal : ideal (partial_iso α β) := ideal_of_cofinals Inhabited.default (partial_iso.defined_at_left β);
  let F :
    (a : α) →
      Subtype
        fun (b : β) =>
          ∃ (f :
            Subtype
              fun (f : finset (α × β)) =>
                ∀ (p q : α × β), p ∈ f → q ∈ f → cmp (prod.fst p) (prod.fst q) = cmp (prod.snd p) (prod.snd q)),
            ∃ (H : f ∈ our_ideal), (a, b) ∈ subtype.val f :=
    fun (a : α) => partial_iso.fun_of_ideal a our_ideal sorry;
  order_embedding.of_strict_mono (fun (a : α) => subtype.val (F a)) sorry

/-- Any two countable dense, nonempty linear orders without endpoints are order isomorphic. -/
def iso_of_countable_dense (α : Type u_1) (β : Type u_2) [linear_order α] [linear_order β] [encodable α] [densely_ordered α] [no_bot_order α] [no_top_order α] [Nonempty α] [encodable β] [densely_ordered β] [no_bot_order β] [no_top_order β] [Nonempty β] : α ≃o β := sorry

