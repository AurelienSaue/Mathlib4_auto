/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

Operations on set-valued functions, aka partial multifunctions, aka relations.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.set.lattice
import Mathlib.PostPort

universes u_1 u_2 u_3 u_4 

namespace Mathlib

/-- A relation on `α` and `β`, aka a set-valued function, aka a partial multifunction --/
def rel (α : Type u_1) (β : Type u_2) := α → β → Prop

namespace rel


/-- The inverse relation : `r.inv x y ↔ r y x`. Note that this is *not* a groupoid inverse. -/
def inv {α : Type u_1} {β : Type u_2} (r : rel α β) : rel β α := flip r

theorem inv_def {α : Type u_1} {β : Type u_2} (r : rel α β) (x : α) (y : β) : inv r y x ↔ r x y :=
  iff.rfl

theorem inv_inv {α : Type u_1} {β : Type u_2} (r : rel α β) : inv (inv r) = r :=
  funext fun (x : α) => funext fun (y : β) => propext (iff.refl (inv (inv r) x y))

/-- Domain of a relation -/
def dom {α : Type u_1} {β : Type u_2} (r : rel α β) : set α :=
  set_of fun (x : α) => ∃ (y : β), r x y

/-- Codomain aka range of a relation-/
def codom {α : Type u_1} {β : Type u_2} (r : rel α β) : set β :=
  set_of fun (y : β) => ∃ (x : α), r x y

theorem codom_inv {α : Type u_1} {β : Type u_2} (r : rel α β) : codom (inv r) = dom r :=
  set.ext fun (x : α) => iff.refl (x ∈ codom (inv r))

theorem dom_inv {α : Type u_1} {β : Type u_2} (r : rel α β) : dom (inv r) = codom r :=
  set.ext fun (x : β) => iff.refl (x ∈ dom (inv r))

/-- Composition of relation; note that it follows the `category_theory/` order of arguments. -/
def comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} (r : rel α β) (s : rel β γ) : rel α γ :=
  fun (x : α) (z : γ) => ∃ (y : β), r x y ∧ s y z

theorem comp_assoc {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} (r : rel α β)
    (s : rel β γ) (t : rel γ δ) : comp (comp r s) t = comp r (comp s t) :=
  sorry

@[simp] theorem comp_right_id {α : Type u_1} {β : Type u_2} (r : rel α β) : comp r Eq = r := sorry

@[simp] theorem comp_left_id {α : Type u_1} {β : Type u_2} (r : rel α β) : comp Eq r = r := sorry

theorem inv_id {α : Type u_1} : inv Eq = Eq :=
  funext fun (x : α) => funext fun (y : α) => propext { mp := Eq.symm, mpr := Eq.symm }

theorem inv_comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} (r : rel α β) (s : rel β γ) :
    inv (comp r s) = comp (inv s) (inv r) :=
  sorry

/-- Image of a set under a relation -/
def image {α : Type u_1} {β : Type u_2} (r : rel α β) (s : set α) : set β :=
  set_of fun (y : β) => ∃ (x : α), ∃ (H : x ∈ s), r x y

theorem mem_image {α : Type u_1} {β : Type u_2} (r : rel α β) (y : β) (s : set α) :
    y ∈ image r s ↔ ∃ (x : α), ∃ (H : x ∈ s), r x y :=
  iff.rfl

theorem image_subset {α : Type u_1} {β : Type u_2} (r : rel α β) :
    relator.lift_fun has_subset.subset has_subset.subset (image r) (image r) :=
  sorry

theorem image_mono {α : Type u_1} {β : Type u_2} (r : rel α β) : monotone (image r) :=
  image_subset r

theorem image_inter {α : Type u_1} {β : Type u_2} (r : rel α β) (s : set α) (t : set α) :
    image r (s ∩ t) ⊆ image r s ∩ image r t :=
  monotone.map_inf_le (image_mono r) s t

theorem image_union {α : Type u_1} {β : Type u_2} (r : rel α β) (s : set α) (t : set α) :
    image r (s ∪ t) = image r s ∪ image r t :=
  sorry

@[simp] theorem image_id {α : Type u_1} (s : set α) : image Eq s = s := sorry

theorem image_comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} (r : rel α β) (s : rel β γ)
    (t : set α) : image (comp r s) t = image s (image r t) :=
  sorry

theorem image_univ {α : Type u_1} {β : Type u_2} (r : rel α β) : image r set.univ = codom r := sorry

/-- Preimage of a set under a relation `r`. Same as the image of `s` under `r.inv` -/
def preimage {α : Type u_1} {β : Type u_2} (r : rel α β) (s : set β) : set α := image (inv r) s

theorem mem_preimage {α : Type u_1} {β : Type u_2} (r : rel α β) (x : α) (s : set β) :
    x ∈ preimage r s ↔ ∃ (y : β), ∃ (H : y ∈ s), r x y :=
  iff.rfl

theorem preimage_def {α : Type u_1} {β : Type u_2} (r : rel α β) (s : set β) :
    preimage r s = set_of fun (x : α) => ∃ (y : β), ∃ (H : y ∈ s), r x y :=
  set.ext fun (x : α) => mem_preimage r x s

theorem preimage_mono {α : Type u_1} {β : Type u_2} (r : rel α β) {s : set β} {t : set β}
    (h : s ⊆ t) : preimage r s ⊆ preimage r t :=
  image_mono (inv r) h

theorem preimage_inter {α : Type u_1} {β : Type u_2} (r : rel α β) (s : set β) (t : set β) :
    preimage r (s ∩ t) ⊆ preimage r s ∩ preimage r t :=
  image_inter (inv r) s t

theorem preimage_union {α : Type u_1} {β : Type u_2} (r : rel α β) (s : set β) (t : set β) :
    preimage r (s ∪ t) = preimage r s ∪ preimage r t :=
  image_union (inv r) s t

theorem preimage_id {α : Type u_1} (s : set α) : preimage Eq s = s := sorry

theorem preimage_comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} (r : rel α β) (s : rel β γ)
    (t : set γ) : preimage (comp r s) t = preimage r (preimage s t) :=
  sorry

theorem preimage_univ {α : Type u_1} {β : Type u_2} (r : rel α β) : preimage r set.univ = dom r :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (preimage r set.univ = dom r)) (preimage.equations._eqn_1 r set.univ)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (image (inv r) set.univ = dom r)) (image_univ (inv r))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (codom (inv r) = dom r)) (codom_inv r))) (Eq.refl (dom r))))

/-- Core of a set `s : set β` w.r.t `r : rel α β` is the set of `x : α` that are related *only*
to elements of `s`. -/
def core {α : Type u_1} {β : Type u_2} (r : rel α β) (s : set β) : set α :=
  set_of fun (x : α) => ∀ (y : β), r x y → y ∈ s

theorem mem_core {α : Type u_1} {β : Type u_2} (r : rel α β) (x : α) (s : set β) :
    x ∈ core r s ↔ ∀ (y : β), r x y → y ∈ s :=
  iff.rfl

theorem core_subset {α : Type u_1} {β : Type u_2} (r : rel α β) :
    relator.lift_fun has_subset.subset has_subset.subset (core r) (core r) :=
  fun (s t : set β) (h : s ⊆ t) (x : α) (h' : x ∈ core r s) (y : β) (rxy : r x y) => h (h' y rxy)

theorem core_mono {α : Type u_1} {β : Type u_2} (r : rel α β) : monotone (core r) := core_subset r

theorem core_inter {α : Type u_1} {β : Type u_2} (r : rel α β) (s : set β) (t : set β) :
    core r (s ∩ t) = core r s ∩ core r t :=
  sorry

theorem core_union {α : Type u_1} {β : Type u_2} (r : rel α β) (s : set β) (t : set β) :
    core r s ∪ core r t ⊆ core r (s ∪ t) :=
  monotone.le_map_sup (core_mono r) s t

@[simp] theorem core_univ {α : Type u_1} {β : Type u_2} (r : rel α β) :
    core r set.univ = set.univ :=
  sorry

theorem core_id {α : Type u_1} (s : set α) : core Eq s = s := sorry

theorem core_comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} (r : rel α β) (s : rel β γ)
    (t : set γ) : core (comp r s) t = core r (core s t) :=
  sorry

/-- Restrict the domain of a relation to a subtype. -/
def restrict_domain {α : Type u_1} {β : Type u_2} (r : rel α β) (s : set α) :
    rel (Subtype fun (x : α) => x ∈ s) β :=
  fun (x : Subtype fun (x : α) => x ∈ s) (y : β) => r (subtype.val x) y

theorem image_subset_iff {α : Type u_1} {β : Type u_2} (r : rel α β) (s : set α) (t : set β) :
    image r s ⊆ t ↔ s ⊆ core r t :=
  sorry

theorem core_preimage_gc {α : Type u_1} {β : Type u_2} (r : rel α β) :
    galois_connection (image r) (core r) :=
  image_subset_iff r

end rel


namespace function


/-- The graph of a function as a relation. -/
def graph {α : Type u_1} {β : Type u_2} (f : α → β) : rel α β := fun (x : α) (y : β) => f x = y

end function


namespace set


-- TODO: if image were defined with bounded quantification in corelib, the next two would

-- be definitional

theorem image_eq {α : Type u_1} {β : Type u_2} (f : α → β) (s : set α) :
    f '' s = rel.image (function.graph f) s :=
  sorry

theorem preimage_eq {α : Type u_1} {β : Type u_2} (f : α → β) (s : set β) :
    f ⁻¹' s = rel.preimage (function.graph f) s :=
  sorry

theorem preimage_eq_core {α : Type u_1} {β : Type u_2} (f : α → β) (s : set β) :
    f ⁻¹' s = rel.core (function.graph f) s :=
  sorry

end Mathlib