/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.set.function
import Mathlib.logic.function.iterate
import Mathlib.PostPort

universes u v 

namespace Mathlib

/-!
# Fixed points of a self-map

In this file we define

* the predicate `is_fixed_pt f x := f x = x`;
* the set `fixed_points f` of fixed points of a self-map `f`.

We also prove some simple lemmas about `is_fixed_pt` and `∘`, `iterate`, and `semiconj`.

## Tags

fixed point
-/

namespace function


/-- A point `x` is a fixed point of `f : α → α` if `f x = x`. -/
def is_fixed_pt {α : Type u} (f : α → α) (x : α) := f x = x

/-- Every point is a fixed point of `id`. -/
theorem is_fixed_pt_id {α : Type u} (x : α) : is_fixed_pt id x := rfl

namespace is_fixed_pt


protected instance decidable {α : Type u} [h : DecidableEq α] {f : α → α} {x : α} :
    Decidable (is_fixed_pt f x) :=
  h (f x) x

/-- If `x` is a fixed point of `f`, then `f x = x`. This is useful, e.g., for `rw` or `simp`.-/
protected theorem eq {α : Type u} {f : α → α} {x : α} (hf : is_fixed_pt f x) : f x = x := hf

/-- If `x` is a fixed point of `f` and `g`, then it is a fixed point of `f ∘ g`. -/
protected theorem comp {α : Type u} {f : α → α} {g : α → α} {x : α} (hf : is_fixed_pt f x)
    (hg : is_fixed_pt g x) : is_fixed_pt (f ∘ g) x :=
  Eq.trans (congr_arg f hg) hf

/-- If `x` is a fixed point of `f`, then it is a fixed point of `f^[n]`. -/
protected theorem iterate {α : Type u} {f : α → α} {x : α} (hf : is_fixed_pt f x) (n : ℕ) :
    is_fixed_pt (nat.iterate f n) x :=
  iterate_fixed hf n

/-- If `x` is a fixed point of `f ∘ g` and `g`, then it is a fixed point of `f`. -/
theorem left_of_comp {α : Type u} {f : α → α} {g : α → α} {x : α} (hfg : is_fixed_pt (f ∘ g) x)
    (hg : is_fixed_pt g x) : is_fixed_pt f x :=
  Eq.trans (congr_arg f (Eq.symm hg)) hfg

/-- If `x` is a fixed point of `f` and `g` is a left inverse of `f`, then `x` is a fixed
point of `g`. -/
theorem to_left_inverse {α : Type u} {f : α → α} {g : α → α} {x : α} (hf : is_fixed_pt f x)
    (h : left_inverse g f) : is_fixed_pt g x :=
  Eq.trans (congr_arg g (Eq.symm hf)) (h x)

/-- If `g` (semi)conjugates `fa` to `fb`, then it sends fixed points of `fa` to fixed points
of `fb`. -/
protected theorem map {α : Type u} {β : Type v} {fa : α → α} {fb : β → β} {x : α}
    (hx : is_fixed_pt fa x) {g : α → β} (h : semiconj g fa fb) : is_fixed_pt fb (g x) :=
  Eq.trans (Eq.symm (semiconj.eq h x)) (congr_arg g hx)

end is_fixed_pt


/-- The set of fixed points of a map `f : α → α`. -/
def fixed_points {α : Type u} (f : α → α) : set α := set_of fun (x : α) => is_fixed_pt f x

protected instance fixed_points.decidable {α : Type u} [DecidableEq α] (f : α → α) (x : α) :
    Decidable (x ∈ fixed_points f) :=
  is_fixed_pt.decidable

@[simp] theorem mem_fixed_points {α : Type u} {f : α → α} {x : α} :
    x ∈ fixed_points f ↔ is_fixed_pt f x :=
  iff.rfl

/-- If `g` semiconjugates `fa` to `fb`, then it sends fixed points of `fa` to fixed points
of `fb`. -/
theorem semiconj.maps_to_fixed_pts {α : Type u} {β : Type v} {fa : α → α} {fb : β → β} {g : α → β}
    (h : semiconj g fa fb) : set.maps_to g (fixed_points fa) (fixed_points fb) :=
  fun (x : α) (hx : x ∈ fixed_points fa) => is_fixed_pt.map hx h

/-- Any two maps `f : α → β` and `g : β → α` are inverse of each other on the sets of fixed points
of `f ∘ g` and `g ∘ f`, respectively. -/
theorem inv_on_fixed_pts_comp {α : Type u} {β : Type v} (f : α → β) (g : β → α) :
    set.inv_on f g (fixed_points (f ∘ g)) (fixed_points (g ∘ f)) :=
  { left := fun (x : β) => id, right := fun (x : α) => id }

/-- Any map `f` sends fixed points of `g ∘ f` to fixed points of `f ∘ g`. -/
theorem maps_to_fixed_pts_comp {α : Type u} {β : Type v} (f : α → β) (g : β → α) :
    set.maps_to f (fixed_points (g ∘ f)) (fixed_points (f ∘ g)) :=
  fun (x : α) (hx : x ∈ fixed_points (g ∘ f)) => is_fixed_pt.map hx fun (x : α) => rfl

/-- Given two maps `f : α → β` and `g : β → α`, `g` is a bijective map between the fixed points
of `f ∘ g` and the fixed points of `g ∘ f`. The inverse map is `f`, see `inv_on_fixed_pts_comp`. -/
theorem bij_on_fixed_pts_comp {α : Type u} {β : Type v} (f : α → β) (g : β → α) :
    set.bij_on g (fixed_points (f ∘ g)) (fixed_points (g ∘ f)) :=
  set.inv_on.bij_on (inv_on_fixed_pts_comp f g) (maps_to_fixed_pts_comp g f)
    (maps_to_fixed_pts_comp f g)

/-- If self-maps `f` and `g` commute, then they are inverse of each other on the set of fixed points
of `f ∘ g`. This is a particular case of `function.inv_on_fixed_pts_comp`. -/
theorem commute.inv_on_fixed_pts_comp {α : Type u} {f : α → α} {g : α → α} (h : commute f g) :
    set.inv_on f g (fixed_points (f ∘ g)) (fixed_points (f ∘ g)) :=
  sorry

/-- If self-maps `f` and `g` commute, then `f` is bijective on the set of fixed points of `f ∘ g`.
This is a particular case of `function.bij_on_fixed_pts_comp`. -/
theorem commute.left_bij_on_fixed_pts_comp {α : Type u} {f : α → α} {g : α → α} (h : commute f g) :
    set.bij_on f (fixed_points (f ∘ g)) (fixed_points (f ∘ g)) :=
  sorry

/-- If self-maps `f` and `g` commute, then `g` is bijective on the set of fixed points of `f ∘ g`.
This is a particular case of `function.bij_on_fixed_pts_comp`. -/
theorem commute.right_bij_on_fixed_pts_comp {α : Type u} {f : α → α} {g : α → α} (h : commute f g) :
    set.bij_on g (fixed_points (f ∘ g)) (fixed_points (f ∘ g)) :=
  sorry

end Mathlib