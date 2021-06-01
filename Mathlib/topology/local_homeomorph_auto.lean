/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.equiv.local_equiv
import Mathlib.topology.opens
import Mathlib.PostPort

universes u_5 u_6 l u_1 u_2 u_3 u_4 

namespace Mathlib

/-!
# Local homeomorphisms

This file defines homeomorphisms between open subsets of topological spaces. An element `e` of
`local_homeomorph α β` is an extension of `local_equiv α β`, i.e., it is a pair of functions
`e.to_fun` and `e.inv_fun`, inverse of each other on the sets `e.source` and `e.target`.
Additionally, we require that these sets are open, and that the functions are continuous on them.
Equivalently, they are homeomorphisms there.

As in equivs, we register a coercion to functions, and we use `e x` and `e.symm x` throughout
instead of `e.to_fun x` and `e.inv_fun x`.

## Main definitions

`homeomorph.to_local_homeomorph`: associating a local homeomorphism to a homeomorphism, with
                                  source = target = univ
`local_homeomorph.symm`  : the inverse of a local homeomorphism
`local_homeomorph.trans` : the composition of two local homeomorphisms
`local_homeomorph.refl`  : the identity local homeomorphism
`local_homeomorph.of_set`: the identity on a set `s`
`eq_on_source`           : equivalence relation describing the "right" notion of equality for local
                           homeomorphisms

## Implementation notes

Most statements are copied from their local_equiv versions, although some care is required
especially when restricting to subsets, as these should be open subsets.

For design notes, see `local_equiv.lean`.
-/

/-- local homeomorphisms, defined on open subsets of the space -/
structure local_homeomorph (α : Type u_5) (β : Type u_6) [topological_space α] [topological_space β]
    extends local_equiv α β where
  open_source : is_open (local_equiv.source _to_local_equiv)
  open_target : is_open (local_equiv.target _to_local_equiv)
  continuous_to_fun :
    continuous_on (local_equiv.to_fun _to_local_equiv) (local_equiv.source _to_local_equiv)
  continuous_inv_fun :
    continuous_on (local_equiv.inv_fun _to_local_equiv) (local_equiv.target _to_local_equiv)

/-- A homeomorphism induces a local homeomorphism on the whole space -/
def homeomorph.to_local_homeomorph {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] (e : α ≃ₜ β) : local_homeomorph α β :=
  local_homeomorph.mk
    (local_equiv.mk (local_equiv.to_fun (equiv.to_local_equiv (homeomorph.to_equiv e)))
      (local_equiv.inv_fun (equiv.to_local_equiv (homeomorph.to_equiv e)))
      (local_equiv.source (equiv.to_local_equiv (homeomorph.to_equiv e)))
      (local_equiv.target (equiv.to_local_equiv (homeomorph.to_equiv e))) sorry sorry sorry sorry)
    is_open_univ is_open_univ sorry sorry

namespace local_homeomorph


protected instance has_coe_to_fun {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] : has_coe_to_fun (local_homeomorph α β) :=
  has_coe_to_fun.mk (fun (e : local_homeomorph α β) => α → β)
    fun (e : local_homeomorph α β) => local_equiv.to_fun (to_local_equiv e)

/-- The inverse of a local homeomorphism -/
protected def symm {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (e : local_homeomorph α β) : local_homeomorph β α :=
  mk
    (local_equiv.mk (local_equiv.to_fun (local_equiv.symm (to_local_equiv e)))
      (local_equiv.inv_fun (local_equiv.symm (to_local_equiv e)))
      (local_equiv.source (local_equiv.symm (to_local_equiv e)))
      (local_equiv.target (local_equiv.symm (to_local_equiv e))) sorry sorry sorry sorry)
    (open_target e) (open_source e) (continuous_inv_fun e) (continuous_to_fun e)

protected theorem continuous_on {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] (e : local_homeomorph α β) :
    continuous_on (⇑e) (local_equiv.source (to_local_equiv e)) :=
  continuous_to_fun e

theorem continuous_on_symm {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (e : local_homeomorph α β) :
    continuous_on (⇑(local_homeomorph.symm e)) (local_equiv.target (to_local_equiv e)) :=
  continuous_inv_fun e

@[simp] theorem mk_coe {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (e : local_equiv α β) (a : is_open (local_equiv.source e)) (b : is_open (local_equiv.target e))
    (c : continuous_on (local_equiv.to_fun e) (local_equiv.source e))
    (d : continuous_on (local_equiv.inv_fun e) (local_equiv.target e)) : ⇑(mk e a b c d) = ⇑e :=
  rfl

@[simp] theorem mk_coe_symm {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] (e : local_equiv α β) (a : is_open (local_equiv.source e))
    (b : is_open (local_equiv.target e))
    (c : continuous_on (local_equiv.to_fun e) (local_equiv.source e))
    (d : continuous_on (local_equiv.inv_fun e) (local_equiv.target e)) :
    ⇑(local_homeomorph.symm (mk e a b c d)) = ⇑(local_equiv.symm e) :=
  rfl

/- Register a few simp lemmas to make sure that `simp` puts the application of a local
homeomorphism in its normal form, i.e., in terms of its coercion to a function. -/

@[simp] theorem to_fun_eq_coe {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] (e : local_homeomorph α β) : local_equiv.to_fun (to_local_equiv e) = ⇑e :=
  rfl

@[simp] theorem inv_fun_eq_coe {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] (e : local_homeomorph α β) :
    local_equiv.inv_fun (to_local_equiv e) = ⇑(local_homeomorph.symm e) :=
  rfl

@[simp] theorem coe_coe {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (e : local_homeomorph α β) : ⇑(to_local_equiv e) = ⇑e :=
  rfl

@[simp] theorem coe_coe_symm {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] (e : local_homeomorph α β) :
    ⇑(local_equiv.symm (to_local_equiv e)) = ⇑(local_homeomorph.symm e) :=
  rfl

@[simp] theorem map_source {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (e : local_homeomorph α β) {x : α} (h : x ∈ local_equiv.source (to_local_equiv e)) :
    coe_fn e x ∈ local_equiv.target (to_local_equiv e) :=
  local_equiv.map_source' (to_local_equiv e) h

@[simp] theorem map_target {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (e : local_homeomorph α β) {x : β} (h : x ∈ local_equiv.target (to_local_equiv e)) :
    coe_fn (local_homeomorph.symm e) x ∈ local_equiv.source (to_local_equiv e) :=
  local_equiv.map_target' (to_local_equiv e) h

@[simp] theorem left_inv {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (e : local_homeomorph α β) {x : α} (h : x ∈ local_equiv.source (to_local_equiv e)) :
    coe_fn (local_homeomorph.symm e) (coe_fn e x) = x :=
  local_equiv.left_inv' (to_local_equiv e) h

@[simp] theorem right_inv {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (e : local_homeomorph α β) {x : β} (h : x ∈ local_equiv.target (to_local_equiv e)) :
    coe_fn e (coe_fn (local_homeomorph.symm e) x) = x :=
  local_equiv.right_inv' (to_local_equiv e) h

theorem source_preimage_target {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] (e : local_homeomorph α β) :
    local_equiv.source (to_local_equiv e) ⊆ ⇑e ⁻¹' local_equiv.target (to_local_equiv e) :=
  fun (_x : α) (h : _x ∈ local_equiv.source (to_local_equiv e)) => map_source e h

theorem eq_of_local_equiv_eq {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] {e : local_homeomorph α β} {e' : local_homeomorph α β}
    (h : to_local_equiv e = to_local_equiv e') : e = e' :=
  sorry

theorem eventually_left_inverse {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] (e : local_homeomorph α β) {x : α}
    (hx : x ∈ local_equiv.source (to_local_equiv e)) :
    filter.eventually (fun (y : α) => coe_fn (local_homeomorph.symm e) (coe_fn e y) = y) (nhds x) :=
  filter.eventually.mono (is_open.eventually_mem (open_source e) hx)
    (local_equiv.left_inv' (to_local_equiv e))

theorem eventually_left_inverse' {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] (e : local_homeomorph α β) {x : β}
    (hx : x ∈ local_equiv.target (to_local_equiv e)) :
    filter.eventually (fun (y : α) => coe_fn (local_homeomorph.symm e) (coe_fn e y) = y)
        (nhds (coe_fn (local_homeomorph.symm e) x)) :=
  eventually_left_inverse e (map_target e hx)

theorem eventually_right_inverse {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] (e : local_homeomorph α β) {x : β}
    (hx : x ∈ local_equiv.target (to_local_equiv e)) :
    filter.eventually (fun (y : β) => coe_fn e (coe_fn (local_homeomorph.symm e) y) = y) (nhds x) :=
  filter.eventually.mono (is_open.eventually_mem (open_target e) hx)
    (local_equiv.right_inv' (to_local_equiv e))

theorem eventually_right_inverse' {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] (e : local_homeomorph α β) {x : α}
    (hx : x ∈ local_equiv.source (to_local_equiv e)) :
    filter.eventually (fun (y : β) => coe_fn e (coe_fn (local_homeomorph.symm e) y) = y)
        (nhds (coe_fn e x)) :=
  eventually_right_inverse e (map_source e hx)

theorem eventually_ne_nhds_within {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] (e : local_homeomorph α β) {x : α}
    (hx : x ∈ local_equiv.source (to_local_equiv e)) :
    filter.eventually (fun (x' : α) => coe_fn e x' ≠ coe_fn e x) (nhds_within x (singleton xᶜ)) :=
  sorry

theorem image_eq_target_inter_inv_preimage {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] (e : local_homeomorph α β) {s : set α}
    (h : s ⊆ local_equiv.source (to_local_equiv e)) :
    ⇑e '' s = local_equiv.target (to_local_equiv e) ∩ ⇑(local_homeomorph.symm e) ⁻¹' s :=
  local_equiv.image_eq_target_inter_inv_preimage (to_local_equiv e) h

theorem image_inter_source_eq {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] (e : local_homeomorph α β) (s : set α) :
    ⇑e '' (s ∩ local_equiv.source (to_local_equiv e)) =
        local_equiv.target (to_local_equiv e) ∩
          ⇑(local_homeomorph.symm e) ⁻¹' (s ∩ local_equiv.source (to_local_equiv e)) :=
  image_eq_target_inter_inv_preimage e
    (set.inter_subset_right s (local_equiv.source (to_local_equiv e)))

theorem symm_image_eq_source_inter_preimage {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] (e : local_homeomorph α β) {s : set β}
    (h : s ⊆ local_equiv.target (to_local_equiv e)) :
    ⇑(local_homeomorph.symm e) '' s = local_equiv.source (to_local_equiv e) ∩ ⇑e ⁻¹' s :=
  image_eq_target_inter_inv_preimage (local_homeomorph.symm e) h

theorem symm_image_inter_target_eq {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] (e : local_homeomorph α β) (s : set β) :
    ⇑(local_homeomorph.symm e) '' (s ∩ local_equiv.target (to_local_equiv e)) =
        local_equiv.source (to_local_equiv e) ∩
          ⇑e ⁻¹' (s ∩ local_equiv.target (to_local_equiv e)) :=
  image_inter_source_eq (local_homeomorph.symm e) s

/-- Two local homeomorphisms are equal when they have equal `to_fun`, `inv_fun` and `source`.
It is not sufficient to have equal `to_fun` and `source`, as this only determines `inv_fun` on
the target. This would only be true for a weaker notion of equality, arguably the right one,
called `eq_on_source`. -/
protected theorem ext {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (e : local_homeomorph α β) (e' : local_homeomorph α β) (h : ∀ (x : α), coe_fn e x = coe_fn e' x)
    (hinv : ∀ (x : β), coe_fn (local_homeomorph.symm e) x = coe_fn (local_homeomorph.symm e') x)
    (hs : local_equiv.source (to_local_equiv e) = local_equiv.source (to_local_equiv e')) :
    e = e' :=
  eq_of_local_equiv_eq (local_equiv.ext h hinv hs)

-- The following lemmas are already simp via local_equiv

@[simp] theorem symm_to_local_equiv {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] (e : local_homeomorph α β) :
    to_local_equiv (local_homeomorph.symm e) = local_equiv.symm (to_local_equiv e) :=
  rfl

theorem symm_source {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (e : local_homeomorph α β) :
    local_equiv.source (to_local_equiv (local_homeomorph.symm e)) =
        local_equiv.target (to_local_equiv e) :=
  rfl

theorem symm_target {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (e : local_homeomorph α β) :
    local_equiv.target (to_local_equiv (local_homeomorph.symm e)) =
        local_equiv.source (to_local_equiv e) :=
  rfl

@[simp] theorem symm_symm {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (e : local_homeomorph α β) : local_homeomorph.symm (local_homeomorph.symm e) = e :=
  sorry

/-- A local homeomorphism is continuous at any point of its source -/
protected theorem continuous_at {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] (e : local_homeomorph α β) {x : α}
    (h : x ∈ local_equiv.source (to_local_equiv e)) : continuous_at (⇑e) x :=
  continuous_within_at.continuous_at (local_homeomorph.continuous_on e x h)
    (mem_nhds_sets (open_source e) h)

/-- A local homeomorphism inverse is continuous at any point of its target -/
theorem continuous_at_symm {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (e : local_homeomorph α β) {x : β} (h : x ∈ local_equiv.target (to_local_equiv e)) :
    continuous_at (⇑(local_homeomorph.symm e)) x :=
  local_homeomorph.continuous_at (local_homeomorph.symm e) h

theorem tendsto_symm {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (e : local_homeomorph α β) {x : α} (hx : x ∈ local_equiv.source (to_local_equiv e)) :
    filter.tendsto (⇑(local_homeomorph.symm e)) (nhds (coe_fn e x)) (nhds x) :=
  sorry

theorem map_nhds_eq {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (e : local_homeomorph α β) {x : α} (hx : x ∈ local_equiv.source (to_local_equiv e)) :
    filter.map (⇑e) (nhds x) = nhds (coe_fn e x) :=
  le_antisymm (local_homeomorph.continuous_at e hx)
    (filter.le_map_of_right_inverse (eventually_right_inverse' e hx) (tendsto_symm e hx))

/-- Preimage of interior or interior of preimage coincide for local homeomorphisms, when restricted
to the source. -/
theorem preimage_interior {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (e : local_homeomorph α β) (s : set β) :
    local_equiv.source (to_local_equiv e) ∩ ⇑e ⁻¹' interior s =
        local_equiv.source (to_local_equiv e) ∩ interior (⇑e ⁻¹' s) :=
  sorry

theorem preimage_open_of_open {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] (e : local_homeomorph α β) {s : set β} (hs : is_open s) :
    is_open (local_equiv.source (to_local_equiv e) ∩ ⇑e ⁻¹' s) :=
  continuous_on.preimage_open_of_open (local_homeomorph.continuous_on e) (open_source e) hs

theorem preimage_open_of_open_symm {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] (e : local_homeomorph α β) {s : set α} (hs : is_open s) :
    is_open (local_equiv.target (to_local_equiv e) ∩ ⇑(local_homeomorph.symm e) ⁻¹' s) :=
  continuous_on.preimage_open_of_open (local_homeomorph.continuous_on (local_homeomorph.symm e))
    (open_target e) hs

/-- The image of an open set in the source is open. -/
theorem image_open_of_open {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (e : local_homeomorph α β) {s : set α} (hs : is_open s)
    (h : s ⊆ local_equiv.source (to_local_equiv e)) : is_open (⇑e '' s) :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (is_open (⇑e '' s)))
        (local_equiv.image_eq_target_inter_inv_preimage (to_local_equiv e) h)))
    (continuous_on.preimage_open_of_open (continuous_on_symm e) (open_target e) hs)

/-- The image of the restriction of an open set to the source is open. -/
theorem image_open_of_open' {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] (e : local_homeomorph α β) {s : set α} (hs : is_open s) :
    is_open (⇑e '' (s ∩ local_equiv.source (to_local_equiv e))) :=
  sorry

/-- Restricting a local homeomorphism `e` to `e.source ∩ s` when `s` is open. This is sometimes hard
to use because of the openness assumption, but it has the advantage that when it can
be used then its local_equiv is defeq to local_equiv.restr -/
protected def restr_open {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (e : local_homeomorph α β) (s : set α) (hs : is_open s) : local_homeomorph α β :=
  mk
    (local_equiv.mk (local_equiv.to_fun (local_equiv.restr (to_local_equiv e) s))
      (local_equiv.inv_fun (local_equiv.restr (to_local_equiv e) s))
      (local_equiv.source (local_equiv.restr (to_local_equiv e) s))
      (local_equiv.target (local_equiv.restr (to_local_equiv e) s)) sorry sorry sorry sorry)
    sorry sorry sorry sorry

@[simp] theorem restr_open_to_local_equiv {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] (e : local_homeomorph α β) (s : set α) (hs : is_open s) :
    to_local_equiv (local_homeomorph.restr_open e s hs) = local_equiv.restr (to_local_equiv e) s :=
  rfl

-- Already simp via local_equiv

theorem restr_open_source {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (e : local_homeomorph α β) (s : set α) (hs : is_open s) :
    local_equiv.source (to_local_equiv (local_homeomorph.restr_open e s hs)) =
        local_equiv.source (to_local_equiv e) ∩ s :=
  rfl

/-- Restricting a local homeomorphism `e` to `e.source ∩ interior s`. We use the interior to make
sure that the restriction is well defined whatever the set s, since local homeomorphisms are by
definition defined on open sets. In applications where `s` is open, this coincides with the
restriction of local equivalences -/
protected def restr {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (e : local_homeomorph α β) (s : set α) : local_homeomorph α β :=
  local_homeomorph.restr_open e (interior s) is_open_interior

@[simp] theorem restr_to_local_equiv {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] (e : local_homeomorph α β) (s : set α) :
    to_local_equiv (local_homeomorph.restr e s) =
        local_equiv.restr (to_local_equiv e) (interior s) :=
  rfl

@[simp] theorem restr_coe {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (e : local_homeomorph α β) (s : set α) : ⇑(local_homeomorph.restr e s) = ⇑e :=
  rfl

@[simp] theorem restr_coe_symm {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] (e : local_homeomorph α β) (s : set α) :
    ⇑(local_homeomorph.symm (local_homeomorph.restr e s)) = ⇑(local_homeomorph.symm e) :=
  rfl

theorem restr_source {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (e : local_homeomorph α β) (s : set α) :
    local_equiv.source (to_local_equiv (local_homeomorph.restr e s)) =
        local_equiv.source (to_local_equiv e) ∩ interior s :=
  rfl

theorem restr_target {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (e : local_homeomorph α β) (s : set α) :
    local_equiv.target (to_local_equiv (local_homeomorph.restr e s)) =
        local_equiv.target (to_local_equiv e) ∩ ⇑(local_homeomorph.symm e) ⁻¹' interior s :=
  rfl

theorem restr_source' {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (e : local_homeomorph α β) (s : set α) (hs : is_open s) :
    local_equiv.source (to_local_equiv (local_homeomorph.restr e s)) =
        local_equiv.source (to_local_equiv e) ∩ s :=
  sorry

theorem restr_to_local_equiv' {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] (e : local_homeomorph α β) (s : set α) (hs : is_open s) :
    to_local_equiv (local_homeomorph.restr e s) = local_equiv.restr (to_local_equiv e) s :=
  sorry

theorem restr_eq_of_source_subset {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] {e : local_homeomorph α β} {s : set α}
    (h : local_equiv.source (to_local_equiv e) ⊆ s) : local_homeomorph.restr e s = e :=
  sorry

@[simp] theorem restr_univ {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    {e : local_homeomorph α β} : local_homeomorph.restr e set.univ = e :=
  restr_eq_of_source_subset (set.subset_univ (local_equiv.source (to_local_equiv e)))

theorem restr_source_inter {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (e : local_homeomorph α β) (s : set α) :
    local_homeomorph.restr e (local_equiv.source (to_local_equiv e) ∩ s) =
        local_homeomorph.restr e s :=
  sorry

/-- The identity on the whole space as a local homeomorphism. -/
protected def refl (α : Type u_1) [topological_space α] : local_homeomorph α α :=
  homeomorph.to_local_homeomorph (homeomorph.refl α)

@[simp] theorem refl_local_equiv {α : Type u_1} [topological_space α] :
    to_local_equiv (local_homeomorph.refl α) = local_equiv.refl α :=
  rfl

theorem refl_source {α : Type u_1} [topological_space α] :
    local_equiv.source (to_local_equiv (local_homeomorph.refl α)) = set.univ :=
  rfl

theorem refl_target {α : Type u_1} [topological_space α] :
    local_equiv.target (to_local_equiv (local_homeomorph.refl α)) = set.univ :=
  rfl

@[simp] theorem refl_symm {α : Type u_1} [topological_space α] :
    local_homeomorph.symm (local_homeomorph.refl α) = local_homeomorph.refl α :=
  rfl

@[simp] theorem refl_coe {α : Type u_1} [topological_space α] : ⇑(local_homeomorph.refl α) = id :=
  rfl

/-- The identity local equiv on a set `s` -/
def of_set {α : Type u_1} [topological_space α] (s : set α) (hs : is_open s) :
    local_homeomorph α α :=
  mk
    (local_equiv.mk (local_equiv.to_fun (local_equiv.of_set s))
      (local_equiv.inv_fun (local_equiv.of_set s)) (local_equiv.source (local_equiv.of_set s))
      (local_equiv.target (local_equiv.of_set s)) sorry sorry sorry sorry)
    hs hs sorry sorry

@[simp] theorem of_set_to_local_equiv {α : Type u_1} [topological_space α] {s : set α}
    (hs : is_open s) : to_local_equiv (of_set s hs) = local_equiv.of_set s :=
  rfl

theorem of_set_source {α : Type u_1} [topological_space α] {s : set α} (hs : is_open s) :
    local_equiv.source (to_local_equiv (of_set s hs)) = s :=
  rfl

theorem of_set_target {α : Type u_1} [topological_space α] {s : set α} (hs : is_open s) :
    local_equiv.target (to_local_equiv (of_set s hs)) = s :=
  rfl

@[simp] theorem of_set_coe {α : Type u_1} [topological_space α] {s : set α} (hs : is_open s) :
    ⇑(of_set s hs) = id :=
  rfl

@[simp] theorem of_set_symm {α : Type u_1} [topological_space α] {s : set α} (hs : is_open s) :
    local_homeomorph.symm (of_set s hs) = of_set s hs :=
  rfl

@[simp] theorem of_set_univ_eq_refl {α : Type u_1} [topological_space α] :
    of_set set.univ is_open_univ = local_homeomorph.refl α :=
  sorry

/-- Composition of two local homeomorphisms when the target of the first and the source of
the second coincide. -/
protected def trans' {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α]
    [topological_space β] [topological_space γ] (e : local_homeomorph α β)
    (e' : local_homeomorph β γ)
    (h : local_equiv.target (to_local_equiv e) = local_equiv.source (to_local_equiv e')) :
    local_homeomorph α γ :=
  mk
    (local_equiv.mk
      (local_equiv.to_fun (local_equiv.trans' (to_local_equiv e) (to_local_equiv e') h))
      (local_equiv.inv_fun (local_equiv.trans' (to_local_equiv e) (to_local_equiv e') h))
      (local_equiv.source (local_equiv.trans' (to_local_equiv e) (to_local_equiv e') h))
      (local_equiv.target (local_equiv.trans' (to_local_equiv e) (to_local_equiv e') h)) sorry sorry
      sorry sorry)
    (open_source e) (open_target e') sorry sorry

/-- Composing two local homeomorphisms, by restricting to the maximal domain where their
composition is well defined. -/
protected def trans {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α]
    [topological_space β] [topological_space γ] (e : local_homeomorph α β)
    (e' : local_homeomorph β γ) : local_homeomorph α γ :=
  local_homeomorph.trans'
    (local_homeomorph.symm
      (local_homeomorph.restr_open (local_homeomorph.symm e)
        (local_equiv.source (to_local_equiv e')) (open_source e')))
    (local_homeomorph.restr_open e' (local_equiv.target (to_local_equiv e)) (open_target e)) sorry

@[simp] theorem trans_to_local_equiv {α : Type u_1} {β : Type u_2} {γ : Type u_3}
    [topological_space α] [topological_space β] [topological_space γ] (e : local_homeomorph α β)
    (e' : local_homeomorph β γ) :
    to_local_equiv (local_homeomorph.trans e e') =
        local_equiv.trans (to_local_equiv e) (to_local_equiv e') :=
  rfl

@[simp] theorem coe_trans {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α]
    [topological_space β] [topological_space γ] (e : local_homeomorph α β)
    (e' : local_homeomorph β γ) : ⇑(local_homeomorph.trans e e') = ⇑e' ∘ ⇑e :=
  rfl

@[simp] theorem coe_trans_symm {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α]
    [topological_space β] [topological_space γ] (e : local_homeomorph α β)
    (e' : local_homeomorph β γ) :
    ⇑(local_homeomorph.symm (local_homeomorph.trans e e')) =
        ⇑(local_homeomorph.symm e) ∘ ⇑(local_homeomorph.symm e') :=
  rfl

theorem trans_symm_eq_symm_trans_symm {α : Type u_1} {β : Type u_2} {γ : Type u_3}
    [topological_space α] [topological_space β] [topological_space γ] (e : local_homeomorph α β)
    (e' : local_homeomorph β γ) :
    local_homeomorph.symm (local_homeomorph.trans e e') =
        local_homeomorph.trans (local_homeomorph.symm e') (local_homeomorph.symm e) :=
  sorry

/- This could be considered as a simp lemma, but there are many situations where it makes something
simple into something more complicated. -/

theorem trans_source {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α]
    [topological_space β] [topological_space γ] (e : local_homeomorph α β)
    (e' : local_homeomorph β γ) :
    local_equiv.source (to_local_equiv (local_homeomorph.trans e e')) =
        local_equiv.source (to_local_equiv e) ∩ ⇑e ⁻¹' local_equiv.source (to_local_equiv e') :=
  local_equiv.trans_source (to_local_equiv e) (to_local_equiv e')

theorem trans_source' {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α]
    [topological_space β] [topological_space γ] (e : local_homeomorph α β)
    (e' : local_homeomorph β γ) :
    local_equiv.source (to_local_equiv (local_homeomorph.trans e e')) =
        local_equiv.source (to_local_equiv e) ∩
          ⇑e ⁻¹' (local_equiv.target (to_local_equiv e) ∩ local_equiv.source (to_local_equiv e')) :=
  local_equiv.trans_source' (to_local_equiv e) (to_local_equiv e')

theorem trans_source'' {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α]
    [topological_space β] [topological_space γ] (e : local_homeomorph α β)
    (e' : local_homeomorph β γ) :
    local_equiv.source (to_local_equiv (local_homeomorph.trans e e')) =
        ⇑(local_homeomorph.symm e) ''
          (local_equiv.target (to_local_equiv e) ∩ local_equiv.source (to_local_equiv e')) :=
  local_equiv.trans_source'' (to_local_equiv e) (to_local_equiv e')

theorem image_trans_source {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α]
    [topological_space β] [topological_space γ] (e : local_homeomorph α β)
    (e' : local_homeomorph β γ) :
    ⇑e '' local_equiv.source (to_local_equiv (local_homeomorph.trans e e')) =
        local_equiv.target (to_local_equiv e) ∩ local_equiv.source (to_local_equiv e') :=
  local_equiv.image_trans_source (to_local_equiv e) (to_local_equiv e')

theorem trans_target {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α]
    [topological_space β] [topological_space γ] (e : local_homeomorph α β)
    (e' : local_homeomorph β γ) :
    local_equiv.target (to_local_equiv (local_homeomorph.trans e e')) =
        local_equiv.target (to_local_equiv e') ∩
          ⇑(local_homeomorph.symm e') ⁻¹' local_equiv.target (to_local_equiv e) :=
  rfl

theorem trans_target' {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α]
    [topological_space β] [topological_space γ] (e : local_homeomorph α β)
    (e' : local_homeomorph β γ) :
    local_equiv.target (to_local_equiv (local_homeomorph.trans e e')) =
        local_equiv.target (to_local_equiv e') ∩
          ⇑(local_homeomorph.symm e') ⁻¹'
            (local_equiv.source (to_local_equiv e') ∩ local_equiv.target (to_local_equiv e)) :=
  trans_source' (local_homeomorph.symm e') (local_homeomorph.symm e)

theorem trans_target'' {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α]
    [topological_space β] [topological_space γ] (e : local_homeomorph α β)
    (e' : local_homeomorph β γ) :
    local_equiv.target (to_local_equiv (local_homeomorph.trans e e')) =
        ⇑e' '' (local_equiv.source (to_local_equiv e') ∩ local_equiv.target (to_local_equiv e)) :=
  trans_source'' (local_homeomorph.symm e') (local_homeomorph.symm e)

theorem inv_image_trans_target {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α]
    [topological_space β] [topological_space γ] (e : local_homeomorph α β)
    (e' : local_homeomorph β γ) :
    ⇑(local_homeomorph.symm e') ''
          local_equiv.target (to_local_equiv (local_homeomorph.trans e e')) =
        local_equiv.source (to_local_equiv e') ∩ local_equiv.target (to_local_equiv e) :=
  image_trans_source (local_homeomorph.symm e') (local_homeomorph.symm e)

theorem trans_assoc {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4}
    [topological_space α] [topological_space β] [topological_space γ] [topological_space δ]
    (e : local_homeomorph α β) (e' : local_homeomorph β γ) (e'' : local_homeomorph γ δ) :
    local_homeomorph.trans (local_homeomorph.trans e e') e'' =
        local_homeomorph.trans e (local_homeomorph.trans e' e'') :=
  eq_of_local_equiv_eq
    (local_equiv.trans_assoc (to_local_equiv e) (to_local_equiv e') (to_local_equiv e''))

@[simp] theorem trans_refl {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (e : local_homeomorph α β) : local_homeomorph.trans e (local_homeomorph.refl β) = e :=
  eq_of_local_equiv_eq (local_equiv.trans_refl (to_local_equiv e))

@[simp] theorem refl_trans {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (e : local_homeomorph α β) : local_homeomorph.trans (local_homeomorph.refl α) e = e :=
  eq_of_local_equiv_eq (local_equiv.refl_trans (to_local_equiv e))

theorem trans_of_set {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (e : local_homeomorph α β) {s : set β} (hs : is_open s) :
    local_homeomorph.trans e (of_set s hs) = local_homeomorph.restr e (⇑e ⁻¹' s) :=
  sorry

theorem trans_of_set' {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (e : local_homeomorph α β) {s : set β} (hs : is_open s) :
    local_homeomorph.trans e (of_set s hs) =
        local_homeomorph.restr e (local_equiv.source (to_local_equiv e) ∩ ⇑e ⁻¹' s) :=
  sorry

theorem of_set_trans {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (e : local_homeomorph α β) {s : set α} (hs : is_open s) :
    local_homeomorph.trans (of_set s hs) e = local_homeomorph.restr e s :=
  sorry

theorem of_set_trans' {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (e : local_homeomorph α β) {s : set α} (hs : is_open s) :
    local_homeomorph.trans (of_set s hs) e =
        local_homeomorph.restr e (local_equiv.source (to_local_equiv e) ∩ s) :=
  sorry

@[simp] theorem of_set_trans_of_set {α : Type u_1} [topological_space α] {s : set α}
    (hs : is_open s) {s' : set α} (hs' : is_open s') :
    local_homeomorph.trans (of_set s hs) (of_set s' hs') = of_set (s ∩ s') (is_open_inter hs hs') :=
  sorry

theorem restr_trans {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α]
    [topological_space β] [topological_space γ] (e : local_homeomorph α β)
    (e' : local_homeomorph β γ) (s : set α) :
    local_homeomorph.trans (local_homeomorph.restr e s) e' =
        local_homeomorph.restr (local_homeomorph.trans e e') s :=
  eq_of_local_equiv_eq (local_equiv.restr_trans (to_local_equiv e) (to_local_equiv e') (interior s))

/-- `eq_on_source e e'` means that `e` and `e'` have the same source, and coincide there. They
should really be considered the same local equiv. -/
def eq_on_source {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (e : local_homeomorph α β) (e' : local_homeomorph α β) :=
  local_equiv.source (to_local_equiv e) = local_equiv.source (to_local_equiv e') ∧
    set.eq_on (⇑e) (⇑e') (local_equiv.source (to_local_equiv e))

theorem eq_on_source_iff {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (e : local_homeomorph α β) (e' : local_homeomorph α β) :
    eq_on_source e e' ↔ local_equiv.eq_on_source (to_local_equiv e) (to_local_equiv e') :=
  iff.rfl

/-- `eq_on_source` is an equivalence relation -/
protected instance setoid {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] : setoid (local_homeomorph α β) :=
  setoid.mk eq_on_source sorry

theorem eq_on_source_refl {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (e : local_homeomorph α β) : e ≈ e :=
  setoid.refl e

/-- If two local homeomorphisms are equivalent, so are their inverses -/
theorem eq_on_source.symm' {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    {e : local_homeomorph α β} {e' : local_homeomorph α β} (h : e ≈ e') :
    local_homeomorph.symm e ≈ local_homeomorph.symm e' :=
  local_equiv.eq_on_source.symm' h

/-- Two equivalent local homeomorphisms have the same source -/
theorem eq_on_source.source_eq {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] {e : local_homeomorph α β} {e' : local_homeomorph α β} (h : e ≈ e') :
    local_equiv.source (to_local_equiv e) = local_equiv.source (to_local_equiv e') :=
  and.left h

/-- Two equivalent local homeomorphisms have the same target -/
theorem eq_on_source.target_eq {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] {e : local_homeomorph α β} {e' : local_homeomorph α β} (h : e ≈ e') :
    local_equiv.target (to_local_equiv e) = local_equiv.target (to_local_equiv e') :=
  and.left (eq_on_source.symm' h)

/-- Two equivalent local homeomorphisms have coinciding `to_fun` on the source -/
theorem eq_on_source.eq_on {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    {e : local_homeomorph α β} {e' : local_homeomorph α β} (h : e ≈ e') :
    set.eq_on (⇑e) (⇑e') (local_equiv.source (to_local_equiv e)) :=
  and.right h

/-- Two equivalent local homeomorphisms have coinciding `inv_fun` on the target -/
theorem eq_on_source.symm_eq_on_target {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] {e : local_homeomorph α β} {e' : local_homeomorph α β} (h : e ≈ e') :
    set.eq_on (⇑(local_homeomorph.symm e)) (⇑(local_homeomorph.symm e'))
        (local_equiv.target (to_local_equiv e)) :=
  and.right (eq_on_source.symm' h)

/-- Composition of local homeomorphisms respects equivalence -/
theorem eq_on_source.trans' {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α]
    [topological_space β] [topological_space γ] {e : local_homeomorph α β}
    {e' : local_homeomorph α β} {f : local_homeomorph β γ} {f' : local_homeomorph β γ} (he : e ≈ e')
    (hf : f ≈ f') : local_homeomorph.trans e f ≈ local_homeomorph.trans e' f' :=
  local_equiv.eq_on_source.trans' he hf

/-- Restriction of local homeomorphisms respects equivalence -/
theorem eq_on_source.restr {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    {e : local_homeomorph α β} {e' : local_homeomorph α β} (he : e ≈ e') (s : set α) :
    local_homeomorph.restr e s ≈ local_homeomorph.restr e' s :=
  local_equiv.eq_on_source.restr he (interior s)

/-- Composition of a local homeomorphism and its inverse is equivalent to the restriction of the
identity to the source -/
theorem trans_self_symm {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (e : local_homeomorph α β) :
    local_homeomorph.trans e (local_homeomorph.symm e) ≈
        of_set (local_equiv.source (to_local_equiv e)) (open_source e) :=
  local_equiv.trans_self_symm (to_local_equiv e)

theorem trans_symm_self {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (e : local_homeomorph α β) :
    local_homeomorph.trans (local_homeomorph.symm e) e ≈
        of_set (local_equiv.target (to_local_equiv e)) (open_target e) :=
  trans_self_symm (local_homeomorph.symm e)

theorem eq_of_eq_on_source_univ {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] {e : local_homeomorph α β} {e' : local_homeomorph α β} (h : e ≈ e')
    (s : local_equiv.source (to_local_equiv e) = set.univ)
    (t : local_equiv.target (to_local_equiv e) = set.univ) : e = e' :=
  eq_of_local_equiv_eq
    (local_equiv.eq_of_eq_on_source_univ (to_local_equiv e) (to_local_equiv e') h s t)

/-- The product of two local homeomorphisms, as a local homeomorphism on the product space. -/
def prod {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} [topological_space α]
    [topological_space β] [topological_space γ] [topological_space δ] (e : local_homeomorph α β)
    (e' : local_homeomorph γ δ) : local_homeomorph (α × γ) (β × δ) :=
  mk
    (local_equiv.mk (local_equiv.to_fun (local_equiv.prod (to_local_equiv e) (to_local_equiv e')))
      (local_equiv.inv_fun (local_equiv.prod (to_local_equiv e) (to_local_equiv e')))
      (local_equiv.source (local_equiv.prod (to_local_equiv e) (to_local_equiv e')))
      (local_equiv.target (local_equiv.prod (to_local_equiv e) (to_local_equiv e'))) sorry sorry
      sorry sorry)
    sorry sorry sorry sorry

@[simp] theorem prod_to_local_equiv {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4}
    [topological_space α] [topological_space β] [topological_space γ] [topological_space δ]
    (e : local_homeomorph α β) (e' : local_homeomorph γ δ) :
    to_local_equiv (prod e e') = local_equiv.prod (to_local_equiv e) (to_local_equiv e') :=
  rfl

theorem prod_source {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4}
    [topological_space α] [topological_space β] [topological_space γ] [topological_space δ]
    (e : local_homeomorph α β) (e' : local_homeomorph γ δ) :
    local_equiv.source (to_local_equiv (prod e e')) =
        set.prod (local_equiv.source (to_local_equiv e)) (local_equiv.source (to_local_equiv e')) :=
  rfl

theorem prod_target {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4}
    [topological_space α] [topological_space β] [topological_space γ] [topological_space δ]
    (e : local_homeomorph α β) (e' : local_homeomorph γ δ) :
    local_equiv.target (to_local_equiv (prod e e')) =
        set.prod (local_equiv.target (to_local_equiv e)) (local_equiv.target (to_local_equiv e')) :=
  rfl

@[simp] theorem prod_coe {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4}
    [topological_space α] [topological_space β] [topological_space γ] [topological_space δ]
    (e : local_homeomorph α β) (e' : local_homeomorph γ δ) :
    ⇑(prod e e') = fun (p : α × γ) => (coe_fn e (prod.fst p), coe_fn e' (prod.snd p)) :=
  rfl

theorem prod_coe_symm {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4}
    [topological_space α] [topological_space β] [topological_space γ] [topological_space δ]
    (e : local_homeomorph α β) (e' : local_homeomorph γ δ) :
    ⇑(local_homeomorph.symm (prod e e')) =
        fun (p : β × δ) =>
          (coe_fn (local_homeomorph.symm e) (prod.fst p),
          coe_fn (local_homeomorph.symm e') (prod.snd p)) :=
  rfl

@[simp] theorem prod_symm {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4}
    [topological_space α] [topological_space β] [topological_space γ] [topological_space δ]
    (e : local_homeomorph α β) (e' : local_homeomorph γ δ) :
    local_homeomorph.symm (prod e e') = prod (local_homeomorph.symm e) (local_homeomorph.symm e') :=
  rfl

@[simp] theorem prod_trans {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4}
    [topological_space α] [topological_space β] [topological_space γ] [topological_space δ]
    {η : Type u_5} {ε : Type u_6} [topological_space η] [topological_space ε]
    (e : local_homeomorph α β) (f : local_homeomorph β γ) (e' : local_homeomorph δ η)
    (f' : local_homeomorph η ε) :
    local_homeomorph.trans (prod e e') (prod f f') =
        prod (local_homeomorph.trans e f) (local_homeomorph.trans e' f') :=
  sorry

/-- Continuity within a set at a point can be read under right composition with a local
homeomorphism, if the point is in its target -/
theorem continuous_within_at_iff_continuous_within_at_comp_right {α : Type u_1} {β : Type u_2}
    {γ : Type u_3} [topological_space α] [topological_space β] [topological_space γ]
    (e : local_homeomorph α β) {f : β → γ} {s : set β} {x : β}
    (h : x ∈ local_equiv.target (to_local_equiv e)) :
    continuous_within_at f s x ↔
        continuous_within_at (f ∘ ⇑e) (⇑e ⁻¹' s) (coe_fn (local_homeomorph.symm e) x) :=
  sorry

/-- Continuity at a point can be read under right composition with a local homeomorphism, if the
point is in its target -/
theorem continuous_at_iff_continuous_at_comp_right {α : Type u_1} {β : Type u_2} {γ : Type u_3}
    [topological_space α] [topological_space β] [topological_space γ] (e : local_homeomorph α β)
    {f : β → γ} {x : β} (h : x ∈ local_equiv.target (to_local_equiv e)) :
    continuous_at f x ↔ continuous_at (f ∘ ⇑e) (coe_fn (local_homeomorph.symm e) x) :=
  sorry

/-- A function is continuous on a set if and only if its composition with a local homeomorphism
on the right is continuous on the corresponding set. -/
theorem continuous_on_iff_continuous_on_comp_right {α : Type u_1} {β : Type u_2} {γ : Type u_3}
    [topological_space α] [topological_space β] [topological_space γ] (e : local_homeomorph α β)
    {f : β → γ} {s : set β} (h : s ⊆ local_equiv.target (to_local_equiv e)) :
    continuous_on f s ↔ continuous_on (f ∘ ⇑e) (local_equiv.source (to_local_equiv e) ∩ ⇑e ⁻¹' s) :=
  sorry

/-- Continuity within a set at a point can be read under left composition with a local
homeomorphism if a neighborhood of the initial point is sent to the source of the local
homeomorphism-/
theorem continuous_within_at_iff_continuous_within_at_comp_left {α : Type u_1} {β : Type u_2}
    {γ : Type u_3} [topological_space α] [topological_space β] [topological_space γ]
    (e : local_homeomorph α β) {f : γ → α} {s : set γ} {x : γ}
    (hx : f x ∈ local_equiv.source (to_local_equiv e))
    (h : f ⁻¹' local_equiv.source (to_local_equiv e) ∈ nhds_within x s) :
    continuous_within_at f s x ↔ continuous_within_at (⇑e ∘ f) s x :=
  sorry

/-- Continuity at a point can be read under left composition with a local homeomorphism if a
neighborhood of the initial point is sent to the source of the local homeomorphism-/
theorem continuous_at_iff_continuous_at_comp_left {α : Type u_1} {β : Type u_2} {γ : Type u_3}
    [topological_space α] [topological_space β] [topological_space γ] (e : local_homeomorph α β)
    {f : γ → α} {x : γ} (h : f ⁻¹' local_equiv.source (to_local_equiv e) ∈ nhds x) :
    continuous_at f x ↔ continuous_at (⇑e ∘ f) x :=
  sorry

/-- A function is continuous on a set if and only if its composition with a local homeomorphism
on the left is continuous on the corresponding set. -/
theorem continuous_on_iff_continuous_on_comp_left {α : Type u_1} {β : Type u_2} {γ : Type u_3}
    [topological_space α] [topological_space β] [topological_space γ] (e : local_homeomorph α β)
    {f : γ → α} {s : set γ} (h : s ⊆ f ⁻¹' local_equiv.source (to_local_equiv e)) :
    continuous_on f s ↔ continuous_on (⇑e ∘ f) s :=
  sorry

/-- If a local homeomorphism has source and target equal to univ, then it induces a homeomorphism
between the whole spaces, expressed in this definition. -/
def to_homeomorph_of_source_eq_univ_target_eq_univ {α : Type u_1} {β : Type u_2}
    [topological_space α] [topological_space β] (e : local_homeomorph α β)
    (h : local_equiv.source (to_local_equiv e) = set.univ)
    (h' : local_equiv.target (to_local_equiv e) = set.univ) : α ≃ₜ β :=
  homeomorph.mk (equiv.mk ⇑e ⇑(local_homeomorph.symm e) sorry sorry)

@[simp] theorem to_homeomorph_coe {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] (e : local_homeomorph α β)
    (h : local_equiv.source (to_local_equiv e) = set.univ)
    (h' : local_equiv.target (to_local_equiv e) = set.univ) :
    ⇑(to_homeomorph_of_source_eq_univ_target_eq_univ e h h') = ⇑e :=
  rfl

@[simp] theorem to_homeomorph_symm_coe {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] (e : local_homeomorph α β)
    (h : local_equiv.source (to_local_equiv e) = set.univ)
    (h' : local_equiv.target (to_local_equiv e) = set.univ) :
    ⇑(homeomorph.symm (to_homeomorph_of_source_eq_univ_target_eq_univ e h h')) =
        ⇑(local_homeomorph.symm e) :=
  rfl

/-- A local homeomorphism whose source is all of `α` defines an open embedding of `α` into `β`.  The
converse is also true; see `open_embedding.to_local_homeomorph`. -/
theorem to_open_embedding {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (e : local_homeomorph α β) (h : local_equiv.source (to_local_equiv e) = set.univ) :
    open_embedding (local_equiv.to_fun (to_local_equiv e)) :=
  sorry

end local_homeomorph


namespace homeomorph


/- Register as simp lemmas that the fields of a local homeomorphism built from a homeomorphism
correspond to the fields of the original homeomorphism. -/

@[simp] theorem to_local_homeomorph_source {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] (e : α ≃ₜ β) :
    local_equiv.source (local_homeomorph.to_local_equiv (to_local_homeomorph e)) = set.univ :=
  rfl

@[simp] theorem to_local_homeomorph_target {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] (e : α ≃ₜ β) :
    local_equiv.target (local_homeomorph.to_local_equiv (to_local_homeomorph e)) = set.univ :=
  rfl

@[simp] theorem to_local_homeomorph_coe {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] (e : α ≃ₜ β) : ⇑(to_local_homeomorph e) = ⇑e :=
  rfl

@[simp] theorem to_local_homeomorph_coe_symm {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] (e : α ≃ₜ β) :
    ⇑(local_homeomorph.symm (to_local_homeomorph e)) = ⇑(homeomorph.symm e) :=
  rfl

@[simp] theorem refl_to_local_homeomorph {α : Type u_1} [topological_space α] :
    to_local_homeomorph (homeomorph.refl α) = local_homeomorph.refl α :=
  rfl

@[simp] theorem symm_to_local_homeomorph {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] (e : α ≃ₜ β) :
    to_local_homeomorph (homeomorph.symm e) = local_homeomorph.symm (to_local_homeomorph e) :=
  rfl

@[simp] theorem trans_to_local_homeomorph {α : Type u_1} {β : Type u_2} {γ : Type u_3}
    [topological_space α] [topological_space β] [topological_space γ] (e : α ≃ₜ β) (e' : β ≃ₜ γ) :
    to_local_homeomorph (homeomorph.trans e e') =
        local_homeomorph.trans (to_local_homeomorph e) (to_local_homeomorph e') :=
  local_homeomorph.eq_of_local_equiv_eq (equiv.trans_to_local_equiv (to_equiv e) (to_equiv e'))

end homeomorph


namespace open_embedding


/-- An open embedding of `α` into `β`, with `α` nonempty, defines a local equivalence whose source
is all of `α`.  This is mainly an auxiliary lemma for the stronger result `to_local_homeomorph`. -/
def to_local_equiv {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    [Nonempty α] {f : α → β} (h : open_embedding f) : local_equiv α β :=
  set.inj_on.to_local_equiv f set.univ sorry

@[simp] theorem to_local_equiv_coe {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] [Nonempty α] {f : α → β} (h : open_embedding f) :
    ⇑(to_local_equiv h) = f :=
  rfl

@[simp] theorem to_local_equiv_source {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] [Nonempty α] {f : α → β} (h : open_embedding f) :
    local_equiv.source (to_local_equiv h) = set.univ :=
  rfl

@[simp] theorem to_local_equiv_target {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] [Nonempty α] {f : α → β} (h : open_embedding f) :
    local_equiv.target (to_local_equiv h) = set.range f :=
  sorry

theorem open_target {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    [Nonempty α] {f : α → β} (h : open_embedding f) :
    is_open (local_equiv.target (to_local_equiv h)) :=
  sorry

theorem continuous_inv_fun {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    [Nonempty α] {f : α → β} (h : open_embedding f) :
    continuous_on (local_equiv.inv_fun (to_local_equiv h))
        (local_equiv.target (to_local_equiv h)) :=
  sorry

/-- An open embedding of `α` into `β`, with `α` nonempty, defines a local homeomorphism whose source
is all of `α`.  The converse is also true; see `local_homeomorph.to_open_embedding`. -/
def to_local_homeomorph {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    [Nonempty α] {f : α → β} (h : open_embedding f) : local_homeomorph α β :=
  local_homeomorph.mk (to_local_equiv h) is_open_univ (open_target h) sorry (continuous_inv_fun h)

@[simp] theorem to_local_homeomorph_coe {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] [Nonempty α] {f : α → β} (h : open_embedding f) :
    ⇑(to_local_homeomorph h) = f :=
  rfl

@[simp] theorem source {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    [Nonempty α] {f : α → β} (h : open_embedding f) :
    local_equiv.source (local_homeomorph.to_local_equiv (to_local_homeomorph h)) = set.univ :=
  rfl

@[simp] theorem target {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    [Nonempty α] {f : α → β} (h : open_embedding f) :
    local_equiv.target (local_homeomorph.to_local_equiv (to_local_homeomorph h)) = set.range f :=
  to_local_equiv_target h

end open_embedding


-- We close and reopen the namespace to avoid

-- picking up the unnecessary `[nonempty α]` typeclass argument

namespace open_embedding


theorem continuous_at_iff {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α]
    [topological_space β] [topological_space γ] {f : α → β} {g : β → γ} (hf : open_embedding f)
    {x : α} : continuous_at (g ∘ f) x ↔ continuous_at g (f x) :=
  sorry

end open_embedding


namespace topological_space.opens


/-- The inclusion of an open subset `s` of a space `α` into `α` is a local homeomorphism from the
subtype `s` to `α`. -/
def local_homeomorph_subtype_coe {α : Type u_1} [topological_space α] (s : opens α) [Nonempty ↥s] :
    local_homeomorph (↥s) α :=
  open_embedding.to_local_homeomorph sorry

@[simp] theorem local_homeomorph_subtype_coe_coe {α : Type u_1} [topological_space α] (s : opens α)
    [Nonempty ↥s] : ⇑(local_homeomorph_subtype_coe s) = coe :=
  rfl

@[simp] theorem local_homeomorph_subtype_coe_source {α : Type u_1} [topological_space α]
    (s : opens α) [Nonempty ↥s] :
    local_equiv.source (local_homeomorph.to_local_equiv (local_homeomorph_subtype_coe s)) =
        set.univ :=
  rfl

@[simp] theorem local_homeomorph_subtype_coe_target {α : Type u_1} [topological_space α]
    (s : opens α) [Nonempty ↥s] :
    local_equiv.target (local_homeomorph.to_local_equiv (local_homeomorph_subtype_coe s)) = ↑s :=
  sorry

end topological_space.opens


namespace local_homeomorph


/-- The restriction of a local homeomorphism `e` to an open subset `s` of the domain type produces a
local homeomorphism whose domain is the subtype `s`.-/
def subtype_restr {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (e : local_homeomorph α β) (s : topological_space.opens α) [Nonempty ↥s] :
    local_homeomorph (↥s) β :=
  local_homeomorph.trans (topological_space.opens.local_homeomorph_subtype_coe s) e

theorem subtype_restr_def {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (e : local_homeomorph α β) (s : topological_space.opens α) [Nonempty ↥s] :
    subtype_restr e s =
        local_homeomorph.trans (topological_space.opens.local_homeomorph_subtype_coe s) e :=
  rfl

@[simp] theorem subtype_restr_coe {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] (e : local_homeomorph α β) (s : topological_space.opens α) [Nonempty ↥s] :
    ⇑(subtype_restr e s) = set.restrict ⇑e ↑s :=
  rfl

@[simp] theorem subtype_restr_source {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] (e : local_homeomorph α β) (s : topological_space.opens α) [Nonempty ↥s] :
    local_equiv.source (to_local_equiv (subtype_restr e s)) =
        coe ⁻¹' local_equiv.source (to_local_equiv e) :=
  sorry

/- This lemma characterizes the transition functions of an open subset in terms of the transition
functions of the original space. -/

theorem subtype_restr_symm_trans_subtype_restr {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] (s : topological_space.opens α) [Nonempty ↥s] (f : local_homeomorph α β)
    (f' : local_homeomorph α β) :
    local_homeomorph.trans (local_homeomorph.symm (subtype_restr f s)) (subtype_restr f' s) ≈
        local_homeomorph.restr (local_homeomorph.trans (local_homeomorph.symm f) f')
          (local_equiv.target (to_local_equiv f) ∩ ⇑(local_homeomorph.symm f) ⁻¹' ↑s) :=
  sorry

end Mathlib