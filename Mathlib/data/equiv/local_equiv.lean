/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.equiv.basic
import Mathlib.PostPort

universes u_5 u_6 l u_1 u_2 u_3 u_4 

namespace Mathlib

/-!
# Local equivalences

This files defines equivalences between subsets of given types.
An element `e` of `local_equiv α β` is made of two maps `e.to_fun` and `e.inv_fun` respectively
from α to β and from  β to α (just like equivs), which are inverse to each other on the subsets
`e.source` and `e.target` of respectively α and β.

They are designed in particular to define charts on manifolds.

The main functionality is `e.trans f`, which composes the two local equivalences by restricting
the source and target to the maximal set where the composition makes sense.

As for equivs, we register a coercion to functions and use it in our simp normal form: we write
`e x` and `e.symm y` instead of `e.to_fun x` and `e.inv_fun y`.

## Main definitions

`equiv.to_local_equiv`: associating a local equiv to an equiv, with source = target = univ
`local_equiv.symm`    : the inverse of a local equiv
`local_equiv.trans`   : the composition of two local equivs
`local_equiv.refl`    : the identity local equiv
`local_equiv.of_set`  : the identity on a set `s`
`eq_on_source`        : equivalence relation describing the "right" notion of equality for local
                        equivs (see below in implementation notes)

## Implementation notes

There are at least three possible implementations of local equivalences:
* equivs on subtypes
* pairs of functions taking values in `option α` and `option β`, equal to none where the local
equivalence is not defined
* pairs of functions defined everywhere, keeping the source and target as additional data

Each of these implementations has pros and cons.
* When dealing with subtypes, one still need to define additional API for composition and
restriction of domains. Checking that one always belongs to the right subtype makes things very
tedious, and leads quickly to DTT hell (as the subtype `u ∩ v` is not the "same" as `v ∩ u`, for
instance).
* With option-valued functions, the composition is very neat (it is just the usual composition, and
the domain is restricted automatically). These are implemented in `pequiv.lean`. For manifolds,
where one wants to discuss thoroughly the smoothness of the maps, this creates however a lot of
overhead as one would need to extend all classes of smoothness to option-valued maps.
* The local_equiv version as explained above is easier to use for manifolds. The drawback is that
there is extra useless data (the values of `to_fun` and `inv_fun` outside of `source` and `target`).
In particular, the equality notion between local equivs is not "the right one", i.e., coinciding
source and target and equality there. Moreover, there are no local equivs in this sense between
an empty type and a nonempty type. Since empty types are not that useful, and since one almost never
needs to talk about equal local equivs, this is not an issue in practice.
Still, we introduce an equivalence relation `eq_on_source` that captures this right notion of
equality, and show that many properties are invariant under this equivalence relation.
-/

-- register in the simpset `mfld_simps` several lemmas that are often useful when dealing

-- with manifolds

namespace tactic.interactive


/-- A very basic tactic to show that sets showing up in manifolds coincide or are included in
one another. -/
end tactic.interactive


/-- Local equivalence between subsets `source` and `target` of α and β respectively. The (global)
maps `to_fun : α → β` and `inv_fun : β → α` map `source` to `target` and conversely, and are inverse
to each other there. The values of `to_fun` outside of `source` and of `inv_fun` outside of `target`
are irrelevant. -/
structure local_equiv (α : Type u_5) (β : Type u_6) 
where
  to_fun : α → β
  inv_fun : β → α
  source : set α
  target : set β
  map_source' : ∀ {x : α}, x ∈ source → to_fun x ∈ target
  map_target' : ∀ {x : β}, x ∈ target → inv_fun x ∈ source
  left_inv' : ∀ {x : α}, x ∈ source → inv_fun (to_fun x) = x
  right_inv' : ∀ {x : β}, x ∈ target → to_fun (inv_fun x) = x

/-- Associating a local_equiv to an equiv-/
def equiv.to_local_equiv {α : Type u_1} {β : Type u_2} (e : α ≃ β) : local_equiv α β :=
  local_equiv.mk (equiv.to_fun e) (equiv.inv_fun e) set.univ set.univ sorry sorry sorry sorry

namespace local_equiv


/-- The inverse of a local equiv -/
protected def symm {α : Type u_1} {β : Type u_2} (e : local_equiv α β) : local_equiv β α :=
  mk (inv_fun e) (to_fun e) (target e) (source e) (map_target' e) (map_source' e) (right_inv' e) (left_inv' e)

protected instance has_coe_to_fun {α : Type u_1} {β : Type u_2} : has_coe_to_fun (local_equiv α β) :=
  has_coe_to_fun.mk (fun (x : local_equiv α β) => α → β) to_fun

@[simp] theorem coe_mk {α : Type u_1} {β : Type u_2} (f : α → β) (g : β → α) (s : set α) (t : set β) (ml : ∀ {x : α}, x ∈ s → f x ∈ t) (mr : ∀ {x : β}, x ∈ t → g x ∈ s) (il : ∀ {x : α}, x ∈ s → g (f x) = x) (ir : ∀ {x : β}, x ∈ t → f (g x) = x) : ⇑(mk f g s t ml mr il ir) = f :=
  rfl

@[simp] theorem coe_symm_mk {α : Type u_1} {β : Type u_2} (f : α → β) (g : β → α) (s : set α) (t : set β) (ml : ∀ {x : α}, x ∈ s → f x ∈ t) (mr : ∀ {x : β}, x ∈ t → g x ∈ s) (il : ∀ {x : α}, x ∈ s → g (f x) = x) (ir : ∀ {x : β}, x ∈ t → f (g x) = x) : ⇑(local_equiv.symm (mk f g s t ml mr il ir)) = g :=
  rfl

@[simp] theorem to_fun_as_coe {α : Type u_1} {β : Type u_2} (e : local_equiv α β) : to_fun e = ⇑e :=
  rfl

@[simp] theorem inv_fun_as_coe {α : Type u_1} {β : Type u_2} (e : local_equiv α β) : inv_fun e = ⇑(local_equiv.symm e) :=
  rfl

@[simp] theorem map_source {α : Type u_1} {β : Type u_2} (e : local_equiv α β) {x : α} (h : x ∈ source e) : coe_fn e x ∈ target e :=
  map_source' e h

protected theorem maps_to {α : Type u_1} {β : Type u_2} (e : local_equiv α β) : set.maps_to (⇑e) (source e) (target e) :=
  fun (_x : α) => map_source e

@[simp] theorem map_target {α : Type u_1} {β : Type u_2} (e : local_equiv α β) {x : β} (h : x ∈ target e) : coe_fn (local_equiv.symm e) x ∈ source e :=
  map_target' e h

theorem symm_maps_to {α : Type u_1} {β : Type u_2} (e : local_equiv α β) : set.maps_to (⇑(local_equiv.symm e)) (target e) (source e) :=
  local_equiv.maps_to (local_equiv.symm e)

@[simp] theorem left_inv {α : Type u_1} {β : Type u_2} (e : local_equiv α β) {x : α} (h : x ∈ source e) : coe_fn (local_equiv.symm e) (coe_fn e x) = x :=
  left_inv' e h

protected theorem left_inv_on {α : Type u_1} {β : Type u_2} (e : local_equiv α β) : set.left_inv_on (⇑(local_equiv.symm e)) (⇑e) (source e) :=
  fun (_x : α) => left_inv e

@[simp] theorem right_inv {α : Type u_1} {β : Type u_2} (e : local_equiv α β) {x : β} (h : x ∈ target e) : coe_fn e (coe_fn (local_equiv.symm e) x) = x :=
  right_inv' e h

protected theorem right_inv_on {α : Type u_1} {β : Type u_2} (e : local_equiv α β) : set.right_inv_on (⇑(local_equiv.symm e)) (⇑e) (target e) :=
  fun (_x : β) => right_inv e

/-- Associating to a local_equiv an equiv between the source and the target -/
protected def to_equiv {α : Type u_1} {β : Type u_2} (e : local_equiv α β) : ↥(source e) ≃ ↥(target e) :=
  equiv.mk (fun (x : ↥(source e)) => { val := coe_fn e ↑x, property := sorry })
    (fun (y : ↥(target e)) => { val := coe_fn (local_equiv.symm e) ↑y, property := sorry }) sorry sorry

@[simp] theorem symm_source {α : Type u_1} {β : Type u_2} (e : local_equiv α β) : source (local_equiv.symm e) = target e :=
  rfl

@[simp] theorem symm_target {α : Type u_1} {β : Type u_2} (e : local_equiv α β) : target (local_equiv.symm e) = source e :=
  rfl

@[simp] theorem symm_symm {α : Type u_1} {β : Type u_2} (e : local_equiv α β) : local_equiv.symm (local_equiv.symm e) = e := sorry

/-- A local equiv induces a bijection between its source and target -/
theorem bij_on_source {α : Type u_1} {β : Type u_2} (e : local_equiv α β) : set.bij_on (⇑e) (source e) (target e) :=
  set.inv_on.bij_on { left := local_equiv.left_inv_on e, right := local_equiv.right_inv_on e } (local_equiv.maps_to e)
    (symm_maps_to e)

theorem image_eq_target_inter_inv_preimage {α : Type u_1} {β : Type u_2} (e : local_equiv α β) {s : set α} (h : s ⊆ source e) : ⇑e '' s = target e ∩ ⇑(local_equiv.symm e) ⁻¹' s := sorry

theorem image_inter_source_eq {α : Type u_1} {β : Type u_2} (e : local_equiv α β) (s : set α) : ⇑e '' (s ∩ source e) = target e ∩ ⇑(local_equiv.symm e) ⁻¹' (s ∩ source e) :=
  image_eq_target_inter_inv_preimage e (set.inter_subset_right s (source e))

theorem image_inter_source_eq' {α : Type u_1} {β : Type u_2} (e : local_equiv α β) (s : set α) : ⇑e '' (s ∩ source e) = target e ∩ ⇑(local_equiv.symm e) ⁻¹' s := sorry

theorem symm_image_eq_source_inter_preimage {α : Type u_1} {β : Type u_2} (e : local_equiv α β) {s : set β} (h : s ⊆ target e) : ⇑(local_equiv.symm e) '' s = source e ∩ ⇑e ⁻¹' s :=
  image_eq_target_inter_inv_preimage (local_equiv.symm e) h

theorem symm_image_inter_target_eq {α : Type u_1} {β : Type u_2} (e : local_equiv α β) (s : set β) : ⇑(local_equiv.symm e) '' (s ∩ target e) = source e ∩ ⇑e ⁻¹' (s ∩ target e) :=
  image_inter_source_eq (local_equiv.symm e) s

theorem symm_image_inter_target_eq' {α : Type u_1} {β : Type u_2} (e : local_equiv α β) (s : set β) : ⇑(local_equiv.symm e) '' (s ∩ target e) = source e ∩ ⇑e ⁻¹' s :=
  image_inter_source_eq' (local_equiv.symm e) s

theorem source_inter_preimage_inv_preimage {α : Type u_1} {β : Type u_2} (e : local_equiv α β) (s : set α) : source e ∩ ⇑e ⁻¹' (⇑(local_equiv.symm e) ⁻¹' s) = source e ∩ s := sorry

theorem target_inter_inv_preimage_preimage {α : Type u_1} {β : Type u_2} (e : local_equiv α β) (s : set β) : target e ∩ ⇑(local_equiv.symm e) ⁻¹' (⇑e ⁻¹' s) = target e ∩ s :=
  source_inter_preimage_inv_preimage (local_equiv.symm e) s

theorem image_source_eq_target {α : Type u_1} {β : Type u_2} (e : local_equiv α β) : ⇑e '' source e = target e :=
  set.bij_on.image_eq (bij_on_source e)

theorem source_subset_preimage_target {α : Type u_1} {β : Type u_2} (e : local_equiv α β) : source e ⊆ ⇑e ⁻¹' target e :=
  fun (x : α) (hx : x ∈ source e) => map_source e hx

theorem inv_image_target_eq_source {α : Type u_1} {β : Type u_2} (e : local_equiv α β) : ⇑(local_equiv.symm e) '' target e = source e :=
  set.bij_on.image_eq (bij_on_source (local_equiv.symm e))

theorem target_subset_preimage_source {α : Type u_1} {β : Type u_2} (e : local_equiv α β) : target e ⊆ ⇑(local_equiv.symm e) ⁻¹' source e :=
  fun (x : β) (hx : x ∈ target e) => map_target e hx

/-- Two local equivs that have the same `source`, same `to_fun` and same `inv_fun`, coincide. -/
protected theorem ext {α : Type u_1} {β : Type u_2} {e : local_equiv α β} {e' : local_equiv α β} (h : ∀ (x : α), coe_fn e x = coe_fn e' x) (hsymm : ∀ (x : β), coe_fn (local_equiv.symm e) x = coe_fn (local_equiv.symm e') x) (hs : source e = source e') : e = e' := sorry

/-- Restricting a local equivalence to e.source ∩ s -/
protected def restr {α : Type u_1} {β : Type u_2} (e : local_equiv α β) (s : set α) : local_equiv α β :=
  mk (⇑e) (⇑(local_equiv.symm e)) (source e ∩ s) (target e ∩ ⇑(local_equiv.symm e) ⁻¹' s) sorry sorry sorry sorry

@[simp] theorem restr_coe {α : Type u_1} {β : Type u_2} (e : local_equiv α β) (s : set α) : ⇑(local_equiv.restr e s) = ⇑e :=
  rfl

@[simp] theorem restr_coe_symm {α : Type u_1} {β : Type u_2} (e : local_equiv α β) (s : set α) : ⇑(local_equiv.symm (local_equiv.restr e s)) = ⇑(local_equiv.symm e) :=
  rfl

@[simp] theorem restr_source {α : Type u_1} {β : Type u_2} (e : local_equiv α β) (s : set α) : source (local_equiv.restr e s) = source e ∩ s :=
  rfl

@[simp] theorem restr_target {α : Type u_1} {β : Type u_2} (e : local_equiv α β) (s : set α) : target (local_equiv.restr e s) = target e ∩ ⇑(local_equiv.symm e) ⁻¹' s :=
  rfl

theorem restr_eq_of_source_subset {α : Type u_1} {β : Type u_2} {e : local_equiv α β} {s : set α} (h : source e ⊆ s) : local_equiv.restr e s = e := sorry

@[simp] theorem restr_univ {α : Type u_1} {β : Type u_2} {e : local_equiv α β} : local_equiv.restr e set.univ = e :=
  restr_eq_of_source_subset (set.subset_univ (source e))

/-- The identity local equiv -/
protected def refl (α : Type u_1) : local_equiv α α :=
  equiv.to_local_equiv (equiv.refl α)

@[simp] theorem refl_source {α : Type u_1} : source (local_equiv.refl α) = set.univ :=
  rfl

@[simp] theorem refl_target {α : Type u_1} : target (local_equiv.refl α) = set.univ :=
  rfl

@[simp] theorem refl_coe {α : Type u_1} : ⇑(local_equiv.refl α) = id :=
  rfl

@[simp] theorem refl_symm {α : Type u_1} : local_equiv.symm (local_equiv.refl α) = local_equiv.refl α :=
  rfl

@[simp] theorem refl_restr_source {α : Type u_1} (s : set α) : source (local_equiv.restr (local_equiv.refl α) s) = s := sorry

@[simp] theorem refl_restr_target {α : Type u_1} (s : set α) : target (local_equiv.restr (local_equiv.refl α) s) = s := sorry

/-- The identity local equiv on a set `s` -/
def of_set {α : Type u_1} (s : set α) : local_equiv α α :=
  mk id id s s sorry sorry sorry sorry

@[simp] theorem of_set_source {α : Type u_1} (s : set α) : source (of_set s) = s :=
  rfl

@[simp] theorem of_set_target {α : Type u_1} (s : set α) : target (of_set s) = s :=
  rfl

@[simp] theorem of_set_coe {α : Type u_1} (s : set α) : ⇑(of_set s) = id :=
  rfl

@[simp] theorem of_set_symm {α : Type u_1} (s : set α) : local_equiv.symm (of_set s) = of_set s :=
  rfl

/-- Composing two local equivs if the target of the first coincides with the source of the
second. -/
protected def trans' {α : Type u_1} {β : Type u_2} {γ : Type u_3} (e : local_equiv α β) (e' : local_equiv β γ) (h : target e = source e') : local_equiv α γ :=
  mk (⇑e' ∘ ⇑e) (⇑(local_equiv.symm e) ∘ ⇑(local_equiv.symm e')) (source e) (target e') sorry sorry sorry sorry

/-- Composing two local equivs, by restricting to the maximal domain where their composition
is well defined. -/
protected def trans {α : Type u_1} {β : Type u_2} {γ : Type u_3} (e : local_equiv α β) (e' : local_equiv β γ) : local_equiv α γ :=
  local_equiv.trans' (local_equiv.symm (local_equiv.restr (local_equiv.symm e) (source e')))
    (local_equiv.restr e' (target e)) sorry

@[simp] theorem coe_trans {α : Type u_1} {β : Type u_2} {γ : Type u_3} (e : local_equiv α β) (e' : local_equiv β γ) : ⇑(local_equiv.trans e e') = ⇑e' ∘ ⇑e :=
  rfl

@[simp] theorem coe_trans_symm {α : Type u_1} {β : Type u_2} {γ : Type u_3} (e : local_equiv α β) (e' : local_equiv β γ) : ⇑(local_equiv.symm (local_equiv.trans e e')) = ⇑(local_equiv.symm e) ∘ ⇑(local_equiv.symm e') :=
  rfl

theorem trans_symm_eq_symm_trans_symm {α : Type u_1} {β : Type u_2} {γ : Type u_3} (e : local_equiv α β) (e' : local_equiv β γ) : local_equiv.symm (local_equiv.trans e e') = local_equiv.trans (local_equiv.symm e') (local_equiv.symm e) := sorry

@[simp] theorem trans_source {α : Type u_1} {β : Type u_2} {γ : Type u_3} (e : local_equiv α β) (e' : local_equiv β γ) : source (local_equiv.trans e e') = source e ∩ ⇑e ⁻¹' source e' :=
  rfl

theorem trans_source' {α : Type u_1} {β : Type u_2} {γ : Type u_3} (e : local_equiv α β) (e' : local_equiv β γ) : source (local_equiv.trans e e') = source e ∩ ⇑e ⁻¹' (target e ∩ source e') := sorry

theorem trans_source'' {α : Type u_1} {β : Type u_2} {γ : Type u_3} (e : local_equiv α β) (e' : local_equiv β γ) : source (local_equiv.trans e e') = ⇑(local_equiv.symm e) '' (target e ∩ source e') := sorry

theorem image_trans_source {α : Type u_1} {β : Type u_2} {γ : Type u_3} (e : local_equiv α β) (e' : local_equiv β γ) : ⇑e '' source (local_equiv.trans e e') = target e ∩ source e' :=
  image_source_eq_target (local_equiv.symm (local_equiv.restr (local_equiv.symm e) (source e')))

@[simp] theorem trans_target {α : Type u_1} {β : Type u_2} {γ : Type u_3} (e : local_equiv α β) (e' : local_equiv β γ) : target (local_equiv.trans e e') = target e' ∩ ⇑(local_equiv.symm e') ⁻¹' target e :=
  rfl

theorem trans_target' {α : Type u_1} {β : Type u_2} {γ : Type u_3} (e : local_equiv α β) (e' : local_equiv β γ) : target (local_equiv.trans e e') = target e' ∩ ⇑(local_equiv.symm e') ⁻¹' (source e' ∩ target e) :=
  trans_source' (local_equiv.symm e') (local_equiv.symm e)

theorem trans_target'' {α : Type u_1} {β : Type u_2} {γ : Type u_3} (e : local_equiv α β) (e' : local_equiv β γ) : target (local_equiv.trans e e') = ⇑e' '' (source e' ∩ target e) :=
  trans_source'' (local_equiv.symm e') (local_equiv.symm e)

theorem inv_image_trans_target {α : Type u_1} {β : Type u_2} {γ : Type u_3} (e : local_equiv α β) (e' : local_equiv β γ) : ⇑(local_equiv.symm e') '' target (local_equiv.trans e e') = source e' ∩ target e :=
  image_trans_source (local_equiv.symm e') (local_equiv.symm e)

theorem trans_assoc {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} (e : local_equiv α β) (e' : local_equiv β γ) (e'' : local_equiv γ δ) : local_equiv.trans (local_equiv.trans e e') e'' = local_equiv.trans e (local_equiv.trans e' e'') := sorry

@[simp] theorem trans_refl {α : Type u_1} {β : Type u_2} (e : local_equiv α β) : local_equiv.trans e (local_equiv.refl β) = e := sorry

@[simp] theorem refl_trans {α : Type u_1} {β : Type u_2} (e : local_equiv α β) : local_equiv.trans (local_equiv.refl α) e = e := sorry

theorem trans_refl_restr {α : Type u_1} {β : Type u_2} (e : local_equiv α β) (s : set β) : local_equiv.trans e (local_equiv.restr (local_equiv.refl β) s) = local_equiv.restr e (⇑e ⁻¹' s) := sorry

theorem trans_refl_restr' {α : Type u_1} {β : Type u_2} (e : local_equiv α β) (s : set β) : local_equiv.trans e (local_equiv.restr (local_equiv.refl β) s) = local_equiv.restr e (source e ∩ ⇑e ⁻¹' s) := sorry

theorem restr_trans {α : Type u_1} {β : Type u_2} {γ : Type u_3} (e : local_equiv α β) (e' : local_equiv β γ) (s : set α) : local_equiv.trans (local_equiv.restr e s) e' = local_equiv.restr (local_equiv.trans e e') s := sorry

/-- `eq_on_source e e'` means that `e` and `e'` have the same source, and coincide there. Then `e`
and `e'` should really be considered the same local equiv. -/
def eq_on_source {α : Type u_1} {β : Type u_2} (e : local_equiv α β) (e' : local_equiv α β)  :=
  source e = source e' ∧ set.eq_on (⇑e) (⇑e') (source e)

/-- `eq_on_source` is an equivalence relation -/
protected instance eq_on_source_setoid {α : Type u_1} {β : Type u_2} : setoid (local_equiv α β) :=
  setoid.mk eq_on_source sorry

theorem eq_on_source_refl {α : Type u_1} {β : Type u_2} (e : local_equiv α β) : e ≈ e :=
  setoid.refl e

/-- Two equivalent local equivs have the same source -/
theorem eq_on_source.source_eq {α : Type u_1} {β : Type u_2} {e : local_equiv α β} {e' : local_equiv α β} (h : e ≈ e') : source e = source e' :=
  and.left h

/-- Two equivalent local equivs coincide on the source -/
theorem eq_on_source.eq_on {α : Type u_1} {β : Type u_2} {e : local_equiv α β} {e' : local_equiv α β} (h : e ≈ e') : set.eq_on (⇑e) (⇑e') (source e) :=
  and.right h

/-- Two equivalent local equivs have the same target -/
theorem eq_on_source.target_eq {α : Type u_1} {β : Type u_2} {e : local_equiv α β} {e' : local_equiv α β} (h : e ≈ e') : target e = target e' := sorry

/-- If two local equivs are equivalent, so are their inverses. -/
theorem eq_on_source.symm' {α : Type u_1} {β : Type u_2} {e : local_equiv α β} {e' : local_equiv α β} (h : e ≈ e') : local_equiv.symm e ≈ local_equiv.symm e' := sorry

/-- Two equivalent local equivs have coinciding inverses on the target -/
theorem eq_on_source.symm_eq_on {α : Type u_1} {β : Type u_2} {e : local_equiv α β} {e' : local_equiv α β} (h : e ≈ e') : set.eq_on (⇑(local_equiv.symm e)) (⇑(local_equiv.symm e')) (target e) :=
  eq_on_source.eq_on (eq_on_source.symm' h)

/-- Composition of local equivs respects equivalence -/
theorem eq_on_source.trans' {α : Type u_1} {β : Type u_2} {γ : Type u_3} {e : local_equiv α β} {e' : local_equiv α β} {f : local_equiv β γ} {f' : local_equiv β γ} (he : e ≈ e') (hf : f ≈ f') : local_equiv.trans e f ≈ local_equiv.trans e' f' := sorry

/-- Restriction of local equivs respects equivalence -/
theorem eq_on_source.restr {α : Type u_1} {β : Type u_2} {e : local_equiv α β} {e' : local_equiv α β} (he : e ≈ e') (s : set α) : local_equiv.restr e s ≈ local_equiv.restr e' s := sorry

/-- Preimages are respected by equivalence -/
theorem eq_on_source.source_inter_preimage_eq {α : Type u_1} {β : Type u_2} {e : local_equiv α β} {e' : local_equiv α β} (he : e ≈ e') (s : set β) : source e ∩ ⇑e ⁻¹' s = source e' ∩ ⇑e' ⁻¹' s := sorry

/-- Composition of a local equiv and its inverse is equivalent to the restriction of the identity
to the source -/
theorem trans_self_symm {α : Type u_1} {β : Type u_2} (e : local_equiv α β) : local_equiv.trans e (local_equiv.symm e) ≈ of_set (source e) := sorry

/-- Composition of the inverse of a local equiv and this local equiv is equivalent to the
restriction of the identity to the target -/
theorem trans_symm_self {α : Type u_1} {β : Type u_2} (e : local_equiv α β) : local_equiv.trans (local_equiv.symm e) e ≈ of_set (target e) :=
  trans_self_symm (local_equiv.symm e)

/-- Two equivalent local equivs are equal when the source and target are univ -/
theorem eq_of_eq_on_source_univ {α : Type u_1} {β : Type u_2} (e : local_equiv α β) (e' : local_equiv α β) (h : e ≈ e') (s : source e = set.univ) (t : target e = set.univ) : e = e' := sorry

/-- The product of two local equivs, as a local equiv on the product. -/
def prod {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} (e : local_equiv α β) (e' : local_equiv γ δ) : local_equiv (α × γ) (β × δ) :=
  mk (fun (p : α × γ) => (coe_fn e (prod.fst p), coe_fn e' (prod.snd p)))
    (fun (p : β × δ) => (coe_fn (local_equiv.symm e) (prod.fst p), coe_fn (local_equiv.symm e') (prod.snd p)))
    (set.prod (source e) (source e')) (set.prod (target e) (target e')) sorry sorry sorry sorry

@[simp] theorem prod_source {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} (e : local_equiv α β) (e' : local_equiv γ δ) : source (prod e e') = set.prod (source e) (source e') :=
  rfl

@[simp] theorem prod_target {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} (e : local_equiv α β) (e' : local_equiv γ δ) : target (prod e e') = set.prod (target e) (target e') :=
  rfl

@[simp] theorem prod_coe {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} (e : local_equiv α β) (e' : local_equiv γ δ) : ⇑(prod e e') = fun (p : α × γ) => (coe_fn e (prod.fst p), coe_fn e' (prod.snd p)) :=
  rfl

theorem prod_coe_symm {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} (e : local_equiv α β) (e' : local_equiv γ δ) : ⇑(local_equiv.symm (prod e e')) =
  fun (p : β × δ) => (coe_fn (local_equiv.symm e) (prod.fst p), coe_fn (local_equiv.symm e') (prod.snd p)) :=
  rfl

@[simp] theorem prod_symm {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} (e : local_equiv α β) (e' : local_equiv γ δ) : local_equiv.symm (prod e e') = prod (local_equiv.symm e) (local_equiv.symm e') := sorry

@[simp] theorem prod_trans {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {η : Type u_5} {ε : Type u_6} (e : local_equiv α β) (f : local_equiv β γ) (e' : local_equiv δ η) (f' : local_equiv η ε) : local_equiv.trans (prod e e') (prod f f') = prod (local_equiv.trans e f) (local_equiv.trans e' f') := sorry

end local_equiv


namespace set


-- All arguments are explicit to avoid missing information in the pretty printer output

/-- A bijection between two sets `s : set α` and `t : set β` provides a local equivalence
between `α` and `β`. -/
@[simp] theorem bij_on.to_local_equiv_inv_fun {α : Type u_1} {β : Type u_2} [Nonempty α] (f : α → β) (s : set α) (t : set β) (hf : bij_on f s t) (b : β) : local_equiv.inv_fun (bij_on.to_local_equiv f s t hf) b = function.inv_fun_on f s b :=
  Eq.refl (local_equiv.inv_fun (bij_on.to_local_equiv f s t hf) b)

/-- A map injective on a subset of its domain provides a local equivalence. -/
@[simp] def inj_on.to_local_equiv {α : Type u_1} {β : Type u_2} [Nonempty α] (f : α → β) (s : set α) (hf : inj_on f s) : local_equiv α β :=
  bij_on.to_local_equiv f s (f '' s) (inj_on.bij_on_image hf)

end set


namespace equiv


/- equivs give rise to local_equiv. We set up simp lemmas to reduce most properties of the local
equiv to that of the equiv. -/

@[simp] theorem to_local_equiv_coe {α : Type u_1} {β : Type u_2} (e : α ≃ β) : ⇑(to_local_equiv e) = ⇑e :=
  rfl

@[simp] theorem to_local_equiv_symm_coe {α : Type u_1} {β : Type u_2} (e : α ≃ β) : ⇑(local_equiv.symm (to_local_equiv e)) = ⇑(equiv.symm e) :=
  rfl

@[simp] theorem to_local_equiv_source {α : Type u_1} {β : Type u_2} (e : α ≃ β) : local_equiv.source (to_local_equiv e) = set.univ :=
  rfl

@[simp] theorem to_local_equiv_target {α : Type u_1} {β : Type u_2} (e : α ≃ β) : local_equiv.target (to_local_equiv e) = set.univ :=
  rfl

@[simp] theorem refl_to_local_equiv {α : Type u_1} : to_local_equiv (equiv.refl α) = local_equiv.refl α :=
  rfl

@[simp] theorem symm_to_local_equiv {α : Type u_1} {β : Type u_2} (e : α ≃ β) : to_local_equiv (equiv.symm e) = local_equiv.symm (to_local_equiv e) :=
  rfl

@[simp] theorem trans_to_local_equiv {α : Type u_1} {β : Type u_2} {γ : Type u_3} (e : α ≃ β) (e' : β ≃ γ) : to_local_equiv (equiv.trans e e') = local_equiv.trans (to_local_equiv e) (to_local_equiv e') := sorry

