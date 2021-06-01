/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

Finite types.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.wlog
import Mathlib.data.finset.powerset
import Mathlib.data.finset.lattice
import Mathlib.data.finset.pi
import Mathlib.data.array.lemmas
import Mathlib.order.well_founded
import Mathlib.group_theory.perm.basic
import Mathlib.PostPort

universes u_4 l u_1 u_2 u v 

namespace Mathlib

/-- `fintype α` means that `α` is finite, i.e. there are only
  finitely many distinct elements of type `α`. The evidence of this
  is a finset `elems` (a list up to permutation without duplicates),
  together with a proof that everything of type `α` is in the list. -/
class fintype (α : Type u_4) where
  elems : finset α
  complete : ∀ (x : α), x ∈ elems

namespace finset


/-- `univ` is the universal finite set of type `finset α` implied from
  the assumption `fintype α`. -/
def univ {α : Type u_1} [fintype α] : finset α := fintype.elems α

@[simp] theorem mem_univ {α : Type u_1} [fintype α] (x : α) : x ∈ univ := fintype.complete x

@[simp] theorem mem_univ_val {α : Type u_1} [fintype α] (x : α) : x ∈ val univ := mem_univ

@[simp] theorem coe_univ {α : Type u_1} [fintype α] : ↑univ = set.univ := sorry

theorem univ_nonempty_iff {α : Type u_1} [fintype α] : finset.nonempty univ ↔ Nonempty α := sorry

theorem univ_nonempty {α : Type u_1} [fintype α] [Nonempty α] : finset.nonempty univ :=
  iff.mpr univ_nonempty_iff _inst_2

theorem univ_eq_empty {α : Type u_1} [fintype α] : univ = ∅ ↔ ¬Nonempty α := sorry

theorem subset_univ {α : Type u_1} [fintype α] (s : finset α) : s ⊆ univ :=
  fun (a : α) (_x : a ∈ s) => mem_univ a

protected instance order_top {α : Type u_1} [fintype α] : order_top (finset α) :=
  order_top.mk univ partial_order.le partial_order.lt sorry sorry sorry subset_univ

protected instance boolean_algebra {α : Type u_1} [fintype α] [DecidableEq α] :
    boolean_algebra (finset α) :=
  boolean_algebra.mk distrib_lattice.sup distrib_lattice.le distrib_lattice.lt sorry sorry sorry
    sorry sorry sorry distrib_lattice.inf sorry sorry sorry sorry order_top.top sorry
    semilattice_inf_bot.bot sorry (fun (s : finset α) => univ \ s) has_sdiff.sdiff sorry sorry sorry

theorem compl_eq_univ_sdiff {α : Type u_1} [fintype α] [DecidableEq α] (s : finset α) :
    sᶜ = univ \ s :=
  rfl

@[simp] theorem mem_compl {α : Type u_1} [fintype α] [DecidableEq α] {s : finset α} {x : α} :
    x ∈ (sᶜ) ↔ ¬x ∈ s :=
  sorry

@[simp] theorem coe_compl {α : Type u_1} [fintype α] [DecidableEq α] (s : finset α) :
    ↑(sᶜ) = (↑sᶜ) :=
  set.ext fun (x : α) => mem_compl

theorem eq_univ_iff_forall {α : Type u_1} [fintype α] {s : finset α} :
    s = univ ↔ ∀ (x : α), x ∈ s :=
  sorry

theorem compl_ne_univ_iff_nonempty {α : Type u_1} [fintype α] [DecidableEq α] (s : finset α) :
    sᶜ ≠ univ ↔ finset.nonempty s :=
  sorry

@[simp] theorem univ_inter {α : Type u_1} [fintype α] [DecidableEq α] (s : finset α) :
    univ ∩ s = s :=
  sorry

@[simp] theorem inter_univ {α : Type u_1} [fintype α] [DecidableEq α] (s : finset α) :
    s ∩ univ = s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (s ∩ univ = s)) (inter_comm s univ)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (univ ∩ s = s)) (univ_inter s))) (Eq.refl s))

@[simp] theorem piecewise_univ {α : Type u_1} [fintype α] [(i : α) → Decidable (i ∈ univ)]
    {δ : α → Sort u_2} (f : (i : α) → δ i) (g : (i : α) → δ i) : piecewise univ f g = f :=
  sorry

theorem piecewise_compl {α : Type u_1} [fintype α] [DecidableEq α] (s : finset α)
    [(i : α) → Decidable (i ∈ s)] [(i : α) → Decidable (i ∈ (sᶜ))] {δ : α → Sort u_2}
    (f : (i : α) → δ i) (g : (i : α) → δ i) : piecewise (sᶜ) f g = piecewise s g f :=
  sorry

theorem univ_map_equiv_to_embedding {α : Type u_1} {β : Type u_2} [fintype α] [fintype β]
    (e : α ≃ β) : map (equiv.to_embedding e) univ = univ :=
  sorry

@[simp] theorem univ_filter_exists {α : Type u_1} {β : Type u_2} [fintype α] (f : α → β) [fintype β]
    [decidable_pred fun (y : β) => ∃ (x : α), f x = y] [DecidableEq β] :
    filter (fun (y : β) => ∃ (x : α), f x = y) univ = image f univ :=
  sorry

/-- Note this is a special case of `(finset.image_preimage f univ _).symm`. -/
theorem univ_filter_mem_range {α : Type u_1} {β : Type u_2} [fintype α] (f : α → β) [fintype β]
    [decidable_pred fun (y : β) => y ∈ set.range f] [DecidableEq β] :
    filter (fun (y : β) => y ∈ set.range f) univ = image f univ :=
  univ_filter_exists f

end finset


namespace fintype


protected instance decidable_pi_fintype {α : Type u_1} {β : α → Type u_2}
    [(a : α) → DecidableEq (β a)] [fintype α] : DecidableEq ((a : α) → β a) :=
  fun (f g : (a : α) → β a) => decidable_of_iff (∀ (a : α), a ∈ elems α → f a = g a) sorry

protected instance decidable_forall_fintype {α : Type u_1} {p : α → Prop} [decidable_pred p]
    [fintype α] : Decidable (∀ (a : α), p a) :=
  decidable_of_iff (∀ (a : α), a ∈ finset.univ → p a) sorry

protected instance decidable_exists_fintype {α : Type u_1} {p : α → Prop} [decidable_pred p]
    [fintype α] : Decidable (∃ (a : α), p a) :=
  decidable_of_iff (∃ (a : α), ∃ (H : a ∈ finset.univ), p a) sorry

protected instance decidable_eq_equiv_fintype {α : Type u_1} {β : Type u_2} [DecidableEq β]
    [fintype α] : DecidableEq (α ≃ β) :=
  fun (a b : α ≃ β) => decidable_of_iff (equiv.to_fun a = equiv.to_fun b) sorry

protected instance decidable_injective_fintype {α : Type u_1} {β : Type u_2} [DecidableEq α]
    [DecidableEq β] [fintype α] : decidable_pred function.injective :=
  fun (x : α → β) => eq.mpr sorry fintype.decidable_forall_fintype

protected instance decidable_surjective_fintype {α : Type u_1} {β : Type u_2} [DecidableEq β]
    [fintype α] [fintype β] : decidable_pred function.surjective :=
  fun (x : α → β) => eq.mpr sorry fintype.decidable_forall_fintype

protected instance decidable_bijective_fintype {α : Type u_1} {β : Type u_2} [DecidableEq α]
    [DecidableEq β] [fintype α] [fintype β] : decidable_pred function.bijective :=
  fun (x : α → β) => eq.mpr sorry and.decidable

protected instance decidable_left_inverse_fintype {α : Type u_1} {β : Type u_2} [DecidableEq α]
    [fintype α] (f : α → β) (g : β → α) : Decidable (function.right_inverse f g) :=
  (fun (this : Decidable (∀ (x : α), g (f x) = x)) => this) fintype.decidable_forall_fintype

protected instance decidable_right_inverse_fintype {α : Type u_1} {β : Type u_2} [DecidableEq β]
    [fintype β] (f : α → β) (g : β → α) : Decidable (function.left_inverse f g) :=
  (fun (this : Decidable (∀ (x : β), f (g x) = x)) => this) fintype.decidable_forall_fintype

/-- Construct a proof of `fintype α` from a universal multiset -/
def of_multiset {α : Type u_1} [DecidableEq α] (s : multiset α) (H : ∀ (x : α), x ∈ s) :
    fintype α :=
  mk (multiset.to_finset s) sorry

/-- Construct a proof of `fintype α` from a universal list -/
def of_list {α : Type u_1} [DecidableEq α] (l : List α) (H : ∀ (x : α), x ∈ l) : fintype α :=
  mk (list.to_finset l) sorry

theorem exists_univ_list (α : Type u_1) [fintype α] :
    ∃ (l : List α), list.nodup l ∧ ∀ (x : α), x ∈ l :=
  sorry

/-- `card α` is the number of elements in `α`, defined when `α` is a fintype. -/
def card (α : Type u_1) [fintype α] : ℕ := finset.card finset.univ

/-- If `l` lists all the elements of `α` without duplicates, then `α ≃ fin (l.length)`. -/
def equiv_fin_of_forall_mem_list {α : Type u_1} [DecidableEq α] {l : List α} (h : ∀ (x : α), x ∈ l)
    (nd : list.nodup l) : α ≃ fin (list.length l) :=
  equiv.mk (fun (a : α) => { val := list.index_of a l, property := sorry })
    (fun (i : fin (list.length l)) => list.nth_le l (subtype.val i) sorry) sorry sorry

/-- There is (computably) a bijection between `α` and `fin n` where
  `n = card α`. Since it is not unique, and depends on which permutation
  of the universe list is used, the bijection is wrapped in `trunc` to
  preserve computability.  -/
def equiv_fin (α : Type u_1) [DecidableEq α] [fintype α] : trunc (α ≃ fin (card α)) :=
  eq.mpr sorry
    (quot.rec_on_subsingleton (finset.val finset.univ)
      (fun (l : List α) (h : ∀ (x : α), x ∈ l) (nd : list.nodup l) =>
        trunc.mk (equiv_fin_of_forall_mem_list h nd))
      finset.mem_univ_val sorry)

theorem exists_equiv_fin (α : Type u_1) [fintype α] : ∃ (n : ℕ), Nonempty (α ≃ fin n) :=
  Exists.intro (card α) (nonempty_of_trunc (equiv_fin α))

protected instance subsingleton (α : Type u_1) : subsingleton (fintype α) :=
  subsingleton.intro fun (_x : fintype α) => sorry

/-- Given a predicate that can be represented by a finset, the subtype
associated to the predicate is a fintype. -/
protected def subtype {α : Type u_1} {p : α → Prop} (s : finset α) (H : ∀ (x : α), x ∈ s ↔ p x) :
    fintype (Subtype fun (x : α) => p x) :=
  mk (finset.mk (multiset.pmap Subtype.mk (finset.val s) sorry) sorry) sorry

theorem subtype_card {α : Type u_1} {p : α → Prop} (s : finset α) (H : ∀ (x : α), x ∈ s ↔ p x) :
    card (Subtype fun (x : α) => p x) = finset.card s :=
  multiset.card_pmap Subtype.mk (finset.val s) (subtype._proof_1 s H)

theorem card_of_subtype {α : Type u_1} {p : α → Prop} (s : finset α) (H : ∀ (x : α), x ∈ s ↔ p x)
    [fintype (Subtype fun (x : α) => p x)] : card (Subtype fun (x : α) => p x) = finset.card s :=
  sorry

/-- Construct a fintype from a finset with the same elements. -/
def of_finset {α : Type u_1} {p : set α} (s : finset α) (H : ∀ (x : α), x ∈ s ↔ x ∈ p) :
    fintype ↥p :=
  fintype.subtype s H

@[simp] theorem card_of_finset {α : Type u_1} {p : set α} (s : finset α)
    (H : ∀ (x : α), x ∈ s ↔ x ∈ p) : card ↥p = finset.card s :=
  subtype_card s H

theorem card_of_finset' {α : Type u_1} {p : set α} (s : finset α) (H : ∀ (x : α), x ∈ s ↔ x ∈ p)
    [fintype ↥p] : card ↥p = finset.card s :=
  sorry

/-- If `f : α → β` is a bijection and `α` is a fintype, then `β` is also a fintype. -/
def of_bijective {α : Type u_1} {β : Type u_2} [fintype α] (f : α → β) (H : function.bijective f) :
    fintype β :=
  mk (finset.map (function.embedding.mk f sorry) finset.univ) sorry

/-- If `f : α → β` is a surjection and `α` is a fintype, then `β` is also a fintype. -/
def of_surjective {α : Type u_1} {β : Type u_2} [DecidableEq β] [fintype α] (f : α → β)
    (H : function.surjective f) : fintype β :=
  mk (finset.image f finset.univ) sorry

/-- Given an injective function to a fintype, the domain is also a
fintype. This is noncomputable because injectivity alone cannot be
used to construct preimages. -/
def of_injective {α : Type u_1} {β : Type u_2} [fintype β] (f : α → β) (H : function.injective f) :
    fintype α :=
  let _inst : (p : Prop) → Decidable p := classical.dec;
  dite (Nonempty α)
    (fun (hα : Nonempty α) => of_surjective (function.inv_fun f) (function.inv_fun_surjective H))
    fun (hα : ¬Nonempty α) => mk ∅ sorry

/-- If `f : α ≃ β` and `α` is a fintype, then `β` is also a fintype. -/
def of_equiv {β : Type u_2} (α : Type u_1) [fintype α] (f : α ≃ β) : fintype β :=
  of_bijective (⇑f) (equiv.bijective f)

theorem of_equiv_card {α : Type u_1} {β : Type u_2} [fintype α] (f : α ≃ β) : card β = card α :=
  multiset.card_map (⇑(function.embedding.mk (⇑f) (of_bijective._proof_1 (⇑f) (equiv.bijective f))))
    (finset.val finset.univ)

theorem card_congr {α : Type u_1} {β : Type u_2} [fintype α] [fintype β] (f : α ≃ β) :
    card α = card β :=
  sorry

theorem card_eq {α : Type u_1} {β : Type u_2} [F : fintype α] [G : fintype β] :
    card α = card β ↔ Nonempty (α ≃ β) :=
  sorry

/-- Subsingleton types are fintypes (with zero or one terms). -/
def of_subsingleton {α : Type u_1} (a : α) [subsingleton α] : fintype α := mk (singleton a) sorry

@[simp] theorem univ_of_subsingleton {α : Type u_1} (a : α) [subsingleton α] :
    finset.univ = singleton a :=
  rfl

@[simp] theorem card_of_subsingleton {α : Type u_1} (a : α) [subsingleton α] : card α = 1 := rfl

end fintype


namespace set


/-- Construct a finset enumerating a set `s`, given a `fintype` instance.  -/
def to_finset {α : Type u_1} (s : set α) [fintype ↥s] : finset α :=
  finset.mk (multiset.map subtype.val (finset.val finset.univ)) sorry

@[simp] theorem mem_to_finset {α : Type u_1} {s : set α} [fintype ↥s] {a : α} :
    a ∈ to_finset s ↔ a ∈ s :=
  sorry

@[simp] theorem mem_to_finset_val {α : Type u_1} {s : set α} [fintype ↥s] {a : α} :
    a ∈ finset.val (to_finset s) ↔ a ∈ s :=
  mem_to_finset

-- We use an arbitrary `[fintype s]` instance here,

-- not necessarily coming from a `[fintype α]`.

@[simp] theorem to_finset_card {α : Type u_1} (s : set α) [fintype ↥s] :
    finset.card (to_finset s) = fintype.card ↥s :=
  multiset.card_map subtype.val (finset.val finset.univ)

@[simp] theorem coe_to_finset {α : Type u_1} (s : set α) [fintype ↥s] : ↑(to_finset s) = s :=
  ext fun (_x : α) => mem_to_finset

@[simp] theorem to_finset_inj {α : Type u_1} {s : set α} {t : set α} [fintype ↥s] [fintype ↥t] :
    to_finset s = to_finset t ↔ s = t :=
  sorry

end set


theorem finset.card_univ {α : Type u_1} [fintype α] : finset.card finset.univ = fintype.card α :=
  rfl

theorem finset.eq_univ_of_card {α : Type u_1} [fintype α] (s : finset α)
    (hs : finset.card s = fintype.card α) : s = finset.univ :=
  sorry

theorem finset.card_eq_iff_eq_univ {α : Type u_1} [fintype α] (s : finset α) :
    finset.card s = fintype.card α ↔ s = finset.univ :=
  { mp := finset.eq_univ_of_card s,
    mpr := fun (ᾰ : s = finset.univ) => Eq._oldrec finset.card_univ (Eq.symm ᾰ) }

theorem finset.card_le_univ {α : Type u_1} [fintype α] (s : finset α) :
    finset.card s ≤ fintype.card α :=
  finset.card_le_of_subset (finset.subset_univ s)

theorem finset.card_lt_iff_ne_univ {α : Type u_1} [fintype α] (s : finset α) :
    finset.card s < fintype.card α ↔ s ≠ finset.univ :=
  iff.trans (has_le.le.lt_iff_ne (finset.card_le_univ s))
    (not_iff_not_of_iff (finset.card_eq_iff_eq_univ s))

theorem finset.card_compl_lt_iff_nonempty {α : Type u_1} [fintype α] [DecidableEq α]
    (s : finset α) : finset.card (sᶜ) < fintype.card α ↔ finset.nonempty s :=
  iff.trans (finset.card_lt_iff_ne_univ (sᶜ)) (finset.compl_ne_univ_iff_nonempty s)

theorem finset.card_univ_diff {α : Type u_1} [DecidableEq α] [fintype α] (s : finset α) :
    finset.card (finset.univ \ s) = fintype.card α - finset.card s :=
  finset.card_sdiff (finset.subset_univ s)

theorem finset.card_compl {α : Type u_1} [DecidableEq α] [fintype α] (s : finset α) :
    finset.card (sᶜ) = fintype.card α - finset.card s :=
  finset.card_univ_diff s

protected instance fin.fintype (n : ℕ) : fintype (fin n) :=
  fintype.mk (finset.fin_range n) finset.mem_fin_range

theorem fin.univ_def (n : ℕ) : finset.univ = finset.fin_range n := rfl

@[simp] theorem fintype.card_fin (n : ℕ) : fintype.card (fin n) = n := list.length_fin_range n

@[simp] theorem finset.card_fin (n : ℕ) : finset.card finset.univ = n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (finset.card finset.univ = n)) finset.card_univ))
    (eq.mpr (id (Eq._oldrec (Eq.refl (fintype.card (fin n) = n)) (fintype.card_fin n))) (Eq.refl n))

theorem fin.equiv_iff_eq {m : ℕ} {n : ℕ} : Nonempty (fin m ≃ fin n) ↔ m = n := sorry

/-- Embed `fin n` into `fin (n + 1)` by prepending zero to the `univ` -/
theorem fin.univ_succ (n : ℕ) : finset.univ = insert 0 (finset.image fin.succ finset.univ) := sorry

/-- Embed `fin n` into `fin (n + 1)` by appending a new `fin.last n` to the `univ` -/
theorem fin.univ_cast_succ (n : ℕ) :
    finset.univ = insert (fin.last n) (finset.image (⇑fin.cast_succ) finset.univ) :=
  sorry

/-- Embed `fin n` into `fin (n + 1)` by inserting
around a specified pivot `p : fin (n + 1)` into the `univ` -/
theorem fin.univ_succ_above (n : ℕ) (p : fin (n + 1)) :
    finset.univ = insert p (finset.image (⇑(fin.succ_above p)) finset.univ) :=
  sorry

instance unique.fintype {α : Type u_1} [unique α] : fintype α :=
  fintype.of_subsingleton Inhabited.default

@[simp] theorem univ_unique {α : Type u_1} [unique α] [f : fintype α] :
    finset.univ = singleton Inhabited.default :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (finset.univ = singleton Inhabited.default))
        (subsingleton.elim f unique.fintype)))
    (Eq.refl finset.univ)

protected instance empty.fintype : fintype empty := fintype.mk ∅ sorry

@[simp] theorem fintype.univ_empty : finset.univ = ∅ := rfl

@[simp] theorem fintype.card_empty : fintype.card empty = 0 := rfl

protected instance pempty.fintype : fintype pempty := fintype.mk ∅ sorry

@[simp] theorem fintype.univ_pempty : finset.univ = ∅ := rfl

@[simp] theorem fintype.card_pempty : fintype.card pempty = 0 := rfl

protected instance unit.fintype : fintype Unit := fintype.of_subsingleton Unit.unit

theorem fintype.univ_unit : finset.univ = singleton Unit.unit := rfl

theorem fintype.card_unit : fintype.card Unit = 1 := rfl

protected instance punit.fintype : fintype PUnit := fintype.of_subsingleton PUnit.unit

@[simp] theorem fintype.univ_punit : finset.univ = singleton PUnit.unit := rfl

@[simp] theorem fintype.card_punit : fintype.card PUnit = 1 := rfl

protected instance bool.fintype : fintype Bool :=
  fintype.mk (finset.mk (tt ::ₘ false ::ₘ 0) sorry) sorry

@[simp] theorem fintype.univ_bool : finset.univ = insert tt (singleton false) := rfl

protected instance units_int.fintype : fintype (units ℤ) :=
  fintype.mk (insert 1 (singleton (-1))) sorry

protected instance additive.fintype {α : Type u_1} [fintype α] : fintype (additive α) := id

protected instance multiplicative.fintype {α : Type u_1} [fintype α] : fintype (multiplicative α) :=
  id

@[simp] theorem fintype.card_units_int : fintype.card (units ℤ) = bit0 1 := rfl

protected instance units.fintype {α : Type u_1} [monoid α] [fintype α] : fintype (units α) :=
  fintype.of_injective units.val units.ext

@[simp] theorem fintype.card_bool : fintype.card Bool = bit0 1 := rfl

/-- Given a finset on `α`, lift it to being a finset on `option α`
using `option.some` and then insert `option.none`. -/
def finset.insert_none {α : Type u_1} (s : finset α) : finset (Option α) :=
  finset.mk (none ::ₘ multiset.map some (finset.val s)) sorry

@[simp] theorem finset.mem_insert_none {α : Type u_1} {s : finset α} {o : Option α} :
    o ∈ finset.insert_none s ↔ ∀ (a : α), a ∈ o → a ∈ s :=
  sorry

theorem finset.some_mem_insert_none {α : Type u_1} {s : finset α} {a : α} :
    some a ∈ finset.insert_none s ↔ a ∈ s :=
  sorry

protected instance option.fintype {α : Type u_1} [fintype α] : fintype (Option α) :=
  fintype.mk (finset.insert_none finset.univ) sorry

@[simp] theorem fintype.card_option {α : Type u_1} [fintype α] :
    fintype.card (Option α) = fintype.card α + 1 :=
  sorry

protected instance sigma.fintype {α : Type u_1} (β : α → Type u_2) [fintype α]
    [(a : α) → fintype (β a)] : fintype (sigma β) :=
  fintype.mk (finset.sigma finset.univ fun (_x : α) => finset.univ) sorry

@[simp] theorem finset.univ_sigma_univ {α : Type u_1} {β : α → Type u_2} [fintype α]
    [(a : α) → fintype (β a)] :
    (finset.sigma finset.univ fun (a : α) => finset.univ) = finset.univ :=
  rfl

protected instance prod.fintype (α : Type u_1) (β : Type u_2) [fintype α] [fintype β] :
    fintype (α × β) :=
  fintype.mk (finset.product finset.univ finset.univ) sorry

@[simp] theorem finset.univ_product_univ {α : Type u_1} {β : Type u_2} [fintype α] [fintype β] :
    finset.product finset.univ finset.univ = finset.univ :=
  rfl

@[simp] theorem fintype.card_prod (α : Type u_1) (β : Type u_2) [fintype α] [fintype β] :
    fintype.card (α × β) = fintype.card α * fintype.card β :=
  finset.card_product finset.univ finset.univ

/-- Given that `α × β` is a fintype, `α` is also a fintype. -/
def fintype.fintype_prod_left {α : Type u_1} {β : Type u_2} [DecidableEq α] [fintype (α × β)]
    [Nonempty β] : fintype α :=
  fintype.mk (finset.image prod.fst (fintype.elems (α × β))) sorry

/-- Given that `α × β` is a fintype, `β` is also a fintype. -/
def fintype.fintype_prod_right {α : Type u_1} {β : Type u_2} [DecidableEq β] [fintype (α × β)]
    [Nonempty α] : fintype β :=
  fintype.mk (finset.image prod.snd (fintype.elems (α × β))) sorry

protected instance ulift.fintype (α : Type u_1) [fintype α] : fintype (ulift α) :=
  fintype.of_equiv α (equiv.symm equiv.ulift)

@[simp] theorem fintype.card_ulift (α : Type u_1) [fintype α] :
    fintype.card (ulift α) = fintype.card α :=
  fintype.of_equiv_card (equiv.symm equiv.ulift)

theorem univ_sum_type {α : Type u_1} {β : Type u_2} [fintype α] [fintype β] [fintype (α ⊕ β)]
    [DecidableEq (α ⊕ β)] :
    finset.univ =
        finset.map function.embedding.inl finset.univ ∪
          finset.map function.embedding.inr finset.univ :=
  sorry

protected instance sum.fintype (α : Type u) (β : Type v) [fintype α] [fintype β] :
    fintype (α ⊕ β) :=
  fintype.of_equiv (sigma fun (b : Bool) => cond b (ulift α) (ulift β))
    (equiv.trans (equiv.symm (equiv.sum_equiv_sigma_bool (ulift α) (ulift β)))
      (equiv.sum_congr equiv.ulift equiv.ulift))

namespace fintype


theorem card_le_of_injective {α : Type u_1} {β : Type u_2} [fintype α] [fintype β] (f : α → β)
    (hf : function.injective f) : card α ≤ card β :=
  finset.card_le_card_of_inj_on f (fun (_x : α) (_x_1 : _x ∈ finset.univ) => finset.mem_univ (f _x))
    fun (_x : α) (_x_1 : _x ∈ finset.univ) (_x_2 : α) (_x_3 : _x_2 ∈ finset.univ)
      (h : f _x = f _x_2) => hf h

/--
The pigeonhole principle for finitely many pigeons and pigeonholes.
This is the `fintype` version of `finset.exists_ne_map_eq_of_card_lt_of_maps_to`.
-/
theorem exists_ne_map_eq_of_card_lt {α : Type u_1} {β : Type u_2} [fintype α] [fintype β]
    (f : α → β) (h : card β < card α) : ∃ (x : α), ∃ (y : α), x ≠ y ∧ f x = f y :=
  sorry

theorem card_eq_one_iff {α : Type u_1} [fintype α] : card α = 1 ↔ ∃ (x : α), ∀ (y : α), y = x :=
  sorry

theorem card_eq_zero_iff {α : Type u_1} [fintype α] : card α = 0 ↔ α → False := sorry

/-- A `fintype` with cardinality zero is (constructively) equivalent to `pempty`. -/
def card_eq_zero_equiv_equiv_pempty {α : Type u_1} [fintype α] : card α = 0 ≃ (α ≃ pempty) :=
  equiv.mk
    (fun (h : card α = 0) =>
      equiv.mk (fun (a : α) => false.elim sorry) (fun (a : pempty) => pempty.elim a) sorry sorry)
    sorry sorry sorry

theorem card_pos_iff {α : Type u_1} [fintype α] : 0 < card α ↔ Nonempty α := sorry

theorem card_le_one_iff {α : Type u_1} [fintype α] : card α ≤ 1 ↔ ∀ (a b : α), a = b := sorry

theorem card_le_one_iff_subsingleton {α : Type u_1} [fintype α] : card α ≤ 1 ↔ subsingleton α :=
  iff.trans card_le_one_iff (iff.symm subsingleton_iff)

theorem one_lt_card_iff_nontrivial {α : Type u_1} [fintype α] : 1 < card α ↔ nontrivial α := sorry

theorem exists_ne_of_one_lt_card {α : Type u_1} [fintype α] (h : 1 < card α) (a : α) :
    ∃ (b : α), b ≠ a :=
  exists_ne a

theorem exists_pair_of_one_lt_card {α : Type u_1} [fintype α] (h : 1 < card α) :
    ∃ (a : α), ∃ (b : α), a ≠ b :=
  exists_pair_ne α

theorem card_eq_one_of_forall_eq {α : Type u_1} [fintype α] {i : α} (h : ∀ (j : α), j = i) :
    card α = 1 :=
  le_antisymm (iff.mpr card_le_one_iff fun (a b : α) => Eq.trans (h a) (Eq.symm (h b)))
    (iff.mpr finset.card_pos (Exists.intro i (finset.mem_univ i)))

theorem injective_iff_surjective {α : Type u_1} [fintype α] {f : α → α} :
    function.injective f ↔ function.surjective f :=
  sorry

theorem injective_iff_bijective {α : Type u_1} [fintype α] {f : α → α} :
    function.injective f ↔ function.bijective f :=
  sorry

theorem surjective_iff_bijective {α : Type u_1} [fintype α] {f : α → α} :
    function.surjective f ↔ function.bijective f :=
  sorry

theorem injective_iff_surjective_of_equiv {α : Type u_1} [fintype α] {β : Type u_2} {f : α → β}
    (e : α ≃ β) : function.injective f ↔ function.surjective f :=
  sorry

theorem nonempty_equiv_of_card_eq {α : Type u_1} {β : Type u_2} [fintype α] [fintype β]
    (h : card α = card β) : Nonempty (α ≃ β) :=
  sorry

theorem bijective_iff_injective_and_card {α : Type u_1} {β : Type u_2} [fintype α] [fintype β]
    (f : α → β) : function.bijective f ↔ function.injective f ∧ card α = card β :=
  sorry

theorem bijective_iff_surjective_and_card {α : Type u_1} {β : Type u_2} [fintype α] [fintype β]
    (f : α → β) : function.bijective f ↔ function.surjective f ∧ card α = card β :=
  sorry

end fintype


theorem fintype.coe_image_univ {α : Type u_1} {β : Type u_2} [fintype α] [DecidableEq β]
    {f : α → β} : ↑(finset.image f finset.univ) = set.range f :=
  sorry

protected instance list.subtype.fintype {α : Type u_1} [DecidableEq α] (l : List α) :
    fintype (Subtype fun (x : α) => x ∈ l) :=
  fintype.of_list (list.attach l) (list.mem_attach l)

protected instance multiset.subtype.fintype {α : Type u_1} [DecidableEq α] (s : multiset α) :
    fintype (Subtype fun (x : α) => x ∈ s) :=
  fintype.of_multiset (multiset.attach s) (multiset.mem_attach s)

protected instance finset.subtype.fintype {α : Type u_1} (s : finset α) :
    fintype (Subtype fun (x : α) => x ∈ s) :=
  fintype.mk (finset.attach s) (finset.mem_attach s)

protected instance finset_coe.fintype {α : Type u_1} (s : finset α) : fintype ↥↑s :=
  finset.subtype.fintype s

@[simp] theorem fintype.card_coe {α : Type u_1} (s : finset α) : fintype.card ↥↑s = finset.card s :=
  finset.card_attach

theorem finset.attach_eq_univ {α : Type u_1} {s : finset α} : finset.attach s = finset.univ := rfl

theorem finset.card_le_one_iff {α : Type u_1} {s : finset α} :
    finset.card s ≤ 1 ↔ ∀ {x y : α}, x ∈ s → y ∈ s → x = y :=
  sorry

/-- A `finset` of a subsingleton type has cardinality at most one. -/
theorem finset.card_le_one_of_subsingleton {α : Type u_1} [subsingleton α] (s : finset α) :
    finset.card s ≤ 1 :=
  iff.mpr finset.card_le_one_iff
    fun (_x _x_1 : α) (_x_2 : _x ∈ s) (_x_3 : _x_1 ∈ s) => subsingleton.elim _x _x_1

theorem finset.one_lt_card_iff {α : Type u_1} {s : finset α} :
    1 < finset.card s ↔ ∃ (x : α), ∃ (y : α), x ∈ s ∧ y ∈ s ∧ x ≠ y :=
  sorry

protected instance plift.fintype (p : Prop) [Decidable p] : fintype (plift p) :=
  fintype.mk (dite p (fun (h : p) => singleton (plift.up h)) fun (h : ¬p) => ∅) sorry

protected instance Prop.fintype : fintype Prop :=
  fintype.mk (finset.mk (True ::ₘ False ::ₘ 0) sorry) sorry

protected instance subtype.fintype {α : Type u_1} (p : α → Prop) [decidable_pred p] [fintype α] :
    fintype (Subtype fun (x : α) => p x) :=
  fintype.subtype (finset.filter p finset.univ) sorry

/-- A set on a fintype, when coerced to a type, is a fintype. -/
def set_fintype {α : Type u_1} [fintype α] (s : set α) [decidable_pred s] : fintype ↥s :=
  subtype.fintype fun (x : α) => x ∈ s

namespace function.embedding


/-- An embedding from a `fintype` to itself can be promoted to an equivalence. -/
def equiv_of_fintype_self_embedding {α : Type u_1} [fintype α] (e : α ↪ α) : α ≃ α :=
  equiv.of_bijective ⇑e sorry

@[simp] theorem equiv_of_fintype_self_embedding_to_embedding {α : Type u_1} [fintype α]
    (e : α ↪ α) : equiv.to_embedding (equiv_of_fintype_self_embedding e) = e :=
  ext fun (x : α) => Eq.refl (coe_fn (equiv.to_embedding (equiv_of_fintype_self_embedding e)) x)

end function.embedding


@[simp] theorem finset.univ_map_embedding {α : Type u_1} [fintype α] (e : α ↪ α) :
    finset.map e finset.univ = finset.univ :=
  sorry

namespace fintype


/-- Given for all `a : α` a finset `t a` of `δ a`, then one can define the
finset `fintype.pi_finset t` of all functions taking values in `t a` for all `a`. This is the
analogue of `finset.pi` where the base finset is `univ` (but formally they are not the same, as
there is an additional condition `i ∈ finset.univ` in the `finset.pi` definition). -/
def pi_finset {α : Type u_1} [DecidableEq α] [fintype α] {δ : α → Type u_4}
    (t : (a : α) → finset (δ a)) : finset ((a : α) → δ a) :=
  finset.map
    (function.embedding.mk
      (fun (f : (a : α) → a ∈ finset.univ → δ a) (a : α) => f a (finset.mem_univ a)) sorry)
    (finset.pi finset.univ t)

@[simp] theorem mem_pi_finset {α : Type u_1} [DecidableEq α] [fintype α] {δ : α → Type u_4}
    {t : (a : α) → finset (δ a)} {f : (a : α) → δ a} : f ∈ pi_finset t ↔ ∀ (a : α), f a ∈ t a :=
  sorry

theorem pi_finset_subset {α : Type u_1} [DecidableEq α] [fintype α] {δ : α → Type u_4}
    (t₁ : (a : α) → finset (δ a)) (t₂ : (a : α) → finset (δ a)) (h : ∀ (a : α), t₁ a ⊆ t₂ a) :
    pi_finset t₁ ⊆ pi_finset t₂ :=
  fun (g : (a : α) → δ a) (hg : g ∈ pi_finset t₁) =>
    iff.mpr mem_pi_finset fun (a : α) => h a (iff.mp mem_pi_finset hg a)

theorem pi_finset_disjoint_of_disjoint {α : Type u_1} [DecidableEq α] [fintype α] {δ : α → Type u_4}
    [(a : α) → DecidableEq (δ a)] (t₁ : (a : α) → finset (δ a)) (t₂ : (a : α) → finset (δ a))
    {a : α} (h : disjoint (t₁ a) (t₂ a)) : disjoint (pi_finset t₁) (pi_finset t₂) :=
  sorry

end fintype


/-! ### pi -/

/-- A dependent product of fintypes, indexed by a fintype, is a fintype. -/
protected instance pi.fintype {α : Type u_1} {β : α → Type u_2} [DecidableEq α] [fintype α]
    [(a : α) → fintype (β a)] : fintype ((a : α) → β a) :=
  fintype.mk (fintype.pi_finset fun (_x : α) => finset.univ) sorry

@[simp] theorem fintype.pi_finset_univ {α : Type u_1} {β : α → Type u_2} [DecidableEq α] [fintype α]
    [(a : α) → fintype (β a)] : (fintype.pi_finset fun (a : α) => finset.univ) = finset.univ :=
  rfl

protected instance d_array.fintype {n : ℕ} {α : fin n → Type u_1} [(n : fin n) → fintype (α n)] :
    fintype (d_array n α) :=
  fintype.of_equiv ((i : fin n) → α i) (equiv.symm (equiv.d_array_equiv_fin α))

protected instance array.fintype {n : ℕ} {α : Type u_1} [fintype α] : fintype (array n α) :=
  d_array.fintype

protected instance vector.fintype {α : Type u_1} [fintype α] {n : ℕ} : fintype (vector α n) :=
  fintype.of_equiv (fin n → α) (equiv.symm (equiv.vector_equiv_fin α n))

protected instance quotient.fintype {α : Type u_1} [fintype α] (s : setoid α)
    [DecidableRel has_equiv.equiv] : fintype (quotient s) :=
  fintype.of_surjective quotient.mk sorry

protected instance finset.fintype {α : Type u_1} [fintype α] : fintype (finset α) :=
  fintype.mk (finset.powerset finset.univ) sorry

@[simp] theorem fintype.card_finset {α : Type u_1} [fintype α] :
    fintype.card (finset α) = bit0 1 ^ fintype.card α :=
  finset.card_powerset finset.univ

@[simp] theorem set.to_finset_univ {α : Type u_1} [fintype α] :
    set.to_finset set.univ = finset.univ :=
  sorry

@[simp] theorem set.to_finset_empty {α : Type u_1} [fintype α] : set.to_finset ∅ = ∅ := sorry

theorem fintype.card_subtype_le {α : Type u_1} [fintype α] (p : α → Prop) [decidable_pred p] :
    fintype.card (Subtype fun (x : α) => p x) ≤ fintype.card α :=
  sorry

theorem fintype.card_subtype_lt {α : Type u_1} [fintype α] {p : α → Prop} [decidable_pred p] {x : α}
    (hx : ¬p x) : fintype.card (Subtype fun (x : α) => p x) < fintype.card α :=
  sorry

protected instance psigma.fintype {α : Type u_1} {β : α → Type u_2} [fintype α]
    [(a : α) → fintype (β a)] : fintype (psigma fun (a : α) => β a) :=
  fintype.of_equiv (sigma fun (a : α) => β a)
    (equiv.symm (equiv.psigma_equiv_sigma fun (a : α) => β a))

protected instance psigma.fintype_prop_left {α : Prop} {β : α → Type u_1} [Decidable α]
    [(a : α) → fintype (β a)] : fintype (psigma fun (a : α) => β a) :=
  dite α
    (fun (h : α) =>
      fintype.of_equiv (β h) (equiv.mk (fun (x : β h) => psigma.mk h x) psigma.snd sorry sorry))
    fun (h : ¬α) => fintype.mk ∅ sorry

protected instance psigma.fintype_prop_right {α : Type u_1} {β : α → Prop}
    [(a : α) → Decidable (β a)] [fintype α] : fintype (psigma fun (a : α) => β a) :=
  fintype.of_equiv (Subtype fun (a : α) => β a)
    (equiv.mk (fun (_x : Subtype fun (a : α) => β a) => sorry)
      (fun (_x : psigma fun (a : α) => β a) => sorry) sorry sorry)

protected instance psigma.fintype_prop_prop {α : Prop} {β : α → Prop} [Decidable α]
    [(a : α) → Decidable (β a)] : fintype (psigma fun (a : α) => β a) :=
  dite (∃ (a : α), β a)
    (fun (h : ∃ (a : α), β a) => fintype.mk (singleton (psigma.mk sorry sorry)) sorry)
    fun (h : ¬∃ (a : α), β a) => fintype.mk ∅ sorry

protected instance set.fintype {α : Type u_1} [fintype α] : fintype (set α) :=
  fintype.mk
    (finset.map (function.embedding.mk coe finset.coe_injective) (finset.powerset finset.univ))
    sorry

protected instance pfun_fintype (p : Prop) [Decidable p] (α : p → Type u_1)
    [(hp : p) → fintype (α hp)] : fintype ((hp : p) → α hp) :=
  dite p
    (fun (hp : p) =>
      fintype.of_equiv (α hp)
        (equiv.mk (fun (a : α hp) (_x : p) => a) (fun (f : (hp : p) → α hp) => f hp) sorry sorry))
    fun (hp : ¬p) => fintype.mk (singleton fun (h : p) => false.elim (hp h)) sorry

@[simp] theorem finset.univ_pi_univ {α : Type u_1} {β : α → Type u_2} [DecidableEq α] [fintype α]
    [(a : α) → fintype (β a)] : (finset.pi finset.univ fun (a : α) => finset.univ) = finset.univ :=
  sorry

theorem mem_image_univ_iff_mem_range {α : Type u_1} {β : Type u_2} [fintype α] [DecidableEq β]
    {f : α → β} {b : β} : b ∈ finset.image f finset.univ ↔ b ∈ set.range f :=
  sorry

theorem card_lt_card_of_injective_of_not_mem {α : Type u_1} {β : Type u_2} [fintype α] [fintype β]
    (f : α → β) (h : function.injective f) {b : β} (w : ¬b ∈ set.range f) :
    fintype.card α < fintype.card β :=
  sorry

/-- An auxiliary function for `quotient.fin_choice`.  Given a
collection of setoids indexed by a type `ι`, a (finite) list `l` of
indices, and a function that for each `i ∈ l` gives a term of the
corresponding quotient type, then there is a corresponding term in the
quotient of the product of the setoids indexed by `l`. -/
def quotient.fin_choice_aux {ι : Type u_1} [DecidableEq ι] {α : ι → Type u_2}
    [S : (i : ι) → setoid (α i)] (l : List ι) :
    ((i : ι) → i ∈ l → quotient (S i)) → quotient Mathlib.pi_setoid :=
  sorry

theorem quotient.fin_choice_aux_eq {ι : Type u_1} [DecidableEq ι] {α : ι → Type u_2}
    [S : (i : ι) → setoid (α i)] (l : List ι) (f : (i : ι) → i ∈ l → α i) :
    (quotient.fin_choice_aux l fun (i : ι) (h : i ∈ l) => quotient.mk (f i h)) = quotient.mk f :=
  sorry

/-- Given a collection of setoids indexed by a fintype `ι` and a
function that for each `i : ι` gives a term of the corresponding
quotient type, then there is corresponding term in the quotient of the
product of the setoids. -/
def quotient.fin_choice {ι : Type u_1} [DecidableEq ι] [fintype ι] {α : ι → Type u_2}
    [S : (i : ι) → setoid (α i)] (f : (i : ι) → quotient (S i)) : quotient Mathlib.pi_setoid :=
  quotient.lift_on
    (quotient.rec_on (finset.val finset.univ)
      (fun (l : List ι) => quotient.fin_choice_aux l fun (i : ι) (_x : i ∈ l) => f i) sorry)
    (fun (f : (i : ι) → i ∈ finset.val finset.univ → α i) =>
      quotient.mk fun (i : ι) => f i (finset.mem_univ i))
    sorry

theorem quotient.fin_choice_eq {ι : Type u_1} [DecidableEq ι] [fintype ι] {α : ι → Type u_2}
    [(i : ι) → setoid (α i)] (f : (i : ι) → α i) :
    (quotient.fin_choice fun (i : ι) => quotient.mk (f i)) = quotient.mk f :=
  sorry

/-- Given a list, produce a list of all permutations of its elements. -/
def perms_of_list {α : Type u_1} [DecidableEq α] : List α → List (equiv.perm α) := sorry

theorem length_perms_of_list {α : Type u_1} [DecidableEq α] (l : List α) :
    list.length (perms_of_list l) = nat.factorial (list.length l) :=
  sorry

theorem mem_perms_of_list_of_mem {α : Type u_1} [DecidableEq α] {l : List α} {f : equiv.perm α}
    (h : ∀ (x : α), coe_fn f x ≠ x → x ∈ l) : f ∈ perms_of_list l :=
  sorry

theorem mem_of_mem_perms_of_list {α : Type u_1} [DecidableEq α] {l : List α} {f : equiv.perm α} :
    f ∈ perms_of_list l → ∀ {x : α}, coe_fn f x ≠ x → x ∈ l :=
  sorry

theorem mem_perms_of_list_iff {α : Type u_1} [DecidableEq α] {l : List α} {f : equiv.perm α} :
    f ∈ perms_of_list l ↔ ∀ {x : α}, coe_fn f x ≠ x → x ∈ l :=
  { mp := mem_of_mem_perms_of_list, mpr := mem_perms_of_list_of_mem }

theorem nodup_perms_of_list {α : Type u_1} [DecidableEq α] {l : List α} (hl : list.nodup l) :
    list.nodup (perms_of_list l) :=
  sorry

/-- Given a finset, produce the finset of all permutations of its elements. -/
def perms_of_finset {α : Type u_1} [DecidableEq α] (s : finset α) : finset (equiv.perm α) :=
  quotient.hrec_on (finset.val s)
    (fun (l : List α) (hl : multiset.nodup (quotient.mk l)) => finset.mk ↑(perms_of_list l) sorry)
    sorry (finset.nodup s)

theorem mem_perms_of_finset_iff {α : Type u_1} [DecidableEq α] {s : finset α} {f : equiv.perm α} :
    f ∈ perms_of_finset s ↔ ∀ {x : α}, coe_fn f x ≠ x → x ∈ s :=
  finset.cases_on s
    fun (s_val : multiset α) (hs : multiset.nodup s_val) =>
      quot.induction_on s_val
        (fun (l : List α) (hs : multiset.nodup (Quot.mk setoid.r l)) => mem_perms_of_list_iff) hs

theorem card_perms_of_finset {α : Type u_1} [DecidableEq α] (s : finset α) :
    finset.card (perms_of_finset s) = nat.factorial (finset.card s) :=
  finset.cases_on s
    fun (s_val : multiset α) (hs : multiset.nodup s_val) =>
      quot.induction_on s_val
        (fun (l : List α) (hs : multiset.nodup (Quot.mk setoid.r l)) => length_perms_of_list l) hs

/-- The collection of permutations of a fintype is a fintype. -/
def fintype_perm {α : Type u_1} [DecidableEq α] [fintype α] : fintype (equiv.perm α) :=
  fintype.mk (perms_of_finset finset.univ) sorry

protected instance equiv.fintype {α : Type u_1} {β : Type u_2} [DecidableEq α] [DecidableEq β]
    [fintype α] [fintype β] : fintype (α ≃ β) :=
  dite (fintype.card β = fintype.card α)
    (fun (h : fintype.card β = fintype.card α) =>
      trunc.rec_on_subsingleton (fintype.equiv_fin α)
        fun (eα : α ≃ fin (fintype.card α)) =>
          trunc.rec_on_subsingleton (fintype.equiv_fin β)
            fun (eβ : β ≃ fin (fintype.card β)) =>
              fintype.of_equiv (equiv.perm α)
                (equiv.equiv_congr (equiv.refl α) (equiv.trans eα (eq.rec_on h (equiv.symm eβ)))))
    fun (h : ¬fintype.card β = fintype.card α) => fintype.mk ∅ sorry

theorem fintype.card_perm {α : Type u_1} [DecidableEq α] [fintype α] :
    fintype.card (equiv.perm α) = nat.factorial (fintype.card α) :=
  subsingleton.elim fintype_perm equiv.fintype ▸ card_perms_of_finset finset.univ

theorem fintype.card_equiv {α : Type u_1} {β : Type u_2} [DecidableEq α] [DecidableEq β] [fintype α]
    [fintype β] (e : α ≃ β) : fintype.card (α ≃ β) = nat.factorial (fintype.card α) :=
  fintype.card_congr (equiv.equiv_congr (equiv.refl α) e) ▸ fintype.card_perm

theorem univ_eq_singleton_of_card_one {α : Type u_1} [fintype α] (x : α) (h : fintype.card α = 1) :
    finset.univ = singleton x :=
  sorry

namespace fintype


/-- Given a fintype `α` and a predicate `p`, associate to a proof that there is a unique element of
`α` satisfying `p` this unique element, as an element of the corresponding subtype. -/
def choose_x {α : Type u_1} [fintype α] (p : α → Prop) [decidable_pred p]
    (hp : exists_unique fun (a : α) => p a) : Subtype fun (a : α) => p a :=
  { val := finset.choose p finset.univ sorry, property := sorry }

/-- Given a fintype `α` and a predicate `p`, associate to a proof that there is a unique element of
`α` satisfying `p` this unique element, as an element of `α`. -/
def choose {α : Type u_1} [fintype α] (p : α → Prop) [decidable_pred p]
    (hp : exists_unique fun (a : α) => p a) : α :=
  ↑(choose_x p hp)

theorem choose_spec {α : Type u_1} [fintype α] (p : α → Prop) [decidable_pred p]
    (hp : exists_unique fun (a : α) => p a) : p (choose p hp) :=
  subtype.property (choose_x p hp)

/-- `
`bij_inv f` is the unique inverse to a bijection `f`. This acts
  as a computable alternative to `function.inv_fun`. -/
def bij_inv {α : Type u_1} {β : Type u_2} [fintype α] [DecidableEq β] {f : α → β}
    (f_bij : function.bijective f) (b : β) : α :=
  choose (fun (a : α) => f a = b) sorry

theorem left_inverse_bij_inv {α : Type u_1} {β : Type u_2} [fintype α] [DecidableEq β] {f : α → β}
    (f_bij : function.bijective f) : function.left_inverse (bij_inv f_bij) f :=
  fun (a : α) =>
    and.left f_bij (bij_inv f_bij (f a)) a
      (choose_spec (fun (a' : α) => f a' = f a) (bij_inv._proof_1 f_bij (f a)))

theorem right_inverse_bij_inv {α : Type u_1} {β : Type u_2} [fintype α] [DecidableEq β] {f : α → β}
    (f_bij : function.bijective f) : function.right_inverse (bij_inv f_bij) f :=
  fun (b : β) => choose_spec (fun (a' : α) => f a' = b) (bij_inv._proof_1 f_bij b)

theorem bijective_bij_inv {α : Type u_1} {β : Type u_2} [fintype α] [DecidableEq β] {f : α → β}
    (f_bij : function.bijective f) : function.bijective (bij_inv f_bij) :=
  { left := function.right_inverse.injective (right_inverse_bij_inv f_bij),
    right := function.left_inverse.surjective (left_inverse_bij_inv f_bij) }

theorem well_founded_of_trans_of_irrefl {α : Type u_1} [fintype α] (r : α → α → Prop) [is_trans α r]
    [is_irrefl α r] : well_founded r :=
  sorry

theorem preorder.well_founded {α : Type u_1} [fintype α] [preorder α] : well_founded Less :=
  well_founded_of_trans_of_irrefl Less

instance linear_order.is_well_order {α : Type u_1} [fintype α] [linear_order α] :
    is_well_order α Less :=
  is_well_order.mk preorder.well_founded

end fintype


/-- A type is said to be infinite if it has no fintype instance. -/
class infinite (α : Type u_4) where
  not_fintype : fintype α → False

@[simp] theorem not_nonempty_fintype {α : Type u_1} : ¬Nonempty (fintype α) ↔ infinite α := sorry

theorem finset.exists_minimal {α : Type u_1} [preorder α] (s : finset α) (h : finset.nonempty s) :
    ∃ (m : α), ∃ (H : m ∈ s), ∀ (x : α), x ∈ s → ¬x < m :=
  sorry

theorem finset.exists_maximal {α : Type u_1} [preorder α] (s : finset α) (h : finset.nonempty s) :
    ∃ (m : α), ∃ (H : m ∈ s), ∀ (x : α), x ∈ s → ¬m < x :=
  finset.exists_minimal s h

namespace infinite


theorem exists_not_mem_finset {α : Type u_1} [infinite α] (s : finset α) : ∃ (x : α), ¬x ∈ s :=
  iff.mp not_forall fun (h : ∀ (x : α), x ∈ s) => not_fintype (fintype.mk s h)

protected instance nontrivial (α : Type u_1) [H : infinite α] : nontrivial α := nontrivial.mk sorry

theorem nonempty (α : Type u_1) [infinite α] : Nonempty α := nontrivial.to_nonempty

theorem of_injective {α : Type u_1} {β : Type u_2} [infinite β] (f : β → α)
    (hf : function.injective f) : infinite α :=
  mk fun (I : fintype α) => not_fintype (fintype.of_injective f hf)

theorem of_surjective {α : Type u_1} {β : Type u_2} [infinite β] (f : α → β)
    (hf : function.surjective f) : infinite α :=
  mk fun (I : fintype α) => not_fintype (fintype.of_surjective f hf)

/-- Embedding of `ℕ` into an infinite type. -/
def nat_embedding (α : Type u_1) [infinite α] : ℕ ↪ α :=
  function.embedding.mk (nat_embedding_aux α) (nat_embedding_aux_injective α)

theorem exists_subset_card_eq (α : Type u_1) [infinite α] (n : ℕ) :
    ∃ (s : finset α), finset.card s = n :=
  sorry

end infinite


theorem not_injective_infinite_fintype {α : Type u_1} {β : Type u_2} [infinite α] [fintype β]
    (f : α → β) : ¬function.injective f :=
  fun (hf : function.injective f) =>
    (fun (H : fintype α) => infinite.not_fintype H) (fintype.of_injective f hf)

/--
The pigeonhole principle for infinitely many pigeons in finitely many
pigeonholes.  If there are infinitely many pigeons in finitely many
pigeonholes, then there are at least two pigeons in the same
pigeonhole.

See also: `fintype.exists_ne_map_eq_of_card_lt`, `fintype.exists_infinite_fiber`.
-/
theorem fintype.exists_ne_map_eq_of_infinite {α : Type u_1} {β : Type u_2} [infinite α] [fintype β]
    (f : α → β) : ∃ (x : α), ∃ (y : α), x ≠ y ∧ f x = f y :=
  sorry

/--
The strong pigeonhole principle for infinitely many pigeons in
finitely many pigeonholes.  If there are infinitely many pigeons in
finitely many pigeonholes, then there is a pigeonhole with infinitely
many pigeons.

See also: `fintype.exists_ne_map_eq_of_infinite`
-/
theorem fintype.exists_infinite_fiber {α : Type u_1} {β : Type u_2} [infinite α] [fintype β]
    (f : α → β) : ∃ (y : β), infinite ↥(f ⁻¹' singleton y) :=
  sorry

theorem not_surjective_fintype_infinite {α : Type u_1} {β : Type u_2} [fintype α] [infinite β]
    (f : α → β) : ¬function.surjective f :=
  fun (hf : function.surjective f) =>
    (fun (H : infinite α) => infinite.not_fintype infer_instance) (infinite.of_surjective f hf)

protected instance nat.infinite : infinite ℕ := infinite.mk fun (_x : fintype ℕ) => sorry

protected instance int.infinite : infinite ℤ :=
  infinite.of_injective Int.ofNat fun (_x _x_1 : ℕ) => int.of_nat.inj

/--
For `s : multiset α`, we can lift the existential statement that `∃ x, x ∈ s` to a `trunc α`.
-/
def trunc_of_multiset_exists_mem {α : Type u_1} (s : multiset α) : (∃ (x : α), x ∈ s) → trunc α :=
  quotient.rec_on_subsingleton s fun (l : List α) (h : ∃ (x : α), x ∈ quotient.mk l) => sorry

/--
A `nonempty` `fintype` constructively contains an element.
-/
def trunc_of_nonempty_fintype (α : Type u_1) [Nonempty α] [fintype α] : trunc α :=
  trunc_of_multiset_exists_mem (finset.val finset.univ) sorry

/--
A `fintype` with positive cardinality constructively contains an element.
-/
def trunc_of_card_pos {α : Type u_1} [fintype α] (h : 0 < fintype.card α) : trunc α :=
  let _inst : Nonempty α := sorry;
  trunc_of_nonempty_fintype α

/--
By iterating over the elements of a fintype, we can lift an existential statement `∃ a, P a`
to `trunc (Σ' a, P a)`, containing data.
-/
def trunc_sigma_of_exists {α : Type u_1} [fintype α] {P : α → Prop} [decidable_pred P]
    (h : ∃ (a : α), P a) : trunc (psigma fun (a : α) => P a) :=
  trunc_of_nonempty_fintype (psigma fun (a : α) => P a)

end Mathlib