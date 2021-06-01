/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.set_theory.cardinal
import Mathlib.PostPort

universes u_4 u_5 l u_1 u_2 u_3 u v w 

namespace Mathlib

/-!
# Ordinals

Ordinals are defined as equivalences of well-ordered sets under order isomorphism. They are endowed
with a total order, where an ordinal is smaller than another one if it embeds into it as an
initial segment (or, equivalently, in any way). This total order is well founded.

## Main definitions

* `initial_seg r s`: type of order embeddings of `r` into `s` for which the range is an initial
  segment (i.e., if `b` belongs to the range, then any `b' < b` also belongs to the range).
  It is denoted by `r ≼i s`.
* `principal_seg r s`: Type of order embeddings of `r` into `s` for which the range is a principal
  segment, i.e., an interval of the form `(-∞, top)` for some element `top`. It is denoted by
  `r ≺i s`.

* `ordinal`: the type of ordinals (in a given universe)
* `type r`: given a well-founded order `r`, this is the corresponding ordinal
* `typein r a`: given a well-founded order `r` on a type `α`, and `a : α`, the ordinal
  corresponding to all elements smaller than `a`.
* `enum r o h`: given a well-order `r` on a type `α`, and an ordinal `o` strictly smaller than
  the ordinal corresponding to `r` (this is the assumption `h`), returns the `o`-th element of `α`.
  In other words, the elements of `α` can be enumerated using ordinals up to `type r`.
* `card o`: the cardinality of an ordinal `o`.
* `lift` lifts an ordinal in universe `u` to an ordinal in universe `max u v`. For a version
  registering additionally that this is an initial segment embedding, see `lift.initial_seg`. For
  a version regiserting that it is a principal segment embedding if `u < v`, see
  `lift.principal_seg`.
* `omega` is the first infinite ordinal. It is the order type of `ℕ`.

* `o₁ + o₂` is the order on the disjoint union of `o₁` and `o₂` obtained by declaring that
  every element of `o₁` is smaller than every element of `o₂`. The main properties of addition
  (and the other operations on ordinals) are stated and proved in `ordinal_arithmetic.lean`. Here,
  we only introduce it and prove its basic properties to deduce the fact that the order on ordinals
  is total (and well founded).
* `succ o` is the successor of the ordinal `o`.

* `min`: the minimal element of a nonempty indexed family of ordinals
* `omin` : the minimal element of a nonempty set of ordinals

* `ord c`: when `c` is a cardinal, `ord c` is the smallest ordinal with this cardinality. It is
  the canonical way to represent a cardinal with an ordinal.

## Notations
* `r ≼i s`: the type of initial segment embeddings of `r` into `s`.
* `r ≺i s`: the type of principal segment embeddings of `r` into `s`.
* `ω` is a notation for the first infinite ordinal in the locale ordinal.
-/

/-!
### Initial segments

Order embeddings whose range is an initial segment of `s` (i.e., if `b` belongs to the range, then
any `b' < b` also belongs to the range). The type of these embeddings from `r` to `s` is called
`initial_seg r s`, and denoted by `r ≼i s`.
-/

/-- If `r` is a relation on `α` and `s` in a relation on `β`, then `f : r ≼i s` is an order
embedding whose range is an initial segment. That is, whenever `b < f a` in `β` then `b` is in the
range of `f`. -/
structure initial_seg {α : Type u_4} {β : Type u_5} (r : α → α → Prop) (s : β → β → Prop)
    extends r ↪r s where
  init :
    ∀ (a : α) (b : β),
      s b (coe_fn _to_rel_embedding a) → ∃ (a' : α), coe_fn _to_rel_embedding a' = b

namespace initial_seg


protected instance rel_embedding.has_coe {α : Type u_1} {β : Type u_2} {r : α → α → Prop}
    {s : β → β → Prop} : has_coe (initial_seg r s) (r ↪r s) :=
  has_coe.mk to_rel_embedding

protected instance has_coe_to_fun {α : Type u_1} {β : Type u_2} {r : α → α → Prop}
    {s : β → β → Prop} : has_coe_to_fun (initial_seg r s) :=
  has_coe_to_fun.mk (fun (_x : initial_seg r s) => α → β)
    fun (f : initial_seg r s) (x : α) => coe_fn (↑f) x

@[simp] theorem coe_fn_mk {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop}
    (f : r ↪r s) (o : ∀ (a : α) (b : β), s b (coe_fn f a) → ∃ (a' : α), coe_fn f a' = b) :
    ⇑(mk f o) = ⇑f :=
  rfl

@[simp] theorem coe_fn_to_rel_embedding {α : Type u_1} {β : Type u_2} {r : α → α → Prop}
    {s : β → β → Prop} (f : initial_seg r s) : ⇑(to_rel_embedding f) = ⇑f :=
  rfl

@[simp] theorem coe_coe_fn {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop}
    (f : initial_seg r s) : ⇑↑f = ⇑f :=
  rfl

theorem init' {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop}
    (f : initial_seg r s) {a : α} {b : β} : s b (coe_fn f a) → ∃ (a' : α), coe_fn f a' = b :=
  init f a b

theorem init_iff {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop}
    (f : initial_seg r s) {a : α} {b : β} :
    s b (coe_fn f a) ↔ ∃ (a' : α), coe_fn f a' = b ∧ r a' a :=
  sorry

/-- An order isomorphism is an initial segment -/
def of_iso {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f : r ≃r s) :
    initial_seg r s :=
  mk ↑f sorry

/-- The identity function shows that `≼i` is reflexive -/
protected def refl {α : Type u_1} (r : α → α → Prop) : initial_seg r r :=
  mk (rel_embedding.refl r) sorry

/-- Composition of functions shows that `≼i` is transitive -/
protected def trans {α : Type u_1} {β : Type u_2} {γ : Type u_3} {r : α → α → Prop}
    {s : β → β → Prop} {t : γ → γ → Prop} (f : initial_seg r s) (g : initial_seg s t) :
    initial_seg r t :=
  mk (rel_embedding.trans (to_rel_embedding f) (to_rel_embedding g)) sorry

@[simp] theorem refl_apply {α : Type u_1} {r : α → α → Prop} (x : α) :
    coe_fn (initial_seg.refl r) x = x :=
  rfl

@[simp] theorem trans_apply {α : Type u_1} {β : Type u_2} {γ : Type u_3} {r : α → α → Prop}
    {s : β → β → Prop} {t : γ → γ → Prop} (f : initial_seg r s) (g : initial_seg s t) (a : α) :
    coe_fn (initial_seg.trans f g) a = coe_fn g (coe_fn f a) :=
  rfl

theorem unique_of_extensional {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop}
    [is_extensional β s] : well_founded r → subsingleton (initial_seg r s) :=
  sorry

protected instance subsingleton {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop}
    [is_well_order β s] : subsingleton (initial_seg r s) :=
  subsingleton.intro fun (a : initial_seg r s) => subsingleton.elim a

protected theorem eq {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop}
    [is_well_order β s] (f : initial_seg r s) (g : initial_seg r s) (a : α) :
    coe_fn f a = coe_fn g a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn f a = coe_fn g a)) (subsingleton.elim f g)))
    (Eq.refl (coe_fn g a))

theorem antisymm.aux {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop}
    [is_well_order α r] (f : initial_seg r s) (g : initial_seg s r) : function.left_inverse ⇑g ⇑f :=
  initial_seg.eq (initial_seg.trans f g) (initial_seg.refl r)

/-- If we have order embeddings between `α` and `β` whose images are initial segments, and `β`
is a well-order then `α` and `β` are order-isomorphic. -/
def antisymm {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} [is_well_order β s]
    (f : initial_seg r s) (g : initial_seg s r) : r ≃r s :=
  rel_iso.mk (equiv.mk ⇑f ⇑g sorry sorry) sorry

@[simp] theorem antisymm_to_fun {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop}
    [is_well_order β s] (f : initial_seg r s) (g : initial_seg s r) : ⇑(antisymm f g) = ⇑f :=
  rfl

@[simp] theorem antisymm_symm {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop}
    [is_well_order α r] [is_well_order β s] (f : initial_seg r s) (g : initial_seg s r) :
    rel_iso.symm (antisymm f g) = antisymm g f :=
  rel_iso.injective_coe_fn rfl

theorem eq_or_principal {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop}
    [is_well_order β s] (f : initial_seg r s) :
    function.surjective ⇑f ∨ ∃ (b : β), ∀ (x : β), s x b ↔ ∃ (y : α), coe_fn f y = x :=
  sorry

/-- Restrict the codomain of an initial segment -/
def cod_restrict {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (p : set β)
    (f : initial_seg r s) (H : ∀ (a : α), coe_fn f a ∈ p) : initial_seg r (subrel s p) :=
  mk (rel_embedding.cod_restrict p (↑f) H) sorry

@[simp] theorem cod_restrict_apply {α : Type u_1} {β : Type u_2} {r : α → α → Prop}
    {s : β → β → Prop} (p : set β) (f : initial_seg r s) (H : ∀ (a : α), coe_fn f a ∈ p) (a : α) :
    coe_fn (cod_restrict p f H) a = { val := coe_fn f a, property := H a } :=
  rfl

/-- Initial segment embedding of an order `r` into the disjoint union of `r` and `s`. -/
def le_add {α : Type u_1} {β : Type u_2} (r : α → α → Prop) (s : β → β → Prop) :
    initial_seg r (sum.lex r s) :=
  mk (rel_embedding.mk (function.embedding.mk sum.inl sorry) sorry) sorry

@[simp] theorem le_add_apply {α : Type u_1} {β : Type u_2} (r : α → α → Prop) (s : β → β → Prop)
    (a : α) : coe_fn (le_add r s) a = sum.inl a :=
  rfl

end initial_seg


/-!
### Principal segments

Order embeddings whose range is a principal segment of `s` (i.e., an interval of the form
`(-∞, top)` for some element `top` of `β`). The type of these embeddings from `r` to `s` is called
`principal_seg r s`, and denoted by `r ≺i s`. Principal segments are in particular initial
segments.
-/

/-- If `r` is a relation on `α` and `s` in a relation on `β`, then `f : r ≺i s` is an order
embedding whose range is an open interval `(-∞, top)` for some element `top` of `β`. Such order
embeddings are called principal segments -/
structure principal_seg {α : Type u_4} {β : Type u_5} (r : α → α → Prop) (s : β → β → Prop)
    extends r ↪r s where
  top : β
  down : ∀ (b : β), s b top ↔ ∃ (a : α), coe_fn _to_rel_embedding a = b

namespace principal_seg


protected instance rel_embedding.has_coe {α : Type u_1} {β : Type u_2} {r : α → α → Prop}
    {s : β → β → Prop} : has_coe (principal_seg r s) (r ↪r s) :=
  has_coe.mk to_rel_embedding

protected instance has_coe_to_fun {α : Type u_1} {β : Type u_2} {r : α → α → Prop}
    {s : β → β → Prop} : has_coe_to_fun (principal_seg r s) :=
  has_coe_to_fun.mk (fun (_x : principal_seg r s) => α → β) fun (f : principal_seg r s) => ⇑f

@[simp] theorem coe_fn_mk {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop}
    (f : r ↪r s) (t : β) (o : ∀ (b : β), s b t ↔ ∃ (a : α), coe_fn f a = b) : ⇑(mk f t o) = ⇑f :=
  rfl

@[simp] theorem coe_fn_to_rel_embedding {α : Type u_1} {β : Type u_2} {r : α → α → Prop}
    {s : β → β → Prop} (f : principal_seg r s) : ⇑(to_rel_embedding f) = ⇑f :=
  rfl

@[simp] theorem coe_coe_fn {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop}
    (f : principal_seg r s) : ⇑↑f = ⇑f :=
  rfl

theorem down' {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop}
    (f : principal_seg r s) {b : β} : s b (top f) ↔ ∃ (a : α), coe_fn f a = b :=
  down f b

theorem lt_top {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop}
    (f : principal_seg r s) (a : α) : s (coe_fn f a) (top f) :=
  iff.mpr (down' f) (Exists.intro a rfl)

theorem init {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} [is_trans β s]
    (f : principal_seg r s) {a : α} {b : β} (h : s b (coe_fn f a)) : ∃ (a' : α), coe_fn f a' = b :=
  iff.mp (down' f) (trans h (lt_top f a))

/-- A principal segment is in particular an initial segment. -/
protected instance has_coe_initial_seg {α : Type u_1} {β : Type u_2} {r : α → α → Prop}
    {s : β → β → Prop} [is_trans β s] : has_coe (principal_seg r s) (initial_seg r s) :=
  has_coe.mk fun (f : principal_seg r s) => initial_seg.mk (to_rel_embedding f) sorry

theorem coe_coe_fn' {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop}
    [is_trans β s] (f : principal_seg r s) : ⇑↑f = ⇑f :=
  rfl

theorem init_iff {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} [is_trans β s]
    (f : principal_seg r s) {a : α} {b : β} :
    s b (coe_fn f a) ↔ ∃ (a' : α), coe_fn f a' = b ∧ r a' a :=
  initial_seg.init_iff ↑f

theorem irrefl {α : Type u_1} (r : α → α → Prop) [is_well_order α r] (f : principal_seg r r) :
    False :=
  sorry

/-- Composition of a principal segment with an initial segment, as a principal segment -/
def lt_le {α : Type u_1} {β : Type u_2} {γ : Type u_3} {r : α → α → Prop} {s : β → β → Prop}
    {t : γ → γ → Prop} (f : principal_seg r s) (g : initial_seg s t) : principal_seg r t :=
  mk (rel_embedding.trans ↑f ↑g) (coe_fn g (top f)) sorry

@[simp] theorem lt_le_apply {α : Type u_1} {β : Type u_2} {γ : Type u_3} {r : α → α → Prop}
    {s : β → β → Prop} {t : γ → γ → Prop} (f : principal_seg r s) (g : initial_seg s t) (a : α) :
    coe_fn (lt_le f g) a = coe_fn g (coe_fn f a) :=
  rel_embedding.trans_apply (↑f) (↑g) a

@[simp] theorem lt_le_top {α : Type u_1} {β : Type u_2} {γ : Type u_3} {r : α → α → Prop}
    {s : β → β → Prop} {t : γ → γ → Prop} (f : principal_seg r s) (g : initial_seg s t) :
    top (lt_le f g) = coe_fn g (top f) :=
  rfl

/-- Composition of two principal segments as a principal segment -/
protected def trans {α : Type u_1} {β : Type u_2} {γ : Type u_3} {r : α → α → Prop}
    {s : β → β → Prop} {t : γ → γ → Prop} [is_trans γ t] (f : principal_seg r s)
    (g : principal_seg s t) : principal_seg r t :=
  lt_le f ↑g

@[simp] theorem trans_apply {α : Type u_1} {β : Type u_2} {γ : Type u_3} {r : α → α → Prop}
    {s : β → β → Prop} {t : γ → γ → Prop} [is_trans γ t] (f : principal_seg r s)
    (g : principal_seg s t) (a : α) : coe_fn (principal_seg.trans f g) a = coe_fn g (coe_fn f a) :=
  lt_le_apply f (↑g) a

@[simp] theorem trans_top {α : Type u_1} {β : Type u_2} {γ : Type u_3} {r : α → α → Prop}
    {s : β → β → Prop} {t : γ → γ → Prop} [is_trans γ t] (f : principal_seg r s)
    (g : principal_seg s t) : top (principal_seg.trans f g) = coe_fn g (top f) :=
  rfl

/-- Composition of an order isomorphism with a principal segment, as a principal segment -/
def equiv_lt {α : Type u_1} {β : Type u_2} {γ : Type u_3} {r : α → α → Prop} {s : β → β → Prop}
    {t : γ → γ → Prop} (f : r ≃r s) (g : principal_seg s t) : principal_seg r t :=
  mk (rel_embedding.trans ↑f ↑g) (top g) sorry

/-- Composition of a principal segment with an order isomorphism, as a principal segment -/
def lt_equiv {α : Type u_1} {β : Type u_2} {γ : Type u_3} {r : α → α → Prop} {s : β → β → Prop}
    {t : γ → γ → Prop} (f : principal_seg r s) (g : s ≃r t) : principal_seg r t :=
  mk (rel_embedding.trans ↑f ↑g) (coe_fn g (top f)) sorry

@[simp] theorem equiv_lt_apply {α : Type u_1} {β : Type u_2} {γ : Type u_3} {r : α → α → Prop}
    {s : β → β → Prop} {t : γ → γ → Prop} (f : r ≃r s) (g : principal_seg s t) (a : α) :
    coe_fn (equiv_lt f g) a = coe_fn g (coe_fn f a) :=
  rel_embedding.trans_apply (↑f) (↑g) a

@[simp] theorem equiv_lt_top {α : Type u_1} {β : Type u_2} {γ : Type u_3} {r : α → α → Prop}
    {s : β → β → Prop} {t : γ → γ → Prop} (f : r ≃r s) (g : principal_seg s t) :
    top (equiv_lt f g) = top g :=
  rfl

/-- Given a well order `s`, there is a most one principal segment embedding of `r` into `s`. -/
protected instance subsingleton {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop}
    [is_well_order β s] : subsingleton (principal_seg r s) :=
  sorry

theorem top_eq {α : Type u_1} {β : Type u_2} {γ : Type u_3} {r : α → α → Prop} {s : β → β → Prop}
    {t : γ → γ → Prop} [is_well_order γ t] (e : r ≃r s) (f : principal_seg r t)
    (g : principal_seg s t) : top f = top g :=
  eq.mpr (id (Eq._oldrec (Eq.refl (top f = top g)) (subsingleton.elim f (equiv_lt e g))))
    (Eq.refl (top (equiv_lt e g)))

theorem top_lt_top {α : Type u_1} {β : Type u_2} {γ : Type u_3} {r : α → α → Prop}
    {s : β → β → Prop} {t : γ → γ → Prop} [is_well_order γ t] (f : principal_seg r s)
    (g : principal_seg s t) (h : principal_seg r t) : t (top h) (top g) :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (t (top h) (top g))) (subsingleton.elim h (principal_seg.trans f g))))
    (lt_top g (top f))

/-- Any element of a well order yields a principal segment -/
def of_element {α : Type u_1} (r : α → α → Prop) (a : α) :
    principal_seg (subrel r (set_of fun (b : α) => r b a)) r :=
  mk (subrel.rel_embedding r (set_of fun (b : α) => r b a)) a sorry

@[simp] theorem of_element_apply {α : Type u_1} (r : α → α → Prop) (a : α)
    (b : ↥(set_of fun (b : α) => r b a)) : coe_fn (of_element r a) b = subtype.val b :=
  rfl

@[simp] theorem of_element_top {α : Type u_1} (r : α → α → Prop) (a : α) :
    top (of_element r a) = a :=
  rfl

/-- Restrict the codomain of a principal segment -/
def cod_restrict {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (p : set β)
    (f : principal_seg r s) (H : ∀ (a : α), coe_fn f a ∈ p) (H₂ : top f ∈ p) :
    principal_seg r (subrel s p) :=
  mk (rel_embedding.cod_restrict p (↑f) H) { val := top f, property := H₂ } sorry

@[simp] theorem cod_restrict_apply {α : Type u_1} {β : Type u_2} {r : α → α → Prop}
    {s : β → β → Prop} (p : set β) (f : principal_seg r s) (H : ∀ (a : α), coe_fn f a ∈ p)
    (H₂ : top f ∈ p) (a : α) :
    coe_fn (cod_restrict p f H H₂) a = { val := coe_fn f a, property := H a } :=
  rfl

@[simp] theorem cod_restrict_top {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop}
    (p : set β) (f : principal_seg r s) (H : ∀ (a : α), coe_fn f a ∈ p) (H₂ : top f ∈ p) :
    top (cod_restrict p f H H₂) = { val := top f, property := H₂ } :=
  rfl

end principal_seg


/-! ### Properties of initial and principal segments -/

/-- To an initial segment taking values in a well order, one can associate either a principal
segment (if the range is not everything, hence one can take as top the minimum of the complement
of the range) or an order isomorphism (if the range is everything). -/
def initial_seg.lt_or_eq {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop}
    [is_well_order β s] (f : initial_seg r s) : principal_seg r s ⊕ (r ≃r s) :=
  dite (function.surjective ⇑f)
    (fun (h : function.surjective ⇑f) => sum.inr (rel_iso.of_surjective (↑f) h))
    fun (h : ¬function.surjective ⇑f) =>
      (fun (h' : ∃ (b : β), ∀ (x : β), s x b ↔ ∃ (y : α), coe_fn f y = x) =>
          sum.inl (principal_seg.mk (↑f) (classical.some h') sorry))
        sorry

theorem initial_seg.lt_or_eq_apply_left {α : Type u_1} {β : Type u_2} {r : α → α → Prop}
    {s : β → β → Prop} [is_well_order β s] (f : initial_seg r s) (g : principal_seg r s) (a : α) :
    coe_fn g a = coe_fn f a :=
  initial_seg.eq (↑g) f a

theorem initial_seg.lt_or_eq_apply_right {α : Type u_1} {β : Type u_2} {r : α → α → Prop}
    {s : β → β → Prop} [is_well_order β s] (f : initial_seg r s) (g : r ≃r s) (a : α) :
    coe_fn g a = coe_fn f a :=
  initial_seg.eq (initial_seg.of_iso g) f a

/-- Composition of an initial segment taking values in a well order and a principal segment. -/
def initial_seg.le_lt {α : Type u_1} {β : Type u_2} {γ : Type u_3} {r : α → α → Prop}
    {s : β → β → Prop} {t : γ → γ → Prop} [is_well_order β s] [is_trans γ t] (f : initial_seg r s)
    (g : principal_seg s t) : principal_seg r t :=
  sorry

@[simp] theorem initial_seg.le_lt_apply {α : Type u_1} {β : Type u_2} {γ : Type u_3}
    {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop} [is_well_order β s] [is_trans γ t]
    (f : initial_seg r s) (g : principal_seg s t) (a : α) :
    coe_fn (initial_seg.le_lt f g) a = coe_fn g (coe_fn f a) :=
  sorry

namespace rel_embedding


/-- Given an order embedding into a well order, collapse the order embedding by filling the
gaps, to obtain an initial segment. Here, we construct the collapsed order embedding pointwise,
but the proof of the fact that it is an initial segment will be given in `collapse`. -/
def collapse_F {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop}
    [is_well_order β s] (f : r ↪r s) (a : α) : Subtype fun (b : β) => ¬s (coe_fn f a) b :=
  well_founded.fix sorry
    fun (a : α) (IH : (y : α) → r y a → Subtype fun (b : β) => ¬s (coe_fn f y) b) =>
      let S : set β :=
        set_of fun (b : β) => ∀ (a_1 : α) (h : r a_1 a), s (subtype.val (IH a_1 h)) b;
      { val := well_founded.min is_well_order.wf S sorry, property := sorry }

theorem collapse_F.lt {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop}
    [is_well_order β s] (f : r ↪r s) {a : α} {a' : α} :
    r a' a → s (subtype.val (collapse_F f a')) (subtype.val (collapse_F f a)) :=
  sorry

theorem collapse_F.not_lt {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop}
    [is_well_order β s] (f : r ↪r s) (a : α) {b : β}
    (h : ∀ (a' : α), r a' a → s (subtype.val (collapse_F f a')) b) :
    ¬s b (subtype.val (collapse_F f a)) :=
  sorry

/-- Construct an initial segment from an order embedding into a well order, by collapsing it
to fill the gaps. -/
def collapse {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} [is_well_order β s]
    (f : r ↪r s) : initial_seg r s :=
  initial_seg.mk (of_monotone (fun (a : α) => subtype.val (collapse_F f a)) sorry) sorry

theorem collapse_apply {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop}
    [is_well_order β s] (f : r ↪r s) (a : α) :
    coe_fn (collapse f) a = subtype.val (collapse_F f a) :=
  rfl

end rel_embedding


/-! ### Well order on an arbitrary type -/

theorem nonempty_embedding_to_cardinal {σ : Type u} : Nonempty (σ ↪ cardinal) := sorry

/-- An embedding of any type to the set of cardinals. -/
def embedding_to_cardinal {σ : Type u} : σ ↪ cardinal :=
  Classical.choice nonempty_embedding_to_cardinal

/-- Any type can be endowed with a well order, obtained by pulling back the well order over
cardinals by some embedding. -/
def well_ordering_rel {σ : Type u} : σ → σ → Prop := ⇑embedding_to_cardinal ⁻¹'o Less

protected instance well_ordering_rel.is_well_order {σ : Type u} :
    is_well_order σ well_ordering_rel :=
  rel_embedding.is_well_order (rel_embedding.preimage embedding_to_cardinal Less)

/-! ### Definition of ordinals -/

/-- Bundled structure registering a well order on a type. Ordinals will be defined as a quotient
of this type. -/
structure Well_order where
  α : Type u
  r : α → α → Prop
  wo : is_well_order α r

namespace Well_order


protected instance inhabited : Inhabited Well_order :=
  { default := mk pempty empty_relation empty_relation.is_well_order }

end Well_order


/-- Equivalence relation on well orders on arbitrary types in universe `u`, given by order
isomorphism. -/
protected instance ordinal.is_equivalent : setoid Well_order :=
  setoid.mk (fun (_x : Well_order) => sorry) sorry

/-- `ordinal.{u}` is the type of well orders in `Type u`, up to order isomorphism. -/
def ordinal := quotient sorry

namespace ordinal


/-- The order type of a well order is an ordinal. -/
def type {α : Type u_1} (r : α → α → Prop) [wo : is_well_order α r] : ordinal :=
  quotient.mk (Well_order.mk α r wo)

/-- The order type of an element inside a well order. For the embedding as a principal segment, see
`typein.principal_seg`. -/
def typein {α : Type u_1} (r : α → α → Prop) [is_well_order α r] (a : α) : ordinal :=
  type (subrel r (set_of fun (b : α) => r b a))

theorem type_def {α : Type u_1} (r : α → α → Prop) [wo : is_well_order α r] :
    quotient.mk (Well_order.mk α r wo) = type r :=
  rfl

@[simp] theorem type_def' {α : Type u_1} (r : α → α → Prop) [is_well_order α r]
    {wo : is_well_order α r} : quotient.mk (Well_order.mk α r wo) = type r :=
  rfl

theorem type_eq {α : Type u_1} {β : Type u_1} {r : α → α → Prop} {s : β → β → Prop}
    [is_well_order α r] [is_well_order β s] : type r = type s ↔ Nonempty (r ≃r s) :=
  quotient.eq

@[simp] theorem type_out (o : ordinal) : type (Well_order.r (quotient.out o)) = o := sorry

theorem induction_on {C : ordinal → Prop} (o : ordinal)
    (H : ∀ (α : Type u_1) (r : α → α → Prop) [_inst_1 : is_well_order α r], C (type r)) : C o :=
  sorry

/-! ### The order on ordinals -/

/-- Ordinal less-equal is defined such that
  well orders `r` and `s` satisfy `type r ≤ type s` if there exists
  a function embedding `r` as an initial segment of `s`. -/
protected def le (a : ordinal) (b : ordinal) :=
  quotient.lift_on₂ a b (fun (_x : Well_order) => sorry) sorry

protected instance has_le : HasLessEq ordinal := { LessEq := ordinal.le }

theorem type_le {α : Type u_1} {β : Type u_1} {r : α → α → Prop} {s : β → β → Prop}
    [is_well_order α r] [is_well_order β s] : type r ≤ type s ↔ Nonempty (initial_seg r s) :=
  iff.rfl

theorem type_le' {α : Type u_1} {β : Type u_1} {r : α → α → Prop} {s : β → β → Prop}
    [is_well_order α r] [is_well_order β s] : type r ≤ type s ↔ Nonempty (r ↪r s) :=
  sorry

/-- Ordinal less-than is defined such that
  well orders `r` and `s` satisfy `type r < type s` if there exists
  a function embedding `r` as a principal segment of `s`. -/
def lt (a : ordinal) (b : ordinal) := quotient.lift_on₂ a b (fun (_x : Well_order) => sorry) sorry

protected instance has_lt : HasLess ordinal := { Less := lt }

@[simp] theorem type_lt {α : Type u_1} {β : Type u_1} {r : α → α → Prop} {s : β → β → Prop}
    [is_well_order α r] [is_well_order β s] : type r < type s ↔ Nonempty (principal_seg r s) :=
  iff.rfl

protected instance partial_order : partial_order ordinal :=
  partial_order.mk LessEq Less sorry sorry sorry

/-- Given two ordinals `α ≤ β`, then `initial_seg_out α β` is the initial segment embedding
of `α` to `β`, as map from a model type for `α` to a model type for `β`. -/
def initial_seg_out {α : ordinal} {β : ordinal} (h : α ≤ β) :
    initial_seg (Well_order.r (quotient.out α)) (Well_order.r (quotient.out β)) :=
  Well_order.cases_on (quotient.out α)
    (fun (α_1 : Type u_1) (r : α_1 → α_1 → Prop) (wo : is_well_order α_1 r) =>
      Well_order.cases_on (quotient.out β)
        fun (α_2 : Type u_1) (r_1 : α_2 → α_2 → Prop) (wo_1 : is_well_order α_2 r_1) =>
          Classical.choice)
    sorry

/-- Given two ordinals `α < β`, then `principal_seg_out α β` is the principal segment embedding
of `α` to `β`, as map from a model type for `α` to a model type for `β`. -/
def principal_seg_out {α : ordinal} {β : ordinal} (h : α < β) :
    principal_seg (Well_order.r (quotient.out α)) (Well_order.r (quotient.out β)) :=
  Well_order.cases_on (quotient.out α)
    (fun (α_1 : Type u_1) (r : α_1 → α_1 → Prop) (wo : is_well_order α_1 r) =>
      Well_order.cases_on (quotient.out β)
        fun (α_2 : Type u_1) (r_1 : α_2 → α_2 → Prop) (wo_1 : is_well_order α_2 r_1) =>
          Classical.choice)
    sorry

/-- Given two ordinals `α = β`, then `rel_iso_out α β` is the order isomorphism between two
model types for `α` and `β`. -/
def rel_iso_out {α : ordinal} {β : ordinal} (h : α = β) :
    Well_order.r (quotient.out α) ≃r Well_order.r (quotient.out β) :=
  Well_order.cases_on (quotient.out α)
    (fun (α_1 : Type u_1) (r : α_1 → α_1 → Prop) (wo : is_well_order α_1 r) =>
      Well_order.cases_on (quotient.out β)
        fun (α_2 : Type u_1) (r_1 : α_2 → α_2 → Prop) (wo_1 : is_well_order α_2 r_1) =>
          Classical.choice ∘ sorry)
    sorry

theorem typein_lt_type {α : Type u_1} (r : α → α → Prop) [is_well_order α r] (a : α) :
    typein r a < type r :=
  Nonempty.intro (principal_seg.of_element r a)

@[simp] theorem typein_top {α : Type u_1} {β : Type u_1} {r : α → α → Prop} {s : β → β → Prop}
    [is_well_order α r] [is_well_order β s] (f : principal_seg r s) :
    typein s (principal_seg.top f) = type r :=
  sorry

@[simp] theorem typein_apply {α : Type u_1} {β : Type u_1} {r : α → α → Prop} {s : β → β → Prop}
    [is_well_order α r] [is_well_order β s] (f : initial_seg r s) (a : α) :
    typein s (coe_fn f a) = typein r a :=
  sorry

@[simp] theorem typein_lt_typein {α : Type u_1} (r : α → α → Prop) [is_well_order α r] {a : α}
    {b : α} : typein r a < typein r b ↔ r a b :=
  sorry

theorem typein_surj {α : Type u_1} (r : α → α → Prop) [is_well_order α r] {o : ordinal}
    (h : o < type r) : ∃ (a : α), typein r a = o :=
  sorry

theorem typein_injective {α : Type u_1} (r : α → α → Prop) [is_well_order α r] :
    function.injective (typein r) :=
  injective_of_increasing r Less (typein r) fun (x y : α) => iff.mpr (typein_lt_typein r)

theorem typein_inj {α : Type u_1} (r : α → α → Prop) [is_well_order α r] {a : α} {b : α} :
    typein r a = typein r b ↔ a = b :=
  function.injective.eq_iff (typein_injective r)

/-! ### Enumerating elements in a well-order with ordinals. -/

/-- `enum r o h` is the `o`-th element of `α` ordered by `r`.
  That is, `enum` maps an initial segment of the ordinals, those
  less than the order type of `r`, to the elements of `α`. -/
def enum {α : Type u_1} (r : α → α → Prop) [is_well_order α r] (o : ordinal) : o < type r → α :=
  quot.rec_on o (fun (_x : Well_order) => sorry) sorry

theorem enum_type {α : Type u_1} {β : Type u_1} {r : α → α → Prop} {s : β → β → Prop}
    [is_well_order α r] [is_well_order β s] (f : principal_seg s r) {h : type s < type r} :
    enum r (type s) h = principal_seg.top f :=
  principal_seg.top_eq (rel_iso.refl s) (Classical.choice h) f

@[simp] theorem enum_typein {α : Type u_1} (r : α → α → Prop) [is_well_order α r] (a : α)
    {h : typein r a < type r} : enum r (typein r a) h = a :=
  enum_type (principal_seg.of_element r a)

@[simp] theorem typein_enum {α : Type u_1} (r : α → α → Prop) [is_well_order α r] {o : ordinal}
    (h : o < type r) : typein r (enum r o h) = o :=
  sorry

/-- A well order `r` is order isomorphic to the set of ordinals strictly smaller than the
ordinal version of `r`. -/
def typein_iso {α : Type u_1} (r : α → α → Prop) [is_well_order α r] :
    r ≃r subrel Less fun (_x : ordinal) => _x < type r :=
  rel_iso.mk
    (equiv.mk (fun (x : α) => { val := typein r x, property := typein_lt_type r x })
      (fun (x : ↥fun (_x : ordinal) => _x < type r) => enum r (subtype.val x) sorry) sorry sorry)
    sorry

theorem enum_lt {α : Type u_1} {r : α → α → Prop} [is_well_order α r] {o₁ : ordinal} {o₂ : ordinal}
    (h₁ : o₁ < type r) (h₂ : o₂ < type r) : r (enum r o₁ h₁) (enum r o₂ h₂) ↔ o₁ < o₂ :=
  sorry

theorem rel_iso_enum' {α : Type u} {β : Type u} {r : α → α → Prop} {s : β → β → Prop}
    [is_well_order α r] [is_well_order β s] (f : r ≃r s) (o : ordinal) (hr : o < type r)
    (hs : o < type s) : coe_fn f (enum r o hr) = enum s o hs :=
  sorry

theorem rel_iso_enum {α : Type u} {β : Type u} {r : α → α → Prop} {s : β → β → Prop}
    [is_well_order α r] [is_well_order β s] (f : r ≃r s) (o : ordinal) (hr : o < type r) :
    coe_fn f (enum r o hr) =
        enum s o
          (eq.mpr
            ((fun (ᾰ ᾰ_1 : ordinal) (e_2 : ᾰ = ᾰ_1) (ᾰ_2 ᾰ_3 : ordinal) (e_3 : ᾰ_2 = ᾰ_3) =>
                congr (congr_arg Less e_2) e_3)
              o o (Eq.refl o) (type s) (type r) (quotient.sound (Nonempty.intro (rel_iso.symm f))))
            hr) :=
  sorry

theorem wf : well_founded Less := sorry

protected instance has_well_founded : has_well_founded ordinal := has_well_founded.mk Less wf

/-- Principal segment version of the `typein` function, embedding a well order into
  ordinals as a principal segment. -/
def typein.principal_seg {α : Type u} (r : α → α → Prop) [is_well_order α r] :
    principal_seg r Less :=
  principal_seg.mk (rel_embedding.of_monotone (typein r) sorry) (type r) sorry

@[simp] theorem typein.principal_seg_coe {α : Type u_1} (r : α → α → Prop) [is_well_order α r] :
    ⇑(typein.principal_seg r) = typein r :=
  rfl

/-! ### Cardinality of ordinals -/

/-- The cardinal of an ordinal is the cardinal of any
  set with that order type. -/
def card (o : ordinal) : cardinal := quot.lift_on o (fun (_x : Well_order) => sorry) sorry

@[simp] theorem card_type {α : Type u_1} (r : α → α → Prop) [is_well_order α r] :
    card (type r) = cardinal.mk α :=
  rfl

theorem card_typein {α : Type u_1} {r : α → α → Prop} [wo : is_well_order α r] (x : α) :
    cardinal.mk (Subtype fun (y : α) => r y x) = card (typein r x) :=
  rfl

theorem card_le_card {o₁ : ordinal} {o₂ : ordinal} : o₁ ≤ o₂ → card o₁ ≤ card o₂ := sorry

protected instance has_zero : HasZero ordinal :=
  { zero := quotient.mk (Well_order.mk pempty empty_relation empty_relation.is_well_order) }

protected instance inhabited : Inhabited ordinal := { default := 0 }

theorem zero_eq_type_empty : 0 = type empty_relation :=
  quotient.sound
    (Nonempty.intro
      (rel_iso.mk (equiv.symm equiv.empty_equiv_pempty) fun (_x _x_1 : pempty) => iff.rfl))

@[simp] theorem card_zero : card 0 = 0 := rfl

protected theorem zero_le (o : ordinal) : 0 ≤ o := sorry

@[simp] protected theorem le_zero {o : ordinal} : o ≤ 0 ↔ o = 0 := sorry

protected theorem pos_iff_ne_zero {o : ordinal} : 0 < o ↔ o ≠ 0 := sorry

protected instance has_one : HasOne ordinal :=
  { one := quotient.mk (Well_order.mk PUnit empty_relation empty_relation.is_well_order) }

theorem one_eq_type_unit : 1 = type empty_relation :=
  quotient.sound
    (Nonempty.intro (rel_iso.mk equiv.punit_equiv_punit fun (_x _x_1 : PUnit) => iff.rfl))

@[simp] theorem card_one : card 1 = 1 := rfl

/-! ### Lifting ordinals to a higher universe -/

/-- The universe lift operation for ordinals, which embeds `ordinal.{u}` as
  a proper initial segment of `ordinal.{v}` for `v > u`. For the initial segment version,
  see `lift.initial_seg`. -/
def lift (o : ordinal) : ordinal := quotient.lift_on o (fun (_x : Well_order) => sorry) sorry

theorem lift_type {α : Type u_1} (r : α → α → Prop) [is_well_order α r] :
    ∃ (wo' : is_well_order (ulift α) (⇑equiv.ulift ⁻¹'o r)),
        lift (type r) = type (⇑equiv.ulift ⁻¹'o r) :=
  Exists.intro (rel_embedding.is_well_order ↑(rel_iso.preimage equiv.ulift r)) rfl

theorem lift_umax : lift = lift := sorry

theorem lift_id' (a : ordinal) : lift a = a :=
  induction_on a
    fun (α : Type (max u_1 u_2)) (r : α → α → Prop) (_x : is_well_order α r) =>
      quotient.sound (Nonempty.intro (rel_iso.preimage equiv.ulift r))

@[simp] theorem lift_id (a : ordinal) : lift a = a := lift_id'

@[simp] theorem lift_lift (a : ordinal) : lift (lift a) = lift a := sorry

theorem lift_type_le {α : Type u} {β : Type v} {r : α → α → Prop} {s : β → β → Prop}
    [is_well_order α r] [is_well_order β s] :
    lift (type r) ≤ lift (type s) ↔ Nonempty (initial_seg r s) :=
  sorry

theorem lift_type_eq {α : Type u} {β : Type v} {r : α → α → Prop} {s : β → β → Prop}
    [is_well_order α r] [is_well_order β s] : lift (type r) = lift (type s) ↔ Nonempty (r ≃r s) :=
  sorry

theorem lift_type_lt {α : Type u} {β : Type v} {r : α → α → Prop} {s : β → β → Prop}
    [is_well_order α r] [is_well_order β s] :
    lift (type r) < lift (type s) ↔ Nonempty (principal_seg r s) :=
  sorry

@[simp] theorem lift_le {a : ordinal} {b : ordinal} : lift a ≤ lift b ↔ a ≤ b := sorry

@[simp] theorem lift_inj {a : ordinal} {b : ordinal} : lift a = lift b ↔ a = b := sorry

@[simp] theorem lift_lt {a : ordinal} {b : ordinal} : lift a < lift b ↔ a < b := sorry

@[simp] theorem lift_zero : lift 0 = 0 := sorry

theorem zero_eq_lift_type_empty : 0 = lift (type empty_relation) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (0 = lift (type empty_relation))) (Eq.symm zero_eq_type_empty)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (0 = lift 0)) lift_zero)) (Eq.refl 0))

@[simp] theorem lift_one : lift 1 = 1 := sorry

theorem one_eq_lift_type_unit : 1 = lift (type empty_relation) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (1 = lift (type empty_relation))) (Eq.symm one_eq_type_unit)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (1 = lift 1)) lift_one)) (Eq.refl 1))

@[simp] theorem lift_card (a : ordinal) : cardinal.lift (card a) = card (lift a) :=
  induction_on a fun (α : Type u_1) (r : α → α → Prop) (_x : is_well_order α r) => rfl

theorem lift_down' {a : cardinal} {b : ordinal} (h : card b ≤ cardinal.lift a) :
    ∃ (a' : ordinal), lift a' = b :=
  sorry

theorem lift_down {a : ordinal} {b : ordinal} (h : b ≤ lift a) : ∃ (a' : ordinal), lift a' = b :=
  lift_down'
    (eq.mpr (id (Eq._oldrec (Eq.refl (card b ≤ cardinal.lift (card a))) (lift_card a)))
      (card_le_card h))

theorem le_lift_iff {a : ordinal} {b : ordinal} :
    b ≤ lift a ↔ ∃ (a' : ordinal), lift a' = b ∧ a' ≤ a :=
  sorry

theorem lt_lift_iff {a : ordinal} {b : ordinal} :
    b < lift a ↔ ∃ (a' : ordinal), lift a' = b ∧ a' < a :=
  sorry

/-- Initial segment version of the lift operation on ordinals, embedding `ordinal.{u}` in
  `ordinal.{v}` as an initial segment when `u ≤ v`. -/
def lift.initial_seg : initial_seg Less Less :=
  initial_seg.mk (rel_embedding.mk (function.embedding.mk lift sorry) sorry) sorry

@[simp] theorem lift.initial_seg_coe : ⇑lift.initial_seg = lift := rfl

/-! ### The first infinite ordinal `omega` -/

/-- `ω` is the first infinite ordinal, defined as the order type of `ℕ`. -/
def omega : ordinal := lift (type Less)

theorem card_omega : card omega = cardinal.omega := rfl

@[simp] theorem lift_omega : lift omega = omega := lift_lift (type Less)

/-!
### Definition and first properties of addition on ordinals

In this paragraph, we introduce the addition on ordinals, and prove just enough properties to
deduce that the order on ordinals is total (and therefore well-founded). Further properties of
the addition, together with properties of the other operations, are proved in
`ordinal_arithmetic.lean`.
-/

/-- `o₁ + o₂` is the order on the disjoint union of `o₁` and `o₂` obtained by declaring that
  every element of `o₁` is smaller than every element of `o₂`. -/
protected instance has_add : Add ordinal :=
  { add := fun (o₁ o₂ : ordinal) => quotient.lift_on₂ o₁ o₂ (fun (_x : Well_order) => sorry) sorry }

@[simp] theorem card_add (o₁ : ordinal) (o₂ : ordinal) : card (o₁ + o₂) = card o₁ + card o₂ :=
  induction_on o₁
    fun (α : Type u_1) (r : α → α → Prop) (_x : is_well_order α r) =>
      induction_on o₂ fun (β : Type u_1) (s : β → β → Prop) (_x_1 : is_well_order β s) => rfl

@[simp] theorem card_nat (n : ℕ) : card ↑n = ↑n := sorry

@[simp] theorem type_add {α : Type u} {β : Type u} (r : α → α → Prop) (s : β → β → Prop)
    [is_well_order α r] [is_well_order β s] : type r + type s = type (sum.lex r s) :=
  rfl

/-- The ordinal successor is the smallest ordinal larger than `o`.
  It is defined as `o + 1`. -/
def succ (o : ordinal) : ordinal := o + 1

theorem succ_eq_add_one (o : ordinal) : succ o = o + 1 := rfl

protected instance add_monoid : add_monoid ordinal := add_monoid.mk Add.add sorry 0 sorry sorry

theorem add_le_add_left {a : ordinal} {b : ordinal} : a ≤ b → ∀ (c : ordinal), c + a ≤ c + b :=
  sorry

theorem le_add_right (a : ordinal) (b : ordinal) : a ≤ a + b := sorry

theorem add_le_add_right {a : ordinal} {b : ordinal} : a ≤ b → ∀ (c : ordinal), a + c ≤ b + c :=
  sorry

theorem le_add_left (a : ordinal) (b : ordinal) : a ≤ b + a := sorry

theorem lt_succ_self (o : ordinal) : o < succ o := sorry

theorem succ_le {a : ordinal} {b : ordinal} : succ a ≤ b ↔ a < b := sorry

theorem le_total (a : ordinal) (b : ordinal) : a ≤ b ∨ b ≤ a := sorry

protected instance linear_order : linear_order ordinal :=
  linear_order.mk partial_order.le partial_order.lt partial_order.le_refl partial_order.le_trans
    partial_order.le_antisymm le_total (classical.dec_rel LessEq)
    Mathlib.decidable_eq_of_decidable_le Mathlib.decidable_lt_of_decidable_le

protected instance has_lt.lt.is_well_order : is_well_order ordinal Less := is_well_order.mk wf

@[simp] theorem typein_le_typein {α : Type u_1} (r : α → α → Prop) [is_well_order α r] {x : α}
    {x' : α} : typein r x ≤ typein r x' ↔ ¬r x' x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (typein r x ≤ typein r x' ↔ ¬r x' x)) (Eq.symm (propext not_lt))))
    (eq.mpr
      (id
        (Eq._oldrec (Eq.refl (¬typein r x' < typein r x ↔ ¬r x' x)) (propext (typein_lt_typein r))))
      (iff.refl (¬r x' x)))

theorem enum_le_enum {α : Type u_1} (r : α → α → Prop) [is_well_order α r] {o : ordinal}
    {o' : ordinal} (ho : o < type r) (ho' : o' < type r) :
    ¬r (enum r o' ho') (enum r o ho) ↔ o ≤ o' :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (¬r (enum r o' ho') (enum r o ho) ↔ o ≤ o')) (Eq.symm (propext not_lt))))
    (eq.mpr
      (id
        (Eq._oldrec (Eq.refl (¬r (enum r o' ho') (enum r o ho) ↔ ¬o' < o))
          (propext (enum_lt ho' ho))))
      (iff.refl (¬o' < o)))

/-- `univ.{u v}` is the order type of the ordinals of `Type u` as a member
  of `ordinal.{v}` (when `u < v`). It is an inaccessible cardinal. -/
def univ : ordinal := lift (type Less)

theorem univ_id : univ = type Less := lift_id (type Less)

@[simp] theorem lift_univ : lift univ = univ := lift_lift (type Less)

theorem univ_umax : univ = univ := congr_fun lift_umax (type Less)

/-- Principal segment version of the lift operation on ordinals, embedding `ordinal.{u}` in
  `ordinal.{v}` as a principal segment when `u < v`. -/
def lift.principal_seg : principal_seg Less Less := principal_seg.mk (↑lift.initial_seg) univ sorry

@[simp] theorem lift.principal_seg_coe : ⇑lift.principal_seg = lift := rfl

@[simp] theorem lift.principal_seg_top : principal_seg.top lift.principal_seg = univ := rfl

theorem lift.principal_seg_top' : principal_seg.top lift.principal_seg = type Less := sorry

/-! ### Minimum -/

/-- The minimal element of a nonempty family of ordinals -/
def min {ι : Sort u_1} (I : Nonempty ι) (f : ι → ordinal) : ordinal :=
  well_founded.min wf (set.range f) sorry

theorem min_eq {ι : Sort u_1} (I : Nonempty ι) (f : ι → ordinal) : ∃ (i : ι), min I f = f i := sorry

theorem min_le {ι : Sort u_1} {I : Nonempty ι} (f : ι → ordinal) (i : ι) : min I f ≤ f i :=
  le_of_not_gt (well_founded.not_lt_min wf (set.range f) (min._match_1 f I) (set.mem_range_self i))

theorem le_min {ι : Sort u_1} {I : Nonempty ι} {f : ι → ordinal} {a : ordinal} :
    a ≤ min I f ↔ ∀ (i : ι), a ≤ f i :=
  sorry

/-- The minimal element of a nonempty set of ordinals -/
def omin (S : set ordinal) (H : ∃ (x : ordinal), x ∈ S) : ordinal := min sorry subtype.val

theorem omin_mem (S : set ordinal) (H : ∃ (x : ordinal), x ∈ S) : omin S H ∈ S := sorry

theorem le_omin {S : set ordinal} {H : ∃ (x : ordinal), x ∈ S} {a : ordinal} :
    a ≤ omin S H ↔ ∀ (i : ordinal), i ∈ S → a ≤ i :=
  iff.trans le_min set_coe.forall

theorem omin_le {S : set ordinal} {H : ∃ (x : ordinal), x ∈ S} {i : ordinal} (h : i ∈ S) :
    omin S H ≤ i :=
  iff.mp le_omin (le_refl (omin S H)) i h

@[simp] theorem lift_min {ι : Sort u_1} (I : Nonempty ι) (f : ι → ordinal) :
    lift (min I f) = min I (lift ∘ f) :=
  sorry

end ordinal


/-! ### Representing a cardinal with an ordinal -/

namespace cardinal


/-- The ordinal corresponding to a cardinal `c` is the least ordinal
  whose cardinal is `c`. For the order-embedding version, see `ord.order_embedding`. -/
def ord (c : cardinal) : ordinal :=
  let ι : Type u_1 → Type (max u_1 0) :=
    fun (α : Type u_1) => Subtype fun (r : α → α → Prop) => is_well_order α r;
  let F : Type u_1 → ordinal :=
    fun (α : Type u_1) =>
      ordinal.min sorry fun (i : ι α) => quotient.mk (Well_order.mk α (subtype.val i) sorry);
  quot.lift_on c F sorry

def ord_eq_min (α : Type u) :
    ord (mk α) =
        ordinal.min (ord._proof_1 α)
          fun (i : Subtype fun (r : α → α → Prop) => is_well_order α r) =>
            quotient.mk (Well_order.mk α (subtype.val i) (subtype.property i)) :=
  rfl

theorem ord_eq (α : Type u_1) : ∃ (r : α → α → Prop), Exists (ord (mk α) = ordinal.type r) := sorry

theorem ord_le_type {α : Type u_1} (r : α → α → Prop) [is_well_order α r] :
    ord (mk α) ≤ ordinal.type r :=
  sorry

theorem ord_le {c : cardinal} {o : ordinal} : ord c ≤ o ↔ c ≤ ordinal.card o := sorry

theorem lt_ord {c : cardinal} {o : ordinal} : o < ord c ↔ ordinal.card o < c := sorry

@[simp] theorem card_ord (c : cardinal) : ordinal.card (ord c) = c := sorry

theorem ord_card_le (o : ordinal) : ord (ordinal.card o) ≤ o :=
  iff.mpr ord_le (le_refl (ordinal.card o))

theorem lt_ord_succ_card (o : ordinal) : o < ord (succ (ordinal.card o)) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (o < ord (succ (ordinal.card o)))) (propext lt_ord)))
    (lt_succ_self (ordinal.card o))

@[simp] theorem ord_le_ord {c₁ : cardinal} {c₂ : cardinal} : ord c₁ ≤ ord c₂ ↔ c₁ ≤ c₂ := sorry

@[simp] theorem ord_lt_ord {c₁ : cardinal} {c₂ : cardinal} : ord c₁ < ord c₂ ↔ c₁ < c₂ := sorry

@[simp] theorem ord_zero : ord 0 = 0 :=
  le_antisymm (iff.mpr ord_le (zero_le (ordinal.card 0))) (ordinal.zero_le (ord 0))

@[simp] theorem ord_nat (n : ℕ) : ord ↑n = ↑n := sorry

@[simp] theorem lift_ord (c : cardinal) : ordinal.lift (ord c) = ord (lift c) := sorry

theorem mk_ord_out (c : cardinal) : mk (Well_order.α (quotient.out (ord c))) = c := sorry

theorem card_typein_lt {α : Type u_1} (r : α → α → Prop) [is_well_order α r] (x : α)
    (h : ord (mk α) = ordinal.type r) : ordinal.card (ordinal.typein r x) < mk α :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (ordinal.card (ordinal.typein r x) < mk α))
        (Eq.symm (propext ord_lt_ord))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (ord (ordinal.card (ordinal.typein r x)) < ord (mk α))) h))
      (lt_of_le_of_lt (ord_card_le (ordinal.typein r x)) (ordinal.typein_lt_type r x)))

theorem card_typein_out_lt (c : cardinal) (x : Well_order.α (quotient.out (ord c))) :
    ordinal.card (ordinal.typein (Well_order.r (quotient.out (ord c))) x) < c :=
  sorry

theorem ord_injective : function.injective ord := sorry

/-- The ordinal corresponding to a cardinal `c` is the least ordinal
  whose cardinal is `c`. This is the order-embedding version. For the regular function, see `ord`.
-/
def ord.order_embedding : cardinal ↪o ordinal :=
  rel_embedding.order_embedding_of_lt_embedding (rel_embedding.of_monotone ord sorry)

@[simp] theorem ord.order_embedding_coe : ⇑ord.order_embedding = ord := rfl

/-- The cardinal `univ` is the cardinality of ordinal `univ`, or
  equivalently the cardinal of `ordinal.{u}`, or `cardinal.{u}`,
  as an element of `cardinal.{v}` (when `u < v`). -/
def univ : cardinal := lift (mk ordinal)

theorem univ_id : univ = mk ordinal := lift_id (mk ordinal)

@[simp] theorem lift_univ : lift univ = univ := lift_lift (mk ordinal)

theorem univ_umax : univ = univ := congr_fun lift_umax (mk ordinal)

theorem lift_lt_univ (c : cardinal) : lift c < univ := sorry

theorem lift_lt_univ' (c : cardinal) : lift c < univ := sorry

@[simp] theorem ord_univ : ord univ = ordinal.univ := sorry

theorem lt_univ {c : cardinal} : c < univ ↔ ∃ (c' : cardinal), c = lift c' := sorry

theorem lt_univ' {c : cardinal} : c < univ ↔ ∃ (c' : cardinal), c = lift c' := sorry

end cardinal


namespace ordinal


@[simp] theorem card_univ : card univ = cardinal.univ := rfl

end Mathlib