/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.finset.fold
import Mathlib.data.equiv.mul_add
import Mathlib.tactic.abel
import PostPort

universes u v w u_1 

namespace Mathlib

/-!
# Big operators

In this file we define products and sums indexed by finite sets (specifically, `finset`).

## Notation

We introduce the following notation, localized in `big_operators`.
To enable the notation, use `open_locale big_operators`.

Let `s` be a `finset α`, and `f : α → β` a function.

* `∏ x in s, f x` is notation for `finset.prod s f` (assuming `β` is a `comm_monoid`)
* `∑ x in s, f x` is notation for `finset.sum s f` (assuming `β` is an `add_comm_monoid`)
* `∏ x, f x` is notation for `finset.prod finset.univ f`
  (assuming `α` is a `fintype` and `β` is a `comm_monoid`)
* `∑ x, f x` is notation for `finset.sum finset.univ f`
  (assuming `α` is a `fintype` and `β` is an `add_comm_monoid`)

-/

namespace finset


/--
`∏ x in s, f x` is the product of `f x`
as `x` ranges over the elements of the finite set `s`.
-/
protected def prod {α : Type u} {β : Type v} [comm_monoid β] (s : finset α) (f : α → β) : β :=
  multiset.prod (multiset.map f (val s))

@[simp] theorem prod_mk {α : Type u} {β : Type v} [comm_monoid β] (s : multiset α) (hs : multiset.nodup s) (f : α → β) : finset.prod (mk s hs) f = multiset.prod (multiset.map f s) :=
  rfl

end finset


/--
## Operator precedence of `∏` and `∑`

There is no established mathematical convention
for the operator precedence of big operators like `∏` and `∑`.
We will have to make a choice.

Online discussions, such as https://math.stackexchange.com/q/185538/30839
seem to suggest that `∏` and `∑` should have the same precedence,
and that this should be somewhere between `*` and `+`.
The latter have precedence levels `70` and `65` respectively,
and we therefore choose the level `67`.

In practice, this means that parentheses should be placed as follows:
```lean
∑ k in K, (a k + b k) = ∑ k in K, a k + ∑ k in K, b k →
  ∏ k in K, a k * b k = (∏ k in K, a k) * (∏ k in K, b k)
```
(Example taken from page 490 of Knuth's *Concrete Mathematics*.)
-/
namespace finset


theorem prod_eq_multiset_prod {α : Type u} {β : Type v} [comm_monoid β] (s : finset α) (f : α → β) : (finset.prod s fun (x : α) => f x) = multiset.prod (multiset.map f (val s)) :=
  rfl

theorem prod_eq_fold {α : Type u} {β : Type v} [comm_monoid β] (s : finset α) (f : α → β) : (finset.prod s fun (x : α) => f x) = fold Mul.mul 1 f s :=
  rfl

end finset


theorem monoid_hom.map_prod {α : Type u} {β : Type v} {γ : Type w} [comm_monoid β] [comm_monoid γ] (g : β →* γ) (f : α → β) (s : finset α) : coe_fn g (finset.prod s fun (x : α) => f x) = finset.prod s fun (x : α) => coe_fn g (f x) := sorry

theorem add_equiv.map_sum {α : Type u} {β : Type v} {γ : Type w} [add_comm_monoid β] [add_comm_monoid γ] (g : β ≃+ γ) (f : α → β) (s : finset α) : coe_fn g (finset.sum s fun (x : α) => f x) = finset.sum s fun (x : α) => coe_fn g (f x) :=
  add_monoid_hom.map_sum (add_equiv.to_add_monoid_hom g) f s

theorem ring_hom.map_list_prod {β : Type v} {γ : Type w} [semiring β] [semiring γ] (f : β →+* γ) (l : List β) : coe_fn f (list.prod l) = list.prod (list.map (⇑f) l) :=
  monoid_hom.map_list_prod (ring_hom.to_monoid_hom f) l

theorem ring_hom.map_list_sum {β : Type v} {γ : Type w} [semiring β] [semiring γ] (f : β →+* γ) (l : List β) : coe_fn f (list.sum l) = list.sum (list.map (⇑f) l) :=
  add_monoid_hom.map_list_sum (ring_hom.to_add_monoid_hom f) l

theorem ring_hom.map_multiset_prod {β : Type v} {γ : Type w} [comm_semiring β] [comm_semiring γ] (f : β →+* γ) (s : multiset β) : coe_fn f (multiset.prod s) = multiset.prod (multiset.map (⇑f) s) :=
  monoid_hom.map_multiset_prod (ring_hom.to_monoid_hom f) s

theorem ring_hom.map_multiset_sum {β : Type v} {γ : Type w} [semiring β] [semiring γ] (f : β →+* γ) (s : multiset β) : coe_fn f (multiset.sum s) = multiset.sum (multiset.map (⇑f) s) :=
  add_monoid_hom.map_multiset_sum (ring_hom.to_add_monoid_hom f) s

theorem ring_hom.map_prod {α : Type u} {β : Type v} {γ : Type w} [comm_semiring β] [comm_semiring γ] (g : β →+* γ) (f : α → β) (s : finset α) : coe_fn g (finset.prod s fun (x : α) => f x) = finset.prod s fun (x : α) => coe_fn g (f x) :=
  monoid_hom.map_prod (ring_hom.to_monoid_hom g) f s

theorem ring_hom.map_sum {α : Type u} {β : Type v} {γ : Type w} [semiring β] [semiring γ] (g : β →+* γ) (f : α → β) (s : finset α) : coe_fn g (finset.sum s fun (x : α) => f x) = finset.sum s fun (x : α) => coe_fn g (f x) :=
  add_monoid_hom.map_sum (ring_hom.to_add_monoid_hom g) f s

theorem add_monoid_hom.coe_sum {α : Type u} {β : Type v} {γ : Type w} [add_monoid β] [add_comm_monoid γ] (f : α → β →+ γ) (s : finset α) : ⇑(finset.sum s fun (x : α) => f x) = finset.sum s fun (x : α) => ⇑(f x) :=
  add_monoid_hom.map_sum (add_monoid_hom.coe_fn β γ) (fun (x : α) => f x) s

@[simp] theorem monoid_hom.finset_prod_apply {α : Type u} {β : Type v} {γ : Type w} [monoid β] [comm_monoid γ] (f : α → β →* γ) (s : finset α) (b : β) : coe_fn (finset.prod s fun (x : α) => f x) b = finset.prod s fun (x : α) => coe_fn (f x) b :=
  monoid_hom.map_prod (coe_fn monoid_hom.eval b) (fun (x : α) => f x) s

namespace finset


@[simp] theorem sum_empty {β : Type v} [add_comm_monoid β] {α : Type u} {f : α → β} : (finset.sum ∅ fun (x : α) => f x) = 0 :=
  rfl

@[simp] theorem prod_insert {α : Type u} {β : Type v} {s : finset α} {a : α} {f : α → β} [comm_monoid β] [DecidableEq α] : ¬a ∈ s → (finset.prod (insert a s) fun (x : α) => f x) = f a * finset.prod s fun (x : α) => f x :=
  fold_insert

/--
The product of `f` over `insert a s` is the same as
the product over `s`, as long as `a` is in `s` or `f a = 1`.
-/
@[simp] theorem prod_insert_of_eq_one_if_not_mem {α : Type u} {β : Type v} {s : finset α} {a : α} {f : α → β} [comm_monoid β] [DecidableEq α] (h : ¬a ∈ s → f a = 1) : (finset.prod (insert a s) fun (x : α) => f x) = finset.prod s fun (x : α) => f x := sorry

/--
The product of `f` over `insert a s` is the same as the product over `s`, as long as `f a = 1`.
-/
@[simp] theorem prod_insert_one {α : Type u} {β : Type v} {s : finset α} {a : α} {f : α → β} [comm_monoid β] [DecidableEq α] (h : f a = 1) : (finset.prod (insert a s) fun (x : α) => f x) = finset.prod s fun (x : α) => f x :=
  prod_insert_of_eq_one_if_not_mem fun (_x : ¬a ∈ s) => h

@[simp] theorem prod_singleton {α : Type u} {β : Type v} {a : α} {f : α → β} [comm_monoid β] : (finset.prod (singleton a) fun (x : α) => f x) = f a :=
  Eq.trans fold_singleton (mul_one (f a))

theorem sum_pair {α : Type u} {β : Type v} {f : α → β} [add_comm_monoid β] [DecidableEq α] {a : α} {b : α} (h : a ≠ b) : (finset.sum (insert a (singleton b)) fun (x : α) => f x) = f a + f b := sorry

@[simp] theorem prod_const_one {α : Type u} {β : Type v} {s : finset α} [comm_monoid β] : (finset.prod s fun (x : α) => 1) = 1 := sorry

@[simp] theorem sum_const_zero {α : Type u} {β : Type u_1} {s : finset α} [add_comm_monoid β] : (finset.sum s fun (x : α) => 0) = 0 :=
  prod_const_one

@[simp] theorem prod_image {α : Type u} {β : Type v} {γ : Type w} {f : α → β} [comm_monoid β] [DecidableEq α] {s : finset γ} {g : γ → α} : (∀ (x : γ), x ∈ s → ∀ (y : γ), y ∈ s → g x = g y → x = y) →
  (finset.prod (image g s) fun (x : α) => f x) = finset.prod s fun (x : γ) => f (g x) :=
  fold_image

@[simp] theorem prod_map {α : Type u} {β : Type v} {γ : Type w} [comm_monoid β] (s : finset α) (e : α ↪ γ) (f : γ → β) : (finset.prod (map e s) fun (x : γ) => f x) = finset.prod s fun (x : α) => f (coe_fn e x) := sorry

theorem prod_congr {α : Type u} {β : Type v} {s₁ : finset α} {s₂ : finset α} {f : α → β} {g : α → β} [comm_monoid β] (h : s₁ = s₂) : (∀ (x : α), x ∈ s₂ → f x = g x) → finset.prod s₁ f = finset.prod s₂ g :=
  eq.mpr (id (Eq._oldrec (Eq.refl ((∀ (x : α), x ∈ s₂ → f x = g x) → finset.prod s₁ f = finset.prod s₂ g)) h)) fold_congr

theorem prod_union_inter {α : Type u} {β : Type v} {s₁ : finset α} {s₂ : finset α} {f : α → β} [comm_monoid β] [DecidableEq α] : ((finset.prod (s₁ ∪ s₂) fun (x : α) => f x) * finset.prod (s₁ ∩ s₂) fun (x : α) => f x) =
  (finset.prod s₁ fun (x : α) => f x) * finset.prod s₂ fun (x : α) => f x :=
  fold_union_inter

theorem sum_union {α : Type u} {β : Type v} {s₁ : finset α} {s₂ : finset α} {f : α → β} [add_comm_monoid β] [DecidableEq α] (h : disjoint s₁ s₂) : (finset.sum (s₁ ∪ s₂) fun (x : α) => f x) = (finset.sum s₁ fun (x : α) => f x) + finset.sum s₂ fun (x : α) => f x := sorry

theorem prod_sdiff {α : Type u} {β : Type v} {s₁ : finset α} {s₂ : finset α} {f : α → β} [comm_monoid β] [DecidableEq α] (h : s₁ ⊆ s₂) : ((finset.prod (s₂ \ s₁) fun (x : α) => f x) * finset.prod s₁ fun (x : α) => f x) = finset.prod s₂ fun (x : α) => f x := sorry

@[simp] theorem prod_sum_elim {α : Type u} {β : Type v} {γ : Type w} [comm_monoid β] [DecidableEq (α ⊕ γ)] (s : finset α) (t : finset γ) (f : α → β) (g : γ → β) : (finset.prod (map function.embedding.inl s ∪ map function.embedding.inr t) fun (x : α ⊕ γ) => sum.elim f g x) =
  (finset.prod s fun (x : α) => f x) * finset.prod t fun (x : γ) => g x := sorry

theorem sum_bUnion {α : Type u} {β : Type v} {γ : Type w} {f : α → β} [add_comm_monoid β] [DecidableEq α] {s : finset γ} {t : γ → finset α} : (∀ (x : γ), x ∈ s → ∀ (y : γ), y ∈ s → x ≠ y → disjoint (t x) (t y)) →
  (finset.sum (finset.bUnion s t) fun (x : α) => f x) = finset.sum s fun (x : γ) => finset.sum (t x) fun (x : α) => f x := sorry

theorem sum_product {α : Type u} {β : Type v} {γ : Type w} [add_comm_monoid β] {s : finset γ} {t : finset α} {f : γ × α → β} : (finset.sum (finset.product s t) fun (x : γ × α) => f x) =
  finset.sum s fun (x : γ) => finset.sum t fun (y : α) => f (x, y) := sorry

/-- An uncurried version of `finset.prod_product`. -/
theorem sum_product' {α : Type u} {β : Type v} {γ : Type w} [add_comm_monoid β] {s : finset γ} {t : finset α} {f : γ → α → β} : (finset.sum (finset.product s t) fun (x : γ × α) => f (prod.fst x) (prod.snd x)) =
  finset.sum s fun (x : γ) => finset.sum t fun (y : α) => f x y :=
  sum_product

/-- Product over a sigma type equals the product of fiberwise products. For rewriting
in the reverse direction, use `finset.prod_sigma'`.  -/
theorem prod_sigma {α : Type u} {β : Type v} [comm_monoid β] {σ : α → Type u_1} (s : finset α) (t : (a : α) → finset (σ a)) (f : sigma σ → β) : (finset.prod (finset.sigma s t) fun (x : sigma fun (a : α) => σ a) => f x) =
  finset.prod s fun (a : α) => finset.prod (t a) fun (s : σ a) => f (sigma.mk a s) := sorry

theorem prod_sigma' {α : Type u} {β : Type v} [comm_monoid β] {σ : α → Type u_1} (s : finset α) (t : (a : α) → finset (σ a)) (f : (a : α) → σ a → β) : (finset.prod s fun (a : α) => finset.prod (t a) fun (s : σ a) => f a s) =
  finset.prod (finset.sigma s t) fun (x : sigma fun (a : α) => σ a) => f (sigma.fst x) (sigma.snd x) :=
  Eq.symm (prod_sigma s t fun (x : sigma fun (a : α) => σ a) => f (sigma.fst x) (sigma.snd x))

theorem prod_fiberwise_of_maps_to {α : Type u} {β : Type v} {γ : Type w} [comm_monoid β] [DecidableEq γ] {s : finset α} {t : finset γ} {g : α → γ} (h : ∀ (x : α), x ∈ s → g x ∈ t) (f : α → β) : (finset.prod t fun (y : γ) => finset.prod (filter (fun (x : α) => g x = y) s) fun (x : α) => f x) =
  finset.prod s fun (x : α) => f x := sorry

theorem prod_image' {α : Type u} {β : Type v} {γ : Type w} {f : α → β} [comm_monoid β] [DecidableEq α] {s : finset γ} {g : γ → α} (h : γ → β) (eq : ∀ (c : γ), c ∈ s → f (g c) = finset.prod (filter (fun (c' : γ) => g c' = g c) s) fun (x : γ) => h x) : (finset.prod (image g s) fun (x : α) => f x) = finset.prod s fun (x : γ) => h x := sorry

theorem prod_mul_distrib {α : Type u} {β : Type v} {s : finset α} {f : α → β} {g : α → β} [comm_monoid β] : (finset.prod s fun (x : α) => f x * g x) = (finset.prod s fun (x : α) => f x) * finset.prod s fun (x : α) => g x := sorry

theorem sum_comm {α : Type u} {β : Type v} {γ : Type w} [add_comm_monoid β] {s : finset γ} {t : finset α} {f : γ → α → β} : (finset.sum s fun (x : γ) => finset.sum t fun (y : α) => f x y) =
  finset.sum t fun (y : α) => finset.sum s fun (x : γ) => f x y := sorry

theorem sum_hom {α : Type u} {β : Type v} {γ : Type w} [add_comm_monoid β] [add_comm_monoid γ] (s : finset α) {f : α → β} (g : β → γ) [is_add_monoid_hom g] : (finset.sum s fun (x : α) => g (f x)) = g (finset.sum s fun (x : α) => f x) :=
  Eq.symm (add_monoid_hom.map_sum (add_monoid_hom.of g) f s)

theorem sum_hom_rel {α : Type u} {β : Type v} {γ : Type w} [add_comm_monoid β] [add_comm_monoid γ] {r : β → γ → Prop} {f : α → β} {g : α → γ} {s : finset α} (h₁ : r 0 0) (h₂ : ∀ (a : α) (b : β) (c : γ), r b c → r (f a + b) (g a + c)) : r (finset.sum s fun (x : α) => f x) (finset.sum s fun (x : α) => g x) :=
  id (multiset.sum_hom_rel (val s) h₁ h₂)

theorem prod_subset {α : Type u} {β : Type v} {s₁ : finset α} {s₂ : finset α} {f : α → β} [comm_monoid β] (h : s₁ ⊆ s₂) (hf : ∀ (x : α), x ∈ s₂ → ¬x ∈ s₁ → f x = 1) : (finset.prod s₁ fun (x : α) => f x) = finset.prod s₂ fun (x : α) => f x := sorry

theorem prod_filter_of_ne {α : Type u} {β : Type v} {s : finset α} {f : α → β} [comm_monoid β] {p : α → Prop} [decidable_pred p] (hp : ∀ (x : α), x ∈ s → f x ≠ 1 → p x) : (finset.prod (filter p s) fun (x : α) => f x) = finset.prod s fun (x : α) => f x := sorry

-- If we use `[decidable_eq β]` here, some rewrites fail because they find a wrong `decidable`

-- instance first; `{∀x, decidable (f x ≠ 1)}` doesn't work with `rw ← prod_filter_ne_one`

theorem sum_filter_ne_zero {α : Type u} {β : Type v} {s : finset α} {f : α → β} [add_comm_monoid β] [(x : α) → Decidable (f x ≠ 0)] : (finset.sum (filter (fun (x : α) => f x ≠ 0) s) fun (x : α) => f x) = finset.sum s fun (x : α) => f x :=
  sum_filter_of_ne fun (_x : α) (_x_1 : _x ∈ s) => id

theorem sum_filter {α : Type u} {β : Type v} {s : finset α} [add_comm_monoid β] (p : α → Prop) [decidable_pred p] (f : α → β) : (finset.sum (filter p s) fun (a : α) => f a) = finset.sum s fun (a : α) => ite (p a) (f a) 0 := sorry

theorem prod_eq_single {α : Type u} {β : Type v} [comm_monoid β] {s : finset α} {f : α → β} (a : α) (h₀ : ∀ (b : α), b ∈ s → b ≠ a → f b = 1) (h₁ : ¬a ∈ s → f a = 1) : (finset.prod s fun (x : α) => f x) = f a := sorry

theorem sum_attach {α : Type u} {β : Type v} {s : finset α} [add_comm_monoid β] {f : α → β} : (finset.sum (attach s) fun (x : Subtype fun (x : α) => x ∈ s) => f ↑x) = finset.sum s fun (x : α) => f x := sorry

/-- A product over `s.subtype p` equals one over `s.filter p`. -/
@[simp] theorem prod_subtype_eq_prod_filter {α : Type u} {β : Type v} {s : finset α} [comm_monoid β] (f : α → β) {p : α → Prop} [decidable_pred p] : (finset.prod (finset.subtype p s) fun (x : Subtype p) => f ↑x) = finset.prod (filter p s) fun (x : α) => f x := sorry

/-- If all elements of a `finset` satisfy the predicate `p`, a product
over `s.subtype p` equals that product over `s`. -/
theorem sum_subtype_of_mem {α : Type u} {β : Type v} {s : finset α} [add_comm_monoid β] (f : α → β) {p : α → Prop} [decidable_pred p] (h : ∀ (x : α), x ∈ s → p x) : (finset.sum (finset.subtype p s) fun (x : Subtype p) => f ↑x) = finset.sum s fun (x : α) => f x := sorry

/-- A product of a function over a `finset` in a subtype equals a
product in the main type of a function that agrees with the first
function on that `finset`. -/
theorem sum_subtype_map_embedding {α : Type u} {β : Type v} [add_comm_monoid β] {p : α → Prop} {s : finset (Subtype fun (x : α) => p x)} {f : (Subtype fun (x : α) => p x) → β} {g : α → β} (h : ∀ (x : Subtype fun (x : α) => p x), x ∈ s → g ↑x = f x) : (finset.sum (map (function.embedding.subtype fun (x : α) => p x) s) fun (x : α) => g x) =
  finset.sum s fun (x : Subtype fun (x : α) => p x) => f x := sorry

theorem prod_eq_one {α : Type u} {β : Type v} [comm_monoid β] {f : α → β} {s : finset α} (h : ∀ (x : α), x ∈ s → f x = 1) : (finset.prod s fun (x : α) => f x) = 1 :=
  Eq.trans (prod_congr rfl h) prod_const_one

theorem sum_apply_dite {α : Type u} {β : Type v} {γ : Type w} [add_comm_monoid β] {s : finset α} {p : α → Prop} {hp : decidable_pred p} (f : (x : α) → p x → γ) (g : (x : α) → ¬p x → γ) (h : γ → β) : (finset.sum s fun (x : α) => h (dite (p x) (fun (hx : p x) => f x hx) fun (hx : ¬p x) => g x hx)) =
  (finset.sum (attach (filter p s))
      fun (x : Subtype fun (x : α) => x ∈ filter p s) =>
        h (f (subtype.val x) (and.right (iff.mp mem_filter (subtype.property x))))) +
    finset.sum (attach (filter (fun (x : α) => ¬p x) s))
      fun (x : Subtype fun (x : α) => x ∈ filter (fun (x : α) => ¬p x) s) =>
        h (g (subtype.val x) (and.right (iff.mp mem_filter (subtype.property x)))) := sorry

theorem prod_apply_ite {α : Type u} {β : Type v} {γ : Type w} [comm_monoid β] {s : finset α} {p : α → Prop} {hp : decidable_pred p} (f : α → γ) (g : α → γ) (h : γ → β) : (finset.prod s fun (x : α) => h (ite (p x) (f x) (g x))) =
  (finset.prod (filter p s) fun (x : α) => h (f x)) *
    finset.prod (filter (fun (x : α) => ¬p x) s) fun (x : α) => h (g x) :=
  trans (prod_apply_dite (fun (x : α) (hx : p x) => f x) (fun (x : α) (hx : ¬p x) => g x) h)
    (congr_arg2 Mul.mul prod_attach prod_attach)

theorem sum_dite {α : Type u} {β : Type v} [add_comm_monoid β] {s : finset α} {p : α → Prop} {hp : decidable_pred p} (f : (x : α) → p x → β) (g : (x : α) → ¬p x → β) : (finset.sum s fun (x : α) => dite (p x) (fun (hx : p x) => f x hx) fun (hx : ¬p x) => g x hx) =
  (finset.sum (attach (filter p s))
      fun (x : Subtype fun (x : α) => x ∈ filter p s) =>
        f (subtype.val x) (and.right (iff.mp mem_filter (subtype.property x)))) +
    finset.sum (attach (filter (fun (x : α) => ¬p x) s))
      fun (x : Subtype fun (x : α) => x ∈ filter (fun (x : α) => ¬p x) s) =>
        g (subtype.val x) (and.right (iff.mp mem_filter (subtype.property x))) := sorry

theorem prod_ite {α : Type u} {β : Type v} [comm_monoid β] {s : finset α} {p : α → Prop} {hp : decidable_pred p} (f : α → β) (g : α → β) : (finset.prod s fun (x : α) => ite (p x) (f x) (g x)) =
  (finset.prod (filter p s) fun (x : α) => f x) * finset.prod (filter (fun (x : α) => ¬p x) s) fun (x : α) => g x := sorry

theorem sum_extend_by_zero {α : Type u} {β : Type v} [add_comm_monoid β] [DecidableEq α] (s : finset α) (f : α → β) : (finset.sum s fun (i : α) => ite (i ∈ s) (f i) 0) = finset.sum s fun (i : α) => f i :=
  sum_congr rfl fun (i : α) (hi : i ∈ s) => if_pos hi

@[simp] theorem sum_dite_eq {α : Type u} {β : Type v} [add_comm_monoid β] [DecidableEq α] (s : finset α) (a : α) (b : (x : α) → a = x → β) : (finset.sum s fun (x : α) => dite (a = x) (fun (h : a = x) => b x h) fun (h : ¬a = x) => 0) = ite (a ∈ s) (b a rfl) 0 := sorry

@[simp] theorem prod_dite_eq' {α : Type u} {β : Type v} [comm_monoid β] [DecidableEq α] (s : finset α) (a : α) (b : (x : α) → x = a → β) : (finset.prod s fun (x : α) => dite (x = a) (fun (h : x = a) => b x h) fun (h : ¬x = a) => 1) = ite (a ∈ s) (b a rfl) 1 := sorry

@[simp] theorem prod_ite_eq {α : Type u} {β : Type v} [comm_monoid β] [DecidableEq α] (s : finset α) (a : α) (b : α → β) : (finset.prod s fun (x : α) => ite (a = x) (b x) 1) = ite (a ∈ s) (b a) 1 :=
  prod_dite_eq s a fun (x : α) (_x : a = x) => b x

/--
  When a product is taken over a conditional whose condition is an equality test on the index
  and whose alternative is 1, then the product's value is either the term at that index or `1`.

  The difference with `prod_ite_eq` is that the arguments to `eq` are swapped.
-/
@[simp] theorem sum_ite_eq' {α : Type u} {β : Type v} [add_comm_monoid β] [DecidableEq α] (s : finset α) (a : α) (b : α → β) : (finset.sum s fun (x : α) => ite (x = a) (b x) 0) = ite (a ∈ s) (b a) 0 :=
  sum_dite_eq' s a fun (x : α) (_x : x = a) => b x

theorem prod_ite_index {α : Type u} {β : Type v} [comm_monoid β] (p : Prop) [Decidable p] (s : finset α) (t : finset α) (f : α → β) : (finset.prod (ite p s t) fun (x : α) => f x) =
  ite p (finset.prod s fun (x : α) => f x) (finset.prod t fun (x : α) => f x) :=
  apply_ite (fun (s : finset α) => finset.prod s fun (x : α) => f x) p s t

/--
  Reorder a product.

  The difference with `prod_bij'` is that the bijection is specified as a surjective injection,
  rather than by an inverse function.
-/
theorem prod_bij {α : Type u} {β : Type v} {γ : Type w} [comm_monoid β] {s : finset α} {t : finset γ} {f : α → β} {g : γ → β} (i : (a : α) → a ∈ s → γ) (hi : ∀ (a : α) (ha : a ∈ s), i a ha ∈ t) (h : ∀ (a : α) (ha : a ∈ s), f a = g (i a ha)) (i_inj : ∀ (a₁ a₂ : α) (ha₁ : a₁ ∈ s) (ha₂ : a₂ ∈ s), i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂) (i_surj : ∀ (b : γ), b ∈ t → ∃ (a : α), ∃ (ha : a ∈ s), b = i a ha) : (finset.prod s fun (x : α) => f x) = finset.prod t fun (x : γ) => g x :=
  congr_arg multiset.prod (multiset.map_eq_map_of_bij_of_nodup f g (nodup s) (nodup t) i hi h i_inj i_surj)

/--
  Reorder a product.

  The difference with `prod_bij` is that the bijection is specified with an inverse, rather than
  as a surjective injection.
-/
theorem sum_bij' {α : Type u} {β : Type v} {γ : Type w} [add_comm_monoid β] {s : finset α} {t : finset γ} {f : α → β} {g : γ → β} (i : (a : α) → a ∈ s → γ) (hi : ∀ (a : α) (ha : a ∈ s), i a ha ∈ t) (h : ∀ (a : α) (ha : a ∈ s), f a = g (i a ha)) (j : (a : γ) → a ∈ t → α) (hj : ∀ (a : γ) (ha : a ∈ t), j a ha ∈ s) (left_inv : ∀ (a : α) (ha : a ∈ s), j (i a ha) (hi a ha) = a) (right_inv : ∀ (a : γ) (ha : a ∈ t), i (j a ha) (hj a ha) = a) : (finset.sum s fun (x : α) => f x) = finset.sum t fun (x : γ) => g x := sorry

theorem prod_bij_ne_one {α : Type u} {β : Type v} {γ : Type w} [comm_monoid β] {s : finset α} {t : finset γ} {f : α → β} {g : γ → β} (i : (a : α) → a ∈ s → f a ≠ 1 → γ) (hi : ∀ (a : α) (h₁ : a ∈ s) (h₂ : f a ≠ 1), i a h₁ h₂ ∈ t) (i_inj : ∀ (a₁ a₂ : α) (h₁₁ : a₁ ∈ s) (h₁₂ : f a₁ ≠ 1) (h₂₁ : a₂ ∈ s) (h₂₂ : f a₂ ≠ 1), i a₁ h₁₁ h₁₂ = i a₂ h₂₁ h₂₂ → a₁ = a₂) (i_surj : ∀ (b : γ), b ∈ t → g b ≠ 1 → ∃ (a : α), ∃ (h₁ : a ∈ s), ∃ (h₂ : f a ≠ 1), b = i a h₁ h₂) (h : ∀ (a : α) (h₁ : a ∈ s) (h₂ : f a ≠ 1), f a = g (i a h₁ h₂)) : (finset.prod s fun (x : α) => f x) = finset.prod t fun (x : γ) => g x := sorry

theorem nonempty_of_sum_ne_zero {α : Type u} {β : Type v} {s : finset α} {f : α → β} [add_comm_monoid β] (h : (finset.sum s fun (x : α) => f x) ≠ 0) : finset.nonempty s :=
  or.elim (eq_empty_or_nonempty s) (fun (H : s = ∅) => false.elim (h (Eq.symm H ▸ sum_empty))) id

theorem exists_ne_zero_of_sum_ne_zero {α : Type u} {β : Type v} {s : finset α} {f : α → β} [add_comm_monoid β] (h : (finset.sum s fun (x : α) => f x) ≠ 0) : ∃ (a : α), ∃ (H : a ∈ s), f a ≠ 0 := sorry

theorem sum_subset_zero_on_sdiff {α : Type u} {β : Type v} {s₁ : finset α} {s₂ : finset α} {f : α → β} {g : α → β} [add_comm_monoid β] [DecidableEq α] (h : s₁ ⊆ s₂) (hg : ∀ (x : α), x ∈ s₂ \ s₁ → g x = 0) (hfg : ∀ (x : α), x ∈ s₁ → f x = g x) : (finset.sum s₁ fun (i : α) => f i) = finset.sum s₂ fun (i : α) => g i := sorry

theorem sum_range_succ {β : Type u_1} [add_comm_monoid β] (f : ℕ → β) (n : ℕ) : (finset.sum (range (n + 1)) fun (x : ℕ) => f x) = f n + finset.sum (range n) fun (x : ℕ) => f x := sorry

theorem prod_range_succ {β : Type v} [comm_monoid β] (f : ℕ → β) (n : ℕ) : (finset.prod (range (n + 1)) fun (x : ℕ) => f x) = f n * finset.prod (range n) fun (x : ℕ) => f x := sorry

theorem prod_range_succ' {β : Type v} [comm_monoid β] (f : ℕ → β) (n : ℕ) : (finset.prod (range (n + 1)) fun (k : ℕ) => f k) = (finset.prod (range n) fun (k : ℕ) => f (k + 1)) * f 0 := sorry

theorem prod_range_zero {β : Type v} [comm_monoid β] (f : ℕ → β) : (finset.prod (range 0) fun (k : ℕ) => f k) = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl ((finset.prod (range 0) fun (k : ℕ) => f k) = 1)) range_zero))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((finset.prod ∅ fun (k : ℕ) => f k) = 1)) prod_empty)) (Eq.refl 1))

theorem prod_range_one {β : Type v} [comm_monoid β] (f : ℕ → β) : (finset.prod (range 1) fun (k : ℕ) => f k) = f 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl ((finset.prod (range 1) fun (k : ℕ) => f k) = f 0)) range_one)) prod_singleton

theorem sum_range_one {δ : Type u_1} [add_comm_monoid δ] (f : ℕ → δ) : (finset.sum (range 1) fun (k : ℕ) => f k) = f 0 :=
  prod_range_one f

theorem prod_multiset_map_count {α : Type u} [DecidableEq α] (s : multiset α) {M : Type u_1} [comm_monoid M] (f : α → M) : multiset.prod (multiset.map f s) = finset.prod (multiset.to_finset s) fun (m : α) => f m ^ multiset.count m s := sorry

theorem prod_multiset_count {α : Type u} [DecidableEq α] [comm_monoid α] (s : multiset α) : multiset.prod s = finset.prod (multiset.to_finset s) fun (m : α) => m ^ multiset.count m s := sorry

/--
To prove a property of a product, it suffices to prove that
the property is multiplicative and holds on factors.
-/
theorem prod_induction {α : Type u} {s : finset α} {M : Type u_1} [comm_monoid M] (f : α → M) (p : M → Prop) (p_mul : ∀ (a b : M), p a → p b → p (a * b)) (p_one : p 1) (p_s : ∀ (x : α), x ∈ s → p (f x)) : p (finset.prod s fun (x : α) => f x) := sorry

/--
For any product along `{0, ..., n-1}` of a commutative-monoid-valued function, we can verify that
it's equal to a different function just by checking ratios of adjacent terms.
This is a multiplicative discrete analogue of the fundamental theorem of calculus. -/
theorem prod_range_induction {M : Type u_1} [comm_monoid M] (f : ℕ → M) (s : ℕ → M) (h0 : s 0 = 1) (h : ∀ (n : ℕ), s (n + 1) = s n * f n) (n : ℕ) : (finset.prod (range n) fun (k : ℕ) => f k) = s n := sorry

/--
For any sum along `{0, ..., n-1}` of a commutative-monoid-valued function,
we can verify that it's equal to a different function
just by checking differences of adjacent terms.
This is a discrete analogue
of the fundamental theorem of calculus.
-/
theorem sum_range_induction {M : Type u_1} [add_comm_monoid M] (f : ℕ → M) (s : ℕ → M) (h0 : s 0 = 0) (h : ∀ (n : ℕ), s (n + 1) = s n + f n) (n : ℕ) : (finset.sum (range n) fun (k : ℕ) => f k) = s n :=
  prod_range_induction f s h0 h n

/-- A telescoping sum along `{0, ..., n-1}` of an additive commutative group valued function
reduces to the difference of the last and first terms.-/
theorem sum_range_sub {G : Type u_1} [add_comm_group G] (f : ℕ → G) (n : ℕ) : (finset.sum (range n) fun (i : ℕ) => f (i + 1) - f i) = f n - f 0 := sorry

theorem sum_range_sub' {G : Type u_1} [add_comm_group G] (f : ℕ → G) (n : ℕ) : (finset.sum (range n) fun (i : ℕ) => f i - f (i + 1)) = f 0 - f n := sorry

/-- A telescoping product along `{0, ..., n-1}` of a commutative group valued function
reduces to the ratio of the last and first factors.-/
theorem prod_range_div {M : Type u_1} [comm_group M] (f : ℕ → M) (n : ℕ) : (finset.prod (range n) fun (i : ℕ) => f (i + 1) * (f i⁻¹)) = f n * (f 0⁻¹) := sorry

theorem prod_range_div' {M : Type u_1} [comm_group M] (f : ℕ → M) (n : ℕ) : (finset.prod (range n) fun (i : ℕ) => f i * (f (i + 1)⁻¹)) = f 0 * (f n⁻¹) := sorry

/--
A telescoping sum along `{0, ..., n-1}` of an `ℕ`-valued function
reduces to the difference of the last and first terms
when the function we are summing is monotone.
-/
theorem sum_range_sub_of_monotone {f : ℕ → ℕ} (h : monotone f) (n : ℕ) : (finset.sum (range n) fun (i : ℕ) => f (i + 1) - f i) = f n - f 0 := sorry

@[simp] theorem prod_const {α : Type u} {β : Type v} {s : finset α} [comm_monoid β] (b : β) : (finset.prod s fun (x : α) => b) = b ^ card s := sorry

theorem pow_eq_prod_const {β : Type v} [comm_monoid β] (b : β) (n : ℕ) : b ^ n = finset.prod (range n) fun (k : ℕ) => b := sorry

theorem prod_pow {α : Type u} {β : Type v} [comm_monoid β] (s : finset α) (n : ℕ) (f : α → β) : (finset.prod s fun (x : α) => f x ^ n) = (finset.prod s fun (x : α) => f x) ^ n := sorry

-- `to_additive` fails on this lemma, so we prove it manually below

theorem prod_flip {β : Type v} [comm_monoid β] {n : ℕ} (f : ℕ → β) : (finset.prod (range (n + 1)) fun (r : ℕ) => f (n - r)) = finset.prod (range (n + 1)) fun (k : ℕ) => f k := sorry

theorem sum_involution {α : Type u} {β : Type v} [add_comm_monoid β] {s : finset α} {f : α → β} (g : (a : α) → a ∈ s → α) (h : ∀ (a : α) (ha : a ∈ s), f a + f (g a ha) = 0) (g_ne : ∀ (a : α) (ha : a ∈ s), f a ≠ 0 → g a ha ≠ a) (g_mem : ∀ (a : α) (ha : a ∈ s), g a ha ∈ s) (g_inv : ∀ (a : α) (ha : a ∈ s), g (g a ha) (g_mem a ha) = a) : (finset.sum s fun (x : α) => f x) = 0 := sorry

/-- The product of the composition of functions `f` and `g`, is the product
over `b ∈ s.image g` of `f b` to the power of the cardinality of the fibre of `b` -/
theorem prod_comp {α : Type u} {β : Type v} {γ : Type w} [comm_monoid β] [DecidableEq γ] {s : finset α} (f : γ → β) (g : α → γ) : (finset.prod s fun (a : α) => f (g a)) =
  finset.prod (image g s) fun (b : γ) => f b ^ card (filter (fun (a : α) => g a = b) s) := sorry

theorem sum_piecewise {α : Type u} {β : Type v} [add_comm_monoid β] [DecidableEq α] (s : finset α) (t : finset α) (f : α → β) (g : α → β) : (finset.sum s fun (x : α) => piecewise t f g x) =
  (finset.sum (s ∩ t) fun (x : α) => f x) + finset.sum (s \ t) fun (x : α) => g x := sorry

theorem sum_inter_add_sum_diff {α : Type u} {β : Type v} [add_comm_monoid β] [DecidableEq α] (s : finset α) (t : finset α) (f : α → β) : ((finset.sum (s ∩ t) fun (x : α) => f x) + finset.sum (s \ t) fun (x : α) => f x) = finset.sum s fun (x : α) => f x := sorry

theorem mul_prod_diff_singleton {α : Type u} {β : Type v} [comm_monoid β] [DecidableEq α] {s : finset α} {i : α} (h : i ∈ s) (f : α → β) : (f i * finset.prod (s \ singleton i) fun (x : α) => f x) = finset.prod s fun (x : α) => f x := sorry

/-- A product can be partitioned into a product of products, each equivalent under a setoid. -/
theorem sum_partition {α : Type u} {β : Type v} {s : finset α} {f : α → β} [add_comm_monoid β] (R : setoid α) [DecidableRel setoid.r] : (finset.sum s fun (x : α) => f x) =
  finset.sum (image quotient.mk s)
    fun (xbar : quotient R) => finset.sum (filter (fun (y : α) => quotient.mk y = xbar) s) fun (x : α) => f x := sorry

/-- If we can partition a product into subsets that cancel out, then the whole product cancels. -/
theorem prod_cancels_of_partition_cancels {α : Type u} {β : Type v} {s : finset α} {f : α → β} [comm_monoid β] (R : setoid α) [DecidableRel setoid.r] (h : ∀ (x : α), x ∈ s → (finset.prod (filter (fun (y : α) => y ≈ x) s) fun (a : α) => f a) = 1) : (finset.prod s fun (a : α) => f a) = 1 := sorry

theorem sum_update_of_not_mem {α : Type u} {β : Type v} [add_comm_monoid β] [DecidableEq α] {s : finset α} {i : α} (h : ¬i ∈ s) (f : α → β) (b : β) : (finset.sum s fun (x : α) => function.update f i b x) = finset.sum s fun (x : α) => f x := sorry

theorem prod_update_of_mem {α : Type u} {β : Type v} [comm_monoid β] [DecidableEq α] {s : finset α} {i : α} (h : i ∈ s) (f : α → β) (b : β) : (finset.prod s fun (x : α) => function.update f i b x) = b * finset.prod (s \ singleton i) fun (x : α) => f x := sorry

/-- If a product of a `finset` of size at most 1 has a given value, so
do the terms in that product. -/
theorem eq_of_card_le_one_of_prod_eq {α : Type u} {β : Type v} [comm_monoid β] {s : finset α} (hc : card s ≤ 1) {f : α → β} {b : β} (h : (finset.prod s fun (x : α) => f x) = b) (x : α) (H : x ∈ s) : f x = b := sorry

/-- If a sum of a `finset` of size at most 1 has a given value, so do
the terms in that sum. -/
theorem eq_of_card_le_one_of_sum_eq {α : Type u} {γ : Type w} [add_comm_monoid γ] {s : finset α} (hc : card s ≤ 1) {f : α → γ} {b : γ} (h : (finset.sum s fun (x : α) => f x) = b) (x : α) (H : x ∈ s) : f x = b := sorry

/-- If a function applied at a point is 1, a product is unchanged by
removing that point, if present, from a `finset`. -/
theorem prod_erase {α : Type u} {β : Type v} [comm_monoid β] [DecidableEq α] (s : finset α) {f : α → β} {a : α} (h : f a = 1) : (finset.prod (erase s a) fun (x : α) => f x) = finset.prod s fun (x : α) => f x := sorry

/-- If a product is 1 and the function is 1 except possibly at one
point, it is 1 everywhere on the `finset`. -/
theorem eq_one_of_prod_eq_one {α : Type u} {β : Type v} [comm_monoid β] {s : finset α} {f : α → β} {a : α} (hp : (finset.prod s fun (x : α) => f x) = 1) (h1 : ∀ (x : α), x ∈ s → x ≠ a → f x = 1) (x : α) (H : x ∈ s) : f x = 1 := sorry

theorem prod_pow_boole {α : Type u} {β : Type v} [comm_monoid β] [DecidableEq α] (s : finset α) (f : α → β) (a : α) : (finset.prod s fun (x : α) => f x ^ ite (a = x) 1 0) = ite (a ∈ s) (f a) 1 := sorry

/-- If `f = g = h` everywhere but at `i`, where `f i = g i + h i`, then the product of `f` over `s`
  is the sum of the products of `g` and `h`. -/
theorem prod_add_prod_eq {α : Type u} {β : Type v} [comm_semiring β] {s : finset α} {i : α} {f : α → β} {g : α → β} {h : α → β} (hi : i ∈ s) (h1 : g i + h i = f i) (h2 : ∀ (j : α), j ∈ s → j ≠ i → g j = f j) (h3 : ∀ (j : α), j ∈ s → j ≠ i → h j = f j) : ((finset.prod s fun (i : α) => g i) + finset.prod s fun (i : α) => h i) = finset.prod s fun (i : α) => f i := sorry

theorem sum_update_of_mem {α : Type u} {β : Type v} [add_comm_monoid β] [DecidableEq α] {s : finset α} {i : α} (h : i ∈ s) (f : α → β) (b : β) : (finset.sum s fun (x : α) => function.update f i b x) = b + finset.sum (s \ singleton i) fun (x : α) => f x := sorry

theorem sum_nsmul {α : Type u} {β : Type v} [add_comm_monoid β] (s : finset α) (n : ℕ) (f : α → β) : (finset.sum s fun (x : α) => n •ℕ f x) = n •ℕ finset.sum s fun (x : α) => f x :=
  prod_pow s n fun (x : α) => f x

@[simp] theorem sum_const {α : Type u} {β : Type v} {s : finset α} [add_comm_monoid β] (b : β) : (finset.sum s fun (x : α) => b) = card s •ℕ b :=
  prod_const b

theorem card_eq_sum_ones {α : Type u} (s : finset α) : card s = finset.sum s fun (_x : α) => 1 := sorry

theorem sum_const_nat {α : Type u} {s : finset α} {m : ℕ} {f : α → ℕ} (h₁ : ∀ (x : α), x ∈ s → f x = m) : (finset.sum s fun (x : α) => f x) = card s * m := sorry

@[simp] theorem sum_boole {α : Type u} {β : Type v} {s : finset α} {p : α → Prop} [semiring β] {hp : decidable_pred p} : (finset.sum s fun (x : α) => ite (p x) 1 0) = ↑(card (filter p s)) := sorry

theorem sum_nat_cast {α : Type u} {β : Type v} [add_comm_monoid β] [HasOne β] (s : finset α) (f : α → ℕ) : ↑(finset.sum s fun (x : α) => f x) = finset.sum s fun (x : α) => ↑(f x) :=
  add_monoid_hom.map_sum (nat.cast_add_monoid_hom β) f s

theorem sum_int_cast {α : Type u} {β : Type v} [add_comm_group β] [HasOne β] (s : finset α) (f : α → ℤ) : ↑(finset.sum s fun (x : α) => f x) = finset.sum s fun (x : α) => ↑(f x) :=
  add_monoid_hom.map_sum (int.cast_add_hom β) f s

theorem sum_comp {α : Type u} {β : Type v} {γ : Type w} [add_comm_monoid β] [DecidableEq γ] {s : finset α} (f : γ → β) (g : α → γ) : (finset.sum s fun (a : α) => f (g a)) =
  finset.sum (image g s) fun (b : γ) => card (filter (fun (a : α) => g a = b) s) •ℕ f b :=
  prod_comp f fun (a : α) => g a

theorem sum_range_succ' {β : Type v} [add_comm_monoid β] (f : ℕ → β) (n : ℕ) : (finset.sum (range (n + 1)) fun (i : ℕ) => f i) = (finset.sum (range n) fun (i : ℕ) => f (i + 1)) + f 0 :=
  prod_range_succ' fun (k : ℕ) => f k

theorem sum_flip {β : Type v} [add_comm_monoid β] {n : ℕ} (f : ℕ → β) : (finset.sum (range (n + 1)) fun (i : ℕ) => f (n - i)) = finset.sum (range (n + 1)) fun (i : ℕ) => f i :=
  prod_flip f

/-- Moving to the opposite additive commutative monoid commutes with summing. -/
@[simp] theorem op_sum {α : Type u} {β : Type v} [add_comm_monoid β] {s : finset α} (f : α → β) : opposite.op (finset.sum s fun (x : α) => f x) = finset.sum s fun (x : α) => opposite.op (f x) :=
  add_equiv.map_sum opposite.op_add_equiv (fun (x : α) => f x) s

@[simp] theorem unop_sum {α : Type u} {β : Type v} [add_comm_monoid β] {s : finset α} (f : α → (βᵒᵖ)) : opposite.unop (finset.sum s fun (x : α) => f x) = finset.sum s fun (x : α) => opposite.unop (f x) :=
  add_equiv.map_sum (add_equiv.symm opposite.op_add_equiv) (fun (x : α) => f x) s

@[simp] theorem sum_neg_distrib {α : Type u} {β : Type v} {s : finset α} {f : α → β} [add_comm_group β] : (finset.sum s fun (x : α) => -f x) = -finset.sum s fun (x : α) => f x :=
  sum_hom s Neg.neg

@[simp] theorem card_sigma {α : Type u} {σ : α → Type u_1} (s : finset α) (t : (a : α) → finset (σ a)) : card (finset.sigma s t) = finset.sum s fun (a : α) => card (t a) :=
  multiset.card_sigma (val s) fun (a : α) => (fun (a : α) => val (t a)) a

theorem card_bUnion {α : Type u} {β : Type v} [DecidableEq β] {s : finset α} {t : α → finset β} (h : ∀ (x : α), x ∈ s → ∀ (y : α), y ∈ s → x ≠ y → disjoint (t x) (t y)) : card (finset.bUnion s t) = finset.sum s fun (u : α) => card (t u) := sorry

theorem card_bUnion_le {α : Type u} {β : Type v} [DecidableEq β] {s : finset α} {t : α → finset β} : card (finset.bUnion s t) ≤ finset.sum s fun (a : α) => card (t a) := sorry

theorem card_eq_sum_card_fiberwise {α : Type u} {β : Type v} [DecidableEq β] {f : α → β} {s : finset α} {t : finset β} (H : ∀ (x : α), x ∈ s → f x ∈ t) : card s = finset.sum t fun (a : β) => card (filter (fun (x : α) => f x = a) s) := sorry

theorem card_eq_sum_card_image {α : Type u} {β : Type v} [DecidableEq β] (f : α → β) (s : finset α) : card s = finset.sum (image f s) fun (a : β) => card (filter (fun (x : α) => f x = a) s) :=
  card_eq_sum_card_fiberwise fun (_x : α) => mem_image_of_mem fun (x : α) => f x

theorem gsmul_sum {α : Type u} {β : Type v} [add_comm_group β] {f : α → β} {s : finset α} (z : ℤ) : (z •ℤ finset.sum s fun (a : α) => f a) = finset.sum s fun (a : α) => z •ℤ f a :=
  Eq.symm (sum_hom s (gsmul z))

@[simp] theorem sum_sub_distrib {α : Type u} {β : Type v} {s : finset α} {f : α → β} {g : α → β} [add_comm_group β] : (finset.sum s fun (x : α) => f x - g x) = (finset.sum s fun (x : α) => f x) - finset.sum s fun (x : α) => g x := sorry

theorem prod_eq_zero {α : Type u} {β : Type v} {s : finset α} {a : α} {f : α → β} [comm_monoid_with_zero β] (ha : a ∈ s) (h : f a = 0) : (finset.prod s fun (x : α) => f x) = 0 := sorry

theorem prod_boole {α : Type u} {β : Type v} [comm_monoid_with_zero β] {s : finset α} {p : α → Prop} [decidable_pred p] : (finset.prod s fun (i : α) => ite (p i) 1 0) = ite (∀ (i : α), i ∈ s → p i) 1 0 := sorry

theorem prod_eq_zero_iff {α : Type u} {β : Type v} {s : finset α} {f : α → β} [comm_monoid_with_zero β] [nontrivial β] [no_zero_divisors β] : (finset.prod s fun (x : α) => f x) = 0 ↔ ∃ (a : α), ∃ (H : a ∈ s), f a = 0 := sorry

theorem prod_ne_zero_iff {α : Type u} {β : Type v} {s : finset α} {f : α → β} [comm_monoid_with_zero β] [nontrivial β] [no_zero_divisors β] : (finset.prod s fun (x : α) => f x) ≠ 0 ↔ ∀ (a : α), a ∈ s → f a ≠ 0 := sorry

@[simp] theorem prod_inv_distrib' {α : Type u} {β : Type v} {s : finset α} {f : α → β} [comm_group_with_zero β] : (finset.prod s fun (x : α) => f x⁻¹) = ((finset.prod s fun (x : α) => f x)⁻¹) := sorry

end finset


namespace list


theorem prod_to_finset {α : Type u} {M : Type u_1} [DecidableEq α] [comm_monoid M] (f : α → M) {l : List α} (hl : nodup l) : finset.prod (to_finset l) f = prod (map f l) := sorry

end list


namespace multiset


@[simp] theorem to_finset_sum_count_eq {α : Type u} [DecidableEq α] (s : multiset α) : (finset.sum (to_finset s) fun (a : α) => count a s) = coe_fn card s := sorry

theorem count_sum' {α : Type u} {β : Type v} [DecidableEq α] {s : finset β} {a : α} {f : β → multiset α} : count a (finset.sum s fun (x : β) => f x) = finset.sum s fun (x : β) => count a (f x) := sorry

@[simp] theorem to_finset_sum_count_smul_eq {α : Type u} [DecidableEq α] (s : multiset α) : (finset.sum (to_finset s) fun (a : α) => count a s •ℕ (a ::ₘ 0)) = s := sorry

theorem exists_smul_of_dvd_count {α : Type u} [DecidableEq α] (s : multiset α) {k : ℕ} (h : ∀ (a : α), k ∣ count a s) : ∃ (u : multiset α), s = k •ℕ u := sorry

end multiset


@[simp] theorem nat.coe_prod {α : Type u} {R : Type u_1} [comm_semiring R] (f : α → ℕ) (s : finset α) : ↑(finset.prod s fun (i : α) => f i) = finset.prod s fun (i : α) => ↑(f i) :=
  ring_hom.map_prod (nat.cast_ring_hom R) (fun (i : α) => f i) s

@[simp] theorem int.coe_prod {α : Type u} {R : Type u_1} [comm_ring R] (f : α → ℤ) (s : finset α) : ↑(finset.prod s fun (i : α) => f i) = finset.prod s fun (i : α) => ↑(f i) :=
  ring_hom.map_prod (int.cast_ring_hom R) (fun (i : α) => f i) s

@[simp] theorem units.coe_prod {α : Type u} {M : Type u_1} [comm_monoid M] (f : α → units M) (s : finset α) : ↑(finset.prod s fun (i : α) => f i) = finset.prod s fun (i : α) => ↑(f i) :=
  monoid_hom.map_prod (units.coe_hom M) (fun (i : α) => f i) s

