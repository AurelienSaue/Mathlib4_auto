/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.measure_theory.measure_space
import Mathlib.measure_theory.borel_space
import Mathlib.data.indicator_function
import Mathlib.data.support
import PostPort

universes u v l u_1 u_2 u_3 u_4 u_5 

namespace Mathlib

/-!
# Lebesgue integral for `ennreal`-valued functions

We define simple functions and show that each Borel measurable function on `ennreal` can be
approximated by a sequence of simple functions.

To prove something for an arbitrary measurable function into `ennreal`, the theorem
`measurable.ennreal_induction` shows that is it sufficient to show that the property holds for
(multiples of) characteristic functions and is closed under addition and supremum of increasing
sequences of functions.

## Notation

We introduce the following notation for the lower Lebesgue integral of a function `f : α → ennreal`.

* `∫⁻ x, f x ∂μ`: integral of a function `f : α → ennreal` with respect to a measure `μ`;
* `∫⁻ x, f x`: integral of a function `f : α → ennreal` with respect to the canonical measure
  `volume` on `α`;
* `∫⁻ x in s, f x ∂μ`: integral of a function `f : α → ennreal` over a set `s` with respect
  to a measure `μ`, defined as `∫⁻ x, f x ∂(μ.restrict s)`;
* `∫⁻ x in s, f x`: integral of a function `f : α → ennreal` over a set `s` with respect
  to the canonical measure `volume`, defined as `∫⁻ x, f x ∂(volume.restrict s)`.

-/

namespace measure_theory


/-- A function `f` from a measurable space to any type is called *simple*,
if every preimage `f ⁻¹' {x}` is measurable, and the range is finite. This structure bundles
a function with these properties. -/
structure simple_func (α : Type u) [measurable_space α] (β : Type v) 
where
  to_fun : α → β
  is_measurable_fiber' : ∀ (x : β), is_measurable (to_fun ⁻¹' singleton x)
  finite_range' : set.finite (set.range to_fun)

namespace simple_func


protected instance has_coe_to_fun {α : Type u_1} {β : Type u_2} [measurable_space α] : has_coe_to_fun (simple_func α β) :=
  has_coe_to_fun.mk (fun (x : simple_func α β) => α → β) to_fun

theorem coe_injective {α : Type u_1} {β : Type u_2} [measurable_space α] {f : simple_func α β} {g : simple_func α β} (H : ⇑f = ⇑g) : f = g := sorry

theorem ext {α : Type u_1} {β : Type u_2} [measurable_space α] {f : simple_func α β} {g : simple_func α β} (H : ∀ (a : α), coe_fn f a = coe_fn g a) : f = g :=
  coe_injective (funext H)

theorem finite_range {α : Type u_1} {β : Type u_2} [measurable_space α] (f : simple_func α β) : set.finite (set.range ⇑f) :=
  finite_range' f

theorem is_measurable_fiber {α : Type u_1} {β : Type u_2} [measurable_space α] (f : simple_func α β) (x : β) : is_measurable (⇑f ⁻¹' singleton x) :=
  is_measurable_fiber' f x

/-- Range of a simple function `α →ₛ β` as a `finset β`. -/
protected def range {α : Type u_1} {β : Type u_2} [measurable_space α] (f : simple_func α β) : finset β :=
  set.finite.to_finset (finite_range f)

@[simp] theorem mem_range {α : Type u_1} {β : Type u_2} [measurable_space α] {f : simple_func α β} {b : β} : b ∈ simple_func.range f ↔ b ∈ set.range ⇑f :=
  set.finite.mem_to_finset

theorem mem_range_self {α : Type u_1} {β : Type u_2} [measurable_space α] (f : simple_func α β) (x : α) : coe_fn f x ∈ simple_func.range f :=
  iff.mpr mem_range (Exists.intro x rfl)

@[simp] theorem coe_range {α : Type u_1} {β : Type u_2} [measurable_space α] (f : simple_func α β) : ↑(simple_func.range f) = set.range ⇑f :=
  set.finite.coe_to_finset (finite_range f)

theorem mem_range_of_measure_ne_zero {α : Type u_1} {β : Type u_2} [measurable_space α] {f : simple_func α β} {x : β} {μ : measure α} (H : coe_fn μ (⇑f ⁻¹' singleton x) ≠ 0) : x ∈ simple_func.range f := sorry

theorem forall_range_iff {α : Type u_1} {β : Type u_2} [measurable_space α] {f : simple_func α β} {p : β → Prop} : (∀ (y : β), y ∈ simple_func.range f → p y) ↔ ∀ (x : α), p (coe_fn f x) := sorry

theorem exists_range_iff {α : Type u_1} {β : Type u_2} [measurable_space α] {f : simple_func α β} {p : β → Prop} : (∃ (y : β), ∃ (H : y ∈ simple_func.range f), p y) ↔ ∃ (x : α), p (coe_fn f x) := sorry

theorem preimage_eq_empty_iff {α : Type u_1} {β : Type u_2} [measurable_space α] (f : simple_func α β) (b : β) : ⇑f ⁻¹' singleton b = ∅ ↔ ¬b ∈ simple_func.range f :=
  iff.trans set.preimage_singleton_eq_empty (not_congr (iff.symm mem_range))

theorem exists_forall_le {α : Type u_1} {β : Type u_2} [measurable_space α] [Nonempty β] [directed_order β] (f : simple_func α β) : ∃ (C : β), ∀ (x : α), coe_fn f x ≤ C :=
  Exists.imp (fun (C : β) => iff.mp forall_range_iff) (finset.exists_le (simple_func.range f))

/-- Constant function as a `simple_func`. -/
def const (α : Type u_1) {β : Type u_2} [measurable_space α] (b : β) : simple_func α β :=
  mk (fun (a : α) => b) sorry set.finite_range_const

protected instance inhabited {α : Type u_1} {β : Type u_2} [measurable_space α] [Inhabited β] : Inhabited (simple_func α β) :=
  { default := const α Inhabited.default }

theorem const_apply {α : Type u_1} {β : Type u_2} [measurable_space α] (a : α) (b : β) : coe_fn (const α b) a = b :=
  rfl

@[simp] theorem coe_const {α : Type u_1} {β : Type u_2} [measurable_space α] (b : β) : ⇑(const α b) = function.const α b :=
  rfl

@[simp] theorem range_const {β : Type u_2} (α : Type u_1) [measurable_space α] [Nonempty α] (b : β) : simple_func.range (const α b) = singleton b := sorry

theorem is_measurable_cut {α : Type u_1} {β : Type u_2} [measurable_space α] (r : α → β → Prop) (f : simple_func α β) (h : ∀ (b : β), is_measurable (set_of fun (a : α) => r a b)) : is_measurable (set_of fun (a : α) => r a (coe_fn f a)) := sorry

theorem is_measurable_preimage {α : Type u_1} {β : Type u_2} [measurable_space α] (f : simple_func α β) (s : set β) : is_measurable (⇑f ⁻¹' s) :=
  is_measurable_cut (fun (_x : α) (b : β) => b ∈ s) f fun (b : β) => is_measurable.const (b ∈ s)

/-- A simple function is measurable -/
protected theorem measurable {α : Type u_1} {β : Type u_2} [measurable_space α] [measurable_space β] (f : simple_func α β) : measurable ⇑f :=
  fun (s : set β) (_x : is_measurable s) => is_measurable_preimage f s

protected theorem ae_measurable {α : Type u_1} {β : Type u_2} [measurable_space α] [measurable_space β] {μ : measure α} (f : simple_func α β) : ae_measurable ⇑f :=
  measurable.ae_measurable (simple_func.measurable f)

protected theorem sum_measure_preimage_singleton {α : Type u_1} {β : Type u_2} [measurable_space α] (f : simple_func α β) {μ : measure α} (s : finset β) : (finset.sum s fun (y : β) => coe_fn μ (⇑f ⁻¹' singleton y)) = coe_fn μ (⇑f ⁻¹' ↑s) :=
  sum_measure_preimage_singleton s fun (_x : β) (_x_1 : _x ∈ s) => is_measurable_fiber f _x

theorem sum_range_measure_preimage_singleton {α : Type u_1} {β : Type u_2} [measurable_space α] (f : simple_func α β) (μ : measure α) : (finset.sum (simple_func.range f) fun (y : β) => coe_fn μ (⇑f ⁻¹' singleton y)) = coe_fn μ set.univ := sorry

/-- If-then-else as a `simple_func`. -/
def piecewise {α : Type u_1} {β : Type u_2} [measurable_space α] (s : set α) (hs : is_measurable s) (f : simple_func α β) (g : simple_func α β) : simple_func α β :=
  mk (set.piecewise s ⇑f ⇑g) sorry sorry

@[simp] theorem coe_piecewise {α : Type u_1} {β : Type u_2} [measurable_space α] {s : set α} (hs : is_measurable s) (f : simple_func α β) (g : simple_func α β) : ⇑(piecewise s hs f g) = set.piecewise s ⇑f ⇑g :=
  rfl

theorem piecewise_apply {α : Type u_1} {β : Type u_2} [measurable_space α] {s : set α} (hs : is_measurable s) (f : simple_func α β) (g : simple_func α β) (a : α) : coe_fn (piecewise s hs f g) a = ite (a ∈ s) (coe_fn f a) (coe_fn g a) :=
  rfl

@[simp] theorem piecewise_compl {α : Type u_1} {β : Type u_2} [measurable_space α] {s : set α} (hs : is_measurable (sᶜ)) (f : simple_func α β) (g : simple_func α β) : piecewise (sᶜ) hs f g = piecewise s (is_measurable.of_compl hs) g f := sorry

@[simp] theorem piecewise_univ {α : Type u_1} {β : Type u_2} [measurable_space α] (f : simple_func α β) (g : simple_func α β) : piecewise set.univ is_measurable.univ f g = f := sorry

@[simp] theorem piecewise_empty {α : Type u_1} {β : Type u_2} [measurable_space α] (f : simple_func α β) (g : simple_func α β) : piecewise ∅ is_measurable.empty f g = g := sorry

theorem measurable_bind {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] [measurable_space γ] (f : simple_func α β) (g : β → α → γ) (hg : ∀ (b : β), measurable (g b)) : measurable fun (a : α) => g (coe_fn f a) a :=
  fun (s : set γ) (hs : is_measurable s) => is_measurable_cut (fun (a : α) (b : β) => g b a ∈ s) f fun (b : β) => hg b hs

/-- If `f : α →ₛ β` is a simple function and `g : β → α →ₛ γ` is a family of simple functions,
then `f.bind g` binds the first argument of `g` to `f`. In other words, `f.bind g a = g (f a) a`. -/
def bind {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] (f : simple_func α β) (g : β → simple_func α γ) : simple_func α γ :=
  mk (fun (a : α) => coe_fn (g (coe_fn f a)) a) sorry sorry

@[simp] theorem bind_apply {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] (f : simple_func α β) (g : β → simple_func α γ) (a : α) : coe_fn (bind f g) a = coe_fn (g (coe_fn f a)) a :=
  rfl

/-- Given a function `g : β → γ` and a simple function `f : α →ₛ β`, `f.map g` return the simple
    function `g ∘ f : α →ₛ γ` -/
def map {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] (g : β → γ) (f : simple_func α β) : simple_func α γ :=
  bind f (const α ∘ g)

theorem map_apply {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] (g : β → γ) (f : simple_func α β) (a : α) : coe_fn (map g f) a = g (coe_fn f a) :=
  rfl

theorem map_map {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} [measurable_space α] (g : β → γ) (h : γ → δ) (f : simple_func α β) : map h (map g f) = map (h ∘ g) f :=
  rfl

@[simp] theorem coe_map {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] (g : β → γ) (f : simple_func α β) : ⇑(map g f) = g ∘ ⇑f :=
  rfl

@[simp] theorem range_map {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] [DecidableEq γ] (g : β → γ) (f : simple_func α β) : simple_func.range (map g f) = finset.image g (simple_func.range f) := sorry

@[simp] theorem map_const {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] (g : β → γ) (b : β) : map g (const α b) = const α (g b) :=
  rfl

theorem map_preimage {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] (f : simple_func α β) (g : β → γ) (s : set γ) : ⇑(map g f) ⁻¹' s = ⇑f ⁻¹' ↑(finset.filter (fun (b : β) => g b ∈ s) (simple_func.range f)) := sorry

theorem map_preimage_singleton {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] (f : simple_func α β) (g : β → γ) (c : γ) : ⇑(map g f) ⁻¹' singleton c = ⇑f ⁻¹' ↑(finset.filter (fun (b : β) => g b = c) (simple_func.range f)) :=
  map_preimage f g (singleton c)

/-- Composition of a `simple_fun` and a measurable function is a `simple_func`. -/
def comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] [measurable_space β] (f : simple_func β γ) (g : α → β) (hgm : measurable g) : simple_func α γ :=
  mk (⇑f ∘ g) sorry sorry

@[simp] theorem coe_comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] [measurable_space β] (f : simple_func β γ) {g : α → β} (hgm : measurable g) : ⇑(comp f g hgm) = ⇑f ∘ g :=
  rfl

theorem range_comp_subset_range {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] [measurable_space β] (f : simple_func β γ) {g : α → β} (hgm : measurable g) : simple_func.range (comp f g hgm) ⊆ simple_func.range f := sorry

/-- If `f` is a simple function taking values in `β → γ` and `g` is another simple function
with the same domain and codomain `β`, then `f.seq g = f a (g a)`. -/
def seq {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] (f : simple_func α (β → γ)) (g : simple_func α β) : simple_func α γ :=
  bind f fun (f : β → γ) => map f g

@[simp] theorem seq_apply {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] (f : simple_func α (β → γ)) (g : simple_func α β) (a : α) : coe_fn (seq f g) a = coe_fn f a (coe_fn g a) :=
  rfl

/-- Combine two simple functions `f : α →ₛ β` and `g : α →ₛ β`
into `λ a, (f a, g a)`. -/
def pair {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] (f : simple_func α β) (g : simple_func α γ) : simple_func α (β × γ) :=
  seq (map Prod.mk f) g

@[simp] theorem pair_apply {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] (f : simple_func α β) (g : simple_func α γ) (a : α) : coe_fn (pair f g) a = (coe_fn f a, coe_fn g a) :=
  rfl

theorem pair_preimage {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] (f : simple_func α β) (g : simple_func α γ) (s : set β) (t : set γ) : ⇑(pair f g) ⁻¹' set.prod s t = ⇑f ⁻¹' s ∩ ⇑g ⁻¹' t :=
  rfl

/- A special form of `pair_preimage` -/

theorem pair_preimage_singleton {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] (f : simple_func α β) (g : simple_func α γ) (b : β) (c : γ) : ⇑(pair f g) ⁻¹' singleton (b, c) = ⇑f ⁻¹' singleton b ∩ ⇑g ⁻¹' singleton c := sorry

theorem bind_const {α : Type u_1} {β : Type u_2} [measurable_space α] (f : simple_func α β) : bind f (const α) = f := sorry

protected instance has_zero {α : Type u_1} {β : Type u_2} [measurable_space α] [HasZero β] : HasZero (simple_func α β) :=
  { zero := const α 0 }

protected instance has_add {α : Type u_1} {β : Type u_2} [measurable_space α] [Add β] : Add (simple_func α β) :=
  { add := fun (f g : simple_func α β) => seq (map Add.add f) g }

protected instance has_mul {α : Type u_1} {β : Type u_2} [measurable_space α] [Mul β] : Mul (simple_func α β) :=
  { mul := fun (f g : simple_func α β) => seq (map Mul.mul f) g }

protected instance has_sup {α : Type u_1} {β : Type u_2} [measurable_space α] [has_sup β] : has_sup (simple_func α β) :=
  has_sup.mk fun (f g : simple_func α β) => seq (map has_sup.sup f) g

protected instance has_inf {α : Type u_1} {β : Type u_2} [measurable_space α] [has_inf β] : has_inf (simple_func α β) :=
  has_inf.mk fun (f g : simple_func α β) => seq (map has_inf.inf f) g

protected instance has_le {α : Type u_1} {β : Type u_2} [measurable_space α] [HasLessEq β] : HasLessEq (simple_func α β) :=
  { LessEq := fun (f g : simple_func α β) => ∀ (a : α), coe_fn f a ≤ coe_fn g a }

@[simp] theorem coe_zero {α : Type u_1} {β : Type u_2} [measurable_space α] [HasZero β] : ⇑0 = 0 :=
  rfl

@[simp] theorem const_zero {α : Type u_1} {β : Type u_2} [measurable_space α] [HasZero β] : const α 0 = 0 :=
  rfl

@[simp] theorem coe_add {α : Type u_1} {β : Type u_2} [measurable_space α] [Add β] (f : simple_func α β) (g : simple_func α β) : ⇑(f + g) = ⇑f + ⇑g :=
  rfl

@[simp] theorem coe_mul {α : Type u_1} {β : Type u_2} [measurable_space α] [Mul β] (f : simple_func α β) (g : simple_func α β) : ⇑(f * g) = ⇑f * ⇑g :=
  rfl

@[simp] theorem coe_le {α : Type u_1} {β : Type u_2} [measurable_space α] [preorder β] {f : simple_func α β} {g : simple_func α β} : ⇑f ≤ ⇑g ↔ f ≤ g :=
  iff.rfl

@[simp] theorem range_zero {α : Type u_1} {β : Type u_2} [measurable_space α] [Nonempty α] [HasZero β] : simple_func.range 0 = singleton 0 := sorry

theorem eq_zero_of_mem_range_zero {α : Type u_1} {β : Type u_2} [measurable_space α] [HasZero β] {y : β} : y ∈ simple_func.range 0 → y = 0 :=
  iff.mpr forall_range_iff fun (x : α) => rfl

theorem sup_apply {α : Type u_1} {β : Type u_2} [measurable_space α] [has_sup β] (f : simple_func α β) (g : simple_func α β) (a : α) : coe_fn (f ⊔ g) a = coe_fn f a ⊔ coe_fn g a :=
  rfl

theorem mul_apply {α : Type u_1} {β : Type u_2} [measurable_space α] [Mul β] (f : simple_func α β) (g : simple_func α β) (a : α) : coe_fn (f * g) a = coe_fn f a * coe_fn g a :=
  rfl

theorem add_apply {α : Type u_1} {β : Type u_2} [measurable_space α] [Add β] (f : simple_func α β) (g : simple_func α β) (a : α) : coe_fn (f + g) a = coe_fn f a + coe_fn g a :=
  rfl

theorem add_eq_map₂ {α : Type u_1} {β : Type u_2} [measurable_space α] [Add β] (f : simple_func α β) (g : simple_func α β) : f + g = map (fun (p : β × β) => prod.fst p + prod.snd p) (pair f g) :=
  rfl

theorem mul_eq_map₂ {α : Type u_1} {β : Type u_2} [measurable_space α] [Mul β] (f : simple_func α β) (g : simple_func α β) : f * g = map (fun (p : β × β) => prod.fst p * prod.snd p) (pair f g) :=
  rfl

theorem sup_eq_map₂ {α : Type u_1} {β : Type u_2} [measurable_space α] [has_sup β] (f : simple_func α β) (g : simple_func α β) : f ⊔ g = map (fun (p : β × β) => prod.fst p ⊔ prod.snd p) (pair f g) :=
  rfl

theorem const_mul_eq_map {α : Type u_1} {β : Type u_2} [measurable_space α] [Mul β] (f : simple_func α β) (b : β) : const α b * f = map (fun (a : β) => b * a) f :=
  rfl

theorem map_add {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] [Add β] [Add γ] {g : β → γ} (hg : ∀ (x y : β), g (x + y) = g x + g y) (f₁ : simple_func α β) (f₂ : simple_func α β) : map g (f₁ + f₂) = map g f₁ + map g f₂ :=
  ext fun (x : α) => hg (coe_fn f₁ x) (coe_fn f₂ x)

protected instance add_monoid {α : Type u_1} {β : Type u_2} [measurable_space α] [add_monoid β] : add_monoid (simple_func α β) :=
  function.injective.add_monoid (fun (f : simple_func α β) => (fun (this : α → β) => this) ⇑f) coe_injective sorry sorry

protected instance add_comm_monoid {α : Type u_1} {β : Type u_2} [measurable_space α] [add_comm_monoid β] : add_comm_monoid (simple_func α β) :=
  function.injective.add_comm_monoid (fun (f : simple_func α β) => (fun (this : α → β) => this) ⇑f) coe_injective sorry
    sorry

protected instance has_neg {α : Type u_1} {β : Type u_2} [measurable_space α] [Neg β] : Neg (simple_func α β) :=
  { neg := fun (f : simple_func α β) => map Neg.neg f }

@[simp] theorem coe_neg {α : Type u_1} {β : Type u_2} [measurable_space α] [Neg β] (f : simple_func α β) : ⇑(-f) = -⇑f :=
  rfl

protected instance has_sub {α : Type u_1} {β : Type u_2} [measurable_space α] [Sub β] : Sub (simple_func α β) :=
  { sub := fun (f g : simple_func α β) => seq (map Sub.sub f) g }

@[simp] theorem coe_sub {α : Type u_1} {β : Type u_2} [measurable_space α] [Sub β] (f : simple_func α β) (g : simple_func α β) : ⇑(f - g) = ⇑f - ⇑g :=
  rfl

theorem sub_apply {α : Type u_1} {β : Type u_2} [measurable_space α] [Sub β] (f : simple_func α β) (g : simple_func α β) (x : α) : coe_fn (f - g) x = coe_fn f x - coe_fn g x :=
  rfl

protected instance add_group {α : Type u_1} {β : Type u_2} [measurable_space α] [add_group β] : add_group (simple_func α β) :=
  function.injective.add_group_sub (fun (f : simple_func α β) => (fun (this : α → β) => this) ⇑f) coe_injective sorry
    sorry sorry sorry

protected instance add_comm_group {α : Type u_1} {β : Type u_2} [measurable_space α] [add_comm_group β] : add_comm_group (simple_func α β) :=
  function.injective.add_comm_group_sub (fun (f : simple_func α β) => (fun (this : α → β) => this) ⇑f) coe_injective sorry
    sorry sorry sorry

protected instance has_scalar {α : Type u_1} {β : Type u_2} [measurable_space α] {K : Type u_5} [has_scalar K β] : has_scalar K (simple_func α β) :=
  has_scalar.mk fun (k : K) (f : simple_func α β) => map (has_scalar.smul k) f

@[simp] theorem coe_smul {α : Type u_1} {β : Type u_2} [measurable_space α] {K : Type u_5} [has_scalar K β] (c : K) (f : simple_func α β) : ⇑(c • f) = c • ⇑f :=
  rfl

theorem smul_apply {α : Type u_1} {β : Type u_2} [measurable_space α] {K : Type u_5} [has_scalar K β] (k : K) (f : simple_func α β) (a : α) : coe_fn (k • f) a = k • coe_fn f a :=
  rfl

protected instance semimodule {α : Type u_1} {β : Type u_2} [measurable_space α] {K : Type u_5} [semiring K] [add_comm_monoid β] [semimodule K β] : semimodule K (simple_func α β) :=
  function.injective.semimodule K
    (add_monoid_hom.mk (fun (f : simple_func α β) => (fun (this : α → β) => this) ⇑f) sorry sorry) coe_injective sorry

theorem smul_eq_map {α : Type u_1} {β : Type u_2} [measurable_space α] {K : Type u_5} [has_scalar K β] (k : K) (f : simple_func α β) : k • f = map (has_scalar.smul k) f :=
  rfl

protected instance preorder {α : Type u_1} {β : Type u_2} [measurable_space α] [preorder β] : preorder (simple_func α β) :=
  preorder.mk LessEq (fun (a b : simple_func α β) => a ≤ b ∧ ¬b ≤ a) sorry sorry

protected instance partial_order {α : Type u_1} {β : Type u_2} [measurable_space α] [partial_order β] : partial_order (simple_func α β) :=
  partial_order.mk preorder.le preorder.lt sorry sorry sorry

protected instance order_bot {α : Type u_1} {β : Type u_2} [measurable_space α] [order_bot β] : order_bot (simple_func α β) :=
  order_bot.mk (const α ⊥) partial_order.le partial_order.lt sorry sorry sorry sorry

protected instance order_top {α : Type u_1} {β : Type u_2} [measurable_space α] [order_top β] : order_top (simple_func α β) :=
  order_top.mk (const α ⊤) partial_order.le partial_order.lt sorry sorry sorry sorry

protected instance semilattice_inf {α : Type u_1} {β : Type u_2} [measurable_space α] [semilattice_inf β] : semilattice_inf (simple_func α β) :=
  semilattice_inf.mk has_inf.inf partial_order.le partial_order.lt sorry sorry sorry sorry sorry sorry

protected instance semilattice_sup {α : Type u_1} {β : Type u_2} [measurable_space α] [semilattice_sup β] : semilattice_sup (simple_func α β) :=
  semilattice_sup.mk has_sup.sup partial_order.le partial_order.lt sorry sorry sorry sorry sorry sorry

protected instance semilattice_sup_bot {α : Type u_1} {β : Type u_2} [measurable_space α] [semilattice_sup_bot β] : semilattice_sup_bot (simple_func α β) :=
  semilattice_sup_bot.mk order_bot.bot semilattice_sup.le semilattice_sup.lt sorry sorry sorry sorry semilattice_sup.sup
    sorry sorry sorry

protected instance lattice {α : Type u_1} {β : Type u_2} [measurable_space α] [lattice β] : lattice (simple_func α β) :=
  lattice.mk semilattice_sup.sup semilattice_sup.le semilattice_sup.lt sorry sorry sorry sorry sorry sorry
    semilattice_inf.inf sorry sorry sorry

protected instance bounded_lattice {α : Type u_1} {β : Type u_2} [measurable_space α] [bounded_lattice β] : bounded_lattice (simple_func α β) :=
  bounded_lattice.mk lattice.sup lattice.le lattice.lt sorry sorry sorry sorry sorry sorry lattice.inf sorry sorry sorry
    order_top.top sorry order_bot.bot sorry

theorem finset_sup_apply {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] [semilattice_sup_bot β] {f : γ → simple_func α β} (s : finset γ) (a : α) : coe_fn (finset.sup s f) a = finset.sup s fun (c : γ) => coe_fn (f c) a := sorry

/-- Restrict a simple function `f : α →ₛ β` to a set `s`. If `s` is measurable,
then `f.restrict s a = if a ∈ s then f a else 0`, otherwise `f.restrict s = const α 0`. -/
def restrict {α : Type u_1} {β : Type u_2} [measurable_space α] [HasZero β] (f : simple_func α β) (s : set α) : simple_func α β :=
  dite (is_measurable s) (fun (hs : is_measurable s) => piecewise s hs f 0) fun (hs : ¬is_measurable s) => 0

theorem restrict_of_not_measurable {α : Type u_1} {β : Type u_2} [measurable_space α] [HasZero β] {f : simple_func α β} {s : set α} (hs : ¬is_measurable s) : restrict f s = 0 :=
  dif_neg hs

@[simp] theorem coe_restrict {α : Type u_1} {β : Type u_2} [measurable_space α] [HasZero β] (f : simple_func α β) {s : set α} (hs : is_measurable s) : ⇑(restrict f s) = set.indicator s ⇑f := sorry

@[simp] theorem restrict_univ {α : Type u_1} {β : Type u_2} [measurable_space α] [HasZero β] (f : simple_func α β) : restrict f set.univ = f := sorry

@[simp] theorem restrict_empty {α : Type u_1} {β : Type u_2} [measurable_space α] [HasZero β] (f : simple_func α β) : restrict f ∅ = 0 := sorry

theorem map_restrict_of_zero {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] [HasZero β] [HasZero γ] {g : β → γ} (hg : g 0 = 0) (f : simple_func α β) (s : set α) : map g (restrict f s) = restrict (map g f) s := sorry

theorem map_coe_ennreal_restrict {α : Type u_1} [measurable_space α] (f : simple_func α nnreal) (s : set α) : map coe (restrict f s) = restrict (map coe f) s :=
  map_restrict_of_zero ennreal.coe_zero f s

theorem map_coe_nnreal_restrict {α : Type u_1} [measurable_space α] (f : simple_func α nnreal) (s : set α) : map coe (restrict f s) = restrict (map coe f) s :=
  map_restrict_of_zero nnreal.coe_zero f s

theorem restrict_apply {α : Type u_1} {β : Type u_2} [measurable_space α] [HasZero β] (f : simple_func α β) {s : set α} (hs : is_measurable s) (a : α) : coe_fn (restrict f s) a = ite (a ∈ s) (coe_fn f a) 0 := sorry

theorem restrict_preimage {α : Type u_1} {β : Type u_2} [measurable_space α] [HasZero β] (f : simple_func α β) {s : set α} (hs : is_measurable s) {t : set β} (ht : ¬0 ∈ t) : ⇑(restrict f s) ⁻¹' t = s ∩ ⇑f ⁻¹' t := sorry

theorem restrict_preimage_singleton {α : Type u_1} {β : Type u_2} [measurable_space α] [HasZero β] (f : simple_func α β) {s : set α} (hs : is_measurable s) {r : β} (hr : r ≠ 0) : ⇑(restrict f s) ⁻¹' singleton r = s ∩ ⇑f ⁻¹' singleton r :=
  restrict_preimage f hs (ne.symm hr)

theorem mem_restrict_range {α : Type u_1} {β : Type u_2} [measurable_space α] [HasZero β] {r : β} {s : set α} {f : simple_func α β} (hs : is_measurable s) : r ∈ simple_func.range (restrict f s) ↔ r = 0 ∧ s ≠ set.univ ∨ r ∈ ⇑f '' s := sorry

theorem mem_image_of_mem_range_restrict {α : Type u_1} {β : Type u_2} [measurable_space α] [HasZero β] {r : β} {s : set α} {f : simple_func α β} (hr : r ∈ simple_func.range (restrict f s)) (h0 : r ≠ 0) : r ∈ ⇑f '' s := sorry

theorem restrict_mono {α : Type u_1} {β : Type u_2} [measurable_space α] [HasZero β] [preorder β] (s : set α) {f : simple_func α β} {g : simple_func α β} (H : f ≤ g) : restrict f s ≤ restrict g s := sorry

/-- Fix a sequence `i : ℕ → β`. Given a function `α → β`, its `n`-th approximation
by simple functions is defined so that in case `β = ennreal` it sends each `a` to the supremum
of the set `{i k | k ≤ n ∧ i k ≤ f a}`, see `approx_apply` and `supr_approx_apply` for details. -/
def approx {α : Type u_1} {β : Type u_2} [measurable_space α] [semilattice_sup_bot β] [HasZero β] (i : ℕ → β) (f : α → β) (n : ℕ) : simple_func α β :=
  finset.sup (finset.range n) fun (k : ℕ) => restrict (const α (i k)) (set_of fun (a : α) => i k ≤ f a)

theorem approx_apply {α : Type u_1} {β : Type u_2} [measurable_space α] [semilattice_sup_bot β] [HasZero β] [topological_space β] [order_closed_topology β] [measurable_space β] [opens_measurable_space β] {i : ℕ → β} {f : α → β} {n : ℕ} (a : α) (hf : measurable f) : coe_fn (approx i f n) a = finset.sup (finset.range n) fun (k : ℕ) => ite (i k ≤ f a) (i k) 0 := sorry

theorem monotone_approx {α : Type u_1} {β : Type u_2} [measurable_space α] [semilattice_sup_bot β] [HasZero β] (i : ℕ → β) (f : α → β) : monotone (approx i f) :=
  fun (n m : ℕ) (h : n ≤ m) => finset.sup_mono (iff.mpr finset.range_subset h)

theorem approx_comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] [semilattice_sup_bot β] [HasZero β] [topological_space β] [order_closed_topology β] [measurable_space β] [opens_measurable_space β] [measurable_space γ] {i : ℕ → β} {f : γ → β} {g : α → γ} {n : ℕ} (a : α) (hf : measurable f) (hg : measurable g) : coe_fn (approx i (f ∘ g) n) a = coe_fn (approx i f n) (g a) := sorry

theorem supr_approx_apply {α : Type u_1} {β : Type u_2} [measurable_space α] [topological_space β] [complete_lattice β] [order_closed_topology β] [HasZero β] [measurable_space β] [opens_measurable_space β] (i : ℕ → β) (f : α → β) (a : α) (hf : measurable f) (h_zero : 0 = ⊥) : (supr fun (n : ℕ) => coe_fn (approx i f n) a) = supr fun (k : ℕ) => supr fun (h : i k ≤ f a) => i k := sorry

/-- A sequence of `ennreal`s such that its range is the set of non-negative rational numbers. -/
def ennreal_rat_embed (n : ℕ) : ennreal :=
  ennreal.of_real ↑(option.get_or_else (encodable.decode ℚ n) 0)

theorem ennreal_rat_embed_encode (q : ℚ) : ennreal_rat_embed (encodable.encode q) = ↑(nnreal.of_real ↑q) := sorry

/-- Approximate a function `α → ennreal` by a sequence of simple functions. -/
def eapprox {α : Type u_1} [measurable_space α] : (α → ennreal) → ℕ → simple_func α ennreal :=
  approx ennreal_rat_embed

theorem monotone_eapprox {α : Type u_1} [measurable_space α] (f : α → ennreal) : monotone (eapprox f) :=
  monotone_approx ennreal_rat_embed f

theorem supr_eapprox_apply {α : Type u_1} [measurable_space α] (f : α → ennreal) (hf : measurable f) (a : α) : (supr fun (n : ℕ) => coe_fn (eapprox f n) a) = f a := sorry

theorem eapprox_comp {α : Type u_1} {γ : Type u_3} [measurable_space α] [measurable_space γ] {f : γ → ennreal} {g : α → γ} {n : ℕ} (hf : measurable f) (hg : measurable g) : ⇑(eapprox (f ∘ g) n) = ⇑(eapprox f n) ∘ g :=
  funext fun (a : α) => approx_comp a hf hg

/-- Integral of a simple function whose codomain is `ennreal`. -/
def lintegral {α : Type u_1} [measurable_space α] (f : simple_func α ennreal) (μ : measure α) : ennreal :=
  finset.sum (simple_func.range f) fun (x : ennreal) => x * coe_fn μ (⇑f ⁻¹' singleton x)

theorem lintegral_eq_of_subset {α : Type u_1} [measurable_space α] {μ : measure α} (f : simple_func α ennreal) {s : finset ennreal} (hs : ∀ (x : α), coe_fn f x ≠ 0 → coe_fn μ (⇑f ⁻¹' singleton (coe_fn f x)) ≠ 0 → coe_fn f x ∈ s) : lintegral f μ = finset.sum s fun (x : ennreal) => x * coe_fn μ (⇑f ⁻¹' singleton x) := sorry

/-- Calculate the integral of `(g ∘ f)`, where `g : β → ennreal` and `f : α →ₛ β`.  -/
theorem map_lintegral {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} (g : β → ennreal) (f : simple_func α β) : lintegral (map g f) μ = finset.sum (simple_func.range f) fun (x : β) => g x * coe_fn μ (⇑f ⁻¹' singleton x) := sorry

theorem add_lintegral {α : Type u_1} [measurable_space α] {μ : measure α} (f : simple_func α ennreal) (g : simple_func α ennreal) : lintegral (f + g) μ = lintegral f μ + lintegral g μ := sorry

theorem const_mul_lintegral {α : Type u_1} [measurable_space α] {μ : measure α} (f : simple_func α ennreal) (x : ennreal) : lintegral (const α x * f) μ = x * lintegral f μ := sorry

/-- Integral of a simple function `α →ₛ ennreal` as a bilinear map. -/
def lintegralₗ {α : Type u_1} [measurable_space α] : linear_map ennreal (simple_func α ennreal) (linear_map ennreal (measure α) ennreal) :=
  linear_map.mk (fun (f : simple_func α ennreal) => linear_map.mk (lintegral f) sorry sorry) sorry sorry

@[simp] theorem zero_lintegral {α : Type u_1} [measurable_space α] {μ : measure α} : lintegral 0 μ = 0 :=
  iff.mp linear_map.ext_iff (linear_map.map_zero lintegralₗ) μ

theorem lintegral_add {α : Type u_1} [measurable_space α] {μ : measure α} {ν : measure α} (f : simple_func α ennreal) : lintegral f (μ + ν) = lintegral f μ + lintegral f ν :=
  linear_map.map_add (coe_fn lintegralₗ f) μ ν

theorem lintegral_smul {α : Type u_1} [measurable_space α] {μ : measure α} (f : simple_func α ennreal) (c : ennreal) : lintegral f (c • μ) = c • lintegral f μ :=
  linear_map.map_smul (coe_fn lintegralₗ f) c μ

@[simp] theorem lintegral_zero {α : Type u_1} [measurable_space α] (f : simple_func α ennreal) : lintegral f 0 = 0 :=
  linear_map.map_zero (coe_fn lintegralₗ f)

theorem lintegral_sum {α : Type u_1} [measurable_space α] {ι : Type u_2} (f : simple_func α ennreal) (μ : ι → measure α) : lintegral f (measure.sum μ) = tsum fun (i : ι) => lintegral f (μ i) := sorry

theorem restrict_lintegral {α : Type u_1} [measurable_space α] {μ : measure α} (f : simple_func α ennreal) {s : set α} (hs : is_measurable s) : lintegral (restrict f s) μ = finset.sum (simple_func.range f) fun (r : ennreal) => r * coe_fn μ (⇑f ⁻¹' singleton r ∩ s) := sorry

theorem lintegral_restrict {α : Type u_1} [measurable_space α] (f : simple_func α ennreal) (s : set α) (μ : measure α) : lintegral f (measure.restrict μ s) =
  finset.sum (simple_func.range f) fun (y : ennreal) => y * coe_fn μ (⇑f ⁻¹' singleton y ∩ s) := sorry

theorem restrict_lintegral_eq_lintegral_restrict {α : Type u_1} [measurable_space α] {μ : measure α} (f : simple_func α ennreal) {s : set α} (hs : is_measurable s) : lintegral (restrict f s) μ = lintegral f (measure.restrict μ s) := sorry

theorem const_lintegral {α : Type u_1} [measurable_space α] {μ : measure α} (c : ennreal) : lintegral (const α c) μ = c * coe_fn μ set.univ := sorry

theorem const_lintegral_restrict {α : Type u_1} [measurable_space α] {μ : measure α} (c : ennreal) (s : set α) : lintegral (const α c) (measure.restrict μ s) = c * coe_fn μ s := sorry

theorem restrict_const_lintegral {α : Type u_1} [measurable_space α] {μ : measure α} (c : ennreal) {s : set α} (hs : is_measurable s) : lintegral (restrict (const α c) s) μ = c * coe_fn μ s := sorry

theorem le_sup_lintegral {α : Type u_1} [measurable_space α] {μ : measure α} (f : simple_func α ennreal) (g : simple_func α ennreal) : lintegral f μ ⊔ lintegral g μ ≤ lintegral (f ⊔ g) μ := sorry

/-- `simple_func.lintegral` is monotone both in function and in measure. -/
theorem lintegral_mono {α : Type u_1} [measurable_space α] {f : simple_func α ennreal} {g : simple_func α ennreal} (hfg : f ≤ g) {μ : measure α} {ν : measure α} (hμν : μ ≤ ν) : lintegral f μ ≤ lintegral g ν := sorry

/-- `simple_func.lintegral` depends only on the measures of `f ⁻¹' {y}`. -/
theorem lintegral_eq_of_measure_preimage {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [measurable_space β] {f : simple_func α ennreal} {g : simple_func β ennreal} {ν : measure β} (H : ∀ (y : ennreal), coe_fn μ (⇑f ⁻¹' singleton y) = coe_fn ν (⇑g ⁻¹' singleton y)) : lintegral f μ = lintegral g ν := sorry

/-- If two simple functions are equal a.e., then their `lintegral`s are equal. -/
theorem lintegral_congr {α : Type u_1} [measurable_space α] {μ : measure α} {f : simple_func α ennreal} {g : simple_func α ennreal} (h : filter.eventually_eq (measure.ae μ) ⇑f ⇑g) : lintegral f μ = lintegral g μ := sorry

theorem lintegral_map {α : Type u_1} [measurable_space α] {μ : measure α} {β : Type u_2} [measurable_space β] {μ' : measure β} (f : simple_func α ennreal) (g : simple_func β ennreal) (m : α → β) (eq : ∀ (a : α), coe_fn f a = coe_fn g (m a)) (h : ∀ (s : set β), is_measurable s → coe_fn μ' s = coe_fn μ (m ⁻¹' s)) : lintegral f μ = lintegral g μ' := sorry

theorem support_eq {α : Type u_1} {β : Type u_2} [measurable_space α] [HasZero β] (f : simple_func α β) : function.support ⇑f =
  set.Union
    fun (y : β) =>
      set.Union fun (H : y ∈ finset.filter (fun (y : β) => y ≠ 0) (simple_func.range f)) => ⇑f ⁻¹' singleton y := sorry

/-- A `simple_func` has finite measure support if it is equal to `0` outside of a set of finite
measure. -/
protected def fin_meas_supp {α : Type u_1} {β : Type u_2} [measurable_space α] [HasZero β] (f : simple_func α β) (μ : measure α)  :=
  filter.eventually_eq (measure.cofinite μ) (⇑f) 0

theorem fin_meas_supp_iff_support {α : Type u_1} {β : Type u_2} [measurable_space α] [HasZero β] {f : simple_func α β} {μ : measure α} : simple_func.fin_meas_supp f μ ↔ coe_fn μ (function.support ⇑f) < ⊤ :=
  iff.rfl

theorem fin_meas_supp_iff {α : Type u_1} {β : Type u_2} [measurable_space α] [HasZero β] {f : simple_func α β} {μ : measure α} : simple_func.fin_meas_supp f μ ↔ ∀ (y : β), y ≠ 0 → coe_fn μ (⇑f ⁻¹' singleton y) < ⊤ := sorry

namespace fin_meas_supp


theorem meas_preimage_singleton_ne_zero {α : Type u_1} {β : Type u_2} [measurable_space α] [HasZero β] {μ : measure α} {f : simple_func α β} (h : simple_func.fin_meas_supp f μ) {y : β} (hy : y ≠ 0) : coe_fn μ (⇑f ⁻¹' singleton y) < ⊤ :=
  iff.mp fin_meas_supp_iff h y hy

protected theorem map {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] [HasZero β] [HasZero γ] {μ : measure α} {f : simple_func α β} {g : β → γ} (hf : simple_func.fin_meas_supp f μ) (hg : g 0 = 0) : simple_func.fin_meas_supp (map g f) μ :=
  flip lt_of_le_of_lt hf (measure_mono (function.support_comp_subset hg ⇑f))

theorem of_map {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] [HasZero β] [HasZero γ] {μ : measure α} {f : simple_func α β} {g : β → γ} (h : simple_func.fin_meas_supp (map g f) μ) (hg : ∀ (b : β), g b = 0 → b = 0) : simple_func.fin_meas_supp f μ :=
  flip lt_of_le_of_lt h (measure_mono (function.support_subset_comp hg fun (x : α) => coe_fn f x))

theorem map_iff {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] [HasZero β] [HasZero γ] {μ : measure α} {f : simple_func α β} {g : β → γ} (hg : ∀ {b : β}, g b = 0 ↔ b = 0) : simple_func.fin_meas_supp (map g f) μ ↔ simple_func.fin_meas_supp f μ :=
  { mp := fun (h : simple_func.fin_meas_supp (map g f) μ) => of_map h fun (b : β) => iff.mp hg,
    mpr := fun (h : simple_func.fin_meas_supp f μ) => fin_meas_supp.map h (iff.mpr hg rfl) }

protected theorem pair {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] [HasZero β] [HasZero γ] {μ : measure α} {f : simple_func α β} {g : simple_func α γ} (hf : simple_func.fin_meas_supp f μ) (hg : simple_func.fin_meas_supp g μ) : simple_func.fin_meas_supp (pair f g) μ := sorry

protected theorem map₂ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} [measurable_space α] [HasZero β] [HasZero γ] [HasZero δ] {μ : measure α} {f : simple_func α β} (hf : simple_func.fin_meas_supp f μ) {g : simple_func α γ} (hg : simple_func.fin_meas_supp g μ) {op : β → γ → δ} (H : op 0 0 = 0) : simple_func.fin_meas_supp (map (function.uncurry op) (pair f g)) μ :=
  fin_meas_supp.map (fin_meas_supp.pair hf hg) H

protected theorem add {α : Type u_1} [measurable_space α] {μ : measure α} {β : Type u_2} [add_monoid β] {f : simple_func α β} {g : simple_func α β} (hf : simple_func.fin_meas_supp f μ) (hg : simple_func.fin_meas_supp g μ) : simple_func.fin_meas_supp (f + g) μ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (simple_func.fin_meas_supp (f + g) μ)) (add_eq_map₂ f g)))
    (fin_meas_supp.map₂ hf hg (zero_add 0))

protected theorem mul {α : Type u_1} [measurable_space α] {μ : measure α} {β : Type u_2} [monoid_with_zero β] {f : simple_func α β} {g : simple_func α β} (hf : simple_func.fin_meas_supp f μ) (hg : simple_func.fin_meas_supp g μ) : simple_func.fin_meas_supp (f * g) μ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (simple_func.fin_meas_supp (f * g) μ)) (mul_eq_map₂ f g)))
    (fin_meas_supp.map₂ hf hg (zero_mul 0))

theorem lintegral_lt_top {α : Type u_1} [measurable_space α] {μ : measure α} {f : simple_func α ennreal} (hm : simple_func.fin_meas_supp f μ) (hf : filter.eventually (fun (a : α) => coe_fn f a < ⊤) (measure.ae μ)) : lintegral f μ < ⊤ := sorry

theorem of_lintegral_lt_top {α : Type u_1} [measurable_space α] {μ : measure α} {f : simple_func α ennreal} (h : lintegral f μ < ⊤) : simple_func.fin_meas_supp f μ := sorry

theorem iff_lintegral_lt_top {α : Type u_1} [measurable_space α] {μ : measure α} {f : simple_func α ennreal} (hf : filter.eventually (fun (a : α) => coe_fn f a < ⊤) (measure.ae μ)) : simple_func.fin_meas_supp f μ ↔ lintegral f μ < ⊤ :=
  { mp := fun (h : simple_func.fin_meas_supp f μ) => lintegral_lt_top h hf,
    mpr := fun (h : lintegral f μ < ⊤) => of_lintegral_lt_top h }

end fin_meas_supp


/-- To prove something for an arbitrary simple function, it suffices to show
that the property holds for (multiples of) characteristic functions and is closed under
addition (of functions with disjoint support).

It is possible to make the hypotheses in `h_sum` a bit stronger, and such conditions can be added
once we need them (for example it is only necessary to consider the case where `g` is a multiple
of a characteristic function, and that this multiple doesn't appear in the image of `f`) -/
protected theorem induction {α : Type u_1} {γ : Type u_2} [measurable_space α] [add_monoid γ] {P : simple_func α γ → Prop} (h_ind : ∀ (c : γ) {s : set α} (hs : is_measurable s), P (piecewise s hs (const α c) (const α 0))) (h_sum : ∀ {f g : simple_func α γ}, set.univ ⊆ ⇑f ⁻¹' singleton 0 ∪ ⇑g ⁻¹' singleton 0 → P f → P g → P (f + g)) (f : simple_func α γ) : P f := sorry

end simple_func


/-- The lower Lebesgue integral of a function `f` with respect to a measure `μ`. -/
def lintegral {α : Type u_1} [measurable_space α] (μ : measure α) (f : α → ennreal) : ennreal :=
  supr fun (g : simple_func α ennreal) => supr fun (hf : ⇑g ≤ f) => simple_func.lintegral g μ

/-! In the notation for integrals, an expression like `∫⁻ x, g ∥x∥ ∂μ` will not be parsed correctly,
  and needs parentheses. We do not set the binding power of `r` to `0`, because then
  `∫⁻ x, f x = 0` will be parsed incorrectly. -/

theorem simple_func.lintegral_eq_lintegral {α : Type u_1} [measurable_space α] (f : simple_func α ennreal) (μ : measure α) : (lintegral μ fun (a : α) => coe_fn f a) = simple_func.lintegral f μ := sorry

theorem lintegral_mono' {α : Type u_1} [measurable_space α] {μ : measure α} {ν : measure α} (hμν : μ ≤ ν) {f : α → ennreal} {g : α → ennreal} (hfg : f ≤ g) : (lintegral μ fun (a : α) => f a) ≤ lintegral ν fun (a : α) => g a := sorry

theorem lintegral_mono {α : Type u_1} [measurable_space α] {μ : measure α} {f : α → ennreal} {g : α → ennreal} (hfg : f ≤ g) : (lintegral μ fun (a : α) => f a) ≤ lintegral μ fun (a : α) => g a :=
  lintegral_mono' (le_refl μ) hfg

theorem lintegral_mono_nnreal {α : Type u_1} [measurable_space α] {μ : measure α} {f : α → nnreal} {g : α → nnreal} (h : f ≤ g) : (lintegral μ fun (a : α) => ↑(f a)) ≤ lintegral μ fun (a : α) => ↑(g a) := sorry

theorem monotone_lintegral {α : Type u_1} [measurable_space α] (μ : measure α) : monotone (lintegral μ) :=
  lintegral_mono

@[simp] theorem lintegral_const {α : Type u_1} [measurable_space α] {μ : measure α} (c : ennreal) : (lintegral μ fun (a : α) => c) = c * coe_fn μ set.univ := sorry

@[simp] theorem lintegral_one {α : Type u_1} [measurable_space α] {μ : measure α} : (lintegral μ fun (a : α) => 1) = coe_fn μ set.univ :=
  eq.mpr (id (Eq._oldrec (Eq.refl ((lintegral μ fun (a : α) => 1) = coe_fn μ set.univ)) (lintegral_const 1)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (1 * coe_fn μ set.univ = coe_fn μ set.univ)) (one_mul (coe_fn μ set.univ))))
      (Eq.refl (coe_fn μ set.univ)))

theorem set_lintegral_const {α : Type u_1} [measurable_space α] {μ : measure α} (s : set α) (c : ennreal) : (lintegral (measure.restrict μ s) fun (a : α) => c) = c * coe_fn μ s := sorry

theorem set_lintegral_one {α : Type u_1} [measurable_space α] {μ : measure α} (s : set α) : (lintegral (measure.restrict μ s) fun (a : α) => 1) = coe_fn μ s := sorry

/-- `∫⁻ a in s, f a ∂μ` is defined as the supremum of integrals of simple functions
`φ : α →ₛ ennreal` such that `φ ≤ f`. This lemma says that it suffices to take
functions `φ : α →ₛ ℝ≥0`. -/
theorem lintegral_eq_nnreal {α : Type u_1} [measurable_space α] (f : α → ennreal) (μ : measure α) : (lintegral μ fun (a : α) => f a) =
  supr
    fun (φ : simple_func α nnreal) =>
      supr fun (hf : ∀ (x : α), ↑(coe_fn φ x) ≤ f x) => simple_func.lintegral (simple_func.map coe φ) μ := sorry

theorem exists_simple_func_forall_lintegral_sub_lt_of_pos {α : Type u_1} [measurable_space α] {μ : measure α} {f : α → ennreal} (h : (lintegral μ fun (x : α) => f x) < ⊤) {ε : ennreal} (hε : 0 < ε) : ∃ (φ : simple_func α nnreal),
  (∀ (x : α), ↑(coe_fn φ x) ≤ f x) ∧
    ∀ (ψ : simple_func α nnreal),
      (∀ (x : α), ↑(coe_fn ψ x) ≤ f x) → simple_func.lintegral (simple_func.map coe (ψ - φ)) μ < ε := sorry

theorem supr_lintegral_le {α : Type u_1} [measurable_space α] {μ : measure α} {ι : Sort u_2} (f : ι → α → ennreal) : (supr fun (i : ι) => lintegral μ fun (a : α) => f i a) ≤ lintegral μ fun (a : α) => supr fun (i : ι) => f i a := sorry

theorem supr2_lintegral_le {α : Type u_1} [measurable_space α] {μ : measure α} {ι : Sort u_2} {ι' : ι → Sort u_3} (f : (i : ι) → ι' i → α → ennreal) : (supr fun (i : ι) => supr fun (h : ι' i) => lintegral μ fun (a : α) => f i h a) ≤
  lintegral μ fun (a : α) => supr fun (i : ι) => supr fun (h : ι' i) => f i h a := sorry

theorem le_infi_lintegral {α : Type u_1} [measurable_space α] {μ : measure α} {ι : Sort u_2} (f : ι → α → ennreal) : (lintegral μ fun (a : α) => infi fun (i : ι) => f i a) ≤ infi fun (i : ι) => lintegral μ fun (a : α) => f i a := sorry

theorem le_infi2_lintegral {α : Type u_1} [measurable_space α] {μ : measure α} {ι : Sort u_2} {ι' : ι → Sort u_3} (f : (i : ι) → ι' i → α → ennreal) : (lintegral μ fun (a : α) => infi fun (i : ι) => infi fun (h : ι' i) => f i h a) ≤
  infi fun (i : ι) => infi fun (h : ι' i) => lintegral μ fun (a : α) => f i h a := sorry

theorem lintegral_mono_ae {α : Type u_1} [measurable_space α] {μ : measure α} {f : α → ennreal} {g : α → ennreal} (h : filter.eventually (fun (a : α) => f a ≤ g a) (measure.ae μ)) : (lintegral μ fun (a : α) => f a) ≤ lintegral μ fun (a : α) => g a := sorry

theorem lintegral_congr_ae {α : Type u_1} [measurable_space α] {μ : measure α} {f : α → ennreal} {g : α → ennreal} (h : filter.eventually_eq (measure.ae μ) f g) : (lintegral μ fun (a : α) => f a) = lintegral μ fun (a : α) => g a :=
  le_antisymm (lintegral_mono_ae (filter.eventually_eq.le h))
    (lintegral_mono_ae (filter.eventually_eq.le (filter.eventually_eq.symm h)))

theorem lintegral_congr {α : Type u_1} [measurable_space α] {μ : measure α} {f : α → ennreal} {g : α → ennreal} (h : ∀ (a : α), f a = g a) : (lintegral μ fun (a : α) => f a) = lintegral μ fun (a : α) => g a := sorry

theorem set_lintegral_congr {α : Type u_1} [measurable_space α] {μ : measure α} {f : α → ennreal} {s : set α} {t : set α} (h : filter.eventually_eq (measure.ae μ) s t) : (lintegral (measure.restrict μ s) fun (x : α) => f x) = lintegral (measure.restrict μ t) fun (x : α) => f x := sorry

/-- Monotone convergence theorem -- sometimes called Beppo-Levi convergence.

See `lintegral_supr_directed` for a more general form. -/
theorem lintegral_supr {α : Type u_1} [measurable_space α] {μ : measure α} {f : ℕ → α → ennreal} (hf : ∀ (n : ℕ), measurable (f n)) (h_mono : monotone f) : (lintegral μ fun (a : α) => supr fun (n : ℕ) => f n a) = supr fun (n : ℕ) => lintegral μ fun (a : α) => f n a := sorry

/-- Monotone convergence theorem -- sometimes called Beppo-Levi convergence. Version with
ae_measurable functions. -/
theorem lintegral_supr' {α : Type u_1} [measurable_space α] {μ : measure α} {f : ℕ → α → ennreal} (hf : ∀ (n : ℕ), ae_measurable (f n)) (h_mono : filter.eventually (fun (x : α) => monotone fun (n : ℕ) => f n x) (measure.ae μ)) : (lintegral μ fun (a : α) => supr fun (n : ℕ) => f n a) = supr fun (n : ℕ) => lintegral μ fun (a : α) => f n a := sorry

theorem lintegral_eq_supr_eapprox_lintegral {α : Type u_1} [measurable_space α] {μ : measure α} {f : α → ennreal} (hf : measurable f) : (lintegral μ fun (a : α) => f a) = supr fun (n : ℕ) => simple_func.lintegral (simple_func.eapprox f n) μ := sorry

/-- If `f` has finite integral, then `∫⁻ x in s, f x ∂μ` is absolutely continuous in `s`: it tends
to zero as `μ s` tends to zero. This lemma states states this fact in terms of `ε` and `δ`. -/
theorem exists_pos_set_lintegral_lt_of_measure_lt {α : Type u_1} [measurable_space α] {μ : measure α} {f : α → ennreal} (h : (lintegral μ fun (x : α) => f x) < ⊤) {ε : ennreal} (hε : 0 < ε) : ∃ (δ : ennreal),
  ∃ (H : δ > 0), ∀ (s : set α), coe_fn μ s < δ → (lintegral (measure.restrict μ s) fun (x : α) => f x) < ε := sorry

/-- If `f` has finite integral, then `∫⁻ x in s, f x ∂μ` is absolutely continuous in `s`: it tends
to zero as `μ s` tends to zero. -/
theorem tendsto_set_lintegral_zero {α : Type u_1} [measurable_space α] {μ : measure α} {ι : Type u_2} {f : α → ennreal} (h : (lintegral μ fun (x : α) => f x) < ⊤) {l : filter ι} {s : ι → set α} (hl : filter.tendsto (⇑μ ∘ s) l (nhds 0)) : filter.tendsto (fun (i : ι) => lintegral (measure.restrict μ (s i)) fun (x : α) => f x) l (nhds 0) := sorry

@[simp] theorem lintegral_add {α : Type u_1} [measurable_space α] {μ : measure α} {f : α → ennreal} {g : α → ennreal} (hf : measurable f) (hg : measurable g) : (lintegral μ fun (a : α) => f a + g a) = (lintegral μ fun (a : α) => f a) + lintegral μ fun (a : α) => g a := sorry

theorem lintegral_add' {α : Type u_1} [measurable_space α] {μ : measure α} {f : α → ennreal} {g : α → ennreal} (hf : ae_measurable f) (hg : ae_measurable g) : (lintegral μ fun (a : α) => f a + g a) = (lintegral μ fun (a : α) => f a) + lintegral μ fun (a : α) => g a := sorry

theorem lintegral_zero {α : Type u_1} [measurable_space α] {μ : measure α} : (lintegral μ fun (a : α) => 0) = 0 := sorry

theorem lintegral_zero_fun {α : Type u_1} [measurable_space α] {μ : measure α} : (lintegral μ fun (a : α) => HasZero.zero a) = 0 := sorry

@[simp] theorem lintegral_smul_measure {α : Type u_1} [measurable_space α] {μ : measure α} (c : ennreal) (f : α → ennreal) : (lintegral (c • μ) fun (a : α) => f a) = c * lintegral μ fun (a : α) => f a := sorry

@[simp] theorem lintegral_sum_measure {α : Type u_1} [measurable_space α] {ι : Type u_2} (f : α → ennreal) (μ : ι → measure α) : (lintegral (measure.sum μ) fun (a : α) => f a) = tsum fun (i : ι) => lintegral (μ i) fun (a : α) => f a := sorry

@[simp] theorem lintegral_add_measure {α : Type u_1} [measurable_space α] (f : α → ennreal) (μ : measure α) (ν : measure α) : (lintegral (μ + ν) fun (a : α) => f a) = (lintegral μ fun (a : α) => f a) + lintegral ν fun (a : α) => f a := sorry

@[simp] theorem lintegral_zero_measure {α : Type u_1} [measurable_space α] (f : α → ennreal) : (lintegral 0 fun (a : α) => f a) = 0 := sorry

theorem lintegral_finset_sum {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} (s : finset β) {f : β → α → ennreal} (hf : ∀ (b : β), measurable (f b)) : (lintegral μ fun (a : α) => finset.sum s fun (b : β) => f b a) =
  finset.sum s fun (b : β) => lintegral μ fun (a : α) => f b a := sorry

@[simp] theorem lintegral_const_mul {α : Type u_1} [measurable_space α] {μ : measure α} (r : ennreal) {f : α → ennreal} (hf : measurable f) : (lintegral μ fun (a : α) => r * f a) = r * lintegral μ fun (a : α) => f a := sorry

theorem lintegral_const_mul'' {α : Type u_1} [measurable_space α] {μ : measure α} (r : ennreal) {f : α → ennreal} (hf : ae_measurable f) : (lintegral μ fun (a : α) => r * f a) = r * lintegral μ fun (a : α) => f a := sorry

theorem lintegral_const_mul_le {α : Type u_1} [measurable_space α] {μ : measure α} (r : ennreal) (f : α → ennreal) : (r * lintegral μ fun (a : α) => f a) ≤ lintegral μ fun (a : α) => r * f a := sorry

theorem lintegral_const_mul' {α : Type u_1} [measurable_space α] {μ : measure α} (r : ennreal) (f : α → ennreal) (hr : r ≠ ⊤) : (lintegral μ fun (a : α) => r * f a) = r * lintegral μ fun (a : α) => f a := sorry

theorem lintegral_mul_const {α : Type u_1} [measurable_space α] {μ : measure α} (r : ennreal) {f : α → ennreal} (hf : measurable f) : (lintegral μ fun (a : α) => f a * r) = (lintegral μ fun (a : α) => f a) * r := sorry

theorem lintegral_mul_const'' {α : Type u_1} [measurable_space α] {μ : measure α} (r : ennreal) {f : α → ennreal} (hf : ae_measurable f) : (lintegral μ fun (a : α) => f a * r) = (lintegral μ fun (a : α) => f a) * r := sorry

theorem lintegral_mul_const_le {α : Type u_1} [measurable_space α] {μ : measure α} (r : ennreal) (f : α → ennreal) : (lintegral μ fun (a : α) => f a) * r ≤ lintegral μ fun (a : α) => f a * r := sorry

theorem lintegral_mul_const' {α : Type u_1} [measurable_space α] {μ : measure α} (r : ennreal) (f : α → ennreal) (hr : r ≠ ⊤) : (lintegral μ fun (a : α) => f a * r) = (lintegral μ fun (a : α) => f a) * r := sorry

/- A double integral of a product where each factor contains only one variable
  is a product of integrals -/

theorem lintegral_lintegral_mul {α : Type u_1} [measurable_space α] {μ : measure α} {β : Type u_2} [measurable_space β] {ν : measure β} {f : α → ennreal} {g : β → ennreal} (hf : measurable f) (hg : measurable g) : (lintegral μ fun (x : α) => lintegral ν fun (y : β) => f x * g y) =
  (lintegral μ fun (x : α) => f x) * lintegral ν fun (y : β) => g y := sorry

-- TODO: Need a better way of rewriting inside of a integral

theorem lintegral_rw₁ {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} {f : α → β} {f' : α → β} (h : filter.eventually_eq (measure.ae μ) f f') (g : β → ennreal) : (lintegral μ fun (a : α) => g (f a)) = lintegral μ fun (a : α) => g (f' a) :=
  lintegral_congr_ae
    (filter.eventually.mono h
      fun (a : α) (h : f a = f' a) => eq.mpr (id (Eq._oldrec (Eq.refl (g (f a) = g (f' a))) h)) (Eq.refl (g (f' a))))

-- TODO: Need a better way of rewriting inside of a integral

theorem lintegral_rw₂ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] {μ : measure α} {f₁ : α → β} {f₁' : α → β} {f₂ : α → γ} {f₂' : α → γ} (h₁ : filter.eventually_eq (measure.ae μ) f₁ f₁') (h₂ : filter.eventually_eq (measure.ae μ) f₂ f₂') (g : β → γ → ennreal) : (lintegral μ fun (a : α) => g (f₁ a) (f₂ a)) = lintegral μ fun (a : α) => g (f₁' a) (f₂' a) := sorry

@[simp] theorem lintegral_indicator {α : Type u_1} [measurable_space α] {μ : measure α} (f : α → ennreal) {s : set α} (hs : is_measurable s) : (lintegral μ fun (a : α) => set.indicator s f a) = lintegral (measure.restrict μ s) fun (a : α) => f a := sorry

/-- Chebyshev's inequality -/
theorem mul_meas_ge_le_lintegral {α : Type u_1} [measurable_space α] {μ : measure α} {f : α → ennreal} (hf : measurable f) (ε : ennreal) : ε * coe_fn μ (set_of fun (x : α) => ε ≤ f x) ≤ lintegral μ fun (a : α) => f a := sorry

theorem meas_ge_le_lintegral_div {α : Type u_1} [measurable_space α] {μ : measure α} {f : α → ennreal} (hf : measurable f) {ε : ennreal} (hε : ε ≠ 0) (hε' : ε ≠ ⊤) : coe_fn μ (set_of fun (x : α) => ε ≤ f x) ≤ (lintegral μ fun (a : α) => f a) / ε := sorry

@[simp] theorem lintegral_eq_zero_iff {α : Type u_1} [measurable_space α] {μ : measure α} {f : α → ennreal} (hf : measurable f) : (lintegral μ fun (a : α) => f a) = 0 ↔ filter.eventually_eq (measure.ae μ) f 0 := sorry

@[simp] theorem lintegral_eq_zero_iff' {α : Type u_1} [measurable_space α] {μ : measure α} {f : α → ennreal} (hf : ae_measurable f) : (lintegral μ fun (a : α) => f a) = 0 ↔ filter.eventually_eq (measure.ae μ) f 0 := sorry

theorem lintegral_pos_iff_support {α : Type u_1} [measurable_space α] {μ : measure α} {f : α → ennreal} (hf : measurable f) : (0 < lintegral μ fun (a : α) => f a) ↔ 0 < coe_fn μ (function.support f) := sorry

/-- Weaker version of the monotone convergence theorem-/
theorem lintegral_supr_ae {α : Type u_1} [measurable_space α] {μ : measure α} {f : ℕ → α → ennreal} (hf : ∀ (n : ℕ), measurable (f n)) (h_mono : ∀ (n : ℕ), filter.eventually (fun (a : α) => f n a ≤ f (Nat.succ n) a) (measure.ae μ)) : (lintegral μ fun (a : α) => supr fun (n : ℕ) => f n a) = supr fun (n : ℕ) => lintegral μ fun (a : α) => f n a := sorry

theorem lintegral_sub {α : Type u_1} [measurable_space α] {μ : measure α} {f : α → ennreal} {g : α → ennreal} (hf : measurable f) (hg : measurable g) (hg_fin : (lintegral μ fun (a : α) => g a) < ⊤) (h_le : filter.eventually_le (measure.ae μ) g f) : (lintegral μ fun (a : α) => f a - g a) = (lintegral μ fun (a : α) => f a) - lintegral μ fun (a : α) => g a := sorry

/-- Monotone convergence theorem for nonincreasing sequences of functions -/
theorem lintegral_infi_ae {α : Type u_1} [measurable_space α] {μ : measure α} {f : ℕ → α → ennreal} (h_meas : ∀ (n : ℕ), measurable (f n)) (h_mono : ∀ (n : ℕ), filter.eventually_le (measure.ae μ) (f (Nat.succ n)) (f n)) (h_fin : (lintegral μ fun (a : α) => f 0 a) < ⊤) : (lintegral μ fun (a : α) => infi fun (n : ℕ) => f n a) = infi fun (n : ℕ) => lintegral μ fun (a : α) => f n a := sorry

/-- Monotone convergence theorem for nonincreasing sequences of functions -/
theorem lintegral_infi {α : Type u_1} [measurable_space α] {μ : measure α} {f : ℕ → α → ennreal} (h_meas : ∀ (n : ℕ), measurable (f n)) (h_mono : ∀ {m n : ℕ}, m ≤ n → f n ≤ f m) (h_fin : (lintegral μ fun (a : α) => f 0 a) < ⊤) : (lintegral μ fun (a : α) => infi fun (n : ℕ) => f n a) = infi fun (n : ℕ) => lintegral μ fun (a : α) => f n a :=
  lintegral_infi_ae h_meas (fun (n : ℕ) => ae_of_all μ (h_mono (le_of_lt (nat.lt_succ_self n)))) h_fin

/-- Known as Fatou's lemma, version with `ae_measurable` functions -/
theorem lintegral_liminf_le' {α : Type u_1} [measurable_space α] {μ : measure α} {f : ℕ → α → ennreal} (h_meas : ∀ (n : ℕ), ae_measurable (f n)) : (lintegral μ fun (a : α) => filter.liminf filter.at_top fun (n : ℕ) => f n a) ≤
  filter.liminf filter.at_top fun (n : ℕ) => lintegral μ fun (a : α) => f n a := sorry

/-- Known as Fatou's lemma -/
theorem lintegral_liminf_le {α : Type u_1} [measurable_space α] {μ : measure α} {f : ℕ → α → ennreal} (h_meas : ∀ (n : ℕ), measurable (f n)) : (lintegral μ fun (a : α) => filter.liminf filter.at_top fun (n : ℕ) => f n a) ≤
  filter.liminf filter.at_top fun (n : ℕ) => lintegral μ fun (a : α) => f n a :=
  lintegral_liminf_le' fun (n : ℕ) => measurable.ae_measurable (h_meas n)

theorem limsup_lintegral_le {α : Type u_1} [measurable_space α] {μ : measure α} {f : ℕ → α → ennreal} {g : α → ennreal} (hf_meas : ∀ (n : ℕ), measurable (f n)) (h_bound : ∀ (n : ℕ), filter.eventually_le (measure.ae μ) (f n) g) (h_fin : (lintegral μ fun (a : α) => g a) < ⊤) : (filter.limsup filter.at_top fun (n : ℕ) => lintegral μ fun (a : α) => f n a) ≤
  lintegral μ fun (a : α) => filter.limsup filter.at_top fun (n : ℕ) => f n a := sorry

/-- Dominated convergence theorem for nonnegative functions -/
theorem tendsto_lintegral_of_dominated_convergence {α : Type u_1} [measurable_space α] {μ : measure α} {F : ℕ → α → ennreal} {f : α → ennreal} (bound : α → ennreal) (hF_meas : ∀ (n : ℕ), measurable (F n)) (h_bound : ∀ (n : ℕ), filter.eventually_le (measure.ae μ) (F n) bound) (h_fin : (lintegral μ fun (a : α) => bound a) < ⊤) (h_lim : filter.eventually (fun (a : α) => filter.tendsto (fun (n : ℕ) => F n a) filter.at_top (nhds (f a))) (measure.ae μ)) : filter.tendsto (fun (n : ℕ) => lintegral μ fun (a : α) => F n a) filter.at_top (nhds (lintegral μ fun (a : α) => f a)) := sorry

/-- Dominated convergence theorem for nonnegative functions which are just almost everywhere
measurable. -/
theorem tendsto_lintegral_of_dominated_convergence' {α : Type u_1} [measurable_space α] {μ : measure α} {F : ℕ → α → ennreal} {f : α → ennreal} (bound : α → ennreal) (hF_meas : ∀ (n : ℕ), ae_measurable (F n)) (h_bound : ∀ (n : ℕ), filter.eventually_le (measure.ae μ) (F n) bound) (h_fin : (lintegral μ fun (a : α) => bound a) < ⊤) (h_lim : filter.eventually (fun (a : α) => filter.tendsto (fun (n : ℕ) => F n a) filter.at_top (nhds (f a))) (measure.ae μ)) : filter.tendsto (fun (n : ℕ) => lintegral μ fun (a : α) => F n a) filter.at_top (nhds (lintegral μ fun (a : α) => f a)) := sorry

/-- Dominated convergence theorem for filters with a countable basis -/
theorem tendsto_lintegral_filter_of_dominated_convergence {α : Type u_1} [measurable_space α] {μ : measure α} {ι : Type u_2} {l : filter ι} {F : ι → α → ennreal} {f : α → ennreal} (bound : α → ennreal) (hl_cb : filter.is_countably_generated l) (hF_meas : filter.eventually (fun (n : ι) => measurable (F n)) l) (h_bound : filter.eventually (fun (n : ι) => filter.eventually (fun (a : α) => F n a ≤ bound a) (measure.ae μ)) l) (h_fin : (lintegral μ fun (a : α) => bound a) < ⊤) (h_lim : filter.eventually (fun (a : α) => filter.tendsto (fun (n : ι) => F n a) l (nhds (f a))) (measure.ae μ)) : filter.tendsto (fun (n : ι) => lintegral μ fun (a : α) => F n a) l (nhds (lintegral μ fun (a : α) => f a)) := sorry

/-- Monotone convergence for a suprema over a directed family and indexed by an encodable type -/
theorem lintegral_supr_directed {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [encodable β] {f : β → α → ennreal} (hf : ∀ (b : β), measurable (f b)) (h_directed : directed LessEq f) : (lintegral μ fun (a : α) => supr fun (b : β) => f b a) = supr fun (b : β) => lintegral μ fun (a : α) => f b a := sorry

theorem lintegral_tsum {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [encodable β] {f : β → α → ennreal} (hf : ∀ (i : β), measurable (f i)) : (lintegral μ fun (a : α) => tsum fun (i : β) => f i a) = tsum fun (i : β) => lintegral μ fun (a : α) => f i a := sorry

theorem lintegral_Union {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [encodable β] {s : β → set α} (hm : ∀ (i : β), is_measurable (s i)) (hd : pairwise (disjoint on s)) (f : α → ennreal) : (lintegral (measure.restrict μ (set.Union fun (i : β) => s i)) fun (a : α) => f a) =
  tsum fun (i : β) => lintegral (measure.restrict μ (s i)) fun (a : α) => f a := sorry

theorem lintegral_Union_le {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [encodable β] (s : β → set α) (f : α → ennreal) : (lintegral (measure.restrict μ (set.Union fun (i : β) => s i)) fun (a : α) => f a) ≤
  tsum fun (i : β) => lintegral (measure.restrict μ (s i)) fun (a : α) => f a := sorry

theorem lintegral_map {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [measurable_space β] {f : β → ennreal} {g : α → β} (hf : measurable f) (hg : measurable g) : (lintegral (coe_fn (measure.map g) μ) fun (a : β) => f a) = lintegral μ fun (a : α) => f (g a) := sorry

theorem lintegral_map' {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [measurable_space β] {f : β → ennreal} {g : α → β} (hf : ae_measurable f) (hg : measurable g) : (lintegral (coe_fn (measure.map g) μ) fun (a : β) => f a) = lintegral μ fun (a : α) => f (g a) :=
  Eq.trans (Eq.trans (lintegral_congr_ae (ae_measurable.ae_eq_mk hf)) (lintegral_map (ae_measurable.measurable_mk hf) hg))
    (lintegral_congr_ae (ae_eq_comp hg (filter.eventually_eq.symm (ae_measurable.ae_eq_mk hf))))

theorem lintegral_comp {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [measurable_space β] {f : β → ennreal} {g : α → β} (hf : measurable f) (hg : measurable g) : lintegral μ (f ∘ g) = lintegral (coe_fn (measure.map g) μ) fun (a : β) => f a :=
  Eq.symm (lintegral_map hf hg)

theorem set_lintegral_map {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [measurable_space β] {f : β → ennreal} {g : α → β} {s : set β} (hs : is_measurable s) (hf : measurable f) (hg : measurable g) : (lintegral (measure.restrict (coe_fn (measure.map g) μ) s) fun (y : β) => f y) =
  lintegral (measure.restrict μ (g ⁻¹' s)) fun (x : α) => f (g x) := sorry

theorem lintegral_dirac' {α : Type u_1} [measurable_space α] (a : α) {f : α → ennreal} (hf : measurable f) : (lintegral (measure.dirac a) fun (a : α) => f a) = f a := sorry

theorem lintegral_dirac {α : Type u_1} [measurable_space α] [measurable_singleton_class α] (a : α) (f : α → ennreal) : (lintegral (measure.dirac a) fun (a : α) => f a) = f a := sorry

theorem lintegral_count' {α : Type u_1} [measurable_space α] {f : α → ennreal} (hf : measurable f) : (lintegral measure.count fun (a : α) => f a) = tsum fun (a : α) => f a := sorry

theorem lintegral_count {α : Type u_1} [measurable_space α] [measurable_singleton_class α] (f : α → ennreal) : (lintegral measure.count fun (a : α) => f a) = tsum fun (a : α) => f a := sorry

theorem ae_lt_top {α : Type u_1} [measurable_space α] {μ : measure α} {f : α → ennreal} (hf : measurable f) (h2f : (lintegral μ fun (x : α) => f x) < ⊤) : filter.eventually (fun (x : α) => f x < ⊤) (measure.ae μ) := sorry

/-- Given a measure `μ : measure α` and a function `f : α → ennreal`, `μ.with_density f` is the
measure such that for a measurable set `s` we have `μ.with_density f s = ∫⁻ a in s, f a ∂μ`. -/
def measure.with_density {α : Type u_1} [measurable_space α] (μ : measure α) (f : α → ennreal) : measure α :=
  measure.of_measurable (fun (s : set α) (hs : is_measurable s) => lintegral (measure.restrict μ s) fun (a : α) => f a)
    sorry sorry

@[simp] theorem with_density_apply {α : Type u_1} [measurable_space α] {μ : measure α} (f : α → ennreal) {s : set α} (hs : is_measurable s) : coe_fn (measure.with_density μ f) s = lintegral (measure.restrict μ s) fun (a : α) => f a :=
  measure.of_measurable_apply s hs

end measure_theory


/-- To prove something for an arbitrary measurable function into `ennreal`, it suffices to show
that the property holds for (multiples of) characteristic functions and is closed under addition
and supremum of increasing sequences of functions.

It is possible to make the hypotheses in the induction steps a bit stronger, and such conditions
can be added once we need them (for example in `h_sum` it is only necessary to consider the sum of
a simple function with a multiple of a characteristic function and that the intersection
of their images is a subset of `{0}`. -/
theorem measurable.ennreal_induction {α : Type u_1} [measurable_space α] {P : (α → ennreal) → Prop} (h_ind : ∀ (c : ennreal) {s : set α}, is_measurable s → P (set.indicator s fun (_x : α) => c)) (h_sum : ∀ {f g : α → ennreal},
  set.univ ⊆ f ⁻¹' singleton 0 ∪ g ⁻¹' singleton 0 → measurable f → measurable g → P f → P g → P (f + g)) (h_supr : ∀ {f : ℕ → α → ennreal},
  (∀ (n : ℕ), measurable (f n)) → monotone f → (∀ (n : ℕ), P (f n)) → P fun (x : α) => supr fun (n : ℕ) => f n x) {f : α → ennreal} (hf : measurable f) : P f := sorry

namespace measure_theory


/-- This is Exercise 1.2.1 from [tao2010]. It allows you to express integration of a measurable
function with respect to `(μ.with_density f)` as an integral with respect to `μ`, called the base
measure. `μ` is often the Lebesgue measure, and in this circumstance `f` is the probability density
function, and `(μ.with_density f)` represents any continuous random variable as a
probability measure, such as the uniform distribution between 0 and 1, the Gaussian distribution,
the exponential distribution, the Beta distribution, or the Cauchy distribution (see Section 2.4
of [wasserman2004]). Thus, this method shows how to one can calculate expectations, variances,
and other moments as a function of the probability density function.
 -/
theorem lintegral_with_density_eq_lintegral_mul {α : Type u_1} [measurable_space α] (μ : measure α) {f : α → ennreal} (h_mf : measurable f) {g : α → ennreal} : measurable g → (lintegral (measure.with_density μ f) fun (a : α) => g a) = lintegral μ fun (a : α) => Mul.mul f g a := sorry

