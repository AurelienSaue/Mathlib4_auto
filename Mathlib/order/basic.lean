/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.subtype
import Mathlib.data.prod
import Mathlib.PostPort

universes u_1 u_2 u v w l 

namespace Mathlib

/-!
# Basic definitions about `≤` and `<`

## Definitions

### Predicates on functions

- `monotone f`: a function between two types equipped with `≤` is monotone
  if `a ≤ b` implies `f a ≤ f b`.
- `strict_mono f` : a function between two types equipped with `<` is strictly monotone
  if `a < b` implies `f a < f b`.
- `order_dual α` : a type tag reversing the meaning of all inequalities.

### Transfering orders

- `order.preimage`, `preorder.lift`: transfer a (pre)order on `β` to an order on `α`
  using a function `f : α → β`.
- `partial_order.lift`, `linear_order.lift`: transfer a partial (resp., linear) order on `β` to a
  partial (resp., linear) order on `α` using an injective function `f`.

### Extra classes

- `no_top_order`, `no_bot_order`: an order without a maximal/minimal element.
- `densely_ordered`: an order with no gaps, i.e. for any two elements `a<b` there exists
  `c`, `a<c<b`.

## Main theorems

- `monotone_of_monotone_nat`: if `f : ℕ → α` and `f n ≤ f (n + 1)` for all `n`, then
  `f` is monotone;
- `strict_mono.nat`: if `f : ℕ → α` and `f n < f (n + 1)` for all `n`, then f is strictly monotone.

## TODO

- expand module docs
- automatic construction of dual definitions / theorems

## See also
- `algebra.order` for basic lemmas about orders, and projection notation for orders

## Tags

preorder, order, partial order, linear order, monotone, strictly monotone
-/

theorem preorder.ext {α : Type u_1} {A : preorder α} {B : preorder α} (H : ∀ (x y : α), x ≤ y ↔ x ≤ y) : A = B := sorry

theorem partial_order.ext {α : Type u_1} {A : partial_order α} {B : partial_order α} (H : ∀ (x y : α), x ≤ y ↔ x ≤ y) : A = B := sorry

theorem linear_order.ext {α : Type u_1} {A : linear_order α} {B : linear_order α} (H : ∀ (x y : α), x ≤ y ↔ x ≤ y) : A = B := sorry

/-- Given a relation `R` on `β` and a function `f : α → β`,
  the preimage relation on `α` is defined by `x ≤ y ↔ f x ≤ f y`.
  It is the unique relation on `α` making `f` a `rel_embedding`
  (assuming `f` is injective). -/
@[simp] def order.preimage {α : Sort u_1} {β : Sort u_2} (f : α → β) (s : β → β → Prop) (x : α) (y : α) :=
  s (f x) (f y)

infixl:80 " ⁻¹'o " => Mathlib.order.preimage

/-- The preimage of a decidable order is decidable. -/
protected instance order.preimage.decidable {α : Sort u_1} {β : Sort u_2} (f : α → β) (s : β → β → Prop) [H : DecidableRel s] : DecidableRel (f ⁻¹'o s) :=
  fun (x y : α) => H (f x) (f y)

/-- A function between preorders is monotone if
  `a ≤ b` implies `f a ≤ f b`. -/
def monotone {α : Type u} {β : Type v} [preorder α] [preorder β] (f : α → β) :=
  ∀ {a b : α}, a ≤ b → f a ≤ f b

theorem monotone_id {α : Type u} [preorder α] : monotone id :=
  fun (x y : α) (h : x ≤ y) => h

theorem monotone_const {α : Type u} {β : Type v} [preorder α] [preorder β] {b : β} : monotone fun (a : α) => b :=
  fun (x y : α) (h : x ≤ y) => le_refl b

protected theorem monotone.comp {α : Type u} {β : Type v} {γ : Type w} [preorder α] [preorder β] [preorder γ] {g : β → γ} {f : α → β} (m_g : monotone g) (m_f : monotone f) : monotone (g ∘ f) :=
  fun (a b : α) (h : a ≤ b) => m_g (m_f h)

protected theorem monotone.iterate {α : Type u} [preorder α] {f : α → α} (hf : monotone f) (n : ℕ) : monotone (nat.iterate f n) :=
  nat.rec_on n monotone_id fun (n : ℕ) (ihn : monotone (nat.iterate f n)) => monotone.comp ihn hf

theorem monotone_of_monotone_nat {α : Type u} [preorder α] {f : ℕ → α} (hf : ∀ (n : ℕ), f n ≤ f (n + 1)) : monotone f := sorry

theorem monotone.reflect_lt {α : Type u_1} {β : Type u_2} [linear_order α] [preorder β] {f : α → β} (hf : monotone f) {x : α} {x' : α} (h : f x < f x') : x < x' :=
  eq.mpr (id (Eq._oldrec (Eq.refl (x < x')) (Eq.symm (propext not_le)))) (id fun (h' : x' ≤ x) => not_le_of_lt h (hf h'))

/-- If `f` is a monotone function from `ℕ` to a preorder such that `y` lies between `f x` and
  `f (x + 1)`, then `y` doesn't lie in the range of `f`. -/
theorem monotone.ne_of_lt_of_lt_nat {α : Type u_1} [preorder α] {f : ℕ → α} (hf : monotone f) (x : ℕ) (x' : ℕ) {y : α} (h1 : f x < y) (h2 : y < f (x + 1)) : f x' ≠ y := sorry

/-- If `f` is a monotone function from `ℤ` to a preorder such that `y` lies between `f x` and
  `f (x + 1)`, then `y` doesn't lie in the range of `f`. -/
theorem monotone.ne_of_lt_of_lt_int {α : Type u_1} [preorder α] {f : ℤ → α} (hf : monotone f) (x : ℤ) (x' : ℤ) {y : α} (h1 : f x < y) (h2 : y < f (x + 1)) : f x' ≠ y := sorry

/-- A function `f` is strictly monotone if `a < b` implies `f a < f b`. -/
def strict_mono {α : Type u} {β : Type v} [HasLess α] [HasLess β] (f : α → β) :=
  ∀ {a b : α}, a < b → f a < f b

theorem strict_mono_id {α : Type u} [HasLess α] : strict_mono id :=
  fun (a b : α) => id

/-- A function `f` is strictly monotone increasing on `t` if `x < y` for `x,y ∈ t` implies
`f x < f y`. -/
def strict_mono_incr_on {α : Type u} {β : Type v} [HasLess α] [HasLess β] (f : α → β) (t : set α) :=
  ∀ {x : α}, x ∈ t → ∀ {y : α}, y ∈ t → x < y → f x < f y

/-- A function `f` is strictly monotone decreasing on `t` if `x < y` for `x,y ∈ t` implies
`f y < f x`. -/
def strict_mono_decr_on {α : Type u} {β : Type v} [HasLess α] [HasLess β] (f : α → β) (t : set α) :=
  ∀ {x : α}, x ∈ t → ∀ {y : α}, y ∈ t → x < y → f y < f x

/-- Type tag for a set with dual order: `≤` means `≥` and `<` means `>`. -/
def order_dual (α : Type u_1) :=
  α

namespace order_dual


protected instance nonempty (α : Type u_1) [h : Nonempty α] : Nonempty (order_dual α) :=
  h

protected instance subsingleton (α : Type u_1) [h : subsingleton α] : subsingleton (order_dual α) :=
  h

protected instance has_le (α : Type u_1) [HasLessEq α] : HasLessEq (order_dual α) :=
  { LessEq := fun (x y : α) => y ≤ x }

protected instance has_lt (α : Type u_1) [HasLess α] : HasLess (order_dual α) :=
  { Less := fun (x y : α) => y < x }

-- `dual_le` and `dual_lt` should not be simp lemmas:

-- they cause a loop since `α` and `order_dual α` are definitionally equal

theorem dual_le {α : Type u} [HasLessEq α] {a : α} {b : α} : a ≤ b ↔ b ≤ a :=
  iff.rfl

theorem dual_lt {α : Type u} [HasLess α] {a : α} {b : α} : a < b ↔ b < a :=
  iff.rfl

theorem dual_compares {α : Type u} [HasLess α] {a : α} {b : α} {o : ordering} : ordering.compares o a b ↔ ordering.compares o b a :=
  ordering.cases_on o iff.rfl eq_comm iff.rfl

protected instance preorder (α : Type u_1) [preorder α] : preorder (order_dual α) :=
  preorder.mk LessEq Less sorry sorry

protected instance partial_order (α : Type u_1) [partial_order α] : partial_order (order_dual α) :=
  partial_order.mk preorder.le preorder.lt sorry sorry sorry

protected instance linear_order (α : Type u_1) [linear_order α] : linear_order (order_dual α) :=
  linear_order.mk partial_order.le partial_order.lt sorry sorry sorry sorry
    ((fun (this : DecidableRel fun (a b : α) => b ≤ a) => this) fun (a b : α) => has_le.le.decidable b a)
    Mathlib.decidable_eq_of_decidable_le
    ((fun (this : DecidableRel fun (a b : α) => b < a) => this) fun (a b : α) => has_lt.lt.decidable b a)

protected instance inhabited {α : Type u} [Inhabited α] : Inhabited (order_dual α) :=
  id

theorem preorder.dual_dual (α : Type u_1) [H : preorder α] : order_dual.preorder (order_dual α) = H :=
  preorder.ext fun (_x _x_1 : order_dual (order_dual α)) => iff.rfl

theorem partial_order.dual_dual (α : Type u_1) [H : partial_order α] : order_dual.partial_order (order_dual α) = H :=
  partial_order.ext fun (_x _x_1 : order_dual (order_dual α)) => iff.rfl

theorem linear_order.dual_dual (α : Type u_1) [H : linear_order α] : order_dual.linear_order (order_dual α) = H :=
  linear_order.ext fun (_x _x_1 : order_dual (order_dual α)) => iff.rfl

theorem cmp_le_flip {α : Type u_1} [HasLessEq α] [DecidableRel LessEq] (x : α) (y : α) : cmp_le x y = cmp_le y x :=
  rfl

end order_dual


namespace strict_mono_incr_on


protected theorem dual {α : Type u} {β : Type v} [preorder α] [preorder β] {f : α → β} {s : set α} (H : strict_mono_incr_on f s) : strict_mono_incr_on f s :=
  fun (x : order_dual α) (hx : x ∈ s) (y : order_dual α) (hy : y ∈ s) => H hy hx

protected theorem dual_right {α : Type u} {β : Type v} [preorder α] [preorder β] {f : α → β} {s : set α} (H : strict_mono_incr_on f s) : strict_mono_decr_on f s :=
  H

theorem le_iff_le {α : Type u} {β : Type v} [linear_order α] [preorder β] {f : α → β} {s : set α} {x : α} {y : α} (H : strict_mono_incr_on f s) (hx : x ∈ s) (hy : y ∈ s) : f x ≤ f y ↔ x ≤ y := sorry

theorem lt_iff_lt {α : Type u} {β : Type v} [linear_order α] [preorder β] {f : α → β} {s : set α} {x : α} {y : α} (H : strict_mono_incr_on f s) (hx : x ∈ s) (hy : y ∈ s) : f x < f y ↔ x < y := sorry

protected theorem compares {α : Type u} {β : Type v} [linear_order α] [preorder β] {f : α → β} {s : set α} {x : α} {y : α} (H : strict_mono_incr_on f s) (hx : x ∈ s) (hy : y ∈ s) {o : ordering} : ordering.compares o (f x) (f y) ↔ ordering.compares o x y := sorry

end strict_mono_incr_on


namespace strict_mono_decr_on


protected theorem dual {α : Type u} {β : Type v} [preorder α] [preorder β] {f : α → β} {s : set α} (H : strict_mono_decr_on f s) : strict_mono_decr_on f s :=
  fun (x : order_dual α) (hx : x ∈ s) (y : order_dual α) (hy : y ∈ s) => H hy hx

protected theorem dual_right {α : Type u} {β : Type v} [preorder α] [preorder β] {f : α → β} {s : set α} (H : strict_mono_decr_on f s) : strict_mono_incr_on f s :=
  H

theorem le_iff_le {α : Type u} {β : Type v} [linear_order α] [preorder β] {f : α → β} {s : set α} {x : α} {y : α} (H : strict_mono_decr_on f s) (hx : x ∈ s) (hy : y ∈ s) : f x ≤ f y ↔ y ≤ x :=
  strict_mono_incr_on.le_iff_le (strict_mono_decr_on.dual_right H) hy hx

theorem lt_iff_lt {α : Type u} {β : Type v} [linear_order α] [preorder β] {f : α → β} {s : set α} {x : α} {y : α} (H : strict_mono_decr_on f s) (hx : x ∈ s) (hy : y ∈ s) : f x < f y ↔ y < x :=
  strict_mono_incr_on.lt_iff_lt (strict_mono_decr_on.dual_right H) hy hx

protected theorem compares {α : Type u} {β : Type v} [linear_order α] [preorder β] {f : α → β} {s : set α} {x : α} {y : α} (H : strict_mono_decr_on f s) (hx : x ∈ s) (hy : y ∈ s) {o : ordering} : ordering.compares o (f x) (f y) ↔ ordering.compares o y x :=
  iff.trans order_dual.dual_compares (strict_mono_incr_on.compares (strict_mono_decr_on.dual_right H) hy hx)

end strict_mono_decr_on


namespace strict_mono


protected theorem strict_mono_incr_on {α : Type u} {β : Type v} [HasLess α] [HasLess β] {f : α → β} (hf : strict_mono f) (s : set α) : strict_mono_incr_on f s :=
  fun (x : α) (hx : x ∈ s) (y : α) (hy : y ∈ s) (hxy : x < y) => hf hxy

theorem comp {α : Type u} {β : Type v} {γ : Type w} [HasLess α] [HasLess β] [HasLess γ] {g : β → γ} {f : α → β} (hg : strict_mono g) (hf : strict_mono f) : strict_mono (g ∘ f) :=
  fun (a b : α) (h : a < b) => hg (hf h)

protected theorem iterate {α : Type u} [HasLess α] {f : α → α} (hf : strict_mono f) (n : ℕ) : strict_mono (nat.iterate f n) :=
  nat.rec_on n strict_mono_id fun (n : ℕ) (ihn : strict_mono (nat.iterate f n)) => comp ihn hf

theorem id_le {φ : ℕ → ℕ} (h : strict_mono φ) (n : ℕ) : n ≤ φ n :=
  nat.rec_on n (nat.zero_le (φ 0))
    fun (n : ℕ) (hn : n ≤ φ n) => nat.succ_le_of_lt (lt_of_le_of_lt hn (h (nat.lt_succ_self n)))

protected theorem ite' {α : Type u} {β : Type v} [preorder α] [HasLess β] {f : α → β} {g : α → β} (hf : strict_mono f) (hg : strict_mono g) {p : α → Prop} [decidable_pred p] (hp : ∀ {x y : α}, x < y → p y → p x) (hfg : ∀ {x y : α}, p x → ¬p y → x < y → f x < g y) : strict_mono fun (x : α) => ite (p x) (f x) (g x) := sorry

protected theorem ite {α : Type u} {β : Type v} [preorder α] [preorder β] {f : α → β} {g : α → β} (hf : strict_mono f) (hg : strict_mono g) {p : α → Prop} [decidable_pred p] (hp : ∀ {x y : α}, x < y → p y → p x) (hfg : ∀ (x : α), f x ≤ g x) : strict_mono fun (x : α) => ite (p x) (f x) (g x) :=
  strict_mono.ite' hf hg hp fun (x y : α) (hx : p x) (hy : ¬p y) (h : x < y) => has_lt.lt.trans_le (hf h) (hfg y)

theorem lt_iff_lt {α : Type u} {β : Type v} [linear_order α] [preorder β] {f : α → β} (H : strict_mono f) {a : α} {b : α} : f a < f b ↔ a < b :=
  strict_mono_incr_on.lt_iff_lt (strict_mono.strict_mono_incr_on H set.univ) trivial trivial

protected theorem compares {α : Type u} {β : Type v} [linear_order α] [preorder β] {f : α → β} (H : strict_mono f) {a : α} {b : α} {o : ordering} : ordering.compares o (f a) (f b) ↔ ordering.compares o a b :=
  strict_mono_incr_on.compares (strict_mono.strict_mono_incr_on H set.univ) trivial trivial

theorem injective {α : Type u} {β : Type v} [linear_order α] [preorder β] {f : α → β} (H : strict_mono f) : function.injective f :=
  fun (x y : α) (h : f x = f y) =>
    (fun (this : ordering.compares ordering.eq x y) => this) (iff.mp (strict_mono.compares H) h)

theorem le_iff_le {α : Type u} {β : Type v} [linear_order α] [preorder β] {f : α → β} (H : strict_mono f) {a : α} {b : α} : f a ≤ f b ↔ a ≤ b :=
  strict_mono_incr_on.le_iff_le (strict_mono.strict_mono_incr_on H set.univ) trivial trivial

theorem top_preimage_top {α : Type u} {β : Type v} [linear_order α] [preorder β] {f : α → β} (H : strict_mono f) {a : α} (h_top : ∀ (p : β), p ≤ f a) (x : α) : x ≤ a :=
  iff.mp (le_iff_le H) (h_top (f x))

theorem bot_preimage_bot {α : Type u} {β : Type v} [linear_order α] [preorder β] {f : α → β} (H : strict_mono f) {a : α} (h_bot : ∀ (p : β), f a ≤ p) (x : α) : a ≤ x :=
  iff.mp (le_iff_le H) (h_bot (f x))

protected theorem nat {β : Type u_1} [preorder β] {f : ℕ → β} (h : ∀ (n : ℕ), f n < f (n + 1)) : strict_mono f := sorry

-- `preorder α` isn't strong enough: if the preorder on α is an equivalence relation,

-- then `strict_mono f` is vacuously true.

theorem monotone {α : Type u} {β : Type v} [partial_order α] [preorder β] {f : α → β} (H : strict_mono f) : monotone f :=
  fun (a b : α) (h : a ≤ b) =>
    Or._oldrec (le_of_lt ∘ H) (fun (h_1 : a = b) => Eq._oldrec (fun (h : a ≤ a) => le_refl (f a)) h_1 h)
      (lt_or_eq_of_le h)

end strict_mono


theorem injective_of_lt_imp_ne {α : Type u} {β : Type v} [linear_order α] {f : α → β} (h : ∀ (x y : α), x < y → f x ≠ f y) : function.injective f := sorry

theorem strict_mono_of_monotone_of_injective {α : Type u} {β : Type v} [partial_order α] [partial_order β] {f : α → β} (h₁ : monotone f) (h₂ : function.injective f) : strict_mono f := sorry

theorem monotone.strict_mono_iff_injective {α : Type u} {β : Type v} [linear_order α] [partial_order β] {f : α → β} (h : monotone f) : strict_mono f ↔ function.injective f :=
  { mp := fun (h : strict_mono f) => strict_mono.injective h, mpr := strict_mono_of_monotone_of_injective h }

theorem strict_mono_of_le_iff_le {α : Type u} {β : Type v} [preorder α] [preorder β] {f : α → β} (h : ∀ (x y : α), x ≤ y ↔ f x ≤ f y) : strict_mono f := sorry

/-! ### Order instances on the function space -/

protected instance pi.preorder {ι : Type u} {α : ι → Type v} [(i : ι) → preorder (α i)] : preorder ((i : ι) → α i) :=
  preorder.mk (fun (x y : (i : ι) → α i) => ∀ (i : ι), x i ≤ y i)
    (fun (a b : (i : ι) → α i) => (∀ (i : ι), a i ≤ b i) ∧ ¬∀ (i : ι), b i ≤ a i) sorry sorry

theorem pi.le_def {ι : Type u} {α : ι → Type v} [(i : ι) → preorder (α i)] {x : (i : ι) → α i} {y : (i : ι) → α i} : x ≤ y ↔ ∀ (i : ι), x i ≤ y i :=
  iff.rfl

theorem le_update_iff {ι : Type u} {α : ι → Type v} [(i : ι) → preorder (α i)] [DecidableEq ι] {x : (i : ι) → α i} {y : (i : ι) → α i} {i : ι} {a : α i} : x ≤ function.update y i a ↔ x i ≤ a ∧ ∀ (j : ι), j ≠ i → x j ≤ y j :=
  function.forall_update_iff y fun (j : ι) (z : α j) => x j ≤ z

theorem update_le_iff {ι : Type u} {α : ι → Type v} [(i : ι) → preorder (α i)] [DecidableEq ι] {x : (i : ι) → α i} {y : (i : ι) → α i} {i : ι} {a : α i} : function.update x i a ≤ y ↔ a ≤ y i ∧ ∀ (j : ι), j ≠ i → x j ≤ y j :=
  function.forall_update_iff x fun (j : ι) (z : α j) => z ≤ y j

protected instance pi.partial_order {ι : Type u} {α : ι → Type v} [(i : ι) → partial_order (α i)] : partial_order ((i : ι) → α i) :=
  partial_order.mk preorder.le preorder.lt sorry sorry sorry

theorem comp_le_comp_left_of_monotone {α : Type u} {β : Type v} {γ : Type w} [preorder α] [preorder β] {f : β → α} {g : γ → β} {h : γ → β} (m_f : monotone f) (le_gh : g ≤ h) : f ∘ g ≤ f ∘ h :=
  fun (x : γ) => m_f (le_gh x)

protected theorem monotone.order_dual {α : Type u} {γ : Type w} [preorder α] [preorder γ] {f : α → γ} (hf : monotone f) : monotone f :=
  fun (x y : order_dual α) (hxy : x ≤ y) => hf hxy

theorem monotone_lam {α : Type u} {β : Type v} {γ : Type w} [preorder α] [preorder γ] {f : α → β → γ} (m : ∀ (b : β), monotone fun (a : α) => f a b) : monotone f :=
  fun (a a' : α) (h : a ≤ a') (b : β) => m b h

theorem monotone_app {α : Type u} {β : Type v} {γ : Type w} [preorder α] [preorder γ] (f : β → α → γ) (b : β) (m : monotone fun (a : α) (b : β) => f b a) : monotone (f b) :=
  fun (a a' : α) (h : a ≤ a') => m h b

theorem strict_mono.order_dual {α : Type u} {β : Type v} [HasLess α] [HasLess β] {f : α → β} (hf : strict_mono f) : strict_mono f :=
  fun (x y : order_dual α) (hxy : x < y) => hf hxy

/-- Transfer a `preorder` on `β` to a `preorder` on `α` using a function `f : α → β`. -/
def preorder.lift {α : Type u_1} {β : Type u_2} [preorder β] (f : α → β) : preorder α :=
  preorder.mk (fun (x y : α) => f x ≤ f y) (fun (x y : α) => f x < f y) sorry sorry

/-- Transfer a `partial_order` on `β` to a `partial_order` on `α` using an injective
function `f : α → β`. -/
def partial_order.lift {α : Type u_1} {β : Type u_2} [partial_order β] (f : α → β) (inj : function.injective f) : partial_order α :=
  partial_order.mk preorder.le preorder.lt sorry sorry sorry

/-- Transfer a `linear_order` on `β` to a `linear_order` on `α` using an injective
function `f : α → β`. -/
def linear_order.lift {α : Type u_1} {β : Type u_2} [linear_order β] (f : α → β) (inj : function.injective f) : linear_order α :=
  linear_order.mk partial_order.le partial_order.lt sorry sorry sorry sorry (fun (x y : α) => infer_instance)
    (fun (x y : α) => decidable_of_iff (f x = f y) (function.injective.eq_iff inj)) fun (x y : α) => infer_instance

protected instance subtype.preorder {α : Type u_1} [preorder α] (p : α → Prop) : preorder (Subtype p) :=
  preorder.lift subtype.val

@[simp] theorem subtype.mk_le_mk {α : Type u_1} [preorder α] {p : α → Prop} {x : α} {y : α} {hx : p x} {hy : p y} : { val := x, property := hx } ≤ { val := y, property := hy } ↔ x ≤ y :=
  iff.rfl

@[simp] theorem subtype.mk_lt_mk {α : Type u_1} [preorder α] {p : α → Prop} {x : α} {y : α} {hx : p x} {hy : p y} : { val := x, property := hx } < { val := y, property := hy } ↔ x < y :=
  iff.rfl

@[simp] theorem subtype.coe_le_coe {α : Type u_1} [preorder α] {p : α → Prop} {x : Subtype p} {y : Subtype p} : ↑x ≤ ↑y ↔ x ≤ y :=
  iff.rfl

@[simp] theorem subtype.coe_lt_coe {α : Type u_1} [preorder α] {p : α → Prop} {x : Subtype p} {y : Subtype p} : ↑x < ↑y ↔ x < y :=
  iff.rfl

protected instance subtype.partial_order {α : Type u_1} [partial_order α] (p : α → Prop) : partial_order (Subtype p) :=
  partial_order.lift subtype.val subtype.val_injective

protected instance subtype.linear_order {α : Type u_1} [linear_order α] (p : α → Prop) : linear_order (Subtype p) :=
  linear_order.lift subtype.val subtype.val_injective

theorem subtype.mono_coe {α : Type u} [preorder α] (t : set α) : monotone coe :=
  fun (x y : Subtype t) => id

theorem subtype.strict_mono_coe {α : Type u} [preorder α] (t : set α) : strict_mono coe :=
  fun (x y : Subtype t) => id

protected instance prod.has_le (α : Type u) (β : Type v) [HasLessEq α] [HasLessEq β] : HasLessEq (α × β) :=
  { LessEq := fun (p q : α × β) => prod.fst p ≤ prod.fst q ∧ prod.snd p ≤ prod.snd q }

protected instance prod.preorder (α : Type u) (β : Type v) [preorder α] [preorder β] : preorder (α × β) :=
  preorder.mk LessEq (fun (a b : α × β) => a ≤ b ∧ ¬b ≤ a) sorry sorry

/-- The pointwise partial order on a product.
    (The lexicographic ordering is defined in order/lexicographic.lean, and the instances are
    available via the type synonym `lex α β = α × β`.) -/
protected instance prod.partial_order (α : Type u) (β : Type v) [partial_order α] [partial_order β] : partial_order (α × β) :=
  partial_order.mk preorder.le preorder.lt sorry sorry sorry

/-!
### Additional order classes
-/

/-- order without a top element; somtimes called cofinal -/
class no_top_order (α : Type u) [preorder α] 
where
  no_top : ∀ (a : α), ∃ (a' : α), a < a'

theorem no_top {α : Type u} [preorder α] [no_top_order α] (a : α) : ∃ (a' : α), a < a' :=
  no_top_order.no_top

protected instance nonempty_gt {α : Type u} [preorder α] [no_top_order α] (a : α) : Nonempty (Subtype fun (x : α) => a < x) :=
  iff.mpr nonempty_subtype (no_top a)

/-- order without a bottom element; somtimes called coinitial or dense -/
class no_bot_order (α : Type u) [preorder α] 
where
  no_bot : ∀ (a : α), ∃ (a' : α), a' < a

theorem no_bot {α : Type u} [preorder α] [no_bot_order α] (a : α) : ∃ (a' : α), a' < a :=
  no_bot_order.no_bot

protected instance order_dual.no_top_order (α : Type u) [preorder α] [no_bot_order α] : no_top_order (order_dual α) :=
  no_top_order.mk fun (a : order_dual α) => no_bot a

protected instance order_dual.no_bot_order (α : Type u) [preorder α] [no_top_order α] : no_bot_order (order_dual α) :=
  no_bot_order.mk fun (a : order_dual α) => no_top a

protected instance nonempty_lt {α : Type u} [preorder α] [no_bot_order α] (a : α) : Nonempty (Subtype fun (x : α) => x < a) :=
  iff.mpr nonempty_subtype (no_bot a)

/-- An order is dense if there is an element between any pair of distinct elements. -/
class densely_ordered (α : Type u) [preorder α] 
where
  dense : ∀ (a₁ a₂ : α), a₁ < a₂ → ∃ (a : α), a₁ < a ∧ a < a₂

theorem exists_between {α : Type u} [preorder α] [densely_ordered α] {a₁ : α} {a₂ : α} : a₁ < a₂ → ∃ (a : α), a₁ < a ∧ a < a₂ :=
  densely_ordered.dense

protected instance order_dual.densely_ordered (α : Type u) [preorder α] [densely_ordered α] : densely_ordered (order_dual α) :=
  densely_ordered.mk fun (a₁ a₂ : order_dual α) (ha : a₁ < a₂) => Exists.imp (fun (a : α) => and.symm) (exists_between ha)

theorem le_of_forall_le_of_dense {α : Type u} [linear_order α] [densely_ordered α] {a₁ : α} {a₂ : α} (h : ∀ (a₃ : α), a₃ > a₂ → a₁ ≤ a₃) : a₁ ≤ a₂ := sorry

theorem eq_of_le_of_forall_le_of_dense {α : Type u} [linear_order α] [densely_ordered α] {a₁ : α} {a₂ : α} (h₁ : a₂ ≤ a₁) (h₂ : ∀ (a₃ : α), a₃ > a₂ → a₁ ≤ a₃) : a₁ = a₂ :=
  le_antisymm (le_of_forall_le_of_dense h₂) h₁

theorem le_of_forall_ge_of_dense {α : Type u} [linear_order α] [densely_ordered α] {a₁ : α} {a₂ : α} (h : ∀ (a₃ : α), a₃ < a₁ → a₃ ≤ a₂) : a₁ ≤ a₂ := sorry

theorem eq_of_le_of_forall_ge_of_dense {α : Type u} [linear_order α] [densely_ordered α] {a₁ : α} {a₂ : α} (h₁ : a₂ ≤ a₁) (h₂ : ∀ (a₃ : α), a₃ < a₁ → a₃ ≤ a₂) : a₁ = a₂ :=
  le_antisymm (le_of_forall_ge_of_dense h₂) h₁

theorem dense_or_discrete {α : Type u} [linear_order α] (a₁ : α) (a₂ : α) : (∃ (a : α), a₁ < a ∧ a < a₂) ∨ (∀ (a : α), a > a₁ → a₂ ≤ a) ∧ ∀ (a : α), a < a₂ → a ≤ a₁ := sorry

/-- Type synonym to create an instance of `linear_order` from a
`partial_order` and `[is_total α (≤)]` -/
def as_linear_order (α : Type u) :=
  α

protected instance as_linear_order.inhabited {α : Type u_1} [Inhabited α] : Inhabited (as_linear_order α) :=
  { default := Inhabited.default }

protected instance as_linear_order.linear_order {α : Type u_1} [partial_order α] [is_total α LessEq] : linear_order (as_linear_order α) :=
  linear_order.mk partial_order.le partial_order.lt partial_order.le_refl partial_order.le_trans partial_order.le_antisymm
    sorry (classical.dec_rel LessEq) Mathlib.decidable_eq_of_decidable_le Mathlib.decidable_lt_of_decidable_le

