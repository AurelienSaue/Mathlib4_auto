/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.pfun
import Mathlib.order.preorder_hom
import Mathlib.tactic.wlog
import Mathlib.tactic.monotonicity.default
import PostPort

universes u_1 u_2 u_5 u_6 u_3 u v l u_4 

namespace Mathlib

/-!
# Omega Complete Partial Orders

An omega-complete partial order is a partial order with a supremum
operation on increasing sequences indexed by natural numbers (which we
call `ωSup`). In this sense, it is strictly weaker than join complete
semi-lattices as only ω-sized totally ordered sets have a supremum.

The concept of an omega-complete partial order (ωCPO) is useful for the
formalization of the semantics of programming languages. Its notion of
supremum helps define the meaning of recursive procedures.

## Main definitions

 * class `omega_complete_partial_order`
 * `ite`, `map`, `bind`, `seq` as continuous morphisms

## Instances of `omega_complete_partial_order`

 * `roption`
 * every `complete_lattice`
 * pi-types
 * product types
 * `monotone_hom`
 * `continuous_hom` (with notation →𝒄)
   * an instance of `omega_complete_partial_order (α →𝒄 β)`
 * `continuous_hom.of_fun`
 * `continuous_hom.of_mono`
 * continuous functions:
   * `id`
   * `ite`
   * `const`
   * `roption.bind`
   * `roption.map`
   * `roption.seq`

## References

 * [G. Markowsky, *Chain-complete posets and directed sets with applications*, https://doi.org/10.1007/BF02485815][markowsky]
 * [J. M. Cadiou and Zohar Manna, *Recursive definitions of partial functions and their computations.*, https://doi.org/10.1145/942580.807072][cadiou]
 * [Carl A. Gunter, *Semantics of Programming Languages: Structures and Techniques*, ISBN: 0262570955][gunter]
-/

namespace preorder_hom


/-- The constant function, as a monotone function. -/
@[simp] theorem const_to_fun (α : Type u_1) {β : Type u_2} [preorder α] [preorder β] (f : β) : ∀ (ᾰ : α), coe_fn (const α f) ᾰ = function.const α f ᾰ :=
  fun (ᾰ : α) => Eq.refl (coe_fn (const α f) ᾰ)

/-- The diagonal function, as a monotone function. -/
def prod.diag {α : Type u_1} [preorder α] : α →ₘ α × α :=
  mk (fun (x : α) => (x, x)) sorry

/-- The `prod.map` function, as a monotone function. -/
@[simp] theorem prod.map_to_fun {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] {α' : Type u_5} {β' : Type u_6} [preorder α'] [preorder β'] (f : α →ₘ β) (f' : α' →ₘ β') (x : α × α') : coe_fn (prod.map f f') x = prod.map (⇑f) (⇑f') x :=
  Eq.refl (coe_fn (prod.map f f') x)

/-- The `prod.fst` projection, as a monotone function. -/
def prod.fst {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] : α × β →ₘ α :=
  mk prod.fst sorry

/-- The `prod.snd` projection, as a monotone function. -/
def prod.snd {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] : α × β →ₘ β :=
  mk prod.snd sorry

/-- The `prod` constructor, as a monotone function. -/
@[simp] theorem prod.zip_to_fun {α : Type u_1} {β : Type u_2} {γ : Type u_3} [preorder α] [preorder β] [preorder γ] (f : α →ₘ β) (g : α →ₘ γ) : ∀ (ᾰ : α), coe_fn (prod.zip f g) ᾰ = (coe_fn f ᾰ, coe_fn g ᾰ) :=
  fun (ᾰ : α) => Eq.refl (coe_fn f ᾰ, coe_fn g ᾰ)

/-- `roption.bind` as a monotone function -/
@[simp] theorem bind_to_fun {α : Type u_1} [preorder α] {β : Type u_2} {γ : Type u_2} (f : α →ₘ roption β) (g : α →ₘ β → roption γ) (x : α) : coe_fn (bind f g) x = coe_fn f x >>= coe_fn g x :=
  Eq.refl (coe_fn (bind f g) x)

end preorder_hom


namespace omega_complete_partial_order


/-- A chain is a monotonically increasing sequence.

See the definition on page 114 of [gunter]. -/
def chain (α : Type u) [preorder α]  :=
  ℕ →ₘ α

namespace chain


protected instance has_coe_to_fun {α : Type u} [preorder α] : has_coe_to_fun (chain α) :=
  infer_instance

protected instance inhabited {α : Type u} [preorder α] [Inhabited α] : Inhabited (chain α) :=
  { default := preorder_hom.mk (fun (_x : ℕ) => Inhabited.default) sorry }

protected instance has_mem {α : Type u} [preorder α] : has_mem α (chain α) :=
  has_mem.mk fun (a : α) (c : ℕ →ₘ α) => ∃ (i : ℕ), a = coe_fn c i

protected instance has_le {α : Type u} [preorder α] : HasLessEq (chain α) :=
  { LessEq := fun (x y : chain α) => ∀ (i : ℕ), ∃ (j : ℕ), coe_fn x i ≤ coe_fn y j }

/-- `map` function for `chain` -/
@[simp] theorem map_to_fun {α : Type u} {β : Type v} [preorder α] [preorder β] (c : chain α) (f : α →ₘ β) : ∀ (ᾰ : ℕ), coe_fn (map c f) ᾰ = coe_fn f (coe_fn c ᾰ) :=
  fun (ᾰ : ℕ) => Eq.refl (coe_fn f (coe_fn c ᾰ))

theorem mem_map {α : Type u} {β : Type v} [preorder α] [preorder β] (c : chain α) {f : α →ₘ β} (x : α) : x ∈ c → coe_fn f x ∈ map c f := sorry

theorem exists_of_mem_map {α : Type u} {β : Type v} [preorder α] [preorder β] (c : chain α) {f : α →ₘ β} {b : β} : b ∈ map c f → ∃ (a : α), a ∈ c ∧ coe_fn f a = b := sorry

theorem mem_map_iff {α : Type u} {β : Type v} [preorder α] [preorder β] (c : chain α) {f : α →ₘ β} {b : β} : b ∈ map c f ↔ ∃ (a : α), a ∈ c ∧ coe_fn f a = b := sorry

@[simp] theorem map_id {α : Type u} [preorder α] (c : chain α) : map c preorder_hom.id = c :=
  preorder_hom.comp_id c

theorem map_comp {α : Type u} {β : Type v} {γ : Type u_1} [preorder α] [preorder β] [preorder γ] (c : chain α) {f : α →ₘ β} (g : β →ₘ γ) : map (map c f) g = map c (preorder_hom.comp g f) :=
  rfl

theorem map_le_map {α : Type u} {β : Type v} [preorder α] [preorder β] (c : chain α) {f : α →ₘ β} {g : α →ₘ β} (h : f ≤ g) : map c f ≤ map c g := sorry

/-- `chain.zip` pairs up the elements of two chains that have the same index -/
@[simp] theorem zip_to_fun {α : Type u} {β : Type v} [preorder α] [preorder β] (c₀ : chain α) (c₁ : chain β) : ∀ (ᾰ : ℕ), coe_fn (zip c₀ c₁) ᾰ = (coe_fn c₀ ᾰ, coe_fn c₁ ᾰ) :=
  fun (ᾰ : ℕ) => Eq.refl (coe_fn c₀ ᾰ, coe_fn c₁ ᾰ)

end chain


end omega_complete_partial_order


/-- An omega-complete partial order is a partial order with a supremum
operation on increasing sequences indexed by natural numbers (which we
call `ωSup`). In this sense, it is strictly weaker than join complete
semi-lattices as only ω-sized totally ordered sets have a supremum.

See the definition on page 114 of [gunter]. -/
class omega_complete_partial_order (α : Type u_1) 
extends partial_order α
where
  ωSup : omega_complete_partial_order.chain α → α
  le_ωSup : ∀ (c : omega_complete_partial_order.chain α) (i : ℕ), coe_fn c i ≤ ωSup c
  ωSup_le : ∀ (c : omega_complete_partial_order.chain α) (x : α), (∀ (i : ℕ), coe_fn c i ≤ x) → ωSup c ≤ x

namespace omega_complete_partial_order


/-- Transfer a `omega_complete_partial_order` on `β` to a `omega_complete_partial_order` on `α` using
a strictly monotone function `f : β →ₘ α`, a definition of ωSup and a proof that `f` is continuous
with regard to the provided `ωSup` and the ωCPO on `α`. -/
protected def lift {α : Type u} {β : Type v} [omega_complete_partial_order α] [partial_order β] (f : β →ₘ α) (ωSup₀ : chain β → β) (h : ∀ (x y : β), coe_fn f x ≤ coe_fn f y → x ≤ y) (h' : ∀ (c : chain β), coe_fn f (ωSup₀ c) = ωSup (chain.map c f)) : omega_complete_partial_order β :=
  mk ωSup₀ sorry sorry

theorem le_ωSup_of_le {α : Type u} [omega_complete_partial_order α] {c : chain α} {x : α} (i : ℕ) (h : x ≤ coe_fn c i) : x ≤ ωSup c :=
  le_trans h (le_ωSup c i)

theorem ωSup_total {α : Type u} [omega_complete_partial_order α] {c : chain α} {x : α} (h : ∀ (i : ℕ), coe_fn c i ≤ x ∨ x ≤ coe_fn c i) : ωSup c ≤ x ∨ x ≤ ωSup c := sorry

theorem ωSup_le_ωSup_of_le {α : Type u} [omega_complete_partial_order α] {c₀ : chain α} {c₁ : chain α} (h : c₀ ≤ c₁) : ωSup c₀ ≤ ωSup c₁ :=
  ωSup_le c₀ (ωSup c₁)
    fun (i : ℕ) => Exists.rec_on (h i) fun (j : ℕ) (h : coe_fn c₀ i ≤ coe_fn c₁ j) => le_trans h (le_ωSup c₁ j)

theorem ωSup_le_iff {α : Type u} [omega_complete_partial_order α] (c : chain α) (x : α) : ωSup c ≤ x ↔ ∀ (i : ℕ), coe_fn c i ≤ x :=
  { mp := fun (ᾰ : ωSup c ≤ x) (i : ℕ) => le_trans (le_ωSup c i) ᾰ,
    mpr := fun (ᾰ : ∀ (i : ℕ), coe_fn c i ≤ x) => ωSup_le c x ᾰ }

/-- A subset `p : α → Prop` of the type closed under `ωSup` induces an
`omega_complete_partial_order` on the subtype `{a : α // p a}`. -/
def subtype {α : Type u_1} [omega_complete_partial_order α] (p : α → Prop) (hp : ∀ (c : chain α), (∀ (i : α), i ∈ c → p i) → p (ωSup c)) : omega_complete_partial_order (Subtype p) :=
  omega_complete_partial_order.lift (preorder_hom.subtype.val p)
    (fun (c : chain (Subtype p)) => { val := ωSup (chain.map c (preorder_hom.subtype.val p)), property := sorry }) sorry
    sorry

/-- A monotone function `f : α →ₘ β` is continuous if it distributes over ωSup.

In order to distinguish it from the (more commonly used) continuity from topology
(see topology/basic.lean), the present definition is often referred to as
"Scott-continuity" (referring to Dana Scott). It corresponds to continuity
in Scott topological spaces (not defined here). -/
def continuous {α : Type u} {β : Type v} [omega_complete_partial_order α] [omega_complete_partial_order β] (f : α →ₘ β)  :=
  ∀ (c : chain α), coe_fn f (ωSup c) = ωSup (chain.map c f)

/-- `continuous' f` asserts that `f` is both monotone and continuous. -/
def continuous' {α : Type u} {β : Type v} [omega_complete_partial_order α] [omega_complete_partial_order β] (f : α → β)  :=
  ∃ (hf : monotone f), continuous (preorder_hom.mk f hf)

theorem continuous.to_monotone {α : Type u} {β : Type v} [omega_complete_partial_order α] [omega_complete_partial_order β] {f : α → β} (hf : continuous' f) : monotone f :=
  Exists.fst hf

theorem continuous.of_bundled {α : Type u} {β : Type v} [omega_complete_partial_order α] [omega_complete_partial_order β] (f : α → β) (hf : monotone f) (hf' : continuous (preorder_hom.mk f hf)) : continuous' f :=
  Exists.intro hf hf'

theorem continuous.of_bundled' {α : Type u} {β : Type v} [omega_complete_partial_order α] [omega_complete_partial_order β] (f : α →ₘ β) (hf' : continuous f) : continuous' ⇑f :=
  Exists.intro (preorder_hom.monotone f) hf'

theorem continuous.to_bundled {α : Type u} {β : Type v} [omega_complete_partial_order α] [omega_complete_partial_order β] (f : α → β) (hf : continuous' f) : continuous (preorder_hom.mk f (continuous.to_monotone hf)) :=
  Exists.snd hf

theorem continuous_id {α : Type u} [omega_complete_partial_order α] : continuous preorder_hom.id := sorry

theorem continuous_comp {α : Type u} {β : Type v} {γ : Type u_1} [omega_complete_partial_order α] [omega_complete_partial_order β] [omega_complete_partial_order γ] (f : α →ₘ β) (g : β →ₘ γ) (hfc : continuous f) (hgc : continuous g) : continuous (preorder_hom.comp g f) := sorry

theorem id_continuous' {α : Type u} [omega_complete_partial_order α] : continuous' id := sorry

theorem const_continuous' {α : Type u} {β : Type v} [omega_complete_partial_order α] [omega_complete_partial_order β] (x : β) : continuous' (function.const α x) := sorry

end omega_complete_partial_order


namespace roption


theorem eq_of_chain {α : Type u} {c : omega_complete_partial_order.chain (roption α)} {a : α} {b : α} (ha : some a ∈ c) (hb : some b ∈ c) : a = b := sorry

/-- The (noncomputable) `ωSup` definition for the `ω`-CPO structure on `roption α`. -/
protected def ωSup {α : Type u} (c : omega_complete_partial_order.chain (roption α)) : roption α :=
  dite (∃ (a : α), some a ∈ c) (fun (h : ∃ (a : α), some a ∈ c) => some (classical.some h))
    fun (h : ¬∃ (a : α), some a ∈ c) => none

theorem ωSup_eq_some {α : Type u} {c : omega_complete_partial_order.chain (roption α)} {a : α} (h : some a ∈ c) : roption.ωSup c = some a := sorry

theorem ωSup_eq_none {α : Type u} {c : omega_complete_partial_order.chain (roption α)} (h : ¬∃ (a : α), some a ∈ c) : roption.ωSup c = none :=
  dif_neg h

theorem mem_chain_of_mem_ωSup {α : Type u} {c : omega_complete_partial_order.chain (roption α)} {a : α} (h : a ∈ roption.ωSup c) : some a ∈ c := sorry

protected instance omega_complete_partial_order {α : Type u} : omega_complete_partial_order (roption α) :=
  omega_complete_partial_order.mk roption.ωSup sorry sorry

theorem mem_ωSup {α : Type u} (x : α) (c : omega_complete_partial_order.chain (roption α)) : x ∈ omega_complete_partial_order.ωSup c ↔ some x ∈ c := sorry

end roption


namespace pi


/-- Function application `λ f, f a` is monotone with respect to `f` for fixed `a`. -/
def monotone_apply {α : Type u_1} {β : α → Type u_2} [(a : α) → partial_order (β a)] (a : α) : ((a : α) → β a) →ₘ β a :=
  preorder_hom.mk (fun (f : (a : α) → β a) => f a) sorry

protected instance omega_complete_partial_order {α : Type u_1} {β : α → Type u_2} [(a : α) → omega_complete_partial_order (β a)] : omega_complete_partial_order ((a : α) → β a) :=
  omega_complete_partial_order.mk
    (fun (c : omega_complete_partial_order.chain ((a : α) → β a)) (a : α) =>
      omega_complete_partial_order.ωSup (omega_complete_partial_order.chain.map c (monotone_apply a)))
    sorry sorry

namespace omega_complete_partial_order


theorem flip₁_continuous' {α : Type u_1} {β : α → Type u_2} {γ : Type u_3} [(x : α) → omega_complete_partial_order (β x)] [omega_complete_partial_order γ] (f : (x : α) → γ → β x) (a : α) (hf : omega_complete_partial_order.continuous' fun (x : γ) (y : α) => f y x) : omega_complete_partial_order.continuous' (f a) := sorry

theorem flip₂_continuous' {α : Type u_1} {β : α → Type u_2} {γ : Type u_3} [(x : α) → omega_complete_partial_order (β x)] [omega_complete_partial_order γ] (f : γ → (x : α) → β x) (hf : ∀ (x : α), omega_complete_partial_order.continuous' fun (g : γ) => f g x) : omega_complete_partial_order.continuous' f := sorry

end omega_complete_partial_order


end pi


namespace prod


/-- The supremum of a chain in the product `ω`-CPO. -/
protected def ωSup {α : Type u_1} {β : Type u_2} [omega_complete_partial_order α] [omega_complete_partial_order β] (c : omega_complete_partial_order.chain (α × β)) : α × β :=
  (omega_complete_partial_order.ωSup (omega_complete_partial_order.chain.map c preorder_hom.prod.fst),
  omega_complete_partial_order.ωSup (omega_complete_partial_order.chain.map c preorder_hom.prod.snd))

protected instance omega_complete_partial_order {α : Type u_1} {β : Type u_2} [omega_complete_partial_order α] [omega_complete_partial_order β] : omega_complete_partial_order (α × β) :=
  omega_complete_partial_order.mk prod.ωSup sorry sorry

end prod


namespace complete_lattice


/-- Any complete lattice has an `ω`-CPO structure where the countable supremum is a special case
of arbitrary suprema. -/
protected instance omega_complete_partial_order (α : Type u) [complete_lattice α] : omega_complete_partial_order α :=
  omega_complete_partial_order.mk (fun (c : omega_complete_partial_order.chain α) => supr fun (i : ℕ) => coe_fn c i) sorry
    sorry

theorem inf_continuous {α : Type u} {β : Type v} [omega_complete_partial_order α] [complete_lattice β] [is_total β LessEq] (f : α →ₘ β) (g : α →ₘ β) (hf : omega_complete_partial_order.continuous f) (hg : omega_complete_partial_order.continuous g) : omega_complete_partial_order.continuous (f ⊓ g) := sorry

theorem Sup_continuous {α : Type u} {β : Type v} [omega_complete_partial_order α] [complete_lattice β] (s : set (α →ₘ β)) (hs : ∀ (f : α →ₘ β), f ∈ s → omega_complete_partial_order.continuous f) : omega_complete_partial_order.continuous (Sup s) := sorry

theorem Sup_continuous' {α : Type u} {β : Type v} [omega_complete_partial_order α] [complete_lattice β] (s : set (α → β)) : (∀ (t : α → β), t ∈ s → omega_complete_partial_order.continuous' t) → omega_complete_partial_order.continuous' (Sup s) := sorry

theorem sup_continuous {α : Type u} {β : Type v} [omega_complete_partial_order α] [complete_lattice β] {f : α →ₘ β} {g : α →ₘ β} (hf : omega_complete_partial_order.continuous f) (hg : omega_complete_partial_order.continuous g) : omega_complete_partial_order.continuous (f ⊔ g) := sorry

theorem top_continuous {α : Type u} {β : Type v} [omega_complete_partial_order α] [complete_lattice β] : omega_complete_partial_order.continuous ⊤ := sorry

theorem bot_continuous {α : Type u} {β : Type v} [omega_complete_partial_order α] [complete_lattice β] : omega_complete_partial_order.continuous ⊥ := sorry

end complete_lattice


namespace omega_complete_partial_order


namespace preorder_hom


/-- Function application `λ f, f a` (for fixed `a`) is a monotone function from the
monotone function space `α →ₘ β` to `β`. -/
def monotone_apply {α : Type u} {β : Type v} [omega_complete_partial_order α] [omega_complete_partial_order β] (a : α) : (α →ₘ β) →ₘ β :=
  preorder_hom.mk (fun (f : α →ₘ β) => coe_fn f a) sorry

/-- The "forgetful functor" from `α →ₘ β` to `α → β` that takes the underlying function,
is monotone. -/
def to_fun_hom {α : Type u} {β : Type v} [omega_complete_partial_order α] [omega_complete_partial_order β] : (α →ₘ β) →ₘ α → β :=
  preorder_hom.mk (fun (f : α →ₘ β) => preorder_hom.to_fun f) sorry

/-- The `ωSup` operator for monotone functions. -/
@[simp] theorem ωSup_to_fun {α : Type u} {β : Type v} [omega_complete_partial_order α] [omega_complete_partial_order β] (c : chain (α →ₘ β)) (a : α) : coe_fn (preorder_hom.ωSup c) a = ωSup (chain.map c (monotone_apply a)) :=
  Eq.refl (coe_fn (preorder_hom.ωSup c) a)

protected instance omega_complete_partial_order {α : Type u} {β : Type v} [omega_complete_partial_order α] [omega_complete_partial_order β] : omega_complete_partial_order (α →ₘ β) :=
  omega_complete_partial_order.lift to_fun_hom preorder_hom.ωSup sorry sorry

end preorder_hom


/-- A monotone function on `ω`-continuous partial orders is said to be continuous
if for every chain `c : chain α`, `f (⊔ i, c i) = ⊔ i, f (c i)`.
This is just the bundled version of `preorder_hom.continuous`. -/
structure continuous_hom (α : Type u) (β : Type v) [omega_complete_partial_order α] [omega_complete_partial_order β] 
extends α →ₘ β
where
  cont : continuous (preorder_hom.mk to_fun monotone')

infixr:25 " →𝒄 " => Mathlib.omega_complete_partial_order.continuous_hom

protected instance continuous_hom.has_coe_to_fun (α : Type u) (β : Type v) [omega_complete_partial_order α] [omega_complete_partial_order β] : has_coe_to_fun (α →𝒄 β) :=
  has_coe_to_fun.mk (fun (_x : α →𝒄 β) => α → β) continuous_hom.to_fun

protected instance preorder_hom.has_coe (α : Type u) (β : Type v) [omega_complete_partial_order α] [omega_complete_partial_order β] : has_coe (α →𝒄 β) (α →ₘ β) :=
  has_coe.mk continuous_hom.to_preorder_hom

protected instance continuous_hom.partial_order (α : Type u) (β : Type v) [omega_complete_partial_order α] [omega_complete_partial_order β] : partial_order (α →𝒄 β) :=
  partial_order.lift continuous_hom.to_fun sorry

namespace continuous_hom


theorem congr_fun {α : Type u} {β : Type v} [omega_complete_partial_order α] [omega_complete_partial_order β] {f : α →𝒄 β} {g : α →𝒄 β} (h : f = g) (x : α) : coe_fn f x = coe_fn g x :=
  congr_arg (fun (h : α →𝒄 β) => coe_fn h x) h

theorem congr_arg {α : Type u} {β : Type v} [omega_complete_partial_order α] [omega_complete_partial_order β] (f : α →𝒄 β) {x : α} {y : α} (h : x = y) : coe_fn f x = coe_fn f y :=
  congr_arg (fun (x : α) => coe_fn f x) h

theorem monotone {α : Type u} {β : Type v} [omega_complete_partial_order α] [omega_complete_partial_order β] (f : α →𝒄 β) : monotone ⇑f :=
  monotone' f

theorem ite_continuous' {α : Type u} {β : Type v} [omega_complete_partial_order α] [omega_complete_partial_order β] {p : Prop} [hp : Decidable p] (f : α → β) (g : α → β) (hf : continuous' f) (hg : continuous' g) : continuous' fun (x : α) => ite p (f x) (g x) := sorry

theorem ωSup_bind {α : Type u} [omega_complete_partial_order α] {β : Type v} {γ : Type v} (c : chain α) (f : α →ₘ roption β) (g : α →ₘ β → roption γ) : ωSup (chain.map c (preorder_hom.bind f g)) = ωSup (chain.map c f) >>= ωSup (chain.map c g) := sorry

theorem bind_continuous' {α : Type u} [omega_complete_partial_order α] {β : Type v} {γ : Type v} (f : α → roption β) (g : α → β → roption γ) : continuous' f → continuous' g → continuous' fun (x : α) => f x >>= g x := sorry

theorem map_continuous' {α : Type u} [omega_complete_partial_order α] {β : Type v} {γ : Type v} (f : β → γ) (g : α → roption β) (hg : continuous' g) : continuous' fun (x : α) => f <$> g x := sorry

theorem seq_continuous' {α : Type u} [omega_complete_partial_order α] {β : Type v} {γ : Type v} (f : α → roption (β → γ)) (g : α → roption β) (hf : continuous' f) (hg : continuous' g) : continuous' fun (x : α) => f x <*> g x := sorry

theorem continuous {α : Type u} {β : Type v} [omega_complete_partial_order α] [omega_complete_partial_order β] (F : α →𝒄 β) (C : chain α) : coe_fn F (ωSup C) = ωSup (chain.map C ↑F) :=
  cont F C

/-- Construct a continuous function from a bare function, a continuous function, and a proof that
they are equal. -/
def of_fun {α : Type u} {β : Type v} [omega_complete_partial_order α] [omega_complete_partial_order β] (f : α → β) (g : α →𝒄 β) (h : f = ⇑g) : α →𝒄 β :=
  mk f sorry sorry

/-- Construct a continuous function from a monotone function with a proof of continuity. -/
def of_mono {α : Type u} {β : Type v} [omega_complete_partial_order α] [omega_complete_partial_order β] (f : α →ₘ β) (h : ∀ (c : chain α), coe_fn f (ωSup c) = ωSup (chain.map c f)) : α →𝒄 β :=
  mk ⇑f sorry h

/-- The identity as a continuous function. -/
@[simp] theorem id_to_fun {α : Type u} [omega_complete_partial_order α] : ∀ (ᾰ : α), coe_fn id ᾰ = ᾰ :=
  fun (ᾰ : α) => Eq.refl ᾰ

/-- The composition of continuous functions. -/
def comp {α : Type u} {β : Type v} {γ : Type u_3} [omega_complete_partial_order α] [omega_complete_partial_order β] [omega_complete_partial_order γ] (f : β →𝒄 γ) (g : α →𝒄 β) : α →𝒄 γ :=
  of_mono (preorder_hom.comp ↑f ↑g) sorry

protected theorem ext {α : Type u} {β : Type v} [omega_complete_partial_order α] [omega_complete_partial_order β] (f : α →𝒄 β) (g : α →𝒄 β) (h : ∀ (x : α), coe_fn f x = coe_fn g x) : f = g := sorry

protected theorem coe_inj {α : Type u} {β : Type v} [omega_complete_partial_order α] [omega_complete_partial_order β] (f : α →𝒄 β) (g : α →𝒄 β) (h : ⇑f = ⇑g) : f = g :=
  continuous_hom.ext f g (congr_fun h)

@[simp] theorem comp_id {β : Type v} {γ : Type u_3} [omega_complete_partial_order β] [omega_complete_partial_order γ] (f : β →𝒄 γ) : comp f id = f :=
  continuous_hom.ext (comp f id) f fun (x : β) => Eq.refl (coe_fn (comp f id) x)

@[simp] theorem id_comp {β : Type v} {γ : Type u_3} [omega_complete_partial_order β] [omega_complete_partial_order γ] (f : β →𝒄 γ) : comp id f = f :=
  continuous_hom.ext (comp id f) f fun (x : β) => Eq.refl (coe_fn (comp id f) x)

@[simp] theorem comp_assoc {α : Type u} {β : Type v} {γ : Type u_3} {φ : Type u_4} [omega_complete_partial_order α] [omega_complete_partial_order β] [omega_complete_partial_order γ] [omega_complete_partial_order φ] (f : γ →𝒄 φ) (g : β →𝒄 γ) (h : α →𝒄 β) : comp f (comp g h) = comp (comp f g) h :=
  continuous_hom.ext (comp f (comp g h)) (comp (comp f g) h) fun (x : α) => Eq.refl (coe_fn (comp f (comp g h)) x)

@[simp] theorem coe_apply {α : Type u} {β : Type v} [omega_complete_partial_order α] [omega_complete_partial_order β] (a : α) (f : α →𝒄 β) : coe_fn (↑f) a = coe_fn f a :=
  rfl

/-- `function.const` is a continuous function. -/
def const {α : Type u} {β : Type v} [omega_complete_partial_order α] [omega_complete_partial_order β] (f : β) : α →𝒄 β :=
  of_mono (preorder_hom.const α f) sorry

@[simp] theorem const_apply {α : Type u} {β : Type v} [omega_complete_partial_order α] [omega_complete_partial_order β] (f : β) (a : α) : coe_fn (const f) a = f :=
  rfl

protected instance inhabited {α : Type u} {β : Type v} [omega_complete_partial_order α] [omega_complete_partial_order β] [Inhabited β] : Inhabited (α →𝒄 β) :=
  { default := const Inhabited.default }

namespace prod


/-- The application of continuous functions as a monotone function.

(It would make sense to make it a continuous function, but we are currently constructing a
`omega_complete_partial_order` instance for `α →𝒄 β`, and we cannot use it as the domain or image
of a continuous function before we do.) -/
def apply {α : Type u} {β : Type v} [omega_complete_partial_order α] [omega_complete_partial_order β] : (α →𝒄 β) × α →ₘ β :=
  preorder_hom.mk (fun (f : (α →𝒄 β) × α) => coe_fn (prod.fst f) (prod.snd f)) sorry

end prod


/-- The map from continuous functions to monotone functions is itself a monotone function. -/
@[simp] theorem to_mono_to_fun {α : Type u} {β : Type v} [omega_complete_partial_order α] [omega_complete_partial_order β] (f : α →𝒄 β) : coe_fn to_mono f = ↑f :=
  Eq.refl (coe_fn to_mono f)

/-- When proving that a chain of applications is below a bound `z`, it suffices to consider the
functions and values being selected from the same index in the chains.

This lemma is more specific than necessary, i.e. `c₀` only needs to be a
chain of monotone functions, but it is only used with continuous functions. -/
@[simp] theorem forall_forall_merge {α : Type u} {β : Type v} [omega_complete_partial_order α] [omega_complete_partial_order β] (c₀ : chain (α →𝒄 β)) (c₁ : chain α) (z : β) : (∀ (i j : ℕ), coe_fn (coe_fn c₀ i) (coe_fn c₁ j) ≤ z) ↔ ∀ (i : ℕ), coe_fn (coe_fn c₀ i) (coe_fn c₁ i) ≤ z := sorry

@[simp] theorem forall_forall_merge' {α : Type u} {β : Type v} [omega_complete_partial_order α] [omega_complete_partial_order β] (c₀ : chain (α →𝒄 β)) (c₁ : chain α) (z : β) : (∀ (j i : ℕ), coe_fn (coe_fn c₀ i) (coe_fn c₁ j) ≤ z) ↔ ∀ (i : ℕ), coe_fn (coe_fn c₀ i) (coe_fn c₁ i) ≤ z := sorry

/-- The `ωSup` operator for continuous functions, which takes the pointwise countable supremum
of the functions in the `ω`-chain. -/
protected def ωSup {α : Type u} {β : Type v} [omega_complete_partial_order α] [omega_complete_partial_order β] (c : chain (α →𝒄 β)) : α →𝒄 β :=
  of_mono (ωSup (chain.map c to_mono)) sorry

protected instance omega_complete_partial_order {α : Type u} {β : Type v} [omega_complete_partial_order α] [omega_complete_partial_order β] : omega_complete_partial_order (α →𝒄 β) :=
  omega_complete_partial_order.lift to_mono continuous_hom.ωSup sorry sorry

theorem ωSup_def {α : Type u} {β : Type v} [omega_complete_partial_order α] [omega_complete_partial_order β] (c : chain (α →𝒄 β)) (x : α) : coe_fn (ωSup c) x = coe_fn (continuous_hom.ωSup c) x :=
  rfl

theorem ωSup_ωSup {α : Type u} {β : Type v} [omega_complete_partial_order α] [omega_complete_partial_order β] (c₀ : chain (α →𝒄 β)) (c₁ : chain α) : coe_fn (ωSup c₀) (ωSup c₁) = ωSup (preorder_hom.comp prod.apply (chain.zip c₀ c₁)) := sorry

/-- A family of continuous functions yields a continuous family of functions. -/
def flip {β : Type v} {γ : Type u_3} [omega_complete_partial_order β] [omega_complete_partial_order γ] {α : Type u_1} (f : α → β →𝒄 γ) : β →𝒄 α → γ :=
  mk (fun (x : β) (y : α) => coe_fn (f y) x) sorry sorry

/-- `roption.bind` as a continuous function. -/
def bind {α : Type u} [omega_complete_partial_order α] {β : Type v} {γ : Type v} (f : α →𝒄 roption β) (g : α →𝒄 β → roption γ) : α →𝒄 roption γ :=
  of_mono (preorder_hom.bind ↑f ↑g) sorry

/-- `roption.map` as a continuous function. -/
@[simp] theorem map_to_fun {α : Type u} [omega_complete_partial_order α] {β : Type v} {γ : Type v} (f : β → γ) (g : α →𝒄 roption β) (x : α) : coe_fn (map f g) x = f <$> coe_fn g x :=
  Eq.refl (coe_fn (map f g) x)

/-- `roption.seq` as a continuous function. -/
def seq {α : Type u} [omega_complete_partial_order α] {β : Type v} {γ : Type v} (f : α →𝒄 roption (β → γ)) (g : α →𝒄 roption β) : α →𝒄 roption γ :=
  of_fun (fun (x : α) => coe_fn f x <*> coe_fn g x) (bind f (flip (flip map g))) sorry

