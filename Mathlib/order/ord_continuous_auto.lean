/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Johannes Hölzl
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.order.conditionally_complete_lattice
import Mathlib.logic.function.iterate
import Mathlib.order.rel_iso
import PostPort

universes u v w x 

namespace Mathlib

/-!
# Order continuity

We say that a function is *left order continuous* if it sends all least upper bounds
to least upper bounds. The order dual notion is called *right order continuity*.

For monotone functions `ℝ → ℝ` these notions correspond to the usual left and right continuity.

We prove some basic lemmas (`map_sup`, `map_Sup` etc) and prove that an `rel_iso` is both left
and right order continuous.
-/

/-!
### Definitions
-/

/-- A function `f` between preorders is left order continuous if it preserves all suprema.  We
define it using `is_lub` instead of `Sup` so that the proof works both for complete lattices and
conditionally complete lattices. -/
def left_ord_continuous {α : Type u} {β : Type v} [preorder α] [preorder β] (f : α → β)  :=
  ∀ {s : set α} {x : α}, is_lub s x → is_lub (f '' s) (f x)

/-- A function `f` between preorders is right order continuous if it preserves all infima.  We
define it using `is_glb` instead of `Inf` so that the proof works both for complete lattices and
conditionally complete lattices. -/
def right_ord_continuous {α : Type u} {β : Type v} [preorder α] [preorder β] (f : α → β)  :=
  ∀ {s : set α} {x : α}, is_glb s x → is_glb (f '' s) (f x)

namespace left_ord_continuous


protected theorem id (α : Type u) [preorder α] : left_ord_continuous id := sorry

protected theorem order_dual {α : Type u} {β : Type v} [preorder α] [preorder β] {f : α → β} (hf : left_ord_continuous f) : right_ord_continuous f :=
  hf

theorem map_is_greatest {α : Type u} {β : Type v} [preorder α] [preorder β] {f : α → β} (hf : left_ord_continuous f) {s : set α} {x : α} (h : is_greatest s x) : is_greatest (f '' s) (f x) :=
  { left := set.mem_image_of_mem f (and.left h), right := and.left (hf (is_greatest.is_lub h)) }

theorem mono {α : Type u} {β : Type v} [preorder α] [preorder β] {f : α → β} (hf : left_ord_continuous f) : monotone f := sorry

theorem comp {α : Type u} {β : Type v} {γ : Type w} [preorder α] [preorder β] [preorder γ] {g : β → γ} {f : α → β} (hg : left_ord_continuous g) (hf : left_ord_continuous f) : left_ord_continuous (g ∘ f) := sorry

protected theorem iterate {α : Type u} [preorder α] {f : α → α} (hf : left_ord_continuous f) (n : ℕ) : left_ord_continuous (nat.iterate f n) :=
  nat.rec_on n (left_ord_continuous.id α) fun (n : ℕ) (ihn : left_ord_continuous (nat.iterate f n)) => comp ihn hf

theorem map_sup {α : Type u} {β : Type v} [semilattice_sup α] [semilattice_sup β] {f : α → β} (hf : left_ord_continuous f) (x : α) (y : α) : f (x ⊔ y) = f x ⊔ f y := sorry

theorem le_iff {α : Type u} {β : Type v} [semilattice_sup α] [semilattice_sup β] {f : α → β} (hf : left_ord_continuous f) (h : function.injective f) {x : α} {y : α} : f x ≤ f y ↔ x ≤ y := sorry

theorem lt_iff {α : Type u} {β : Type v} [semilattice_sup α] [semilattice_sup β] {f : α → β} (hf : left_ord_continuous f) (h : function.injective f) {x : α} {y : α} : f x < f y ↔ x < y := sorry

/-- Convert an injective left order continuous function to an order embedding. -/
def to_order_embedding {α : Type u} {β : Type v} [semilattice_sup α] [semilattice_sup β] (f : α → β) (hf : left_ord_continuous f) (h : function.injective f) : α ↪o β :=
  rel_embedding.mk (function.embedding.mk f h) sorry

@[simp] theorem coe_to_order_embedding {α : Type u} {β : Type v} [semilattice_sup α] [semilattice_sup β] {f : α → β} (hf : left_ord_continuous f) (h : function.injective f) : ⇑(to_order_embedding f hf h) = f :=
  rfl

theorem map_Sup' {α : Type u} {β : Type v} [complete_lattice α] [complete_lattice β] {f : α → β} (hf : left_ord_continuous f) (s : set α) : f (Sup s) = Sup (f '' s) :=
  Eq.symm (is_lub.Sup_eq (hf (is_lub_Sup s)))

theorem map_Sup {α : Type u} {β : Type v} [complete_lattice α] [complete_lattice β] {f : α → β} (hf : left_ord_continuous f) (s : set α) : f (Sup s) = supr fun (x : α) => supr fun (H : x ∈ s) => f x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (f (Sup s) = supr fun (x : α) => supr fun (H : x ∈ s) => f x)) (map_Sup' hf s)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (Sup (f '' s) = supr fun (x : α) => supr fun (H : x ∈ s) => f x)) Sup_image))
      (Eq.refl (supr fun (a : α) => supr fun (H : a ∈ s) => f a)))

theorem map_supr {α : Type u} {β : Type v} {ι : Sort x} [complete_lattice α] [complete_lattice β] {f : α → β} (hf : left_ord_continuous f) (g : ι → α) : f (supr fun (i : ι) => g i) = supr fun (i : ι) => f (g i) := sorry

theorem map_cSup {α : Type u} {β : Type v} [conditionally_complete_lattice α] [conditionally_complete_lattice β] {f : α → β} (hf : left_ord_continuous f) {s : set α} (sne : set.nonempty s) (sbdd : bdd_above s) : f (Sup s) = Sup (f '' s) :=
  Eq.symm (is_lub.cSup_eq (hf (is_lub_cSup sne sbdd)) (set.nonempty.image f sne))

theorem map_csupr {α : Type u} {β : Type v} {ι : Sort x} [conditionally_complete_lattice α] [conditionally_complete_lattice β] [Nonempty ι] {f : α → β} (hf : left_ord_continuous f) {g : ι → α} (hg : bdd_above (set.range g)) : f (supr fun (i : ι) => g i) = supr fun (i : ι) => f (g i) := sorry

end left_ord_continuous


namespace right_ord_continuous


protected theorem id (α : Type u) [preorder α] : right_ord_continuous id := sorry

protected theorem order_dual {α : Type u} {β : Type v} [preorder α] [preorder β] {f : α → β} (hf : right_ord_continuous f) : left_ord_continuous f :=
  hf

theorem map_is_least {α : Type u} {β : Type v} [preorder α] [preorder β] {f : α → β} (hf : right_ord_continuous f) {s : set α} {x : α} (h : is_least s x) : is_least (f '' s) (f x) :=
  left_ord_continuous.map_is_greatest (right_ord_continuous.order_dual hf) h

theorem mono {α : Type u} {β : Type v} [preorder α] [preorder β] {f : α → β} (hf : right_ord_continuous f) : monotone f :=
  monotone.order_dual (left_ord_continuous.mono (right_ord_continuous.order_dual hf))

theorem comp {α : Type u} {β : Type v} {γ : Type w} [preorder α] [preorder β] [preorder γ] {g : β → γ} {f : α → β} (hg : right_ord_continuous g) (hf : right_ord_continuous f) : right_ord_continuous (g ∘ f) :=
  left_ord_continuous.comp (right_ord_continuous.order_dual hg) (right_ord_continuous.order_dual hf)

protected theorem iterate {α : Type u} [preorder α] {f : α → α} (hf : right_ord_continuous f) (n : ℕ) : right_ord_continuous (nat.iterate f n) :=
  left_ord_continuous.iterate (right_ord_continuous.order_dual hf) n

theorem map_inf {α : Type u} {β : Type v} [semilattice_inf α] [semilattice_inf β] {f : α → β} (hf : right_ord_continuous f) (x : α) (y : α) : f (x ⊓ y) = f x ⊓ f y :=
  left_ord_continuous.map_sup (right_ord_continuous.order_dual hf) x y

theorem le_iff {α : Type u} {β : Type v} [semilattice_inf α] [semilattice_inf β] {f : α → β} (hf : right_ord_continuous f) (h : function.injective f) {x : α} {y : α} : f x ≤ f y ↔ x ≤ y :=
  left_ord_continuous.le_iff (right_ord_continuous.order_dual hf) h

theorem lt_iff {α : Type u} {β : Type v} [semilattice_inf α] [semilattice_inf β] {f : α → β} (hf : right_ord_continuous f) (h : function.injective f) {x : α} {y : α} : f x < f y ↔ x < y :=
  left_ord_continuous.lt_iff (right_ord_continuous.order_dual hf) h

/-- Convert an injective left order continuous function to a `order_embedding`. -/
def to_order_embedding {α : Type u} {β : Type v} [semilattice_inf α] [semilattice_inf β] (f : α → β) (hf : right_ord_continuous f) (h : function.injective f) : α ↪o β :=
  rel_embedding.mk (function.embedding.mk f h) sorry

@[simp] theorem coe_to_order_embedding {α : Type u} {β : Type v} [semilattice_inf α] [semilattice_inf β] {f : α → β} (hf : right_ord_continuous f) (h : function.injective f) : ⇑(to_order_embedding f hf h) = f :=
  rfl

theorem map_Inf' {α : Type u} {β : Type v} [complete_lattice α] [complete_lattice β] {f : α → β} (hf : right_ord_continuous f) (s : set α) : f (Inf s) = Inf (f '' s) :=
  left_ord_continuous.map_Sup' (right_ord_continuous.order_dual hf) s

theorem map_Inf {α : Type u} {β : Type v} [complete_lattice α] [complete_lattice β] {f : α → β} (hf : right_ord_continuous f) (s : set α) : f (Inf s) = infi fun (x : α) => infi fun (H : x ∈ s) => f x :=
  left_ord_continuous.map_Sup (right_ord_continuous.order_dual hf) s

theorem map_infi {α : Type u} {β : Type v} {ι : Sort x} [complete_lattice α] [complete_lattice β] {f : α → β} (hf : right_ord_continuous f) (g : ι → α) : f (infi fun (i : ι) => g i) = infi fun (i : ι) => f (g i) :=
  left_ord_continuous.map_supr (right_ord_continuous.order_dual hf) g

theorem map_cInf {α : Type u} {β : Type v} [conditionally_complete_lattice α] [conditionally_complete_lattice β] {f : α → β} (hf : right_ord_continuous f) {s : set α} (sne : set.nonempty s) (sbdd : bdd_below s) : f (Inf s) = Inf (f '' s) :=
  left_ord_continuous.map_cSup (right_ord_continuous.order_dual hf) sne sbdd

theorem map_cinfi {α : Type u} {β : Type v} {ι : Sort x} [conditionally_complete_lattice α] [conditionally_complete_lattice β] [Nonempty ι] {f : α → β} (hf : right_ord_continuous f) {g : ι → α} (hg : bdd_below (set.range g)) : f (infi fun (i : ι) => g i) = infi fun (i : ι) => f (g i) :=
  left_ord_continuous.map_csupr (right_ord_continuous.order_dual hf) hg

end right_ord_continuous


namespace order_iso


protected theorem left_ord_continuous {α : Type u} {β : Type v} [preorder α] [preorder β] (e : α ≃o β) : left_ord_continuous ⇑e := sorry

protected theorem right_ord_continuous {α : Type u} {β : Type v} [preorder α] [preorder β] (e : α ≃o β) : right_ord_continuous ⇑e :=
  order_iso.left_ord_continuous (order_iso.dual e)

