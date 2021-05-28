/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Johannes Hölzl
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.order.filter.partial
import Mathlib.order.filter.at_top_bot
import Mathlib.PostPort

universes u_1 u_2 u_3 

namespace Mathlib

/-!
# liminfs and limsups of functions and filters

Defines the Liminf/Limsup of a function taking values in a conditionally complete lattice, with
respect to an arbitrary filter.

We define `f.Limsup` (`f.Liminf`) where `f` is a filter taking values in a conditionally complete
lattice. `f.Limsup` is the smallest element `a` such that, eventually, `u ≤ a` (and vice versa for
`f.Liminf`). To work with the Limsup along a function `u` use `(f.map u).Limsup`.

Usually, one defines the Limsup as `Inf (Sup s)` where the Inf is taken over all sets in the filter.
For instance, in ℕ along a function `u`, this is `Inf_n (Sup_{k ≥ n} u k)` (and the latter quantity
decreases with `n`, so this is in fact a limit.). There is however a difficulty: it is well possible
that `u` is not bounded on the whole space, only eventually (think of `Limsup (λx, 1/x)` on ℝ. Then
there is no guarantee that the quantity above really decreases (the value of the `Sup` beforehand is
not really well defined, as one can not use ∞), so that the Inf could be anything. So one can not
use this `Inf Sup ...` definition in conditionally complete lattices, and one has to use a less
tractable definition.

In conditionally complete lattices, the definition is only useful for filters which are eventually
bounded above (otherwise, the Limsup would morally be +∞, which does not belong to the space) and
which are frequently bounded below (otherwise, the Limsup would morally be -∞, which is not in the
space either). We start with definitions of these concepts for arbitrary filters, before turning to
the definitions of Limsup and Liminf.

In complete lattices, however, it coincides with the `Inf Sup` definition.
-/

namespace filter


/-- `f.is_bounded (≺)`: the filter `f` is eventually bounded w.r.t. the relation `≺`, i.e.
eventually, it is bounded by some uniform bound.
`r` will be usually instantiated with `≤` or `≥`. -/
def is_bounded {α : Type u_1} (r : α → α → Prop) (f : filter α)  :=
  ∃ (b : α), filter.eventually (fun (x : α) => r x b) f

/-- `f.is_bounded_under (≺) u`: the image of the filter `f` under `u` is eventually bounded w.r.t.
the relation `≺`, i.e. eventually, it is bounded by some uniform bound. -/
def is_bounded_under {α : Type u_1} {β : Type u_2} (r : α → α → Prop) (f : filter β) (u : β → α)  :=
  is_bounded r (map u f)

/-- `f` is eventually bounded if and only if, there exists an admissible set on which it is
bounded. -/
theorem is_bounded_iff {α : Type u_1} {r : α → α → Prop} {f : filter α} : is_bounded r f ↔ ∃ (s : set α), ∃ (H : s ∈ sets f), ∃ (b : α), s ⊆ set_of fun (x : α) => r x b := sorry

/-- A bounded function `u` is in particular eventually bounded. -/
theorem is_bounded_under_of {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {f : filter β} {u : β → α} : (∃ (b : α), ∀ (x : β), r (u x) b) → is_bounded_under r f u := sorry

theorem is_bounded_bot {α : Type u_1} {r : α → α → Prop} : is_bounded r ⊥ ↔ Nonempty α := sorry

theorem is_bounded_top {α : Type u_1} {r : α → α → Prop} : is_bounded r ⊤ ↔ ∃ (t : α), ∀ (x : α), r x t := sorry

theorem is_bounded_principal {α : Type u_1} {r : α → α → Prop} (s : set α) : is_bounded r (principal s) ↔ ∃ (t : α), ∀ (x : α), x ∈ s → r x t := sorry

theorem is_bounded_sup {α : Type u_1} {r : α → α → Prop} {f : filter α} {g : filter α} [is_trans α r] (hr : ∀ (b₁ b₂ : α), ∃ (b : α), r b₁ b ∧ r b₂ b) : is_bounded r f → is_bounded r g → is_bounded r (f ⊔ g) := sorry

theorem is_bounded.mono {α : Type u_1} {r : α → α → Prop} {f : filter α} {g : filter α} (h : f ≤ g) : is_bounded r g → is_bounded r f := sorry

theorem is_bounded_under.mono {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {f : filter β} {g : filter β} {u : β → α} (h : f ≤ g) : is_bounded_under r g u → is_bounded_under r f u :=
  fun (hg : is_bounded_under r g u) => is_bounded.mono (map_mono h) hg

theorem is_bounded.is_bounded_under {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {f : filter α} {q : β → β → Prop} {u : α → β} (hf : ∀ (a₀ a₁ : α), r a₀ a₁ → q (u a₀) (u a₁)) : is_bounded r f → is_bounded_under q f u := sorry

/-- `is_cobounded (≺) f` states that the filter `f` does not tend to infinity w.r.t. `≺`. This is
also called frequently bounded. Will be usually instantiated with `≤` or `≥`.

There is a subtlety in this definition: we want `f.is_cobounded` to hold for any `f` in the case of
complete lattices. This will be relevant to deduce theorems on complete lattices from their
versions on conditionally complete lattices with additional assumptions. We have to be careful in
the edge case of the trivial filter containing the empty set: the other natural definition
  `¬ ∀ a, ∀ᶠ n in f, a ≤ n`
would not work as well in this case.
-/
def is_cobounded {α : Type u_1} (r : α → α → Prop) (f : filter α)  :=
  ∃ (b : α), ∀ (a : α), filter.eventually (fun (x : α) => r x a) f → r b a

/-- `is_cobounded_under (≺) f u` states that the image of the filter `f` under the map `u` does not
tend to infinity w.r.t. `≺`. This is also called frequently bounded. Will be usually instantiated
with `≤` or `≥`. -/
def is_cobounded_under {α : Type u_1} {β : Type u_2} (r : α → α → Prop) (f : filter β) (u : β → α)  :=
  is_cobounded r (map u f)

/-- To check that a filter is frequently bounded, it suffices to have a witness
which bounds `f` at some point for every admissible set.

This is only an implication, as the other direction is wrong for the trivial filter.-/
theorem is_cobounded.mk {α : Type u_1} {r : α → α → Prop} {f : filter α} [is_trans α r] (a : α) (h : ∀ (s : set α) (H : s ∈ f), ∃ (x : α), ∃ (H : x ∈ s), r a x) : is_cobounded r f := sorry

/-- A filter which is eventually bounded is in particular frequently bounded (in the opposite
direction). At least if the filter is not trivial. -/
theorem is_bounded.is_cobounded_flip {α : Type u_1} {r : α → α → Prop} {f : filter α} [is_trans α r] [ne_bot f] : is_bounded r f → is_cobounded (flip r) f := sorry

theorem is_cobounded_bot {α : Type u_1} {r : α → α → Prop} : is_cobounded r ⊥ ↔ ∃ (b : α), ∀ (x : α), r b x := sorry

theorem is_cobounded_top {α : Type u_1} {r : α → α → Prop} : is_cobounded r ⊤ ↔ Nonempty α := sorry

theorem is_cobounded_principal {α : Type u_1} {r : α → α → Prop} (s : set α) : is_cobounded r (principal s) ↔ ∃ (b : α), ∀ (a : α), (∀ (x : α), x ∈ s → r x a) → r b a := sorry

theorem is_cobounded.mono {α : Type u_1} {r : α → α → Prop} {f : filter α} {g : filter α} (h : f ≤ g) : is_cobounded r f → is_cobounded r g := sorry

theorem is_cobounded_le_of_bot {α : Type u_1} [order_bot α] {f : filter α} : is_cobounded LessEq f :=
  Exists.intro ⊥ fun (a : α) (h : filter.eventually (fun (x : α) => x ≤ a) f) => bot_le

theorem is_cobounded_ge_of_top {α : Type u_1} [order_top α] {f : filter α} : is_cobounded ge f :=
  Exists.intro ⊤ fun (a : α) (h : filter.eventually (fun (x : α) => x ≥ a) f) => le_top

theorem is_bounded_le_of_top {α : Type u_1} [order_top α] {f : filter α} : is_bounded LessEq f :=
  Exists.intro ⊤ (eventually_of_forall fun (_x : α) => le_top)

theorem is_bounded_ge_of_bot {α : Type u_1} [order_bot α] {f : filter α} : is_bounded ge f :=
  Exists.intro ⊥ (eventually_of_forall fun (_x : α) => bot_le)

theorem is_bounded_under_sup {α : Type u_1} {β : Type u_2} [semilattice_sup α] {f : filter β} {u : β → α} {v : β → α} : is_bounded_under LessEq f u → is_bounded_under LessEq f v → is_bounded_under LessEq f fun (a : β) => u a ⊔ v a := sorry

theorem is_bounded_under_inf {α : Type u_1} {β : Type u_2} [semilattice_inf α] {f : filter β} {u : β → α} {v : β → α} : is_bounded_under ge f u → is_bounded_under ge f v → is_bounded_under ge f fun (a : β) => u a ⊓ v a := sorry

/-- Filters are automatically bounded or cobounded in complete lattices. To use the same statements
in complete and conditionally complete lattices but let automation fill automatically the
boundedness proofs in complete lattices, we use the tactic `is_bounded_default` in the statements,
in the form `(hf : f.is_bounded (≥) . is_bounded_default)`. -/
/-- The `Limsup` of a filter `f` is the infimum of the `a` such that, eventually for `f`,
holds `x ≤ a`. -/
def Limsup {α : Type u_1} [conditionally_complete_lattice α] (f : filter α) : α :=
  Inf (set_of fun (a : α) => filter.eventually (fun (n : α) => n ≤ a) f)

/-- The `Liminf` of a filter `f` is the supremum of the `a` such that, eventually for `f`,
holds `x ≥ a`. -/
def Liminf {α : Type u_1} [conditionally_complete_lattice α] (f : filter α) : α :=
  Sup (set_of fun (a : α) => filter.eventually (fun (n : α) => a ≤ n) f)

/-- The `limsup` of a function `u` along a filter `f` is the infimum of the `a` such that,
eventually for `f`, holds `u x ≤ a`. -/
def limsup {α : Type u_1} {β : Type u_2} [conditionally_complete_lattice α] (f : filter β) (u : β → α) : α :=
  Limsup (map u f)

/-- The `liminf` of a function `u` along a filter `f` is the supremum of the `a` such that,
eventually for `f`, holds `u x ≥ a`. -/
def liminf {α : Type u_1} {β : Type u_2} [conditionally_complete_lattice α] (f : filter β) (u : β → α) : α :=
  Liminf (map u f)

theorem limsup_eq {α : Type u_1} {β : Type u_2} [conditionally_complete_lattice α] {f : filter β} {u : β → α} : limsup f u = Inf (set_of fun (a : α) => filter.eventually (fun (n : β) => u n ≤ a) f) :=
  rfl

theorem liminf_eq {α : Type u_1} {β : Type u_2} [conditionally_complete_lattice α] {f : filter β} {u : β → α} : liminf f u = Sup (set_of fun (a : α) => filter.eventually (fun (n : β) => a ≤ u n) f) :=
  rfl

theorem Limsup_le_of_le {α : Type u_1} [conditionally_complete_lattice α] {f : filter α} {a : α} (hf : autoParam (is_cobounded LessEq f)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.filter.is_bounded_default")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "filter") "is_bounded_default")
    [])) (h : filter.eventually (fun (n : α) => n ≤ a) f) : Limsup f ≤ a :=
  cInf_le hf h

theorem le_Liminf_of_le {α : Type u_1} [conditionally_complete_lattice α] {f : filter α} {a : α} (hf : autoParam (is_cobounded ge f)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.filter.is_bounded_default")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "filter") "is_bounded_default")
    [])) (h : filter.eventually (fun (n : α) => a ≤ n) f) : a ≤ Liminf f :=
  le_cSup hf h

theorem le_Limsup_of_le {α : Type u_1} [conditionally_complete_lattice α] {f : filter α} {a : α} (hf : autoParam (is_bounded LessEq f)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.filter.is_bounded_default")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "filter") "is_bounded_default")
    [])) (h : ∀ (b : α), filter.eventually (fun (n : α) => n ≤ b) f → a ≤ b) : a ≤ Limsup f :=
  le_cInf hf h

theorem Liminf_le_of_le {α : Type u_1} [conditionally_complete_lattice α] {f : filter α} {a : α} (hf : autoParam (is_bounded ge f)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.filter.is_bounded_default")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "filter") "is_bounded_default")
    [])) (h : ∀ (b : α), filter.eventually (fun (n : α) => b ≤ n) f → b ≤ a) : Liminf f ≤ a :=
  cSup_le hf h

theorem Liminf_le_Limsup {α : Type u_1} [conditionally_complete_lattice α] {f : filter α} [ne_bot f] (h₁ : autoParam (is_bounded LessEq f)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.filter.is_bounded_default")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "filter") "is_bounded_default")
    [])) (h₂ : autoParam (is_bounded ge f)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.filter.is_bounded_default")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "filter") "is_bounded_default")
    [])) : Liminf f ≤ Limsup f := sorry

theorem Liminf_le_Liminf {α : Type u_1} [conditionally_complete_lattice α] {f : filter α} {g : filter α} (hf : autoParam (is_bounded ge f)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.filter.is_bounded_default")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "filter") "is_bounded_default")
    [])) (hg : autoParam (is_cobounded ge g)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.filter.is_bounded_default")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "filter") "is_bounded_default")
    [])) (h : ∀ (a : α), filter.eventually (fun (n : α) => a ≤ n) f → filter.eventually (fun (n : α) => a ≤ n) g) : Liminf f ≤ Liminf g :=
  cSup_le_cSup hg hf h

theorem Limsup_le_Limsup {α : Type u_1} [conditionally_complete_lattice α] {f : filter α} {g : filter α} (hf : autoParam (is_cobounded LessEq f)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.filter.is_bounded_default")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "filter") "is_bounded_default")
    [])) (hg : autoParam (is_bounded LessEq g)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.filter.is_bounded_default")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "filter") "is_bounded_default")
    [])) (h : ∀ (a : α), filter.eventually (fun (n : α) => n ≤ a) g → filter.eventually (fun (n : α) => n ≤ a) f) : Limsup f ≤ Limsup g :=
  cInf_le_cInf hf hg h

theorem Limsup_le_Limsup_of_le {α : Type u_1} [conditionally_complete_lattice α] {f : filter α} {g : filter α} (h : f ≤ g) (hf : autoParam (is_cobounded LessEq f)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.filter.is_bounded_default")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "filter") "is_bounded_default")
    [])) (hg : autoParam (is_bounded LessEq g)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.filter.is_bounded_default")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "filter") "is_bounded_default")
    [])) : Limsup f ≤ Limsup g :=
  Limsup_le_Limsup fun (a : α) (ha : filter.eventually (fun (n : α) => n ≤ a) g) => h ha

theorem Liminf_le_Liminf_of_le {α : Type u_1} [conditionally_complete_lattice α] {f : filter α} {g : filter α} (h : g ≤ f) (hf : autoParam (is_bounded ge f)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.filter.is_bounded_default")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "filter") "is_bounded_default")
    [])) (hg : autoParam (is_cobounded ge g)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.filter.is_bounded_default")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "filter") "is_bounded_default")
    [])) : Liminf f ≤ Liminf g :=
  Liminf_le_Liminf fun (a : α) (ha : filter.eventually (fun (n : α) => a ≤ n) f) => h ha

theorem limsup_le_limsup {β : Type u_2} {α : Type u_1} [conditionally_complete_lattice β] {f : filter α} {u : α → β} {v : α → β} (h : eventually_le f u v) (hu : autoParam (is_cobounded_under LessEq f u)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.filter.is_bounded_default")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "filter") "is_bounded_default")
    [])) (hv : autoParam (is_bounded_under LessEq f v)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.filter.is_bounded_default")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "filter") "is_bounded_default")
    [])) : limsup f u ≤ limsup f v :=
  Limsup_le_Limsup fun (b : β) => eventually_le.trans h

theorem liminf_le_liminf {β : Type u_2} {α : Type u_1} [conditionally_complete_lattice β] {f : filter α} {u : α → β} {v : α → β} (h : filter.eventually (fun (a : α) => u a ≤ v a) f) (hu : autoParam (is_bounded_under ge f u)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.filter.is_bounded_default")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "filter") "is_bounded_default")
    [])) (hv : autoParam (is_cobounded_under ge f v)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.filter.is_bounded_default")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "filter") "is_bounded_default")
    [])) : liminf f u ≤ liminf f v :=
  limsup_le_limsup h

theorem Limsup_principal {α : Type u_1} [conditionally_complete_lattice α] {s : set α} (h : bdd_above s) (hs : set.nonempty s) : Limsup (principal s) = Sup s := sorry

theorem Liminf_principal {α : Type u_1} [conditionally_complete_lattice α] {s : set α} (h : bdd_below s) (hs : set.nonempty s) : Liminf (principal s) = Inf s :=
  Limsup_principal h hs

theorem limsup_congr {β : Type u_2} {α : Type u_1} [conditionally_complete_lattice β] {f : filter α} {u : α → β} {v : α → β} (h : filter.eventually (fun (a : α) => u a = v a) f) : limsup f u = limsup f v := sorry

theorem liminf_congr {β : Type u_2} {α : Type u_1} [conditionally_complete_lattice β] {f : filter α} {u : α → β} {v : α → β} (h : filter.eventually (fun (a : α) => u a = v a) f) : liminf f u = liminf f v :=
  limsup_congr h

theorem limsup_const {β : Type u_2} {α : Type u_1} [conditionally_complete_lattice β] {f : filter α} [ne_bot f] (b : β) : (limsup f fun (x : α) => b) = b := sorry

theorem liminf_const {β : Type u_2} {α : Type u_1} [conditionally_complete_lattice β] {f : filter α} [ne_bot f] (b : β) : (liminf f fun (x : α) => b) = b :=
  limsup_const b

@[simp] theorem Limsup_bot {α : Type u_1} [complete_lattice α] : Limsup ⊥ = ⊥ := sorry

@[simp] theorem Liminf_bot {α : Type u_1} [complete_lattice α] : Liminf ⊥ = ⊤ := sorry

@[simp] theorem Limsup_top {α : Type u_1} [complete_lattice α] : Limsup ⊤ = ⊤ := sorry

@[simp] theorem Liminf_top {α : Type u_1} [complete_lattice α] : Liminf ⊤ = ⊥ := sorry

/-- Same as limsup_const applied to `⊥` but without the `ne_bot f` assumption -/
theorem limsup_const_bot {α : Type u_1} {β : Type u_2} [complete_lattice α] {f : filter β} : (limsup f fun (x : β) => ⊥) = ⊥ := sorry

/-- Same as limsup_const applied to `⊤` but without the `ne_bot f` assumption -/
theorem liminf_const_top {α : Type u_1} {β : Type u_2} [complete_lattice α] {f : filter β} : (liminf f fun (x : β) => ⊤) = ⊤ :=
  limsup_const_bot

theorem liminf_le_limsup {α : Type u_1} {β : Type u_2} [complete_lattice α] {f : filter β} [ne_bot f] {u : β → α} : liminf f u ≤ limsup f u :=
  Liminf_le_Limsup

theorem has_basis.Limsup_eq_infi_Sup {α : Type u_1} [complete_lattice α] {ι : Type u_2} {p : ι → Prop} {s : ι → set α} {f : filter α} (h : has_basis f p s) : Limsup f = infi fun (i : ι) => infi fun (hi : p i) => Sup (s i) := sorry

theorem has_basis.Liminf_eq_supr_Inf {α : Type u_1} {ι : Type u_3} [complete_lattice α] {p : ι → Prop} {s : ι → set α} {f : filter α} (h : has_basis f p s) : Liminf f = supr fun (i : ι) => supr fun (hi : p i) => Inf (s i) :=
  has_basis.Limsup_eq_infi_Sup h

theorem Limsup_eq_infi_Sup {α : Type u_1} [complete_lattice α] {f : filter α} : Limsup f = infi fun (s : set α) => infi fun (H : s ∈ f) => Sup s :=
  has_basis.Limsup_eq_infi_Sup (basis_sets f)

theorem Liminf_eq_supr_Inf {α : Type u_1} [complete_lattice α] {f : filter α} : Liminf f = supr fun (s : set α) => supr fun (H : s ∈ f) => Inf s :=
  Limsup_eq_infi_Sup

/-- In a complete lattice, the limsup of a function is the infimum over sets `s` in the filter
of the supremum of the function over `s` -/
theorem limsup_eq_infi_supr {α : Type u_1} {β : Type u_2} [complete_lattice α] {f : filter β} {u : β → α} : limsup f u = infi fun (s : set β) => infi fun (H : s ∈ f) => supr fun (a : β) => supr fun (H : a ∈ s) => u a := sorry

theorem limsup_eq_infi_supr_of_nat {α : Type u_1} [complete_lattice α] {u : ℕ → α} : limsup at_top u = infi fun (n : ℕ) => supr fun (i : ℕ) => supr fun (H : i ≥ n) => u i := sorry

theorem limsup_eq_infi_supr_of_nat' {α : Type u_1} [complete_lattice α] {u : ℕ → α} : limsup at_top u = infi fun (n : ℕ) => supr fun (i : ℕ) => u (i + n) := sorry

theorem has_basis.limsup_eq_infi_supr {α : Type u_1} {β : Type u_2} {ι : Type u_3} [complete_lattice α] {p : ι → Prop} {s : ι → set β} {f : filter β} {u : β → α} (h : has_basis f p s) : limsup f u = infi fun (i : ι) => infi fun (hi : p i) => supr fun (a : β) => supr fun (H : a ∈ s i) => u a := sorry

/-- In a complete lattice, the liminf of a function is the infimum over sets `s` in the filter
of the supremum of the function over `s` -/
theorem liminf_eq_supr_infi {α : Type u_1} {β : Type u_2} [complete_lattice α] {f : filter β} {u : β → α} : liminf f u = supr fun (s : set β) => supr fun (H : s ∈ f) => infi fun (a : β) => infi fun (H : a ∈ s) => u a :=
  limsup_eq_infi_supr

theorem liminf_eq_supr_infi_of_nat {α : Type u_1} [complete_lattice α] {u : ℕ → α} : liminf at_top u = supr fun (n : ℕ) => infi fun (i : ℕ) => infi fun (H : i ≥ n) => u i :=
  limsup_eq_infi_supr_of_nat

theorem liminf_eq_supr_infi_of_nat' {α : Type u_1} [complete_lattice α] {u : ℕ → α} : liminf at_top u = supr fun (n : ℕ) => infi fun (i : ℕ) => u (i + n) :=
  limsup_eq_infi_supr_of_nat'

theorem has_basis.liminf_eq_supr_infi {α : Type u_1} {β : Type u_2} {ι : Type u_3} [complete_lattice α] {p : ι → Prop} {s : ι → set β} {f : filter β} {u : β → α} (h : has_basis f p s) : liminf f u = supr fun (i : ι) => supr fun (hi : p i) => infi fun (a : β) => infi fun (H : a ∈ s i) => u a :=
  has_basis.limsup_eq_infi_supr h

theorem eventually_lt_of_lt_liminf {α : Type u_1} {β : Type u_2} {f : filter α} [conditionally_complete_linear_order β] {u : α → β} {b : β} (h : b < liminf f u) (hu : autoParam (is_bounded_under ge f u)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.filter.is_bounded_default")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "filter") "is_bounded_default")
    [])) : filter.eventually (fun (a : α) => b < u a) f := sorry

theorem eventually_lt_of_limsup_lt {α : Type u_1} {β : Type u_2} {f : filter α} [conditionally_complete_linear_order β] {u : α → β} {b : β} (h : limsup f u < b) (hu : autoParam (is_bounded_under LessEq f u)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.filter.is_bounded_default")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "filter") "is_bounded_default")
    [])) : filter.eventually (fun (a : α) => u a < b) f :=
  eventually_lt_of_lt_liminf h

theorem le_limsup_of_frequently_le {α : Type u_1} {β : Type u_2} [conditionally_complete_linear_order β] {f : filter α} {u : α → β} {b : β} (hu_le : filter.frequently (fun (x : α) => b ≤ u x) f) (hu : autoParam (is_bounded_under LessEq f u)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.filter.is_bounded_default")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "filter") "is_bounded_default")
    [])) : b ≤ limsup f u := sorry

theorem liminf_le_of_frequently_le {α : Type u_1} {β : Type u_2} [conditionally_complete_linear_order β] {f : filter α} {u : α → β} {b : β} (hu_le : filter.frequently (fun (x : α) => u x ≤ b) f) (hu : autoParam (is_bounded_under ge f u)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.filter.is_bounded_default")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "filter") "is_bounded_default")
    [])) : liminf f u ≤ b :=
  le_limsup_of_frequently_le hu_le

end filter


theorem galois_connection.l_limsup_le {α : Type u_1} {β : Type u_2} {γ : Type u_3} [conditionally_complete_lattice β] [conditionally_complete_lattice γ] {f : filter α} {v : α → β} {l : β → γ} {u : γ → β} (gc : galois_connection l u) (hlv : autoParam (filter.is_bounded_under LessEq f fun (x : α) => l (v x))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.filter.is_bounded_default")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "filter") "is_bounded_default")
    [])) (hv_co : autoParam (filter.is_cobounded_under LessEq f v)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.filter.is_bounded_default")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "filter") "is_bounded_default")
    [])) : l (filter.limsup f v) ≤ filter.limsup f fun (x : α) => l (v x) := sorry

theorem order_iso.limsup_apply {α : Type u_1} {β : Type u_2} {γ : Type u_3} [conditionally_complete_lattice β] [conditionally_complete_lattice γ] {f : filter α} {u : α → β} (g : β ≃o γ) (hu : autoParam (filter.is_bounded_under LessEq f u)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.filter.is_bounded_default")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "filter") "is_bounded_default")
    [])) (hu_co : autoParam (filter.is_cobounded_under LessEq f u)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.filter.is_bounded_default")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "filter") "is_bounded_default")
    [])) (hgu : autoParam (filter.is_bounded_under LessEq f fun (x : α) => coe_fn g (u x))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.filter.is_bounded_default")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "filter") "is_bounded_default")
    [])) (hgu_co : autoParam (filter.is_cobounded_under LessEq f fun (x : α) => coe_fn g (u x))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.filter.is_bounded_default")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "filter") "is_bounded_default")
    [])) : coe_fn g (filter.limsup f u) = filter.limsup f fun (x : α) => coe_fn g (u x) := sorry

theorem order_iso.liminf_apply {α : Type u_1} {β : Type u_2} {γ : Type u_3} [conditionally_complete_lattice β] [conditionally_complete_lattice γ] {f : filter α} {u : α → β} (g : β ≃o γ) (hu : autoParam (filter.is_bounded_under ge f u)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.filter.is_bounded_default")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "filter") "is_bounded_default")
    [])) (hu_co : autoParam (filter.is_cobounded_under ge f u)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.filter.is_bounded_default")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "filter") "is_bounded_default")
    [])) (hgu : autoParam (filter.is_bounded_under ge f fun (x : α) => coe_fn g (u x))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.filter.is_bounded_default")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "filter") "is_bounded_default")
    [])) (hgu_co : autoParam (filter.is_cobounded_under ge f fun (x : α) => coe_fn g (u x))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.filter.is_bounded_default")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "filter") "is_bounded_default")
    [])) : coe_fn g (filter.liminf f u) = filter.liminf f fun (x : α) => coe_fn g (u x) :=
  order_iso.limsup_apply (order_iso.dual g)

