/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.order.filter.basic
import PostPort

universes u v w x u_1 u_2 

namespace Mathlib

/-!
# Minimum and maximum w.r.t. a filter and on a aet

## Main Definitions

This file defines six predicates of the form `is_A_B`, where `A` is `min`, `max`, or `extr`,
and `B` is `filter` or `on`.

* `is_min_filter f l a` means that `f a ≤ f x` in some `l`-neighborhood of `a`;
* `is_max_filter f l a` means that `f x ≤ f a` in some `l`-neighborhood of `a`;
* `is_extr_filter f l a` means `is_min_filter f l a` or `is_max_filter f l a`.

Similar predicates with `_on` suffix are particular cases for `l = 𝓟 s`.

## Main statements

### Change of the filter (set) argument

* `is_*_filter.filter_mono` : replace the filter with a smaller one;
* `is_*_filter.filter_inf` : replace a filter `l` with `l ⊓ l'`;
* `is_*_on.on_subset` : restrict to a smaller set;
* `is_*_on.inter` : replace a set `s` wtih `s ∩ t`.

### Composition

* `is_*_*.comp_mono` : if `x` is an extremum for `f` and `g` is a monotone function,
  then `x` is an extremum for `g ∘ f`;
* `is_*_*.comp_antimono` : similarly for the case of monotonically decreasing `g`;
* `is_*_*.bicomp_mono` : if `x` is an extremum of the same type for `f` and `g`
  and a binary operation `op` is monotone in both arguments, then `x` is an extremum
  of the same type for `λ x, op (f x) (g x)`.
* `is_*_filter.comp_tendsto` : if `g x` is an extremum for `f` w.r.t. `l'` and `tendsto g l l'`,
  then `x` is an extremum for `f ∘ g` w.r.t. `l`.
* `is_*_on.on_preimage` : if `g x` is an extremum for `f` on `s`, then `x` is an extremum
  for `f ∘ g` on `g ⁻¹' s`.

### Algebraic operations

* `is_*_*.add` : if `x` is an extremum of the same type for two functions,
  then it is an extremum of the same type for their sum;
* `is_*_*.neg` : if `x` is an extremum for `f`, then it is an extremum
  of the opposite type for `-f`;
* `is_*_*.sub` : if `x` is an a minimum for `f` and a maximum for `g`,
  then it is a minimum for `f - g` and a maximum for `g - f`;
* `is_*_*.max`, `is_*_*.min`, `is_*_*.sup`, `is_*_*.inf` : similarly for `is_*_*.add`
  for pointwise `max`, `min`, `sup`, `inf`, respectively.


### Miscellaneous definitions

* `is_*_*_const` : any point is both a minimum and maximum for a constant function;
* `is_min/max_*.is_ext` : any minimum/maximum point is an extremum;
* `is_*_*.dual`, `is_*_*.undual`: conversion between codomains `α` and `dual α`;

## Missing features (TODO)

* Multiplication and division;
* `is_*_*.bicompl` : if `x` is a minimum for `f`, `y` is a minimum for `g`, and `op` is a monotone
  binary operation, then `(x, y)` is a minimum for `uncurry (bicompl op f g)`. From this point of view,
  `is_*_*.bicomp` is a composition
* It would be nice to have a tactic that specializes `comp_(anti)mono` or `bicomp_mono`
  based on a proof of monotonicity of a given (binary) function. The tactic should maintain a `meta`
  list of known (anti)monotone (binary) functions with their names, as well as a list of special
  types of filters, and define the missing lemmas once one of these two lists grows.
-/

/-! ### Definitions -/

/-- `is_min_filter f l a` means that `f a ≤ f x` in some `l`-neighborhood of `a` -/
def is_min_filter {α : Type u} {β : Type v} [preorder β] (f : α → β) (l : filter α) (a : α)  :=
  filter.eventually (fun (x : α) => f a ≤ f x) l

/-- `is_max_filter f l a` means that `f x ≤ f a` in some `l`-neighborhood of `a` -/
def is_max_filter {α : Type u} {β : Type v} [preorder β] (f : α → β) (l : filter α) (a : α)  :=
  filter.eventually (fun (x : α) => f x ≤ f a) l

/-- `is_extr_filter f l a` means `is_min_filter f l a` or `is_max_filter f l a` -/
def is_extr_filter {α : Type u} {β : Type v} [preorder β] (f : α → β) (l : filter α) (a : α)  :=
  is_min_filter f l a ∨ is_max_filter f l a

/-- `is_min_on f s a` means that `f a ≤ f x` for all `x ∈ a`. Note that we do not assume `a ∈ s`. -/
def is_min_on {α : Type u} {β : Type v} [preorder β] (f : α → β) (s : set α) (a : α)  :=
  is_min_filter f (filter.principal s) a

/-- `is_max_on f s a` means that `f x ≤ f a` for all `x ∈ a`. Note that we do not assume `a ∈ s`. -/
def is_max_on {α : Type u} {β : Type v} [preorder β] (f : α → β) (s : set α) (a : α)  :=
  is_max_filter f (filter.principal s) a

/-- `is_extr_on f s a` means `is_min_on f s a` or `is_max_on f s a` -/
def is_extr_on {α : Type u} {β : Type v} [preorder β] (f : α → β) (s : set α) (a : α)  :=
  is_extr_filter f (filter.principal s) a

theorem is_extr_on.elim {α : Type u} {β : Type v} [preorder β] {f : α → β} {s : set α} {a : α} {p : Prop} : is_extr_on f s a → (is_min_on f s a → p) → (is_max_on f s a → p) → p :=
  or.elim

theorem is_min_on_iff {α : Type u} {β : Type v} [preorder β] {f : α → β} {s : set α} {a : α} : is_min_on f s a ↔ ∀ (x : α), x ∈ s → f a ≤ f x :=
  iff.rfl

theorem is_max_on_iff {α : Type u} {β : Type v} [preorder β] {f : α → β} {s : set α} {a : α} : is_max_on f s a ↔ ∀ (x : α), x ∈ s → f x ≤ f a :=
  iff.rfl

theorem is_min_on_univ_iff {α : Type u} {β : Type v} [preorder β] {f : α → β} {a : α} : is_min_on f set.univ a ↔ ∀ (x : α), f a ≤ f x :=
  iff.trans set.univ_subset_iff set.eq_univ_iff_forall

theorem is_max_on_univ_iff {α : Type u} {β : Type v} [preorder β] {f : α → β} {a : α} : is_max_on f set.univ a ↔ ∀ (x : α), f x ≤ f a :=
  iff.trans set.univ_subset_iff set.eq_univ_iff_forall

/-! ### Conversion to `is_extr_*` -/

theorem is_min_filter.is_extr {α : Type u} {β : Type v} [preorder β] {f : α → β} {l : filter α} {a : α} : is_min_filter f l a → is_extr_filter f l a :=
  Or.inl

theorem is_max_filter.is_extr {α : Type u} {β : Type v} [preorder β] {f : α → β} {l : filter α} {a : α} : is_max_filter f l a → is_extr_filter f l a :=
  Or.inr

theorem is_min_on.is_extr {α : Type u} {β : Type v} [preorder β] {f : α → β} {s : set α} {a : α} (h : is_min_on f s a) : is_extr_on f s a :=
  is_min_filter.is_extr h

theorem is_max_on.is_extr {α : Type u} {β : Type v} [preorder β] {f : α → β} {s : set α} {a : α} (h : is_max_on f s a) : is_extr_on f s a :=
  is_max_filter.is_extr h

/-! ### Constant function -/

theorem is_min_filter_const {α : Type u} {β : Type v} [preorder β] {l : filter α} {a : α} {b : β} : is_min_filter (fun (_x : α) => b) l a :=
  filter.univ_mem_sets' fun (_x : α) => le_refl ((fun (_x : α) => b) a)

theorem is_max_filter_const {α : Type u} {β : Type v} [preorder β] {l : filter α} {a : α} {b : β} : is_max_filter (fun (_x : α) => b) l a :=
  filter.univ_mem_sets' fun (_x : α) => le_refl ((fun (_x : α) => b) _x)

theorem is_extr_filter_const {α : Type u} {β : Type v} [preorder β] {l : filter α} {a : α} {b : β} : is_extr_filter (fun (_x : α) => b) l a :=
  is_min_filter.is_extr is_min_filter_const

theorem is_min_on_const {α : Type u} {β : Type v} [preorder β] {s : set α} {a : α} {b : β} : is_min_on (fun (_x : α) => b) s a :=
  is_min_filter_const

theorem is_max_on_const {α : Type u} {β : Type v} [preorder β] {s : set α} {a : α} {b : β} : is_max_on (fun (_x : α) => b) s a :=
  is_max_filter_const

theorem is_extr_on_const {α : Type u} {β : Type v} [preorder β] {s : set α} {a : α} {b : β} : is_extr_on (fun (_x : α) => b) s a :=
  is_extr_filter_const

/-! ### Order dual -/

theorem is_min_filter_dual_iff {α : Type u} {β : Type v} [preorder β] {f : α → β} {l : filter α} {a : α} : is_min_filter f l a ↔ is_max_filter f l a :=
  iff.rfl

theorem is_max_filter_dual_iff {α : Type u} {β : Type v} [preorder β] {f : α → β} {l : filter α} {a : α} : is_max_filter f l a ↔ is_min_filter f l a :=
  iff.rfl

theorem is_extr_filter_dual_iff {α : Type u} {β : Type v} [preorder β] {f : α → β} {l : filter α} {a : α} : is_extr_filter f l a ↔ is_extr_filter f l a :=
  or_comm (is_min_filter f l a) (is_max_filter f l a)

theorem is_max_filter.dual {α : Type u} {β : Type v} [preorder β] {f : α → β} {l : filter α} {a : α} : is_max_filter f l a → is_min_filter f l a :=
  iff.mpr is_min_filter_dual_iff

theorem is_max_filter.undual {α : Type u} {β : Type v} [preorder β] {f : α → β} {l : filter α} {a : α} : is_max_filter f l a → is_min_filter f l a :=
  iff.mp is_max_filter_dual_iff

theorem is_extr_filter.dual {α : Type u} {β : Type v} [preorder β] {f : α → β} {l : filter α} {a : α} : is_extr_filter f l a → is_extr_filter f l a :=
  iff.mpr is_extr_filter_dual_iff

theorem is_min_on_dual_iff {α : Type u} {β : Type v} [preorder β] {f : α → β} {s : set α} {a : α} : is_min_on f s a ↔ is_max_on f s a :=
  iff.rfl

theorem is_max_on_dual_iff {α : Type u} {β : Type v} [preorder β] {f : α → β} {s : set α} {a : α} : is_max_on f s a ↔ is_min_on f s a :=
  iff.rfl

theorem is_extr_on_dual_iff {α : Type u} {β : Type v} [preorder β] {f : α → β} {s : set α} {a : α} : is_extr_on f s a ↔ is_extr_on f s a :=
  or_comm (is_min_filter f (filter.principal s) a) (is_max_filter f (filter.principal s) a)

theorem is_max_on.dual {α : Type u} {β : Type v} [preorder β] {f : α → β} {s : set α} {a : α} : is_max_on f s a → is_min_on f s a :=
  iff.mpr is_min_on_dual_iff

theorem is_min_on.dual {α : Type u} {β : Type v} [preorder β] {f : α → β} {s : set α} {a : α} : is_min_on f s a → is_max_on f s a :=
  iff.mpr is_max_on_dual_iff

theorem is_extr_on.dual {α : Type u} {β : Type v} [preorder β] {f : α → β} {s : set α} {a : α} : is_extr_on f s a → is_extr_on f s a :=
  iff.mpr is_extr_on_dual_iff

/-! ### Operations on the filter/set -/

theorem is_min_filter.filter_mono {α : Type u} {β : Type v} [preorder β] {f : α → β} {l : filter α} {a : α} {l' : filter α} (h : is_min_filter f l a) (hl : l' ≤ l) : is_min_filter f l' a :=
  hl h

theorem is_max_filter.filter_mono {α : Type u} {β : Type v} [preorder β] {f : α → β} {l : filter α} {a : α} {l' : filter α} (h : is_max_filter f l a) (hl : l' ≤ l) : is_max_filter f l' a :=
  hl h

theorem is_extr_filter.filter_mono {α : Type u} {β : Type v} [preorder β] {f : α → β} {l : filter α} {a : α} {l' : filter α} (h : is_extr_filter f l a) (hl : l' ≤ l) : is_extr_filter f l' a :=
  or.elim h (fun (h : is_min_filter f l a) => is_min_filter.is_extr (is_min_filter.filter_mono h hl))
    fun (h : is_max_filter f l a) => is_max_filter.is_extr (is_max_filter.filter_mono h hl)

theorem is_min_filter.filter_inf {α : Type u} {β : Type v} [preorder β] {f : α → β} {l : filter α} {a : α} (h : is_min_filter f l a) (l' : filter α) : is_min_filter f (l ⊓ l') a :=
  is_min_filter.filter_mono h inf_le_left

theorem is_max_filter.filter_inf {α : Type u} {β : Type v} [preorder β] {f : α → β} {l : filter α} {a : α} (h : is_max_filter f l a) (l' : filter α) : is_max_filter f (l ⊓ l') a :=
  is_max_filter.filter_mono h inf_le_left

theorem is_extr_filter.filter_inf {α : Type u} {β : Type v} [preorder β] {f : α → β} {l : filter α} {a : α} (h : is_extr_filter f l a) (l' : filter α) : is_extr_filter f (l ⊓ l') a :=
  is_extr_filter.filter_mono h inf_le_left

theorem is_min_on.on_subset {α : Type u} {β : Type v} [preorder β] {f : α → β} {s : set α} {a : α} {t : set α} (hf : is_min_on f t a) (h : s ⊆ t) : is_min_on f s a :=
  is_min_filter.filter_mono hf (iff.mpr filter.principal_mono h)

theorem is_max_on.on_subset {α : Type u} {β : Type v} [preorder β] {f : α → β} {s : set α} {a : α} {t : set α} (hf : is_max_on f t a) (h : s ⊆ t) : is_max_on f s a :=
  is_max_filter.filter_mono hf (iff.mpr filter.principal_mono h)

theorem is_extr_on.on_subset {α : Type u} {β : Type v} [preorder β] {f : α → β} {s : set α} {a : α} {t : set α} (hf : is_extr_on f t a) (h : s ⊆ t) : is_extr_on f s a :=
  is_extr_filter.filter_mono hf (iff.mpr filter.principal_mono h)

theorem is_min_on.inter {α : Type u} {β : Type v} [preorder β] {f : α → β} {s : set α} {a : α} (hf : is_min_on f s a) (t : set α) : is_min_on f (s ∩ t) a :=
  is_min_on.on_subset hf (set.inter_subset_left s t)

theorem is_max_on.inter {α : Type u} {β : Type v} [preorder β] {f : α → β} {s : set α} {a : α} (hf : is_max_on f s a) (t : set α) : is_max_on f (s ∩ t) a :=
  is_max_on.on_subset hf (set.inter_subset_left s t)

theorem is_extr_on.inter {α : Type u} {β : Type v} [preorder β] {f : α → β} {s : set α} {a : α} (hf : is_extr_on f s a) (t : set α) : is_extr_on f (s ∩ t) a :=
  is_extr_on.on_subset hf (set.inter_subset_left s t)

/-! ### Composition with (anti)monotone functions -/

theorem is_min_filter.comp_mono {α : Type u} {β : Type v} {γ : Type w} [preorder β] [preorder γ] {f : α → β} {l : filter α} {a : α} (hf : is_min_filter f l a) {g : β → γ} (hg : monotone g) : is_min_filter (g ∘ f) l a :=
  filter.mem_sets_of_superset hf fun (x : α) (hx : x ∈ set_of fun (x : α) => (fun (x : α) => f a ≤ f x) x) => hg hx

theorem is_max_filter.comp_mono {α : Type u} {β : Type v} {γ : Type w} [preorder β] [preorder γ] {f : α → β} {l : filter α} {a : α} (hf : is_max_filter f l a) {g : β → γ} (hg : monotone g) : is_max_filter (g ∘ f) l a :=
  filter.mem_sets_of_superset hf fun (x : α) (hx : x ∈ set_of fun (x : α) => (fun (x : α) => f x ≤ f a) x) => hg hx

theorem is_extr_filter.comp_mono {α : Type u} {β : Type v} {γ : Type w} [preorder β] [preorder γ] {f : α → β} {l : filter α} {a : α} (hf : is_extr_filter f l a) {g : β → γ} (hg : monotone g) : is_extr_filter (g ∘ f) l a :=
  or.elim hf (fun (hf : is_min_filter f l a) => is_min_filter.is_extr (is_min_filter.comp_mono hf hg))
    fun (hf : is_max_filter f l a) => is_max_filter.is_extr (is_max_filter.comp_mono hf hg)

theorem is_min_filter.comp_antimono {α : Type u} {β : Type v} {γ : Type w} [preorder β] [preorder γ] {f : α → β} {l : filter α} {a : α} (hf : is_min_filter f l a) {g : β → γ} (hg : ∀ {x y : β}, x ≤ y → g y ≤ g x) : is_max_filter (g ∘ f) l a :=
  is_max_filter.comp_mono (is_min_filter.dual hf) fun (x y : order_dual β) (h : x ≤ y) => hg h

theorem is_max_filter.comp_antimono {α : Type u} {β : Type v} {γ : Type w} [preorder β] [preorder γ] {f : α → β} {l : filter α} {a : α} (hf : is_max_filter f l a) {g : β → γ} (hg : ∀ {x y : β}, x ≤ y → g y ≤ g x) : is_min_filter (g ∘ f) l a :=
  is_min_filter.comp_mono (is_max_filter.dual hf) fun (x y : order_dual β) (h : x ≤ y) => hg h

theorem is_extr_filter.comp_antimono {α : Type u} {β : Type v} {γ : Type w} [preorder β] [preorder γ] {f : α → β} {l : filter α} {a : α} (hf : is_extr_filter f l a) {g : β → γ} (hg : ∀ {x y : β}, x ≤ y → g y ≤ g x) : is_extr_filter (g ∘ f) l a :=
  is_extr_filter.comp_mono (is_extr_filter.dual hf) fun (x y : order_dual β) (h : x ≤ y) => hg h

theorem is_min_on.comp_mono {α : Type u} {β : Type v} {γ : Type w} [preorder β] [preorder γ] {f : α → β} {s : set α} {a : α} (hf : is_min_on f s a) {g : β → γ} (hg : monotone g) : is_min_on (g ∘ f) s a :=
  is_min_filter.comp_mono hf hg

theorem is_max_on.comp_mono {α : Type u} {β : Type v} {γ : Type w} [preorder β] [preorder γ] {f : α → β} {s : set α} {a : α} (hf : is_max_on f s a) {g : β → γ} (hg : monotone g) : is_max_on (g ∘ f) s a :=
  is_max_filter.comp_mono hf hg

theorem is_extr_on.comp_mono {α : Type u} {β : Type v} {γ : Type w} [preorder β] [preorder γ] {f : α → β} {s : set α} {a : α} (hf : is_extr_on f s a) {g : β → γ} (hg : monotone g) : is_extr_on (g ∘ f) s a :=
  is_extr_filter.comp_mono hf hg

theorem is_min_on.comp_antimono {α : Type u} {β : Type v} {γ : Type w} [preorder β] [preorder γ] {f : α → β} {s : set α} {a : α} (hf : is_min_on f s a) {g : β → γ} (hg : ∀ {x y : β}, x ≤ y → g y ≤ g x) : is_max_on (g ∘ f) s a :=
  is_min_filter.comp_antimono hf hg

theorem is_max_on.comp_antimono {α : Type u} {β : Type v} {γ : Type w} [preorder β] [preorder γ] {f : α → β} {s : set α} {a : α} (hf : is_max_on f s a) {g : β → γ} (hg : ∀ {x y : β}, x ≤ y → g y ≤ g x) : is_min_on (g ∘ f) s a :=
  is_max_filter.comp_antimono hf hg

theorem is_extr_on.comp_antimono {α : Type u} {β : Type v} {γ : Type w} [preorder β] [preorder γ] {f : α → β} {s : set α} {a : α} (hf : is_extr_on f s a) {g : β → γ} (hg : ∀ {x y : β}, x ≤ y → g y ≤ g x) : is_extr_on (g ∘ f) s a :=
  is_extr_filter.comp_antimono hf hg

theorem is_min_filter.bicomp_mono {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} [preorder β] [preorder γ] {f : α → β} {l : filter α} {a : α} [preorder δ] {op : β → γ → δ} (hop : relator.lift_fun LessEq (LessEq ⇒ LessEq) op op) (hf : is_min_filter f l a) {g : α → γ} (hg : is_min_filter g l a) : is_min_filter (fun (x : α) => op (f x) (g x)) l a := sorry

theorem is_max_filter.bicomp_mono {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} [preorder β] [preorder γ] {f : α → β} {l : filter α} {a : α} [preorder δ] {op : β → γ → δ} (hop : relator.lift_fun LessEq (LessEq ⇒ LessEq) op op) (hf : is_max_filter f l a) {g : α → γ} (hg : is_max_filter g l a) : is_max_filter (fun (x : α) => op (f x) (g x)) l a := sorry

-- No `extr` version because we need `hf` and `hg` to be of the same kind

theorem is_min_on.bicomp_mono {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} [preorder β] [preorder γ] {f : α → β} {s : set α} {a : α} [preorder δ] {op : β → γ → δ} (hop : relator.lift_fun LessEq (LessEq ⇒ LessEq) op op) (hf : is_min_on f s a) {g : α → γ} (hg : is_min_on g s a) : is_min_on (fun (x : α) => op (f x) (g x)) s a :=
  is_min_filter.bicomp_mono hop hf hg

theorem is_max_on.bicomp_mono {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} [preorder β] [preorder γ] {f : α → β} {s : set α} {a : α} [preorder δ] {op : β → γ → δ} (hop : relator.lift_fun LessEq (LessEq ⇒ LessEq) op op) (hf : is_max_on f s a) {g : α → γ} (hg : is_max_on g s a) : is_max_on (fun (x : α) => op (f x) (g x)) s a :=
  is_max_filter.bicomp_mono hop hf hg

/-! ### Composition with `tendsto` -/

theorem is_min_filter.comp_tendsto {α : Type u} {β : Type v} {δ : Type x} [preorder β] {f : α → β} {l : filter α} {g : δ → α} {l' : filter δ} {b : δ} (hf : is_min_filter f l (g b)) (hg : filter.tendsto g l' l) : is_min_filter (f ∘ g) l' b :=
  hg hf

theorem is_max_filter.comp_tendsto {α : Type u} {β : Type v} {δ : Type x} [preorder β] {f : α → β} {l : filter α} {g : δ → α} {l' : filter δ} {b : δ} (hf : is_max_filter f l (g b)) (hg : filter.tendsto g l' l) : is_max_filter (f ∘ g) l' b :=
  hg hf

theorem is_extr_filter.comp_tendsto {α : Type u} {β : Type v} {δ : Type x} [preorder β] {f : α → β} {l : filter α} {g : δ → α} {l' : filter δ} {b : δ} (hf : is_extr_filter f l (g b)) (hg : filter.tendsto g l' l) : is_extr_filter (f ∘ g) l' b :=
  or.elim hf (fun (hf : is_min_filter f l (g b)) => is_min_filter.is_extr (is_min_filter.comp_tendsto hf hg))
    fun (hf : is_max_filter f l (g b)) => is_max_filter.is_extr (is_max_filter.comp_tendsto hf hg)

theorem is_min_on.on_preimage {α : Type u} {β : Type v} {δ : Type x} [preorder β] {f : α → β} {s : set α} (g : δ → α) {b : δ} (hf : is_min_on f s (g b)) : is_min_on (f ∘ g) (g ⁻¹' s) b :=
  is_min_filter.comp_tendsto hf (iff.mpr filter.tendsto_principal_principal (set.subset.refl (g ⁻¹' s)))

theorem is_max_on.on_preimage {α : Type u} {β : Type v} {δ : Type x} [preorder β] {f : α → β} {s : set α} (g : δ → α) {b : δ} (hf : is_max_on f s (g b)) : is_max_on (f ∘ g) (g ⁻¹' s) b :=
  is_max_filter.comp_tendsto hf (iff.mpr filter.tendsto_principal_principal (set.subset.refl (g ⁻¹' s)))

theorem is_extr_on.on_preimage {α : Type u} {β : Type v} {δ : Type x} [preorder β] {f : α → β} {s : set α} (g : δ → α) {b : δ} (hf : is_extr_on f s (g b)) : is_extr_on (f ∘ g) (g ⁻¹' s) b :=
  is_extr_on.elim hf (fun (hf : is_min_on f s (g b)) => is_min_on.is_extr (is_min_on.on_preimage g hf))
    fun (hf : is_max_on f s (g b)) => is_max_on.is_extr (is_max_on.on_preimage g hf)

/-! ### Pointwise addition -/

theorem is_min_filter.add {α : Type u} {β : Type v} [ordered_add_comm_monoid β] {f : α → β} {g : α → β} {a : α} {l : filter α} (hf : is_min_filter f l a) (hg : is_min_filter g l a) : is_min_filter (fun (x : α) => f x + g x) l a :=
  (fun (this : is_min_filter (fun (x : α) => f x + g x) l a) => this)
    (is_min_filter.bicomp_mono (fun (x x' : β) (hx : x ≤ x') (y y' : β) (hy : y ≤ y') => add_le_add hx hy) hf hg)

theorem is_max_filter.add {α : Type u} {β : Type v} [ordered_add_comm_monoid β] {f : α → β} {g : α → β} {a : α} {l : filter α} (hf : is_max_filter f l a) (hg : is_max_filter g l a) : is_max_filter (fun (x : α) => f x + g x) l a :=
  (fun (this : is_max_filter (fun (x : α) => f x + g x) l a) => this)
    (is_max_filter.bicomp_mono (fun (x x' : β) (hx : x ≤ x') (y y' : β) (hy : y ≤ y') => add_le_add hx hy) hf hg)

theorem is_min_on.add {α : Type u} {β : Type v} [ordered_add_comm_monoid β] {f : α → β} {g : α → β} {a : α} {s : set α} (hf : is_min_on f s a) (hg : is_min_on g s a) : is_min_on (fun (x : α) => f x + g x) s a :=
  is_min_filter.add hf hg

theorem is_max_on.add {α : Type u} {β : Type v} [ordered_add_comm_monoid β] {f : α → β} {g : α → β} {a : α} {s : set α} (hf : is_max_on f s a) (hg : is_max_on g s a) : is_max_on (fun (x : α) => f x + g x) s a :=
  is_max_filter.add hf hg

/-! ### Pointwise negation and subtraction -/

theorem is_min_filter.neg {α : Type u} {β : Type v} [ordered_add_comm_group β] {f : α → β} {a : α} {l : filter α} (hf : is_min_filter f l a) : is_max_filter (fun (x : α) => -f x) l a :=
  is_min_filter.comp_antimono hf fun (x y : β) (hx : x ≤ y) => neg_le_neg hx

theorem is_max_filter.neg {α : Type u} {β : Type v} [ordered_add_comm_group β] {f : α → β} {a : α} {l : filter α} (hf : is_max_filter f l a) : is_min_filter (fun (x : α) => -f x) l a :=
  is_max_filter.comp_antimono hf fun (x y : β) (hx : x ≤ y) => neg_le_neg hx

theorem is_extr_filter.neg {α : Type u} {β : Type v} [ordered_add_comm_group β] {f : α → β} {a : α} {l : filter α} (hf : is_extr_filter f l a) : is_extr_filter (fun (x : α) => -f x) l a :=
  or.elim hf (fun (hf : is_min_filter f l a) => is_max_filter.is_extr (is_min_filter.neg hf))
    fun (hf : is_max_filter f l a) => is_min_filter.is_extr (is_max_filter.neg hf)

theorem is_min_on.neg {α : Type u} {β : Type v} [ordered_add_comm_group β] {f : α → β} {a : α} {s : set α} (hf : is_min_on f s a) : is_max_on (fun (x : α) => -f x) s a :=
  is_min_on.comp_antimono hf fun (x y : β) (hx : x ≤ y) => neg_le_neg hx

theorem is_max_on.neg {α : Type u} {β : Type v} [ordered_add_comm_group β] {f : α → β} {a : α} {s : set α} (hf : is_max_on f s a) : is_min_on (fun (x : α) => -f x) s a :=
  is_max_on.comp_antimono hf fun (x y : β) (hx : x ≤ y) => neg_le_neg hx

theorem is_extr_on.neg {α : Type u} {β : Type v} [ordered_add_comm_group β] {f : α → β} {a : α} {s : set α} (hf : is_extr_on f s a) : is_extr_on (fun (x : α) => -f x) s a :=
  is_extr_on.elim hf (fun (hf : is_min_on f s a) => is_max_on.is_extr (is_min_on.neg hf))
    fun (hf : is_max_on f s a) => is_min_on.is_extr (is_max_on.neg hf)

theorem is_min_filter.sub {α : Type u} {β : Type v} [ordered_add_comm_group β] {f : α → β} {g : α → β} {a : α} {l : filter α} (hf : is_min_filter f l a) (hg : is_max_filter g l a) : is_min_filter (fun (x : α) => f x - g x) l a := sorry

theorem is_max_filter.sub {α : Type u} {β : Type v} [ordered_add_comm_group β] {f : α → β} {g : α → β} {a : α} {l : filter α} (hf : is_max_filter f l a) (hg : is_min_filter g l a) : is_max_filter (fun (x : α) => f x - g x) l a := sorry

theorem is_min_on.sub {α : Type u} {β : Type v} [ordered_add_comm_group β] {f : α → β} {g : α → β} {a : α} {s : set α} (hf : is_min_on f s a) (hg : is_max_on g s a) : is_min_on (fun (x : α) => f x - g x) s a := sorry

theorem is_max_on.sub {α : Type u} {β : Type v} [ordered_add_comm_group β] {f : α → β} {g : α → β} {a : α} {s : set α} (hf : is_max_on f s a) (hg : is_min_on g s a) : is_max_on (fun (x : α) => f x - g x) s a := sorry

/-! ### Pointwise `sup`/`inf` -/

theorem is_min_filter.sup {α : Type u} {β : Type v} [semilattice_sup β] {f : α → β} {g : α → β} {a : α} {l : filter α} (hf : is_min_filter f l a) (hg : is_min_filter g l a) : is_min_filter (fun (x : α) => f x ⊔ g x) l a :=
  (fun (this : is_min_filter (fun (x : α) => f x ⊔ g x) l a) => this)
    (is_min_filter.bicomp_mono (fun (x x' : β) (hx : x ≤ x') (y y' : β) (hy : y ≤ y') => sup_le_sup hx hy) hf hg)

theorem is_max_filter.sup {α : Type u} {β : Type v} [semilattice_sup β] {f : α → β} {g : α → β} {a : α} {l : filter α} (hf : is_max_filter f l a) (hg : is_max_filter g l a) : is_max_filter (fun (x : α) => f x ⊔ g x) l a :=
  (fun (this : is_max_filter (fun (x : α) => f x ⊔ g x) l a) => this)
    (is_max_filter.bicomp_mono (fun (x x' : β) (hx : x ≤ x') (y y' : β) (hy : y ≤ y') => sup_le_sup hx hy) hf hg)

theorem is_min_on.sup {α : Type u} {β : Type v} [semilattice_sup β] {f : α → β} {g : α → β} {a : α} {s : set α} (hf : is_min_on f s a) (hg : is_min_on g s a) : is_min_on (fun (x : α) => f x ⊔ g x) s a :=
  is_min_filter.sup hf hg

theorem is_max_on.sup {α : Type u} {β : Type v} [semilattice_sup β] {f : α → β} {g : α → β} {a : α} {s : set α} (hf : is_max_on f s a) (hg : is_max_on g s a) : is_max_on (fun (x : α) => f x ⊔ g x) s a :=
  is_max_filter.sup hf hg

theorem is_min_filter.inf {α : Type u} {β : Type v} [semilattice_inf β] {f : α → β} {g : α → β} {a : α} {l : filter α} (hf : is_min_filter f l a) (hg : is_min_filter g l a) : is_min_filter (fun (x : α) => f x ⊓ g x) l a :=
  (fun (this : is_min_filter (fun (x : α) => f x ⊓ g x) l a) => this)
    (is_min_filter.bicomp_mono (fun (x x' : β) (hx : x ≤ x') (y y' : β) (hy : y ≤ y') => inf_le_inf hx hy) hf hg)

theorem is_max_filter.inf {α : Type u} {β : Type v} [semilattice_inf β] {f : α → β} {g : α → β} {a : α} {l : filter α} (hf : is_max_filter f l a) (hg : is_max_filter g l a) : is_max_filter (fun (x : α) => f x ⊓ g x) l a :=
  (fun (this : is_max_filter (fun (x : α) => f x ⊓ g x) l a) => this)
    (is_max_filter.bicomp_mono (fun (x x' : β) (hx : x ≤ x') (y y' : β) (hy : y ≤ y') => inf_le_inf hx hy) hf hg)

theorem is_min_on.inf {α : Type u} {β : Type v} [semilattice_inf β] {f : α → β} {g : α → β} {a : α} {s : set α} (hf : is_min_on f s a) (hg : is_min_on g s a) : is_min_on (fun (x : α) => f x ⊓ g x) s a :=
  is_min_filter.inf hf hg

theorem is_max_on.inf {α : Type u} {β : Type v} [semilattice_inf β] {f : α → β} {g : α → β} {a : α} {s : set α} (hf : is_max_on f s a) (hg : is_max_on g s a) : is_max_on (fun (x : α) => f x ⊓ g x) s a :=
  is_max_filter.inf hf hg

/-! ### Pointwise `min`/`max` -/

theorem is_min_filter.min {α : Type u} {β : Type v} [linear_order β] {f : α → β} {g : α → β} {a : α} {l : filter α} (hf : is_min_filter f l a) (hg : is_min_filter g l a) : is_min_filter (fun (x : α) => min (f x) (g x)) l a :=
  (fun (this : is_min_filter (fun (x : α) => min (f x) (g x)) l a) => this)
    (is_min_filter.bicomp_mono (fun (x x' : β) (hx : x ≤ x') (y y' : β) (hy : y ≤ y') => min_le_min hx hy) hf hg)

theorem is_max_filter.min {α : Type u} {β : Type v} [linear_order β] {f : α → β} {g : α → β} {a : α} {l : filter α} (hf : is_max_filter f l a) (hg : is_max_filter g l a) : is_max_filter (fun (x : α) => min (f x) (g x)) l a :=
  (fun (this : is_max_filter (fun (x : α) => min (f x) (g x)) l a) => this)
    (is_max_filter.bicomp_mono (fun (x x' : β) (hx : x ≤ x') (y y' : β) (hy : y ≤ y') => min_le_min hx hy) hf hg)

theorem is_min_on.min {α : Type u} {β : Type v} [linear_order β] {f : α → β} {g : α → β} {a : α} {s : set α} (hf : is_min_on f s a) (hg : is_min_on g s a) : is_min_on (fun (x : α) => min (f x) (g x)) s a :=
  is_min_filter.min hf hg

theorem is_max_on.min {α : Type u} {β : Type v} [linear_order β] {f : α → β} {g : α → β} {a : α} {s : set α} (hf : is_max_on f s a) (hg : is_max_on g s a) : is_max_on (fun (x : α) => min (f x) (g x)) s a :=
  is_max_filter.min hf hg

theorem is_min_filter.max {α : Type u} {β : Type v} [linear_order β] {f : α → β} {g : α → β} {a : α} {l : filter α} (hf : is_min_filter f l a) (hg : is_min_filter g l a) : is_min_filter (fun (x : α) => max (f x) (g x)) l a :=
  (fun (this : is_min_filter (fun (x : α) => max (f x) (g x)) l a) => this)
    (is_min_filter.bicomp_mono (fun (x x' : β) (hx : x ≤ x') (y y' : β) (hy : y ≤ y') => max_le_max hx hy) hf hg)

theorem is_max_filter.max {α : Type u} {β : Type v} [linear_order β] {f : α → β} {g : α → β} {a : α} {l : filter α} (hf : is_max_filter f l a) (hg : is_max_filter g l a) : is_max_filter (fun (x : α) => max (f x) (g x)) l a :=
  (fun (this : is_max_filter (fun (x : α) => max (f x) (g x)) l a) => this)
    (is_max_filter.bicomp_mono (fun (x x' : β) (hx : x ≤ x') (y y' : β) (hy : y ≤ y') => max_le_max hx hy) hf hg)

theorem is_min_on.max {α : Type u} {β : Type v} [linear_order β] {f : α → β} {g : α → β} {a : α} {s : set α} (hf : is_min_on f s a) (hg : is_min_on g s a) : is_min_on (fun (x : α) => max (f x) (g x)) s a :=
  is_min_filter.max hf hg

theorem is_max_on.max {α : Type u} {β : Type v} [linear_order β] {f : α → β} {g : α → β} {a : α} {s : set α} (hf : is_max_on f s a) (hg : is_max_on g s a) : is_max_on (fun (x : α) => max (f x) (g x)) s a :=
  is_max_filter.max hf hg

/-! ### Relation with `eventually` comparisons of two functions -/

theorem filter.eventually_le.is_max_filter {α : Type u_1} {β : Type u_2} [preorder β] {f : α → β} {g : α → β} {a : α} {l : filter α} (hle : filter.eventually_le l g f) (hfga : f a = g a) (h : is_max_filter f l a) : is_max_filter g l a := sorry

theorem is_max_filter.congr {α : Type u_1} {β : Type u_2} [preorder β] {f : α → β} {g : α → β} {a : α} {l : filter α} (h : is_max_filter f l a) (heq : filter.eventually_eq l f g) (hfga : f a = g a) : is_max_filter g l a :=
  filter.eventually_le.is_max_filter (filter.eventually_eq.le (filter.eventually_eq.symm heq)) hfga h

theorem filter.eventually_eq.is_max_filter_iff {α : Type u_1} {β : Type u_2} [preorder β] {f : α → β} {g : α → β} {a : α} {l : filter α} (heq : filter.eventually_eq l f g) (hfga : f a = g a) : is_max_filter f l a ↔ is_max_filter g l a :=
  { mp := fun (h : is_max_filter f l a) => is_max_filter.congr h heq hfga,
    mpr := fun (h : is_max_filter g l a) => is_max_filter.congr h (filter.eventually_eq.symm heq) (Eq.symm hfga) }

theorem filter.eventually_le.is_min_filter {α : Type u_1} {β : Type u_2} [preorder β] {f : α → β} {g : α → β} {a : α} {l : filter α} (hle : filter.eventually_le l f g) (hfga : f a = g a) (h : is_min_filter f l a) : is_min_filter g l a :=
  filter.eventually_le.is_max_filter hle hfga h

theorem is_min_filter.congr {α : Type u_1} {β : Type u_2} [preorder β] {f : α → β} {g : α → β} {a : α} {l : filter α} (h : is_min_filter f l a) (heq : filter.eventually_eq l f g) (hfga : f a = g a) : is_min_filter g l a :=
  filter.eventually_le.is_min_filter (filter.eventually_eq.le heq) hfga h

theorem filter.eventually_eq.is_min_filter_iff {α : Type u_1} {β : Type u_2} [preorder β] {f : α → β} {g : α → β} {a : α} {l : filter α} (heq : filter.eventually_eq l f g) (hfga : f a = g a) : is_min_filter f l a ↔ is_min_filter g l a :=
  { mp := fun (h : is_min_filter f l a) => is_min_filter.congr h heq hfga,
    mpr := fun (h : is_min_filter g l a) => is_min_filter.congr h (filter.eventually_eq.symm heq) (Eq.symm hfga) }

theorem is_extr_filter.congr {α : Type u_1} {β : Type u_2} [preorder β] {f : α → β} {g : α → β} {a : α} {l : filter α} (h : is_extr_filter f l a) (heq : filter.eventually_eq l f g) (hfga : f a = g a) : is_extr_filter g l a := sorry

theorem filter.eventually_eq.is_extr_filter_iff {α : Type u_1} {β : Type u_2} [preorder β] {f : α → β} {g : α → β} {a : α} {l : filter α} (heq : filter.eventually_eq l f g) (hfga : f a = g a) : is_extr_filter f l a ↔ is_extr_filter g l a :=
  { mp := fun (h : is_extr_filter f l a) => is_extr_filter.congr h heq hfga,
    mpr := fun (h : is_extr_filter g l a) => is_extr_filter.congr h (filter.eventually_eq.symm heq) (Eq.symm hfga) }

