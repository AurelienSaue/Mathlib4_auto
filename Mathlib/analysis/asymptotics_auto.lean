/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.analysis.normed_space.basic
import Mathlib.topology.local_homeomorph
import Mathlib.PostPort

universes u_1 u_3 u_4 u_7 u_6 u_2 u_5 u_8 u_11 u_9 u_13 

namespace Mathlib

/-!
# Asymptotics

We introduce these relations:

* `is_O_with c f g l` : "f is big O of g along l with constant c";
* `is_O f g l` : "f is big O of g along l";
* `is_o f g l` : "f is little o of g along l".

Here `l` is any filter on the domain of `f` and `g`, which are assumed to be the same. The codomains
of `f` and `g` do not need to be the same; all that is needed that there is a norm associated with
these types, and it is the norm that is compared asymptotically.

The relation `is_O_with c` is introduced to factor out common algebraic arguments in the proofs of
similar properties of `is_O` and `is_o`. Usually proofs outside of this file should use `is_O`
instead.

Often the ranges of `f` and `g` will be the real numbers, in which case the norm is the absolute
value. In general, we have

  `is_O f g l ↔ is_O (λ x, ∥f x∥) (λ x, ∥g x∥) l`,

and similarly for `is_o`. But our setup allows us to use the notions e.g. with functions
to the integers, rationals, complex numbers, or any normed vector space without mentioning the
norm explicitly.

If `f` and `g` are functions to a normed field like the reals or complex numbers and `g` is always
nonzero, we have

  `is_o f g l ↔ tendsto (λ x, f x / (g x)) l (𝓝 0)`.

In fact, the right-to-left direction holds without the hypothesis on `g`, and in the other direction
it suffices to assume that `f` is zero wherever `g` is. (This generalization is useful in defining
the Fréchet derivative.)
-/

namespace asymptotics


/-! ### Definitions -/

/-- This version of the Landau notation `is_O_with C f g l` where `f` and `g` are two functions on
a type `α` and `l` is a filter on `α`, means that eventually for `l`, `∥f∥` is bounded by `C * ∥g∥`.
In other words, `∥f∥ / ∥g∥` is eventually bounded by `C`, modulo division by zero issues that are
avoided by this definition. Probably you want to use `is_O` instead of this relation. -/
def is_O_with {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E] [has_norm F] (c : ℝ)
    (f : α → E) (g : α → F) (l : filter α) :=
  filter.eventually (fun (x : α) => norm (f x) ≤ c * norm (g x)) l

/-- Definition of `is_O_with`. We record it in a lemma as we will set `is_O_with` to be irreducible
at the end of this file. -/
theorem is_O_with_iff {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E] [has_norm F] {c : ℝ}
    {f : α → E} {g : α → F} {l : filter α} :
    is_O_with c f g l ↔ filter.eventually (fun (x : α) => norm (f x) ≤ c * norm (g x)) l :=
  iff.rfl

theorem is_O_with.of_bound {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E] [has_norm F]
    {c : ℝ} {f : α → E} {g : α → F} {l : filter α}
    (h : filter.eventually (fun (x : α) => norm (f x) ≤ c * norm (g x)) l) : is_O_with c f g l :=
  h

/-- The Landau notation `is_O f g l` where `f` and `g` are two functions on a type `α` and `l` is
a filter on `α`, means that eventually for `l`, `∥f∥` is bounded by a constant multiple of `∥g∥`.
In other words, `∥f∥ / ∥g∥` is eventually bounded, modulo division by zero issues that are avoided
by this definition. -/
def is_O {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E] [has_norm F] (f : α → E)
    (g : α → F) (l : filter α) :=
  ∃ (c : ℝ), is_O_with c f g l

/-- Definition of `is_O` in terms of `is_O_with`. We record it in a lemma as we will set
`is_O` to be irreducible at the end of this file. -/
theorem is_O_iff_is_O_with {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E] [has_norm F]
    {f : α → E} {g : α → F} {l : filter α} : is_O f g l ↔ ∃ (c : ℝ), is_O_with c f g l :=
  iff.rfl

/-- Definition of `is_O` in terms of filters. We record it in a lemma as we will set
`is_O` to be irreducible at the end of this file. -/
theorem is_O_iff {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E] [has_norm F] {f : α → E}
    {g : α → F} {l : filter α} :
    is_O f g l ↔ ∃ (c : ℝ), filter.eventually (fun (x : α) => norm (f x) ≤ c * norm (g x)) l :=
  iff.rfl

theorem is_O.of_bound {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E] [has_norm F] (c : ℝ)
    {f : α → E} {g : α → F} {l : filter α}
    (h : filter.eventually (fun (x : α) => norm (f x) ≤ c * norm (g x)) l) : is_O f g l :=
  Exists.intro c h

/-- The Landau notation `is_o f g l` where `f` and `g` are two functions on a type `α` and `l` is
a filter on `α`, means that eventually for `l`, `∥f∥` is bounded by an arbitrarily small constant
multiple of `∥g∥`. In other words, `∥f∥ / ∥g∥` tends to `0` along `l`, modulo division by zero
issues that are avoided by this definition. -/
def is_o {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E] [has_norm F] (f : α → E)
    (g : α → F) (l : filter α) :=
  ∀ {c : ℝ}, 0 < c → is_O_with c f g l

/-- Definition of `is_o` in terms of `is_O_with`. We record it in a lemma as we will set
`is_o` to be irreducible at the end of this file. -/
theorem is_o_iff_forall_is_O_with {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E]
    [has_norm F] {f : α → E} {g : α → F} {l : filter α} :
    is_o f g l ↔ ∀ {c : ℝ}, 0 < c → is_O_with c f g l :=
  iff.rfl

/-- Definition of `is_o` in terms of filters. We record it in a lemma as we will set
`is_o` to be irreducible at the end of this file. -/
theorem is_o_iff {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E] [has_norm F] {f : α → E}
    {g : α → F} {l : filter α} :
    is_o f g l ↔
        ∀ {c : ℝ}, 0 < c → filter.eventually (fun (x : α) => norm (f x) ≤ c * norm (g x)) l :=
  iff.rfl

theorem is_o.def {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E] [has_norm F] {f : α → E}
    {g : α → F} {l : filter α} (h : is_o f g l) {c : ℝ} (hc : 0 < c) :
    filter.eventually (fun (x : α) => norm (f x) ≤ c * norm (g x)) l :=
  h hc

theorem is_o.def' {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E] [has_norm F] {f : α → E}
    {g : α → F} {l : filter α} (h : is_o f g l) {c : ℝ} (hc : 0 < c) : is_O_with c f g l :=
  h hc

/-! ### Conversions -/

theorem is_O_with.is_O {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E] [has_norm F]
    {c : ℝ} {f : α → E} {g : α → F} {l : filter α} (h : is_O_with c f g l) : is_O f g l :=
  Exists.intro c h

theorem is_o.is_O_with {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E] [has_norm F]
    {f : α → E} {g : α → F} {l : filter α} (hgf : is_o f g l) : is_O_with 1 f g l :=
  hgf zero_lt_one

theorem is_o.is_O {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E] [has_norm F] {f : α → E}
    {g : α → F} {l : filter α} (hgf : is_o f g l) : is_O f g l :=
  is_O_with.is_O (is_o.is_O_with hgf)

theorem is_O_with.weaken {α : Type u_1} {E : Type u_3} {F' : Type u_7} [has_norm E]
    [normed_group F'] {c : ℝ} {c' : ℝ} {f : α → E} {g' : α → F'} {l : filter α}
    (h : is_O_with c f g' l) (hc : c ≤ c') : is_O_with c' f g' l :=
  filter.mem_sets_of_superset h
    fun (x : α) (hx : x ∈ set_of fun (x : α) => (fun (x : α) => norm (f x) ≤ c * norm (g' x)) x) =>
      le_trans hx (mul_le_mul_of_nonneg_right hc (norm_nonneg (g' x)))

theorem is_O_with.exists_pos {α : Type u_1} {E : Type u_3} {F' : Type u_7} [has_norm E]
    [normed_group F'] {c : ℝ} {f : α → E} {g' : α → F'} {l : filter α} (h : is_O_with c f g' l) :
    ∃ (c' : ℝ), ∃ (H : 0 < c'), is_O_with c' f g' l :=
  Exists.intro (max c 1)
    (Exists.intro (lt_of_lt_of_le zero_lt_one (le_max_right c 1))
      (is_O_with.weaken h (le_max_left c 1)))

theorem is_O.exists_pos {α : Type u_1} {E : Type u_3} {F' : Type u_7} [has_norm E] [normed_group F']
    {f : α → E} {g' : α → F'} {l : filter α} (h : is_O f g' l) :
    ∃ (c : ℝ), ∃ (H : 0 < c), is_O_with c f g' l :=
  sorry

theorem is_O_with.exists_nonneg {α : Type u_1} {E : Type u_3} {F' : Type u_7} [has_norm E]
    [normed_group F'] {c : ℝ} {f : α → E} {g' : α → F'} {l : filter α} (h : is_O_with c f g' l) :
    ∃ (c' : ℝ), ∃ (H : 0 ≤ c'), is_O_with c' f g' l :=
  sorry

theorem is_O.exists_nonneg {α : Type u_1} {E : Type u_3} {F' : Type u_7} [has_norm E]
    [normed_group F'] {f : α → E} {g' : α → F'} {l : filter α} (h : is_O f g' l) :
    ∃ (c : ℝ), ∃ (H : 0 ≤ c), is_O_with c f g' l :=
  sorry

/-! ### Subsingleton -/

theorem is_o_of_subsingleton {α : Type u_1} {E' : Type u_6} {F' : Type u_7} [normed_group E']
    [normed_group F'] {f' : α → E'} {g' : α → F'} {l : filter α} [subsingleton E'] : is_o f' g' l :=
  sorry

theorem is_O_of_subsingleton {α : Type u_1} {E' : Type u_6} {F' : Type u_7} [normed_group E']
    [normed_group F'] {f' : α → E'} {g' : α → F'} {l : filter α} [subsingleton E'] : is_O f' g' l :=
  is_o.is_O is_o_of_subsingleton

/-! ### Congruence -/

theorem is_O_with_congr {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E] [has_norm F]
    {c₁ : ℝ} {c₂ : ℝ} {f₁ : α → E} {f₂ : α → E} {g₁ : α → F} {g₂ : α → F} {l : filter α}
    (hc : c₁ = c₂) (hf : filter.eventually_eq l f₁ f₂) (hg : filter.eventually_eq l g₁ g₂) :
    is_O_with c₁ f₁ g₁ l ↔ is_O_with c₂ f₂ g₂ l :=
  sorry

theorem is_O_with.congr' {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E] [has_norm F]
    {c₁ : ℝ} {c₂ : ℝ} {f₁ : α → E} {f₂ : α → E} {g₁ : α → F} {g₂ : α → F} {l : filter α}
    (hc : c₁ = c₂) (hf : filter.eventually_eq l f₁ f₂) (hg : filter.eventually_eq l g₁ g₂) :
    is_O_with c₁ f₁ g₁ l → is_O_with c₂ f₂ g₂ l :=
  iff.mp (is_O_with_congr hc hf hg)

theorem is_O_with.congr {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E] [has_norm F]
    {c₁ : ℝ} {c₂ : ℝ} {f₁ : α → E} {f₂ : α → E} {g₁ : α → F} {g₂ : α → F} {l : filter α}
    (hc : c₁ = c₂) (hf : ∀ (x : α), f₁ x = f₂ x) (hg : ∀ (x : α), g₁ x = g₂ x) :
    is_O_with c₁ f₁ g₁ l → is_O_with c₂ f₂ g₂ l :=
  fun (h : is_O_with c₁ f₁ g₁ l) =>
    is_O_with.congr' hc (filter.univ_mem_sets' hf) (filter.univ_mem_sets' hg) h

theorem is_O_with.congr_left {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E] [has_norm F]
    {c : ℝ} {g : α → F} {f₁ : α → E} {f₂ : α → E} {l : filter α} (hf : ∀ (x : α), f₁ x = f₂ x) :
    is_O_with c f₁ g l → is_O_with c f₂ g l :=
  is_O_with.congr rfl hf fun (_x : α) => rfl

theorem is_O_with.congr_right {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E] [has_norm F]
    {c : ℝ} {f : α → E} {g₁ : α → F} {g₂ : α → F} {l : filter α} (hg : ∀ (x : α), g₁ x = g₂ x) :
    is_O_with c f g₁ l → is_O_with c f g₂ l :=
  is_O_with.congr rfl (fun (_x : α) => rfl) hg

theorem is_O_with.congr_const {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E] [has_norm F]
    {f : α → E} {g : α → F} {c₁ : ℝ} {c₂ : ℝ} {l : filter α} (hc : c₁ = c₂) :
    is_O_with c₁ f g l → is_O_with c₂ f g l :=
  is_O_with.congr hc (fun (_x : α) => rfl) fun (_x : α) => rfl

theorem is_O_congr {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E] [has_norm F]
    {f₁ : α → E} {f₂ : α → E} {g₁ : α → F} {g₂ : α → F} {l : filter α}
    (hf : filter.eventually_eq l f₁ f₂) (hg : filter.eventually_eq l g₁ g₂) :
    is_O f₁ g₁ l ↔ is_O f₂ g₂ l :=
  exists_congr fun (c : ℝ) => is_O_with_congr rfl hf hg

theorem is_O.congr' {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E] [has_norm F]
    {f₁ : α → E} {f₂ : α → E} {g₁ : α → F} {g₂ : α → F} {l : filter α}
    (hf : filter.eventually_eq l f₁ f₂) (hg : filter.eventually_eq l g₁ g₂) :
    is_O f₁ g₁ l → is_O f₂ g₂ l :=
  iff.mp (is_O_congr hf hg)

theorem is_O.congr {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E] [has_norm F]
    {f₁ : α → E} {f₂ : α → E} {g₁ : α → F} {g₂ : α → F} {l : filter α} (hf : ∀ (x : α), f₁ x = f₂ x)
    (hg : ∀ (x : α), g₁ x = g₂ x) : is_O f₁ g₁ l → is_O f₂ g₂ l :=
  fun (h : is_O f₁ g₁ l) => is_O.congr' (filter.univ_mem_sets' hf) (filter.univ_mem_sets' hg) h

theorem is_O.congr_left {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E] [has_norm F]
    {g : α → F} {f₁ : α → E} {f₂ : α → E} {l : filter α} (hf : ∀ (x : α), f₁ x = f₂ x) :
    is_O f₁ g l → is_O f₂ g l :=
  is_O.congr hf fun (_x : α) => rfl

theorem is_O.congr_right {α : Type u_1} {E : Type u_3} [has_norm E] {f : α → E} {g₁ : α → E}
    {g₂ : α → E} {l : filter α} (hg : ∀ (x : α), g₁ x = g₂ x) : is_O f g₁ l → is_O f g₂ l :=
  is_O.congr (fun (_x : α) => rfl) hg

theorem is_o_congr {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E] [has_norm F]
    {f₁ : α → E} {f₂ : α → E} {g₁ : α → F} {g₂ : α → F} {l : filter α}
    (hf : filter.eventually_eq l f₁ f₂) (hg : filter.eventually_eq l g₁ g₂) :
    is_o f₁ g₁ l ↔ is_o f₂ g₂ l :=
  ball_congr fun (c : ℝ) (hc : 0 < c) => is_O_with_congr (Eq.refl c) hf hg

theorem is_o.congr' {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E] [has_norm F]
    {f₁ : α → E} {f₂ : α → E} {g₁ : α → F} {g₂ : α → F} {l : filter α}
    (hf : filter.eventually_eq l f₁ f₂) (hg : filter.eventually_eq l g₁ g₂) :
    is_o f₁ g₁ l → is_o f₂ g₂ l :=
  iff.mp (is_o_congr hf hg)

theorem is_o.congr {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E] [has_norm F]
    {f₁ : α → E} {f₂ : α → E} {g₁ : α → F} {g₂ : α → F} {l : filter α} (hf : ∀ (x : α), f₁ x = f₂ x)
    (hg : ∀ (x : α), g₁ x = g₂ x) : is_o f₁ g₁ l → is_o f₂ g₂ l :=
  fun (h : is_o f₁ g₁ l) => is_o.congr' (filter.univ_mem_sets' hf) (filter.univ_mem_sets' hg) h

theorem is_o.congr_left {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E] [has_norm F]
    {g : α → F} {f₁ : α → E} {f₂ : α → E} {l : filter α} (hf : ∀ (x : α), f₁ x = f₂ x) :
    is_o f₁ g l → is_o f₂ g l :=
  is_o.congr hf fun (_x : α) => rfl

theorem is_o.congr_right {α : Type u_1} {E : Type u_3} [has_norm E] {f : α → E} {g₁ : α → E}
    {g₂ : α → E} {l : filter α} (hg : ∀ (x : α), g₁ x = g₂ x) : is_o f g₁ l → is_o f g₂ l :=
  is_o.congr (fun (_x : α) => rfl) hg

/-! ### Filter operations and transitivity -/

theorem is_O_with.comp_tendsto {α : Type u_1} {β : Type u_2} {E : Type u_3} {F : Type u_4}
    [has_norm E] [has_norm F] {c : ℝ} {f : α → E} {g : α → F} {l : filter α}
    (hcfg : is_O_with c f g l) {k : β → α} {l' : filter β} (hk : filter.tendsto k l' l) :
    is_O_with c (f ∘ k) (g ∘ k) l' :=
  hk hcfg

theorem is_O.comp_tendsto {α : Type u_1} {β : Type u_2} {E : Type u_3} {F : Type u_4} [has_norm E]
    [has_norm F] {f : α → E} {g : α → F} {l : filter α} (hfg : is_O f g l) {k : β → α}
    {l' : filter β} (hk : filter.tendsto k l' l) : is_O (f ∘ k) (g ∘ k) l' :=
  Exists.imp (fun (c : ℝ) (h : is_O_with c f g l) => is_O_with.comp_tendsto h hk) hfg

theorem is_o.comp_tendsto {α : Type u_1} {β : Type u_2} {E : Type u_3} {F : Type u_4} [has_norm E]
    [has_norm F] {f : α → E} {g : α → F} {l : filter α} (hfg : is_o f g l) {k : β → α}
    {l' : filter β} (hk : filter.tendsto k l' l) : is_o (f ∘ k) (g ∘ k) l' :=
  fun (c : ℝ) (cpos : 0 < c) => is_O_with.comp_tendsto (hfg cpos) hk

@[simp] theorem is_O_with_map {α : Type u_1} {β : Type u_2} {E : Type u_3} {F : Type u_4}
    [has_norm E] [has_norm F] {c : ℝ} {f : α → E} {g : α → F} {k : β → α} {l : filter β} :
    is_O_with c f g (filter.map k l) ↔ is_O_with c (f ∘ k) (g ∘ k) l :=
  filter.mem_map

@[simp] theorem is_O_map {α : Type u_1} {β : Type u_2} {E : Type u_3} {F : Type u_4} [has_norm E]
    [has_norm F] {f : α → E} {g : α → F} {k : β → α} {l : filter β} :
    is_O f g (filter.map k l) ↔ is_O (f ∘ k) (g ∘ k) l :=
  sorry

@[simp] theorem is_o_map {α : Type u_1} {β : Type u_2} {E : Type u_3} {F : Type u_4} [has_norm E]
    [has_norm F] {f : α → E} {g : α → F} {k : β → α} {l : filter β} :
    is_o f g (filter.map k l) ↔ is_o (f ∘ k) (g ∘ k) l :=
  sorry

theorem is_O_with.mono {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E] [has_norm F]
    {c : ℝ} {f : α → E} {g : α → F} {l : filter α} {l' : filter α} (h : is_O_with c f g l')
    (hl : l ≤ l') : is_O_with c f g l :=
  hl h

theorem is_O.mono {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E] [has_norm F] {f : α → E}
    {g : α → F} {l : filter α} {l' : filter α} (h : is_O f g l') (hl : l ≤ l') : is_O f g l :=
  Exists.imp (fun (c : ℝ) (h : is_O_with c f g l') => is_O_with.mono h hl) h

theorem is_o.mono {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E] [has_norm F] {f : α → E}
    {g : α → F} {l : filter α} {l' : filter α} (h : is_o f g l') (hl : l ≤ l') : is_o f g l :=
  fun (c : ℝ) (cpos : 0 < c) => is_O_with.mono (h cpos) hl

theorem is_O_with.trans {α : Type u_1} {E : Type u_3} {F : Type u_4} {G : Type u_5} [has_norm E]
    [has_norm F] [has_norm G] {c : ℝ} {c' : ℝ} {f : α → E} {g : α → F} {k : α → G} {l : filter α}
    (hfg : is_O_with c f g l) (hgk : is_O_with c' g k l) (hc : 0 ≤ c) : is_O_with (c * c') f k l :=
  sorry

theorem is_O.trans {α : Type u_1} {E : Type u_3} {G : Type u_5} {F' : Type u_7} [has_norm E]
    [has_norm G] [normed_group F'] {f : α → E} {k : α → G} {g' : α → F'} {l : filter α}
    (hfg : is_O f g' l) (hgk : is_O g' k l) : is_O f k l :=
  sorry

theorem is_o.trans_is_O_with {α : Type u_1} {E : Type u_3} {F : Type u_4} {G : Type u_5}
    [has_norm E] [has_norm F] [has_norm G] {c : ℝ} {f : α → E} {g : α → F} {k : α → G}
    {l : filter α} (hfg : is_o f g l) (hgk : is_O_with c g k l) (hc : 0 < c) : is_o f k l :=
  sorry

theorem is_o.trans_is_O {α : Type u_1} {E : Type u_3} {F : Type u_4} {G' : Type u_8} [has_norm E]
    [has_norm F] [normed_group G'] {f : α → E} {g : α → F} {k' : α → G'} {l : filter α}
    (hfg : is_o f g l) (hgk : is_O g k' l) : is_o f k' l :=
  sorry

theorem is_O_with.trans_is_o {α : Type u_1} {E : Type u_3} {F : Type u_4} {G : Type u_5}
    [has_norm E] [has_norm F] [has_norm G] {c : ℝ} {f : α → E} {g : α → F} {k : α → G}
    {l : filter α} (hfg : is_O_with c f g l) (hgk : is_o g k l) (hc : 0 < c) : is_o f k l :=
  sorry

theorem is_O.trans_is_o {α : Type u_1} {E : Type u_3} {G : Type u_5} {F' : Type u_7} [has_norm E]
    [has_norm G] [normed_group F'] {f : α → E} {k : α → G} {g' : α → F'} {l : filter α}
    (hfg : is_O f g' l) (hgk : is_o g' k l) : is_o f k l :=
  sorry

theorem is_o.trans {α : Type u_1} {E : Type u_3} {F : Type u_4} {G' : Type u_8} [has_norm E]
    [has_norm F] [normed_group G'] {f : α → E} {g : α → F} {k' : α → G'} {l : filter α}
    (hfg : is_o f g l) (hgk : is_o g k' l) : is_o f k' l :=
  is_o.trans_is_O hfg (is_o.is_O hgk)

theorem is_o.trans' {α : Type u_1} {E : Type u_3} {G : Type u_5} {F' : Type u_7} [has_norm E]
    [has_norm G] [normed_group F'] {f : α → E} {k : α → G} {g' : α → F'} {l : filter α}
    (hfg : is_o f g' l) (hgk : is_o g' k l) : is_o f k l :=
  is_O.trans_is_o (is_o.is_O hfg) hgk

theorem is_O_with_of_le' {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E] [has_norm F]
    {c : ℝ} {f : α → E} {g : α → F} (l : filter α) (hfg : ∀ (x : α), norm (f x) ≤ c * norm (g x)) :
    is_O_with c f g l :=
  filter.univ_mem_sets' hfg

theorem is_O_with_of_le {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E] [has_norm F]
    {f : α → E} {g : α → F} (l : filter α) (hfg : ∀ (x : α), norm (f x) ≤ norm (g x)) :
    is_O_with 1 f g l :=
  is_O_with_of_le' l
    fun (x : α) =>
      eq.mpr (id (Eq._oldrec (Eq.refl (norm (f x) ≤ 1 * norm (g x))) (one_mul (norm (g x)))))
        (hfg x)

theorem is_O_of_le' {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E] [has_norm F] {c : ℝ}
    {f : α → E} {g : α → F} (l : filter α) (hfg : ∀ (x : α), norm (f x) ≤ c * norm (g x)) :
    is_O f g l :=
  is_O_with.is_O (is_O_with_of_le' l hfg)

theorem is_O_of_le {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E] [has_norm F]
    {f : α → E} {g : α → F} (l : filter α) (hfg : ∀ (x : α), norm (f x) ≤ norm (g x)) :
    is_O f g l :=
  is_O_with.is_O (is_O_with_of_le l hfg)

theorem is_O_with_refl {α : Type u_1} {E : Type u_3} [has_norm E] (f : α → E) (l : filter α) :
    is_O_with 1 f f l :=
  is_O_with_of_le l fun (_x : α) => le_refl (norm (f _x))

theorem is_O_refl {α : Type u_1} {E : Type u_3} [has_norm E] (f : α → E) (l : filter α) :
    is_O f f l :=
  is_O_with.is_O (is_O_with_refl f l)

theorem is_O_with.trans_le {α : Type u_1} {E : Type u_3} {F : Type u_4} {G : Type u_5} [has_norm E]
    [has_norm F] [has_norm G] {c : ℝ} {f : α → E} {g : α → F} {k : α → G} {l : filter α}
    (hfg : is_O_with c f g l) (hgk : ∀ (x : α), norm (g x) ≤ norm (k x)) (hc : 0 ≤ c) :
    is_O_with c f k l :=
  is_O_with.congr_const (mul_one c) (is_O_with.trans hfg (is_O_with_of_le l hgk) hc)

theorem is_O.trans_le {α : Type u_1} {E : Type u_3} {G : Type u_5} {F' : Type u_7} [has_norm E]
    [has_norm G] [normed_group F'] {f : α → E} {k : α → G} {g' : α → F'} {l : filter α}
    (hfg : is_O f g' l) (hgk : ∀ (x : α), norm (g' x) ≤ norm (k x)) : is_O f k l :=
  is_O.trans hfg (is_O_of_le l hgk)

theorem is_o.trans_le {α : Type u_1} {E : Type u_3} {F : Type u_4} {G : Type u_5} [has_norm E]
    [has_norm F] [has_norm G] {f : α → E} {g : α → F} {k : α → G} {l : filter α} (hfg : is_o f g l)
    (hgk : ∀ (x : α), norm (g x) ≤ norm (k x)) : is_o f k l :=
  is_o.trans_is_O_with hfg (is_O_with_of_le l hgk) zero_lt_one

@[simp] theorem is_O_with_bot {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E] [has_norm F]
    (c : ℝ) (f : α → E) (g : α → F) : is_O_with c f g ⊥ :=
  trivial

@[simp] theorem is_O_bot {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E] [has_norm F]
    (f : α → E) (g : α → F) : is_O f g ⊥ :=
  is_O_with.is_O (is_O_with_bot 1 f g)

@[simp] theorem is_o_bot {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E] [has_norm F]
    (f : α → E) (g : α → F) : is_o f g ⊥ :=
  fun (c : ℝ) (_x : 0 < c) => is_O_with_bot c f g

theorem is_O_with.join {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E] [has_norm F]
    {c : ℝ} {f : α → E} {g : α → F} {l : filter α} {l' : filter α} (h : is_O_with c f g l)
    (h' : is_O_with c f g l') : is_O_with c f g (l ⊔ l') :=
  iff.mpr filter.mem_sup_sets { left := h, right := h' }

theorem is_O_with.join' {α : Type u_1} {E : Type u_3} {F' : Type u_7} [has_norm E] [normed_group F']
    {c : ℝ} {c' : ℝ} {f : α → E} {g' : α → F'} {l : filter α} {l' : filter α}
    (h : is_O_with c f g' l) (h' : is_O_with c' f g' l') : is_O_with (max c c') f g' (l ⊔ l') :=
  iff.mpr filter.mem_sup_sets
    { left := is_O_with.weaken h (le_max_left c c'),
      right := is_O_with.weaken h' (le_max_right c c') }

theorem is_O.join {α : Type u_1} {E : Type u_3} {F' : Type u_7} [has_norm E] [normed_group F']
    {f : α → E} {g' : α → F'} {l : filter α} {l' : filter α} (h : is_O f g' l) (h' : is_O f g' l') :
    is_O f g' (l ⊔ l') :=
  sorry

theorem is_o.join {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E] [has_norm F] {f : α → E}
    {g : α → F} {l : filter α} {l' : filter α} (h : is_o f g l) (h' : is_o f g l') :
    is_o f g (l ⊔ l') :=
  fun (c : ℝ) (cpos : 0 < c) => is_O_with.join (h cpos) (h' cpos)

/-! ### Simplification : norm -/

@[simp] theorem is_O_with_norm_right {α : Type u_1} {E : Type u_3} {F' : Type u_7} [has_norm E]
    [normed_group F'] {c : ℝ} {f : α → E} {g' : α → F'} {l : filter α} :
    is_O_with c f (fun (x : α) => norm (g' x)) l ↔ is_O_with c f g' l :=
  sorry

theorem is_O_with.norm_right {α : Type u_1} {E : Type u_3} {F' : Type u_7} [has_norm E]
    [normed_group F'] {c : ℝ} {f : α → E} {g' : α → F'} {l : filter α} :
    is_O_with c f g' l → is_O_with c f (fun (x : α) => norm (g' x)) l :=
  iff.mpr is_O_with_norm_right

@[simp] theorem is_O_norm_right {α : Type u_1} {E : Type u_3} {F' : Type u_7} [has_norm E]
    [normed_group F'] {f : α → E} {g' : α → F'} {l : filter α} :
    is_O f (fun (x : α) => norm (g' x)) l ↔ is_O f g' l :=
  exists_congr fun (_x : ℝ) => is_O_with_norm_right

theorem is_O.norm_right {α : Type u_1} {E : Type u_3} {F' : Type u_7} [has_norm E] [normed_group F']
    {f : α → E} {g' : α → F'} {l : filter α} :
    is_O f g' l → is_O f (fun (x : α) => norm (g' x)) l :=
  iff.mpr is_O_norm_right

@[simp] theorem is_o_norm_right {α : Type u_1} {E : Type u_3} {F' : Type u_7} [has_norm E]
    [normed_group F'] {f : α → E} {g' : α → F'} {l : filter α} :
    is_o f (fun (x : α) => norm (g' x)) l ↔ is_o f g' l :=
  forall_congr fun (_x : ℝ) => forall_congr fun (_x_1 : 0 < _x) => is_O_with_norm_right

theorem is_o.norm_right {α : Type u_1} {E : Type u_3} {F' : Type u_7} [has_norm E] [normed_group F']
    {f : α → E} {g' : α → F'} {l : filter α} :
    is_o f g' l → is_o f (fun (x : α) => norm (g' x)) l :=
  iff.mpr is_o_norm_right

@[simp] theorem is_O_with_norm_left {α : Type u_1} {F : Type u_4} {E' : Type u_6} [has_norm F]
    [normed_group E'] {c : ℝ} {g : α → F} {f' : α → E'} {l : filter α} :
    is_O_with c (fun (x : α) => norm (f' x)) g l ↔ is_O_with c f' g l :=
  sorry

theorem is_O_with.of_norm_left {α : Type u_1} {F : Type u_4} {E' : Type u_6} [has_norm F]
    [normed_group E'] {c : ℝ} {g : α → F} {f' : α → E'} {l : filter α} :
    is_O_with c (fun (x : α) => norm (f' x)) g l → is_O_with c f' g l :=
  iff.mp is_O_with_norm_left

@[simp] theorem is_O_norm_left {α : Type u_1} {F : Type u_4} {E' : Type u_6} [has_norm F]
    [normed_group E'] {g : α → F} {f' : α → E'} {l : filter α} :
    is_O (fun (x : α) => norm (f' x)) g l ↔ is_O f' g l :=
  exists_congr fun (_x : ℝ) => is_O_with_norm_left

theorem is_O.of_norm_left {α : Type u_1} {F : Type u_4} {E' : Type u_6} [has_norm F]
    [normed_group E'] {g : α → F} {f' : α → E'} {l : filter α} :
    is_O (fun (x : α) => norm (f' x)) g l → is_O f' g l :=
  iff.mp is_O_norm_left

@[simp] theorem is_o_norm_left {α : Type u_1} {F : Type u_4} {E' : Type u_6} [has_norm F]
    [normed_group E'] {g : α → F} {f' : α → E'} {l : filter α} :
    is_o (fun (x : α) => norm (f' x)) g l ↔ is_o f' g l :=
  forall_congr fun (_x : ℝ) => forall_congr fun (_x_1 : 0 < _x) => is_O_with_norm_left

theorem is_o.of_norm_left {α : Type u_1} {F : Type u_4} {E' : Type u_6} [has_norm F]
    [normed_group E'] {g : α → F} {f' : α → E'} {l : filter α} :
    is_o (fun (x : α) => norm (f' x)) g l → is_o f' g l :=
  iff.mp is_o_norm_left

theorem is_O_with_norm_norm {α : Type u_1} {E' : Type u_6} {F' : Type u_7} [normed_group E']
    [normed_group F'] {c : ℝ} {f' : α → E'} {g' : α → F'} {l : filter α} :
    is_O_with c (fun (x : α) => norm (f' x)) (fun (x : α) => norm (g' x)) l ↔ is_O_with c f' g' l :=
  iff.trans is_O_with_norm_left is_O_with_norm_right

theorem is_O_with.of_norm_norm {α : Type u_1} {E' : Type u_6} {F' : Type u_7} [normed_group E']
    [normed_group F'] {c : ℝ} {f' : α → E'} {g' : α → F'} {l : filter α} :
    is_O_with c (fun (x : α) => norm (f' x)) (fun (x : α) => norm (g' x)) l → is_O_with c f' g' l :=
  iff.mp is_O_with_norm_norm

theorem is_O_norm_norm {α : Type u_1} {E' : Type u_6} {F' : Type u_7} [normed_group E']
    [normed_group F'] {f' : α → E'} {g' : α → F'} {l : filter α} :
    is_O (fun (x : α) => norm (f' x)) (fun (x : α) => norm (g' x)) l ↔ is_O f' g' l :=
  iff.trans is_O_norm_left is_O_norm_right

theorem is_O.of_norm_norm {α : Type u_1} {E' : Type u_6} {F' : Type u_7} [normed_group E']
    [normed_group F'] {f' : α → E'} {g' : α → F'} {l : filter α} :
    is_O (fun (x : α) => norm (f' x)) (fun (x : α) => norm (g' x)) l → is_O f' g' l :=
  iff.mp is_O_norm_norm

theorem is_o_norm_norm {α : Type u_1} {E' : Type u_6} {F' : Type u_7} [normed_group E']
    [normed_group F'] {f' : α → E'} {g' : α → F'} {l : filter α} :
    is_o (fun (x : α) => norm (f' x)) (fun (x : α) => norm (g' x)) l ↔ is_o f' g' l :=
  iff.trans is_o_norm_left is_o_norm_right

theorem is_o.norm_norm {α : Type u_1} {E' : Type u_6} {F' : Type u_7} [normed_group E']
    [normed_group F'] {f' : α → E'} {g' : α → F'} {l : filter α} :
    is_o f' g' l → is_o (fun (x : α) => norm (f' x)) (fun (x : α) => norm (g' x)) l :=
  iff.mpr is_o_norm_norm

/-! ### Simplification: negate -/

@[simp] theorem is_O_with_neg_right {α : Type u_1} {E : Type u_3} {F' : Type u_7} [has_norm E]
    [normed_group F'] {c : ℝ} {f : α → E} {g' : α → F'} {l : filter α} :
    is_O_with c f (fun (x : α) => -g' x) l ↔ is_O_with c f g' l :=
  sorry

theorem is_O_with.neg_right {α : Type u_1} {E : Type u_3} {F' : Type u_7} [has_norm E]
    [normed_group F'] {c : ℝ} {f : α → E} {g' : α → F'} {l : filter α} :
    is_O_with c f g' l → is_O_with c f (fun (x : α) => -g' x) l :=
  iff.mpr is_O_with_neg_right

@[simp] theorem is_O_neg_right {α : Type u_1} {E : Type u_3} {F' : Type u_7} [has_norm E]
    [normed_group F'] {f : α → E} {g' : α → F'} {l : filter α} :
    is_O f (fun (x : α) => -g' x) l ↔ is_O f g' l :=
  exists_congr fun (_x : ℝ) => is_O_with_neg_right

theorem is_O.of_neg_right {α : Type u_1} {E : Type u_3} {F' : Type u_7} [has_norm E]
    [normed_group F'] {f : α → E} {g' : α → F'} {l : filter α} :
    is_O f (fun (x : α) => -g' x) l → is_O f g' l :=
  iff.mp is_O_neg_right

@[simp] theorem is_o_neg_right {α : Type u_1} {E : Type u_3} {F' : Type u_7} [has_norm E]
    [normed_group F'] {f : α → E} {g' : α → F'} {l : filter α} :
    is_o f (fun (x : α) => -g' x) l ↔ is_o f g' l :=
  forall_congr fun (_x : ℝ) => forall_congr fun (_x_1 : 0 < _x) => is_O_with_neg_right

theorem is_o.of_neg_right {α : Type u_1} {E : Type u_3} {F' : Type u_7} [has_norm E]
    [normed_group F'] {f : α → E} {g' : α → F'} {l : filter α} :
    is_o f (fun (x : α) => -g' x) l → is_o f g' l :=
  iff.mp is_o_neg_right

@[simp] theorem is_O_with_neg_left {α : Type u_1} {F : Type u_4} {E' : Type u_6} [has_norm F]
    [normed_group E'] {c : ℝ} {g : α → F} {f' : α → E'} {l : filter α} :
    is_O_with c (fun (x : α) => -f' x) g l ↔ is_O_with c f' g l :=
  sorry

theorem is_O_with.neg_left {α : Type u_1} {F : Type u_4} {E' : Type u_6} [has_norm F]
    [normed_group E'] {c : ℝ} {g : α → F} {f' : α → E'} {l : filter α} :
    is_O_with c f' g l → is_O_with c (fun (x : α) => -f' x) g l :=
  iff.mpr is_O_with_neg_left

@[simp] theorem is_O_neg_left {α : Type u_1} {F : Type u_4} {E' : Type u_6} [has_norm F]
    [normed_group E'] {g : α → F} {f' : α → E'} {l : filter α} :
    is_O (fun (x : α) => -f' x) g l ↔ is_O f' g l :=
  exists_congr fun (_x : ℝ) => is_O_with_neg_left

theorem is_O.neg_left {α : Type u_1} {F : Type u_4} {E' : Type u_6} [has_norm F] [normed_group E']
    {g : α → F} {f' : α → E'} {l : filter α} : is_O f' g l → is_O (fun (x : α) => -f' x) g l :=
  iff.mpr is_O_neg_left

@[simp] theorem is_o_neg_left {α : Type u_1} {F : Type u_4} {E' : Type u_6} [has_norm F]
    [normed_group E'] {g : α → F} {f' : α → E'} {l : filter α} :
    is_o (fun (x : α) => -f' x) g l ↔ is_o f' g l :=
  forall_congr fun (_x : ℝ) => forall_congr fun (_x_1 : 0 < _x) => is_O_with_neg_left

theorem is_o.neg_left {α : Type u_1} {F : Type u_4} {E' : Type u_6} [has_norm F] [normed_group E']
    {g : α → F} {f' : α → E'} {l : filter α} : is_o f' g l → is_o (fun (x : α) => -f' x) g l :=
  iff.mpr is_o_neg_left

/-! ### Product of functions (right) -/

theorem is_O_with_fst_prod {α : Type u_1} {E' : Type u_6} {F' : Type u_7} [normed_group E']
    [normed_group F'] {f' : α → E'} {g' : α → F'} {l : filter α} :
    is_O_with 1 f' (fun (x : α) => (f' x, g' x)) l :=
  is_O_with_of_le l fun (x : α) => le_max_left (norm (f' x)) (norm (prod.snd (f' x, g' x)))

theorem is_O_with_snd_prod {α : Type u_1} {E' : Type u_6} {F' : Type u_7} [normed_group E']
    [normed_group F'] {f' : α → E'} {g' : α → F'} {l : filter α} :
    is_O_with 1 g' (fun (x : α) => (f' x, g' x)) l :=
  is_O_with_of_le l fun (x : α) => le_max_right (norm (prod.fst (f' x, g' x))) (norm (g' x))

theorem is_O_fst_prod {α : Type u_1} {E' : Type u_6} {F' : Type u_7} [normed_group E']
    [normed_group F'] {f' : α → E'} {g' : α → F'} {l : filter α} :
    is_O f' (fun (x : α) => (f' x, g' x)) l :=
  is_O_with.is_O is_O_with_fst_prod

theorem is_O_snd_prod {α : Type u_1} {E' : Type u_6} {F' : Type u_7} [normed_group E']
    [normed_group F'] {f' : α → E'} {g' : α → F'} {l : filter α} :
    is_O g' (fun (x : α) => (f' x, g' x)) l :=
  is_O_with.is_O is_O_with_snd_prod

theorem is_O_fst_prod' {α : Type u_1} {E' : Type u_6} {F' : Type u_7} [normed_group E']
    [normed_group F'] {l : filter α} {f' : α → E' × F'} :
    is_O (fun (x : α) => prod.fst (f' x)) f' l :=
  is_O_fst_prod

theorem is_O_snd_prod' {α : Type u_1} {E' : Type u_6} {F' : Type u_7} [normed_group E']
    [normed_group F'] {l : filter α} {f' : α → E' × F'} :
    is_O (fun (x : α) => prod.snd (f' x)) f' l :=
  is_O_snd_prod

theorem is_O_with.prod_rightl {α : Type u_1} {E : Type u_3} {F' : Type u_7} {G' : Type u_8}
    [has_norm E] [normed_group F'] [normed_group G'] {c : ℝ} {f : α → E} {g' : α → F'} (k' : α → G')
    {l : filter α} (h : is_O_with c f g' l) (hc : 0 ≤ c) :
    is_O_with c f (fun (x : α) => (g' x, k' x)) l :=
  is_O_with.congr_const (mul_one c) (is_O_with.trans h is_O_with_fst_prod hc)

theorem is_O.prod_rightl {α : Type u_1} {E : Type u_3} {F' : Type u_7} {G' : Type u_8} [has_norm E]
    [normed_group F'] [normed_group G'] {f : α → E} {g' : α → F'} (k' : α → G') {l : filter α}
    (h : is_O f g' l) : is_O f (fun (x : α) => (g' x, k' x)) l :=
  sorry

theorem is_o.prod_rightl {α : Type u_1} {E : Type u_3} {F' : Type u_7} {G' : Type u_8} [has_norm E]
    [normed_group F'] [normed_group G'] {f : α → E} {g' : α → F'} (k' : α → G') {l : filter α}
    (h : is_o f g' l) : is_o f (fun (x : α) => (g' x, k' x)) l :=
  fun (c : ℝ) (cpos : 0 < c) => is_O_with.prod_rightl k' (h cpos) (le_of_lt cpos)

theorem is_O_with.prod_rightr {α : Type u_1} {E : Type u_3} {E' : Type u_6} {F' : Type u_7}
    [has_norm E] [normed_group E'] [normed_group F'] {c : ℝ} {f : α → E} (f' : α → E') {g' : α → F'}
    {l : filter α} (h : is_O_with c f g' l) (hc : 0 ≤ c) :
    is_O_with c f (fun (x : α) => (f' x, g' x)) l :=
  is_O_with.congr_const (mul_one c) (is_O_with.trans h is_O_with_snd_prod hc)

theorem is_O.prod_rightr {α : Type u_1} {E : Type u_3} {E' : Type u_6} {F' : Type u_7} [has_norm E]
    [normed_group E'] [normed_group F'] {f : α → E} (f' : α → E') {g' : α → F'} {l : filter α}
    (h : is_O f g' l) : is_O f (fun (x : α) => (f' x, g' x)) l :=
  sorry

theorem is_o.prod_rightr {α : Type u_1} {E : Type u_3} {E' : Type u_6} {F' : Type u_7} [has_norm E]
    [normed_group E'] [normed_group F'] {f : α → E} (f' : α → E') {g' : α → F'} {l : filter α}
    (h : is_o f g' l) : is_o f (fun (x : α) => (f' x, g' x)) l :=
  fun (c : ℝ) (cpos : 0 < c) => is_O_with.prod_rightr f' (h cpos) (le_of_lt cpos)

theorem is_O_with.prod_left_same {α : Type u_1} {E' : Type u_6} {F' : Type u_7} {G' : Type u_8}
    [normed_group E'] [normed_group F'] [normed_group G'] {c : ℝ} {f' : α → E'} {g' : α → F'}
    {k' : α → G'} {l : filter α} (hf : is_O_with c f' k' l) (hg : is_O_with c g' k' l) :
    is_O_with c (fun (x : α) => (f' x, g' x)) k' l :=
  filter.mp_sets hg (filter.mp_sets hf (filter.univ_mem_sets' (id fun (x : α) => max_le)))

theorem is_O_with.prod_left {α : Type u_1} {E' : Type u_6} {F' : Type u_7} {G' : Type u_8}
    [normed_group E'] [normed_group F'] [normed_group G'] {c : ℝ} {c' : ℝ} {f' : α → E'}
    {g' : α → F'} {k' : α → G'} {l : filter α} (hf : is_O_with c f' k' l)
    (hg : is_O_with c' g' k' l) : is_O_with (max c c') (fun (x : α) => (f' x, g' x)) k' l :=
  is_O_with.prod_left_same (is_O_with.weaken hf (le_max_left c c'))
    (is_O_with.weaken hg (le_max_right c c'))

theorem is_O_with.prod_left_fst {α : Type u_1} {E' : Type u_6} {F' : Type u_7} {G' : Type u_8}
    [normed_group E'] [normed_group F'] [normed_group G'] {c : ℝ} {f' : α → E'} {g' : α → F'}
    {k' : α → G'} {l : filter α} (h : is_O_with c (fun (x : α) => (f' x, g' x)) k' l) :
    is_O_with c f' k' l :=
  is_O_with.congr_const (one_mul c) (is_O_with.trans is_O_with_fst_prod h zero_le_one)

theorem is_O_with.prod_left_snd {α : Type u_1} {E' : Type u_6} {F' : Type u_7} {G' : Type u_8}
    [normed_group E'] [normed_group F'] [normed_group G'] {c : ℝ} {f' : α → E'} {g' : α → F'}
    {k' : α → G'} {l : filter α} (h : is_O_with c (fun (x : α) => (f' x, g' x)) k' l) :
    is_O_with c g' k' l :=
  is_O_with.congr_const (one_mul c) (is_O_with.trans is_O_with_snd_prod h zero_le_one)

theorem is_O_with_prod_left {α : Type u_1} {E' : Type u_6} {F' : Type u_7} {G' : Type u_8}
    [normed_group E'] [normed_group F'] [normed_group G'] {c : ℝ} {f' : α → E'} {g' : α → F'}
    {k' : α → G'} {l : filter α} :
    is_O_with c (fun (x : α) => (f' x, g' x)) k' l ↔ is_O_with c f' k' l ∧ is_O_with c g' k' l :=
  sorry

theorem is_O.prod_left {α : Type u_1} {E' : Type u_6} {F' : Type u_7} {G' : Type u_8}
    [normed_group E'] [normed_group F'] [normed_group G'] {f' : α → E'} {g' : α → F'} {k' : α → G'}
    {l : filter α} (hf : is_O f' k' l) (hg : is_O g' k' l) :
    is_O (fun (x : α) => (f' x, g' x)) k' l :=
  sorry

theorem is_O.prod_left_fst {α : Type u_1} {E' : Type u_6} {F' : Type u_7} {G' : Type u_8}
    [normed_group E'] [normed_group F'] [normed_group G'] {f' : α → E'} {g' : α → F'} {k' : α → G'}
    {l : filter α} (h : is_O (fun (x : α) => (f' x, g' x)) k' l) : is_O f' k' l :=
  is_O.trans is_O_fst_prod h

theorem is_O.prod_left_snd {α : Type u_1} {E' : Type u_6} {F' : Type u_7} {G' : Type u_8}
    [normed_group E'] [normed_group F'] [normed_group G'] {f' : α → E'} {g' : α → F'} {k' : α → G'}
    {l : filter α} (h : is_O (fun (x : α) => (f' x, g' x)) k' l) : is_O g' k' l :=
  is_O.trans is_O_snd_prod h

@[simp] theorem is_O_prod_left {α : Type u_1} {E' : Type u_6} {F' : Type u_7} {G' : Type u_8}
    [normed_group E'] [normed_group F'] [normed_group G'] {f' : α → E'} {g' : α → F'} {k' : α → G'}
    {l : filter α} : is_O (fun (x : α) => (f' x, g' x)) k' l ↔ is_O f' k' l ∧ is_O g' k' l :=
  sorry

theorem is_o.prod_left {α : Type u_1} {E' : Type u_6} {F' : Type u_7} {G' : Type u_8}
    [normed_group E'] [normed_group F'] [normed_group G'] {f' : α → E'} {g' : α → F'} {k' : α → G'}
    {l : filter α} (hf : is_o f' k' l) (hg : is_o g' k' l) :
    is_o (fun (x : α) => (f' x, g' x)) k' l :=
  fun (c : ℝ) (hc : 0 < c) => is_O_with.prod_left_same (hf hc) (hg hc)

theorem is_o.prod_left_fst {α : Type u_1} {E' : Type u_6} {F' : Type u_7} {G' : Type u_8}
    [normed_group E'] [normed_group F'] [normed_group G'] {f' : α → E'} {g' : α → F'} {k' : α → G'}
    {l : filter α} (h : is_o (fun (x : α) => (f' x, g' x)) k' l) : is_o f' k' l :=
  is_O.trans_is_o is_O_fst_prod h

theorem is_o.prod_left_snd {α : Type u_1} {E' : Type u_6} {F' : Type u_7} {G' : Type u_8}
    [normed_group E'] [normed_group F'] [normed_group G'] {f' : α → E'} {g' : α → F'} {k' : α → G'}
    {l : filter α} (h : is_o (fun (x : α) => (f' x, g' x)) k' l) : is_o g' k' l :=
  is_O.trans_is_o is_O_snd_prod h

@[simp] theorem is_o_prod_left {α : Type u_1} {E' : Type u_6} {F' : Type u_7} {G' : Type u_8}
    [normed_group E'] [normed_group F'] [normed_group G'] {f' : α → E'} {g' : α → F'} {k' : α → G'}
    {l : filter α} : is_o (fun (x : α) => (f' x, g' x)) k' l ↔ is_o f' k' l ∧ is_o g' k' l :=
  sorry

theorem is_O_with.eq_zero_imp {α : Type u_1} {E' : Type u_6} {F' : Type u_7} [normed_group E']
    [normed_group F'] {c : ℝ} {f' : α → E'} {g' : α → F'} {l : filter α} (h : is_O_with c f' g' l) :
    filter.eventually (fun (x : α) => g' x = 0 → f' x = 0) l :=
  sorry

theorem is_O.eq_zero_imp {α : Type u_1} {E' : Type u_6} {F' : Type u_7} [normed_group E']
    [normed_group F'] {f' : α → E'} {g' : α → F'} {l : filter α} (h : is_O f' g' l) :
    filter.eventually (fun (x : α) => g' x = 0 → f' x = 0) l :=
  sorry

/-! ### Addition and subtraction -/

theorem is_O_with.add {α : Type u_1} {F : Type u_4} {E' : Type u_6} [has_norm F] [normed_group E']
    {g : α → F} {l : filter α} {c₁ : ℝ} {c₂ : ℝ} {f₁ : α → E'} {f₂ : α → E'}
    (h₁ : is_O_with c₁ f₁ g l) (h₂ : is_O_with c₂ f₂ g l) :
    is_O_with (c₁ + c₂) (fun (x : α) => f₁ x + f₂ x) g l :=
  sorry

theorem is_O.add {α : Type u_1} {F : Type u_4} {E' : Type u_6} [has_norm F] [normed_group E']
    {g : α → F} {l : filter α} {f₁ : α → E'} {f₂ : α → E'} :
    is_O f₁ g l → is_O f₂ g l → is_O (fun (x : α) => f₁ x + f₂ x) g l :=
  sorry

theorem is_o.add {α : Type u_1} {F : Type u_4} {E' : Type u_6} [has_norm F] [normed_group E']
    {g : α → F} {l : filter α} {f₁ : α → E'} {f₂ : α → E'} (h₁ : is_o f₁ g l) (h₂ : is_o f₂ g l) :
    is_o (fun (x : α) => f₁ x + f₂ x) g l :=
  fun (c : ℝ) (cpos : 0 < c) =>
    is_O_with.congr_const (add_halves c) (is_O_with.add (h₁ (half_pos cpos)) (h₂ (half_pos cpos)))

theorem is_o.add_add {α : Type u_1} {E' : Type u_6} {F' : Type u_7} [normed_group E']
    [normed_group F'] {l : filter α} {f₁ : α → E'} {f₂ : α → E'} {g₁ : α → F'} {g₂ : α → F'}
    (h₁ : is_o f₁ g₁ l) (h₂ : is_o f₂ g₂ l) :
    is_o (fun (x : α) => f₁ x + f₂ x) (fun (x : α) => norm (g₁ x) + norm (g₂ x)) l :=
  sorry

theorem is_O.add_is_o {α : Type u_1} {F : Type u_4} {E' : Type u_6} [has_norm F] [normed_group E']
    {g : α → F} {l : filter α} {f₁ : α → E'} {f₂ : α → E'} (h₁ : is_O f₁ g l) (h₂ : is_o f₂ g l) :
    is_O (fun (x : α) => f₁ x + f₂ x) g l :=
  is_O.add h₁ (is_o.is_O h₂)

theorem is_o.add_is_O {α : Type u_1} {F : Type u_4} {E' : Type u_6} [has_norm F] [normed_group E']
    {g : α → F} {l : filter α} {f₁ : α → E'} {f₂ : α → E'} (h₁ : is_o f₁ g l) (h₂ : is_O f₂ g l) :
    is_O (fun (x : α) => f₁ x + f₂ x) g l :=
  is_O.add (is_o.is_O h₁) h₂

theorem is_O_with.add_is_o {α : Type u_1} {F : Type u_4} {E' : Type u_6} [has_norm F]
    [normed_group E'] {g : α → F} {l : filter α} {c₁ : ℝ} {c₂ : ℝ} {f₁ : α → E'} {f₂ : α → E'}
    (h₁ : is_O_with c₁ f₁ g l) (h₂ : is_o f₂ g l) (hc : c₁ < c₂) :
    is_O_with c₂ (fun (x : α) => f₁ x + f₂ x) g l :=
  is_O_with.congr_const (add_sub_cancel'_right c₁ c₂) (is_O_with.add h₁ (h₂ (iff.mpr sub_pos hc)))

theorem is_o.add_is_O_with {α : Type u_1} {F : Type u_4} {E' : Type u_6} [has_norm F]
    [normed_group E'] {g : α → F} {l : filter α} {c₁ : ℝ} {c₂ : ℝ} {f₁ : α → E'} {f₂ : α → E'}
    (h₁ : is_o f₁ g l) (h₂ : is_O_with c₁ f₂ g l) (hc : c₁ < c₂) :
    is_O_with c₂ (fun (x : α) => f₁ x + f₂ x) g l :=
  is_O_with.congr_left (fun (_x : α) => add_comm (f₂ _x) (f₁ _x)) (is_O_with.add_is_o h₂ h₁ hc)

theorem is_O_with.sub {α : Type u_1} {F : Type u_4} {E' : Type u_6} [has_norm F] [normed_group E']
    {g : α → F} {l : filter α} {c₁ : ℝ} {c₂ : ℝ} {f₁ : α → E'} {f₂ : α → E'}
    (h₁ : is_O_with c₁ f₁ g l) (h₂ : is_O_with c₂ f₂ g l) :
    is_O_with (c₁ + c₂) (fun (x : α) => f₁ x - f₂ x) g l :=
  sorry

theorem is_O_with.sub_is_o {α : Type u_1} {F : Type u_4} {E' : Type u_6} [has_norm F]
    [normed_group E'] {g : α → F} {l : filter α} {c₁ : ℝ} {c₂ : ℝ} {f₁ : α → E'} {f₂ : α → E'}
    (h₁ : is_O_with c₁ f₁ g l) (h₂ : is_o f₂ g l) (hc : c₁ < c₂) :
    is_O_with c₂ (fun (x : α) => f₁ x - f₂ x) g l :=
  sorry

theorem is_O.sub {α : Type u_1} {F : Type u_4} {E' : Type u_6} [has_norm F] [normed_group E']
    {g : α → F} {l : filter α} {f₁ : α → E'} {f₂ : α → E'} (h₁ : is_O f₁ g l) (h₂ : is_O f₂ g l) :
    is_O (fun (x : α) => f₁ x - f₂ x) g l :=
  sorry

theorem is_o.sub {α : Type u_1} {F : Type u_4} {E' : Type u_6} [has_norm F] [normed_group E']
    {g : α → F} {l : filter α} {f₁ : α → E'} {f₂ : α → E'} (h₁ : is_o f₁ g l) (h₂ : is_o f₂ g l) :
    is_o (fun (x : α) => f₁ x - f₂ x) g l :=
  sorry

/-! ### Lemmas about `is_O (f₁ - f₂) g l` / `is_o (f₁ - f₂) g l` treated as a binary relation -/

theorem is_O_with.symm {α : Type u_1} {F : Type u_4} {E' : Type u_6} [has_norm F] [normed_group E']
    {c : ℝ} {g : α → F} {l : filter α} {f₁ : α → E'} {f₂ : α → E'}
    (h : is_O_with c (fun (x : α) => f₁ x - f₂ x) g l) :
    is_O_with c (fun (x : α) => f₂ x - f₁ x) g l :=
  is_O_with.congr_left (fun (x : α) => neg_sub (f₁ x) (f₂ x)) (is_O_with.neg_left h)

theorem is_O_with_comm {α : Type u_1} {F : Type u_4} {E' : Type u_6} [has_norm F] [normed_group E']
    {c : ℝ} {g : α → F} {l : filter α} {f₁ : α → E'} {f₂ : α → E'} :
    is_O_with c (fun (x : α) => f₁ x - f₂ x) g l ↔ is_O_with c (fun (x : α) => f₂ x - f₁ x) g l :=
  { mp := is_O_with.symm, mpr := is_O_with.symm }

theorem is_O.symm {α : Type u_1} {F : Type u_4} {E' : Type u_6} [has_norm F] [normed_group E']
    {g : α → F} {l : filter α} {f₁ : α → E'} {f₂ : α → E'}
    (h : is_O (fun (x : α) => f₁ x - f₂ x) g l) : is_O (fun (x : α) => f₂ x - f₁ x) g l :=
  is_O.congr_left (fun (x : α) => neg_sub (f₁ x) (f₂ x)) (is_O.neg_left h)

theorem is_O_comm {α : Type u_1} {F : Type u_4} {E' : Type u_6} [has_norm F] [normed_group E']
    {g : α → F} {l : filter α} {f₁ : α → E'} {f₂ : α → E'} :
    is_O (fun (x : α) => f₁ x - f₂ x) g l ↔ is_O (fun (x : α) => f₂ x - f₁ x) g l :=
  { mp := is_O.symm, mpr := is_O.symm }

theorem is_o.symm {α : Type u_1} {F : Type u_4} {E' : Type u_6} [has_norm F] [normed_group E']
    {g : α → F} {l : filter α} {f₁ : α → E'} {f₂ : α → E'}
    (h : is_o (fun (x : α) => f₁ x - f₂ x) g l) : is_o (fun (x : α) => f₂ x - f₁ x) g l :=
  sorry

theorem is_o_comm {α : Type u_1} {F : Type u_4} {E' : Type u_6} [has_norm F] [normed_group E']
    {g : α → F} {l : filter α} {f₁ : α → E'} {f₂ : α → E'} :
    is_o (fun (x : α) => f₁ x - f₂ x) g l ↔ is_o (fun (x : α) => f₂ x - f₁ x) g l :=
  { mp := is_o.symm, mpr := is_o.symm }

theorem is_O_with.triangle {α : Type u_1} {F : Type u_4} {E' : Type u_6} [has_norm F]
    [normed_group E'] {c : ℝ} {c' : ℝ} {g : α → F} {l : filter α} {f₁ : α → E'} {f₂ : α → E'}
    {f₃ : α → E'} (h₁ : is_O_with c (fun (x : α) => f₁ x - f₂ x) g l)
    (h₂ : is_O_with c' (fun (x : α) => f₂ x - f₃ x) g l) :
    is_O_with (c + c') (fun (x : α) => f₁ x - f₃ x) g l :=
  is_O_with.congr_left (fun (x : α) => sub_add_sub_cancel (f₁ x) (f₂ x) (f₃ x))
    (is_O_with.add h₁ h₂)

theorem is_O.triangle {α : Type u_1} {F : Type u_4} {E' : Type u_6} [has_norm F] [normed_group E']
    {g : α → F} {l : filter α} {f₁ : α → E'} {f₂ : α → E'} {f₃ : α → E'}
    (h₁ : is_O (fun (x : α) => f₁ x - f₂ x) g l) (h₂ : is_O (fun (x : α) => f₂ x - f₃ x) g l) :
    is_O (fun (x : α) => f₁ x - f₃ x) g l :=
  is_O.congr_left (fun (x : α) => sub_add_sub_cancel (f₁ x) (f₂ x) (f₃ x)) (is_O.add h₁ h₂)

theorem is_o.triangle {α : Type u_1} {F : Type u_4} {E' : Type u_6} [has_norm F] [normed_group E']
    {g : α → F} {l : filter α} {f₁ : α → E'} {f₂ : α → E'} {f₃ : α → E'}
    (h₁ : is_o (fun (x : α) => f₁ x - f₂ x) g l) (h₂ : is_o (fun (x : α) => f₂ x - f₃ x) g l) :
    is_o (fun (x : α) => f₁ x - f₃ x) g l :=
  is_o.congr_left (fun (x : α) => sub_add_sub_cancel (f₁ x) (f₂ x) (f₃ x)) (is_o.add h₁ h₂)

theorem is_O.congr_of_sub {α : Type u_1} {F : Type u_4} {E' : Type u_6} [has_norm F]
    [normed_group E'] {g : α → F} {l : filter α} {f₁ : α → E'} {f₂ : α → E'}
    (h : is_O (fun (x : α) => f₁ x - f₂ x) g l) : is_O f₁ g l ↔ is_O f₂ g l :=
  { mp :=
      fun (h' : is_O f₁ g l) =>
        is_O.congr_left (fun (x : α) => sub_sub_cancel (f₁ x) (f₂ x)) (is_O.sub h' h),
    mpr :=
      fun (h' : is_O f₂ g l) =>
        is_O.congr_left (fun (x : α) => sub_add_cancel (f₁ x) (f₂ x)) (is_O.add h h') }

theorem is_o.congr_of_sub {α : Type u_1} {F : Type u_4} {E' : Type u_6} [has_norm F]
    [normed_group E'] {g : α → F} {l : filter α} {f₁ : α → E'} {f₂ : α → E'}
    (h : is_o (fun (x : α) => f₁ x - f₂ x) g l) : is_o f₁ g l ↔ is_o f₂ g l :=
  { mp :=
      fun (h' : is_o f₁ g l) =>
        is_o.congr_left (fun (x : α) => sub_sub_cancel (f₁ x) (f₂ x)) (is_o.sub h' h),
    mpr :=
      fun (h' : is_o f₂ g l) =>
        is_o.congr_left (fun (x : α) => sub_add_cancel (f₁ x) (f₂ x)) (is_o.add h h') }

/-! ### Zero, one, and other constants -/

theorem is_o_zero {α : Type u_1} {E' : Type u_6} {F' : Type u_7} [normed_group E'] [normed_group F']
    (g' : α → F') (l : filter α) : is_o (fun (x : α) => 0) g' l :=
  sorry

theorem is_O_with_zero {α : Type u_1} {E' : Type u_6} {F' : Type u_7} [normed_group E']
    [normed_group F'] {c : ℝ} (g' : α → F') (l : filter α) (hc : 0 ≤ c) :
    is_O_with c (fun (x : α) => 0) g' l :=
  sorry

theorem is_O_with_zero' {α : Type u_1} {F : Type u_4} {E' : Type u_6} [has_norm F] [normed_group E']
    (g : α → F) (l : filter α) : is_O_with 0 (fun (x : α) => 0) g l :=
  sorry

theorem is_O_zero {α : Type u_1} {F : Type u_4} {E' : Type u_6} [has_norm F] [normed_group E']
    (g : α → F) (l : filter α) : is_O (fun (x : α) => 0) g l :=
  Exists.intro 0 (is_O_with_zero' g l)

theorem is_O_refl_left {α : Type u_1} {E' : Type u_6} {F' : Type u_7} [normed_group E']
    [normed_group F'] {f' : α → E'} (g' : α → F') (l : filter α) :
    is_O (fun (x : α) => f' x - f' x) g' l :=
  is_O.congr_left (fun (x : α) => Eq.symm (sub_self (f' x))) (is_O_zero g' l)

theorem is_o_refl_left {α : Type u_1} {E' : Type u_6} {F' : Type u_7} [normed_group E']
    [normed_group F'] {f' : α → E'} (g' : α → F') (l : filter α) :
    is_o (fun (x : α) => f' x - f' x) g' l :=
  is_o.congr_left (fun (x : α) => Eq.symm (sub_self (f' x))) (is_o_zero g' l)

@[simp] theorem is_O_with_zero_right_iff {α : Type u_1} {E' : Type u_6} {F' : Type u_7}
    [normed_group E'] [normed_group F'] {c : ℝ} {f' : α → E'} {l : filter α} :
    is_O_with c f' (fun (x : α) => 0) l ↔ filter.eventually (fun (x : α) => f' x = 0) l :=
  sorry

@[simp] theorem is_O_zero_right_iff {α : Type u_1} {E' : Type u_6} {F' : Type u_7} [normed_group E']
    [normed_group F'] {f' : α → E'} {l : filter α} :
    is_O f' (fun (x : α) => 0) l ↔ filter.eventually (fun (x : α) => f' x = 0) l :=
  sorry

@[simp] theorem is_o_zero_right_iff {α : Type u_1} {E' : Type u_6} {F' : Type u_7} [normed_group E']
    [normed_group F'] {f' : α → E'} {l : filter α} :
    is_o f' (fun (x : α) => 0) l ↔ filter.eventually (fun (x : α) => f' x = 0) l :=
  { mp := fun (h : is_o f' (fun (x : α) => 0) l) => iff.mp is_O_zero_right_iff (is_o.is_O h),
    mpr :=
      fun (h : filter.eventually (fun (x : α) => f' x = 0) l) (c : ℝ) (hc : 0 < c) =>
        iff.mpr is_O_with_zero_right_iff h }

theorem is_O_with_const_const {α : Type u_1} {E : Type u_3} {F' : Type u_7} [has_norm E]
    [normed_group F'] (c : E) {c' : F'} (hc' : c' ≠ 0) (l : filter α) :
    is_O_with (norm c / norm c') (fun (x : α) => c) (fun (x : α) => c') l :=
  sorry

theorem is_O_const_const {α : Type u_1} {E : Type u_3} {F' : Type u_7} [has_norm E]
    [normed_group F'] (c : E) {c' : F'} (hc' : c' ≠ 0) (l : filter α) :
    is_O (fun (x : α) => c) (fun (x : α) => c') l :=
  is_O_with.is_O (is_O_with_const_const c hc' l)

@[simp] theorem is_O_with_top {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E] [has_norm F]
    {c : ℝ} {f : α → E} {g : α → F} : is_O_with c f g ⊤ ↔ ∀ (x : α), norm (f x) ≤ c * norm (g x) :=
  iff.rfl

@[simp] theorem is_O_top {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E] [has_norm F]
    {f : α → E} {g : α → F} : is_O f g ⊤ ↔ ∃ (C : ℝ), ∀ (x : α), norm (f x) ≤ C * norm (g x) :=
  iff.rfl

@[simp] theorem is_o_top {α : Type u_1} {E' : Type u_6} {F' : Type u_7} [normed_group E']
    [normed_group F'] {f' : α → E'} {g' : α → F'} : is_o f' g' ⊤ ↔ ∀ (x : α), f' x = 0 :=
  sorry

@[simp] theorem is_O_with_principal {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E]
    [has_norm F] {c : ℝ} {f : α → E} {g : α → F} {s : set α} :
    is_O_with c f g (filter.principal s) ↔ ∀ (x : α), x ∈ s → norm (f x) ≤ c * norm (g x) :=
  iff.rfl

theorem is_O_principal {α : Type u_1} {E : Type u_3} {F : Type u_4} [has_norm E] [has_norm F]
    {f : α → E} {g : α → F} {s : set α} :
    is_O f g (filter.principal s) ↔ ∃ (c : ℝ), ∀ (x : α), x ∈ s → norm (f x) ≤ c * norm (g x) :=
  iff.rfl

theorem is_O_with_const_one {α : Type u_1} {E : Type u_3} {𝕜 : Type u_11} [has_norm E]
    [normed_field 𝕜] (c : E) (l : filter α) :
    is_O_with (norm c) (fun (x : α) => c) (fun (x : α) => 1) l :=
  sorry

theorem is_O_const_one {α : Type u_1} {E : Type u_3} {𝕜 : Type u_11} [has_norm E] [normed_field 𝕜]
    (c : E) (l : filter α) : is_O (fun (x : α) => c) (fun (x : α) => 1) l :=
  is_O_with.is_O (is_O_with_const_one c l)

theorem is_o_const_iff_is_o_one {α : Type u_1} {E : Type u_3} {F' : Type u_7} (𝕜 : Type u_11)
    [has_norm E] [normed_group F'] [normed_field 𝕜] {f : α → E} {l : filter α} {c : F'}
    (hc : c ≠ 0) : is_o f (fun (x : α) => c) l ↔ is_o f (fun (x : α) => 1) l :=
  { mp := fun (h : is_o f (fun (x : α) => c) l) => is_o.trans_is_O h (is_O_const_one c l),
    mpr := fun (h : is_o f (fun (x : α) => 1) l) => is_o.trans_is_O h (is_O_const_const 1 hc l) }

theorem is_o_const_iff {α : Type u_1} {E' : Type u_6} {F' : Type u_7} [normed_group E']
    [normed_group F'] {f' : α → E'} {l : filter α} {c : F'} (hc : c ≠ 0) :
    is_o f' (fun (x : α) => c) l ↔ filter.tendsto f' l (nhds 0) :=
  sorry

theorem is_o_id_const {E' : Type u_6} {F' : Type u_7} [normed_group E'] [normed_group F'] {c : F'}
    (hc : c ≠ 0) : is_o (fun (x : E') => x) (fun (x : E') => c) (nhds 0) :=
  iff.mpr (is_o_const_iff hc) (continuous.tendsto continuous_id 0)

theorem is_O_const_of_tendsto {α : Type u_1} {E' : Type u_6} {F' : Type u_7} [normed_group E']
    [normed_group F'] {f' : α → E'} {l : filter α} {y : E'} (h : filter.tendsto f' l (nhds y))
    {c : F'} (hc : c ≠ 0) : is_O f' (fun (x : α) => c) l :=
  sorry

theorem is_o_one_iff {α : Type u_1} {E' : Type u_6} (𝕜 : Type u_11) [normed_group E']
    [normed_field 𝕜] {f' : α → E'} {l : filter α} :
    is_o f' (fun (x : α) => 1) l ↔ filter.tendsto f' l (nhds 0) :=
  is_o_const_iff one_ne_zero

theorem is_O_one_of_tendsto {α : Type u_1} {E' : Type u_6} (𝕜 : Type u_11) [normed_group E']
    [normed_field 𝕜] {f' : α → E'} {l : filter α} {y : E'} (h : filter.tendsto f' l (nhds y)) :
    is_O f' (fun (x : α) => 1) l :=
  is_O_const_of_tendsto h one_ne_zero

theorem is_O.trans_tendsto_nhds {α : Type u_1} {E : Type u_3} {F' : Type u_7} (𝕜 : Type u_11)
    [has_norm E] [normed_group F'] [normed_field 𝕜] {f : α → E} {g' : α → F'} {l : filter α}
    (hfg : is_O f g' l) {y : F'} (hg : filter.tendsto g' l (nhds y)) :
    is_O f (fun (x : α) => 1) l :=
  is_O.trans hfg (is_O_one_of_tendsto 𝕜 hg)

theorem is_O.trans_tendsto {α : Type u_1} {E' : Type u_6} {F' : Type u_7} [normed_group E']
    [normed_group F'] {f' : α → E'} {g' : α → F'} {l : filter α} (hfg : is_O f' g' l)
    (hg : filter.tendsto g' l (nhds 0)) : filter.tendsto f' l (nhds 0) :=
  iff.mp (is_o_one_iff ℝ) (is_O.trans_is_o hfg (iff.mpr (is_o_one_iff ℝ) hg))

theorem is_o.trans_tendsto {α : Type u_1} {E' : Type u_6} {F' : Type u_7} [normed_group E']
    [normed_group F'] {f' : α → E'} {g' : α → F'} {l : filter α} (hfg : is_o f' g' l)
    (hg : filter.tendsto g' l (nhds 0)) : filter.tendsto f' l (nhds 0) :=
  is_O.trans_tendsto (is_o.is_O hfg) hg

/-! ### Multiplication by a constant -/

theorem is_O_with_const_mul_self {α : Type u_1} {R : Type u_9} [normed_ring R] (c : R) (f : α → R)
    (l : filter α) : is_O_with (norm c) (fun (x : α) => c * f x) f l :=
  is_O_with_of_le' l fun (x : α) => norm_mul_le c (f x)

theorem is_O_const_mul_self {α : Type u_1} {R : Type u_9} [normed_ring R] (c : R) (f : α → R)
    (l : filter α) : is_O (fun (x : α) => c * f x) f l :=
  is_O_with.is_O (is_O_with_const_mul_self c f l)

theorem is_O_with.const_mul_left {α : Type u_1} {F : Type u_4} {R : Type u_9} [has_norm F]
    [normed_ring R] {c : ℝ} {g : α → F} {l : filter α} {f : α → R} (h : is_O_with c f g l)
    (c' : R) : is_O_with (norm c' * c) (fun (x : α) => c' * f x) g l :=
  is_O_with.trans (is_O_with_const_mul_self c' f l) h (norm_nonneg c')

theorem is_O.const_mul_left {α : Type u_1} {F : Type u_4} {R : Type u_9} [has_norm F]
    [normed_ring R] {g : α → F} {l : filter α} {f : α → R} (h : is_O f g l) (c' : R) :
    is_O (fun (x : α) => c' * f x) g l :=
  sorry

theorem is_O_with_self_const_mul' {α : Type u_1} {R : Type u_9} [normed_ring R] (u : units R)
    (f : α → R) (l : filter α) : is_O_with (norm ↑(u⁻¹)) f (fun (x : α) => ↑u * f x) l :=
  is_O_with.congr_left (fun (x : α) => units.inv_mul_cancel_left u (f x))
    (is_O_with_const_mul_self (↑(u⁻¹)) (fun (x : α) => ↑u * f x) l)

theorem is_O_with_self_const_mul {α : Type u_1} {𝕜 : Type u_11} [normed_field 𝕜] (c : 𝕜)
    (hc : c ≠ 0) (f : α → 𝕜) (l : filter α) : is_O_with (norm c⁻¹) f (fun (x : α) => c * f x) l :=
  is_O_with.congr_const (normed_field.norm_inv c) (is_O_with_self_const_mul' (units.mk0 c hc) f l)

theorem is_O_self_const_mul' {α : Type u_1} {R : Type u_9} [normed_ring R] {c : R} (hc : is_unit c)
    (f : α → R) (l : filter α) : is_O f (fun (x : α) => c * f x) l :=
  sorry

theorem is_O_self_const_mul {α : Type u_1} {𝕜 : Type u_11} [normed_field 𝕜] (c : 𝕜) (hc : c ≠ 0)
    (f : α → 𝕜) (l : filter α) : is_O f (fun (x : α) => c * f x) l :=
  is_O_self_const_mul' (is_unit.mk0 c hc) f l

theorem is_O_const_mul_left_iff' {α : Type u_1} {F : Type u_4} {R : Type u_9} [has_norm F]
    [normed_ring R] {g : α → F} {l : filter α} {f : α → R} {c : R} (hc : is_unit c) :
    is_O (fun (x : α) => c * f x) g l ↔ is_O f g l :=
  { mp := is_O.trans (is_O_self_const_mul' hc f l),
    mpr := fun (h : is_O f g l) => is_O.const_mul_left h c }

theorem is_O_const_mul_left_iff {α : Type u_1} {F : Type u_4} {𝕜 : Type u_11} [has_norm F]
    [normed_field 𝕜] {g : α → F} {l : filter α} {f : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) :
    is_O (fun (x : α) => c * f x) g l ↔ is_O f g l :=
  is_O_const_mul_left_iff' (is_unit.mk0 c hc)

theorem is_o.const_mul_left {α : Type u_1} {F : Type u_4} {R : Type u_9} [has_norm F]
    [normed_ring R] {g : α → F} {l : filter α} {f : α → R} (h : is_o f g l) (c : R) :
    is_o (fun (x : α) => c * f x) g l :=
  is_O.trans_is_o (is_O_const_mul_self c f l) h

theorem is_o_const_mul_left_iff' {α : Type u_1} {F : Type u_4} {R : Type u_9} [has_norm F]
    [normed_ring R] {g : α → F} {l : filter α} {f : α → R} {c : R} (hc : is_unit c) :
    is_o (fun (x : α) => c * f x) g l ↔ is_o f g l :=
  { mp := is_O.trans_is_o (is_O_self_const_mul' hc f l),
    mpr := fun (h : is_o f g l) => is_o.const_mul_left h c }

theorem is_o_const_mul_left_iff {α : Type u_1} {F : Type u_4} {𝕜 : Type u_11} [has_norm F]
    [normed_field 𝕜] {g : α → F} {l : filter α} {f : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) :
    is_o (fun (x : α) => c * f x) g l ↔ is_o f g l :=
  is_o_const_mul_left_iff' (is_unit.mk0 c hc)

theorem is_O_with.of_const_mul_right {α : Type u_1} {E : Type u_3} {R : Type u_9} [has_norm E]
    [normed_ring R] {c' : ℝ} {f : α → E} {l : filter α} {g : α → R} {c : R} (hc' : 0 ≤ c')
    (h : is_O_with c' f (fun (x : α) => c * g x) l) : is_O_with (c' * norm c) f g l :=
  is_O_with.trans h (is_O_with_const_mul_self c g l) hc'

theorem is_O.of_const_mul_right {α : Type u_1} {E : Type u_3} {R : Type u_9} [has_norm E]
    [normed_ring R] {f : α → E} {l : filter α} {g : α → R} {c : R}
    (h : is_O f (fun (x : α) => c * g x) l) : is_O f g l :=
  sorry

theorem is_O_with.const_mul_right' {α : Type u_1} {E : Type u_3} {R : Type u_9} [has_norm E]
    [normed_ring R] {f : α → E} {l : filter α} {g : α → R} {u : units R} {c' : ℝ} (hc' : 0 ≤ c')
    (h : is_O_with c' f g l) : is_O_with (c' * norm ↑(u⁻¹)) f (fun (x : α) => ↑u * g x) l :=
  is_O_with.trans h (is_O_with_self_const_mul' u g l) hc'

theorem is_O_with.const_mul_right {α : Type u_1} {E : Type u_3} {𝕜 : Type u_11} [has_norm E]
    [normed_field 𝕜] {f : α → E} {l : filter α} {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) {c' : ℝ}
    (hc' : 0 ≤ c') (h : is_O_with c' f g l) :
    is_O_with (c' * (norm c⁻¹)) f (fun (x : α) => c * g x) l :=
  is_O_with.trans h (is_O_with_self_const_mul c hc g l) hc'

theorem is_O.const_mul_right' {α : Type u_1} {E : Type u_3} {R : Type u_9} [has_norm E]
    [normed_ring R] {f : α → E} {l : filter α} {g : α → R} {c : R} (hc : is_unit c)
    (h : is_O f g l) : is_O f (fun (x : α) => c * g x) l :=
  is_O.trans h (is_O_self_const_mul' hc g l)

theorem is_O.const_mul_right {α : Type u_1} {E : Type u_3} {𝕜 : Type u_11} [has_norm E]
    [normed_field 𝕜] {f : α → E} {l : filter α} {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) (h : is_O f g l) :
    is_O f (fun (x : α) => c * g x) l :=
  is_O.const_mul_right' (is_unit.mk0 c hc) h

theorem is_O_const_mul_right_iff' {α : Type u_1} {E : Type u_3} {R : Type u_9} [has_norm E]
    [normed_ring R] {f : α → E} {l : filter α} {g : α → R} {c : R} (hc : is_unit c) :
    is_O f (fun (x : α) => c * g x) l ↔ is_O f g l :=
  { mp := fun (h : is_O f (fun (x : α) => c * g x) l) => is_O.of_const_mul_right h,
    mpr := fun (h : is_O f g l) => is_O.const_mul_right' hc h }

theorem is_O_const_mul_right_iff {α : Type u_1} {E : Type u_3} {𝕜 : Type u_11} [has_norm E]
    [normed_field 𝕜] {f : α → E} {l : filter α} {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) :
    is_O f (fun (x : α) => c * g x) l ↔ is_O f g l :=
  is_O_const_mul_right_iff' (is_unit.mk0 c hc)

theorem is_o.of_const_mul_right {α : Type u_1} {E : Type u_3} {R : Type u_9} [has_norm E]
    [normed_ring R] {f : α → E} {l : filter α} {g : α → R} {c : R}
    (h : is_o f (fun (x : α) => c * g x) l) : is_o f g l :=
  is_o.trans_is_O h (is_O_const_mul_self c g l)

theorem is_o.const_mul_right' {α : Type u_1} {E : Type u_3} {R : Type u_9} [has_norm E]
    [normed_ring R] {f : α → E} {l : filter α} {g : α → R} {c : R} (hc : is_unit c)
    (h : is_o f g l) : is_o f (fun (x : α) => c * g x) l :=
  is_o.trans_is_O h (is_O_self_const_mul' hc g l)

theorem is_o.const_mul_right {α : Type u_1} {E : Type u_3} {𝕜 : Type u_11} [has_norm E]
    [normed_field 𝕜] {f : α → E} {l : filter α} {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) (h : is_o f g l) :
    is_o f (fun (x : α) => c * g x) l :=
  is_o.const_mul_right' (is_unit.mk0 c hc) h

theorem is_o_const_mul_right_iff' {α : Type u_1} {E : Type u_3} {R : Type u_9} [has_norm E]
    [normed_ring R] {f : α → E} {l : filter α} {g : α → R} {c : R} (hc : is_unit c) :
    is_o f (fun (x : α) => c * g x) l ↔ is_o f g l :=
  { mp := fun (h : is_o f (fun (x : α) => c * g x) l) => is_o.of_const_mul_right h,
    mpr := fun (h : is_o f g l) => is_o.const_mul_right' hc h }

theorem is_o_const_mul_right_iff {α : Type u_1} {E : Type u_3} {𝕜 : Type u_11} [has_norm E]
    [normed_field 𝕜] {f : α → E} {l : filter α} {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) :
    is_o f (fun (x : α) => c * g x) l ↔ is_o f g l :=
  is_o_const_mul_right_iff' (is_unit.mk0 c hc)

/-! ### Multiplication -/

theorem is_O_with.mul {α : Type u_1} {R : Type u_9} {𝕜 : Type u_11} [normed_ring R] [normed_field 𝕜]
    {l : filter α} {f₁ : α → R} {f₂ : α → R} {g₁ : α → 𝕜} {g₂ : α → 𝕜} {c₁ : ℝ} {c₂ : ℝ}
    (h₁ : is_O_with c₁ f₁ g₁ l) (h₂ : is_O_with c₂ f₂ g₂ l) :
    is_O_with (c₁ * c₂) (fun (x : α) => f₁ x * f₂ x) (fun (x : α) => g₁ x * g₂ x) l :=
  sorry

theorem is_O.mul {α : Type u_1} {R : Type u_9} {𝕜 : Type u_11} [normed_ring R] [normed_field 𝕜]
    {l : filter α} {f₁ : α → R} {f₂ : α → R} {g₁ : α → 𝕜} {g₂ : α → 𝕜} (h₁ : is_O f₁ g₁ l)
    (h₂ : is_O f₂ g₂ l) : is_O (fun (x : α) => f₁ x * f₂ x) (fun (x : α) => g₁ x * g₂ x) l :=
  sorry

theorem is_O.mul_is_o {α : Type u_1} {R : Type u_9} {𝕜 : Type u_11} [normed_ring R] [normed_field 𝕜]
    {l : filter α} {f₁ : α → R} {f₂ : α → R} {g₁ : α → 𝕜} {g₂ : α → 𝕜} (h₁ : is_O f₁ g₁ l)
    (h₂ : is_o f₂ g₂ l) : is_o (fun (x : α) => f₁ x * f₂ x) (fun (x : α) => g₁ x * g₂ x) l :=
  sorry

theorem is_o.mul_is_O {α : Type u_1} {R : Type u_9} {𝕜 : Type u_11} [normed_ring R] [normed_field 𝕜]
    {l : filter α} {f₁ : α → R} {f₂ : α → R} {g₁ : α → 𝕜} {g₂ : α → 𝕜} (h₁ : is_o f₁ g₁ l)
    (h₂ : is_O f₂ g₂ l) : is_o (fun (x : α) => f₁ x * f₂ x) (fun (x : α) => g₁ x * g₂ x) l :=
  sorry

theorem is_o.mul {α : Type u_1} {R : Type u_9} {𝕜 : Type u_11} [normed_ring R] [normed_field 𝕜]
    {l : filter α} {f₁ : α → R} {f₂ : α → R} {g₁ : α → 𝕜} {g₂ : α → 𝕜} (h₁ : is_o f₁ g₁ l)
    (h₂ : is_o f₂ g₂ l) : is_o (fun (x : α) => f₁ x * f₂ x) (fun (x : α) => g₁ x * g₂ x) l :=
  is_o.mul_is_O h₁ (is_o.is_O h₂)

theorem is_O_with.pow' {α : Type u_1} {R : Type u_9} {𝕜 : Type u_11} [normed_ring R]
    [normed_field 𝕜] {c : ℝ} {l : filter α} {f : α → R} {g : α → 𝕜} (h : is_O_with c f g l)
    (n : ℕ) :
    is_O_with (nat.cases_on n (norm 1) fun (n : ℕ) => c ^ (n + 1)) (fun (x : α) => f x ^ n)
        (fun (x : α) => g x ^ n) l :=
  sorry

theorem is_O_with.pow {α : Type u_1} {R : Type u_9} {𝕜 : Type u_11} [normed_ring R] [normed_field 𝕜]
    {c : ℝ} {l : filter α} [norm_one_class R] {f : α → R} {g : α → 𝕜} (h : is_O_with c f g l)
    (n : ℕ) : is_O_with (c ^ n) (fun (x : α) => f x ^ n) (fun (x : α) => g x ^ n) l :=
  sorry

theorem is_O.pow {α : Type u_1} {R : Type u_9} {𝕜 : Type u_11} [normed_ring R] [normed_field 𝕜]
    {l : filter α} {f : α → R} {g : α → 𝕜} (h : is_O f g l) (n : ℕ) :
    is_O (fun (x : α) => f x ^ n) (fun (x : α) => g x ^ n) l :=
  sorry

theorem is_o.pow {α : Type u_1} {R : Type u_9} {𝕜 : Type u_11} [normed_ring R] [normed_field 𝕜]
    {l : filter α} {f : α → R} {g : α → 𝕜} (h : is_o f g l) {n : ℕ} (hn : 0 < n) :
    is_o (fun (x : α) => f x ^ n) (fun (x : α) => g x ^ n) l :=
  sorry

/-! ### Scalar multiplication -/

theorem is_O_with.const_smul_left {α : Type u_1} {F : Type u_4} {E' : Type u_6} {𝕜 : Type u_11}
    [has_norm F] [normed_group E'] [normed_field 𝕜] {c : ℝ} {g : α → F} {f' : α → E'} {l : filter α}
    [normed_space 𝕜 E'] (h : is_O_with c f' g l) (c' : 𝕜) :
    is_O_with (norm c' * c) (fun (x : α) => c' • f' x) g l :=
  sorry

theorem is_O_const_smul_left_iff {α : Type u_1} {F : Type u_4} {E' : Type u_6} {𝕜 : Type u_11}
    [has_norm F] [normed_group E'] [normed_field 𝕜] {g : α → F} {f' : α → E'} {l : filter α}
    [normed_space 𝕜 E'] {c : 𝕜} (hc : c ≠ 0) : is_O (fun (x : α) => c • f' x) g l ↔ is_O f' g l :=
  sorry

theorem is_o_const_smul_left {α : Type u_1} {F : Type u_4} {E' : Type u_6} {𝕜 : Type u_11}
    [has_norm F] [normed_group E'] [normed_field 𝕜] {g : α → F} {f' : α → E'} {l : filter α}
    [normed_space 𝕜 E'] (h : is_o f' g l) (c : 𝕜) : is_o (fun (x : α) => c • f' x) g l :=
  is_o.of_norm_left
    (is_o.congr_left (fun (x : α) => Eq.symm (norm_smul c (f' x)))
      (is_o.const_mul_left (is_o.norm_left h) (norm c)))

theorem is_o_const_smul_left_iff {α : Type u_1} {F : Type u_4} {E' : Type u_6} {𝕜 : Type u_11}
    [has_norm F] [normed_group E'] [normed_field 𝕜] {g : α → F} {f' : α → E'} {l : filter α}
    [normed_space 𝕜 E'] {c : 𝕜} (hc : c ≠ 0) : is_o (fun (x : α) => c • f' x) g l ↔ is_o f' g l :=
  sorry

theorem is_O_const_smul_right {α : Type u_1} {E : Type u_3} {E' : Type u_6} {𝕜 : Type u_11}
    [has_norm E] [normed_group E'] [normed_field 𝕜] {f : α → E} {f' : α → E'} {l : filter α}
    [normed_space 𝕜 E'] {c : 𝕜} (hc : c ≠ 0) : is_O f (fun (x : α) => c • f' x) l ↔ is_O f f' l :=
  sorry

theorem is_o_const_smul_right {α : Type u_1} {E : Type u_3} {E' : Type u_6} {𝕜 : Type u_11}
    [has_norm E] [normed_group E'] [normed_field 𝕜] {f : α → E} {f' : α → E'} {l : filter α}
    [normed_space 𝕜 E'] {c : 𝕜} (hc : c ≠ 0) : is_o f (fun (x : α) => c • f' x) l ↔ is_o f f' l :=
  sorry

theorem is_O_with.smul {α : Type u_1} {E' : Type u_6} {F' : Type u_7} {𝕜 : Type u_11}
    [normed_group E'] [normed_group F'] [normed_field 𝕜] {c : ℝ} {c' : ℝ} {f' : α → E'}
    {g' : α → F'} {l : filter α} [normed_space 𝕜 E'] [normed_space 𝕜 F'] {k₁ : α → 𝕜} {k₂ : α → 𝕜}
    (h₁ : is_O_with c k₁ k₂ l) (h₂ : is_O_with c' f' g' l) :
    is_O_with (c * c') (fun (x : α) => k₁ x • f' x) (fun (x : α) => k₂ x • g' x) l :=
  sorry

theorem is_O.smul {α : Type u_1} {E' : Type u_6} {F' : Type u_7} {𝕜 : Type u_11} [normed_group E']
    [normed_group F'] [normed_field 𝕜] {f' : α → E'} {g' : α → F'} {l : filter α}
    [normed_space 𝕜 E'] [normed_space 𝕜 F'] {k₁ : α → 𝕜} {k₂ : α → 𝕜} (h₁ : is_O k₁ k₂ l)
    (h₂ : is_O f' g' l) : is_O (fun (x : α) => k₁ x • f' x) (fun (x : α) => k₂ x • g' x) l :=
  sorry

theorem is_O.smul_is_o {α : Type u_1} {E' : Type u_6} {F' : Type u_7} {𝕜 : Type u_11}
    [normed_group E'] [normed_group F'] [normed_field 𝕜] {f' : α → E'} {g' : α → F'} {l : filter α}
    [normed_space 𝕜 E'] [normed_space 𝕜 F'] {k₁ : α → 𝕜} {k₂ : α → 𝕜} (h₁ : is_O k₁ k₂ l)
    (h₂ : is_o f' g' l) : is_o (fun (x : α) => k₁ x • f' x) (fun (x : α) => k₂ x • g' x) l :=
  sorry

theorem is_o.smul_is_O {α : Type u_1} {E' : Type u_6} {F' : Type u_7} {𝕜 : Type u_11}
    [normed_group E'] [normed_group F'] [normed_field 𝕜] {f' : α → E'} {g' : α → F'} {l : filter α}
    [normed_space 𝕜 E'] [normed_space 𝕜 F'] {k₁ : α → 𝕜} {k₂ : α → 𝕜} (h₁ : is_o k₁ k₂ l)
    (h₂ : is_O f' g' l) : is_o (fun (x : α) => k₁ x • f' x) (fun (x : α) => k₂ x • g' x) l :=
  sorry

theorem is_o.smul {α : Type u_1} {E' : Type u_6} {F' : Type u_7} {𝕜 : Type u_11} [normed_group E']
    [normed_group F'] [normed_field 𝕜] {f' : α → E'} {g' : α → F'} {l : filter α}
    [normed_space 𝕜 E'] [normed_space 𝕜 F'] {k₁ : α → 𝕜} {k₂ : α → 𝕜} (h₁ : is_o k₁ k₂ l)
    (h₂ : is_o f' g' l) : is_o (fun (x : α) => k₁ x • f' x) (fun (x : α) => k₂ x • g' x) l :=
  sorry

/-! ### Sum -/

theorem is_O_with.sum {α : Type u_1} {F : Type u_4} {E' : Type u_6} [has_norm F] [normed_group E']
    {g : α → F} {l : filter α} {ι : Type u_13} {A : ι → α → E'} {C : ι → ℝ} {s : finset ι}
    (h : ∀ (i : ι), i ∈ s → is_O_with (C i) (A i) g l) :
    is_O_with (finset.sum s fun (i : ι) => C i) (fun (x : α) => finset.sum s fun (i : ι) => A i x) g
        l :=
  sorry

theorem is_O.sum {α : Type u_1} {F : Type u_4} {E' : Type u_6} [has_norm F] [normed_group E']
    {g : α → F} {l : filter α} {ι : Type u_13} {A : ι → α → E'} {s : finset ι}
    (h : ∀ (i : ι), i ∈ s → is_O (A i) g l) :
    is_O (fun (x : α) => finset.sum s fun (i : ι) => A i x) g l :=
  sorry

theorem is_o.sum {α : Type u_1} {E' : Type u_6} {F' : Type u_7} [normed_group E'] [normed_group F']
    {g' : α → F'} {l : filter α} {ι : Type u_13} {A : ι → α → E'} {s : finset ι}
    (h : ∀ (i : ι), i ∈ s → is_o (A i) g' l) :
    is_o (fun (x : α) => finset.sum s fun (i : ι) => A i x) g' l :=
  sorry

/-! ### Relation between `f = o(g)` and `f / g → 0` -/

theorem is_o.tendsto_0 {α : Type u_1} {𝕜 : Type u_11} [normed_field 𝕜] {f : α → 𝕜} {g : α → 𝕜}
    {l : filter α} (h : is_o f g l) : filter.tendsto (fun (x : α) => f x / g x) l (nhds 0) :=
  sorry

theorem is_o_iff_tendsto' {α : Type u_1} {𝕜 : Type u_11} [normed_field 𝕜] {f : α → 𝕜} {g : α → 𝕜}
    {l : filter α} (hgf : filter.eventually (fun (x : α) => g x = 0 → f x = 0) l) :
    is_o f g l ↔ filter.tendsto (fun (x : α) => f x / g x) l (nhds 0) :=
  sorry

theorem is_o_iff_tendsto {α : Type u_1} {𝕜 : Type u_11} [normed_field 𝕜] {f : α → 𝕜} {g : α → 𝕜}
    {l : filter α} (hgf : ∀ (x : α), g x = 0 → f x = 0) :
    is_o f g l ↔ filter.tendsto (fun (x : α) => f x / g x) l (nhds 0) :=
  { mp := fun (h : is_o f g l) => is_o.tendsto_0 h,
    mpr := iff.mpr (is_o_iff_tendsto' (filter.eventually_of_forall hgf)) }

theorem is_o_of_tendsto' {α : Type u_1} {𝕜 : Type u_11} [normed_field 𝕜] {f : α → 𝕜} {g : α → 𝕜}
    {l : filter α} (hgf : filter.eventually (fun (x : α) => g x = 0 → f x = 0) l) :
    filter.tendsto (fun (x : α) => f x / g x) l (nhds 0) → is_o f g l :=
  iff.mpr (is_o_iff_tendsto' hgf)

theorem is_o_of_tendsto {α : Type u_1} {𝕜 : Type u_11} [normed_field 𝕜] {f : α → 𝕜} {g : α → 𝕜}
    {l : filter α} (hgf : ∀ (x : α), g x = 0 → f x = 0) :
    filter.tendsto (fun (x : α) => f x / g x) l (nhds 0) → is_o f g l :=
  iff.mpr (is_o_iff_tendsto hgf)

/-!
### Eventually (u / v) * v = u

If `u` and `v` are linked by an `is_O_with` relation, then we
eventually have `(u / v) * v = u`, even if `v` vanishes.
-/

theorem is_O_with.eventually_mul_div_cancel {α : Type u_1} {𝕜 : Type u_11} [normed_field 𝕜] {c : ℝ}
    {l : filter α} {u : α → 𝕜} {v : α → 𝕜} (h : is_O_with c u v l) :
    filter.eventually_eq l (u / v * v) u :=
  sorry

/-- If `u = O(v)` along `l`, then `(u / v) * v = u` eventually at `l`. -/
theorem is_O.eventually_mul_div_cancel {α : Type u_1} {𝕜 : Type u_11} [normed_field 𝕜]
    {l : filter α} {u : α → 𝕜} {v : α → 𝕜} (h : is_O u v l) :
    filter.eventually_eq l (u / v * v) u :=
  sorry

/-- If `u = o(v)` along `l`, then `(u / v) * v = u` eventually at `l`. -/
theorem is_o.eventually_mul_div_cancel {α : Type u_1} {𝕜 : Type u_11} [normed_field 𝕜]
    {l : filter α} {u : α → 𝕜} {v : α → 𝕜} (h : is_o u v l) :
    filter.eventually_eq l (u / v * v) u :=
  is_O_with.eventually_mul_div_cancel (h zero_lt_one)

/-! ### Equivalent definitions of the form `∃ φ, u =ᶠ[l] φ * v` in a `normed_field`. -/

/-- If `∥φ∥` is eventually bounded by `c`, and `u =ᶠ[l] φ * v`, then we have `is_O_with c u v l`.
    This does not require any assumptions on `c`, which is why we keep this version along with
    `is_O_with_iff_exists_eq_mul`. -/
theorem is_O_with_of_eq_mul {α : Type u_1} {𝕜 : Type u_11} [normed_field 𝕜] {c : ℝ} {l : filter α}
    {u : α → 𝕜} {v : α → 𝕜} (φ : α → 𝕜) (hφ : filter.eventually (fun (x : α) => norm (φ x) ≤ c) l)
    (h : filter.eventually_eq l u (φ * v)) : is_O_with c u v l :=
  sorry

theorem is_O_with_iff_exists_eq_mul {α : Type u_1} {𝕜 : Type u_11} [normed_field 𝕜] {c : ℝ}
    {l : filter α} {u : α → 𝕜} {v : α → 𝕜} (hc : 0 ≤ c) :
    is_O_with c u v l ↔
        ∃ (φ : α → 𝕜),
          ∃ (hφ : filter.eventually (fun (x : α) => norm (φ x) ≤ c) l),
            filter.eventually_eq l u (φ * v) :=
  sorry

theorem is_O_with.exists_eq_mul {α : Type u_1} {𝕜 : Type u_11} [normed_field 𝕜] {c : ℝ}
    {l : filter α} {u : α → 𝕜} {v : α → 𝕜} (h : is_O_with c u v l) (hc : 0 ≤ c) :
    ∃ (φ : α → 𝕜),
        ∃ (hφ : filter.eventually (fun (x : α) => norm (φ x) ≤ c) l),
          filter.eventually_eq l u (φ * v) :=
  iff.mp (is_O_with_iff_exists_eq_mul hc) h

theorem is_O_iff_exists_eq_mul {α : Type u_1} {𝕜 : Type u_11} [normed_field 𝕜] {l : filter α}
    {u : α → 𝕜} {v : α → 𝕜} :
    is_O u v l ↔
        ∃ (φ : α → 𝕜),
          ∃ (hφ : filter.is_bounded_under LessEq l (norm ∘ φ)), filter.eventually_eq l u (φ * v) :=
  sorry

theorem is_O.exists_eq_mul {α : Type u_1} {𝕜 : Type u_11} [normed_field 𝕜] {l : filter α}
    {u : α → 𝕜} {v : α → 𝕜} :
    is_O u v l →
        ∃ (φ : α → 𝕜),
          ∃ (hφ : filter.is_bounded_under LessEq l (norm ∘ φ)), filter.eventually_eq l u (φ * v) :=
  iff.mp is_O_iff_exists_eq_mul

theorem is_o_iff_exists_eq_mul {α : Type u_1} {𝕜 : Type u_11} [normed_field 𝕜] {l : filter α}
    {u : α → 𝕜} {v : α → 𝕜} :
    is_o u v l ↔
        ∃ (φ : α → 𝕜), ∃ (hφ : filter.tendsto φ l (nhds 0)), filter.eventually_eq l u (φ * v) :=
  sorry

theorem is_o.exists_eq_mul {α : Type u_1} {𝕜 : Type u_11} [normed_field 𝕜] {l : filter α}
    {u : α → 𝕜} {v : α → 𝕜} :
    is_o u v l →
        ∃ (φ : α → 𝕜), ∃ (hφ : filter.tendsto φ l (nhds 0)), filter.eventually_eq l u (φ * v) :=
  iff.mp is_o_iff_exists_eq_mul

/-! ### Miscellanous lemmas -/

theorem is_o_pow_pow {𝕜 : Type u_11} [normed_field 𝕜] {m : ℕ} {n : ℕ} (h : m < n) :
    is_o (fun (x : 𝕜) => x ^ n) (fun (x : 𝕜) => x ^ m) (nhds 0) :=
  sorry

theorem is_o_norm_pow_norm_pow {E' : Type u_6} [normed_group E'] {m : ℕ} {n : ℕ} (h : m < n) :
    is_o (fun (x : E') => norm x ^ n) (fun (x : E') => norm x ^ m) (nhds 0) :=
  is_o.comp_tendsto (is_o_pow_pow h) tendsto_norm_zero

theorem is_o_pow_id {𝕜 : Type u_11} [normed_field 𝕜] {n : ℕ} (h : 1 < n) :
    is_o (fun (x : 𝕜) => x ^ n) (fun (x : 𝕜) => x) (nhds 0) :=
  sorry

theorem is_o_norm_pow_id {E' : Type u_6} [normed_group E'] {n : ℕ} (h : 1 < n) :
    is_o (fun (x : E') => norm x ^ n) (fun (x : E') => x) (nhds 0) :=
  sorry

theorem is_O_with.right_le_sub_of_lt_1 {α : Type u_1} {E' : Type u_6} [normed_group E'] {c : ℝ}
    {l : filter α} {f₁ : α → E'} {f₂ : α → E'} (h : is_O_with c f₁ f₂ l) (hc : c < 1) :
    is_O_with (1 / (1 - c)) f₂ (fun (x : α) => f₂ x - f₁ x) l :=
  sorry

theorem is_O_with.right_le_add_of_lt_1 {α : Type u_1} {E' : Type u_6} [normed_group E'] {c : ℝ}
    {l : filter α} {f₁ : α → E'} {f₂ : α → E'} (h : is_O_with c f₁ f₂ l) (hc : c < 1) :
    is_O_with (1 / (1 - c)) f₂ (fun (x : α) => f₁ x + f₂ x) l :=
  sorry

theorem is_o.right_is_O_sub {α : Type u_1} {E' : Type u_6} [normed_group E'] {l : filter α}
    {f₁ : α → E'} {f₂ : α → E'} (h : is_o f₁ f₂ l) : is_O f₂ (fun (x : α) => f₂ x - f₁ x) l :=
  is_O_with.is_O (is_O_with.right_le_sub_of_lt_1 (is_o.def' h one_half_pos) one_half_lt_one)

theorem is_o.right_is_O_add {α : Type u_1} {E' : Type u_6} [normed_group E'] {l : filter α}
    {f₁ : α → E'} {f₂ : α → E'} (h : is_o f₁ f₂ l) : is_O f₂ (fun (x : α) => f₁ x + f₂ x) l :=
  is_O_with.is_O (is_O_with.right_le_add_of_lt_1 (is_o.def' h one_half_pos) one_half_lt_one)

/-- If `f x = O(g x)` along `cofinite`, then there exists a positive constant `C` such that
`∥f x∥ ≤ C * ∥g x∥` whenever `g x ≠ 0`. -/
theorem bound_of_is_O_cofinite {α : Type u_1} {E : Type u_3} {F' : Type u_7} [has_norm E]
    [normed_group F'] {f : α → E} {g' : α → F'} (h : is_O f g' filter.cofinite) :
    ∃ (C : ℝ), ∃ (H : C > 0), ∀ {x : α}, g' x ≠ 0 → norm (f x) ≤ C * norm (g' x) :=
  sorry

theorem is_O_cofinite_iff {α : Type u_1} {E' : Type u_6} {F' : Type u_7} [normed_group E']
    [normed_group F'] {f' : α → E'} {g' : α → F'} (h : ∀ (x : α), g' x = 0 → f' x = 0) :
    is_O f' g' filter.cofinite ↔ ∃ (C : ℝ), ∀ (x : α), norm (f' x) ≤ C * norm (g' x) :=
  sorry

theorem bound_of_is_O_nat_at_top {E : Type u_3} {E' : Type u_6} [has_norm E] [normed_group E']
    {f : ℕ → E} {g' : ℕ → E'} (h : is_O f g' filter.at_top) :
    ∃ (C : ℝ), ∃ (H : C > 0), ∀ {x : ℕ}, g' x ≠ 0 → norm (f x) ≤ C * norm (g' x) :=
  sorry

theorem is_O_nat_at_top_iff {E' : Type u_6} {F' : Type u_7} [normed_group E'] [normed_group F']
    {f : ℕ → E'} {g : ℕ → F'} (h : ∀ (x : ℕ), g x = 0 → f x = 0) :
    is_O f g filter.at_top ↔ ∃ (C : ℝ), ∀ (x : ℕ), norm (f x) ≤ C * norm (g x) :=
  sorry

theorem is_O_one_nat_at_top_iff {E' : Type u_6} [normed_group E'] {f : ℕ → E'} :
    is_O f (fun (n : ℕ) => 1) filter.at_top ↔ ∃ (C : ℝ), ∀ (n : ℕ), norm (f n) ≤ C :=
  sorry

end asymptotics


theorem summable_of_is_O {ι : Type u_1} {E : Type u_2} [normed_group E] [complete_space E]
    {f : ι → E} (g : ι → ℝ) (hg : summable g) (h : asymptotics.is_O f g filter.cofinite) :
    summable f :=
  sorry

theorem summable_of_is_O_nat {E : Type u_1} [normed_group E] [complete_space E] {f : ℕ → E}
    (g : ℕ → ℝ) (hg : summable g) (h : asymptotics.is_O f g filter.at_top) : summable f :=
  summable_of_is_O g hg (Eq.symm nat.cofinite_eq_at_top ▸ h)

namespace local_homeomorph


/-- Transfer `is_O_with` over a `local_homeomorph`. -/
theorem is_O_with_congr {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    {E : Type u_3} [has_norm E] {F : Type u_4} [has_norm F] (e : local_homeomorph α β) {b : β}
    (hb : b ∈ local_equiv.target (to_local_equiv e)) {f : β → E} {g : β → F} {C : ℝ} :
    asymptotics.is_O_with C f g (nhds b) ↔
        asymptotics.is_O_with C (f ∘ ⇑e) (g ∘ ⇑e) (nhds (coe_fn (local_homeomorph.symm e) b)) :=
  sorry

/-- Transfer `is_O` over a `local_homeomorph`. -/
theorem is_O_congr {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    {E : Type u_3} [has_norm E] {F : Type u_4} [has_norm F] (e : local_homeomorph α β) {b : β}
    (hb : b ∈ local_equiv.target (to_local_equiv e)) {f : β → E} {g : β → F} :
    asymptotics.is_O f g (nhds b) ↔
        asymptotics.is_O (f ∘ ⇑e) (g ∘ ⇑e) (nhds (coe_fn (local_homeomorph.symm e) b)) :=
  exists_congr fun (C : ℝ) => is_O_with_congr e hb

/-- Transfer `is_o` over a `local_homeomorph`. -/
theorem is_o_congr {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    {E : Type u_3} [has_norm E] {F : Type u_4} [has_norm F] (e : local_homeomorph α β) {b : β}
    (hb : b ∈ local_equiv.target (to_local_equiv e)) {f : β → E} {g : β → F} :
    asymptotics.is_o f g (nhds b) ↔
        asymptotics.is_o (f ∘ ⇑e) (g ∘ ⇑e) (nhds (coe_fn (local_homeomorph.symm e) b)) :=
  forall_congr fun (c : ℝ) => forall_congr fun (hc : 0 < c) => is_O_with_congr e hb

end local_homeomorph


namespace homeomorph


/-- Transfer `is_O_with` over a `homeomorph`. -/
theorem is_O_with_congr {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    {E : Type u_3} [has_norm E] {F : Type u_4} [has_norm F] (e : α ≃ₜ β) {b : β} {f : β → E}
    {g : β → F} {C : ℝ} :
    asymptotics.is_O_with C f g (nhds b) ↔
        asymptotics.is_O_with C (f ∘ ⇑e) (g ∘ ⇑e) (nhds (coe_fn (homeomorph.symm e) b)) :=
  local_homeomorph.is_O_with_congr (to_local_homeomorph e) trivial

/-- Transfer `is_O` over a `homeomorph`. -/
theorem is_O_congr {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    {E : Type u_3} [has_norm E] {F : Type u_4} [has_norm F] (e : α ≃ₜ β) {b : β} {f : β → E}
    {g : β → F} :
    asymptotics.is_O f g (nhds b) ↔
        asymptotics.is_O (f ∘ ⇑e) (g ∘ ⇑e) (nhds (coe_fn (homeomorph.symm e) b)) :=
  exists_congr fun (C : ℝ) => is_O_with_congr e

/-- Transfer `is_o` over a `homeomorph`. -/
theorem is_o_congr {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    {E : Type u_3} [has_norm E] {F : Type u_4} [has_norm F] (e : α ≃ₜ β) {b : β} {f : β → E}
    {g : β → F} :
    asymptotics.is_o f g (nhds b) ↔
        asymptotics.is_o (f ∘ ⇑e) (g ∘ ⇑e) (nhds (coe_fn (homeomorph.symm e) b)) :=
  forall_congr fun (c : ℝ) => forall_congr fun (hc : 0 < c) => is_O_with_congr e

end Mathlib