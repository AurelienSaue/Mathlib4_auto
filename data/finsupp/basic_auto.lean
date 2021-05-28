/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Scott Morrison
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.group.pi
import Mathlib.algebra.big_operators.order
import Mathlib.algebra.module.basic
import Mathlib.group_theory.submonoid.basic
import Mathlib.data.fintype.card
import Mathlib.data.finset.preimage
import Mathlib.data.multiset.antidiagonal
import Mathlib.data.indicator_function
import PostPort

universes u_13 u_14 l u_1 u_5 u_7 u_2 u_8 u_6 u_11 u_12 u_9 u_4 u_3 

namespace Mathlib

/-!

# Type of functions with finite support

For any type `α` and a type `M` with zero, we define the type `finsupp α M` (notation: `α →₀ M`)
of finitely supported functions from `α` to `M`, i.e. the functions which are zero everywhere
on `α` except on a finite set.

Functions with finite support are used (at least) in the following parts of the library:

* `monoid_algebra R M` and `add_monoid_algebra R M` are defined as `M →₀ R`;

* polynomials and multivariate polynomials are defined as `add_monoid_algebra`s, hence they use
  `finsupp` under the hood;

* the linear combination of a family of vectors `v i` with coefficients `f i` (as used, e.g., to
  define linearly independent family `linear_independent`) is defined as a map
  `finsupp.total : (ι → M) → (ι →₀ R) →ₗ[R] M`.

Some other constructions are naturally equivalent to `α →₀ M` with some `α` and `M` but are defined
in a different way in the library:

* `multiset α ≃+ α →₀ ℕ`;
* `free_abelian_group α ≃+ α →₀ ℤ`.

Most of the theory assumes that the range is a commutative additive monoid. This gives us the big
sum operator as a powerful way to construct `finsupp` elements.

Many constructions based on `α →₀ M` use `semireducible` type tags to avoid reusing unwanted type
instances. E.g., `monoid_algebra`, `add_monoid_algebra`, and types based on these two have
non-pointwise multiplication.

## Notations

This file adds `α →₀ M` as a global notation for `finsupp α M`. We also use the following convention
for `Type*` variables in this file

* `α`, `β`, `γ`: types with no additional structure that appear as the first argument to `finsupp`
  somewhere in the statement;

* `ι` : an auxiliary index type;

* `M`, `M'`, `N`, `P`: types with `has_zero` or `(add_)(comm_)monoid` structure; `M` is also used
  for a (semi)module over a (semi)ring.

* `G`, `H`: groups (commutative or not, multiplicative or additive);

* `R`, `S`: (semi)rings.

## TODO

* This file is currently ~2K lines long, so possibly it should be splitted into smaller chunks;

* Add the list of definitions and important lemmas to the module docstring.

## Implementation notes

This file is a `noncomputable theory` and uses classical logic throughout.

## Notation

This file defines `α →₀ β` as notation for `finsupp α β`.

-/

/-- `finsupp α M`, denoted `α →₀ M`, is the type of functions `f : α → M` such that
  `f x = 0` for all but finitely many `x`. -/
structure finsupp (α : Type u_13) (M : Type u_14) [HasZero M] 
where
  support : finset α
  to_fun : α → M
  mem_support_to_fun : ∀ (a : α), a ∈ support ↔ to_fun a ≠ 0

infixr:25 " →₀ " => Mathlib.finsupp

namespace finsupp


/-! ### Basic declarations about `finsupp` -/

protected instance has_coe_to_fun {α : Type u_1} {M : Type u_5} [HasZero M] : has_coe_to_fun (α →₀ M) :=
  has_coe_to_fun.mk (fun (_x : α →₀ M) => α → M) to_fun

@[simp] theorem coe_mk {α : Type u_1} {M : Type u_5} [HasZero M] (f : α → M) (s : finset α) (h : ∀ (a : α), a ∈ s ↔ f a ≠ 0) : ⇑(mk s f h) = f :=
  rfl

protected instance has_zero {α : Type u_1} {M : Type u_5} [HasZero M] : HasZero (α →₀ M) :=
  { zero := mk ∅ (fun (_x : α) => 0) sorry }

@[simp] theorem coe_zero {α : Type u_1} {M : Type u_5} [HasZero M] : ⇑0 = fun (_x : α) => 0 :=
  rfl

theorem zero_apply {α : Type u_1} {M : Type u_5} [HasZero M] {a : α} : coe_fn 0 a = 0 :=
  rfl

@[simp] theorem support_zero {α : Type u_1} {M : Type u_5} [HasZero M] : support 0 = ∅ :=
  rfl

protected instance inhabited {α : Type u_1} {M : Type u_5} [HasZero M] : Inhabited (α →₀ M) :=
  { default := 0 }

@[simp] theorem mem_support_iff {α : Type u_1} {M : Type u_5} [HasZero M] {f : α →₀ M} {a : α} : a ∈ support f ↔ coe_fn f a ≠ 0 :=
  mem_support_to_fun f

@[simp] theorem fun_support_eq {α : Type u_1} {M : Type u_5} [HasZero M] (f : α →₀ M) : function.support ⇑f = ↑(support f) :=
  set.ext fun (x : α) => iff.symm mem_support_iff

theorem not_mem_support_iff {α : Type u_1} {M : Type u_5} [HasZero M] {f : α →₀ M} {a : α} : ¬a ∈ support f ↔ coe_fn f a = 0 :=
  iff.mp not_iff_comm (iff.symm mem_support_iff)

theorem coe_fn_injective {α : Type u_1} {M : Type u_5} [HasZero M] : function.injective fun (f : α →₀ M) (x : α) => coe_fn f x := sorry

theorem ext {α : Type u_1} {M : Type u_5} [HasZero M] {f : α →₀ M} {g : α →₀ M} (h : ∀ (a : α), coe_fn f a = coe_fn g a) : f = g :=
  coe_fn_injective (funext h)

theorem ext_iff {α : Type u_1} {M : Type u_5} [HasZero M] {f : α →₀ M} {g : α →₀ M} : f = g ↔ ∀ (a : α), coe_fn f a = coe_fn g a :=
  { mp := fun (ᾰ : f = g) (a : α) => Eq._oldrec (Eq.refl (coe_fn f a)) ᾰ, mpr := ext }

theorem ext_iff' {α : Type u_1} {M : Type u_5} [HasZero M] {f : α →₀ M} {g : α →₀ M} : f = g ↔ support f = support g ∧ ∀ (x : α), x ∈ support f → coe_fn f x = coe_fn g x := sorry

@[simp] theorem support_eq_empty {α : Type u_1} {M : Type u_5} [HasZero M] {f : α →₀ M} : support f = ∅ ↔ f = 0 := sorry

theorem card_support_eq_zero {α : Type u_1} {M : Type u_5} [HasZero M] {f : α →₀ M} : finset.card (support f) = 0 ↔ f = 0 := sorry

protected instance finsupp.decidable_eq {α : Type u_1} {M : Type u_5} [HasZero M] [DecidableEq α] [DecidableEq M] : DecidableEq (α →₀ M) :=
  fun (f g : α →₀ M) =>
    decidable_of_iff (support f = support g ∧ ∀ (a : α), a ∈ support f → coe_fn f a = coe_fn g a) sorry

theorem finite_supp {α : Type u_1} {M : Type u_5} [HasZero M] (f : α →₀ M) : set.finite (set_of fun (a : α) => coe_fn f a ≠ 0) :=
  Nonempty.intro (fintype.of_finset (support f) fun (_x : α) => mem_support_iff)

theorem support_subset_iff {α : Type u_1} {M : Type u_5} [HasZero M] {s : set α} {f : α →₀ M} : ↑(support f) ⊆ s ↔ ∀ (a : α), ¬a ∈ s → coe_fn f a = 0 := sorry

/-- Given `fintype α`, `equiv_fun_on_fintype` is the `equiv` between `α →₀ β` and `α → β`.
  (All functions on a finite type are finitely supported.) -/
def equiv_fun_on_fintype {α : Type u_1} {M : Type u_5} [HasZero M] [fintype α] : (α →₀ M) ≃ (α → M) :=
  equiv.mk (fun (f : α →₀ M) (a : α) => coe_fn f a)
    (fun (f : α → M) => mk (finset.filter (fun (a : α) => f a ≠ 0) finset.univ) f sorry) sorry sorry

/-! ### Declarations about `single` -/

/-- `single a b` is the finitely supported function which has
  value `b` at `a` and zero otherwise. -/
def single {α : Type u_1} {M : Type u_5} [HasZero M] (a : α) (b : M) : α →₀ M :=
  mk (ite (b = 0) ∅ (singleton a)) (fun (a' : α) => ite (a = a') b 0) sorry

theorem single_apply {α : Type u_1} {M : Type u_5} [HasZero M] {a : α} {a' : α} {b : M} : coe_fn (single a b) a' = ite (a = a') b 0 :=
  rfl

theorem single_eq_indicator {α : Type u_1} {M : Type u_5} [HasZero M] {a : α} {b : M} : ⇑(single a b) = set.indicator (singleton a) fun (_x : α) => b := sorry

@[simp] theorem single_eq_same {α : Type u_1} {M : Type u_5} [HasZero M] {a : α} {b : M} : coe_fn (single a b) a = b :=
  if_pos rfl

@[simp] theorem single_eq_of_ne {α : Type u_1} {M : Type u_5} [HasZero M] {a : α} {a' : α} {b : M} (h : a ≠ a') : coe_fn (single a b) a' = 0 :=
  if_neg h

theorem single_eq_update {α : Type u_1} {M : Type u_5} [HasZero M] {a : α} {b : M} : ⇑(single a b) = function.update 0 a b := sorry

@[simp] theorem single_zero {α : Type u_1} {M : Type u_5} [HasZero M] {a : α} : single a 0 = 0 := sorry

theorem single_of_single_apply {α : Type u_1} {M : Type u_5} [HasZero M] (a : α) (a' : α) (b : M) : single a (coe_fn (single a' b) a) = coe_fn (single a' (single a' b)) a := sorry

theorem support_single_ne_zero {α : Type u_1} {M : Type u_5} [HasZero M] {a : α} {b : M} (hb : b ≠ 0) : support (single a b) = singleton a :=
  if_neg hb

theorem support_single_subset {α : Type u_1} {M : Type u_5} [HasZero M] {a : α} {b : M} : support (single a b) ⊆ singleton a := sorry

theorem single_apply_mem {α : Type u_1} {M : Type u_5} [HasZero M] {a : α} {b : M} (x : α) : coe_fn (single a b) x ∈ insert 0 (singleton b) := sorry

theorem range_single_subset {α : Type u_1} {M : Type u_5} [HasZero M] {a : α} {b : M} : set.range ⇑(single a b) ⊆ insert 0 (singleton b) :=
  iff.mpr set.range_subset_iff single_apply_mem

theorem single_injective {α : Type u_1} {M : Type u_5} [HasZero M] (a : α) : function.injective (single a) := sorry

theorem single_apply_eq_zero {α : Type u_1} {M : Type u_5} [HasZero M] {a : α} {x : α} {b : M} : coe_fn (single a b) x = 0 ↔ x = a → b = 0 := sorry

theorem mem_support_single {α : Type u_1} {M : Type u_5} [HasZero M] (a : α) (a' : α) (b : M) : a ∈ support (single a' b) ↔ a = a' ∧ b ≠ 0 := sorry

theorem eq_single_iff {α : Type u_1} {M : Type u_5} [HasZero M] {f : α →₀ M} {a : α} {b : M} : f = single a b ↔ support f ⊆ singleton a ∧ coe_fn f a = b := sorry

theorem single_eq_single_iff {α : Type u_1} {M : Type u_5} [HasZero M] (a₁ : α) (a₂ : α) (b₁ : M) (b₂ : M) : single a₁ b₁ = single a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ ∨ b₁ = 0 ∧ b₂ = 0 := sorry

theorem single_left_inj {α : Type u_1} {M : Type u_5} [HasZero M] {a : α} {a' : α} {b : M} (h : b ≠ 0) : single a b = single a' b ↔ a = a' := sorry

@[simp] theorem single_eq_zero {α : Type u_1} {M : Type u_5} [HasZero M] {a : α} {b : M} : single a b = 0 ↔ b = 0 := sorry

theorem single_swap {α : Type u_1} {M : Type u_5} [HasZero M] (a₁ : α) (a₂ : α) (b : M) : coe_fn (single a₁ b) a₂ = coe_fn (single a₂ b) a₁ := sorry

protected instance nontrivial {α : Type u_1} {M : Type u_5} [HasZero M] [Nonempty α] [nontrivial M] : nontrivial (α →₀ M) :=
  nonempty.elim_to_inhabited
    fun (inst : Inhabited α) =>
      Exists.dcases_on (exists_ne 0)
        fun (x : M) (hx : x ≠ 0) => nontrivial_of_ne (single Inhabited.default x) 0 (mt (iff.mp single_eq_zero) hx)

theorem unique_single {α : Type u_1} {M : Type u_5} [HasZero M] [unique α] (x : α →₀ M) : x = single Inhabited.default (coe_fn x Inhabited.default) :=
  ext (iff.mpr unique.forall_iff (Eq.symm single_eq_same))

theorem unique_ext {α : Type u_1} {M : Type u_5} [HasZero M] [unique α] {f : α →₀ M} {g : α →₀ M} (h : coe_fn f Inhabited.default = coe_fn g Inhabited.default) : f = g :=
  ext fun (a : α) => eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn f a = coe_fn g a)) (unique.eq_default a))) h

theorem unique_ext_iff {α : Type u_1} {M : Type u_5} [HasZero M] [unique α] {f : α →₀ M} {g : α →₀ M} : f = g ↔ coe_fn f Inhabited.default = coe_fn g Inhabited.default :=
  { mp := fun (h : f = g) => h ▸ rfl, mpr := unique_ext }

@[simp] theorem unique_single_eq_iff {α : Type u_1} {M : Type u_5} [HasZero M] {a : α} {a' : α} {b : M} [unique α] {b' : M} : single a b = single a' b' ↔ b = b' := sorry

theorem support_eq_singleton {α : Type u_1} {M : Type u_5} [HasZero M] {f : α →₀ M} {a : α} : support f = singleton a ↔ coe_fn f a ≠ 0 ∧ f = single a (coe_fn f a) := sorry

theorem support_eq_singleton' {α : Type u_1} {M : Type u_5} [HasZero M] {f : α →₀ M} {a : α} : support f = singleton a ↔ ∃ (b : M), ∃ (H : b ≠ 0), f = single a b := sorry

theorem card_support_eq_one {α : Type u_1} {M : Type u_5} [HasZero M] {f : α →₀ M} : finset.card (support f) = 1 ↔ ∃ (a : α), coe_fn f a ≠ 0 ∧ f = single a (coe_fn f a) := sorry

theorem card_support_eq_one' {α : Type u_1} {M : Type u_5} [HasZero M] {f : α →₀ M} : finset.card (support f) = 1 ↔ ∃ (a : α), ∃ (b : M), ∃ (H : b ≠ 0), f = single a b := sorry

/-! ### Declarations about `on_finset` -/

/-- `on_finset s f hf` is the finsupp function representing `f` restricted to the finset `s`.
  The function needs to be `0` outside of `s`. Use this when the set needs to be filtered anyways,
  otherwise a better set representation is often available. -/
def on_finset {α : Type u_1} {M : Type u_5} [HasZero M] (s : finset α) (f : α → M) (hf : ∀ (a : α), f a ≠ 0 → a ∈ s) : α →₀ M :=
  mk (finset.filter (fun (a : α) => f a ≠ 0) s) f sorry

@[simp] theorem on_finset_apply {α : Type u_1} {M : Type u_5} [HasZero M] {s : finset α} {f : α → M} {hf : ∀ (a : α), f a ≠ 0 → a ∈ s} {a : α} : coe_fn (on_finset s f hf) a = f a :=
  rfl

@[simp] theorem support_on_finset_subset {α : Type u_1} {M : Type u_5} [HasZero M] {s : finset α} {f : α → M} {hf : ∀ (a : α), f a ≠ 0 → a ∈ s} : support (on_finset s f hf) ⊆ s :=
  finset.filter_subset (fun (a : α) => f a ≠ 0) s

@[simp] theorem mem_support_on_finset {α : Type u_1} {M : Type u_5} [HasZero M] {s : finset α} {f : α → M} (hf : ∀ (a : α), f a ≠ 0 → a ∈ s) {a : α} : a ∈ support (on_finset s f hf) ↔ f a ≠ 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ∈ support (on_finset s f hf) ↔ f a ≠ 0)) (propext mem_support_iff)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn (on_finset s f hf) a ≠ 0 ↔ f a ≠ 0)) on_finset_apply)) (iff.refl (f a ≠ 0)))

theorem support_on_finset {α : Type u_1} {M : Type u_5} [HasZero M] {s : finset α} {f : α → M} (hf : ∀ (a : α), f a ≠ 0 → a ∈ s) : support (on_finset s f hf) = finset.filter (fun (a : α) => f a ≠ 0) s :=
  rfl

/-! ### Declarations about `map_range` -/

/-- The composition of `f : M → N` and `g : α →₀ M` is
`map_range f hf g : α →₀ N`, well-defined when `f 0 = 0`. -/
def map_range {α : Type u_1} {M : Type u_5} {N : Type u_7} [HasZero M] [HasZero N] (f : M → N) (hf : f 0 = 0) (g : α →₀ M) : α →₀ N :=
  on_finset (support g) (f ∘ ⇑g) sorry

@[simp] theorem map_range_apply {α : Type u_1} {M : Type u_5} {N : Type u_7} [HasZero M] [HasZero N] {f : M → N} {hf : f 0 = 0} {g : α →₀ M} {a : α} : coe_fn (map_range f hf g) a = f (coe_fn g a) :=
  rfl

@[simp] theorem map_range_zero {α : Type u_1} {M : Type u_5} {N : Type u_7} [HasZero M] [HasZero N] {f : M → N} {hf : f 0 = 0} : map_range f hf 0 = 0 := sorry

theorem support_map_range {α : Type u_1} {M : Type u_5} {N : Type u_7} [HasZero M] [HasZero N] {f : M → N} {hf : f 0 = 0} {g : α →₀ M} : support (map_range f hf g) ⊆ support g :=
  support_on_finset_subset

@[simp] theorem map_range_single {α : Type u_1} {M : Type u_5} {N : Type u_7} [HasZero M] [HasZero N] {f : M → N} {hf : f 0 = 0} {a : α} {b : M} : map_range f hf (single a b) = single a (f b) := sorry

/-! ### Declarations about `emb_domain` -/

/-- Given `f : α ↪ β` and `v : α →₀ M`, `emb_domain f v : β →₀ M`
is the finitely supported function whose value at `f a : β` is `v a`.
For a `b : β` outside the range of `f`, it is zero. -/
def emb_domain {α : Type u_1} {β : Type u_2} {M : Type u_5} [HasZero M] (f : α ↪ β) (v : α →₀ M) : β →₀ M :=
  mk (finset.map f (support v))
    (fun (a₂ : β) =>
      dite (a₂ ∈ finset.map f (support v))
        (fun (h : a₂ ∈ finset.map f (support v)) =>
          coe_fn v (finset.choose (fun (a₁ : α) => coe_fn f a₁ = a₂) (support v) sorry))
        fun (h : ¬a₂ ∈ finset.map f (support v)) => 0)
    sorry

@[simp] theorem support_emb_domain {α : Type u_1} {β : Type u_2} {M : Type u_5} [HasZero M] (f : α ↪ β) (v : α →₀ M) : support (emb_domain f v) = finset.map f (support v) :=
  rfl

@[simp] theorem emb_domain_zero {α : Type u_1} {β : Type u_2} {M : Type u_5} [HasZero M] (f : α ↪ β) : emb_domain f 0 = 0 :=
  rfl

@[simp] theorem emb_domain_apply {α : Type u_1} {β : Type u_2} {M : Type u_5} [HasZero M] (f : α ↪ β) (v : α →₀ M) (a : α) : coe_fn (emb_domain f v) (coe_fn f a) = coe_fn v a := sorry

theorem emb_domain_notin_range {α : Type u_1} {β : Type u_2} {M : Type u_5} [HasZero M] (f : α ↪ β) (v : α →₀ M) (a : β) (h : ¬a ∈ set.range ⇑f) : coe_fn (emb_domain f v) a = 0 := sorry

theorem emb_domain_injective {α : Type u_1} {β : Type u_2} {M : Type u_5} [HasZero M] (f : α ↪ β) : function.injective (emb_domain f) := sorry

@[simp] theorem emb_domain_inj {α : Type u_1} {β : Type u_2} {M : Type u_5} [HasZero M] {f : α ↪ β} {l₁ : α →₀ M} {l₂ : α →₀ M} : emb_domain f l₁ = emb_domain f l₂ ↔ l₁ = l₂ :=
  function.injective.eq_iff (emb_domain_injective f)

@[simp] theorem emb_domain_eq_zero {α : Type u_1} {β : Type u_2} {M : Type u_5} [HasZero M] {f : α ↪ β} {l : α →₀ M} : emb_domain f l = 0 ↔ l = 0 :=
  function.injective.eq_iff' (emb_domain_injective f) (emb_domain_zero f)

theorem emb_domain_map_range {α : Type u_1} {β : Type u_2} {M : Type u_5} {N : Type u_7} [HasZero M] [HasZero N] (f : α ↪ β) (g : M → N) (p : α →₀ M) (hg : g 0 = 0) : emb_domain f (map_range g hg p) = map_range g hg (emb_domain f p) := sorry

theorem single_of_emb_domain_single {α : Type u_1} {β : Type u_2} {M : Type u_5} [HasZero M] (l : α →₀ M) (f : α ↪ β) (a : β) (b : M) (hb : b ≠ 0) (h : emb_domain f l = single a b) : ∃ (x : α), l = single x b ∧ coe_fn f x = a := sorry

/-! ### Declarations about `zip_with` -/

/-- `zip_with f hf g₁ g₂` is the finitely supported function satisfying
  `zip_with f hf g₁ g₂ a = f (g₁ a) (g₂ a)`, and it is well-defined when `f 0 0 = 0`. -/
def zip_with {α : Type u_1} {M : Type u_5} {N : Type u_7} {P : Type u_8} [HasZero M] [HasZero N] [HasZero P] (f : M → N → P) (hf : f 0 0 = 0) (g₁ : α →₀ M) (g₂ : α →₀ N) : α →₀ P :=
  on_finset (support g₁ ∪ support g₂) (fun (a : α) => f (coe_fn g₁ a) (coe_fn g₂ a)) sorry

@[simp] theorem zip_with_apply {α : Type u_1} {M : Type u_5} {N : Type u_7} {P : Type u_8} [HasZero M] [HasZero N] [HasZero P] {f : M → N → P} {hf : f 0 0 = 0} {g₁ : α →₀ M} {g₂ : α →₀ N} {a : α} : coe_fn (zip_with f hf g₁ g₂) a = f (coe_fn g₁ a) (coe_fn g₂ a) :=
  rfl

theorem support_zip_with {α : Type u_1} {M : Type u_5} {N : Type u_7} {P : Type u_8} [HasZero M] [HasZero N] [HasZero P] {f : M → N → P} {hf : f 0 0 = 0} {g₁ : α →₀ M} {g₂ : α →₀ N} : support (zip_with f hf g₁ g₂) ⊆ support g₁ ∪ support g₂ :=
  support_on_finset_subset

/-! ### Declarations about `erase` -/

/-- `erase a f` is the finitely supported function equal to `f` except at `a` where it is equal to
  `0`. -/
def erase {α : Type u_1} {M : Type u_5} [HasZero M] (a : α) (f : α →₀ M) : α →₀ M :=
  mk (finset.erase (support f) a) (fun (a' : α) => ite (a' = a) 0 (coe_fn f a')) sorry

@[simp] theorem support_erase {α : Type u_1} {M : Type u_5} [HasZero M] {a : α} {f : α →₀ M} : support (erase a f) = finset.erase (support f) a :=
  rfl

@[simp] theorem erase_same {α : Type u_1} {M : Type u_5} [HasZero M] {a : α} {f : α →₀ M} : coe_fn (erase a f) a = 0 :=
  if_pos rfl

@[simp] theorem erase_ne {α : Type u_1} {M : Type u_5} [HasZero M] {a : α} {a' : α} {f : α →₀ M} (h : a' ≠ a) : coe_fn (erase a f) a' = coe_fn f a' :=
  if_neg h

@[simp] theorem erase_single {α : Type u_1} {M : Type u_5} [HasZero M] {a : α} {b : M} : erase a (single a b) = 0 := sorry

theorem erase_single_ne {α : Type u_1} {M : Type u_5} [HasZero M] {a : α} {a' : α} {b : M} (h : a ≠ a') : erase a (single a' b) = single a' b := sorry

@[simp] theorem erase_zero {α : Type u_1} {M : Type u_5} [HasZero M] (a : α) : erase a 0 = 0 := sorry

/-!
### Declarations about `sum` and `prod`

In most of this section, the domain `β` is assumed to be an `add_monoid`.
-/

-- [to_additive sum] for finsupp.prod doesn't work, the equation lemmas are not generated

/-- `sum f g` is the sum of `g a (f a)` over the support of `f`. -/
def sum {α : Type u_1} {M : Type u_5} {N : Type u_7} [HasZero M] [add_comm_monoid N] (f : α →₀ M) (g : α → M → N) : N :=
  finset.sum (support f) fun (a : α) => g a (coe_fn f a)

/-- `prod f g` is the product of `g a (f a)` over the support of `f`. -/
def prod {α : Type u_1} {M : Type u_5} {N : Type u_7} [HasZero M] [comm_monoid N] (f : α →₀ M) (g : α → M → N) : N :=
  finset.prod (support f) fun (a : α) => g a (coe_fn f a)

theorem sum_of_support_subset {α : Type u_1} {M : Type u_5} {N : Type u_7} [HasZero M] [add_comm_monoid N] (f : α →₀ M) {s : finset α} (hs : support f ⊆ s) (g : α → M → N) (h : ∀ (i : α), i ∈ s → g i 0 = 0) : sum f g = finset.sum s fun (x : α) => g x (coe_fn f x) :=
  finset.sum_subset hs
    fun (x : α) (hxs : x ∈ s) (hx : ¬x ∈ support f) =>
      Eq.subst (h x hxs) (congr_arg (g x)) (iff.mp not_mem_support_iff hx)

theorem prod_fintype {α : Type u_1} {M : Type u_5} {N : Type u_7} [HasZero M] [comm_monoid N] [fintype α] (f : α →₀ M) (g : α → M → N) (h : ∀ (i : α), g i 0 = 1) : prod f g = finset.prod finset.univ fun (i : α) => g i (coe_fn f i) :=
  prod_of_support_subset f (finset.subset_univ (support f)) g fun (x : α) (_x : x ∈ finset.univ) => h x

@[simp] theorem prod_single_index {α : Type u_1} {M : Type u_5} {N : Type u_7} [HasZero M] [comm_monoid N] {a : α} {b : M} {h : α → M → N} (h_zero : h a 0 = 1) : prod (single a b) h = h a b := sorry

theorem prod_map_range_index {α : Type u_1} {M : Type u_5} {M' : Type u_6} {N : Type u_7} [HasZero M] [HasZero M'] [comm_monoid N] {f : M → M'} {hf : f 0 = 0} {g : α →₀ M} {h : α → M' → N} (h0 : ∀ (a : α), h a 0 = 1) : prod (map_range f hf g) h = prod g fun (a : α) (b : M) => h a (f b) := sorry

@[simp] theorem sum_zero_index {α : Type u_1} {M : Type u_5} {N : Type u_7} [HasZero M] [add_comm_monoid N] {h : α → M → N} : sum 0 h = 0 :=
  rfl

theorem sum_comm {α : Type u_1} {β : Type u_2} {M : Type u_5} {M' : Type u_6} {N : Type u_7} [HasZero M] [HasZero M'] [add_comm_monoid N] (f : α →₀ M) (g : β →₀ M') (h : α → M → β → M' → N) : (sum f fun (x : α) (v : M) => sum g fun (x' : β) (v' : M') => h x v x' v') =
  sum g fun (x' : β) (v' : M') => sum f fun (x : α) (v : M) => h x v x' v' :=
  finset.sum_comm

@[simp] theorem prod_ite_eq {α : Type u_1} {M : Type u_5} {N : Type u_7} [HasZero M] [comm_monoid N] [DecidableEq α] (f : α →₀ M) (a : α) (b : α → M → N) : (prod f fun (x : α) (v : M) => ite (a = x) (b x v) 1) = ite (a ∈ support f) (b a (coe_fn f a)) 1 := sorry

@[simp] theorem sum_ite_self_eq {α : Type u_1} [DecidableEq α] {N : Type u_2} [add_comm_monoid N] (f : α →₀ N) (a : α) : (sum f fun (x : α) (v : N) => ite (a = x) v 0) = coe_fn f a := sorry

/-- A restatement of `prod_ite_eq` with the equality test reversed. -/
@[simp] theorem sum_ite_eq' {α : Type u_1} {M : Type u_5} {N : Type u_7} [HasZero M] [add_comm_monoid N] [DecidableEq α] (f : α →₀ M) (a : α) (b : α → M → N) : (sum f fun (x : α) (v : M) => ite (x = a) (b x v) 0) = ite (a ∈ support f) (b a (coe_fn f a)) 0 := sorry

@[simp] theorem sum_ite_self_eq' {α : Type u_1} [DecidableEq α] {N : Type u_2} [add_comm_monoid N] (f : α →₀ N) (a : α) : (sum f fun (x : α) (v : N) => ite (x = a) v 0) = coe_fn f a := sorry

@[simp] theorem prod_pow {α : Type u_1} {N : Type u_7} [comm_monoid N] [fintype α] (f : α →₀ ℕ) (g : α → N) : (prod f fun (a : α) (b : ℕ) => g a ^ b) = finset.prod finset.univ fun (a : α) => g a ^ coe_fn f a :=
  prod_fintype f (fun (a : α) (b : ℕ) => g a ^ b) fun (a : α) => pow_zero (g a)

/-- If `g` maps a second argument of 0 to 1, then multiplying it over the
result of `on_finset` is the same as multiplying it over the original
`finset`. -/
theorem on_finset_sum {α : Type u_1} {M : Type u_5} {N : Type u_7} [HasZero M] [add_comm_monoid N] {s : finset α} {f : α → M} {g : α → M → N} (hf : ∀ (a : α), f a ≠ 0 → a ∈ s) (hg : ∀ (a : α), g a 0 = 0) : sum (on_finset s f hf) g = finset.sum s fun (a : α) => g a (f a) := sorry

/-!
### Additive monoid structure on `α →₀ M`
-/

protected instance has_add {α : Type u_1} {M : Type u_5} [add_monoid M] : Add (α →₀ M) :=
  { add := zip_with Add.add sorry }

@[simp] theorem coe_add {α : Type u_1} {M : Type u_5} [add_monoid M] (f : α →₀ M) (g : α →₀ M) : ⇑(f + g) = ⇑f + ⇑g :=
  rfl

theorem add_apply {α : Type u_1} {M : Type u_5} [add_monoid M] {g₁ : α →₀ M} {g₂ : α →₀ M} {a : α} : coe_fn (g₁ + g₂) a = coe_fn g₁ a + coe_fn g₂ a :=
  rfl

theorem support_add {α : Type u_1} {M : Type u_5} [add_monoid M] {g₁ : α →₀ M} {g₂ : α →₀ M} : support (g₁ + g₂) ⊆ support g₁ ∪ support g₂ :=
  support_zip_with

theorem support_add_eq {α : Type u_1} {M : Type u_5} [add_monoid M] {g₁ : α →₀ M} {g₂ : α →₀ M} (h : disjoint (support g₁) (support g₂)) : support (g₁ + g₂) = support g₁ ∪ support g₂ := sorry

@[simp] theorem single_add {α : Type u_1} {M : Type u_5} [add_monoid M] {a : α} {b₁ : M} {b₂ : M} : single a (b₁ + b₂) = single a b₁ + single a b₂ := sorry

protected instance add_monoid {α : Type u_1} {M : Type u_5} [add_monoid M] : add_monoid (α →₀ M) :=
  add_monoid.mk Add.add sorry 0 sorry sorry

/-- `finsupp.single` as an `add_monoid_hom`.

See `finsupp.lsingle` for the stronger version as a linear map.
-/
def single_add_hom {α : Type u_1} {M : Type u_5} [add_monoid M] (a : α) : M →+ α →₀ M :=
  add_monoid_hom.mk (single a) sorry sorry

/-- Evaluation of a function `f : α →₀ M` at a point as an additive monoid homomorphism.

See `finsupp.lapply` for the stronger version as a linear map. -/
@[simp] theorem apply_add_hom_apply {α : Type u_1} {M : Type u_5} [add_monoid M] (a : α) (g : α →₀ M) : coe_fn (apply_add_hom a) g = coe_fn g a :=
  Eq.refl (coe_fn (apply_add_hom a) g)

theorem single_add_erase {α : Type u_1} {M : Type u_5} [add_monoid M] (a : α) (f : α →₀ M) : single a (coe_fn f a) + erase a f = f := sorry

theorem erase_add_single {α : Type u_1} {M : Type u_5} [add_monoid M] (a : α) (f : α →₀ M) : erase a f + single a (coe_fn f a) = f := sorry

@[simp] theorem erase_add {α : Type u_1} {M : Type u_5} [add_monoid M] (a : α) (f : α →₀ M) (f' : α →₀ M) : erase a (f + f') = erase a f + erase a f' := sorry

protected theorem induction {α : Type u_1} {M : Type u_5} [add_monoid M] {p : (α →₀ M) → Prop} (f : α →₀ M) (h0 : p 0) (ha : ∀ (a : α) (b : M) (f : α →₀ M), ¬a ∈ support f → b ≠ 0 → p f → p (single a b + f)) : p f := sorry

theorem induction₂ {α : Type u_1} {M : Type u_5} [add_monoid M] {p : (α →₀ M) → Prop} (f : α →₀ M) (h0 : p 0) (ha : ∀ (a : α) (b : M) (f : α →₀ M), ¬a ∈ support f → b ≠ 0 → p f → p (f + single a b)) : p f := sorry

@[simp] theorem add_closure_Union_range_single {α : Type u_1} {M : Type u_5} [add_monoid M] : add_submonoid.closure (set.Union fun (a : α) => set.range (single a)) = ⊤ := sorry

/-- If two additive homomorphisms from `α →₀ M` are equal on each `single a b`, then
they are equal. -/
theorem add_hom_ext {α : Type u_1} {M : Type u_5} {N : Type u_7} [add_monoid M] [add_monoid N] {f : (α →₀ M) →+ N} {g : (α →₀ M) →+ N} (H : ∀ (x : α) (y : M), coe_fn f (single x y) = coe_fn g (single x y)) : f = g := sorry

/-- If two additive homomorphisms from `α →₀ M` are equal on each `single a b`, then
they are equal.

We formulate this using equality of `add_monoid_hom`s so that `ext` tactic can apply a type-specific
extensionality lemma after this one.  E.g., if the fiber `M` is `ℕ` or `ℤ`, then it suffices to
verify `f (single a 1) = g (single a 1)`. -/
theorem add_hom_ext' {α : Type u_1} {M : Type u_5} {N : Type u_7} [add_monoid M] [add_monoid N] {f : (α →₀ M) →+ N} {g : (α →₀ M) →+ N} (H : ∀ (x : α), add_monoid_hom.comp f (single_add_hom x) = add_monoid_hom.comp g (single_add_hom x)) : f = g :=
  add_hom_ext fun (x : α) => add_monoid_hom.congr_fun (H x)

theorem mul_hom_ext {α : Type u_1} {M : Type u_5} {N : Type u_7} [add_monoid M] [monoid N] {f : multiplicative (α →₀ M) →* N} {g : multiplicative (α →₀ M) →* N} (H : ∀ (x : α) (y : M),
  coe_fn f (coe_fn multiplicative.of_add (single x y)) = coe_fn g (coe_fn multiplicative.of_add (single x y))) : f = g :=
  monoid_hom.ext (add_monoid_hom.congr_fun (add_hom_ext H))

theorem mul_hom_ext' {α : Type u_1} {M : Type u_5} {N : Type u_7} [add_monoid M] [monoid N] {f : multiplicative (α →₀ M) →* N} {g : multiplicative (α →₀ M) →* N} (H : ∀ (x : α),
  monoid_hom.comp f (coe_fn add_monoid_hom.to_multiplicative (single_add_hom x)) =
    monoid_hom.comp g (coe_fn add_monoid_hom.to_multiplicative (single_add_hom x))) : f = g :=
  mul_hom_ext fun (x : α) => monoid_hom.congr_fun (H x)

theorem map_range_add {α : Type u_1} {M : Type u_5} {N : Type u_7} [add_monoid M] [add_monoid N] {f : M → N} {hf : f 0 = 0} (hf' : ∀ (x y : M), f (x + y) = f x + f y) (v₁ : α →₀ M) (v₂ : α →₀ M) : map_range f hf (v₁ + v₂) = map_range f hf v₁ + map_range f hf v₂ := sorry

end finsupp


theorem mul_equiv.map_finsupp_prod {α : Type u_1} {M : Type u_5} {N : Type u_7} {P : Type u_8} [HasZero M] [comm_monoid N] [comm_monoid P] (h : N ≃* P) (f : α →₀ M) (g : α → M → N) : coe_fn h (finsupp.prod f g) = finsupp.prod f fun (a : α) (b : M) => coe_fn h (g a b) :=
  mul_equiv.map_prod h (fun (a : α) => g a (coe_fn f a)) (finsupp.support f)

theorem add_monoid_hom.map_finsupp_sum {α : Type u_1} {M : Type u_5} {N : Type u_7} {P : Type u_8} [HasZero M] [add_comm_monoid N] [add_comm_monoid P] (h : N →+ P) (f : α →₀ M) (g : α → M → N) : coe_fn h (finsupp.sum f g) = finsupp.sum f fun (a : α) (b : M) => coe_fn h (g a b) :=
  add_monoid_hom.map_sum h (fun (a : α) => g a (coe_fn f a)) (finsupp.support f)

theorem ring_hom.map_finsupp_sum {α : Type u_1} {M : Type u_5} {R : Type u_11} {S : Type u_12} [HasZero M] [semiring R] [semiring S] (h : R →+* S) (f : α →₀ M) (g : α → M → R) : coe_fn h (finsupp.sum f g) = finsupp.sum f fun (a : α) (b : M) => coe_fn h (g a b) :=
  ring_hom.map_sum h (fun (a : α) => g a (coe_fn f a)) (finsupp.support f)

theorem ring_hom.map_finsupp_prod {α : Type u_1} {M : Type u_5} {R : Type u_11} {S : Type u_12} [HasZero M] [comm_semiring R] [comm_semiring S] (h : R →+* S) (f : α →₀ M) (g : α → M → R) : coe_fn h (finsupp.prod f g) = finsupp.prod f fun (a : α) (b : M) => coe_fn h (g a b) :=
  ring_hom.map_prod h (fun (a : α) => g a (coe_fn f a)) (finsupp.support f)

theorem monoid_hom.coe_finsupp_prod {α : Type u_1} {β : Type u_2} {N : Type u_7} {P : Type u_8} [HasZero β] [monoid N] [comm_monoid P] (f : α →₀ β) (g : α → β → N →* P) : ⇑(finsupp.prod f g) = finsupp.prod f fun (i : α) (fi : β) => ⇑(g i fi) :=
  monoid_hom.coe_prod (fun (a : α) => g a (coe_fn f a)) (finsupp.support f)

@[simp] theorem add_monoid_hom.finsupp_sum_apply {α : Type u_1} {β : Type u_2} {N : Type u_7} {P : Type u_8} [HasZero β] [add_monoid N] [add_comm_monoid P] (f : α →₀ β) (g : α → β → N →+ P) (x : N) : coe_fn (finsupp.sum f g) x = finsupp.sum f fun (i : α) (fi : β) => coe_fn (g i fi) x :=
  add_monoid_hom.finset_sum_apply (fun (a : α) => g a (coe_fn f a)) (finsupp.support f) x

namespace finsupp


protected instance nat_sub {α : Type u_1} : Sub (α →₀ ℕ) :=
  { sub := zip_with (fun (m n : ℕ) => m - n) sorry }

@[simp] theorem nat_sub_apply {α : Type u_1} {g₁ : α →₀ ℕ} {g₂ : α →₀ ℕ} {a : α} : coe_fn (g₁ - g₂) a = coe_fn g₁ a - coe_fn g₂ a :=
  rfl

@[simp] theorem single_sub {α : Type u_1} {a : α} {n₁ : ℕ} {n₂ : ℕ} : single a (n₁ - n₂) = single a n₁ - single a n₂ := sorry

-- These next two lemmas are used in developing

-- the partial derivative on `mv_polynomial`.

theorem sub_single_one_add {α : Type u_1} {a : α} {u : α →₀ ℕ} {u' : α →₀ ℕ} (h : coe_fn u a ≠ 0) : u - single a 1 + u' = u + u' - single a 1 := sorry

theorem add_sub_single_one {α : Type u_1} {a : α} {u : α →₀ ℕ} {u' : α →₀ ℕ} (h : coe_fn u' a ≠ 0) : u + (u' - single a 1) = u + u' - single a 1 := sorry

@[simp] theorem nat_zero_sub {α : Type u_1} (f : α →₀ ℕ) : 0 - f = 0 :=
  ext fun (x : α) => nat.zero_sub (coe_fn f x)

protected instance add_comm_monoid {α : Type u_1} {M : Type u_5} [add_comm_monoid M] : add_comm_monoid (α →₀ M) :=
  add_comm_monoid.mk add_monoid.add sorry add_monoid.zero sorry sorry sorry

protected instance has_sub {α : Type u_1} {G : Type u_9} [add_group G] : Sub (α →₀ G) :=
  { sub := zip_with Sub.sub sorry }

protected instance add_group {α : Type u_1} {G : Type u_9} [add_group G] : add_group (α →₀ G) :=
  add_group.mk add_monoid.add sorry add_monoid.zero sorry sorry (map_range Neg.neg neg_zero) Sub.sub sorry

protected instance add_comm_group {α : Type u_1} {G : Type u_9} [add_comm_group G] : add_comm_group (α →₀ G) :=
  add_comm_group.mk add_group.add sorry add_group.zero sorry sorry add_group.neg add_group.sub sorry sorry

theorem single_multiset_sum {α : Type u_1} {M : Type u_5} [add_comm_monoid M] (s : multiset M) (a : α) : single a (multiset.sum s) = multiset.sum (multiset.map (single a) s) := sorry

theorem single_finset_sum {α : Type u_1} {ι : Type u_4} {M : Type u_5} [add_comm_monoid M] (s : finset ι) (f : ι → M) (a : α) : single a (finset.sum s fun (b : ι) => f b) = finset.sum s fun (b : ι) => single a (f b) := sorry

theorem single_sum {α : Type u_1} {ι : Type u_4} {M : Type u_5} {N : Type u_7} [HasZero M] [add_comm_monoid N] (s : ι →₀ M) (f : ι → M → N) (a : α) : single a (sum s f) = sum s fun (d : ι) (c : M) => single a (f d c) :=
  single_finset_sum (support s) (fun (a : ι) => f a (coe_fn s a)) a

theorem sum_neg_index {α : Type u_1} {M : Type u_5} {G : Type u_9} [add_group G] [add_comm_monoid M] {g : α →₀ G} {h : α → G → M} (h0 : ∀ (a : α), h a 0 = 0) : sum (-g) h = sum g fun (a : α) (b : G) => h a (-b) :=
  sum_map_range_index h0

@[simp] theorem neg_apply {α : Type u_1} {G : Type u_9} [add_group G] {g : α →₀ G} {a : α} : coe_fn (-g) a = -coe_fn g a :=
  rfl

@[simp] theorem sub_apply {α : Type u_1} {G : Type u_9} [add_group G] {g₁ : α →₀ G} {g₂ : α →₀ G} {a : α} : coe_fn (g₁ - g₂) a = coe_fn g₁ a - coe_fn g₂ a :=
  rfl

@[simp] theorem support_neg {α : Type u_1} {G : Type u_9} [add_group G] {f : α →₀ G} : support (-f) = support f :=
  finset.subset.antisymm support_map_range
    (trans_rel_right has_subset.subset (congr_arg support (Eq.symm (neg_neg f))) support_map_range)

@[simp] theorem sum_apply {α : Type u_1} {β : Type u_2} {M : Type u_5} {N : Type u_7} [HasZero M] [add_comm_monoid N] {f : α →₀ M} {g : α → M → β →₀ N} {a₂ : β} : coe_fn (sum f g) a₂ = sum f fun (a₁ : α) (b : M) => coe_fn (g a₁ b) a₂ :=
  add_monoid_hom.map_sum (apply_add_hom a₂) (fun (a : α) => g a (coe_fn f a)) (support f)

theorem support_sum {α : Type u_1} {β : Type u_2} {M : Type u_5} {N : Type u_7} [HasZero M] [add_comm_monoid N] {f : α →₀ M} {g : α → M → β →₀ N} : support (sum f g) ⊆ finset.bUnion (support f) fun (a : α) => support (g a (coe_fn f a)) := sorry

@[simp] theorem sum_zero {α : Type u_1} {M : Type u_5} {N : Type u_7} [HasZero M] [add_comm_monoid N] {f : α →₀ M} : (sum f fun (a : α) (b : M) => 0) = 0 :=
  finset.sum_const_zero

@[simp] theorem prod_mul {α : Type u_1} {M : Type u_5} {N : Type u_7} [HasZero M] [comm_monoid N] {f : α →₀ M} {h₁ : α → M → N} {h₂ : α → M → N} : (prod f fun (a : α) (b : M) => h₁ a b * h₂ a b) = prod f h₁ * prod f h₂ :=
  finset.prod_mul_distrib

@[simp] theorem sum_neg {α : Type u_1} {M : Type u_5} {G : Type u_9} [HasZero M] [add_comm_group G] {f : α →₀ M} {h : α → M → G} : (sum f fun (a : α) (b : M) => -h a b) = -sum f h :=
  Eq.symm (add_monoid_hom.map_sum (-add_monoid_hom.id G) (fun (x : α) => h x (coe_fn f x)) (support f))

@[simp] theorem sum_sub {α : Type u_1} {M : Type u_5} {G : Type u_9} [HasZero M] [add_comm_group G] {f : α →₀ M} {h₁ : α → M → G} {h₂ : α → M → G} : (sum f fun (a : α) (b : M) => h₁ a b - h₂ a b) = sum f h₁ - sum f h₂ :=
  finset.sum_sub_distrib

theorem prod_add_index {α : Type u_1} {M : Type u_5} {N : Type u_7} [add_comm_monoid M] [comm_monoid N] {f : α →₀ M} {g : α →₀ M} {h : α → M → N} (h_zero : ∀ (a : α), h a 0 = 1) (h_add : ∀ (a : α) (b₁ b₂ : M), h a (b₁ + b₂) = h a b₁ * h a b₂) : prod (f + g) h = prod f h * prod g h := sorry

@[simp] theorem sum_add_index' {α : Type u_1} {M : Type u_5} {N : Type u_7} [add_comm_monoid M] [add_comm_monoid N] {f : α →₀ M} {g : α →₀ M} (h : α → M →+ N) : (sum (f + g) fun (x : α) => ⇑(h x)) = (sum f fun (x : α) => ⇑(h x)) + sum g fun (x : α) => ⇑(h x) :=
  sum_add_index (fun (a : α) => add_monoid_hom.map_zero (h a)) fun (a : α) => add_monoid_hom.map_add (h a)

@[simp] theorem prod_add_index' {α : Type u_1} {M : Type u_5} {N : Type u_7} [add_comm_monoid M] [comm_monoid N] {f : α →₀ M} {g : α →₀ M} (h : α → multiplicative M →* N) : (prod (f + g) fun (a : α) (b : M) => coe_fn (h a) (coe_fn multiplicative.of_add b)) =
  (prod f fun (a : α) (b : M) => coe_fn (h a) (coe_fn multiplicative.of_add b)) *
    prod g fun (a : α) (b : M) => coe_fn (h a) (coe_fn multiplicative.of_add b) :=
  prod_add_index (fun (a : α) => monoid_hom.map_one (h a)) fun (a : α) => monoid_hom.map_mul (h a)

/-- The canonical isomorphism between families of additive monoid homomorphisms `α → (M →+ N)`
and monoid homomorphisms `(α →₀ M) →+ N`. -/
def lift_add_hom {α : Type u_1} {M : Type u_5} {N : Type u_7} [add_comm_monoid M] [add_comm_monoid N] : (α → M →+ N) ≃+ ((α →₀ M) →+ N) :=
  add_equiv.mk (fun (F : α → M →+ N) => add_monoid_hom.mk (fun (f : α →₀ M) => sum f fun (x : α) => ⇑(F x)) sorry sorry)
    (fun (F : (α →₀ M) →+ N) (x : α) => add_monoid_hom.comp F (single_add_hom x)) sorry sorry sorry

@[simp] theorem lift_add_hom_apply {α : Type u_1} {M : Type u_5} {N : Type u_7} [add_comm_monoid M] [add_comm_monoid N] (F : α → M →+ N) (f : α →₀ M) : coe_fn (coe_fn lift_add_hom F) f = sum f fun (x : α) => ⇑(F x) :=
  rfl

@[simp] theorem lift_add_hom_symm_apply {α : Type u_1} {M : Type u_5} {N : Type u_7} [add_comm_monoid M] [add_comm_monoid N] (F : (α →₀ M) →+ N) (x : α) : coe_fn (add_equiv.symm lift_add_hom) F x = add_monoid_hom.comp F (single_add_hom x) :=
  rfl

theorem lift_add_hom_symm_apply_apply {α : Type u_1} {M : Type u_5} {N : Type u_7} [add_comm_monoid M] [add_comm_monoid N] (F : (α →₀ M) →+ N) (x : α) (y : M) : coe_fn (coe_fn (add_equiv.symm lift_add_hom) F x) y = coe_fn F (single x y) :=
  rfl

@[simp] theorem lift_add_hom_single_add_hom {α : Type u_1} {M : Type u_5} [add_comm_monoid M] : coe_fn lift_add_hom single_add_hom = add_monoid_hom.id (α →₀ M) :=
  iff.mpr (equiv.apply_eq_iff_eq_symm_apply (add_equiv.to_equiv lift_add_hom)) rfl

@[simp] theorem sum_single {α : Type u_1} {M : Type u_5} [add_comm_monoid M] (f : α →₀ M) : sum f single = f :=
  add_monoid_hom.congr_fun lift_add_hom_single_add_hom f

@[simp] theorem lift_add_hom_apply_single {α : Type u_1} {M : Type u_5} {N : Type u_7} [add_comm_monoid M] [add_comm_monoid N] (f : α → M →+ N) (a : α) (b : M) : coe_fn (coe_fn lift_add_hom f) (single a b) = coe_fn (f a) b :=
  sum_single_index (add_monoid_hom.map_zero (f a))

@[simp] theorem lift_add_hom_comp_single {α : Type u_1} {M : Type u_5} {N : Type u_7} [add_comm_monoid M] [add_comm_monoid N] (f : α → M →+ N) (a : α) : add_monoid_hom.comp (coe_fn lift_add_hom f) (single_add_hom a) = f a :=
  add_monoid_hom.ext fun (b : M) => lift_add_hom_apply_single f a b

theorem comp_lift_add_hom {α : Type u_1} {M : Type u_5} {N : Type u_7} {P : Type u_8} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] (g : N →+ P) (f : α → M →+ N) : add_monoid_hom.comp g (coe_fn lift_add_hom f) = coe_fn lift_add_hom fun (a : α) => add_monoid_hom.comp g (f a) := sorry

theorem sum_sub_index {α : Type u_1} {β : Type u_2} {γ : Type u_3} [add_comm_group β] [add_comm_group γ] {f : α →₀ β} {g : α →₀ β} {h : α → β → γ} (h_sub : ∀ (a : α) (b₁ b₂ : β), h a (b₁ - b₂) = h a b₁ - h a b₂) : sum (f - g) h = sum f h - sum g h :=
  add_monoid_hom.map_sub (coe_fn lift_add_hom fun (a : α) => add_monoid_hom.of_map_sub (h a) (h_sub a)) f g

theorem sum_emb_domain {α : Type u_1} {β : Type u_2} {M : Type u_5} {N : Type u_7} [HasZero M] [add_comm_monoid N] {v : α →₀ M} {f : α ↪ β} {g : β → M → N} : sum (emb_domain f v) g = sum v fun (a : α) (b : M) => g (coe_fn f a) b := sorry

theorem sum_finset_sum_index {α : Type u_1} {ι : Type u_4} {M : Type u_5} {N : Type u_7} [add_comm_monoid M] [add_comm_monoid N] {s : finset ι} {g : ι → α →₀ M} {h : α → M → N} (h_zero : ∀ (a : α), h a 0 = 0) (h_add : ∀ (a : α) (b₁ b₂ : M), h a (b₁ + b₂) = h a b₁ + h a b₂) : (finset.sum s fun (i : ι) => sum (g i) h) = sum (finset.sum s fun (i : ι) => g i) h := sorry

theorem prod_sum_index {α : Type u_1} {β : Type u_2} {M : Type u_5} {N : Type u_7} {P : Type u_8} [add_comm_monoid M] [add_comm_monoid N] [comm_monoid P] {f : α →₀ M} {g : α → M → β →₀ N} {h : β → N → P} (h_zero : ∀ (a : β), h a 0 = 1) (h_add : ∀ (a : β) (b₁ b₂ : N), h a (b₁ + b₂) = h a b₁ * h a b₂) : prod (sum f g) h = prod f fun (a : α) (b : M) => prod (g a b) h :=
  Eq.symm (prod_finset_sum_index h_zero h_add)

theorem multiset_sum_sum_index {α : Type u_1} {M : Type u_5} {N : Type u_7} [add_comm_monoid M] [add_comm_monoid N] (f : multiset (α →₀ M)) (h : α → M → N) (h₀ : ∀ (a : α), h a 0 = 0) (h₁ : ∀ (a : α) (b₁ b₂ : M), h a (b₁ + b₂) = h a b₁ + h a b₂) : sum (multiset.sum f) h = multiset.sum (multiset.map (fun (g : α →₀ M) => sum g h) f) := sorry

theorem multiset_map_sum {α : Type u_1} {β : Type u_2} {γ : Type u_3} {M : Type u_5} [HasZero M] {f : α →₀ M} {m : β → γ} {h : α → M → multiset β} : multiset.map m (sum f h) = sum f fun (a : α) (b : M) => multiset.map m (h a b) :=
  Eq.symm (finset.sum_hom (support f) (multiset.map m))

theorem multiset_sum_sum {α : Type u_1} {M : Type u_5} {N : Type u_7} [HasZero M] [add_comm_monoid N] {f : α →₀ M} {h : α → M → multiset N} : multiset.sum (sum f h) = sum f fun (a : α) (b : M) => multiset.sum (h a b) :=
  Eq.symm (finset.sum_hom (support f) multiset.sum)

/--
Composition with a fixed additive homomorphism is itself an additive homomorphism on functions.
-/
def map_range.add_monoid_hom {α : Type u_1} {M : Type u_5} {N : Type u_7} [add_comm_monoid M] [add_comm_monoid N] (f : M →+ N) : (α →₀ M) →+ α →₀ N :=
  add_monoid_hom.mk (map_range ⇑f sorry) sorry sorry

theorem map_range_multiset_sum {α : Type u_1} {M : Type u_5} {N : Type u_7} [add_comm_monoid M] [add_comm_monoid N] (f : M →+ N) (m : multiset (α →₀ M)) : map_range (⇑f) (add_monoid_hom.map_zero f) (multiset.sum m) =
  multiset.sum (multiset.map (fun (x : α →₀ M) => map_range (⇑f) (add_monoid_hom.map_zero f) x) m) :=
  Eq.symm (multiset.sum_hom m (map_range.add_monoid_hom f))

theorem map_range_finset_sum {α : Type u_1} {ι : Type u_4} {M : Type u_5} {N : Type u_7} [add_comm_monoid M] [add_comm_monoid N] (f : M →+ N) (s : finset ι) (g : ι → α →₀ M) : map_range (⇑f) (add_monoid_hom.map_zero f) (finset.sum s fun (x : ι) => g x) =
  finset.sum s fun (x : ι) => map_range (⇑f) (add_monoid_hom.map_zero f) (g x) := sorry

/-! ### Declarations about `map_domain` -/

/-- Given `f : α → β` and `v : α →₀ M`, `map_domain f v : β →₀ M`
  is the finitely supported function whose value at `a : β` is the sum
  of `v x` over all `x` such that `f x = a`. -/
def map_domain {α : Type u_1} {β : Type u_2} {M : Type u_5} [add_comm_monoid M] (f : α → β) (v : α →₀ M) : β →₀ M :=
  sum v fun (a : α) => single (f a)

theorem map_domain_apply {α : Type u_1} {β : Type u_2} {M : Type u_5} [add_comm_monoid M] {f : α → β} (hf : function.injective f) (x : α →₀ M) (a : α) : coe_fn (map_domain f x) (f a) = coe_fn x a := sorry

theorem map_domain_notin_range {α : Type u_1} {β : Type u_2} {M : Type u_5} [add_comm_monoid M] {f : α → β} (x : α →₀ M) (a : β) (h : ¬a ∈ set.range f) : coe_fn (map_domain f x) a = 0 := sorry

theorem map_domain_id {α : Type u_1} {M : Type u_5} [add_comm_monoid M] {v : α →₀ M} : map_domain id v = v :=
  sum_single v

theorem map_domain_comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} {M : Type u_5} [add_comm_monoid M] {v : α →₀ M} {f : α → β} {g : β → γ} : map_domain (g ∘ f) v = map_domain g (map_domain f v) :=
  Eq.symm
    (Eq.trans (sum_sum_index (fun (a : β) => single_zero) fun (a : β) (b₁ b₂ : M) => single_add)
      (finset.sum_congr rfl fun (_x : α) (_x_1 : _x ∈ support v) => sum_single_index single_zero))

theorem map_domain_single {α : Type u_1} {β : Type u_2} {M : Type u_5} [add_comm_monoid M] {f : α → β} {a : α} {b : M} : map_domain f (single a b) = single (f a) b :=
  sum_single_index single_zero

@[simp] theorem map_domain_zero {α : Type u_1} {β : Type u_2} {M : Type u_5} [add_comm_monoid M] {f : α → β} : map_domain f 0 = 0 :=
  sum_zero_index

theorem map_domain_congr {α : Type u_1} {β : Type u_2} {M : Type u_5} [add_comm_monoid M] {v : α →₀ M} {f : α → β} {g : α → β} (h : ∀ (x : α), x ∈ support v → f x = g x) : map_domain f v = map_domain g v := sorry

theorem map_domain_add {α : Type u_1} {β : Type u_2} {M : Type u_5} [add_comm_monoid M] {v₁ : α →₀ M} {v₂ : α →₀ M} {f : α → β} : map_domain f (v₁ + v₂) = map_domain f v₁ + map_domain f v₂ :=
  sum_add_index (fun (_x : α) => single_zero) fun (_x : α) (_x_1 _x_2 : M) => single_add

theorem map_domain_finset_sum {α : Type u_1} {β : Type u_2} {ι : Type u_4} {M : Type u_5} [add_comm_monoid M] {f : α → β} {s : finset ι} {v : ι → α →₀ M} : map_domain f (finset.sum s fun (i : ι) => v i) = finset.sum s fun (i : ι) => map_domain f (v i) :=
  Eq.symm (sum_finset_sum_index (fun (_x : α) => single_zero) fun (_x : α) (_x_1 _x_2 : M) => single_add)

theorem map_domain_sum {α : Type u_1} {β : Type u_2} {M : Type u_5} {N : Type u_7} [add_comm_monoid M] [HasZero N] {f : α → β} {s : α →₀ N} {v : α → N → α →₀ M} : map_domain f (sum s v) = sum s fun (a : α) (b : N) => map_domain f (v a b) :=
  Eq.symm (sum_finset_sum_index (fun (_x : α) => single_zero) fun (_x : α) (_x_1 _x_2 : M) => single_add)

theorem map_domain_support {α : Type u_1} {β : Type u_2} {M : Type u_5} [add_comm_monoid M] {f : α → β} {s : α →₀ M} : support (map_domain f s) ⊆ finset.image f (support s) := sorry

theorem sum_map_domain_index {α : Type u_1} {β : Type u_2} {M : Type u_5} {N : Type u_7} [add_comm_monoid M] [add_comm_monoid N] {f : α → β} {s : α →₀ M} {h : β → M → N} (h_zero : ∀ (a : β), h a 0 = 0) (h_add : ∀ (a : β) (b₁ b₂ : M), h a (b₁ + b₂) = h a b₁ + h a b₂) : sum (map_domain f s) h = sum s fun (a : α) (b : M) => h (f a) b :=
  Eq.trans (sum_sum_index h_zero h_add)
    (finset.sum_congr rfl fun (_x : α) (_x_1 : _x ∈ support s) => sum_single_index (h_zero (f _x)))

theorem emb_domain_eq_map_domain {α : Type u_1} {β : Type u_2} {M : Type u_5} [add_comm_monoid M] (f : α ↪ β) (v : α →₀ M) : emb_domain f v = map_domain (⇑f) v := sorry

theorem sum_map_domain_index_inj {α : Type u_1} {β : Type u_2} {M : Type u_5} {N : Type u_7} [add_comm_monoid M] [add_comm_monoid N] {f : α → β} {s : α →₀ M} {h : β → M → N} (hf : function.injective f) : sum (map_domain f s) h = sum s fun (a : α) (b : M) => h (f a) b := sorry

theorem map_domain_injective {α : Type u_1} {β : Type u_2} {M : Type u_5} [add_comm_monoid M] {f : α → β} (hf : function.injective f) : function.injective (map_domain f) := sorry

/-! ### Declarations about `comap_domain` -/

/-- Given `f : α → β`, `l : β →₀ M` and a proof `hf` that `f` is injective on
the preimage of `l.support`, `comap_domain f l hf` is the finitely supported function
from `α` to `M` given by composing `l` with `f`. -/
def comap_domain {α : Type u_1} {β : Type u_2} {M : Type u_5} [HasZero M] (f : α → β) (l : β →₀ M) (hf : set.inj_on f (f ⁻¹' ↑(support l))) : α →₀ M :=
  mk (finset.preimage (support l) f hf) (fun (a : α) => coe_fn l (f a)) sorry

@[simp] theorem comap_domain_apply {α : Type u_1} {β : Type u_2} {M : Type u_5} [HasZero M] (f : α → β) (l : β →₀ M) (hf : set.inj_on f (f ⁻¹' ↑(support l))) (a : α) : coe_fn (comap_domain f l hf) a = coe_fn l (f a) :=
  rfl

theorem sum_comap_domain {α : Type u_1} {β : Type u_2} {M : Type u_5} {N : Type u_7} [HasZero M] [add_comm_monoid N] (f : α → β) (l : β →₀ M) (g : β → M → N) (hf : set.bij_on f (f ⁻¹' ↑(support l)) ↑(support l)) : sum (comap_domain f l (set.bij_on.inj_on hf)) (g ∘ f) = sum l g := sorry

theorem eq_zero_of_comap_domain_eq_zero {α : Type u_1} {β : Type u_2} {M : Type u_5} [add_comm_monoid M] (f : α → β) (l : β →₀ M) (hf : set.bij_on f (f ⁻¹' ↑(support l)) ↑(support l)) : comap_domain f l (set.bij_on.inj_on hf) = 0 → l = 0 := sorry

theorem map_domain_comap_domain {α : Type u_1} {β : Type u_2} {M : Type u_5} [add_comm_monoid M] (f : α → β) (l : β →₀ M) (hf : function.injective f) (hl : ↑(support l) ⊆ set.range f) : map_domain f (comap_domain f l (function.injective.inj_on hf (f ⁻¹' ↑(support l)))) = l := sorry

/-! ### Declarations about `filter` -/

/-- `filter p f` is the function which is `f a` if `p a` is true and 0 otherwise. -/
def filter {α : Type u_1} {M : Type u_5} [HasZero M] (p : α → Prop) (f : α →₀ M) : α →₀ M :=
  mk (finset.filter (fun (a : α) => p a) (support f)) (fun (a : α) => ite (p a) (coe_fn f a) 0) sorry

theorem filter_apply {α : Type u_1} {M : Type u_5} [HasZero M] (p : α → Prop) (f : α →₀ M) (a : α) : coe_fn (filter p f) a = ite (p a) (coe_fn f a) 0 :=
  rfl

theorem filter_eq_indicator {α : Type u_1} {M : Type u_5} [HasZero M] (p : α → Prop) (f : α →₀ M) : ⇑(filter p f) = set.indicator (set_of fun (x : α) => p x) ⇑f :=
  rfl

@[simp] theorem filter_apply_pos {α : Type u_1} {M : Type u_5} [HasZero M] (p : α → Prop) (f : α →₀ M) {a : α} (h : p a) : coe_fn (filter p f) a = coe_fn f a :=
  if_pos h

@[simp] theorem filter_apply_neg {α : Type u_1} {M : Type u_5} [HasZero M] (p : α → Prop) (f : α →₀ M) {a : α} (h : ¬p a) : coe_fn (filter p f) a = 0 :=
  if_neg h

@[simp] theorem support_filter {α : Type u_1} {M : Type u_5} [HasZero M] (p : α → Prop) (f : α →₀ M) : support (filter p f) = finset.filter p (support f) :=
  rfl

theorem filter_zero {α : Type u_1} {M : Type u_5} [HasZero M] (p : α → Prop) : filter p 0 = 0 := sorry

@[simp] theorem filter_single_of_pos {α : Type u_1} {M : Type u_5} [HasZero M] (p : α → Prop) {a : α} {b : M} (h : p a) : filter p (single a b) = single a b := sorry

@[simp] theorem filter_single_of_neg {α : Type u_1} {M : Type u_5} [HasZero M] (p : α → Prop) {a : α} {b : M} (h : ¬p a) : filter p (single a b) = 0 := sorry

theorem filter_pos_add_filter_neg {α : Type u_1} {M : Type u_5} [add_monoid M] (f : α →₀ M) (p : α → Prop) : filter p f + filter (fun (a : α) => ¬p a) f = f :=
  coe_fn_injective (set.indicator_self_add_compl (set_of fun (x : α) => p x) ⇑f)

/-! ### Declarations about `frange` -/

/-- `frange f` is the image of `f` on the support of `f`. -/
def frange {α : Type u_1} {M : Type u_5} [HasZero M] (f : α →₀ M) : finset M :=
  finset.image (⇑f) (support f)

theorem mem_frange {α : Type u_1} {M : Type u_5} [HasZero M] {f : α →₀ M} {y : M} : y ∈ frange f ↔ y ≠ 0 ∧ ∃ (x : α), coe_fn f x = y := sorry

theorem zero_not_mem_frange {α : Type u_1} {M : Type u_5} [HasZero M] {f : α →₀ M} : ¬0 ∈ frange f :=
  fun (H : 0 ∈ frange f) => and.left (iff.mp mem_frange H) rfl

theorem frange_single {α : Type u_1} {M : Type u_5} [HasZero M] {x : α} {y : M} : frange (single x y) ⊆ singleton y := sorry

/-! ### Declarations about `subtype_domain` -/

/-- `subtype_domain p f` is the restriction of the finitely supported function
  `f` to the subtype `p`. -/
def subtype_domain {α : Type u_1} {M : Type u_5} [HasZero M] (p : α → Prop) (f : α →₀ M) : Subtype p →₀ M :=
  mk (finset.subtype p (support f)) (⇑f ∘ coe) sorry

@[simp] theorem support_subtype_domain {α : Type u_1} {M : Type u_5} [HasZero M] {p : α → Prop} {f : α →₀ M} : support (subtype_domain p f) = finset.subtype p (support f) :=
  rfl

@[simp] theorem subtype_domain_apply {α : Type u_1} {M : Type u_5} [HasZero M] {p : α → Prop} {a : Subtype p} {v : α →₀ M} : coe_fn (subtype_domain p v) a = coe_fn v (subtype.val a) :=
  rfl

@[simp] theorem subtype_domain_zero {α : Type u_1} {M : Type u_5} [HasZero M] {p : α → Prop} : subtype_domain p 0 = 0 :=
  rfl

theorem subtype_domain_eq_zero_iff' {α : Type u_1} {M : Type u_5} [HasZero M] {p : α → Prop} {f : α →₀ M} : subtype_domain p f = 0 ↔ ∀ (x : α), p x → coe_fn f x = 0 := sorry

theorem subtype_domain_eq_zero_iff {α : Type u_1} {M : Type u_5} [HasZero M] {p : α → Prop} {f : α →₀ M} (hf : ∀ (x : α), x ∈ support f → p x) : subtype_domain p f = 0 ↔ f = 0 := sorry

theorem prod_subtype_domain_index {α : Type u_1} {M : Type u_5} {N : Type u_7} [HasZero M] {p : α → Prop} [comm_monoid N] {v : α →₀ M} {h : α → M → N} (hp : ∀ (x : α), x ∈ support v → p x) : (prod (subtype_domain p v) fun (a : Subtype p) (b : M) => h (↑a) b) = prod v h := sorry

@[simp] theorem subtype_domain_add {α : Type u_1} {M : Type u_5} [add_monoid M] {p : α → Prop} {v : α →₀ M} {v' : α →₀ M} : subtype_domain p (v + v') = subtype_domain p v + subtype_domain p v' :=
  ext fun (_x : Subtype p) => rfl

protected instance subtype_domain.is_add_monoid_hom {α : Type u_1} {M : Type u_5} [add_monoid M] {p : α → Prop} : is_add_monoid_hom (subtype_domain p) :=
  is_add_monoid_hom.mk subtype_domain_zero

/-- `finsupp.filter` as an `add_monoid_hom`. -/
def filter_add_hom {α : Type u_1} {M : Type u_5} [add_monoid M] (p : α → Prop) : (α →₀ M) →+ α →₀ M :=
  add_monoid_hom.mk (filter p) sorry sorry

@[simp] theorem filter_add {α : Type u_1} {M : Type u_5} [add_monoid M] {p : α → Prop} {v : α →₀ M} {v' : α →₀ M} : filter p (v + v') = filter p v + filter p v' :=
  add_monoid_hom.map_add (filter_add_hom p) v v'

theorem subtype_domain_sum {α : Type u_1} {ι : Type u_4} {M : Type u_5} [add_comm_monoid M] {p : α → Prop} {s : finset ι} {h : ι → α →₀ M} : subtype_domain p (finset.sum s fun (c : ι) => h c) = finset.sum s fun (c : ι) => subtype_domain p (h c) :=
  Eq.symm (finset.sum_hom s (subtype_domain p))

theorem subtype_domain_finsupp_sum {α : Type u_1} {β : Type u_2} {M : Type u_5} {N : Type u_7} [add_comm_monoid M] {p : α → Prop} [HasZero N] {s : β →₀ N} {h : β → N → α →₀ M} : subtype_domain p (sum s h) = sum s fun (c : β) (d : N) => subtype_domain p (h c d) :=
  subtype_domain_sum

theorem filter_sum {α : Type u_1} {ι : Type u_4} {M : Type u_5} [add_comm_monoid M] {p : α → Prop} (s : finset ι) (f : ι → α →₀ M) : filter p (finset.sum s fun (a : ι) => f a) = finset.sum s fun (a : ι) => filter p (f a) :=
  add_monoid_hom.map_sum (filter_add_hom p) f s

theorem filter_eq_sum {α : Type u_1} {M : Type u_5} [add_comm_monoid M] (p : α → Prop) (f : α →₀ M) : filter p f = finset.sum (finset.filter p (support f)) fun (i : α) => single i (coe_fn f i) := sorry

@[simp] theorem subtype_domain_neg {α : Type u_1} {G : Type u_9} [add_group G] {p : α → Prop} {v : α →₀ G} : subtype_domain p (-v) = -subtype_domain p v :=
  ext fun (_x : Subtype p) => rfl

@[simp] theorem subtype_domain_sub {α : Type u_1} {G : Type u_9} [add_group G] {p : α → Prop} {v : α →₀ G} {v' : α →₀ G} : subtype_domain p (v - v') = subtype_domain p v - subtype_domain p v' :=
  ext fun (_x : Subtype p) => rfl

/-! ### Declarations relating `finsupp` to `multiset` -/

/-- Given `f : α →₀ ℕ`, `f.to_multiset` is the multiset with multiplicities given by the values of
`f` on the elements of `α`. We define this function as an `add_equiv`. -/
def to_multiset {α : Type u_1} : (α →₀ ℕ) ≃+ multiset α :=
  add_equiv.mk (fun (f : α →₀ ℕ) => sum f fun (a : α) (n : ℕ) => n •ℕ singleton a)
    (fun (s : multiset α) => mk (multiset.to_finset s) (fun (a : α) => multiset.count a s) sorry) sorry sorry sorry

theorem to_multiset_zero {α : Type u_1} : coe_fn to_multiset 0 = 0 :=
  rfl

theorem to_multiset_add {α : Type u_1} (m : α →₀ ℕ) (n : α →₀ ℕ) : coe_fn to_multiset (m + n) = coe_fn to_multiset m + coe_fn to_multiset n :=
  add_equiv.map_add to_multiset m n

theorem to_multiset_apply {α : Type u_1} (f : α →₀ ℕ) : coe_fn to_multiset f = sum f fun (a : α) (n : ℕ) => n •ℕ singleton a :=
  rfl

@[simp] theorem to_multiset_single {α : Type u_1} (a : α) (n : ℕ) : coe_fn to_multiset (single a n) = n •ℕ singleton a := sorry

theorem card_to_multiset {α : Type u_1} (f : α →₀ ℕ) : coe_fn multiset.card (coe_fn to_multiset f) = sum f fun (a : α) => id := sorry

theorem to_multiset_map {α : Type u_1} {β : Type u_2} (f : α →₀ ℕ) (g : α → β) : multiset.map g (coe_fn to_multiset f) = coe_fn to_multiset (map_domain g f) := sorry

@[simp] theorem prod_to_multiset {M : Type u_5} [comm_monoid M] (f : M →₀ ℕ) : multiset.prod (coe_fn to_multiset f) = prod f fun (a : M) (n : ℕ) => a ^ n := sorry

@[simp] theorem to_finset_to_multiset {α : Type u_1} (f : α →₀ ℕ) : multiset.to_finset (coe_fn to_multiset f) = support f := sorry

@[simp] theorem count_to_multiset {α : Type u_1} (f : α →₀ ℕ) (a : α) : multiset.count a (coe_fn to_multiset f) = coe_fn f a := sorry

theorem mem_support_multiset_sum {α : Type u_1} {M : Type u_5} [add_comm_monoid M] {s : multiset (α →₀ M)} (a : α) : a ∈ support (multiset.sum s) → ∃ (f : α →₀ M), ∃ (H : f ∈ s), a ∈ support f := sorry

theorem mem_support_finset_sum {α : Type u_1} {ι : Type u_4} {M : Type u_5} [add_comm_monoid M] {s : finset ι} {h : ι → α →₀ M} (a : α) (ha : a ∈ support (finset.sum s fun (c : ι) => h c)) : ∃ (c : ι), ∃ (H : c ∈ s), a ∈ support (h c) := sorry

@[simp] theorem mem_to_multiset {α : Type u_1} (f : α →₀ ℕ) (i : α) : i ∈ coe_fn to_multiset f ↔ i ∈ support f := sorry

/-! ### Declarations about `curry` and `uncurry` -/

/-- Given a finitely supported function `f` from a product type `α × β` to `γ`,
`curry f` is the "curried" finitely supported function from `α` to the type of
finitely supported functions from `β` to `γ`. -/
protected def curry {α : Type u_1} {β : Type u_2} {M : Type u_5} [add_comm_monoid M] (f : α × β →₀ M) : α →₀ β →₀ M :=
  sum f fun (p : α × β) (c : M) => single (prod.fst p) (single (prod.snd p) c)

theorem sum_curry_index {α : Type u_1} {β : Type u_2} {M : Type u_5} {N : Type u_7} [add_comm_monoid M] [add_comm_monoid N] (f : α × β →₀ M) (g : α → β → M → N) (hg₀ : ∀ (a : α) (b : β), g a b 0 = 0) (hg₁ : ∀ (a : α) (b : β) (c₀ c₁ : M), g a b (c₀ + c₁) = g a b c₀ + g a b c₁) : (sum (finsupp.curry f) fun (a : α) (f : β →₀ M) => sum f (g a)) =
  sum f fun (p : α × β) (c : M) => g (prod.fst p) (prod.snd p) c := sorry

/-- Given a finitely supported function `f` from `α` to the type of
finitely supported functions from `β` to `M`,
`uncurry f` is the "uncurried" finitely supported function from `α × β` to `M`. -/
protected def uncurry {α : Type u_1} {β : Type u_2} {M : Type u_5} [add_comm_monoid M] (f : α →₀ β →₀ M) : α × β →₀ M :=
  sum f fun (a : α) (g : β →₀ M) => sum g fun (b : β) (c : M) => single (a, b) c

/-- `finsupp_prod_equiv` defines the `equiv` between `((α × β) →₀ M)` and `(α →₀ (β →₀ M))` given by
currying and uncurrying. -/
def finsupp_prod_equiv {α : Type u_1} {β : Type u_2} {M : Type u_5} [add_comm_monoid M] : (α × β →₀ M) ≃ (α →₀ β →₀ M) :=
  equiv.mk finsupp.curry finsupp.uncurry sorry sorry

theorem filter_curry {α : Type u_1} {β : Type u_2} {M : Type u_5} [add_comm_monoid M] (f : α × β →₀ M) (p : α → Prop) : finsupp.curry (filter (fun (a : α × β) => p (prod.fst a)) f) = filter p (finsupp.curry f) := sorry

theorem support_curry {α : Type u_1} {β : Type u_2} {M : Type u_5} [add_comm_monoid M] (f : α × β →₀ M) : support (finsupp.curry f) ⊆ finset.image prod.fst (support f) := sorry

/--
Scalar multiplication by a group element g,
given by precomposition with the action of g⁻¹ on the domain.
-/
def comap_has_scalar {α : Type u_1} {M : Type u_5} {G : Type u_9} [group G] [mul_action G α] [add_comm_monoid M] : has_scalar G (α →₀ M) :=
  has_scalar.mk fun (g : G) (f : α →₀ M) => comap_domain (fun (a : α) => g⁻¹ • a) f sorry

/--
Scalar multiplication by a group element,
given by precomposition with the action of g⁻¹ on the domain,
is multiplicative in g.
-/
def comap_mul_action {α : Type u_1} {M : Type u_5} {G : Type u_9} [group G] [mul_action G α] [add_comm_monoid M] : mul_action G (α →₀ M) :=
  mul_action.mk sorry sorry

/--
Scalar multiplication by a group element,
given by precomposition with the action of g⁻¹ on the domain,
is additive in the second argument.
-/
def comap_distrib_mul_action {α : Type u_1} {M : Type u_5} {G : Type u_9} [group G] [mul_action G α] [add_comm_monoid M] : distrib_mul_action G (α →₀ M) :=
  distrib_mul_action.mk sorry sorry

/--
Scalar multiplication by a group element on finitely supported functions on a group,
given by precomposition with the action of g⁻¹. -/
def comap_distrib_mul_action_self {M : Type u_5} {G : Type u_9} [group G] [add_comm_monoid M] : distrib_mul_action G (G →₀ M) :=
  comap_distrib_mul_action

@[simp] theorem comap_smul_single {α : Type u_1} {M : Type u_5} {G : Type u_9} [group G] [mul_action G α] [add_comm_monoid M] (g : G) (a : α) (b : M) : g • single a b = single (g • a) b := sorry

@[simp] theorem comap_smul_apply {α : Type u_1} {M : Type u_5} {G : Type u_9} [group G] [mul_action G α] [add_comm_monoid M] (g : G) (f : α →₀ M) (a : α) : coe_fn (g • f) a = coe_fn f (g⁻¹ • a) :=
  rfl

protected instance has_scalar {α : Type u_1} {M : Type u_5} {R : Type u_11} [semiring R] [add_comm_monoid M] [semimodule R M] : has_scalar R (α →₀ M) :=
  has_scalar.mk fun (a : R) (v : α →₀ M) => map_range (has_scalar.smul a) sorry v

/-!
Throughout this section, some `semiring` arguments are specified with `{}` instead of `[]`.
See note [implicit instance arguments].
-/

@[simp] theorem smul_apply' (α : Type u_1) (M : Type u_5) {R : Type u_11} {_x : semiring R} [add_comm_monoid M] [semimodule R M] {a : α} {b : R} {v : α →₀ M} : coe_fn (b • v) a = b • coe_fn v a :=
  rfl

protected instance semimodule (α : Type u_1) (M : Type u_5) {R : Type u_11} [semiring R] [add_comm_monoid M] [semimodule R M] : semimodule R (α →₀ M) :=
  semimodule.mk sorry sorry

theorem support_smul {α : Type u_1} {M : Type u_5} {R : Type u_11} {_x : semiring R} [add_comm_monoid M] [semimodule R M] {b : R} {g : α →₀ M} : support (b • g) ⊆ support g := sorry

@[simp] theorem filter_smul {α : Type u_1} {M : Type u_5} {R : Type u_11} {p : α → Prop} {_x : semiring R} [add_comm_monoid M] [semimodule R M] {b : R} {v : α →₀ M} : filter p (b • v) = b • filter p v :=
  coe_fn_injective (set.indicator_smul (set_of fun (x : α) => p x) b ⇑v)

theorem map_domain_smul {α : Type u_1} {β : Type u_2} {M : Type u_5} {R : Type u_11} {_x : semiring R} [add_comm_monoid M] [semimodule R M] {f : α → β} (b : R) (v : α →₀ M) : map_domain f (b • v) = b • map_domain f v := sorry

@[simp] theorem smul_single {α : Type u_1} {M : Type u_5} {R : Type u_11} {_x : semiring R} [add_comm_monoid M] [semimodule R M] (c : R) (a : α) (b : M) : c • single a b = single a (c • b) :=
  map_range_single

@[simp] theorem smul_single' {α : Type u_1} {R : Type u_11} {_x : semiring R} (c : R) (a : α) (b : R) : c • single a b = single a (c * b) :=
  smul_single c a b

theorem smul_single_one {α : Type u_1} {R : Type u_11} [semiring R] (a : α) (b : R) : b • single a 1 = single a b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (b • single a 1 = single a b)) (smul_single b a 1)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (single a (b • 1) = single a b)) smul_eq_mul))
      (eq.mpr (id (Eq._oldrec (Eq.refl (single a (b * 1) = single a b)) (mul_one b))) (Eq.refl (single a b))))

@[simp] theorem smul_apply {α : Type u_1} {R : Type u_11} [semiring R] {a : α} {b : R} {v : α →₀ R} : coe_fn (b • v) a = b • coe_fn v a :=
  rfl

theorem sum_smul_index {α : Type u_1} {M : Type u_5} {R : Type u_11} [semiring R] [add_comm_monoid M] {g : α →₀ R} {b : R} {h : α → R → M} (h0 : ∀ (i : α), h i 0 = 0) : sum (b • g) h = sum g fun (i : α) (a : R) => h i (b * a) :=
  sum_map_range_index h0

theorem sum_smul_index' {α : Type u_1} {M : Type u_5} {N : Type u_7} {R : Type u_11} [semiring R] [add_comm_monoid M] [semimodule R M] [add_comm_monoid N] {g : α →₀ M} {b : R} {h : α → M → N} (h0 : ∀ (i : α), h i 0 = 0) : sum (b • g) h = sum g fun (i : α) (c : M) => h i (b • c) :=
  sum_map_range_index h0

theorem sum_mul {α : Type u_1} {R : Type u_11} {S : Type u_12} [semiring R] [semiring S] (b : S) (s : α →₀ R) {f : α → R → S} : sum s f * b = sum s fun (a : α) (c : R) => f a c * b := sorry

theorem mul_sum {α : Type u_1} {R : Type u_11} {S : Type u_12} [semiring R] [semiring S] (b : S) (s : α →₀ R) {f : α → R → S} : b * sum s f = sum s fun (a : α) (c : R) => b * f a c := sorry

protected instance unique_of_right {α : Type u_1} {R : Type u_11} [semiring R] [subsingleton R] : unique (α →₀ R) :=
  unique.mk { default := Inhabited.default } sorry

/-- Given an `add_comm_monoid M` and `s : set α`, `restrict_support_equiv s M` is the `equiv`
between the subtype of finitely supported functions with support contained in `s` and
the type of finitely supported functions from `s`. -/
def restrict_support_equiv {α : Type u_1} (s : set α) (M : Type u_2) [add_comm_monoid M] : (Subtype fun (f : α →₀ M) => ↑(support f) ⊆ s) ≃ (↥s →₀ M) :=
  equiv.mk
    (fun (f : Subtype fun (f : α →₀ M) => ↑(support f) ⊆ s) => subtype_domain (fun (x : α) => x ∈ s) (subtype.val f))
    (fun (f : ↥s →₀ M) => { val := map_domain subtype.val f, property := sorry }) sorry sorry

/-- Given `add_comm_monoid M` and `e : α ≃ β`, `dom_congr e` is the corresponding `equiv` between
`α →₀ M` and `β →₀ M`. -/
protected def dom_congr {α : Type u_1} {β : Type u_2} {M : Type u_5} [add_comm_monoid M] (e : α ≃ β) : (α →₀ M) ≃+ (β →₀ M) :=
  add_equiv.mk (map_domain ⇑e) (map_domain ⇑(equiv.symm e)) sorry sorry sorry

end finsupp


namespace finsupp


/-! ### Declarations about sigma types -/

/-- Given `l`, a finitely supported function from the sigma type `Σ (i : ι), αs i` to `M` and
an index element `i : ι`, `split l i` is the `i`th component of `l`,
a finitely supported function from `as i` to `M`. -/
def split {ι : Type u_4} {M : Type u_5} {αs : ι → Type u_13} [HasZero M] (l : (sigma fun (i : ι) => αs i) →₀ M) (i : ι) : αs i →₀ M :=
  comap_domain (sigma.mk i) l sorry

theorem split_apply {ι : Type u_4} {M : Type u_5} {αs : ι → Type u_13} [HasZero M] (l : (sigma fun (i : ι) => αs i) →₀ M) (i : ι) (x : αs i) : coe_fn (split l i) x = coe_fn l (sigma.mk i x) := sorry

/-- Given `l`, a finitely supported function from the sigma type `Σ (i : ι), αs i` to `β`,
`split_support l` is the finset of indices in `ι` that appear in the support of `l`. -/
def split_support {ι : Type u_4} {M : Type u_5} {αs : ι → Type u_13} [HasZero M] (l : (sigma fun (i : ι) => αs i) →₀ M) : finset ι :=
  finset.image sigma.fst (support l)

theorem mem_split_support_iff_nonzero {ι : Type u_4} {M : Type u_5} {αs : ι → Type u_13} [HasZero M] (l : (sigma fun (i : ι) => αs i) →₀ M) (i : ι) : i ∈ split_support l ↔ split l i ≠ 0 := sorry

/-- Given `l`, a finitely supported function from the sigma type `Σ i, αs i` to `β` and
an `ι`-indexed family `g` of functions from `(αs i →₀ β)` to `γ`, `split_comp` defines a
finitely supported function from the index type `ι` to `γ` given by composing `g i` with
`split l i`. -/
def split_comp {ι : Type u_4} {M : Type u_5} {N : Type u_7} {αs : ι → Type u_13} [HasZero M] (l : (sigma fun (i : ι) => αs i) →₀ M) [HasZero N] (g : (i : ι) → (αs i →₀ M) → N) (hg : ∀ (i : ι) (x : αs i →₀ M), x = 0 ↔ g i x = 0) : ι →₀ N :=
  mk (split_support l) (fun (i : ι) => g i (split l i)) sorry

theorem sigma_support {ι : Type u_4} {M : Type u_5} {αs : ι → Type u_13} [HasZero M] (l : (sigma fun (i : ι) => αs i) →₀ M) : support l = finset.sigma (split_support l) fun (i : ι) => support (split l i) := sorry

theorem sigma_sum {ι : Type u_4} {M : Type u_5} {N : Type u_7} {αs : ι → Type u_13} [HasZero M] (l : (sigma fun (i : ι) => αs i) →₀ M) [add_comm_monoid N] (f : (sigma fun (i : ι) => αs i) → M → N) : sum l f = finset.sum (split_support l) fun (i : ι) => sum (split l i) fun (a : αs i) (b : M) => f (sigma.mk i a) b := sorry

end finsupp


/-! ### Declarations relating `multiset` to `finsupp` -/

namespace multiset


/-- Given a multiset `s`, `s.to_finsupp` returns the finitely supported function on `ℕ` given by
the multiplicities of the elements of `s`. -/
def to_finsupp {α : Type u_1} : multiset α ≃+ (α →₀ ℕ) :=
  add_equiv.symm finsupp.to_multiset

@[simp] theorem to_finsupp_support {α : Type u_1} (s : multiset α) : finsupp.support (coe_fn to_finsupp s) = to_finset s :=
  rfl

@[simp] theorem to_finsupp_apply {α : Type u_1} (s : multiset α) (a : α) : coe_fn (coe_fn to_finsupp s) a = count a s :=
  rfl

theorem to_finsupp_zero {α : Type u_1} : coe_fn to_finsupp 0 = 0 :=
  add_equiv.map_zero to_finsupp

theorem to_finsupp_add {α : Type u_1} (s : multiset α) (t : multiset α) : coe_fn to_finsupp (s + t) = coe_fn to_finsupp s + coe_fn to_finsupp t :=
  add_equiv.map_add to_finsupp s t

@[simp] theorem to_finsupp_singleton {α : Type u_1} (a : α) : coe_fn to_finsupp (a ::ₘ 0) = finsupp.single a 1 := sorry

@[simp] theorem to_finsupp_to_multiset {α : Type u_1} (s : multiset α) : coe_fn finsupp.to_multiset (coe_fn to_finsupp s) = s :=
  add_equiv.apply_symm_apply finsupp.to_multiset s

theorem to_finsupp_eq_iff {α : Type u_1} {s : multiset α} {f : α →₀ ℕ} : coe_fn to_finsupp s = f ↔ s = coe_fn finsupp.to_multiset f :=
  add_equiv.symm_apply_eq finsupp.to_multiset

end multiset


@[simp] theorem finsupp.to_multiset_to_finsupp {α : Type u_1} (f : α →₀ ℕ) : coe_fn multiset.to_finsupp (coe_fn finsupp.to_multiset f) = f :=
  add_equiv.symm_apply_apply finsupp.to_multiset f

/-! ### Declarations about order(ed) instances on `finsupp` -/

namespace finsupp


protected instance preorder {α : Type u_1} {M : Type u_5} [preorder M] [HasZero M] : preorder (α →₀ M) :=
  preorder.mk (fun (f g : α →₀ M) => ∀ (s : α), coe_fn f s ≤ coe_fn g s)
    (fun (a b : α →₀ M) => (∀ (s : α), coe_fn a s ≤ coe_fn b s) ∧ ¬∀ (s : α), coe_fn b s ≤ coe_fn a s) sorry sorry

protected instance partial_order {α : Type u_1} {M : Type u_5} [partial_order M] [HasZero M] : partial_order (α →₀ M) :=
  partial_order.mk preorder.le preorder.lt sorry sorry sorry

protected instance add_left_cancel_semigroup {α : Type u_1} {M : Type u_5} [ordered_cancel_add_comm_monoid M] : add_left_cancel_semigroup (α →₀ M) :=
  add_left_cancel_semigroup.mk add_monoid.add sorry sorry

protected instance add_right_cancel_semigroup {α : Type u_1} {M : Type u_5} [ordered_cancel_add_comm_monoid M] : add_right_cancel_semigroup (α →₀ M) :=
  add_right_cancel_semigroup.mk add_monoid.add sorry sorry

protected instance ordered_cancel_add_comm_monoid {α : Type u_1} {M : Type u_5} [ordered_cancel_add_comm_monoid M] : ordered_cancel_add_comm_monoid (α →₀ M) :=
  ordered_cancel_add_comm_monoid.mk add_comm_monoid.add sorry sorry add_comm_monoid.zero sorry sorry sorry sorry
    partial_order.le partial_order.lt sorry sorry sorry sorry sorry

theorem le_def {α : Type u_1} {M : Type u_5} [preorder M] [HasZero M] {f : α →₀ M} {g : α →₀ M} : f ≤ g ↔ ∀ (x : α), coe_fn f x ≤ coe_fn g x :=
  iff.rfl

theorem le_iff {α : Type u_1} {M : Type u_5} [canonically_ordered_add_monoid M] (f : α →₀ M) (g : α →₀ M) : f ≤ g ↔ ∀ (s : α), s ∈ support f → coe_fn f s ≤ coe_fn g s := sorry

@[simp] theorem add_eq_zero_iff {α : Type u_1} {M : Type u_5} [canonically_ordered_add_monoid M] (f : α →₀ M) (g : α →₀ M) : f + g = 0 ↔ f = 0 ∧ g = 0 := sorry

/-- `finsupp.to_multiset` as an order isomorphism. -/
def order_iso_multiset {α : Type u_1} : (α →₀ ℕ) ≃o multiset α :=
  rel_iso.mk (add_equiv.to_equiv to_multiset) sorry

@[simp] theorem coe_order_iso_multiset {α : Type u_1} : ⇑order_iso_multiset = ⇑to_multiset :=
  rfl

@[simp] theorem coe_order_iso_multiset_symm {α : Type u_1} : ⇑(order_iso.symm order_iso_multiset) = ⇑multiset.to_finsupp :=
  rfl

theorem to_multiset_strict_mono {α : Type u_1} : strict_mono ⇑to_multiset :=
  order_iso.strict_mono order_iso_multiset

theorem sum_id_lt_of_lt {α : Type u_1} (m : α →₀ ℕ) (n : α →₀ ℕ) (h : m < n) : (sum m fun (_x : α) => id) < sum n fun (_x : α) => id := sorry

/-- The order on `σ →₀ ℕ` is well-founded.-/
theorem lt_wf (α : Type u_1) : well_founded Less :=
  subrelation.wf sum_id_lt_of_lt (inv_image.wf (fun (x : α →₀ ℕ) => sum x fun (_x : α) => id) nat.lt_wf)

protected instance decidable_le (α : Type u_1) : DecidableRel LessEq :=
  fun (m n : α →₀ ℕ) => eq.mpr sorry finset.decidable_dforall_finset

@[simp] theorem nat_add_sub_cancel {α : Type u_1} (f : α →₀ ℕ) (g : α →₀ ℕ) : f + g - g = f :=
  ext fun (a : α) => nat.add_sub_cancel (coe_fn f a) (coe_fn g a)

@[simp] theorem nat_add_sub_cancel_left {α : Type u_1} (f : α →₀ ℕ) (g : α →₀ ℕ) : f + g - f = g :=
  ext fun (a : α) => nat.add_sub_cancel_left (coe_fn f a) (coe_fn g a)

theorem nat_add_sub_of_le {α : Type u_1} {f : α →₀ ℕ} {g : α →₀ ℕ} (h : f ≤ g) : f + (g - f) = g :=
  ext fun (a : α) => nat.add_sub_of_le (h a)

theorem nat_sub_add_cancel {α : Type u_1} {f : α →₀ ℕ} {g : α →₀ ℕ} (h : f ≤ g) : g - f + f = g :=
  ext fun (a : α) => nat.sub_add_cancel (h a)

protected instance canonically_ordered_add_monoid {α : Type u_1} : canonically_ordered_add_monoid (α →₀ ℕ) :=
  canonically_ordered_add_monoid.mk ordered_add_comm_monoid.add sorry ordered_add_comm_monoid.zero sorry sorry sorry
    ordered_add_comm_monoid.le ordered_add_comm_monoid.lt sorry sorry sorry sorry sorry 0 sorry sorry

/-- The `finsupp` counterpart of `multiset.antidiagonal`: the antidiagonal of
`s : α →₀ ℕ` consists of all pairs `(t₁, t₂) : (α →₀ ℕ) × (α →₀ ℕ)` such that `t₁ + t₂ = s`.
The finitely supported function `antidiagonal s` is equal to the multiplicities of these pairs. -/
def antidiagonal {α : Type u_1} (f : α →₀ ℕ) : (α →₀ ℕ) × (α →₀ ℕ) →₀ ℕ :=
  coe_fn multiset.to_finsupp
    (multiset.map (prod.map ⇑multiset.to_finsupp ⇑multiset.to_finsupp) (multiset.antidiagonal (coe_fn to_multiset f)))

@[simp] theorem mem_antidiagonal_support {α : Type u_1} {f : α →₀ ℕ} {p : (α →₀ ℕ) × (α →₀ ℕ)} : p ∈ support (antidiagonal f) ↔ prod.fst p + prod.snd p = f := sorry

theorem swap_mem_antidiagonal_support {α : Type u_1} {n : α →₀ ℕ} {f : (α →₀ ℕ) × (α →₀ ℕ)} : prod.swap f ∈ support (antidiagonal n) ↔ f ∈ support (antidiagonal n) := sorry

theorem antidiagonal_support_filter_fst_eq {α : Type u_1} (f : α →₀ ℕ) (g : α →₀ ℕ) : finset.filter (fun (p : (α →₀ ℕ) × (α →₀ ℕ)) => prod.fst p = g) (support (antidiagonal f)) =
  ite (g ≤ f) (singleton (g, f - g)) ∅ := sorry

theorem antidiagonal_support_filter_snd_eq {α : Type u_1} (f : α →₀ ℕ) (g : α →₀ ℕ) : finset.filter (fun (p : (α →₀ ℕ) × (α →₀ ℕ)) => prod.snd p = g) (support (antidiagonal f)) =
  ite (g ≤ f) (singleton (f - g, g)) ∅ := sorry

@[simp] theorem antidiagonal_zero {α : Type u_1} : antidiagonal 0 = single (0, 0) 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (antidiagonal 0 = single (0, 0) 1)) (Eq.symm (multiset.to_finsupp_singleton (0, 0)))))
    (Eq.refl (antidiagonal 0))

theorem sum_antidiagonal_support_swap {α : Type u_1} {M : Type u_2} [add_comm_monoid M] (n : α →₀ ℕ) (f : (α →₀ ℕ) → (α →₀ ℕ) → M) : (finset.sum (support (antidiagonal n)) fun (p : (α →₀ ℕ) × (α →₀ ℕ)) => f (prod.fst p) (prod.snd p)) =
  finset.sum (support (antidiagonal n)) fun (p : (α →₀ ℕ) × (α →₀ ℕ)) => f (prod.snd p) (prod.fst p) := sorry

/-- The set `{m : α →₀ ℕ | m ≤ n}` as a `finset`. -/
def Iic_finset {α : Type u_1} (n : α →₀ ℕ) : finset (α →₀ ℕ) :=
  finset.image prod.fst (support (antidiagonal n))

@[simp] theorem mem_Iic_finset {α : Type u_1} {m : α →₀ ℕ} {n : α →₀ ℕ} : m ∈ Iic_finset n ↔ m ≤ n := sorry

@[simp] theorem coe_Iic_finset {α : Type u_1} (n : α →₀ ℕ) : ↑(Iic_finset n) = set.Iic n := sorry

/-- Let `n : α →₀ ℕ` be a finitely supported function.
The set of `m : α →₀ ℕ` that are coordinatewise less than or equal to `n`,
is a finite set. -/
theorem finite_le_nat {α : Type u_1} (n : α →₀ ℕ) : set.finite (set_of fun (m : α →₀ ℕ) => m ≤ n) := sorry

/-- Let `n : α →₀ ℕ` be a finitely supported function.
The set of `m : α →₀ ℕ` that are coordinatewise less than or equal to `n`,
but not equal to `n` everywhere, is a finite set. -/
theorem finite_lt_nat {α : Type u_1} (n : α →₀ ℕ) : set.finite (set_of fun (m : α →₀ ℕ) => m < n) :=
  set.finite.subset (finite_le_nat n) fun (m : α →₀ ℕ) => le_of_lt

end finsupp


namespace multiset


theorem to_finsuppstrict_mono {α : Type u_1} : strict_mono ⇑to_finsupp :=
  order_iso.strict_mono (order_iso.symm finsupp.order_iso_multiset)

