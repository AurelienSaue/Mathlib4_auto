/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.uniform_space.uniform_embedding
import Mathlib.PostPort

universes u l u_1 u_2 u_3 u_4 

namespace Mathlib

/-!
# Abstract theory of Hausdorff completions of uniform spaces

This file characterizes Hausdorff completions of a uniform space α as complete Hausdorff spaces
equipped with a map from α which has dense image and induce the original uniform structure on α.
Assuming these properties we "extend" uniformly continuous maps from α to complete Hausdorff spaces
to the completions of α. This is the universal property expected from a completion.
It is then used to extend uniformly continuous maps from α to α' to maps between
completions of α and α'.

This file does not construct any such completion, it only study consequences of their existence.
The first advantage is that formal properties are clearly highlighted without interference from
construction details. The second advantage is that this framework can then be used to compare
different completion constructions. See `topology/uniform_space/compare_reals` for an example.
Of course the comparison comes from the universal property as usual.

A general explicit construction of completions is done in `uniform_space/completion`, leading
to a functor from uniform spaces to complete Hausdorff uniform spaces that is left adjoint to the
inclusion, see `uniform_space/UniformSpace` for the category packaging.

## Implementation notes

A tiny technical advantage of using a characteristic predicate such as the properties listed in
`abstract_completion` instead of stating the universal property is that the universal property
derived from the predicate is more universe polymorphic.

## References

We don't know any traditional text discussing this. Real world mathematics simply silently
identify the results of any two constructions that lead to something one could reasonnably
call a completion.

## Tags

uniform spaces, completion, universal property
-/

/-- A completion of `α` is the data of a complete separated uniform space (from the same universe)
and a map from `α` with dense range and inducing the original uniform structure on `α`. -/
structure abstract_completion (α : Type u) [uniform_space α] where
  space : Type u
  coe : α → space
  uniform_struct : uniform_space space
  complete : complete_space space
  separation : separated_space space
  uniform_inducing : uniform_inducing coe
  dense : dense_range coe

namespace abstract_completion


theorem closure_range {α : Type u_1} [uniform_space α] (pkg : abstract_completion α) :
    closure (set.range (coe pkg)) = set.univ :=
  dense_range.closure_range (dense pkg)

theorem dense_inducing {α : Type u_1} [uniform_space α] (pkg : abstract_completion α) :
    dense_inducing (coe pkg) :=
  dense_inducing.mk (uniform_inducing.inducing (uniform_inducing pkg)) (dense pkg)

theorem uniform_continuous_coe {α : Type u_1} [uniform_space α] (pkg : abstract_completion α) :
    uniform_continuous (coe pkg) :=
  uniform_inducing.uniform_continuous (uniform_inducing pkg)

theorem continuous_coe {α : Type u_1} [uniform_space α] (pkg : abstract_completion α) :
    continuous (coe pkg) :=
  uniform_continuous.continuous (uniform_continuous_coe pkg)

theorem induction_on {α : Type u_1} [uniform_space α] (pkg : abstract_completion α)
    {p : space pkg → Prop} (a : space pkg) (hp : is_closed (set_of fun (a : space pkg) => p a))
    (ih : ∀ (a : α), p (coe pkg a)) : p a :=
  is_closed_property (dense pkg) hp ih a

protected theorem funext {α : Type u_1} [uniform_space α] (pkg : abstract_completion α)
    {β : Type u_2} [uniform_space β] [t2_space β] {f : space pkg → β} {g : space pkg → β}
    (hf : continuous f) (hg : continuous g) (h : ∀ (a : α), f (coe pkg a) = g (coe pkg a)) :
    f = g :=
  funext fun (a : space pkg) => induction_on pkg a (is_closed_eq hf hg) h

/-- Extension of maps to completions -/
protected def extend {α : Type u_1} [uniform_space α] (pkg : abstract_completion α) {β : Type u_2}
    [uniform_space β] (f : α → β) : space pkg → β :=
  ite (uniform_continuous f) (dense_inducing.extend (dense_inducing pkg) f)
    fun (x : space pkg) => f (dense_range.some (dense pkg) x)

theorem extend_def {α : Type u_1} [uniform_space α] (pkg : abstract_completion α) {β : Type u_2}
    [uniform_space β] {f : α → β} (hf : uniform_continuous f) :
    abstract_completion.extend pkg f = dense_inducing.extend (dense_inducing pkg) f :=
  if_pos hf

theorem extend_coe {α : Type u_1} [uniform_space α] (pkg : abstract_completion α) {β : Type u_2}
    [uniform_space β] {f : α → β} [t2_space β] (hf : uniform_continuous f) (a : α) :
    abstract_completion.extend pkg f (coe pkg a) = f a :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (abstract_completion.extend pkg f (coe pkg a) = f a))
        (extend_def pkg hf)))
    (dense_inducing.extend_eq (dense_inducing pkg) (uniform_continuous.continuous hf) a)

theorem uniform_continuous_extend {α : Type u_1} [uniform_space α] (pkg : abstract_completion α)
    {β : Type u_2} [uniform_space β] {f : α → β} [complete_space β] [separated_space β] :
    uniform_continuous (abstract_completion.extend pkg f) :=
  sorry

theorem continuous_extend {α : Type u_1} [uniform_space α] (pkg : abstract_completion α)
    {β : Type u_2} [uniform_space β] {f : α → β} [complete_space β] [separated_space β] :
    continuous (abstract_completion.extend pkg f) :=
  uniform_continuous.continuous (uniform_continuous_extend pkg)

theorem extend_unique {α : Type u_1} [uniform_space α] (pkg : abstract_completion α) {β : Type u_2}
    [uniform_space β] {f : α → β} [complete_space β] [separated_space β] (hf : uniform_continuous f)
    {g : space pkg → β} (hg : uniform_continuous g) (h : ∀ (a : α), f a = g (coe pkg a)) :
    abstract_completion.extend pkg f = g :=
  sorry

@[simp] theorem extend_comp_coe {α : Type u_1} [uniform_space α] (pkg : abstract_completion α)
    {β : Type u_2} [uniform_space β] [complete_space β] [separated_space β] {f : space pkg → β}
    (hf : uniform_continuous f) : abstract_completion.extend pkg (f ∘ coe pkg) = f :=
  sorry

/-- Lifting maps to completions -/
protected def map {α : Type u_1} [uniform_space α] (pkg : abstract_completion α) {β : Type u_2}
    [uniform_space β] (pkg' : abstract_completion β) (f : α → β) : space pkg → space pkg' :=
  abstract_completion.extend pkg (coe pkg' ∘ f)

theorem uniform_continuous_map {α : Type u_1} [uniform_space α] (pkg : abstract_completion α)
    {β : Type u_2} [uniform_space β] (pkg' : abstract_completion β) (f : α → β) :
    uniform_continuous (abstract_completion.map pkg pkg' f) :=
  uniform_continuous_extend pkg

theorem continuous_map {α : Type u_1} [uniform_space α] (pkg : abstract_completion α) {β : Type u_2}
    [uniform_space β] (pkg' : abstract_completion β) (f : α → β) :
    continuous (abstract_completion.map pkg pkg' f) :=
  continuous_extend pkg

@[simp] theorem map_coe {α : Type u_1} [uniform_space α] (pkg : abstract_completion α)
    {β : Type u_2} [uniform_space β] (pkg' : abstract_completion β) {f : α → β}
    (hf : uniform_continuous f) (a : α) :
    abstract_completion.map pkg pkg' f (coe pkg a) = coe pkg' (f a) :=
  extend_coe pkg (uniform_continuous.comp (uniform_continuous_coe pkg') hf) a

theorem map_unique {α : Type u_1} [uniform_space α] (pkg : abstract_completion α) {β : Type u_2}
    [uniform_space β] (pkg' : abstract_completion β) {f : α → β} {g : space pkg → space pkg'}
    (hg : uniform_continuous g) (h : ∀ (a : α), coe pkg' (f a) = g (coe pkg a)) :
    abstract_completion.map pkg pkg' f = g :=
  sorry

@[simp] theorem map_id {α : Type u_1} [uniform_space α] (pkg : abstract_completion α) :
    abstract_completion.map pkg pkg id = id :=
  map_unique pkg pkg uniform_continuous_id fun (a : α) => rfl

theorem extend_map {α : Type u_1} [uniform_space α] (pkg : abstract_completion α) {β : Type u_2}
    [uniform_space β] (pkg' : abstract_completion β) {γ : Type u_3} [uniform_space γ]
    [complete_space γ] [separated_space γ] {f : β → γ} {g : α → β} (hf : uniform_continuous f)
    (hg : uniform_continuous g) :
    abstract_completion.extend pkg' f ∘ abstract_completion.map pkg pkg' g =
        abstract_completion.extend pkg (f ∘ g) :=
  sorry

theorem map_comp {α : Type u_1} [uniform_space α] (pkg : abstract_completion α) {β : Type u_2}
    [uniform_space β] (pkg' : abstract_completion β) {γ : Type u_3} [uniform_space γ]
    (pkg'' : abstract_completion γ) {g : β → γ} {f : α → β} (hg : uniform_continuous g)
    (hf : uniform_continuous f) :
    abstract_completion.map pkg' pkg'' g ∘ abstract_completion.map pkg pkg' f =
        abstract_completion.map pkg pkg'' (g ∘ f) :=
  extend_map pkg pkg' (uniform_continuous.comp (uniform_continuous_coe pkg'') hg) hf

-- We can now compare two completion packages for the same uniform space

/-- The comparison map between two completions of the same uniform space. -/
def compare {α : Type u_1} [uniform_space α] (pkg : abstract_completion α)
    (pkg' : abstract_completion α) : space pkg → space pkg' :=
  abstract_completion.extend pkg (coe pkg')

theorem uniform_continuous_compare {α : Type u_1} [uniform_space α] (pkg : abstract_completion α)
    (pkg' : abstract_completion α) : uniform_continuous (compare pkg pkg') :=
  uniform_continuous_extend pkg

theorem compare_coe {α : Type u_1} [uniform_space α] (pkg : abstract_completion α)
    (pkg' : abstract_completion α) (a : α) : compare pkg pkg' (coe pkg a) = coe pkg' a :=
  extend_coe pkg (uniform_continuous_coe pkg') a

theorem inverse_compare {α : Type u_1} [uniform_space α] (pkg : abstract_completion α)
    (pkg' : abstract_completion α) : compare pkg pkg' ∘ compare pkg' pkg = id :=
  sorry

/-- The bijection between two completions of the same uniform space. -/
def compare_equiv {α : Type u_1} [uniform_space α] (pkg : abstract_completion α)
    (pkg' : abstract_completion α) : space pkg ≃ space pkg' :=
  equiv.mk (compare pkg pkg') (compare pkg' pkg) sorry sorry

theorem uniform_continuous_compare_equiv {α : Type u_1} [uniform_space α]
    (pkg : abstract_completion α) (pkg' : abstract_completion α) :
    uniform_continuous ⇑(compare_equiv pkg pkg') :=
  uniform_continuous_compare pkg pkg'

theorem uniform_continuous_compare_equiv_symm {α : Type u_1} [uniform_space α]
    (pkg : abstract_completion α) (pkg' : abstract_completion α) :
    uniform_continuous ⇑(equiv.symm (compare_equiv pkg pkg')) :=
  uniform_continuous_compare pkg' pkg

/-- Products of completions -/
protected def prod {α : Type u_1} [uniform_space α] (pkg : abstract_completion α) {β : Type u_2}
    [uniform_space β] (pkg' : abstract_completion β) : abstract_completion (α × β) :=
  mk (space pkg × space pkg') (fun (p : α × β) => (coe pkg (prod.fst p), coe pkg' (prod.snd p)))
    prod.uniform_space sorry sorry sorry sorry

/-- Extend two variable map to completions. -/
protected def extend₂ {α : Type u_1} [uniform_space α] (pkg : abstract_completion α) {β : Type u_2}
    [uniform_space β] (pkg' : abstract_completion β) {γ : Type u_3} [uniform_space γ]
    (f : α → β → γ) : space pkg → space pkg' → γ :=
  function.curry
    (abstract_completion.extend (abstract_completion.prod pkg pkg') (function.uncurry f))

theorem extension₂_coe_coe {α : Type u_1} [uniform_space α] (pkg : abstract_completion α)
    {β : Type u_2} [uniform_space β] (pkg' : abstract_completion β) {γ : Type u_3} [uniform_space γ]
    [separated_space γ] {f : α → β → γ} (hf : uniform_continuous (function.uncurry f)) (a : α)
    (b : β) : abstract_completion.extend₂ pkg pkg' f (coe pkg a) (coe pkg' b) = f a b :=
  sorry

theorem uniform_continuous_extension₂ {α : Type u_1} [uniform_space α] (pkg : abstract_completion α)
    {β : Type u_2} [uniform_space β] (pkg' : abstract_completion β) {γ : Type u_3} [uniform_space γ]
    [separated_space γ] (f : α → β → γ) [complete_space γ] :
    uniform_continuous₂ (abstract_completion.extend₂ pkg pkg' f) :=
  sorry

/-- Lift two variable maps to completions. -/
protected def map₂ {α : Type u_1} [uniform_space α] (pkg : abstract_completion α) {β : Type u_2}
    [uniform_space β] (pkg' : abstract_completion β) {γ : Type u_3} [uniform_space γ]
    (pkg'' : abstract_completion γ) (f : α → β → γ) : space pkg → space pkg' → space pkg'' :=
  abstract_completion.extend₂ pkg pkg' (function.bicompr (coe pkg'') f)

theorem uniform_continuous_map₂ {α : Type u_1} [uniform_space α] (pkg : abstract_completion α)
    {β : Type u_2} [uniform_space β] (pkg' : abstract_completion β) {γ : Type u_3} [uniform_space γ]
    (pkg'' : abstract_completion γ) (f : α → β → γ) :
    uniform_continuous₂ (abstract_completion.map₂ pkg pkg' pkg'' f) :=
  uniform_continuous_extension₂ pkg pkg' (function.bicompr (coe pkg'') f)

theorem continuous_map₂ {α : Type u_1} [uniform_space α] (pkg : abstract_completion α)
    {β : Type u_2} [uniform_space β] (pkg' : abstract_completion β) {γ : Type u_3} [uniform_space γ]
    (pkg'' : abstract_completion γ) {δ : Type u_4} [topological_space δ] {f : α → β → γ}
    {a : δ → space pkg} {b : δ → space pkg'} (ha : continuous a) (hb : continuous b) :
    continuous fun (d : δ) => abstract_completion.map₂ pkg pkg' pkg'' f (a d) (b d) :=
  continuous.comp (uniform_continuous.continuous (uniform_continuous_map₂ pkg pkg' pkg'' f))
    (continuous.prod_mk ha hb)

theorem map₂_coe_coe {α : Type u_1} [uniform_space α] (pkg : abstract_completion α) {β : Type u_2}
    [uniform_space β] (pkg' : abstract_completion β) {γ : Type u_3} [uniform_space γ]
    (pkg'' : abstract_completion γ) (a : α) (b : β) (f : α → β → γ) (hf : uniform_continuous₂ f) :
    abstract_completion.map₂ pkg pkg' pkg'' f (coe pkg a) (coe pkg' b) = coe pkg'' (f a b) :=
  extension₂_coe_coe pkg pkg' (uniform_continuous.comp (uniform_continuous_coe pkg'') hf) a b

end Mathlib