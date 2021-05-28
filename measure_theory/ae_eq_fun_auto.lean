/-
Copyright (c) 2019 Johannes Hölzl, Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Zhouhang Zhou
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.measure_theory.integration
import Mathlib.order.filter.germ
import PostPort

universes u_1 u_2 u_3 u_4 u_5 u_6 

namespace Mathlib

/-!

# Almost everywhere equal functions

Two measurable functions are treated as identical if they are almost everywhere equal. We form the
set of equivalence classes under the relation of being almost everywhere equal, which is sometimes
known as the `L⁰` space.

See `l1_space.lean` for `L¹` space.

## Notation

* `α →ₘ[μ] β` is the type of `L⁰` space, where `α` and `β` are measurable spaces and `μ`
  is a measure on `α`. `f : α →ₘ β` is a "function" in `L⁰`. In comments, `[f]` is also used
  to denote an `L⁰` function.

  `ₘ` can be typed as `\_m`. Sometimes it is shown as a box if font is missing.


## Main statements

* The linear structure of `L⁰` :
    Addition and scalar multiplication are defined on `L⁰` in the natural way, i.e.,
    `[f] + [g] := [f + g]`, `c • [f] := [c • f]`. So defined, `α →ₘ β` inherits the linear structure
    of `β`. For example, if `β` is a module, then `α →ₘ β` is a module over the same ring.

    See `mk_add_mk`,  `neg_mk`,     `mk_sub_mk`,  `smul_mk`,
        `add_to_fun`, `neg_to_fun`, `sub_to_fun`, `smul_to_fun`

* The order structure of `L⁰` :
    `≤` can be defined in a similar way: `[f] ≤ [g]` if `f a ≤ g a` for almost all `a` in domain.
    And `α →ₘ β` inherits the preorder and partial order of `β`.

    TODO: Define `sup` and `inf` on `L⁰` so that it forms a lattice. It seems that `β` must be a
    linear order, since otherwise `f ⊔ g` may not be a measurable function.

* Emetric on `L⁰` :
    If `β` is an `emetric_space`, then `L⁰` can be made into an `emetric_space`, where
    `edist [f] [g]` is defined to be `∫⁻ a, edist (f a) (g a)`.

    The integral used here is `lintegral : (α → ennreal) → ennreal`, which is defined in the file
    `integration.lean`.

    See `edist_mk_mk` and `edist_to_fun`.

## Implementation notes

* `f.to_fun`     : To find a representative of `f : α →ₘ β`, use `f.to_fun`.
                 For each operation `op` in `L⁰`, there is a lemma called `op_to_fun`,
                 characterizing, say, `(f op g).to_fun`.
* `ae_eq_fun.mk` : To constructs an `L⁰` function `α →ₘ β` from a measurable function `f : α → β`,
                 use `ae_eq_fun.mk`
* `comp`         : Use `comp g f` to get `[g ∘ f]` from `g : β → γ` and `[f] : α →ₘ γ`
* `comp₂`        : Use `comp₂ g f₁ f₂ to get `[λa, g (f₁ a) (f₂ a)]`.
                 For example, `[f + g]` is `comp₂ (+)`


## Tags

function space, almost everywhere equal, `L⁰`, ae_eq_fun

-/

namespace measure_theory


/-- The equivalence relation of being almost everywhere equal -/
def measure.ae_eq_setoid {α : Type u_1} (β : Type u_2) [measurable_space α] [measurable_space β] (μ : measure α) : setoid (Subtype fun (f : α → β) => ae_measurable f) :=
  setoid.mk (fun (f g : Subtype fun (f : α → β) => ae_measurable f) => filter.eventually_eq (measure.ae μ) ↑f ↑g) sorry

/-- The space of equivalence classes of measurable functions, where two measurable functions are
    equivalent if they agree almost everywhere, i.e., they differ on a set of measure `0`.  -/
def ae_eq_fun (α : Type u_1) (β : Type u_2) [measurable_space α] [measurable_space β] (μ : measure α)  :=
  quotient (measure.ae_eq_setoid β μ)

namespace ae_eq_fun


/-- Construct the equivalence class `[f]` of an almost everywhere measurable function `f`, based
    on the equivalence relation of being almost everywhere equal. -/
def mk {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [measurable_space β] (f : α → β) (hf : ae_measurable f) : ae_eq_fun α β μ :=
  quotient.mk' { val := f, property := hf }

/-- A measurable representative of an `ae_eq_fun` [f] -/
protected instance has_coe_to_fun {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [measurable_space β] : has_coe_to_fun (ae_eq_fun α β μ) :=
  has_coe_to_fun.mk (fun (f : ae_eq_fun α β μ) => α → β)
    fun (f : ae_eq_fun α β μ) => ae_measurable.mk (subtype.val (quotient.out' f)) sorry

protected theorem measurable {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [measurable_space β] (f : ae_eq_fun α β μ) : measurable ⇑f :=
  ae_measurable.measurable_mk (has_coe_to_fun._proof_1 f)

protected theorem ae_measurable {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [measurable_space β] (f : ae_eq_fun α β μ) : ae_measurable ⇑f :=
  measurable.ae_measurable (ae_eq_fun.measurable f)

@[simp] theorem quot_mk_eq_mk {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [measurable_space β] (f : α → β) (hf : ae_measurable f) : Quot.mk setoid.r { val := f, property := hf } = mk f hf :=
  rfl

@[simp] theorem mk_eq_mk {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [measurable_space β] {f : α → β} {g : α → β} {hf : ae_measurable f} {hg : ae_measurable g} : mk f hf = mk g hg ↔ filter.eventually_eq (measure.ae μ) f g :=
  quotient.eq'

@[simp] theorem mk_coe_fn {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [measurable_space β] (f : ae_eq_fun α β μ) : mk (⇑f) (ae_eq_fun.ae_measurable f) = f := sorry

theorem ext {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [measurable_space β] {f : ae_eq_fun α β μ} {g : ae_eq_fun α β μ} (h : filter.eventually_eq (measure.ae μ) ⇑f ⇑g) : f = g := sorry

theorem coe_fn_mk {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [measurable_space β] (f : α → β) (hf : ae_measurable f) : filter.eventually_eq (measure.ae μ) (⇑(mk f hf)) f :=
  filter.eventually_eq.trans (filter.eventually_eq.symm (ae_measurable.ae_eq_mk (has_coe_to_fun._proof_1 (mk f hf))))
    (quotient.mk_out' { val := f, property := hf })

theorem induction_on {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [measurable_space β] (f : ae_eq_fun α β μ) {p : ae_eq_fun α β μ → Prop} (H : ∀ (f : α → β) (hf : ae_measurable f), p (mk f hf)) : p f :=
  quotient.induction_on' f (iff.mpr subtype.forall H)

theorem induction_on₂ {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [measurable_space β] {α' : Type u_3} {β' : Type u_4} [measurable_space α'] [measurable_space β'] {μ' : measure α'} (f : ae_eq_fun α β μ) (f' : ae_eq_fun α' β' μ') {p : ae_eq_fun α β μ → ae_eq_fun α' β' μ' → Prop} (H : ∀ (f : α → β) (hf : ae_measurable f) (f' : α' → β') (hf' : ae_measurable f'), p (mk f hf) (mk f' hf')) : p f f' :=
  induction_on f fun (f : α → β) (hf : ae_measurable f) => induction_on f' (H f hf)

theorem induction_on₃ {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [measurable_space β] {α' : Type u_3} {β' : Type u_4} [measurable_space α'] [measurable_space β'] {μ' : measure α'} {α'' : Type u_5} {β'' : Type u_6} [measurable_space α''] [measurable_space β''] {μ'' : measure α''} (f : ae_eq_fun α β μ) (f' : ae_eq_fun α' β' μ') (f'' : ae_eq_fun α'' β'' μ'') {p : ae_eq_fun α β μ → ae_eq_fun α' β' μ' → ae_eq_fun α'' β'' μ'' → Prop} (H : ∀ (f : α → β) (hf : ae_measurable f) (f' : α' → β') (hf' : ae_measurable f') (f'' : α'' → β'')
  (hf'' : ae_measurable f''), p (mk f hf) (mk f' hf') (mk f'' hf'')) : p f f' f'' :=
  induction_on f fun (f : α → β) (hf : ae_measurable f) => induction_on₂ f' f'' (H f hf)

/-- Given a measurable function `g : β → γ`, and an almost everywhere equal function `[f] : α →ₘ β`,
    return the equivalence class of `g ∘ f`, i.e., the almost everywhere equal function
    `[g ∘ f] : α →ₘ γ`. -/
def comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space β] [measurable_space γ] (g : β → γ) (hg : measurable g) (f : ae_eq_fun α β μ) : ae_eq_fun α γ μ :=
  quotient.lift_on' f (fun (f : Subtype fun (f : α → β) => ae_measurable f) => mk (g ∘ ↑f) sorry) sorry

@[simp] theorem comp_mk {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space β] [measurable_space γ] (g : β → γ) (hg : measurable g) (f : α → β) (hf : ae_measurable f) : comp g hg (mk f hf) = mk (g ∘ f) (measurable.comp_ae_measurable hg hf) :=
  rfl

theorem comp_eq_mk {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space β] [measurable_space γ] (g : β → γ) (hg : measurable g) (f : ae_eq_fun α β μ) : comp g hg f = mk (g ∘ ⇑f) (measurable.comp_ae_measurable hg (ae_eq_fun.ae_measurable f)) := sorry

theorem coe_fn_comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space β] [measurable_space γ] (g : β → γ) (hg : measurable g) (f : ae_eq_fun α β μ) : filter.eventually_eq (measure.ae μ) (⇑(comp g hg f)) (g ∘ ⇑f) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (filter.eventually_eq (measure.ae μ) (⇑(comp g hg f)) (g ∘ ⇑f))) (comp_eq_mk g hg f)))
    (coe_fn_mk (g ∘ ⇑f) (measurable.comp_ae_measurable hg (ae_eq_fun.ae_measurable f)))

/-- The class of `x ↦ (f x, g x)`. -/
def pair {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space β] [measurable_space γ] (f : ae_eq_fun α β μ) (g : ae_eq_fun α γ μ) : ae_eq_fun α (β × γ) μ :=
  quotient.lift_on₂' f g
    (fun (f : Subtype fun (f : α → β) => ae_measurable f) (g : Subtype fun (f : α → γ) => ae_measurable f) =>
      mk (fun (x : α) => (subtype.val f x, subtype.val g x)) sorry)
    sorry

@[simp] theorem pair_mk_mk {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space β] [measurable_space γ] (f : α → β) (hf : ae_measurable f) (g : α → γ) (hg : ae_measurable g) : pair (mk f hf) (mk g hg) = mk (fun (x : α) => (f x, g x)) (ae_measurable.prod_mk hf hg) :=
  rfl

theorem pair_eq_mk {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space β] [measurable_space γ] (f : ae_eq_fun α β μ) (g : ae_eq_fun α γ μ) : pair f g =
  mk (fun (x : α) => (coe_fn f x, coe_fn g x))
    (ae_measurable.prod_mk (ae_eq_fun.ae_measurable f) (ae_eq_fun.ae_measurable g)) := sorry

theorem coe_fn_pair {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space β] [measurable_space γ] (f : ae_eq_fun α β μ) (g : ae_eq_fun α γ μ) : filter.eventually_eq (measure.ae μ) ⇑(pair f g) fun (x : α) => (coe_fn f x, coe_fn g x) := sorry

/-- Given a measurable function `g : β → γ → δ`, and almost everywhere equal functions
    `[f₁] : α →ₘ β` and `[f₂] : α →ₘ γ`, return the equivalence class of the function
    `λa, g (f₁ a) (f₂ a)`, i.e., the almost everywhere equal function
    `[λa, g (f₁ a) (f₂ a)] : α →ₘ γ` -/
def comp₂ {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [measurable_space β] {γ : Type u_3} {δ : Type u_4} [measurable_space γ] [measurable_space δ] (g : β → γ → δ) (hg : measurable (function.uncurry g)) (f₁ : ae_eq_fun α β μ) (f₂ : ae_eq_fun α γ μ) : ae_eq_fun α δ μ :=
  comp (function.uncurry g) hg (pair f₁ f₂)

@[simp] theorem comp₂_mk_mk {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [measurable_space β] {γ : Type u_3} {δ : Type u_4} [measurable_space γ] [measurable_space δ] (g : β → γ → δ) (hg : measurable (function.uncurry g)) (f₁ : α → β) (f₂ : α → γ) (hf₁ : ae_measurable f₁) (hf₂ : ae_measurable f₂) : comp₂ g hg (mk f₁ hf₁) (mk f₂ hf₂) =
  mk (fun (a : α) => g (f₁ a) (f₂ a)) (measurable.comp_ae_measurable hg (ae_measurable.prod_mk hf₁ hf₂)) :=
  rfl

theorem comp₂_eq_pair {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [measurable_space β] {γ : Type u_3} {δ : Type u_4} [measurable_space γ] [measurable_space δ] (g : β → γ → δ) (hg : measurable (function.uncurry g)) (f₁ : ae_eq_fun α β μ) (f₂ : ae_eq_fun α γ μ) : comp₂ g hg f₁ f₂ = comp (function.uncurry g) hg (pair f₁ f₂) :=
  rfl

theorem comp₂_eq_mk {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [measurable_space β] {γ : Type u_3} {δ : Type u_4} [measurable_space γ] [measurable_space δ] (g : β → γ → δ) (hg : measurable (function.uncurry g)) (f₁ : ae_eq_fun α β μ) (f₂ : ae_eq_fun α γ μ) : comp₂ g hg f₁ f₂ =
  mk (fun (a : α) => g (coe_fn f₁ a) (coe_fn f₂ a))
    (measurable.comp_ae_measurable hg (ae_measurable.prod_mk (ae_eq_fun.ae_measurable f₁) (ae_eq_fun.ae_measurable f₂))) := sorry

theorem coe_fn_comp₂ {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [measurable_space β] {γ : Type u_3} {δ : Type u_4} [measurable_space γ] [measurable_space δ] (g : β → γ → δ) (hg : measurable (function.uncurry g)) (f₁ : ae_eq_fun α β μ) (f₂ : ae_eq_fun α γ μ) : filter.eventually_eq (measure.ae μ) ⇑(comp₂ g hg f₁ f₂) fun (a : α) => g (coe_fn f₁ a) (coe_fn f₂ a) := sorry

/-- Interpret `f : α →ₘ[μ] β` as a germ at `μ.ae` forgetting that `f` is almost everywhere
    measurable. -/
def to_germ {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [measurable_space β] (f : ae_eq_fun α β μ) : filter.germ (measure.ae μ) β :=
  quotient.lift_on' f (fun (f : Subtype fun (f : α → β) => ae_measurable f) => ↑↑f) sorry

@[simp] theorem mk_to_germ {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [measurable_space β] (f : α → β) (hf : ae_measurable f) : to_germ (mk f hf) = ↑f :=
  rfl

theorem to_germ_eq {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [measurable_space β] (f : ae_eq_fun α β μ) : to_germ f = ↑⇑f :=
  eq.mpr (id (Eq._oldrec (Eq.refl (to_germ f = ↑⇑f)) (Eq.symm (mk_to_germ (⇑f) (ae_eq_fun.ae_measurable f)))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (to_germ f = to_germ (mk (⇑f) (ae_eq_fun.ae_measurable f)))) (mk_coe_fn f)))
      (Eq.refl (to_germ f)))

theorem to_germ_injective {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [measurable_space β] : function.injective to_germ := sorry

theorem comp_to_germ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space β] [measurable_space γ] (g : β → γ) (hg : measurable g) (f : ae_eq_fun α β μ) : to_germ (comp g hg f) = filter.germ.map g (to_germ f) := sorry

theorem comp₂_to_germ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} [measurable_space α] {μ : measure α} [measurable_space β] [measurable_space γ] [measurable_space δ] (g : β → γ → δ) (hg : measurable (function.uncurry g)) (f₁ : ae_eq_fun α β μ) (f₂ : ae_eq_fun α γ μ) : to_germ (comp₂ g hg f₁ f₂) = filter.germ.map₂ g (to_germ f₁) (to_germ f₂) := sorry

/-- Given a predicate `p` and an equivalence class `[f]`, return true if `p` holds of `f a`
    for almost all `a` -/
def lift_pred {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [measurable_space β] (p : β → Prop) (f : ae_eq_fun α β μ)  :=
  filter.germ.lift_pred p (to_germ f)

/-- Given a relation `r` and equivalence class `[f]` and `[g]`, return true if `r` holds of
    `(f a, g a)` for almost all `a` -/
def lift_rel {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space β] [measurable_space γ] (r : β → γ → Prop) (f : ae_eq_fun α β μ) (g : ae_eq_fun α γ μ)  :=
  filter.germ.lift_rel r (to_germ f) (to_germ g)

theorem lift_rel_mk_mk {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space β] [measurable_space γ] {r : β → γ → Prop} {f : α → β} {g : α → γ} {hf : ae_measurable f} {hg : ae_measurable g} : lift_rel r (mk f hf) (mk g hg) ↔ filter.eventually (fun (a : α) => r (f a) (g a)) (measure.ae μ) :=
  iff.rfl

theorem lift_rel_iff_coe_fn {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space β] [measurable_space γ] {r : β → γ → Prop} {f : ae_eq_fun α β μ} {g : ae_eq_fun α γ μ} : lift_rel r f g ↔ filter.eventually (fun (a : α) => r (coe_fn f a) (coe_fn g a)) (measure.ae μ) := sorry

protected instance preorder {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [measurable_space β] [preorder β] : preorder (ae_eq_fun α β μ) :=
  preorder.lift to_germ

@[simp] theorem mk_le_mk {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [measurable_space β] [preorder β] {f : α → β} {g : α → β} (hf : ae_measurable f) (hg : ae_measurable g) : mk f hf ≤ mk g hg ↔ filter.eventually_le (measure.ae μ) f g :=
  iff.rfl

@[simp] theorem coe_fn_le {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [measurable_space β] [preorder β] {f : ae_eq_fun α β μ} {g : ae_eq_fun α β μ} : filter.eventually_le (measure.ae μ) ⇑f ⇑g ↔ f ≤ g :=
  iff.symm lift_rel_iff_coe_fn

protected instance partial_order {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [measurable_space β] [partial_order β] : partial_order (ae_eq_fun α β μ) :=
  partial_order.lift to_germ to_germ_injective

/- TODO: Prove `L⁰` space is a lattice if β is linear order.
         What if β is only a lattice? -/

-- instance [linear_order β] : semilattice_sup (α →ₘ β) :=

-- { sup := comp₂ (⊔) (_),

--    .. ae_eq_fun.partial_order }

/-- The equivalence class of a constant function: `[λa:α, b]`, based on the equivalence relation of
    being almost everywhere equal -/
def const (α : Type u_1) {β : Type u_2} [measurable_space α] {μ : measure α} [measurable_space β] (b : β) : ae_eq_fun α β μ :=
  mk (fun (a : α) => b) ae_measurable_const

theorem coe_fn_const (α : Type u_1) {β : Type u_2} [measurable_space α] {μ : measure α} [measurable_space β] (b : β) : filter.eventually_eq (measure.ae μ) (⇑(const α b)) (function.const α b) :=
  coe_fn_mk (fun (a : α) => b) ae_measurable_const

protected instance inhabited {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [measurable_space β] [Inhabited β] : Inhabited (ae_eq_fun α β μ) :=
  { default := const α Inhabited.default }

protected instance has_zero {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [measurable_space β] [HasZero β] : HasZero (ae_eq_fun α β μ) :=
  { zero := const α 0 }

theorem one_def {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [measurable_space β] [HasOne β] : 1 = mk (fun (a : α) => 1) ae_measurable_const :=
  rfl

theorem coe_fn_one {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [measurable_space β] [HasOne β] : filter.eventually_eq (measure.ae μ) (⇑1) 1 :=
  coe_fn_const α 1

@[simp] theorem one_to_germ {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [measurable_space β] [HasOne β] : to_germ 1 = 1 :=
  rfl

protected instance has_mul {α : Type u_1} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space γ] [topological_space γ] [topological_space.second_countable_topology γ] [borel_space γ] [monoid γ] [has_continuous_mul γ] : Mul (ae_eq_fun α γ μ) :=
  { mul := comp₂ Mul.mul sorry }

@[simp] theorem mk_mul_mk {α : Type u_1} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space γ] [topological_space γ] [topological_space.second_countable_topology γ] [borel_space γ] [monoid γ] [has_continuous_mul γ] (f : α → γ) (g : α → γ) (hf : ae_measurable f) (hg : ae_measurable g) : mk f hf * mk g hg = mk (f * g) (ae_measurable.mul hf hg) :=
  rfl

theorem coe_fn_mul {α : Type u_1} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space γ] [topological_space γ] [topological_space.second_countable_topology γ] [borel_space γ] [monoid γ] [has_continuous_mul γ] (f : ae_eq_fun α γ μ) (g : ae_eq_fun α γ μ) : filter.eventually_eq (measure.ae μ) (⇑(f * g)) (⇑f * ⇑g) :=
  coe_fn_comp₂ Mul.mul has_mul._proof_1 f g

@[simp] theorem mul_to_germ {α : Type u_1} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space γ] [topological_space γ] [topological_space.second_countable_topology γ] [borel_space γ] [monoid γ] [has_continuous_mul γ] (f : ae_eq_fun α γ μ) (g : ae_eq_fun α γ μ) : to_germ (f * g) = to_germ f * to_germ g :=
  comp₂_to_germ Mul.mul has_mul._proof_1 f g

protected instance add_monoid {α : Type u_1} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space γ] [topological_space γ] [topological_space.second_countable_topology γ] [borel_space γ] [add_monoid γ] [has_continuous_add γ] : add_monoid (ae_eq_fun α γ μ) :=
  function.injective.add_monoid to_germ to_germ_injective sorry add_to_germ

protected instance add_comm_monoid {α : Type u_1} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space γ] [topological_space γ] [topological_space.second_countable_topology γ] [borel_space γ] [add_comm_monoid γ] [has_continuous_add γ] : add_comm_monoid (ae_eq_fun α γ μ) :=
  function.injective.add_comm_monoid to_germ to_germ_injective sorry sorry

protected instance has_inv {α : Type u_1} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space γ] [topological_space γ] [borel_space γ] [group γ] [topological_group γ] : has_inv (ae_eq_fun α γ μ) :=
  has_inv.mk (comp has_inv.inv measurable_inv)

@[simp] theorem inv_mk {α : Type u_1} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space γ] [topological_space γ] [borel_space γ] [group γ] [topological_group γ] (f : α → γ) (hf : ae_measurable f) : mk f hf⁻¹ = mk (f⁻¹) (ae_measurable.inv hf) :=
  rfl

theorem coe_fn_neg {α : Type u_1} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space γ] [topological_space γ] [borel_space γ] [add_group γ] [topological_add_group γ] (f : ae_eq_fun α γ μ) : filter.eventually_eq (measure.ae μ) (⇑(-f)) (-⇑f) :=
  coe_fn_comp Neg.neg measurable_neg f

theorem inv_to_germ {α : Type u_1} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space γ] [topological_space γ] [borel_space γ] [group γ] [topological_group γ] (f : ae_eq_fun α γ μ) : to_germ (f⁻¹) = (to_germ f⁻¹) :=
  comp_to_germ has_inv.inv measurable_inv f

protected instance group {α : Type u_1} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space γ] [topological_space γ] [borel_space γ] [group γ] [topological_group γ] [topological_space.second_countable_topology γ] : group (ae_eq_fun α γ μ) :=
  function.injective.group to_germ to_germ_injective sorry sorry inv_to_germ

@[simp] theorem mk_sub {α : Type u_1} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space γ] [topological_space γ] [borel_space γ] [add_group γ] [topological_add_group γ] [topological_space.second_countable_topology γ] (f : α → γ) (g : α → γ) (hf : ae_measurable fun (x : α) => f x) (hg : ae_measurable fun (x : α) => g x) : mk (f - g) (ae_measurable.sub hf hg) = mk f hf - mk g hg := sorry

theorem coe_fn_sub {α : Type u_1} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space γ] [topological_space γ] [borel_space γ] [add_group γ] [topological_add_group γ] [topological_space.second_countable_topology γ] (f : ae_eq_fun α γ μ) (g : ae_eq_fun α γ μ) : filter.eventually_eq (measure.ae μ) (⇑(f - g)) (⇑f - ⇑g) := sorry

protected instance comm_group {α : Type u_1} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space γ] [topological_space γ] [borel_space γ] [comm_group γ] [topological_group γ] [topological_space.second_countable_topology γ] : comm_group (ae_eq_fun α γ μ) :=
  comm_group.mk group.mul sorry group.one sorry sorry group.inv group.div sorry sorry

protected instance has_scalar {α : Type u_1} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space γ] {𝕜 : Type u_5} [semiring 𝕜] [topological_space 𝕜] [topological_space γ] [borel_space γ] [add_comm_monoid γ] [semimodule 𝕜 γ] [topological_semimodule 𝕜 γ] : has_scalar 𝕜 (ae_eq_fun α γ μ) :=
  has_scalar.mk fun (c : 𝕜) (f : ae_eq_fun α γ μ) => comp (has_scalar.smul c) sorry f

@[simp] theorem smul_mk {α : Type u_1} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space γ] {𝕜 : Type u_5} [semiring 𝕜] [topological_space 𝕜] [topological_space γ] [borel_space γ] [add_comm_monoid γ] [semimodule 𝕜 γ] [topological_semimodule 𝕜 γ] (c : 𝕜) (f : α → γ) (hf : ae_measurable f) : c • mk f hf = mk (c • f) (ae_measurable.const_smul hf c) :=
  rfl

theorem coe_fn_smul {α : Type u_1} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space γ] {𝕜 : Type u_5} [semiring 𝕜] [topological_space 𝕜] [topological_space γ] [borel_space γ] [add_comm_monoid γ] [semimodule 𝕜 γ] [topological_semimodule 𝕜 γ] (c : 𝕜) (f : ae_eq_fun α γ μ) : filter.eventually_eq (measure.ae μ) (⇑(c • f)) (c • ⇑f) :=
  coe_fn_comp (has_scalar.smul c) (has_scalar._proof_1 c) f

theorem smul_to_germ {α : Type u_1} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space γ] {𝕜 : Type u_5} [semiring 𝕜] [topological_space 𝕜] [topological_space γ] [borel_space γ] [add_comm_monoid γ] [semimodule 𝕜 γ] [topological_semimodule 𝕜 γ] (c : 𝕜) (f : ae_eq_fun α γ μ) : to_germ (c • f) = c • to_germ f :=
  comp_to_germ (has_scalar.smul c) (has_scalar._proof_1 c) f

protected instance semimodule {α : Type u_1} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space γ] {𝕜 : Type u_5} [semiring 𝕜] [topological_space 𝕜] [topological_space γ] [borel_space γ] [add_comm_monoid γ] [semimodule 𝕜 γ] [topological_semimodule 𝕜 γ] [topological_space.second_countable_topology γ] [has_continuous_add γ] : semimodule 𝕜 (ae_eq_fun α γ μ) :=
  function.injective.semimodule 𝕜 (add_monoid_hom.mk to_germ sorry sorry) to_germ_injective smul_to_germ

/- TODO : Prove that `L⁰` is a complete space if the codomain is complete. -/

/-- For `f : α → ennreal`, define `∫ [f]` to be `∫ f` -/
def lintegral {α : Type u_1} [measurable_space α] {μ : measure α} (f : ae_eq_fun α ennreal μ) : ennreal :=
  quotient.lift_on' f (fun (f : Subtype fun (f : α → ennreal) => ae_measurable f) => lintegral μ fun (a : α) => coe f a)
    sorry

@[simp] theorem lintegral_mk {α : Type u_1} [measurable_space α] {μ : measure α} (f : α → ennreal) (hf : ae_measurable f) : lintegral (mk f hf) = lintegral μ fun (a : α) => f a :=
  rfl

theorem lintegral_coe_fn {α : Type u_1} [measurable_space α] {μ : measure α} (f : ae_eq_fun α ennreal μ) : (lintegral μ fun (a : α) => coe_fn f a) = lintegral f := sorry

@[simp] theorem lintegral_zero {α : Type u_1} [measurable_space α] {μ : measure α} : lintegral 0 = 0 :=
  lintegral_zero

@[simp] theorem lintegral_eq_zero_iff {α : Type u_1} [measurable_space α] {μ : measure α} {f : ae_eq_fun α ennreal μ} : lintegral f = 0 ↔ f = 0 :=
  induction_on f fun (f : α → ennreal) (hf : ae_measurable f) => iff.trans (lintegral_eq_zero_iff' hf) (iff.symm mk_eq_mk)

theorem lintegral_add {α : Type u_1} [measurable_space α] {μ : measure α} (f : ae_eq_fun α ennreal μ) (g : ae_eq_fun α ennreal μ) : lintegral (f + g) = lintegral f + lintegral g := sorry

theorem lintegral_mono {α : Type u_1} [measurable_space α] {μ : measure α} {f : ae_eq_fun α ennreal μ} {g : ae_eq_fun α ennreal μ} : f ≤ g → lintegral f ≤ lintegral g :=
  induction_on₂ f g
    fun (f : α → ennreal) (hf : ae_measurable f) (g : α → ennreal) (hg : ae_measurable g) (hfg : mk f hf ≤ mk g hg) =>
      lintegral_mono_ae hfg

/-- `comp_edist [f] [g] a` will return `edist (f a) (g a)` -/
protected def edist {α : Type u_1} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space γ] [emetric_space γ] [topological_space.second_countable_topology γ] [opens_measurable_space γ] (f : ae_eq_fun α γ μ) (g : ae_eq_fun α γ μ) : ae_eq_fun α ennreal μ :=
  comp₂ edist measurable_edist f g

protected theorem edist_comm {α : Type u_1} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space γ] [emetric_space γ] [topological_space.second_countable_topology γ] [opens_measurable_space γ] (f : ae_eq_fun α γ μ) (g : ae_eq_fun α γ μ) : ae_eq_fun.edist f g = ae_eq_fun.edist g f :=
  induction_on₂ f g
    fun (f : α → γ) (hf : ae_measurable f) (g : α → γ) (hg : ae_measurable g) =>
      iff.mpr mk_eq_mk (filter.eventually_of_forall fun (x : α) => edist_comm (f x) (g x))

theorem coe_fn_edist {α : Type u_1} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space γ] [emetric_space γ] [topological_space.second_countable_topology γ] [opens_measurable_space γ] (f : ae_eq_fun α γ μ) (g : ae_eq_fun α γ μ) : filter.eventually_eq (measure.ae μ) ⇑(ae_eq_fun.edist f g) fun (a : α) => edist (coe_fn f a) (coe_fn g a) :=
  coe_fn_comp₂ edist measurable_edist f g

protected theorem edist_self {α : Type u_1} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space γ] [emetric_space γ] [topological_space.second_countable_topology γ] [opens_measurable_space γ] (f : ae_eq_fun α γ μ) : ae_eq_fun.edist f f = 0 :=
  induction_on f
    fun (f : α → γ) (hf : ae_measurable f) =>
      iff.mpr mk_eq_mk (filter.eventually_of_forall fun (x : α) => edist_self (f x))

/-- Almost everywhere equal functions form an `emetric_space`, with the emetric defined as
  `edist f g = ∫⁻ a, edist (f a) (g a)`. -/
protected instance emetric_space {α : Type u_1} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space γ] [emetric_space γ] [topological_space.second_countable_topology γ] [opens_measurable_space γ] : emetric_space (ae_eq_fun α γ μ) :=
  emetric_space.mk sorry sorry sorry sorry
    (uniform_space_of_edist (fun (f g : ae_eq_fun α γ μ) => lintegral (ae_eq_fun.edist f g)) sorry sorry sorry)

theorem edist_mk_mk {α : Type u_1} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space γ] [emetric_space γ] [topological_space.second_countable_topology γ] [opens_measurable_space γ] {f : α → γ} {g : α → γ} (hf : ae_measurable f) (hg : ae_measurable g) : edist (mk f hf) (mk g hg) = lintegral μ fun (x : α) => edist (f x) (g x) :=
  rfl

theorem edist_eq_coe {α : Type u_1} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space γ] [emetric_space γ] [topological_space.second_countable_topology γ] [opens_measurable_space γ] (f : ae_eq_fun α γ μ) (g : ae_eq_fun α γ μ) : edist f g = lintegral μ fun (x : α) => edist (coe_fn f x) (coe_fn g x) := sorry

theorem edist_zero_eq_coe {α : Type u_1} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space γ] [emetric_space γ] [topological_space.second_countable_topology γ] [opens_measurable_space γ] [HasZero γ] (f : ae_eq_fun α γ μ) : edist f 0 = lintegral μ fun (x : α) => edist (coe_fn f x) 0 := sorry

theorem edist_mk_mk' {α : Type u_1} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space γ] [metric_space γ] [topological_space.second_countable_topology γ] [opens_measurable_space γ] {f : α → γ} {g : α → γ} (hf : ae_measurable f) (hg : ae_measurable g) : edist (mk f hf) (mk g hg) = lintegral μ fun (x : α) => ↑(nndist (f x) (g x)) := sorry

theorem edist_eq_coe' {α : Type u_1} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space γ] [metric_space γ] [topological_space.second_countable_topology γ] [opens_measurable_space γ] (f : ae_eq_fun α γ μ) (g : ae_eq_fun α γ μ) : edist f g = lintegral μ fun (x : α) => ↑(nndist (coe_fn f x) (coe_fn g x)) := sorry

theorem edist_add_right {α : Type u_1} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space γ] [normed_group γ] [topological_space.second_countable_topology γ] [borel_space γ] (f : ae_eq_fun α γ μ) (g : ae_eq_fun α γ μ) (h : ae_eq_fun α γ μ) : edist (f + h) (g + h) = edist f g := sorry

theorem edist_smul {α : Type u_1} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space γ] {𝕜 : Type u_5} [normed_field 𝕜] [normed_group γ] [topological_space.second_countable_topology γ] [normed_space 𝕜 γ] [borel_space γ] (c : 𝕜) (f : ae_eq_fun α γ μ) : edist (c • f) 0 = ennreal.of_real (norm c) * edist f 0 := sorry

/-- Positive part of an `ae_eq_fun`. -/
def pos_part {α : Type u_1} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space γ] [topological_space γ] [linear_order γ] [order_closed_topology γ] [topological_space.second_countable_topology γ] [HasZero γ] [opens_measurable_space γ] (f : ae_eq_fun α γ μ) : ae_eq_fun α γ μ :=
  comp (fun (x : γ) => max x 0) sorry f

@[simp] theorem pos_part_mk {α : Type u_1} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space γ] [topological_space γ] [linear_order γ] [order_closed_topology γ] [topological_space.second_countable_topology γ] [HasZero γ] [opens_measurable_space γ] (f : α → γ) (hf : ae_measurable f) : pos_part (mk f hf) = mk (fun (x : α) => max (f x) 0) (ae_measurable.max hf ae_measurable_const) :=
  rfl

theorem coe_fn_pos_part {α : Type u_1} {γ : Type u_3} [measurable_space α] {μ : measure α} [measurable_space γ] [topological_space γ] [linear_order γ] [order_closed_topology γ] [topological_space.second_countable_topology γ] [HasZero γ] [opens_measurable_space γ] (f : ae_eq_fun α γ μ) : filter.eventually_eq (measure.ae μ) ⇑(pos_part f) fun (a : α) => max (coe_fn f a) 0 :=
  coe_fn_comp (fun (x : γ) => max x 0) pos_part._proof_1 f

