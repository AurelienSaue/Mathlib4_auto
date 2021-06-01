/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Abhimanyu Pallavi Sudhir
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.order.filter.basic
import Mathlib.algebra.module.pi
import Mathlib.PostPort

universes u_1 u_2 u_3 u_4 u_5 u_6 u_7 

namespace Mathlib

/-!
# Germ of a function at a filter

The germ of a function `f : α → β` at a filter `l : filter α` is the equivalence class of `f`
with respect to the equivalence relation `eventually_eq l`: `f ≈ g` means `∀ᶠ x in l, f x = g x`.

## Main definitions

We define

* `germ l β` to be the space of germs of functions `α → β` at a filter `l : filter α`;
* coercion from `α → β` to `germ l β`: `(f : germ l β)` is the germ of `f : α → β`
  at `l : filter α`; this coercion is declared as `has_coe_t`, so it does not require an explicit
  up arrow `↑`;
* coercion from `β` to `germ l β`: `(↑c : germ l β)` is the germ of the constant function
  `λ x:α, c` at a filter `l`; this coercion is declared as `has_lift_t`, so it requires an explicit
  up arrow `↑`, see [TPiL][TPiL_coe] for details.
* `map (F : β → γ) (f : germ l β)` to be the composition of a function `F` and a germ `f`;
* `map₂ (F : β → γ → δ) (f : germ l β) (g : germ l γ)` to be the germ of `λ x, F (f x) (g x)`
  at `l`;
* `f.tendsto lb`: we say that a germ `f : germ l β` tends to a filter `lb` if its representatives
  tend to `lb` along `l`;
* `f.comp_tendsto g hg` and `f.comp_tendsto' g hg`: given `f : germ l β` and a function
  `g : γ → α` (resp., a germ `g : germ lc α`), if `g` tends to `l` along `lc`, then the composition
  `f ∘ g` is a well-defined germ at `lc`;
* `germ.lift_pred`, `germ.lift_rel`: lift a predicate or a relation to the space of germs:
  `(f : germ l β).lift_pred p` means `∀ᶠ x in l, p (f x)`, and similarly for a relation.
[TPiL_coe]: https://leanprover.github.io/theorem_proving_in_lean/type_classes.html#coercions-using-type-classes

We also define `map (F : β → γ) : germ l β → germ l γ` sending each germ `f` to `F ∘ f`.

For each of the following structures we prove that if `β` has this structure, then so does
`germ l β`:

* one-operation algebraic structures up to `comm_group`;
* `mul_zero_class`, `distrib`, `semiring`, `comm_semiring`, `ring`, `comm_ring`;
* `mul_action`, `distrib_mul_action`, `semimodule`;
* `preorder`, `partial_order`, and `lattice` structures up to `bounded_lattice`;
* `ordered_cancel_comm_monoid` and `ordered_cancel_add_comm_monoid`.

## Tags

filter, germ
-/

namespace filter


theorem const_eventually_eq' {α : Type u_1} {β : Type u_2} {l : filter α} [ne_bot l] {a : β}
    {b : β} : filter.eventually (fun (x : α) => a = b) l ↔ a = b :=
  eventually_const

theorem const_eventually_eq {α : Type u_1} {β : Type u_2} {l : filter α} [ne_bot l] {a : β}
    {b : β} : (eventually_eq l (fun (_x : α) => a) fun (_x : α) => b) ↔ a = b :=
  const_eventually_eq'

theorem eventually_eq.comp_tendsto {α : Type u_1} {β : Type u_2} {γ : Type u_3} {l : filter α}
    {f : α → β} {f' : α → β} (H : eventually_eq l f f') {g : γ → α} {lc : filter γ}
    (hg : tendsto g lc l) : eventually_eq lc (f ∘ g) (f' ∘ g) :=
  tendsto.eventually hg H

/-- Setoid used to define the space of germs. -/
def germ_setoid {α : Type u_1} (l : filter α) (β : Type u_2) : setoid (α → β) :=
  setoid.mk (eventually_eq l) sorry

/-- The space of germs of functions `α → β` at a filter `l`. -/
def germ {α : Type u_1} (l : filter α) (β : Type u_2) := quotient (germ_setoid l β)

namespace germ


protected instance has_coe_t {α : Type u_1} {β : Type u_2} {l : filter α} :
    has_coe_t (α → β) (germ l β) :=
  has_coe_t.mk quotient.mk'

protected instance has_lift_t {α : Type u_1} {β : Type u_2} {l : filter α} :
    has_lift_t β (germ l β) :=
  has_lift_t.mk fun (c : β) => ↑fun (x : α) => c

@[simp] theorem quot_mk_eq_coe {α : Type u_1} {β : Type u_2} (l : filter α) (f : α → β) :
    Quot.mk setoid.r f = ↑f :=
  rfl

@[simp] theorem mk'_eq_coe {α : Type u_1} {β : Type u_2} (l : filter α) (f : α → β) :
    quotient.mk' f = ↑f :=
  rfl

theorem induction_on {α : Type u_1} {β : Type u_2} {l : filter α} (f : germ l β)
    {p : germ l β → Prop} (h : ∀ (f : α → β), p ↑f) : p f :=
  quotient.induction_on' f h

theorem induction_on₂ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {l : filter α} (f : germ l β)
    (g : germ l γ) {p : germ l β → germ l γ → Prop} (h : ∀ (f : α → β) (g : α → γ), p ↑f ↑g) :
    p f g :=
  quotient.induction_on₂' f g h

theorem induction_on₃ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {l : filter α}
    (f : germ l β) (g : germ l γ) (h : germ l δ) {p : germ l β → germ l γ → germ l δ → Prop}
    (H : ∀ (f : α → β) (g : α → γ) (h : α → δ), p ↑f ↑g ↑h) : p f g h :=
  quotient.induction_on₃' f g h H

/-- Given a map `F : (α → β) → (γ → δ)` that sends functions eventually equal at `l` to functions
eventually equal at `lc`, returns a map from `germ l β` to `germ lc δ`. -/
def map' {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {l : filter α} {lc : filter γ}
    (F : (α → β) → γ → δ) (hF : relator.lift_fun (eventually_eq l) (eventually_eq lc) F F) :
    germ l β → germ lc δ :=
  quotient.map' F hF

/-- Given a germ `f : germ l β` and a function `F : (α → β) → γ` sending eventually equal functions
to the same value, returns the value `F` takes on functions having germ `f` at `l`. -/
def lift_on {α : Type u_1} {β : Type u_2} {l : filter α} {γ : Sort u_3} (f : germ l β)
    (F : (α → β) → γ) (hF : relator.lift_fun (eventually_eq l) Eq F F) : γ :=
  quotient.lift_on' f F hF

@[simp] theorem map'_coe {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {l : filter α}
    {lc : filter γ} (F : (α → β) → γ → δ)
    (hF : relator.lift_fun (eventually_eq l) (eventually_eq lc) F F) (f : α → β) :
    map' F hF ↑f = ↑(F f) :=
  rfl

@[simp] theorem coe_eq {α : Type u_1} {β : Type u_2} {l : filter α} {f : α → β} {g : α → β} :
    ↑f = ↑g ↔ eventually_eq l f g :=
  quotient.eq'

theorem Mathlib.filter.eventually_eq.germ_eq {α : Type u_1} {β : Type u_2} {l : filter α}
    {f : α → β} {g : α → β} : eventually_eq l f g → ↑f = ↑g :=
  iff.mpr coe_eq

/-- Lift a function `β → γ` to a function `germ l β → germ l γ`. -/
def map {α : Type u_1} {β : Type u_2} {γ : Type u_3} {l : filter α} (op : β → γ) :
    germ l β → germ l γ :=
  map' (function.comp op) sorry

@[simp] theorem map_coe {α : Type u_1} {β : Type u_2} {γ : Type u_3} {l : filter α} (op : β → γ)
    (f : α → β) : map op ↑f = ↑(op ∘ f) :=
  rfl

@[simp] theorem map_id {α : Type u_1} {β : Type u_2} {l : filter α} : map id = id :=
  funext
    fun (x : germ l β) =>
      quot.induction_on x fun (f : α → β) => Eq.refl (map id (Quot.mk setoid.r f))

theorem map_map {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {l : filter α}
    (op₁ : γ → δ) (op₂ : β → γ) (f : germ l β) : map op₁ (map op₂ f) = map (op₁ ∘ op₂) f :=
  induction_on f fun (f : α → β) => rfl

/-- Lift a binary function `β → γ → δ` to a function `germ l β → germ l γ → germ l δ`. -/
def map₂ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {l : filter α}
    (op : β → γ → δ) : germ l β → germ l γ → germ l δ :=
  quotient.map₂' (fun (f : α → β) (g : α → γ) (x : α) => op (f x) (g x)) sorry

@[simp] theorem map₂_coe {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {l : filter α}
    (op : β → γ → δ) (f : α → β) (g : α → γ) : map₂ op ↑f ↑g = ↑fun (x : α) => op (f x) (g x) :=
  rfl

/-- A germ at `l` of maps from `α` to `β` tends to `lb : filter β` if it is represented by a map
which tends to `lb` along `l`. -/
protected def tendsto {α : Type u_1} {β : Type u_2} {l : filter α} (f : germ l β) (lb : filter β) :=
  lift_on f (fun (f : α → β) => tendsto f l lb) sorry

@[simp] theorem coe_tendsto {α : Type u_1} {β : Type u_2} {l : filter α} {f : α → β}
    {lb : filter β} : germ.tendsto (↑f) lb ↔ tendsto f l lb :=
  iff.rfl

theorem Mathlib.filter.tendsto.germ_tendsto {α : Type u_1} {β : Type u_2} {l : filter α} {f : α → β}
    {lb : filter β} : tendsto f l lb → germ.tendsto (↑f) lb :=
  iff.mpr coe_tendsto

/-- Given two germs `f : germ l β`, and `g : germ lc α`, where `l : filter α`, if `g` tends to `l`,
then the composition `f ∘ g` is well-defined as a germ at `lc`. -/
def comp_tendsto' {α : Type u_1} {β : Type u_2} {γ : Type u_3} {l : filter α} (f : germ l β)
    {lc : filter γ} (g : germ lc α) (hg : germ.tendsto g l) : germ lc β :=
  lift_on f (fun (f : α → β) => map f g) sorry

@[simp] theorem coe_comp_tendsto' {α : Type u_1} {β : Type u_2} {γ : Type u_3} {l : filter α}
    (f : α → β) {lc : filter γ} {g : germ lc α} (hg : germ.tendsto g l) :
    comp_tendsto' (↑f) g hg = map f g :=
  rfl

/-- Given a germ `f : germ l β` and a function `g : γ → α`, where `l : filter α`, if `g` tends
to `l` along `lc : filter γ`, then the composition `f ∘ g` is well-defined as a germ at `lc`. -/
def comp_tendsto {α : Type u_1} {β : Type u_2} {γ : Type u_3} {l : filter α} (f : germ l β)
    {lc : filter γ} (g : γ → α) (hg : tendsto g lc l) : germ lc β :=
  comp_tendsto' f (↑g) (tendsto.germ_tendsto hg)

@[simp] theorem coe_comp_tendsto {α : Type u_1} {β : Type u_2} {γ : Type u_3} {l : filter α}
    (f : α → β) {lc : filter γ} {g : γ → α} (hg : tendsto g lc l) :
    comp_tendsto (↑f) g hg = ↑(f ∘ g) :=
  rfl

@[simp] theorem comp_tendsto'_coe {α : Type u_1} {β : Type u_2} {γ : Type u_3} {l : filter α}
    (f : germ l β) {lc : filter γ} {g : γ → α} (hg : tendsto g lc l) :
    comp_tendsto' f (↑g) (tendsto.germ_tendsto hg) = comp_tendsto f g hg :=
  rfl

@[simp] theorem const_inj {α : Type u_1} {β : Type u_2} {l : filter α} [ne_bot l] {a : β} {b : β} :
    ↑a = ↑b ↔ a = b :=
  iff.trans coe_eq const_eventually_eq

@[simp] theorem map_const {α : Type u_1} {β : Type u_2} {γ : Type u_3} (l : filter α) (a : β)
    (f : β → γ) : map f ↑a = ↑(f a) :=
  rfl

@[simp] theorem map₂_const {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4}
    (l : filter α) (b : β) (c : γ) (f : β → γ → δ) : map₂ f ↑b ↑c = ↑(f b c) :=
  rfl

@[simp] theorem const_comp_tendsto {α : Type u_1} {β : Type u_2} {γ : Type u_3} {l : filter α}
    (b : β) {lc : filter γ} {g : γ → α} (hg : tendsto g lc l) : comp_tendsto (↑b) g hg = ↑b :=
  rfl

@[simp] theorem const_comp_tendsto' {α : Type u_1} {β : Type u_2} {γ : Type u_3} {l : filter α}
    (b : β) {lc : filter γ} {g : germ lc α} (hg : germ.tendsto g l) :
    comp_tendsto' (↑b) g hg = ↑b :=
  induction_on g (fun (_x : γ → α) (_x_1 : germ.tendsto (↑_x) l) => rfl) hg

/-- Lift a predicate on `β` to `germ l β`. -/
def lift_pred {α : Type u_1} {β : Type u_2} {l : filter α} (p : β → Prop) (f : germ l β) :=
  lift_on f (fun (f : α → β) => filter.eventually (fun (x : α) => p (f x)) l) sorry

@[simp] theorem lift_pred_coe {α : Type u_1} {β : Type u_2} {l : filter α} {p : β → Prop}
    {f : α → β} : lift_pred p ↑f ↔ filter.eventually (fun (x : α) => p (f x)) l :=
  iff.rfl

theorem lift_pred_const {α : Type u_1} {β : Type u_2} {l : filter α} {p : β → Prop} {x : β}
    (hx : p x) : lift_pred p ↑x :=
  eventually_of_forall fun (y : α) => hx

@[simp] theorem lift_pred_const_iff {α : Type u_1} {β : Type u_2} {l : filter α} [ne_bot l]
    {p : β → Prop} {x : β} : lift_pred p ↑x ↔ p x :=
  eventually_const

/-- Lift a relation `r : β → γ → Prop` to `germ l β → germ l γ → Prop`. -/
def lift_rel {α : Type u_1} {β : Type u_2} {γ : Type u_3} {l : filter α} (r : β → γ → Prop)
    (f : germ l β) (g : germ l γ) :=
  quotient.lift_on₂' f g
    (fun (f : α → β) (g : α → γ) => filter.eventually (fun (x : α) => r (f x) (g x)) l) sorry

@[simp] theorem lift_rel_coe {α : Type u_1} {β : Type u_2} {γ : Type u_3} {l : filter α}
    {r : β → γ → Prop} {f : α → β} {g : α → γ} :
    lift_rel r ↑f ↑g ↔ filter.eventually (fun (x : α) => r (f x) (g x)) l :=
  iff.rfl

theorem lift_rel_const {α : Type u_1} {β : Type u_2} {γ : Type u_3} {l : filter α}
    {r : β → γ → Prop} {x : β} {y : γ} (h : r x y) : lift_rel r ↑x ↑y :=
  eventually_of_forall fun (_x : α) => h

@[simp] theorem lift_rel_const_iff {α : Type u_1} {β : Type u_2} {γ : Type u_3} {l : filter α}
    [ne_bot l] {r : β → γ → Prop} {x : β} {y : γ} : lift_rel r ↑x ↑y ↔ r x y :=
  eventually_const

protected instance inhabited {α : Type u_1} {β : Type u_2} {l : filter α} [Inhabited β] :
    Inhabited (germ l β) :=
  { default := ↑Inhabited.default }

protected instance has_add {α : Type u_1} {l : filter α} {M : Type u_5} [Add M] : Add (germ l M) :=
  { add := map₂ Add.add }

@[simp] theorem coe_add {α : Type u_1} {l : filter α} {M : Type u_5} [Add M] (f : α → M)
    (g : α → M) : ↑(f + g) = ↑f + ↑g :=
  rfl

protected instance has_one {α : Type u_1} {l : filter α} {M : Type u_5} [HasOne M] :
    HasOne (germ l M) :=
  { one := ↑1 }

@[simp] theorem coe_zero {α : Type u_1} {l : filter α} {M : Type u_5} [HasZero M] : ↑0 = 0 := rfl

protected instance add_semigroup {α : Type u_1} {l : filter α} {M : Type u_5} [add_semigroup M] :
    add_semigroup (germ l M) :=
  add_semigroup.mk Add.add sorry

protected instance add_comm_semigroup {α : Type u_1} {l : filter α} {M : Type u_5}
    [add_comm_semigroup M] : add_comm_semigroup (germ l M) :=
  add_comm_semigroup.mk Add.add sorry sorry

protected instance left_cancel_semigroup {α : Type u_1} {l : filter α} {M : Type u_5}
    [left_cancel_semigroup M] : left_cancel_semigroup (germ l M) :=
  left_cancel_semigroup.mk Mul.mul sorry sorry

protected instance right_cancel_semigroup {α : Type u_1} {l : filter α} {M : Type u_5}
    [right_cancel_semigroup M] : right_cancel_semigroup (germ l M) :=
  right_cancel_semigroup.mk Mul.mul sorry sorry

protected instance monoid {α : Type u_1} {l : filter α} {M : Type u_5} [monoid M] :
    monoid (germ l M) :=
  monoid.mk Mul.mul sorry 1 sorry sorry

/-- coercion from functions to germs as a monoid homomorphism. -/
def coe_mul_hom {α : Type u_1} {M : Type u_5} [monoid M] (l : filter α) : (α → M) →* germ l M :=
  monoid_hom.mk coe sorry sorry

/-- coercion from functions to germs as an additive monoid homomorphism. -/
@[simp] theorem coe_coe_mul_hom {α : Type u_1} {l : filter α} {M : Type u_5} [monoid M] :
    ⇑(coe_mul_hom l) = coe :=
  rfl

protected instance add_comm_monoid {α : Type u_1} {l : filter α} {M : Type u_5}
    [add_comm_monoid M] : add_comm_monoid (germ l M) :=
  add_comm_monoid.mk Add.add sorry 0 sorry sorry sorry

protected instance has_neg {α : Type u_1} {l : filter α} {G : Type u_6} [Neg G] : Neg (germ l G) :=
  { neg := map Neg.neg }

@[simp] theorem coe_neg {α : Type u_1} {l : filter α} {G : Type u_6} [Neg G] (f : α → G) :
    ↑(-f) = -↑f :=
  rfl

protected instance has_div {α : Type u_1} {l : filter α} {M : Type u_5} [Div M] : Div (germ l M) :=
  { div := map₂ Div.div }

@[simp] theorem coe_div {α : Type u_1} {l : filter α} {M : Type u_5} [Div M] (f : α → M)
    (g : α → M) : ↑(f / g) = ↑f / ↑g :=
  rfl

protected instance sub_neg_add_monoid {α : Type u_1} {l : filter α} {G : Type u_6}
    [sub_neg_monoid G] : sub_neg_monoid (germ l G) :=
  sub_neg_monoid.mk add_monoid.add sorry add_monoid.zero sorry sorry Neg.neg Sub.sub

protected instance group {α : Type u_1} {l : filter α} {G : Type u_6} [group G] :
    group (germ l G) :=
  group.mk Mul.mul sorry 1 sorry sorry div_inv_monoid.inv div_inv_monoid.div sorry

protected instance comm_group {α : Type u_1} {l : filter α} {G : Type u_6} [comm_group G] :
    comm_group (germ l G) :=
  comm_group.mk Mul.mul sorry 1 sorry sorry has_inv.inv group.div sorry sorry

protected instance nontrivial {α : Type u_1} {l : filter α} {R : Type u_5} [nontrivial R]
    [ne_bot l] : nontrivial (germ l R) :=
  sorry

protected instance mul_zero_class {α : Type u_1} {l : filter α} {R : Type u_5} [mul_zero_class R] :
    mul_zero_class (germ l R) :=
  mul_zero_class.mk Mul.mul 0 sorry sorry

protected instance distrib {α : Type u_1} {l : filter α} {R : Type u_5} [distrib R] :
    distrib (germ l R) :=
  distrib.mk Mul.mul Add.add sorry sorry

protected instance semiring {α : Type u_1} {l : filter α} {R : Type u_5} [semiring R] :
    semiring (germ l R) :=
  semiring.mk add_comm_monoid.add sorry add_comm_monoid.zero sorry sorry sorry monoid.mul sorry
    monoid.one sorry sorry sorry sorry sorry sorry

/-- Coercion `(α → R) → germ l R` as a `ring_hom`. -/
def coe_ring_hom {α : Type u_1} {R : Type u_5} [semiring R] (l : filter α) : (α → R) →+* germ l R :=
  ring_hom.mk coe sorry sorry sorry sorry

@[simp] theorem coe_coe_ring_hom {α : Type u_1} {l : filter α} {R : Type u_5} [semiring R] :
    ⇑(coe_ring_hom l) = coe :=
  rfl

protected instance ring {α : Type u_1} {l : filter α} {R : Type u_5} [ring R] : ring (germ l R) :=
  ring.mk add_comm_group.add sorry add_comm_group.zero sorry sorry add_comm_group.neg
    add_comm_group.sub sorry sorry monoid.mul sorry monoid.one sorry sorry sorry sorry

protected instance comm_semiring {α : Type u_1} {l : filter α} {R : Type u_5} [comm_semiring R] :
    comm_semiring (germ l R) :=
  comm_semiring.mk semiring.add sorry semiring.zero sorry sorry sorry semiring.mul sorry
    semiring.one sorry sorry sorry sorry sorry sorry sorry

protected instance comm_ring {α : Type u_1} {l : filter α} {R : Type u_5} [comm_ring R] :
    comm_ring (germ l R) :=
  comm_ring.mk ring.add sorry ring.zero sorry sorry ring.neg ring.sub sorry sorry ring.mul sorry
    ring.one sorry sorry sorry sorry sorry

protected instance has_scalar {α : Type u_1} {β : Type u_2} {l : filter α} {M : Type u_5}
    [has_scalar M β] : has_scalar M (germ l β) :=
  has_scalar.mk fun (c : M) => map (has_scalar.smul c)

protected instance has_scalar' {α : Type u_1} {β : Type u_2} {l : filter α} {M : Type u_5}
    [has_scalar M β] : has_scalar (germ l M) (germ l β) :=
  has_scalar.mk (map₂ has_scalar.smul)

@[simp] theorem coe_smul {α : Type u_1} {β : Type u_2} {l : filter α} {M : Type u_5}
    [has_scalar M β] (c : M) (f : α → β) : ↑(c • f) = c • ↑f :=
  rfl

@[simp] theorem coe_smul' {α : Type u_1} {β : Type u_2} {l : filter α} {M : Type u_5}
    [has_scalar M β] (c : α → M) (f : α → β) : ↑(c • f) = ↑c • ↑f :=
  rfl

protected instance mul_action {α : Type u_1} {β : Type u_2} {l : filter α} {M : Type u_5} [monoid M]
    [mul_action M β] : mul_action M (germ l β) :=
  mul_action.mk sorry sorry

protected instance mul_action' {α : Type u_1} {β : Type u_2} {l : filter α} {M : Type u_5}
    [monoid M] [mul_action M β] : mul_action (germ l M) (germ l β) :=
  mul_action.mk sorry sorry

protected instance distrib_mul_action {α : Type u_1} {l : filter α} {M : Type u_5} {N : Type u_6}
    [monoid M] [add_monoid N] [distrib_mul_action M N] : distrib_mul_action M (germ l N) :=
  distrib_mul_action.mk sorry sorry

protected instance distrib_mul_action' {α : Type u_1} {l : filter α} {M : Type u_5} {N : Type u_6}
    [monoid M] [add_monoid N] [distrib_mul_action M N] : distrib_mul_action (germ l M) (germ l N) :=
  distrib_mul_action.mk sorry sorry

protected instance semimodule {α : Type u_1} {l : filter α} {M : Type u_5} {R : Type u_7}
    [semiring R] [add_comm_monoid M] [semimodule R M] : semimodule R (germ l M) :=
  semimodule.mk sorry sorry

protected instance semimodule' {α : Type u_1} {l : filter α} {M : Type u_5} {R : Type u_7}
    [semiring R] [add_comm_monoid M] [semimodule R M] : semimodule (germ l R) (germ l M) :=
  semimodule.mk sorry sorry

protected instance has_le {α : Type u_1} {β : Type u_2} {l : filter α} [HasLessEq β] :
    HasLessEq (germ l β) :=
  { LessEq := lift_rel LessEq }

@[simp] theorem coe_le {α : Type u_1} {β : Type u_2} {l : filter α} {f : α → β} {g : α → β}
    [HasLessEq β] : ↑f ≤ ↑g ↔ eventually_le l f g :=
  iff.rfl

theorem le_def {α : Type u_1} {β : Type u_2} {l : filter α} [HasLessEq β] :
    LessEq = lift_rel LessEq :=
  rfl

theorem const_le {α : Type u_1} {β : Type u_2} {l : filter α} [HasLessEq β] {x : β} {y : β}
    (h : x ≤ y) : ↑x ≤ ↑y :=
  lift_rel_const h

@[simp] theorem const_le_iff {α : Type u_1} {β : Type u_2} {l : filter α} [HasLessEq β] [ne_bot l]
    {x : β} {y : β} : ↑x ≤ ↑y ↔ x ≤ y :=
  lift_rel_const_iff

protected instance preorder {α : Type u_1} {β : Type u_2} {l : filter α} [preorder β] :
    preorder (germ l β) :=
  preorder.mk LessEq (fun (a b : germ l β) => a ≤ b ∧ ¬b ≤ a) sorry sorry

protected instance partial_order {α : Type u_1} {β : Type u_2} {l : filter α} [partial_order β] :
    partial_order (germ l β) :=
  partial_order.mk LessEq preorder.lt sorry sorry sorry

protected instance has_bot {α : Type u_1} {β : Type u_2} {l : filter α} [has_bot β] :
    has_bot (germ l β) :=
  has_bot.mk ↑⊥

@[simp] theorem const_bot {α : Type u_1} {β : Type u_2} {l : filter α} [has_bot β] : ↑⊥ = ⊥ := rfl

protected instance order_bot {α : Type u_1} {β : Type u_2} {l : filter α} [order_bot β] :
    order_bot (germ l β) :=
  order_bot.mk ⊥ LessEq partial_order.lt sorry sorry sorry sorry

protected instance has_top {α : Type u_1} {β : Type u_2} {l : filter α} [has_top β] :
    has_top (germ l β) :=
  has_top.mk ↑⊤

@[simp] theorem const_top {α : Type u_1} {β : Type u_2} {l : filter α} [has_top β] : ↑⊤ = ⊤ := rfl

protected instance order_top {α : Type u_1} {β : Type u_2} {l : filter α} [order_top β] :
    order_top (germ l β) :=
  order_top.mk ⊤ LessEq partial_order.lt sorry sorry sorry sorry

protected instance has_sup {α : Type u_1} {β : Type u_2} {l : filter α} [has_sup β] :
    has_sup (germ l β) :=
  has_sup.mk (map₂ has_sup.sup)

@[simp] theorem const_sup {α : Type u_1} {β : Type u_2} {l : filter α} [has_sup β] (a : β) (b : β) :
    ↑(a ⊔ b) = ↑a ⊔ ↑b :=
  rfl

protected instance has_inf {α : Type u_1} {β : Type u_2} {l : filter α} [has_inf β] :
    has_inf (germ l β) :=
  has_inf.mk (map₂ has_inf.inf)

@[simp] theorem const_inf {α : Type u_1} {β : Type u_2} {l : filter α} [has_inf β] (a : β) (b : β) :
    ↑(a ⊓ b) = ↑a ⊓ ↑b :=
  rfl

protected instance semilattice_sup {α : Type u_1} {β : Type u_2} {l : filter α}
    [semilattice_sup β] : semilattice_sup (germ l β) :=
  semilattice_sup.mk has_sup.sup partial_order.le partial_order.lt sorry sorry sorry sorry sorry
    sorry

protected instance semilattice_inf {α : Type u_1} {β : Type u_2} {l : filter α}
    [semilattice_inf β] : semilattice_inf (germ l β) :=
  semilattice_inf.mk has_inf.inf partial_order.le partial_order.lt sorry sorry sorry sorry sorry
    sorry

protected instance semilattice_inf_bot {α : Type u_1} {β : Type u_2} {l : filter α}
    [semilattice_inf_bot β] : semilattice_inf_bot (germ l β) :=
  semilattice_inf_bot.mk order_bot.bot semilattice_inf.le semilattice_inf.lt sorry sorry sorry sorry
    semilattice_inf.inf sorry sorry sorry

protected instance semilattice_sup_bot {α : Type u_1} {β : Type u_2} {l : filter α}
    [semilattice_sup_bot β] : semilattice_sup_bot (germ l β) :=
  semilattice_sup_bot.mk order_bot.bot semilattice_sup.le semilattice_sup.lt sorry sorry sorry sorry
    semilattice_sup.sup sorry sorry sorry

protected instance semilattice_inf_top {α : Type u_1} {β : Type u_2} {l : filter α}
    [semilattice_inf_top β] : semilattice_inf_top (germ l β) :=
  semilattice_inf_top.mk order_top.top semilattice_inf.le semilattice_inf.lt sorry sorry sorry sorry
    semilattice_inf.inf sorry sorry sorry

protected instance semilattice_sup_top {α : Type u_1} {β : Type u_2} {l : filter α}
    [semilattice_sup_top β] : semilattice_sup_top (germ l β) :=
  semilattice_sup_top.mk order_top.top semilattice_sup.le semilattice_sup.lt sorry sorry sorry sorry
    semilattice_sup.sup sorry sorry sorry

protected instance lattice {α : Type u_1} {β : Type u_2} {l : filter α} [lattice β] :
    lattice (germ l β) :=
  lattice.mk semilattice_sup.sup semilattice_sup.le semilattice_sup.lt sorry sorry sorry sorry sorry
    sorry semilattice_inf.inf sorry sorry sorry

protected instance bounded_lattice {α : Type u_1} {β : Type u_2} {l : filter α}
    [bounded_lattice β] : bounded_lattice (germ l β) :=
  bounded_lattice.mk lattice.sup lattice.le lattice.lt sorry sorry sorry sorry sorry sorry
    lattice.inf sorry sorry sorry order_top.top sorry order_bot.bot sorry

protected instance ordered_cancel_add_comm_monoid {α : Type u_1} {β : Type u_2} {l : filter α}
    [ordered_cancel_add_comm_monoid β] : ordered_cancel_add_comm_monoid (germ l β) :=
  ordered_cancel_add_comm_monoid.mk add_comm_monoid.add sorry sorry add_comm_monoid.zero sorry sorry
    sorry sorry partial_order.le partial_order.lt sorry sorry sorry sorry sorry

protected instance ordered_add_comm_group {α : Type u_1} {β : Type u_2} {l : filter α}
    [ordered_add_comm_group β] : ordered_add_comm_group (germ l β) :=
  ordered_add_comm_group.mk add_comm_group.add sorry add_comm_group.zero sorry sorry
    add_comm_group.neg add_comm_group.sub sorry sorry partial_order.le partial_order.lt sorry sorry
    sorry sorry

end Mathlib