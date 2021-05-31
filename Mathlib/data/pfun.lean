/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Jeremy Avigad, Simon Hudon
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.rel
import Mathlib.PostPort

universes u l u_1 u_2 u_3 

namespace Mathlib

/-- `roption α` is the type of "partial values" of type `α`. It
  is similar to `option α` except the domain condition can be an
  arbitrary proposition, not necessarily decidable. -/
structure roption (α : Type u) 
where
  dom : Prop
  get : dom → α

namespace roption


/-- Convert an `roption α` with a decidable domain to an option -/
def to_option {α : Type u_1} (o : roption α) [Decidable (dom o)] : Option α :=
  dite (dom o) (fun (h : dom o) => some (get o h)) fun (h : ¬dom o) => none

/-- `roption` extensionality -/
theorem ext' {α : Type u_1} {o : roption α} {p : roption α} (H1 : dom o ↔ dom p) (H2 : ∀ (h₁ : dom o) (h₂ : dom p), get o h₁ = get p h₂) : o = p := sorry

/-- `roption` eta expansion -/
@[simp] theorem eta {α : Type u_1} (o : roption α) : (mk (dom o) fun (h : dom o) => get o h) = o := sorry

/-- `a ∈ o` means that `o` is defined and equal to `a` -/
protected def mem {α : Type u_1} (a : α) (o : roption α) :=
  ∃ (h : dom o), get o h = a

protected instance has_mem {α : Type u_1} : has_mem α (roption α) :=
  has_mem.mk roption.mem

theorem mem_eq {α : Type u_1} (a : α) (o : roption α) : a ∈ o = ∃ (h : dom o), get o h = a :=
  rfl

theorem dom_iff_mem {α : Type u_1} {o : roption α} : dom o ↔ ∃ (y : α), y ∈ o := sorry

theorem get_mem {α : Type u_1} {o : roption α} (h : dom o) : get o h ∈ o :=
  Exists.intro h rfl

/-- `roption` extensionality -/
theorem ext {α : Type u_1} {o : roption α} {p : roption α} (H : ∀ (a : α), a ∈ o ↔ a ∈ p) : o = p := sorry

/-- The `none` value in `roption` has a `false` domain and an empty function. -/
def none {α : Type u_1} : roption α :=
  mk False False._oldrec

protected instance inhabited {α : Type u_1} : Inhabited (roption α) :=
  { default := none }

@[simp] theorem not_mem_none {α : Type u_1} (a : α) : ¬a ∈ none :=
  fun (h : a ∈ none) => Exists.fst h

/-- The `some a` value in `roption` has a `true` domain and the
  function returns `a`. -/
def some {α : Type u_1} (a : α) : roption α :=
  mk True fun (_x : True) => a

theorem mem_unique {α : Type u_1} : relator.left_unique has_mem.mem := sorry

theorem get_eq_of_mem {α : Type u_1} {o : roption α} {a : α} (h : a ∈ o) (h' : dom o) : get o h' = a :=
  mem_unique (Exists.intro h' rfl) h

@[simp] theorem get_some {α : Type u_1} {a : α} (ha : dom (some a)) : get (some a) ha = a :=
  rfl

theorem mem_some {α : Type u_1} (a : α) : a ∈ some a :=
  Exists.intro trivial rfl

@[simp] theorem mem_some_iff {α : Type u_1} {a : α} {b : α} : b ∈ some a ↔ b = a := sorry

theorem eq_some_iff {α : Type u_1} {a : α} {o : roption α} : o = some a ↔ a ∈ o := sorry

theorem eq_none_iff {α : Type u_1} {o : roption α} : o = none ↔ ∀ (a : α), ¬a ∈ o := sorry

theorem eq_none_iff' {α : Type u_1} {o : roption α} : o = none ↔ ¬dom o :=
  { mp := fun (e : o = none) => Eq.symm e ▸ id,
    mpr := fun (h : ¬dom o) => iff.mpr eq_none_iff fun (a : α) (h' : a ∈ o) => h (Exists.fst h') }

theorem some_ne_none {α : Type u_1} (x : α) : some x ≠ none :=
  id fun (h : some x = none) => id (eq.mpr (id (Eq._oldrec (Eq.refl (dom none)) (Eq.symm h))) trivial)

theorem ne_none_iff {α : Type u_1} {o : roption α} : o ≠ none ↔ ∃ (x : α), o = some x := sorry

theorem eq_none_or_eq_some {α : Type u_1} (o : roption α) : o = none ∨ ∃ (x : α), o = some x := sorry

@[simp] theorem some_inj {α : Type u_1} {a : α} {b : α} : some a = some b ↔ a = b :=
  function.injective.eq_iff fun (a b : α) (h : some a = some b) => congr_fun (eq_of_heq (and.right (mk.inj h))) trivial

@[simp] theorem some_get {α : Type u_1} {a : roption α} (ha : dom a) : some (get a ha) = a :=
  Eq.symm (iff.mpr eq_some_iff (Exists.intro ha rfl))

theorem get_eq_iff_eq_some {α : Type u_1} {a : roption α} {ha : dom a} {b : α} : get a ha = b ↔ a = some b := sorry

protected instance none_decidable {α : Type u_1} : Decidable (dom none) :=
  decidable.false

protected instance some_decidable {α : Type u_1} (a : α) : Decidable (dom (some a)) :=
  decidable.true

def get_or_else {α : Type u_1} (a : roption α) [Decidable (dom a)] (d : α) : α :=
  dite (dom a) (fun (ha : dom a) => get a ha) fun (ha : ¬dom a) => d

@[simp] theorem get_or_else_none {α : Type u_1} (d : α) : get_or_else none d = d :=
  dif_neg id

@[simp] theorem get_or_else_some {α : Type u_1} (a : α) (d : α) : get_or_else (some a) d = a :=
  dif_pos trivial

@[simp] theorem mem_to_option {α : Type u_1} {o : roption α} [Decidable (dom o)] {a : α} : a ∈ to_option o ↔ a ∈ o := sorry

/-- Convert an `option α` into an `roption α` -/
def of_option {α : Type u_1} : Option α → roption α :=
  sorry

@[simp] theorem mem_of_option {α : Type u_1} {a : α} {o : Option α} : a ∈ of_option o ↔ a ∈ o := sorry

@[simp] theorem of_option_dom {α : Type u_1} (o : Option α) : dom (of_option o) ↔ ↥(option.is_some o) := sorry

theorem of_option_eq_get {α : Type u_1} (o : Option α) : of_option o = mk (↥(option.is_some o)) option.get := sorry

protected instance has_coe {α : Type u_1} : has_coe (Option α) (roption α) :=
  has_coe.mk of_option

@[simp] theorem mem_coe {α : Type u_1} {a : α} {o : Option α} : a ∈ ↑o ↔ a ∈ o :=
  mem_of_option

@[simp] theorem coe_none {α : Type u_1} : ↑none = none :=
  rfl

@[simp] theorem coe_some {α : Type u_1} (a : α) : ↑(some a) = some a :=
  rfl

protected theorem induction_on {α : Type u_1} {P : roption α → Prop} (a : roption α) (hnone : P none) (hsome : ∀ (a : α), P (some a)) : P a :=
  or.elim (classical.em (dom a)) (fun (h : dom a) => some_get h ▸ hsome (get a h))
    fun (h : ¬dom a) => Eq.symm (iff.mpr eq_none_iff' h) ▸ hnone

protected instance of_option_decidable {α : Type u_1} (o : Option α) : Decidable (dom (of_option o)) :=
  sorry

@[simp] theorem to_of_option {α : Type u_1} (o : Option α) : to_option (of_option o) = o :=
  option.cases_on o (Eq.refl (to_option (of_option none))) fun (o : α) => Eq.refl (to_option (of_option (some o)))

@[simp] theorem of_to_option {α : Type u_1} (o : roption α) [Decidable (dom o)] : of_option (to_option o) = o :=
  ext fun (a : α) => iff.trans mem_of_option mem_to_option

def equiv_option {α : Type u_1} : roption α ≃ Option α :=
  equiv.mk (fun (o : roption α) => to_option o) of_option sorry sorry

protected instance order_bot {α : Type u_1} : order_bot (roption α) :=
  order_bot.mk none (fun (x y : roption α) => ∀ (i : α), i ∈ x → i ∈ y)
    (partial_order.lt._default fun (x y : roption α) => ∀ (i : α), i ∈ x → i ∈ y) sorry sorry sorry sorry

protected instance preorder {α : Type u_1} : preorder (roption α) :=
  partial_order.to_preorder (roption α)

theorem le_total_of_le_of_le {α : Type u_1} {x : roption α} {y : roption α} (z : roption α) (hx : x ≤ z) (hy : y ≤ z) : x ≤ y ∨ y ≤ x := sorry

/-- `assert p f` is a bind-like operation which appends an additional condition
  `p` to the domain and uses `f` to produce the value. -/
def assert {α : Type u_1} (p : Prop) (f : p → roption α) : roption α :=
  mk (∃ (h : p), dom (f h)) fun (ha : ∃ (h : p), dom (f h)) => get (f sorry) sorry

/-- The bind operation has value `g (f.get)`, and is defined when all the
  parts are defined. -/
protected def bind {α : Type u_1} {β : Type u_2} (f : roption α) (g : α → roption β) : roption β :=
  assert (dom f) fun (b : dom f) => g (get f b)

/-- The map operation for `roption` just maps the value and maintains the same domain. -/
def map {α : Type u_1} {β : Type u_2} (f : α → β) (o : roption α) : roption β :=
  mk (dom o) (f ∘ get o)

theorem mem_map {α : Type u_1} {β : Type u_2} (f : α → β) {o : roption α} {a : α} : a ∈ o → f a ∈ map f o := sorry

@[simp] theorem mem_map_iff {α : Type u_1} {β : Type u_2} (f : α → β) {o : roption α} {b : β} : b ∈ map f o ↔ ∃ (a : α), ∃ (H : a ∈ o), f a = b := sorry

@[simp] theorem map_none {α : Type u_1} {β : Type u_2} (f : α → β) : map f none = none := sorry

@[simp] theorem map_some {α : Type u_1} {β : Type u_2} (f : α → β) (a : α) : map f (some a) = some (f a) :=
  iff.mpr eq_some_iff (mem_map f (mem_some a))

theorem mem_assert {α : Type u_1} {p : Prop} {f : p → roption α} {a : α} (h : p) : a ∈ f h → a ∈ assert p f := sorry

@[simp] theorem mem_assert_iff {α : Type u_1} {p : Prop} {f : p → roption α} {a : α} : a ∈ assert p f ↔ ∃ (h : p), a ∈ f h := sorry

theorem assert_pos {α : Type u_1} {p : Prop} {f : p → roption α} (h : p) : assert p f = f h := sorry

theorem assert_neg {α : Type u_1} {p : Prop} {f : p → roption α} (h : ¬p) : assert p f = none := sorry

theorem mem_bind {α : Type u_1} {β : Type u_2} {f : roption α} {g : α → roption β} {a : α} {b : β} : a ∈ f → b ∈ g a → b ∈ roption.bind f g := sorry

@[simp] theorem mem_bind_iff {α : Type u_1} {β : Type u_2} {f : roption α} {g : α → roption β} {b : β} : b ∈ roption.bind f g ↔ ∃ (a : α), ∃ (H : a ∈ f), b ∈ g a := sorry

@[simp] theorem bind_none {α : Type u_1} {β : Type u_2} (f : α → roption β) : roption.bind none f = none := sorry

@[simp] theorem bind_some {α : Type u_1} {β : Type u_2} (a : α) (f : α → roption β) : roption.bind (some a) f = f a := sorry

theorem bind_some_eq_map {α : Type u_1} {β : Type u_2} (f : α → β) (x : roption α) : roption.bind x (some ∘ f) = map f x := sorry

theorem bind_assoc {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : roption α) (g : α → roption β) (k : β → roption γ) : roption.bind (roption.bind f g) k = roption.bind f fun (x : α) => roption.bind (g x) k := sorry

@[simp] theorem bind_map {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : α → β) (x : roption α) (g : β → roption γ) : roption.bind (map f x) g = roption.bind x fun (y : α) => g (f y) := sorry

@[simp] theorem map_bind {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : α → roption β) (x : roption α) (g : β → γ) : map g (roption.bind x f) = roption.bind x fun (y : α) => map g (f y) := sorry

theorem map_map {α : Type u_1} {β : Type u_2} {γ : Type u_3} (g : β → γ) (f : α → β) (o : roption α) : map g (map f o) = map (g ∘ f) o := sorry

protected instance monad : Monad roption :=
  { toApplicative :=
      { toFunctor := { map := map, mapConst := fun (α β : Type u_1) => map ∘ function.const β },
        toPure := { pure := some },
        toSeq :=
          { seq :=
              fun (α β : Type u_1) (f : roption (α → β)) (x : roption α) => roption.bind f fun (_x : α → β) => map _x x },
        toSeqLeft :=
          { seqLeft :=
              fun (α β : Type u_1) (a : roption α) (b : roption β) =>
                (fun (α β : Type u_1) (f : roption (α → β)) (x : roption α) =>
                    roption.bind f fun (_x : α → β) => map _x x)
                  β α (map (function.const β) a) b },
        toSeqRight :=
          { seqRight :=
              fun (α β : Type u_1) (a : roption α) (b : roption β) =>
                (fun (α β : Type u_1) (f : roption (α → β)) (x : roption α) =>
                    roption.bind f fun (_x : α → β) => map _x x)
                  β β (map (function.const α id) a) b } },
    toBind := { bind := roption.bind } }

protected instance is_lawful_monad : is_lawful_monad roption :=
  is_lawful_monad.mk bind_some bind_assoc

theorem map_id' {α : Type u_1} {f : α → α} (H : ∀ (x : α), f x = x) (o : roption α) : map f o = o :=
  eq.mpr (id (Eq._oldrec (Eq.refl (map f o = o)) ((fun (this : f = id) => this) (funext H)))) (id_map o)

@[simp] theorem bind_some_right {α : Type u_1} (x : roption α) : roption.bind x some = x := sorry

@[simp] theorem pure_eq_some {α : Type u_1} (a : α) : pure a = some a :=
  rfl

@[simp] theorem ret_eq_some {α : Type u_1} (a : α) : return a = some a :=
  rfl

@[simp] theorem map_eq_map {α : Type u_1} {β : Type u_1} (f : α → β) (o : roption α) : f <$> o = map f o :=
  rfl

@[simp] theorem bind_eq_bind {α : Type u_1} {β : Type u_1} (f : roption α) (g : α → roption β) : f >>= g = roption.bind f g :=
  rfl

theorem bind_le {β : Type u_2} {α : Type u_2} (x : roption α) (f : α → roption β) (y : roption β) : x >>= f ≤ y ↔ ∀ (a : α), a ∈ x → f a ≤ y := sorry

protected instance monad_fail : monad_fail roption :=
  monad_fail.mk fun (_x : Type u_1) (_x_1 : string) => none

/- `restrict p o h` replaces the domain of `o` with `p`, and is well defined when
  `p` implies `o` is defined. -/

def restrict {α : Type u_1} (p : Prop) (o : roption α) : (p → dom o) → roption α :=
  sorry

@[simp] theorem mem_restrict {α : Type u_1} (p : Prop) (o : roption α) (h : p → dom o) (a : α) : a ∈ restrict p o h ↔ p ∧ a ∈ o := sorry

/-- `unwrap o` gets the value at `o`, ignoring the condition.
  (This function is unsound.) -/
theorem assert_defined {α : Type u_1} {p : Prop} {f : p → roption α} (h : p) : dom (f h) → dom (assert p f) :=
  exists.intro

theorem bind_defined {α : Type u_1} {β : Type u_2} {f : roption α} {g : α → roption β} (h : dom f) : dom (g (get f h)) → dom (roption.bind f g) :=
  assert_defined

@[simp] theorem bind_dom {α : Type u_1} {β : Type u_2} {f : roption α} {g : α → roption β} : dom (roption.bind f g) ↔ ∃ (h : dom f), dom (g (get f h)) :=
  iff.rfl

end roption


/-- `pfun α β`, or `α →. β`, is the type of partial functions from
  `α` to `β`. It is defined as `α → roption β`. -/
def pfun (α : Type u_1) (β : Type u_2) :=
  α → roption β

infixr:25 " →. " => Mathlib.pfun

namespace pfun


protected instance inhabited {α : Type u_1} {β : Type u_2} : Inhabited (α →. β) :=
  { default := fun (a : α) => roption.none }

/-- The domain of a partial function -/
def dom {α : Type u_1} {β : Type u_2} (f : α →. β) : set α :=
  set_of fun (a : α) => roption.dom (f a)

theorem mem_dom {α : Type u_1} {β : Type u_2} (f : α →. β) (x : α) : x ∈ dom f ↔ ∃ (y : β), y ∈ f x := sorry

theorem dom_eq {α : Type u_1} {β : Type u_2} (f : α →. β) : dom f = set_of fun (x : α) => ∃ (y : β), y ∈ f x :=
  set.ext (mem_dom f)

/-- Evaluate a partial function -/
def fn {α : Type u_1} {β : Type u_2} (f : α →. β) (x : α) (h : dom f x) : β :=
  roption.get (f x) h

/-- Evaluate a partial function to return an `option` -/
def eval_opt {α : Type u_1} {β : Type u_2} (f : α →. β) [D : decidable_pred (dom f)] (x : α) : Option β :=
  roption.to_option (f x)

/-- Partial function extensionality -/
theorem ext' {α : Type u_1} {β : Type u_2} {f : α →. β} {g : α →. β} (H1 : ∀ (a : α), a ∈ dom f ↔ a ∈ dom g) (H2 : ∀ (a : α) (p : dom f a) (q : dom g a), fn f a p = fn g a q) : f = g :=
  funext fun (a : α) => roption.ext' (H1 a) (H2 a)

theorem ext {α : Type u_1} {β : Type u_2} {f : α →. β} {g : α →. β} (H : ∀ (a : α) (b : β), b ∈ f a ↔ b ∈ g a) : f = g :=
  funext fun (a : α) => roption.ext (H a)

/-- Turn a partial function into a function out of a subtype -/
def as_subtype {α : Type u_1} {β : Type u_2} (f : α →. β) (s : ↥(dom f)) : β :=
  fn f ↑s sorry

/-- The set of partial functions `α →. β` is equivalent to
the set of pairs `(p : α → Prop, f : subtype p → β)`. -/
def equiv_subtype {α : Type u_1} {β : Type u_2} : (α →. β) ≃ sigma fun (p : α → Prop) => Subtype p → β :=
  equiv.mk (fun (f : α →. β) => sigma.mk (fun (a : α) => roption.dom (f a)) (as_subtype f))
    (fun (f : sigma fun (p : α → Prop) => Subtype p → β) (x : α) =>
      roption.mk (sigma.fst f x) fun (h : sigma.fst f x) => sigma.snd f { val := x, property := h })
    sorry sorry

theorem as_subtype_eq_of_mem {α : Type u_1} {β : Type u_2} {f : α →. β} {x : α} {y : β} (fxy : y ∈ f x) (domx : x ∈ dom f) : as_subtype f { val := x, property := domx } = y :=
  roption.mem_unique (roption.get_mem (as_subtype._proof_1 f { val := x, property := domx })) fxy

/-- Turn a total function into a partial function -/
protected def lift {α : Type u_1} {β : Type u_2} (f : α → β) : α →. β :=
  fun (a : α) => roption.some (f a)

protected instance has_coe {α : Type u_1} {β : Type u_2} : has_coe (α → β) (α →. β) :=
  has_coe.mk pfun.lift

@[simp] theorem lift_eq_coe {α : Type u_1} {β : Type u_2} (f : α → β) : pfun.lift f = ↑f :=
  rfl

@[simp] theorem coe_val {α : Type u_1} {β : Type u_2} (f : α → β) (a : α) : coe f a = roption.some (f a) :=
  rfl

/-- The graph of a partial function is the set of pairs
  `(x, f x)` where `x` is in the domain of `f`. -/
def graph {α : Type u_1} {β : Type u_2} (f : α →. β) : set (α × β) :=
  set_of fun (p : α × β) => prod.snd p ∈ f (prod.fst p)

def graph' {α : Type u_1} {β : Type u_2} (f : α →. β) : rel α β :=
  fun (x : α) (y : β) => y ∈ f x

/-- The range of a partial function is the set of values
  `f x` where `x` is in the domain of `f`. -/
def ran {α : Type u_1} {β : Type u_2} (f : α →. β) : set β :=
  set_of fun (b : β) => ∃ (a : α), b ∈ f a

/-- Restrict a partial function to a smaller domain. -/
def restrict {α : Type u_1} {β : Type u_2} (f : α →. β) {p : set α} (H : p ⊆ dom f) : α →. β :=
  fun (x : α) => roption.restrict (x ∈ p) (f x) H

@[simp] theorem mem_restrict {α : Type u_1} {β : Type u_2} {f : α →. β} {s : set α} (h : s ⊆ dom f) (a : α) (b : β) : b ∈ restrict f h a ↔ a ∈ s ∧ b ∈ f a := sorry

def res {α : Type u_1} {β : Type u_2} (f : α → β) (s : set α) : α →. β :=
  restrict (pfun.lift f) (set.subset_univ s)

theorem mem_res {α : Type u_1} {β : Type u_2} (f : α → β) (s : set α) (a : α) (b : β) : b ∈ res f s a ↔ a ∈ s ∧ f a = b := sorry

theorem res_univ {α : Type u_1} {β : Type u_2} (f : α → β) : res f set.univ = ↑f :=
  rfl

theorem dom_iff_graph {α : Type u_1} {β : Type u_2} (f : α →. β) (x : α) : x ∈ dom f ↔ ∃ (y : β), (x, y) ∈ graph f :=
  roption.dom_iff_mem

theorem lift_graph {α : Type u_1} {β : Type u_2} {f : α → β} {a : α} {b : β} : (a, b) ∈ graph ↑f ↔ f a = b := sorry

/-- The monad `pure` function, the total constant `x` function -/
protected def pure {α : Type u_1} {β : Type u_2} (x : β) : α →. β :=
  fun (_x : α) => roption.some x

/-- The monad `bind` function, pointwise `roption.bind` -/
def bind {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : α →. β) (g : β → α →. γ) : α →. γ :=
  fun (a : α) => roption.bind (f a) fun (b : β) => g b a

/-- The monad `map` function, pointwise `roption.map` -/
def map {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : β → γ) (g : α →. β) : α →. γ :=
  fun (a : α) => roption.map f (g a)

protected instance monad {α : Type u_1} : Monad (pfun α) :=
  { toApplicative :=
      { toFunctor := { map := map, mapConst := fun (α_1 β : Type u_2) => map ∘ function.const β },
        toPure := { pure := pfun.pure },
        toSeq :=
          { seq := fun (α_1 β : Type u_2) (f : α →. α_1 → β) (x : α →. α_1) => bind f fun (_x : α_1 → β) => map _x x },
        toSeqLeft :=
          { seqLeft :=
              fun (α_1 β : Type u_2) (a : α →. α_1) (b : α →. β) =>
                (fun (α_2 β : Type u_2) (f : α →. α_2 → β) (x : α →. α_2) => bind f fun (_x : α_2 → β) => map _x x) β α_1
                  (map (function.const β) a) b },
        toSeqRight :=
          { seqRight :=
              fun (α_1 β : Type u_2) (a : α →. α_1) (b : α →. β) =>
                (fun (α_2 β : Type u_2) (f : α →. α_2 → β) (x : α →. α_2) => bind f fun (_x : α_2 → β) => map _x x) β β
                  (map (function.const α_1 id) a) b } },
    toBind := { bind := bind } }

protected instance is_lawful_monad {α : Type u_1} : is_lawful_monad (pfun α) :=
  is_lawful_monad.mk (fun (β γ : Type u_2) (x : β) (f : β → α →. γ) => funext fun (a : α) => roption.bind_some a (f x))
    fun (β γ δ : Type u_2) (f : α →. β) (g : β → α →. γ) (k : γ → α →. δ) =>
      funext fun (a : α) => roption.bind_assoc (f a) (fun (b : β) => g b a) fun (b : γ) => k b a

theorem pure_defined {α : Type u_1} {β : Type u_2} (p : set α) (x : β) : p ⊆ dom (pfun.pure x) :=
  set.subset_univ p

theorem bind_defined {α : Type u_1} {β : Type u_2} {γ : Type u_2} (p : set α) {f : α →. β} {g : β → α →. γ} (H1 : p ⊆ dom f) (H2 : ∀ (x : β), p ⊆ dom (g x)) : p ⊆ dom (f >>= g) :=
  fun (a : α) (ha : a ∈ p) => Exists.intro (H1 ha) (H2 (roption.get (f a) (H1 ha)) ha)

def fix {α : Type u_1} {β : Type u_2} (f : α →. β ⊕ α) : α →. β :=
  fun (a : α) =>
    roption.assert (acc (fun (x y : α) => sum.inr x ∈ f y) a)
      fun (h : acc (fun (x y : α) => sum.inr x ∈ f y) a) =>
        well_founded.fix_F
          (fun (a : α) (IH : (y : α) → sum.inr y ∈ f a → roption β) =>
            roption.assert (roption.dom (f a))
              fun (hf : roption.dom (f a)) =>
                (fun (_x : β ⊕ α) (e : roption.get (f a) hf = _x) =>
                    sum.cases_on _x (fun (b : β) (e : roption.get (f a) hf = sum.inl b) => roption.some b)
                      (fun (a' : α) (e : roption.get (f a) hf = sum.inr a') => IH a' sorry) e)
                  (roption.get (f a) hf) sorry)
          a h

theorem dom_of_mem_fix {α : Type u_1} {β : Type u_2} {f : α →. β ⊕ α} {a : α} {b : β} (h : b ∈ fix f a) : roption.dom (f a) := sorry

theorem mem_fix_iff {α : Type u_1} {β : Type u_2} {f : α →. β ⊕ α} {a : α} {b : β} : b ∈ fix f a ↔ sum.inl b ∈ f a ∨ ∃ (a' : α), sum.inr a' ∈ f a ∧ b ∈ fix f a' := sorry

def fix_induction {α : Type u_1} {β : Type u_2} {f : α →. β ⊕ α} {b : β} {C : α → Sort u_3} {a : α} (h : b ∈ fix f a) (H : (a : α) → b ∈ fix f a → ((a' : α) → b ∈ fix f a' → sum.inr a' ∈ f a → C a') → C a) : C a := sorry

end pfun


namespace pfun


def image {α : Type u_1} {β : Type u_2} (f : α →. β) (s : set α) : set β :=
  rel.image (graph' f) s

theorem image_def {α : Type u_1} {β : Type u_2} (f : α →. β) (s : set α) : image f s = set_of fun (y : β) => ∃ (x : α), ∃ (H : x ∈ s), y ∈ f x :=
  rfl

theorem mem_image {α : Type u_1} {β : Type u_2} (f : α →. β) (y : β) (s : set α) : y ∈ image f s ↔ ∃ (x : α), ∃ (H : x ∈ s), y ∈ f x :=
  iff.rfl

theorem image_mono {α : Type u_1} {β : Type u_2} (f : α →. β) {s : set α} {t : set α} (h : s ⊆ t) : image f s ⊆ image f t :=
  rel.image_mono (graph' f) h

theorem image_inter {α : Type u_1} {β : Type u_2} (f : α →. β) (s : set α) (t : set α) : image f (s ∩ t) ⊆ image f s ∩ image f t :=
  rel.image_inter (graph' f) s t

theorem image_union {α : Type u_1} {β : Type u_2} (f : α →. β) (s : set α) (t : set α) : image f (s ∪ t) = image f s ∪ image f t :=
  rel.image_union (graph' f) s t

def preimage {α : Type u_1} {β : Type u_2} (f : α →. β) (s : set β) : set α :=
  rel.preimage (fun (x : α) (y : β) => y ∈ f x) s

theorem preimage_def {α : Type u_1} {β : Type u_2} (f : α →. β) (s : set β) : preimage f s = set_of fun (x : α) => ∃ (y : β), ∃ (H : y ∈ s), y ∈ f x :=
  rfl

theorem mem_preimage {α : Type u_1} {β : Type u_2} (f : α →. β) (s : set β) (x : α) : x ∈ preimage f s ↔ ∃ (y : β), ∃ (H : y ∈ s), y ∈ f x :=
  iff.rfl

theorem preimage_subset_dom {α : Type u_1} {β : Type u_2} (f : α →. β) (s : set β) : preimage f s ⊆ dom f := sorry

theorem preimage_mono {α : Type u_1} {β : Type u_2} (f : α →. β) {s : set β} {t : set β} (h : s ⊆ t) : preimage f s ⊆ preimage f t :=
  rel.preimage_mono (fun (x : α) (y : β) => y ∈ f x) h

theorem preimage_inter {α : Type u_1} {β : Type u_2} (f : α →. β) (s : set β) (t : set β) : preimage f (s ∩ t) ⊆ preimage f s ∩ preimage f t :=
  rel.preimage_inter (fun (x : α) (y : β) => y ∈ f x) s t

theorem preimage_union {α : Type u_1} {β : Type u_2} (f : α →. β) (s : set β) (t : set β) : preimage f (s ∪ t) = preimage f s ∪ preimage f t :=
  rel.preimage_union (fun (x : α) (y : β) => y ∈ f x) s t

theorem preimage_univ {α : Type u_1} {β : Type u_2} (f : α →. β) : preimage f set.univ = dom f := sorry

def core {α : Type u_1} {β : Type u_2} (f : α →. β) (s : set β) : set α :=
  rel.core (graph' f) s

theorem core_def {α : Type u_1} {β : Type u_2} (f : α →. β) (s : set β) : core f s = set_of fun (x : α) => ∀ (y : β), y ∈ f x → y ∈ s :=
  rfl

theorem mem_core {α : Type u_1} {β : Type u_2} (f : α →. β) (x : α) (s : set β) : x ∈ core f s ↔ ∀ (y : β), y ∈ f x → y ∈ s :=
  iff.rfl

theorem compl_dom_subset_core {α : Type u_1} {β : Type u_2} (f : α →. β) (s : set β) : dom fᶜ ⊆ core f s :=
  fun (x : α) (hx : x ∈ (dom fᶜ)) (y : β) (fxy : graph' f x y) => absurd (iff.mpr (mem_dom f x) (Exists.intro y fxy)) hx

theorem core_mono {α : Type u_1} {β : Type u_2} (f : α →. β) {s : set β} {t : set β} (h : s ⊆ t) : core f s ⊆ core f t :=
  rel.core_mono (graph' f) h

theorem core_inter {α : Type u_1} {β : Type u_2} (f : α →. β) (s : set β) (t : set β) : core f (s ∩ t) = core f s ∩ core f t :=
  rel.core_inter (graph' f) s t

theorem mem_core_res {α : Type u_1} {β : Type u_2} (f : α → β) (s : set α) (t : set β) (x : α) : x ∈ core (res f s) t ↔ x ∈ s → f x ∈ t := sorry

theorem core_res {α : Type u_1} {β : Type u_2} (f : α → β) (s : set α) (t : set β) : core (res f s) t = sᶜ ∪ f ⁻¹' t := sorry

theorem core_restrict {α : Type u_1} {β : Type u_2} (f : α → β) (s : set β) : core (↑f) s = f ⁻¹' s := sorry

theorem preimage_subset_core {α : Type u_1} {β : Type u_2} (f : α →. β) (s : set β) : preimage f s ⊆ core f s := sorry

theorem preimage_eq {α : Type u_1} {β : Type u_2} (f : α →. β) (s : set β) : preimage f s = core f s ∩ dom f := sorry

theorem core_eq {α : Type u_1} {β : Type u_2} (f : α →. β) (s : set β) : core f s = preimage f s ∪ (dom fᶜ) := sorry

theorem preimage_as_subtype {α : Type u_1} {β : Type u_2} (f : α →. β) (s : set β) : as_subtype f ⁻¹' s = subtype.val ⁻¹' preimage f s := sorry

