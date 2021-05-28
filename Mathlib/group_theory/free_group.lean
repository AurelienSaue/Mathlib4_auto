/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Free groups as a quotient over the reduction relation `a * x * x⁻¹ * b = a * b`.

First we introduce the one step reduction relation
  `free_group.red.step`:  w * x * x⁻¹ * v   ~>   w * v
its reflexive transitive closure:
  `free_group.red.trans`
and proof that its join is an equivalence relation.

Then we introduce `free_group α` as a quotient over `free_group.red.step`.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.fintype.basic
import Mathlib.group_theory.subgroup
import Mathlib.PostPort

universes u v u_1 w u_2 

namespace Mathlib

namespace free_group


/-- Reduction step: `w * x * x⁻¹ * v ~> w * v` -/
inductive red.step {α : Type u} : List (α × Bool) → List (α × Bool) → Prop
where
| bnot : ∀ {L₁ L₂ : List (α × Bool)} {x : α} {b : Bool}, red.step (L₁ ++ (x, b) :: (x, !b) :: L₂) (L₁ ++ L₂)

/-- Reflexive-transitive closure of red.step -/
def red {α : Type u} : List (α × Bool) → List (α × Bool) → Prop :=
  relation.refl_trans_gen sorry

theorem red.refl {α : Type u} {L : List (α × Bool)} : red L L :=
  relation.refl_trans_gen.refl

theorem red.trans {α : Type u} {L₁ : List (α × Bool)} {L₂ : List (α × Bool)} {L₃ : List (α × Bool)} : red L₁ L₂ → red L₂ L₃ → red L₁ L₃ :=
  relation.refl_trans_gen.trans

namespace red


/-- Predicate asserting that word `w₁` can be reduced to `w₂` in one step, i.e. there are words
`w₃ w₄` and letter `x` such that `w₁ = w₃xx⁻¹w₄` and `w₂ = w₃w₄`  -/
theorem step.length {α : Type u} {L₁ : List (α × Bool)} {L₂ : List (α × Bool)} : step L₁ L₂ → list.length L₂ + bit0 1 = list.length L₁ := sorry

@[simp] theorem step.bnot_rev {α : Type u} {L₁ : List (α × Bool)} {L₂ : List (α × Bool)} {x : α} {b : Bool} : step (L₁ ++ (x, !b) :: (x, b) :: L₂) (L₁ ++ L₂) :=
  bool.cases_on b step.bnot step.bnot

@[simp] theorem step.cons_bnot {α : Type u} {L : List (α × Bool)} {x : α} {b : Bool} : step ((x, b) :: (x, !b) :: L) L :=
  step.bnot

@[simp] theorem step.cons_bnot_rev {α : Type u} {L : List (α × Bool)} {x : α} {b : Bool} : step ((x, !b) :: (x, b) :: L) L :=
  step.bnot_rev

theorem step.append_left {α : Type u} {L₁ : List (α × Bool)} {L₂ : List (α × Bool)} {L₃ : List (α × Bool)} : step L₂ L₃ → step (L₁ ++ L₂) (L₁ ++ L₃) := sorry

theorem step.cons {α : Type u} {L₁ : List (α × Bool)} {L₂ : List (α × Bool)} {x : α × Bool} (H : step L₁ L₂) : step (x :: L₁) (x :: L₂) :=
  step.append_left H

theorem step.append_right {α : Type u} {L₁ : List (α × Bool)} {L₂ : List (α × Bool)} {L₃ : List (α × Bool)} : step L₁ L₂ → step (L₁ ++ L₃) (L₂ ++ L₃) := sorry

theorem not_step_nil {α : Type u} {L : List (α × Bool)} : ¬step [] L := sorry

theorem step.cons_left_iff {α : Type u} {L₁ : List (α × Bool)} {L₂ : List (α × Bool)} {a : α} {b : Bool} : step ((a, b) :: L₁) L₂ ↔ (∃ (L : List (α × Bool)), step L₁ L ∧ L₂ = (a, b) :: L) ∨ L₁ = (a, !b) :: L₂ := sorry

theorem not_step_singleton {α : Type u} {L : List (α × Bool)} {p : α × Bool} : ¬step [p] L := sorry

theorem step.cons_cons_iff {α : Type u} {L₁ : List (α × Bool)} {L₂ : List (α × Bool)} {p : α × Bool} : step (p :: L₁) (p :: L₂) ↔ step L₁ L₂ := sorry

theorem step.append_left_iff {α : Type u} {L₁ : List (α × Bool)} {L₂ : List (α × Bool)} (L : List (α × Bool)) : step (L ++ L₁) (L ++ L₂) ↔ step L₁ L₂ := sorry

theorem step.diamond {α : Type u} {L₁ : List (α × Bool)} {L₂ : List (α × Bool)} {L₃ : List (α × Bool)} {L₄ : List (α × Bool)} : step L₁ L₃ → step L₂ L₄ → L₁ = L₂ → L₃ = L₄ ∨ ∃ (L₅ : List (α × Bool)), step L₃ L₅ ∧ step L₄ L₅ := sorry

theorem step.to_red {α : Type u} {L₁ : List (α × Bool)} {L₂ : List (α × Bool)} : step L₁ L₂ → red L₁ L₂ :=
  relation.refl_trans_gen.single

/-- Church-Rosser theorem for word reduction: If `w1 w2 w3` are words such that `w1` reduces to `w2`
and `w3` respectively, then there is a word `w4` such that `w2` and `w3` reduce to `w4` respectively. -/
theorem church_rosser {α : Type u} {L₁ : List (α × Bool)} {L₂ : List (α × Bool)} {L₃ : List (α × Bool)} : red L₁ L₂ → red L₁ L₃ → relation.join red L₂ L₃ := sorry

theorem cons_cons {α : Type u} {L₁ : List (α × Bool)} {L₂ : List (α × Bool)} {p : α × Bool} : red L₁ L₂ → red (p :: L₁) (p :: L₂) :=
  relation.refl_trans_gen_lift (List.cons p) fun (a b : List (α × Bool)) => step.cons

theorem cons_cons_iff {α : Type u} {L₁ : List (α × Bool)} {L₂ : List (α × Bool)} (p : α × Bool) : red (p :: L₁) (p :: L₂) ↔ red L₁ L₂ := sorry

theorem append_append_left_iff {α : Type u} {L₁ : List (α × Bool)} {L₂ : List (α × Bool)} (L : List (α × Bool)) : red (L ++ L₁) (L ++ L₂) ↔ red L₁ L₂ := sorry

theorem append_append {α : Type u} {L₁ : List (α × Bool)} {L₂ : List (α × Bool)} {L₃ : List (α × Bool)} {L₄ : List (α × Bool)} (h₁ : red L₁ L₃) (h₂ : red L₂ L₄) : red (L₁ ++ L₂) (L₃ ++ L₄) := sorry

theorem to_append_iff {α : Type u} {L : List (α × Bool)} {L₁ : List (α × Bool)} {L₂ : List (α × Bool)} : red L (L₁ ++ L₂) ↔ ∃ (L₃ : List (α × Bool)), ∃ (L₄ : List (α × Bool)), L = L₃ ++ L₄ ∧ red L₃ L₁ ∧ red L₄ L₂ := sorry

/-- The empty word `[]` only reduces to itself. -/
theorem nil_iff {α : Type u} {L : List (α × Bool)} : red [] L ↔ L = [] :=
  relation.refl_trans_gen_iff_eq fun (l : List (α × Bool)) => not_step_nil

/-- A letter only reduces to itself. -/
theorem singleton_iff {α : Type u} {L₁ : List (α × Bool)} {x : α × Bool} : red [x] L₁ ↔ L₁ = [x] :=
  relation.refl_trans_gen_iff_eq fun (l : List (α × Bool)) => not_step_singleton

/-- If `x` is a letter and `w` is a word such that `xw` reduces to the empty word, then `w` reduces
to `x⁻¹` -/
theorem cons_nil_iff_singleton {α : Type u} {L : List (α × Bool)} {x : α} {b : Bool} : red ((x, b) :: L) [] ↔ red L [(x, !b)] := sorry

theorem red_iff_irreducible {α : Type u} {L : List (α × Bool)} {x1 : α} {b1 : Bool} {x2 : α} {b2 : Bool} (h : (x1, b1) ≠ (x2, b2)) : red [(x1, !b1), (x2, b2)] L ↔ L = [(x1, !b1), (x2, b2)] := sorry

/-- If `x` and `y` are distinct letters and `w₁ w₂` are words such that `xw₁` reduces to `yw₂`, then
`w₁` reduces to `x⁻¹yw₂`. -/
theorem inv_of_red_of_ne {α : Type u} {L₁ : List (α × Bool)} {L₂ : List (α × Bool)} {x1 : α} {b1 : Bool} {x2 : α} {b2 : Bool} (H1 : (x1, b1) ≠ (x2, b2)) (H2 : red ((x1, b1) :: L₁) ((x2, b2) :: L₂)) : red L₁ ((x1, !b1) :: (x2, b2) :: L₂) := sorry

theorem step.sublist {α : Type u} {L₁ : List (α × Bool)} {L₂ : List (α × Bool)} (H : step L₁ L₂) : L₂ <+ L₁ := sorry

/-- If `w₁ w₂` are words such that `w₁` reduces to `w₂`, then `w₂` is a sublist of `w₁`. -/
theorem sublist {α : Type u} {L₁ : List (α × Bool)} {L₂ : List (α × Bool)} : red L₁ L₂ → L₂ <+ L₁ :=
  relation.refl_trans_gen_of_transitive_reflexive (fun (l : List (α × Bool)) => list.sublist.refl l)
    (fun (a b c : List (α × Bool)) (hab : b <+ a) (hbc : c <+ b) => list.sublist.trans hbc hab)
    fun (a b : List (α × Bool)) => step.sublist

theorem sizeof_of_step {α : Type u} {L₁ : List (α × Bool)} {L₂ : List (α × Bool)} : step L₁ L₂ → list.sizeof L₂ < list.sizeof L₁ := sorry

theorem length {α : Type u} {L₁ : List (α × Bool)} {L₂ : List (α × Bool)} (h : red L₁ L₂) : ∃ (n : ℕ), list.length L₁ = list.length L₂ + bit0 1 * n := sorry

theorem antisymm {α : Type u} {L₁ : List (α × Bool)} {L₂ : List (α × Bool)} (h₁₂ : red L₁ L₂) : red L₂ L₁ → L₁ = L₂ := sorry

end red


theorem equivalence_join_red {α : Type u} : equivalence (relation.join red) := sorry

theorem join_red_of_step {α : Type u} {L₁ : List (α × Bool)} {L₂ : List (α × Bool)} (h : red.step L₁ L₂) : relation.join red L₁ L₂ :=
  relation.join_of_single relation.reflexive_refl_trans_gen (red.step.to_red h)

theorem eqv_gen_step_iff_join_red {α : Type u} {L₁ : List (α × Bool)} {L₂ : List (α × Bool)} : eqv_gen red.step L₁ L₂ ↔ relation.join red L₁ L₂ := sorry

end free_group


/-- The free group over a type, i.e. the words formed by the elements of the type and their formal
inverses, quotient by one step reduction. -/
def free_group (α : Type u)  :=
  Quot sorry

namespace free_group


/-- The canonical map from `list (α × bool)` to the free group on `α`. -/
def mk {α : Type u} (L : List (α × Bool)) : free_group α :=
  Quot.mk red.step L

@[simp] theorem quot_mk_eq_mk {α : Type u} {L : List (α × Bool)} : Quot.mk red.step L = mk L :=
  rfl

@[simp] theorem quot_lift_mk {α : Type u} {L : List (α × Bool)} (β : Type v) (f : List (α × Bool) → β) (H : ∀ (L₁ L₂ : List (α × Bool)), red.step L₁ L₂ → f L₁ = f L₂) : Quot.lift f H (mk L) = f L :=
  rfl

@[simp] theorem quot_lift_on_mk {α : Type u} {L : List (α × Bool)} (β : Type v) (f : List (α × Bool) → β) (H : ∀ (L₁ L₂ : List (α × Bool)), red.step L₁ L₂ → f L₁ = f L₂) : quot.lift_on (mk L) f H = f L :=
  rfl

protected instance has_one {α : Type u} : HasOne (free_group α) :=
  { one := mk [] }

theorem one_eq_mk {α : Type u} : 1 = mk [] :=
  rfl

protected instance inhabited {α : Type u} : Inhabited (free_group α) :=
  { default := 1 }

protected instance has_mul {α : Type u} : Mul (free_group α) :=
  { mul :=
      fun (x y : free_group α) =>
        quot.lift_on x (fun (L₁ : List (α × Bool)) => quot.lift_on y (fun (L₂ : List (α × Bool)) => mk (L₁ ++ L₂)) sorry)
          sorry }

@[simp] theorem mul_mk {α : Type u} {L₁ : List (α × Bool)} {L₂ : List (α × Bool)} : mk L₁ * mk L₂ = mk (L₁ ++ L₂) :=
  rfl

protected instance has_inv {α : Type u} : has_inv (free_group α) :=
  has_inv.mk
    fun (x : free_group α) =>
      quot.lift_on x
        (fun (L : List (α × Bool)) => mk (list.reverse (list.map (fun (x : α × Bool) => (prod.fst x, !prod.snd x)) L)))
        sorry

@[simp] theorem inv_mk {α : Type u} {L : List (α × Bool)} : mk L⁻¹ = mk (list.reverse (list.map (fun (x : α × Bool) => (prod.fst x, !prod.snd x)) L)) :=
  rfl

protected instance group {α : Type u} : group (free_group α) :=
  group.mk Mul.mul sorry 1 sorry sorry has_inv.inv (div_inv_monoid.div._default Mul.mul sorry 1 sorry sorry has_inv.inv)
    sorry

/-- `of x` is the canonical injection from the type to the free group over that type by sending each
element to the equivalence class of the letter that is the element. -/
def of {α : Type u} (x : α) : free_group α :=
  mk [(x, tt)]

theorem red.exact {α : Type u} {L₁ : List (α × Bool)} {L₂ : List (α × Bool)} : mk L₁ = mk L₂ ↔ relation.join red L₁ L₂ :=
  iff.trans { mp := quot.exact red.step, mpr := quot.eqv_gen_sound } eqv_gen_step_iff_join_red

/-- The canonical injection from the type to the free group is an injection. -/
theorem of_injective {α : Type u} : function.injective of := sorry

/-- Given `f : α → β` with `β` a group, the canonical map `list (α × bool) → β` -/
def to_group.aux {α : Type u} {β : Type v} [group β] (f : α → β) : List (α × Bool) → β :=
  fun (L : List (α × Bool)) =>
    list.prod (list.map (fun (x : α × Bool) => cond (prod.snd x) (f (prod.fst x)) (f (prod.fst x)⁻¹)) L)

theorem red.step.to_group {α : Type u} {L₁ : List (α × Bool)} {L₂ : List (α × Bool)} {β : Type v} [group β] {f : α → β} (H : red.step L₁ L₂) : to_group.aux f L₁ = to_group.aux f L₂ := sorry

/-- If `β` is a group, then any function from `α` to `β`
extends uniquely to a group homomorphism from
the free group over `α` to `β`. Note that this is the bare function; the
group homomorphism is `to_group`. -/
def to_group.to_fun {α : Type u} {β : Type v} [group β] (f : α → β) : free_group α → β :=
  Quot.lift (to_group.aux f) sorry

/-- If `β` is a group, then any function from `α` to `β`
extends uniquely to a group homomorphism from
the free group over `α` to `β` -/
def to_group {α : Type u} {β : Type v} [group β] (f : α → β) : free_group α →* β :=
  monoid_hom.mk' sorry sorry

@[simp] theorem to_group.mk {α : Type u} {L : List (α × Bool)} {β : Type v} [group β] {f : α → β} : coe_fn (to_group f) (mk L) =
  list.prod (list.map (fun (x : α × Bool) => cond (prod.snd x) (f (prod.fst x)) (f (prod.fst x)⁻¹)) L) :=
  rfl

@[simp] theorem to_group.of {α : Type u} {β : Type v} [group β] {f : α → β} {x : α} : coe_fn (to_group f) (of x) = f x :=
  one_mul ((fun (x : α × Bool) => cond (prod.snd x) (f (prod.fst x)) (f (prod.fst x)⁻¹)) (x, tt))

protected instance to_group.is_group_hom {α : Type u} {β : Type v} [group β] {f : α → β} : is_group_hom ⇑(to_group f) :=
  is_group_hom.mk

@[simp] theorem to_group.mul {α : Type u} {β : Type v} [group β] {f : α → β} {x : free_group α} {y : free_group α} : coe_fn (to_group f) (x * y) = coe_fn (to_group f) x * coe_fn (to_group f) y :=
  is_mul_hom.map_mul (⇑(to_group f)) x y

@[simp] theorem to_group.one {α : Type u} {β : Type v} [group β] {f : α → β} : coe_fn (to_group f) 1 = 1 :=
  is_group_hom.map_one ⇑(to_group f)

@[simp] theorem to_group.inv {α : Type u} {β : Type v} [group β] {f : α → β} {x : free_group α} : coe_fn (to_group f) (x⁻¹) = (coe_fn (to_group f) x⁻¹) :=
  is_group_hom.map_inv (⇑(to_group f)) x

theorem to_group.unique {α : Type u} {β : Type v} [group β] {f : α → β} (g : free_group α →* β) (hg : ∀ (x : α), coe_fn g (of x) = f x) {x : free_group α} : coe_fn g x = coe_fn (to_group f) x := sorry

/-- Two homomorphisms out of a free group are equal if they are equal on generators.

See note [partially-applied ext lemmas]. -/
theorem ext_hom {α : Type u} {G : Type u_1} [group G] (f : free_group α →* G) (g : free_group α →* G) (h : ∀ (a : α), coe_fn f (of a) = coe_fn g (of a)) : f = g := sorry

theorem to_group.of_eq {α : Type u} (x : free_group α) : coe_fn (to_group of) x = x :=
  Eq.symm (to_group.unique (monoid_hom.id (free_group α)) fun (x : α) => rfl)

theorem to_group.range_subset {α : Type u} {β : Type v} [group β] {f : α → β} {s : subgroup β} (H : set.range f ⊆ ↑s) : set.range ⇑(to_group f) ⊆ ↑s := sorry

theorem closure_subset {G : Type u_1} [group G] {s : set G} {t : subgroup G} (h : s ⊆ ↑t) : subgroup.closure s ≤ t :=
  eq.mpr (id (Eq.trans (propext (subgroup.closure_le t)) (propext (iff_true_intro h)))) trivial

theorem to_group.range_eq_closure {α : Type u} {β : Type v} [group β] {f : α → β} : set.range ⇑(to_group f) = ↑(subgroup.closure (set.range f)) := sorry

/-- Given `f : α → β`, the canonical map `list (α × bool) → list (β × bool)`. -/
def map.aux {α : Type u} {β : Type v} (f : α → β) (L : List (α × Bool)) : List (β × Bool) :=
  list.map (fun (x : α × Bool) => (f (prod.fst x), prod.snd x)) L

/-- Any function from `α` to `β` extends uniquely
to a group homomorphism from the free group
over `α` to the free group over `β`. Note that this is the bare function;
for the group homomorphism use `map`. -/
def map.to_fun {α : Type u} {β : Type v} (f : α → β) (x : free_group α) : free_group β :=
  quot.lift_on x (fun (L : List (α × Bool)) => mk (map.aux f L)) sorry

/-- Any function from `α` to `β` extends uniquely
to a group homomorphism from the free group
ver `α` to the free group over `β`. -/
def map {α : Type u} {β : Type v} (f : α → β) : free_group α →* free_group β :=
  monoid_hom.mk' sorry sorry

--by rintros ⟨L₁⟩ ⟨L₂⟩; simp [map, map.aux]

@[simp] theorem map.mk {α : Type u} {L : List (α × Bool)} {β : Type v} {f : α → β} : coe_fn (map f) (mk L) = mk (list.map (fun (x : α × Bool) => (f (prod.fst x), prod.snd x)) L) :=
  rfl

@[simp] theorem map.id {α : Type u} {x : free_group α} : coe_fn (map id) x = x := sorry

@[simp] theorem map.id' {α : Type u} {x : free_group α} : coe_fn (map fun (z : α) => z) x = x :=
  map.id

theorem map.comp {α : Type u} {β : Type v} {γ : Type w} {f : α → β} {g : β → γ} {x : free_group α} : coe_fn (map g) (coe_fn (map f) x) = coe_fn (map (g ∘ f)) x := sorry

@[simp] theorem map.of {α : Type u} {β : Type v} {f : α → β} {x : α} : coe_fn (map f) (of x) = of (f x) :=
  rfl

@[simp] theorem map.mul {α : Type u} {β : Type v} {f : α → β} {x : free_group α} {y : free_group α} : coe_fn (map f) (x * y) = coe_fn (map f) x * coe_fn (map f) y :=
  is_mul_hom.map_mul (⇑(map f)) x y

@[simp] theorem map.one {α : Type u} {β : Type v} {f : α → β} : coe_fn (map f) 1 = 1 :=
  is_group_hom.map_one ⇑(map f)

@[simp] theorem map.inv {α : Type u} {β : Type v} {f : α → β} {x : free_group α} : coe_fn (map f) (x⁻¹) = (coe_fn (map f) x⁻¹) :=
  is_group_hom.map_inv (⇑(map f)) x

theorem map.unique {α : Type u} {β : Type v} {f : α → β} (g : free_group α → free_group β) [is_group_hom g] (hg : ∀ (x : α), g (of x) = of (f x)) {x : free_group α} : g x = coe_fn (map f) x := sorry

/-- Equivalent types give rise to equivalent free groups. -/
def free_group_congr {α : Type u_1} {β : Type u_2} (e : α ≃ β) : free_group α ≃ free_group β :=
  equiv.mk ⇑(map ⇑e) ⇑(map ⇑(equiv.symm e)) sorry sorry

theorem map_eq_to_group {α : Type u} {β : Type v} {f : α → β} {x : free_group α} : coe_fn (map f) x = coe_fn (to_group (of ∘ f)) x := sorry

/-- If `α` is a group, then any function from `α` to `α`
extends uniquely to a homomorphism from the
free group over `α` to `α`. This is the multiplicative
version of `sum`. -/
def prod {α : Type u} [group α] : free_group α →* α :=
  to_group id

@[simp] theorem prod_mk {α : Type u} {L : List (α × Bool)} [group α] : coe_fn prod (mk L) = list.prod (list.map (fun (x : α × Bool) => cond (prod.snd x) (prod.fst x) (prod.fst x⁻¹)) L) :=
  rfl

@[simp] theorem prod.of {α : Type u} [group α] {x : α} : coe_fn prod (of x) = x :=
  to_group.of

@[simp] theorem prod.mul {α : Type u} [group α] {x : free_group α} {y : free_group α} : coe_fn prod (x * y) = coe_fn prod x * coe_fn prod y :=
  to_group.mul

@[simp] theorem prod.one {α : Type u} [group α] : coe_fn prod 1 = 1 :=
  to_group.one

@[simp] theorem prod.inv {α : Type u} [group α] {x : free_group α} : coe_fn prod (x⁻¹) = (coe_fn prod x⁻¹) :=
  to_group.inv

theorem prod.unique {α : Type u} [group α] (g : free_group α →* α) (hg : ∀ (x : α), coe_fn g (of x) = x) {x : free_group α} : coe_fn g x = coe_fn prod x :=
  to_group.unique g hg

theorem to_group_eq_prod_map {α : Type u} {β : Type v} [group β] {f : α → β} {x : free_group α} : coe_fn (to_group f) x = coe_fn prod (coe_fn (map f) x) := sorry

/-- If `α` is a group, then any function from `α` to `α`
extends uniquely to a homomorphism from the
free group over `α` to `α`. This is the additive
version of `prod`. -/
def sum {α : Type u} [add_group α] (x : free_group α) : α :=
  coe_fn prod x

@[simp] theorem sum_mk {α : Type u} {L : List (α × Bool)} [add_group α] : sum (mk L) = list.sum (list.map (fun (x : α × Bool) => cond (prod.snd x) (prod.fst x) (-prod.fst x)) L) :=
  rfl

@[simp] theorem sum.of {α : Type u} [add_group α] {x : α} : sum (of x) = x :=
  prod.of

protected instance sum.is_group_hom {α : Type u} [add_group α] : is_group_hom sum :=
  monoid_hom.is_group_hom prod

@[simp] theorem sum.mul {α : Type u} [add_group α] {x : free_group α} {y : free_group α} : sum (x * y) = sum x + sum y :=
  prod.mul

@[simp] theorem sum.one {α : Type u} [add_group α] : sum 1 = 0 :=
  prod.one

@[simp] theorem sum.inv {α : Type u} [add_group α] {x : free_group α} : sum (x⁻¹) = -sum x :=
  prod.inv

/-- The bijection between the free group on the empty type, and a type with one element. -/
def free_group_empty_equiv_unit : free_group empty ≃ Unit :=
  equiv.mk (fun (_x : free_group empty) => Unit.unit) (fun (_x : Unit) => 1) sorry sorry

/-- The bijection between the free group on a singleton, and the integers. -/
def free_group_unit_equiv_int : free_group Unit ≃ ℤ :=
  equiv.mk (fun (x : free_group Unit) => sum (monoid_hom.to_fun (map fun (_x : Unit) => 1) x))
    (fun (x : ℤ) => of Unit.unit ^ x) sorry sorry

protected instance monad : Monad free_group := sorry

protected theorem induction_on {α : Type u} {C : free_group α → Prop} (z : free_group α) (C1 : C 1) (Cp : ∀ (x : α), C (pure x)) (Ci : ∀ (x : α), C (pure x) → C (pure x⁻¹)) (Cm : ∀ (x y : free_group α), C x → C y → C (x * y)) : C z := sorry

@[simp] theorem map_pure {α : Type u} {β : Type u} (f : α → β) (x : α) : f <$> pure x = pure (f x) :=
  map.of

@[simp] theorem map_one {α : Type u} {β : Type u} (f : α → β) : f <$> 1 = 1 :=
  map.one

@[simp] theorem map_mul {α : Type u} {β : Type u} (f : α → β) (x : free_group α) (y : free_group α) : f <$> (x * y) = f <$> x * f <$> y :=
  map.mul

@[simp] theorem map_inv {α : Type u} {β : Type u} (f : α → β) (x : free_group α) : f <$> (x⁻¹) = (f <$> x⁻¹) :=
  map.inv

@[simp] theorem pure_bind {α : Type u} {β : Type u} (f : α → free_group β) (x : α) : pure x >>= f = f x :=
  to_group.of

@[simp] theorem one_bind {α : Type u} {β : Type u} (f : α → free_group β) : 1 >>= f = 1 :=
  to_group.one

@[simp] theorem mul_bind {α : Type u} {β : Type u} (f : α → free_group β) (x : free_group α) (y : free_group α) : x * y >>= f = (x >>= f) * (y >>= f) :=
  to_group.mul

@[simp] theorem inv_bind {α : Type u} {β : Type u} (f : α → free_group β) (x : free_group α) : x⁻¹ >>= f = (x >>= f⁻¹) :=
  to_group.inv

protected instance is_lawful_monad : is_lawful_monad free_group := sorry

/-- The maximal reduction of a word. It is computable
iff `α` has decidable equality. -/
def reduce {α : Type u} [DecidableEq α] (L : List (α × Bool)) : List (α × Bool) :=
  list.rec_on L []
    fun (hd1 : α × Bool) (tl1 ih : List (α × Bool)) =>
      list.cases_on ih [hd1]
        fun (hd2 : α × Bool) (tl2 : List (α × Bool)) =>
          ite (prod.fst hd1 = prod.fst hd2 ∧ prod.snd hd1 = !prod.snd hd2) tl2 (hd1 :: hd2 :: tl2)

@[simp] theorem reduce.cons {α : Type u} {L : List (α × Bool)} [DecidableEq α] (x : α × Bool) : reduce (x :: L) =
  list.cases_on (reduce L) [x]
    fun (hd : α × Bool) (tl : List (α × Bool)) =>
      ite (prod.fst x = prod.fst hd ∧ prod.snd x = !prod.snd hd) tl (x :: hd :: tl) :=
  rfl

/-- The first theorem that characterises the function
`reduce`: a word reduces to its maximal reduction. -/
theorem reduce.red {α : Type u} {L : List (α × Bool)} [DecidableEq α] : red L (reduce L) := sorry

theorem reduce.not {α : Type u} [DecidableEq α] {p : Prop} {L₁ : List (α × Bool)} {L₂ : List (α × Bool)} {L₃ : List (α × Bool)} {x : α} {b : Bool} : reduce L₁ = L₂ ++ (x, b) :: (x, !b) :: L₃ → p := sorry

/-- The second theorem that characterises the
function `reduce`: the maximal reduction of a word
only reduces to itself. -/
theorem reduce.min {α : Type u} {L₁ : List (α × Bool)} {L₂ : List (α × Bool)} [DecidableEq α] (H : red (reduce L₁) L₂) : reduce L₁ = L₂ := sorry

/-- `reduce` is idempotent, i.e. the maximal reduction
of the maximal reduction of a word is the maximal
reduction of the word. -/
theorem reduce.idem {α : Type u} {L : List (α × Bool)} [DecidableEq α] : reduce (reduce L) = reduce L :=
  Eq.symm (reduce.min reduce.red)

theorem reduce.step.eq {α : Type u} {L₁ : List (α × Bool)} {L₂ : List (α × Bool)} [DecidableEq α] (H : red.step L₁ L₂) : reduce L₁ = reduce L₂ := sorry

/-- If a word reduces to another word, then they have
a common maximal reduction. -/
theorem reduce.eq_of_red {α : Type u} {L₁ : List (α × Bool)} {L₂ : List (α × Bool)} [DecidableEq α] (H : red L₁ L₂) : reduce L₁ = reduce L₂ := sorry

/-- If two words correspond to the same element in
the free group, then they have a common maximal
reduction. This is the proof that the function that
sends an element of the free group to its maximal
reduction is well-defined. -/
theorem reduce.sound {α : Type u} {L₁ : List (α × Bool)} {L₂ : List (α × Bool)} [DecidableEq α] (H : mk L₁ = mk L₂) : reduce L₁ = reduce L₂ := sorry

/-- If two words have a common maximal reduction,
then they correspond to the same element in the free group. -/
theorem reduce.exact {α : Type u} {L₁ : List (α × Bool)} {L₂ : List (α × Bool)} [DecidableEq α] (H : reduce L₁ = reduce L₂) : mk L₁ = mk L₂ :=
  iff.mpr red.exact (Exists.intro (reduce L₂) { left := H ▸ reduce.red, right := reduce.red })

/-- A word and its maximal reduction correspond to
the same element of the free group. -/
theorem reduce.self {α : Type u} {L : List (α × Bool)} [DecidableEq α] : mk (reduce L) = mk L :=
  reduce.exact reduce.idem

/-- If words `w₁ w₂` are such that `w₁` reduces to `w₂`,
then `w₂` reduces to the maximal reduction of `w₁`. -/
theorem reduce.rev {α : Type u} {L₁ : List (α × Bool)} {L₂ : List (α × Bool)} [DecidableEq α] (H : red L₁ L₂) : red L₂ (reduce L₁) :=
  Eq.symm (reduce.eq_of_red H) ▸ reduce.red

/-- The function that sends an element of the free
group to its maximal reduction. -/
def to_word {α : Type u} [DecidableEq α] : free_group α → List (α × Bool) :=
  Quot.lift reduce sorry

theorem to_word.mk {α : Type u} [DecidableEq α] {x : free_group α} : mk (to_word x) = x :=
  quot.induction_on x fun (L : List (α × Bool)) => reduce.self

theorem to_word.inj {α : Type u} [DecidableEq α] (x : free_group α) (y : free_group α) : to_word x = to_word y → x = y :=
  quot.induction_on x fun (L₁ : List (α × Bool)) => quot.induction_on y fun (L₂ : List (α × Bool)) => reduce.exact

/-- Constructive Church-Rosser theorem (compare `church_rosser`). -/
def reduce.church_rosser {α : Type u} {L₁ : List (α × Bool)} {L₂ : List (α × Bool)} {L₃ : List (α × Bool)} [DecidableEq α] (H12 : red L₁ L₂) (H13 : red L₁ L₃) : Subtype fun (L₄ : List (α × Bool)) => red L₂ L₄ ∧ red L₃ L₄ :=
  { val := reduce L₁, property := sorry }

protected instance decidable_eq {α : Type u} [DecidableEq α] : DecidableEq (free_group α) :=
  function.injective.decidable_eq sorry

protected instance red.decidable_rel {α : Type u} [DecidableEq α] : DecidableRel red :=
  sorry

/-- A list containing every word that `w₁` reduces to. -/
def red.enum {α : Type u} [DecidableEq α] (L₁ : List (α × Bool)) : List (List (α × Bool)) :=
  list.filter (fun (L₂ : List (α × Bool)) => red L₁ L₂) (list.sublists L₁)

theorem red.enum.sound {α : Type u} {L₁ : List (α × Bool)} {L₂ : List (α × Bool)} [DecidableEq α] (H : L₂ ∈ red.enum L₁) : red L₁ L₂ :=
  list.of_mem_filter H

theorem red.enum.complete {α : Type u} {L₁ : List (α × Bool)} {L₂ : List (α × Bool)} [DecidableEq α] (H : red L₁ L₂) : L₂ ∈ red.enum L₁ :=
  list.mem_filter_of_mem (iff.mpr list.mem_sublists (red.sublist H)) H

protected instance subtype.fintype {α : Type u} {L₁ : List (α × Bool)} [DecidableEq α] : fintype (Subtype fun (L₂ : List (α × Bool)) => red L₁ L₂) :=
  fintype.subtype (list.to_finset (red.enum L₁)) sorry

