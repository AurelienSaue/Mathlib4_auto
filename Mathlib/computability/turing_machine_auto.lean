/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.order
import Mathlib.data.fintype.basic
import Mathlib.data.pfun
import Mathlib.tactic.apply_fun
import Mathlib.logic.function.iterate
import PostPort

universes u_1 u_2 u v l u_3 u_4 

namespace Mathlib

/-!
# Turing machines

This file defines a sequence of simple machine languages, starting with Turing machines and working
up to more complex languages based on Wang B-machines.

## Naming conventions

Each model of computation in this file shares a naming convention for the elements of a model of
computation. These are the parameters for the language:

* `Γ` is the alphabet on the tape.
* `Λ` is the set of labels, or internal machine states.
* `σ` is the type of internal memory, not on the tape. This does not exist in the TM0 model, and
  later models achieve this by mixing it into `Λ`.
* `K` is used in the TM2 model, which has multiple stacks, and denotes the number of such stacks.

All of these variables denote "essentially finite" types, but for technical reasons it is
convenient to allow them to be infinite anyway. When using an infinite type, we will be interested
to prove that only finitely many values of the type are ever interacted with.

Given these parameters, there are a few common structures for the model that arise:

* `stmt` is the set of all actions that can be performed in one step. For the TM0 model this set is
  finite, and for later models it is an infinite inductive type representing "possible program
  texts".
* `cfg` is the set of instantaneous configurations, that is, the state of the machine together with
  its environment.
* `machine` is the set of all machines in the model. Usually this is approximately a function
  `Λ → stmt`, although different models have different ways of halting and other actions.
* `step : cfg → option cfg` is the function that describes how the state evolves over one step.
  If `step c = none`, then `c` is a terminal state, and the result of the computation is read off
  from `c`. Because of the type of `step`, these models are all deterministic by construction.
* `init : input → cfg` sets up the initial state. The type `input` depends on the model;
  in most cases it is `list Γ`.
* `eval : machine → input → roption output`, given a machine `M` and input `i`, starts from
  `init i`, runs `step` until it reaches an output, and then applies a function `cfg → output` to
  the final state to obtain the result. The type `output` depends on the model.
* `supports : machine → finset Λ → Prop` asserts that a machine `M` starts in `S : finset Λ`, and
  can only ever jump to other states inside `S`. This implies that the behavior of `M` on any input
  cannot depend on its values outside `S`. We use this to allow `Λ` to be an infinite set when
  convenient, and prove that only finitely many of these states are actually accessible. This
  formalizes "essentially finite" mentioned above.
-/

namespace turing


/-- The `blank_extends` partial order holds of `l₁` and `l₂` if `l₂` is obtained by adding
blanks (`default Γ`) to the end of `l₁`. -/
def blank_extends {Γ : Type u_1} [Inhabited Γ] (l₁ : List Γ) (l₂ : List Γ)  :=
  ∃ (n : ℕ), l₂ = l₁ ++ list.repeat Inhabited.default n

theorem blank_extends.refl {Γ : Type u_1} [Inhabited Γ] (l : List Γ) : blank_extends l l := sorry

theorem blank_extends.trans {Γ : Type u_1} [Inhabited Γ] {l₁ : List Γ} {l₂ : List Γ} {l₃ : List Γ} : blank_extends l₁ l₂ → blank_extends l₂ l₃ → blank_extends l₁ l₃ := sorry

theorem blank_extends.below_of_le {Γ : Type u_1} [Inhabited Γ] {l : List Γ} {l₁ : List Γ} {l₂ : List Γ} : blank_extends l l₁ → blank_extends l l₂ → list.length l₁ ≤ list.length l₂ → blank_extends l₁ l₂ := sorry

/-- Any two extensions by blank `l₁,l₂` of `l` have a common join (which can be taken to be the
longer of `l₁` and `l₂`). -/
def blank_extends.above {Γ : Type u_1} [Inhabited Γ] {l : List Γ} {l₁ : List Γ} {l₂ : List Γ} (h₁ : blank_extends l l₁) (h₂ : blank_extends l l₂) : Subtype fun (l' : List Γ) => blank_extends l₁ l' ∧ blank_extends l₂ l' :=
  dite (list.length l₁ ≤ list.length l₂) (fun (h : list.length l₁ ≤ list.length l₂) => { val := l₂, property := sorry })
    fun (h : ¬list.length l₁ ≤ list.length l₂) => { val := l₁, property := sorry }

theorem blank_extends.above_of_le {Γ : Type u_1} [Inhabited Γ] {l : List Γ} {l₁ : List Γ} {l₂ : List Γ} : blank_extends l₁ l → blank_extends l₂ l → list.length l₁ ≤ list.length l₂ → blank_extends l₁ l₂ := sorry

/-- `blank_rel` is the symmetric closure of `blank_extends`, turning it into an equivalence
relation. Two lists are related by `blank_rel` if one extends the other by blanks. -/
def blank_rel {Γ : Type u_1} [Inhabited Γ] (l₁ : List Γ) (l₂ : List Γ)  :=
  blank_extends l₁ l₂ ∨ blank_extends l₂ l₁

theorem blank_rel.refl {Γ : Type u_1} [Inhabited Γ] (l : List Γ) : blank_rel l l :=
  Or.inl (blank_extends.refl l)

theorem blank_rel.symm {Γ : Type u_1} [Inhabited Γ] {l₁ : List Γ} {l₂ : List Γ} : blank_rel l₁ l₂ → blank_rel l₂ l₁ :=
  or.symm

theorem blank_rel.trans {Γ : Type u_1} [Inhabited Γ] {l₁ : List Γ} {l₂ : List Γ} {l₃ : List Γ} : blank_rel l₁ l₂ → blank_rel l₂ l₃ → blank_rel l₁ l₃ := sorry

/-- Given two `blank_rel` lists, there exists (constructively) a common join. -/
def blank_rel.above {Γ : Type u_1} [Inhabited Γ] {l₁ : List Γ} {l₂ : List Γ} (h : blank_rel l₁ l₂) : Subtype fun (l : List Γ) => blank_extends l₁ l ∧ blank_extends l₂ l :=
  dite (list.length l₁ ≤ list.length l₂) (fun (hl : list.length l₁ ≤ list.length l₂) => { val := l₂, property := sorry })
    fun (hl : ¬list.length l₁ ≤ list.length l₂) => { val := l₁, property := sorry }

/-- Given two `blank_rel` lists, there exists (constructively) a common meet. -/
def blank_rel.old_below {Γ : Type u_1} [Inhabited Γ] {l₁ : List Γ} {l₂ : List Γ} (h : blank_rel l₁ l₂) : Subtype fun (l : List Γ) => blank_extends l l₁ ∧ blank_extends l l₂ :=
  dite (list.length l₁ ≤ list.length l₂)
    (fun (hl : list.length l₁ ≤ list.length l₂) => { val := l₁, property := blank_rel.below._proof_1 h hl })
    fun (hl : ¬list.length l₁ ≤ list.length l₂) => { val := l₂, property := blank_rel.below._proof_2 h hl }

theorem blank_rel.equivalence (Γ : Type u_1) [Inhabited Γ] : equivalence blank_rel :=
  { left := blank_rel.refl, right := { left := blank_rel.symm, right := blank_rel.trans } }

/-- Construct a setoid instance for `blank_rel`. -/
def blank_rel.setoid (Γ : Type u_1) [Inhabited Γ] : setoid (List Γ) :=
  setoid.mk blank_rel (blank_rel.equivalence Γ)

/-- A `list_blank Γ` is a quotient of `list Γ` by extension by blanks at the end. This is used to
represent half-tapes of a Turing machine, so that we can pretend that the list continues
infinitely with blanks. -/
def list_blank (Γ : Type u_1) [Inhabited Γ]  :=
  quotient (blank_rel.setoid Γ)

protected instance list_blank.inhabited {Γ : Type u_1} [Inhabited Γ] : Inhabited (list_blank Γ) :=
  { default := quotient.mk' [] }

protected instance list_blank.has_emptyc {Γ : Type u_1} [Inhabited Γ] : has_emptyc (list_blank Γ) :=
  has_emptyc.mk (quotient.mk' [])

/-- A modified version of `quotient.lift_on'` specialized for `list_blank`, with the stronger
precondition `blank_extends` instead of `blank_rel`. -/
protected def list_blank.lift_on {Γ : Type u_1} [Inhabited Γ] {α : Sort u_2} (l : list_blank Γ) (f : List Γ → α) (H : ∀ (a b : List Γ), blank_extends a b → f a = f b) : α :=
  quotient.lift_on' l f sorry

/-- The quotient map turning a `list` into a `list_blank`. -/
def list_blank.mk {Γ : Type u_1} [Inhabited Γ] : List Γ → list_blank Γ :=
  quotient.mk'

protected theorem list_blank.induction_on {Γ : Type u_1} [Inhabited Γ] {p : list_blank Γ → Prop} (q : list_blank Γ) (h : ∀ (a : List Γ), p (list_blank.mk a)) : p q :=
  quotient.induction_on' q h

/-- The head of a `list_blank` is well defined. -/
def list_blank.head {Γ : Type u_1} [Inhabited Γ] (l : list_blank Γ) : Γ :=
  list_blank.lift_on l list.head sorry

@[simp] theorem list_blank.head_mk {Γ : Type u_1} [Inhabited Γ] (l : List Γ) : list_blank.head (list_blank.mk l) = list.head l :=
  rfl

/-- The tail of a `list_blank` is well defined (up to the tail of blanks). -/
def list_blank.tail {Γ : Type u_1} [Inhabited Γ] (l : list_blank Γ) : list_blank Γ :=
  list_blank.lift_on l (fun (l : List Γ) => list_blank.mk (list.tail l)) sorry

@[simp] theorem list_blank.tail_mk {Γ : Type u_1} [Inhabited Γ] (l : List Γ) : list_blank.tail (list_blank.mk l) = list_blank.mk (list.tail l) :=
  rfl

/-- We can cons an element onto a `list_blank`. -/
def list_blank.cons {Γ : Type u_1} [Inhabited Γ] (a : Γ) (l : list_blank Γ) : list_blank Γ :=
  list_blank.lift_on l (fun (l : List Γ) => list_blank.mk (a :: l)) sorry

@[simp] theorem list_blank.cons_mk {Γ : Type u_1} [Inhabited Γ] (a : Γ) (l : List Γ) : list_blank.cons a (list_blank.mk l) = list_blank.mk (a :: l) :=
  rfl

@[simp] theorem list_blank.head_cons {Γ : Type u_1} [Inhabited Γ] (a : Γ) (l : list_blank Γ) : list_blank.head (list_blank.cons a l) = a :=
  quotient.ind' fun (l : List Γ) => rfl

@[simp] theorem list_blank.tail_cons {Γ : Type u_1} [Inhabited Γ] (a : Γ) (l : list_blank Γ) : list_blank.tail (list_blank.cons a l) = l :=
  quotient.ind' fun (l : List Γ) => rfl

/-- The `cons` and `head`/`tail` functions are mutually inverse, unlike in the case of `list` where
this only holds for nonempty lists. -/
@[simp] theorem list_blank.cons_head_tail {Γ : Type u_1} [Inhabited Γ] (l : list_blank Γ) : list_blank.cons (list_blank.head l) (list_blank.tail l) = l := sorry

/-- The `cons` and `head`/`tail` functions are mutually inverse, unlike in the case of `list` where
this only holds for nonempty lists. -/
theorem list_blank.exists_cons {Γ : Type u_1} [Inhabited Γ] (l : list_blank Γ) : ∃ (a : Γ), ∃ (l' : list_blank Γ), l = list_blank.cons a l' :=
  Exists.intro (list_blank.head l) (Exists.intro (list_blank.tail l) (Eq.symm (list_blank.cons_head_tail l)))

/-- The n-th element of a `list_blank` is well defined for all `n : ℕ`, unlike in a `list`. -/
def list_blank.nth {Γ : Type u_1} [Inhabited Γ] (l : list_blank Γ) (n : ℕ) : Γ :=
  list_blank.lift_on l (fun (l : List Γ) => list.inth l n) sorry

@[simp] theorem list_blank.nth_mk {Γ : Type u_1} [Inhabited Γ] (l : List Γ) (n : ℕ) : list_blank.nth (list_blank.mk l) n = list.inth l n :=
  rfl

@[simp] theorem list_blank.nth_zero {Γ : Type u_1} [Inhabited Γ] (l : list_blank Γ) : list_blank.nth l 0 = list_blank.head l := sorry

@[simp] theorem list_blank.nth_succ {Γ : Type u_1} [Inhabited Γ] (l : list_blank Γ) (n : ℕ) : list_blank.nth l (n + 1) = list_blank.nth (list_blank.tail l) n := sorry

theorem list_blank.ext {Γ : Type u_1} [Inhabited Γ] {L₁ : list_blank Γ} {L₂ : list_blank Γ} : (∀ (i : ℕ), list_blank.nth L₁ i = list_blank.nth L₂ i) → L₁ = L₂ := sorry

/-- Apply a function to a value stored at the nth position of the list. -/
@[simp] def list_blank.modify_nth {Γ : Type u_1} [Inhabited Γ] (f : Γ → Γ) : ℕ → list_blank Γ → list_blank Γ :=
  sorry

theorem list_blank.nth_modify_nth {Γ : Type u_1} [Inhabited Γ] (f : Γ → Γ) (n : ℕ) (i : ℕ) (L : list_blank Γ) : list_blank.nth (list_blank.modify_nth f n L) i = ite (i = n) (f (list_blank.nth L i)) (list_blank.nth L i) := sorry

/-- A pointed map of `inhabited` types is a map that sends one default value to the other. -/
structure pointed_map (Γ : Type u) (Γ' : Type v) [Inhabited Γ] [Inhabited Γ'] 
where
  f : Γ → Γ'
  map_pt' : f Inhabited.default = Inhabited.default

protected instance pointed_map.inhabited {Γ : Type u_1} {Γ' : Type u_2} [Inhabited Γ] [Inhabited Γ'] : Inhabited (pointed_map Γ Γ') :=
  { default := pointed_map.mk (fun (_x : Γ) => Inhabited.default) sorry }

protected instance pointed_map.has_coe_to_fun {Γ : Type u_1} {Γ' : Type u_2} [Inhabited Γ] [Inhabited Γ'] : has_coe_to_fun (pointed_map Γ Γ') :=
  has_coe_to_fun.mk (fun (x : pointed_map Γ Γ') => Γ → Γ') pointed_map.f

@[simp] theorem pointed_map.mk_val {Γ : Type u_1} {Γ' : Type u_2} [Inhabited Γ] [Inhabited Γ'] (f : Γ → Γ') (pt : f Inhabited.default = Inhabited.default) : ⇑(pointed_map.mk f pt) = f :=
  rfl

@[simp] theorem pointed_map.map_pt {Γ : Type u_1} {Γ' : Type u_2} [Inhabited Γ] [Inhabited Γ'] (f : pointed_map Γ Γ') : coe_fn f Inhabited.default = Inhabited.default :=
  pointed_map.map_pt' f

@[simp] theorem pointed_map.head_map {Γ : Type u_1} {Γ' : Type u_2} [Inhabited Γ] [Inhabited Γ'] (f : pointed_map Γ Γ') (l : List Γ) : list.head (list.map (⇑f) l) = coe_fn f (list.head l) :=
  list.cases_on l (Eq.symm (pointed_map.map_pt f))
    fun (l_hd : Γ) (l_tl : List Γ) => Eq.refl (list.head (list.map (⇑f) (l_hd :: l_tl)))

/-- The `map` function on lists is well defined on `list_blank`s provided that the map is
pointed. -/
def list_blank.map {Γ : Type u_1} {Γ' : Type u_2} [Inhabited Γ] [Inhabited Γ'] (f : pointed_map Γ Γ') (l : list_blank Γ) : list_blank Γ' :=
  list_blank.lift_on l (fun (l : List Γ) => list_blank.mk (list.map (⇑f) l)) sorry

@[simp] theorem list_blank.map_mk {Γ : Type u_1} {Γ' : Type u_2} [Inhabited Γ] [Inhabited Γ'] (f : pointed_map Γ Γ') (l : List Γ) : list_blank.map f (list_blank.mk l) = list_blank.mk (list.map (⇑f) l) :=
  rfl

@[simp] theorem list_blank.head_map {Γ : Type u_1} {Γ' : Type u_2} [Inhabited Γ] [Inhabited Γ'] (f : pointed_map Γ Γ') (l : list_blank Γ) : list_blank.head (list_blank.map f l) = coe_fn f (list_blank.head l) := sorry

@[simp] theorem list_blank.tail_map {Γ : Type u_1} {Γ' : Type u_2} [Inhabited Γ] [Inhabited Γ'] (f : pointed_map Γ Γ') (l : list_blank Γ) : list_blank.tail (list_blank.map f l) = list_blank.map f (list_blank.tail l) := sorry

@[simp] theorem list_blank.map_cons {Γ : Type u_1} {Γ' : Type u_2} [Inhabited Γ] [Inhabited Γ'] (f : pointed_map Γ Γ') (l : list_blank Γ) (a : Γ) : list_blank.map f (list_blank.cons a l) = list_blank.cons (coe_fn f a) (list_blank.map f l) := sorry

@[simp] theorem list_blank.nth_map {Γ : Type u_1} {Γ' : Type u_2} [Inhabited Γ] [Inhabited Γ'] (f : pointed_map Γ Γ') (l : list_blank Γ) (n : ℕ) : list_blank.nth (list_blank.map f l) n = coe_fn f (list_blank.nth l n) := sorry

/-- The `i`-th projection as a pointed map. -/
def proj {ι : Type u_1} {Γ : ι → Type u_2} [(i : ι) → Inhabited (Γ i)] (i : ι) : pointed_map ((i : ι) → Γ i) (Γ i) :=
  pointed_map.mk (fun (a : (i : ι) → Γ i) => a i) sorry

theorem proj_map_nth {ι : Type u_1} {Γ : ι → Type u_2} [(i : ι) → Inhabited (Γ i)] (i : ι) (L : list_blank ((i : ι) → Γ i)) (n : ℕ) : list_blank.nth (list_blank.map (proj i) L) n = list_blank.nth L n i := sorry

theorem list_blank.map_modify_nth {Γ : Type u_1} {Γ' : Type u_2} [Inhabited Γ] [Inhabited Γ'] (F : pointed_map Γ Γ') (f : Γ → Γ) (f' : Γ' → Γ') (H : ∀ (x : Γ), coe_fn F (f x) = f' (coe_fn F x)) (n : ℕ) (L : list_blank Γ) : list_blank.map F (list_blank.modify_nth f n L) = list_blank.modify_nth f' n (list_blank.map F L) := sorry

/-- Append a list on the left side of a list_blank. -/
@[simp] def list_blank.append {Γ : Type u_1} [Inhabited Γ] : List Γ → list_blank Γ → list_blank Γ :=
  sorry

@[simp] theorem list_blank.append_mk {Γ : Type u_1} [Inhabited Γ] (l₁ : List Γ) (l₂ : List Γ) : list_blank.append l₁ (list_blank.mk l₂) = list_blank.mk (l₁ ++ l₂) := sorry

theorem list_blank.append_assoc {Γ : Type u_1} [Inhabited Γ] (l₁ : List Γ) (l₂ : List Γ) (l₃ : list_blank Γ) : list_blank.append (l₁ ++ l₂) l₃ = list_blank.append l₁ (list_blank.append l₂ l₃) := sorry

/-- The `bind` function on lists is well defined on `list_blank`s provided that the default element
is sent to a sequence of default elements. -/
def list_blank.bind {Γ : Type u_1} {Γ' : Type u_2} [Inhabited Γ] [Inhabited Γ'] (l : list_blank Γ) (f : Γ → List Γ') (hf : ∃ (n : ℕ), f Inhabited.default = list.repeat Inhabited.default n) : list_blank Γ' :=
  list_blank.lift_on l (fun (l : List Γ) => list_blank.mk (list.bind l f)) sorry

@[simp] theorem list_blank.bind_mk {Γ : Type u_1} {Γ' : Type u_2} [Inhabited Γ] [Inhabited Γ'] (l : List Γ) (f : Γ → List Γ') (hf : ∃ (n : ℕ), f Inhabited.default = list.repeat Inhabited.default n) : list_blank.bind (list_blank.mk l) f hf = list_blank.mk (list.bind l f) :=
  rfl

@[simp] theorem list_blank.cons_bind {Γ : Type u_1} {Γ' : Type u_2} [Inhabited Γ] [Inhabited Γ'] (a : Γ) (l : list_blank Γ) (f : Γ → List Γ') (hf : ∃ (n : ℕ), f Inhabited.default = list.repeat Inhabited.default n) : list_blank.bind (list_blank.cons a l) f hf = list_blank.append (f a) (list_blank.bind l f hf) := sorry

/-- The tape of a Turing machine is composed of a head element (which we imagine to be the
current position of the head), together with two `list_blank`s denoting the portions of the tape
going off to the left and right. When the Turing machine moves right, an element is pulled from the
right side and becomes the new head, while the head element is consed onto the left side. -/
structure tape (Γ : Type u_1) [Inhabited Γ] 
where
  head : Γ
  left : list_blank Γ
  right : list_blank Γ

protected instance tape.inhabited {Γ : Type u_1} [Inhabited Γ] : Inhabited (tape Γ) :=
  { default := tape.mk Inhabited.default Inhabited.default Inhabited.default }

/-- A direction for the turing machine `move` command, either
  left or right. -/
inductive dir 
where
| left : dir
| right : dir

/-- The "inclusive" left side of the tape, including both `left` and `head`. -/
def tape.left₀ {Γ : Type u_1} [Inhabited Γ] (T : tape Γ) : list_blank Γ :=
  list_blank.cons (tape.head T) (tape.left T)

/-- The "inclusive" right side of the tape, including both `right` and `head`. -/
def tape.right₀ {Γ : Type u_1} [Inhabited Γ] (T : tape Γ) : list_blank Γ :=
  list_blank.cons (tape.head T) (tape.right T)

/-- Move the tape in response to a motion of the Turing machine. Note that `T.move dir.left` makes
`T.left` smaller; the Turing machine is moving left and the tape is moving right. -/
def tape.move {Γ : Type u_1} [Inhabited Γ] : dir → tape Γ → tape Γ :=
  sorry

@[simp] theorem tape.move_left_right {Γ : Type u_1} [Inhabited Γ] (T : tape Γ) : tape.move dir.right (tape.move dir.left T) = T := sorry

@[simp] theorem tape.move_right_left {Γ : Type u_1} [Inhabited Γ] (T : tape Γ) : tape.move dir.left (tape.move dir.right T) = T := sorry

/-- Construct a tape from a left side and an inclusive right side. -/
def tape.mk' {Γ : Type u_1} [Inhabited Γ] (L : list_blank Γ) (R : list_blank Γ) : tape Γ :=
  tape.mk (list_blank.head R) L (list_blank.tail R)

@[simp] theorem tape.mk'_left {Γ : Type u_1} [Inhabited Γ] (L : list_blank Γ) (R : list_blank Γ) : tape.left (tape.mk' L R) = L :=
  rfl

@[simp] theorem tape.mk'_head {Γ : Type u_1} [Inhabited Γ] (L : list_blank Γ) (R : list_blank Γ) : tape.head (tape.mk' L R) = list_blank.head R :=
  rfl

@[simp] theorem tape.mk'_right {Γ : Type u_1} [Inhabited Γ] (L : list_blank Γ) (R : list_blank Γ) : tape.right (tape.mk' L R) = list_blank.tail R :=
  rfl

@[simp] theorem tape.mk'_right₀ {Γ : Type u_1} [Inhabited Γ] (L : list_blank Γ) (R : list_blank Γ) : tape.right₀ (tape.mk' L R) = R :=
  list_blank.cons_head_tail R

@[simp] theorem tape.mk'_left_right₀ {Γ : Type u_1} [Inhabited Γ] (T : tape Γ) : tape.mk' (tape.left T) (tape.right₀ T) = T := sorry

theorem tape.exists_mk' {Γ : Type u_1} [Inhabited Γ] (T : tape Γ) : ∃ (L : list_blank Γ), ∃ (R : list_blank Γ), T = tape.mk' L R :=
  Exists.intro (tape.left T) (Exists.intro (tape.right₀ T) (Eq.symm (tape.mk'_left_right₀ T)))

@[simp] theorem tape.move_left_mk' {Γ : Type u_1} [Inhabited Γ] (L : list_blank Γ) (R : list_blank Γ) : tape.move dir.left (tape.mk' L R) = tape.mk' (list_blank.tail L) (list_blank.cons (list_blank.head L) R) := sorry

@[simp] theorem tape.move_right_mk' {Γ : Type u_1} [Inhabited Γ] (L : list_blank Γ) (R : list_blank Γ) : tape.move dir.right (tape.mk' L R) = tape.mk' (list_blank.cons (list_blank.head R) L) (list_blank.tail R) := sorry

/-- Construct a tape from a left side and an inclusive right side. -/
def tape.mk₂ {Γ : Type u_1} [Inhabited Γ] (L : List Γ) (R : List Γ) : tape Γ :=
  tape.mk' (list_blank.mk L) (list_blank.mk R)

/-- Construct a tape from a list, with the head of the list at the TM head and the rest going
to the right. -/
def tape.mk₁ {Γ : Type u_1} [Inhabited Γ] (l : List Γ) : tape Γ :=
  tape.mk₂ [] l

/-- The `nth` function of a tape is integer-valued, with index `0` being the head, negative indexes
on the left and positive indexes on the right. (Picture a number line.) -/
def tape.nth {Γ : Type u_1} [Inhabited Γ] (T : tape Γ) : ℤ → Γ :=
  sorry

@[simp] theorem tape.nth_zero {Γ : Type u_1} [Inhabited Γ] (T : tape Γ) : tape.nth T 0 = tape.head T :=
  rfl

theorem tape.right₀_nth {Γ : Type u_1} [Inhabited Γ] (T : tape Γ) (n : ℕ) : list_blank.nth (tape.right₀ T) n = tape.nth T ↑n := sorry

@[simp] theorem tape.mk'_nth_nat {Γ : Type u_1} [Inhabited Γ] (L : list_blank Γ) (R : list_blank Γ) (n : ℕ) : tape.nth (tape.mk' L R) ↑n = list_blank.nth R n := sorry

@[simp] theorem tape.move_left_nth {Γ : Type u_1} [Inhabited Γ] (T : tape Γ) (i : ℤ) : tape.nth (tape.move dir.left T) i = tape.nth T (i - 1) := sorry

@[simp] theorem tape.move_right_nth {Γ : Type u_1} [Inhabited Γ] (T : tape Γ) (i : ℤ) : tape.nth (tape.move dir.right T) i = tape.nth T (i + 1) := sorry

@[simp] theorem tape.move_right_n_head {Γ : Type u_1} [Inhabited Γ] (T : tape Γ) (i : ℕ) : tape.head (nat.iterate (tape.move dir.right) i T) = tape.nth T ↑i := sorry

/-- Replace the current value of the head on the tape. -/
def tape.write {Γ : Type u_1} [Inhabited Γ] (b : Γ) (T : tape Γ) : tape Γ :=
  tape.mk b (tape.left T) (tape.right T)

@[simp] theorem tape.write_self {Γ : Type u_1} [Inhabited Γ] (T : tape Γ) : tape.write (tape.head T) T = T :=
  tape.cases_on T
    fun (T_head : Γ) (T_left T_right : list_blank Γ) =>
      Eq.refl (tape.write (tape.head (tape.mk T_head T_left T_right)) (tape.mk T_head T_left T_right))

@[simp] theorem tape.write_nth {Γ : Type u_1} [Inhabited Γ] (b : Γ) (T : tape Γ) {i : ℤ} : tape.nth (tape.write b T) i = ite (i = 0) b (tape.nth T i) := sorry

@[simp] theorem tape.write_mk' {Γ : Type u_1} [Inhabited Γ] (a : Γ) (b : Γ) (L : list_blank Γ) (R : list_blank Γ) : tape.write b (tape.mk' L (list_blank.cons a R)) = tape.mk' L (list_blank.cons b R) := sorry

/-- Apply a pointed map to a tape to change the alphabet. -/
def tape.map {Γ : Type u_1} {Γ' : Type u_2} [Inhabited Γ] [Inhabited Γ'] (f : pointed_map Γ Γ') (T : tape Γ) : tape Γ' :=
  tape.mk (coe_fn f (tape.head T)) (list_blank.map f (tape.left T)) (list_blank.map f (tape.right T))

@[simp] theorem tape.map_fst {Γ : Type u_1} {Γ' : Type u_2} [Inhabited Γ] [Inhabited Γ'] (f : pointed_map Γ Γ') (T : tape Γ) : tape.head (tape.map f T) = coe_fn f (tape.head T) :=
  tape.cases_on T
    fun (T_head : Γ) (T_left T_right : list_blank Γ) => Eq.refl (tape.head (tape.map f (tape.mk T_head T_left T_right)))

@[simp] theorem tape.map_write {Γ : Type u_1} {Γ' : Type u_2} [Inhabited Γ] [Inhabited Γ'] (f : pointed_map Γ Γ') (b : Γ) (T : tape Γ) : tape.map f (tape.write b T) = tape.write (coe_fn f b) (tape.map f T) :=
  tape.cases_on T
    fun (T_head : Γ) (T_left T_right : list_blank Γ) =>
      Eq.refl (tape.map f (tape.write b (tape.mk T_head T_left T_right)))

@[simp] theorem tape.write_move_right_n {Γ : Type u_1} [Inhabited Γ] (f : Γ → Γ) (L : list_blank Γ) (R : list_blank Γ) (n : ℕ) : tape.write (f (list_blank.nth R n)) (nat.iterate (tape.move dir.right) n (tape.mk' L R)) =
  nat.iterate (tape.move dir.right) n (tape.mk' L (list_blank.modify_nth f n R)) := sorry

theorem tape.map_move {Γ : Type u_1} {Γ' : Type u_2} [Inhabited Γ] [Inhabited Γ'] (f : pointed_map Γ Γ') (T : tape Γ) (d : dir) : tape.map f (tape.move d T) = tape.move d (tape.map f T) := sorry

theorem tape.map_mk' {Γ : Type u_1} {Γ' : Type u_2} [Inhabited Γ] [Inhabited Γ'] (f : pointed_map Γ Γ') (L : list_blank Γ) (R : list_blank Γ) : tape.map f (tape.mk' L R) = tape.mk' (list_blank.map f L) (list_blank.map f R) := sorry

theorem tape.map_mk₂ {Γ : Type u_1} {Γ' : Type u_2} [Inhabited Γ] [Inhabited Γ'] (f : pointed_map Γ Γ') (L : List Γ) (R : List Γ) : tape.map f (tape.mk₂ L R) = tape.mk₂ (list.map (⇑f) L) (list.map (⇑f) R) := sorry

theorem tape.map_mk₁ {Γ : Type u_1} {Γ' : Type u_2} [Inhabited Γ] [Inhabited Γ'] (f : pointed_map Γ Γ') (l : List Γ) : tape.map f (tape.mk₁ l) = tape.mk₁ (list.map (⇑f) l) :=
  tape.map_mk₂ f [] l

/-- Run a state transition function `σ → option σ` "to completion". The return value is the last
state returned before a `none` result. If the state transition function always returns `some`,
then the computation diverges, returning `roption.none`. -/
def eval {σ : Type u_1} (f : σ → Option σ) : σ → roption σ :=
  pfun.fix fun (s : σ) => roption.some (option.elim (f s) (sum.inl s) sum.inr)

/-- The reflexive transitive closure of a state transition function. `reaches f a b` means
there is a finite sequence of steps `f a = some a₁`, `f a₁ = some a₂`, ... such that `aₙ = b`.
This relation permits zero steps of the state transition function. -/
def reaches {σ : Type u_1} (f : σ → Option σ) : σ → σ → Prop :=
  relation.refl_trans_gen fun (a b : σ) => b ∈ f a

/-- The transitive closure of a state transition function. `reaches₁ f a b` means there is a
nonempty finite sequence of steps `f a = some a₁`, `f a₁ = some a₂`, ... such that `aₙ = b`.
This relation does not permit zero steps of the state transition function. -/
def reaches₁ {σ : Type u_1} (f : σ → Option σ) : σ → σ → Prop :=
  relation.trans_gen fun (a b : σ) => b ∈ f a

theorem reaches₁_eq {σ : Type u_1} {f : σ → Option σ} {a : σ} {b : σ} {c : σ} (h : f a = f b) : reaches₁ f a c ↔ reaches₁ f b c := sorry

theorem reaches_total {σ : Type u_1} {f : σ → Option σ} {a : σ} {b : σ} {c : σ} : reaches f a b → reaches f a c → reaches f b c ∨ reaches f c b :=
  relation.refl_trans_gen.total_of_right_unique fun (_x _x_1 _x_2 : σ) => option.mem_unique

theorem reaches₁_fwd {σ : Type u_1} {f : σ → Option σ} {a : σ} {b : σ} {c : σ} (h₁ : reaches₁ f a c) (h₂ : b ∈ f a) : reaches f b c := sorry

/-- A variation on `reaches`. `reaches₀ f a b` holds if whenever `reaches₁ f b c` then
`reaches₁ f a c`. This is a weaker property than `reaches` and is useful for replacing states with
equivalent states without taking a step. -/
def reaches₀ {σ : Type u_1} (f : σ → Option σ) (a : σ) (b : σ)  :=
  ∀ (c : σ), reaches₁ f b c → reaches₁ f a c

theorem reaches₀.trans {σ : Type u_1} {f : σ → Option σ} {a : σ} {b : σ} {c : σ} (h₁ : reaches₀ f a b) (h₂ : reaches₀ f b c) : reaches₀ f a c :=
  fun (c_1 : σ) (ᾰ : reaches₁ f c c_1) => idRhs (reaches₁ f a c_1) (h₁ c_1 (h₂ c_1 ᾰ))

theorem reaches₀.refl {σ : Type u_1} {f : σ → Option σ} (a : σ) : reaches₀ f a a :=
  fun (c : σ) (ᾰ : reaches₁ f a c) => idRhs (reaches₁ f a c) ᾰ

theorem reaches₀.single {σ : Type u_1} {f : σ → Option σ} {a : σ} {b : σ} (h : b ∈ f a) : reaches₀ f a b :=
  fun (c : σ) (ᾰ : reaches₁ f b c) =>
    idRhs (relation.trans_gen (fun (a b : σ) => b ∈ f a) a c) (relation.trans_gen.head h ᾰ)

theorem reaches₀.head {σ : Type u_1} {f : σ → Option σ} {a : σ} {b : σ} {c : σ} (h : b ∈ f a) (h₂ : reaches₀ f b c) : reaches₀ f a c :=
  reaches₀.trans (reaches₀.single h) h₂

theorem reaches₀.tail {σ : Type u_1} {f : σ → Option σ} {a : σ} {b : σ} {c : σ} (h₁ : reaches₀ f a b) (h : c ∈ f b) : reaches₀ f a c :=
  reaches₀.trans h₁ (reaches₀.single h)

theorem reaches₀_eq {σ : Type u_1} {f : σ → Option σ} {a : σ} {b : σ} (e : f a = f b) : reaches₀ f a b :=
  fun (c : σ) (ᾰ : reaches₁ f b c) => idRhs (reaches₁ f a c) (iff.mpr (reaches₁_eq e) ᾰ)

theorem reaches₁.to₀ {σ : Type u_1} {f : σ → Option σ} {a : σ} {b : σ} (h : reaches₁ f a b) : reaches₀ f a b :=
  fun (c : σ) (ᾰ : reaches₁ f b c) =>
    idRhs (relation.trans_gen (fun (a b : σ) => b ∈ f a) a c) (relation.trans_gen.trans h ᾰ)

theorem reaches.to₀ {σ : Type u_1} {f : σ → Option σ} {a : σ} {b : σ} (h : reaches f a b) : reaches₀ f a b :=
  fun (c : σ) (ᾰ : reaches₁ f b c) =>
    idRhs (relation.trans_gen (fun (a b : σ) => b ∈ f a) a c) (relation.trans_gen.trans_right h ᾰ)

theorem reaches₀.tail' {σ : Type u_1} {f : σ → Option σ} {a : σ} {b : σ} {c : σ} (h : reaches₀ f a b) (h₂ : c ∈ f b) : reaches₁ f a c :=
  h c (relation.trans_gen.single h₂)

/-- (co-)Induction principle for `eval`. If a property `C` holds of any point `a` evaluating to `b`
which is either terminal (meaning `a = b`) or where the next point also satisfies `C`, then it
holds of any point where `eval f a` evaluates to `b`. This formalizes the notion that if
`eval f a` evaluates to `b` then it reaches terminal state `b` in finitely many steps. -/
def eval_induction {σ : Type u_1} {f : σ → Option σ} {b : σ} {C : σ → Sort u_2} {a : σ} (h : b ∈ eval f a) (H : (a : σ) → b ∈ eval f a → ((a' : σ) → b ∈ eval f a' → f a = some a' → C a') → C a) : C a :=
  pfun.fix_induction h
    fun (a' : σ) (ha' : b ∈ pfun.fix (fun (s : σ) => roption.some (option.elim (f s) (sum.inl s) sum.inr)) a')
      (h' :
      (a'_1 : σ) →
        b ∈ pfun.fix (fun (s : σ) => roption.some (option.elim (f s) (sum.inl s) sum.inr)) a'_1 →
          sum.inr a'_1 ∈ roption.some (option.elim (f a') (sum.inl a') sum.inr) → C a'_1) =>
      H a' ha' fun (b' : σ) (hb' : b ∈ eval f b') (e : f a' = some b') => h' b' hb' sorry

theorem mem_eval {σ : Type u_1} {f : σ → Option σ} {a : σ} {b : σ} : b ∈ eval f a ↔ reaches f a b ∧ f b = none := sorry

theorem eval_maximal₁ {σ : Type u_1} {f : σ → Option σ} {a : σ} {b : σ} (h : b ∈ eval f a) (c : σ) : ¬reaches₁ f b c := sorry

theorem eval_maximal {σ : Type u_1} {f : σ → Option σ} {a : σ} {b : σ} (h : b ∈ eval f a) {c : σ} : reaches f b c ↔ c = b := sorry

theorem reaches_eval {σ : Type u_1} {f : σ → Option σ} {a : σ} {b : σ} (ab : reaches f a b) : eval f a = eval f b := sorry

/-- Given a relation `tr : σ₁ → σ₂ → Prop` between state spaces, and state transition functions
`f₁ : σ₁ → option σ₁` and `f₂ : σ₂ → option σ₂`, `respects f₁ f₂ tr` means that if `tr a₁ a₂` holds
initially and `f₁` takes a step to `a₂` then `f₂` will take one or more steps before reaching a
state `b₂` satisfying `tr a₂ b₂`, and if `f₁ a₁` terminates then `f₂ a₂` also terminates.
Such a relation `tr` is also known as a refinement. -/
def respects {σ₁ : Type u_1} {σ₂ : Type u_2} (f₁ : σ₁ → Option σ₁) (f₂ : σ₂ → Option σ₂) (tr : σ₁ → σ₂ → Prop)  :=
  {a₁ : σ₁} → {a₂ : σ₂} → tr a₁ a₂ → sorry

theorem tr_reaches₁ {σ₁ : Type u_1} {σ₂ : Type u_2} {f₁ : σ₁ → Option σ₁} {f₂ : σ₂ → Option σ₂} {tr : σ₁ → σ₂ → Prop} (H : respects f₁ f₂ tr) {a₁ : σ₁} {a₂ : σ₂} (aa : tr a₁ a₂) {b₁ : σ₁} (ab : reaches₁ f₁ a₁ b₁) : ∃ (b₂ : σ₂), tr b₁ b₂ ∧ reaches₁ f₂ a₂ b₂ := sorry

theorem tr_reaches {σ₁ : Type u_1} {σ₂ : Type u_2} {f₁ : σ₁ → Option σ₁} {f₂ : σ₂ → Option σ₂} {tr : σ₁ → σ₂ → Prop} (H : respects f₁ f₂ tr) {a₁ : σ₁} {a₂ : σ₂} (aa : tr a₁ a₂) {b₁ : σ₁} (ab : reaches f₁ a₁ b₁) : ∃ (b₂ : σ₂), tr b₁ b₂ ∧ reaches f₂ a₂ b₂ := sorry

theorem tr_reaches_rev {σ₁ : Type u_1} {σ₂ : Type u_2} {f₁ : σ₁ → Option σ₁} {f₂ : σ₂ → Option σ₂} {tr : σ₁ → σ₂ → Prop} (H : respects f₁ f₂ tr) {a₁ : σ₁} {a₂ : σ₂} (aa : tr a₁ a₂) {b₂ : σ₂} (ab : reaches f₂ a₂ b₂) : ∃ (c₁ : σ₁), ∃ (c₂ : σ₂), reaches f₂ b₂ c₂ ∧ tr c₁ c₂ ∧ reaches f₁ a₁ c₁ := sorry

theorem tr_eval {σ₁ : Type u_1} {σ₂ : Type u_2} {f₁ : σ₁ → Option σ₁} {f₂ : σ₂ → Option σ₂} {tr : σ₁ → σ₂ → Prop} (H : respects f₁ f₂ tr) {a₁ : σ₁} {b₁ : σ₁} {a₂ : σ₂} (aa : tr a₁ a₂) (ab : b₁ ∈ eval f₁ a₁) : ∃ (b₂ : σ₂), tr b₁ b₂ ∧ b₂ ∈ eval f₂ a₂ := sorry

theorem tr_eval_rev {σ₁ : Type u_1} {σ₂ : Type u_2} {f₁ : σ₁ → Option σ₁} {f₂ : σ₂ → Option σ₂} {tr : σ₁ → σ₂ → Prop} (H : respects f₁ f₂ tr) {a₁ : σ₁} {b₂ : σ₂} {a₂ : σ₂} (aa : tr a₁ a₂) (ab : b₂ ∈ eval f₂ a₂) : ∃ (b₁ : σ₁), tr b₁ b₂ ∧ b₁ ∈ eval f₁ a₁ := sorry

theorem tr_eval_dom {σ₁ : Type u_1} {σ₂ : Type u_2} {f₁ : σ₁ → Option σ₁} {f₂ : σ₂ → Option σ₂} {tr : σ₁ → σ₂ → Prop} (H : respects f₁ f₂ tr) {a₁ : σ₁} {a₂ : σ₂} (aa : tr a₁ a₂) : roption.dom (eval f₂ a₂) ↔ roption.dom (eval f₁ a₁) := sorry

/-- A simpler version of `respects` when the state transition relation `tr` is a function. -/
def frespects {σ₁ : Type u_1} {σ₂ : Type u_2} (f₂ : σ₂ → Option σ₂) (tr : σ₁ → σ₂) (a₂ : σ₂) : Option σ₁ → Prop :=
  sorry

theorem frespects_eq {σ₁ : Type u_1} {σ₂ : Type u_2} {f₂ : σ₂ → Option σ₂} {tr : σ₁ → σ₂} {a₂ : σ₂} {b₂ : σ₂} (h : f₂ a₂ = f₂ b₂) {b₁ : Option σ₁} : frespects f₂ tr a₂ b₁ ↔ frespects f₂ tr b₂ b₁ := sorry

theorem fun_respects {σ₁ : Type u_1} {σ₂ : Type u_2} {f₁ : σ₁ → Option σ₁} {f₂ : σ₂ → Option σ₂} {tr : σ₁ → σ₂} : (respects f₁ f₂ fun (a : σ₁) (b : σ₂) => tr a = b) ↔ ∀ {a₁ : σ₁}, frespects f₂ tr (tr a₁) (f₁ a₁) := sorry

theorem tr_eval' {σ₁ : Type u_1} {σ₂ : Type u_1} (f₁ : σ₁ → Option σ₁) (f₂ : σ₂ → Option σ₂) (tr : σ₁ → σ₂) (H : respects f₁ f₂ fun (a : σ₁) (b : σ₂) => tr a = b) (a₁ : σ₁) : eval f₂ (tr a₁) = tr <$> eval f₁ a₁ := sorry

/-!
## The TM0 model

A TM0 turing machine is essentially a Post-Turing machine, adapted for type theory.

A Post-Turing machine with symbol type `Γ` and label type `Λ` is a function
`Λ → Γ → option (Λ × stmt)`, where a `stmt` can be either `move left`, `move right` or `write a`
for `a : Γ`. The machine works over a "tape", a doubly-infinite sequence of elements of `Γ`, and
an instantaneous configuration, `cfg`, is a label `q : Λ` indicating the current internal state of
the machine, and a `tape Γ` (which is essentially `ℤ →₀ Γ`). The evolution is described by the
`step` function:

* If `M q T.head = none`, then the machine halts.
* If `M q T.head = some (q', s)`, then the machine performs action `s : stmt` and then transitions
  to state `q'`.

The initial state takes a `list Γ` and produces a `tape Γ` where the head of the list is the head
of the tape and the rest of the list extends to the right, with the left side all blank. The final
state takes the entire right side of the tape right or equal to the current position of the
machine. (This is actually a `list_blank Γ`, not a `list Γ`, because we don't know, at this level
of generality, where the output ends. If equality to `default Γ` is decidable we can trim the list
to remove the infinite tail of blanks.)
-/

namespace TM0


/-- A Turing machine "statement" is just a command to either move
  left or right, or write a symbol on the tape. -/
inductive stmt (Γ : Type u_1) [Inhabited Γ] 
where
| move : dir → stmt Γ
| write : Γ → stmt Γ

protected instance stmt.inhabited (Γ : Type u_1) [Inhabited Γ] : Inhabited (stmt Γ) :=
  { default := stmt.write Inhabited.default }

/-- A Post-Turing machine with symbol type `Γ` and label type `Λ`
  is a function which, given the current state `q : Λ` and
  the tape head `a : Γ`, either halts (returns `none`) or returns
  a new state `q' : Λ` and a `stmt` describing what to do,
  either a move left or right, or a write command.

  Both `Λ` and `Γ` are required to be inhabited; the default value
  for `Γ` is the "blank" tape value, and the default value of `Λ` is
  the initial state. -/
def machine (Γ : Type u_1) [Inhabited Γ] (Λ : Type u_2) [Inhabited Λ]  :=
  Λ → Γ → Option (Λ × stmt Γ)

protected instance machine.inhabited (Γ : Type u_1) [Inhabited Γ] (Λ : Type u_2) [Inhabited Λ] : Inhabited (machine Γ Λ) :=
  eq.mpr sorry (pi.inhabited Λ)

/-- The configuration state of a Turing machine during operation
  consists of a label (machine state), and a tape, represented in
  the form `(a, L, R)` meaning the tape looks like `L.rev ++ [a] ++ R`
  with the machine currently reading the `a`. The lists are
  automatically extended with blanks as the machine moves around. -/
structure cfg (Γ : Type u_1) [Inhabited Γ] (Λ : Type u_2) [Inhabited Λ] 
where
  q : Λ
  tape : tape Γ

protected instance cfg.inhabited (Γ : Type u_1) [Inhabited Γ] (Λ : Type u_2) [Inhabited Λ] : Inhabited (cfg Γ Λ) :=
  { default := cfg.mk Inhabited.default Inhabited.default }

/-- Execution semantics of the Turing machine. -/
def step {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} [Inhabited Λ] (M : machine Γ Λ) : cfg Γ Λ → Option (cfg Γ Λ) :=
  sorry

/-- The statement `reaches M s₁ s₂` means that `s₂` is obtained
  starting from `s₁` after a finite number of steps from `s₂`. -/
def reaches {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} [Inhabited Λ] (M : machine Γ Λ) : cfg Γ Λ → cfg Γ Λ → Prop :=
  relation.refl_trans_gen fun (a b : cfg Γ Λ) => b ∈ step M a

/-- The initial configuration. -/
def init {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} [Inhabited Λ] (l : List Γ) : cfg Γ Λ :=
  cfg.mk Inhabited.default (tape.mk₁ l)

/-- Evaluate a Turing machine on initial input to a final state,
  if it terminates. -/
def eval {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} [Inhabited Λ] (M : machine Γ Λ) (l : List Γ) : roption (list_blank Γ) :=
  roption.map (fun (c : cfg Γ Λ) => tape.right₀ (cfg.tape c)) (eval (step M) (init l))

/-- The raw definition of a Turing machine does not require that
  `Γ` and `Λ` are finite, and in practice we will be interested
  in the infinite `Λ` case. We recover instead a notion of
  "effectively finite" Turing machines, which only make use of a
  finite subset of their states. We say that a set `S ⊆ Λ`
  supports a Turing machine `M` if `S` is closed under the
  transition function and contains the initial state. -/
def supports {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} [Inhabited Λ] (M : machine Γ Λ) (S : set Λ)  :=
  Inhabited.default ∈ S ∧ ∀ {q : Λ} {a : Γ} {q' : Λ} {s : stmt Γ}, (q', s) ∈ M q a → q ∈ S → q' ∈ S

theorem step_supports {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} [Inhabited Λ] (M : machine Γ Λ) {S : set Λ} (ss : supports M S) {c : cfg Γ Λ} {c' : cfg Γ Λ} : c' ∈ step M c → cfg.q c ∈ S → cfg.q c' ∈ S := sorry

theorem univ_supports {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} [Inhabited Λ] (M : machine Γ Λ) : supports M set.univ :=
  { left := trivial,
    right := fun (q : Λ) (a : Γ) (q' : Λ) (s : stmt Γ) (h₁ : (q', s) ∈ M q a) (h₂ : q ∈ set.univ) => trivial }

/-- Map a TM statement across a function. This does nothing to move statements and maps the write
values. -/
def stmt.map {Γ : Type u_1} [Inhabited Γ] {Γ' : Type u_2} [Inhabited Γ'] (f : pointed_map Γ Γ') : stmt Γ → stmt Γ' :=
  sorry

/-- Map a configuration across a function, given `f : Γ → Γ'` a map of the alphabets and
`g : Λ → Λ'` a map of the machine states. -/
def cfg.map {Γ : Type u_1} [Inhabited Γ] {Γ' : Type u_2} [Inhabited Γ'] {Λ : Type u_3} [Inhabited Λ] {Λ' : Type u_4} [Inhabited Λ'] (f : pointed_map Γ Γ') (g : Λ → Λ') : cfg Γ Λ → cfg Γ' Λ' :=
  sorry

/-- Because the state transition function uses the alphabet and machine states in both the input
and output, to map a machine from one alphabet and machine state space to another we need functions
in both directions, essentially an `equiv` without the laws. -/
def machine.map {Γ : Type u_1} [Inhabited Γ] {Γ' : Type u_2} [Inhabited Γ'] {Λ : Type u_3} [Inhabited Λ] {Λ' : Type u_4} [Inhabited Λ'] (M : machine Γ Λ) (f₁ : pointed_map Γ Γ') (f₂ : pointed_map Γ' Γ) (g₁ : Λ → Λ') (g₂ : Λ' → Λ) : machine Γ' Λ' :=
  sorry

theorem machine.map_step {Γ : Type u_1} [Inhabited Γ] {Γ' : Type u_2} [Inhabited Γ'] {Λ : Type u_3} [Inhabited Λ] {Λ' : Type u_4} [Inhabited Λ'] (M : machine Γ Λ) (f₁ : pointed_map Γ Γ') (f₂ : pointed_map Γ' Γ) (g₁ : Λ → Λ') (g₂ : Λ' → Λ) {S : set Λ} (f₂₁ : function.right_inverse ⇑f₁ ⇑f₂) (g₂₁ : ∀ (q : Λ), q ∈ S → g₂ (g₁ q) = q) (c : cfg Γ Λ) : cfg.q c ∈ S → option.map (cfg.map f₁ g₁) (step M c) = step (machine.map M f₁ f₂ g₁ g₂) (cfg.map f₁ g₁ c) := sorry

theorem map_init {Γ : Type u_1} [Inhabited Γ] {Γ' : Type u_2} [Inhabited Γ'] {Λ : Type u_3} [Inhabited Λ] {Λ' : Type u_4} [Inhabited Λ'] (f₁ : pointed_map Γ Γ') (g₁ : pointed_map Λ Λ') (l : List Γ) : cfg.map f₁ (⇑g₁) (init l) = init (list.map (⇑f₁) l) :=
  congr (congr_arg cfg.mk (pointed_map.map_pt g₁)) (tape.map_mk₁ f₁ l)

theorem machine.map_respects {Γ : Type u_1} [Inhabited Γ] {Γ' : Type u_2} [Inhabited Γ'] {Λ : Type u_3} [Inhabited Λ] {Λ' : Type u_4} [Inhabited Λ'] (M : machine Γ Λ) (f₁ : pointed_map Γ Γ') (f₂ : pointed_map Γ' Γ) (g₁ : pointed_map Λ Λ') (g₂ : Λ' → Λ) {S : set Λ} (ss : supports M S) (f₂₁ : function.right_inverse ⇑f₁ ⇑f₂) (g₂₁ : ∀ (q : Λ), q ∈ S → g₂ (coe_fn g₁ q) = q) : respects (step M) (step (machine.map M f₁ f₂ (⇑g₁) g₂))
  fun (a : cfg Γ Λ) (b : cfg Γ' Λ') => cfg.q a ∈ S ∧ cfg.map f₁ (⇑g₁) a = b := sorry

end TM0


/-!
## The TM1 model

The TM1 model is a simplification and extension of TM0 (Post-Turing model) in the direction of
Wang B-machines. The machine's internal state is extended with a (finite) store `σ` of variables
that may be accessed and updated at any time.

A machine is given by a `Λ` indexed set of procedures or functions. Each function has a body which
is a `stmt`. Most of the regular commands are allowed to use the current value `a` of the local
variables and the value `T.head` on the tape to calculate what to write or how to change local
state, but the statements themselves have a fixed structure. The `stmt`s can be as follows:

* `move d q`: move left or right, and then do `q`
* `write (f : Γ → σ → Γ) q`: write `f a T.head` to the tape, then do `q`
* `load (f : Γ → σ → σ) q`: change the internal state to `f a T.head`
* `branch (f : Γ → σ → bool) qtrue qfalse`: If `f a T.head` is true, do `qtrue`, else `qfalse`
* `goto (f : Γ → σ → Λ)`: Go to label `f a T.head`
* `halt`: Transition to the halting state, which halts on the following step

Note that here most statements do not have labels; `goto` commands can only go to a new function.
Only the `goto` and `halt` statements actually take a step; the rest is done by recursion on
statements and so take 0 steps. (There is a uniform bound on many statements can be executed before
the next `goto`, so this is an `O(1)` speedup with the constant depending on the machine.)

The `halt` command has a one step stutter before actually halting so that any changes made before
the halt have a chance to be "committed", since the `eval` relation uses the final configuration
before the halt as the output, and `move` and `write` etc. take 0 steps in this model.
-/

namespace TM1


/-- The TM1 model is a simplification and extension of TM0
  (Post-Turing model) in the direction of Wang B-machines. The machine's
  internal state is extended with a (finite) store `σ` of variables
  that may be accessed and updated at any time.
  A machine is given by a `Λ` indexed set of procedures or functions.
  Each function has a body which is a `stmt`, which can either be a
  `move` or `write` command, a `branch` (if statement based on the
  current tape value), a `load` (set the variable value),
  a `goto` (call another function), or `halt`. Note that here
  most statements do not have labels; `goto` commands can only
  go to a new function. All commands have access to the variable value
  and current tape value. -/
inductive stmt (Γ : Type u_1) [Inhabited Γ] (Λ : Type u_2) (σ : Type u_3) 
where
| move : dir → stmt Γ Λ σ → stmt Γ Λ σ
| write : (Γ → σ → Γ) → stmt Γ Λ σ → stmt Γ Λ σ
| load : (Γ → σ → σ) → stmt Γ Λ σ → stmt Γ Λ σ
| branch : (Γ → σ → Bool) → stmt Γ Λ σ → stmt Γ Λ σ → stmt Γ Λ σ
| goto : (Γ → σ → Λ) → stmt Γ Λ σ
| halt : stmt Γ Λ σ

protected instance stmt.inhabited (Γ : Type u_1) [Inhabited Γ] (Λ : Type u_2) (σ : Type u_3) : Inhabited (stmt Γ Λ σ) :=
  { default := stmt.halt }

/-- The configuration of a TM1 machine is given by the currently
  evaluating statement, the variable store value, and the tape. -/
structure cfg (Γ : Type u_1) [Inhabited Γ] (Λ : Type u_2) (σ : Type u_3) 
where
  l : Option Λ
  var : σ
  tape : tape Γ

protected instance cfg.inhabited (Γ : Type u_1) [Inhabited Γ] (Λ : Type u_2) (σ : Type u_3) [Inhabited σ] : Inhabited (cfg Γ Λ σ) :=
  { default := cfg.mk Inhabited.default Inhabited.default Inhabited.default }

/-- The semantics of TM1 evaluation. -/
def step_aux {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} {σ : Type u_3} : stmt Γ Λ σ → σ → tape Γ → cfg Γ Λ σ :=
  sorry

/-- The state transition function. -/
def step {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} {σ : Type u_3} (M : Λ → stmt Γ Λ σ) : cfg Γ Λ σ → Option (cfg Γ Λ σ) :=
  sorry

/-- A set `S` of labels supports the statement `q` if all the `goto`
  statements in `q` refer only to other functions in `S`. -/
def supports_stmt {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} {σ : Type u_3} (S : finset Λ) : stmt Γ Λ σ → Prop :=
  sorry

/-- The subterm closure of a statement. -/
def stmts₁ {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} {σ : Type u_3} : stmt Γ Λ σ → finset (stmt Γ Λ σ) :=
  sorry

theorem stmts₁_self {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} {σ : Type u_3} {q : stmt Γ Λ σ} : q ∈ stmts₁ q := sorry

theorem stmts₁_trans {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} {σ : Type u_3} {q₁ : stmt Γ Λ σ} {q₂ : stmt Γ Λ σ} : q₁ ∈ stmts₁ q₂ → stmts₁ q₁ ⊆ stmts₁ q₂ := sorry

theorem stmts₁_supports_stmt_mono {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} {σ : Type u_3} {S : finset Λ} {q₁ : stmt Γ Λ σ} {q₂ : stmt Γ Λ σ} (h : q₁ ∈ stmts₁ q₂) (hs : supports_stmt S q₂) : supports_stmt S q₁ := sorry

/-- The set of all statements in a turing machine, plus one extra value `none` representing the
halt state. This is used in the TM1 to TM0 reduction. -/
def stmts {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} {σ : Type u_3} (M : Λ → stmt Γ Λ σ) (S : finset Λ) : finset (Option (stmt Γ Λ σ)) :=
  finset.insert_none (finset.bUnion S fun (q : Λ) => stmts₁ (M q))

theorem stmts_trans {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} {σ : Type u_3} {M : Λ → stmt Γ Λ σ} {S : finset Λ} {q₁ : stmt Γ Λ σ} {q₂ : stmt Γ Λ σ} (h₁ : q₁ ∈ stmts₁ q₂) : some q₂ ∈ stmts M S → some q₁ ∈ stmts M S := sorry

/-- A set `S` of labels supports machine `M` if all the `goto`
  statements in the functions in `S` refer only to other functions
  in `S`. -/
def supports {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} {σ : Type u_3} [Inhabited Λ] (M : Λ → stmt Γ Λ σ) (S : finset Λ)  :=
  Inhabited.default ∈ S ∧ ∀ (q : Λ), q ∈ S → supports_stmt S (M q)

theorem stmts_supports_stmt {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} {σ : Type u_3} [Inhabited Λ] {M : Λ → stmt Γ Λ σ} {S : finset Λ} {q : stmt Γ Λ σ} (ss : supports M S) : some q ∈ stmts M S → supports_stmt S q := sorry

theorem step_supports {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} {σ : Type u_3} [Inhabited Λ] (M : Λ → stmt Γ Λ σ) {S : finset Λ} (ss : supports M S) {c : cfg Γ Λ σ} {c' : cfg Γ Λ σ} : c' ∈ step M c → cfg.l c ∈ finset.insert_none S → cfg.l c' ∈ finset.insert_none S := sorry

/-- The initial state, given a finite input that is placed on the tape starting at the TM head and
going to the right. -/
def init {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} {σ : Type u_3} [Inhabited Λ] [Inhabited σ] (l : List Γ) : cfg Γ Λ σ :=
  cfg.mk (some Inhabited.default) Inhabited.default (tape.mk₁ l)

/-- Evaluate a TM to completion, resulting in an output list on the tape (with an indeterminate
number of blanks on the end). -/
def eval {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} {σ : Type u_3} [Inhabited Λ] [Inhabited σ] (M : Λ → stmt Γ Λ σ) (l : List Γ) : roption (list_blank Γ) :=
  roption.map (fun (c : cfg Γ Λ σ) => tape.right₀ (cfg.tape c)) (eval (step M) (init l))

end TM1


/-!
## TM1 emulator in TM0

To prove that TM1 computable functions are TM0 computable, we need to reduce each TM1 program to a
TM0 program. So suppose a TM1 program is given. We take the following:

* The alphabet `Γ` is the same for both TM1 and TM0
* The set of states `Λ'` is defined to be `option stmt₁ × σ`, that is, a TM1 statement or `none`
  representing halt, and the possible settings of the internal variables.
  Note that this is an infinite set, because `stmt₁` is infinite. This is okay because we assume
  that from the initial TM1 state, only finitely many other labels are reachable, and there are
  only finitely many statements that appear in all of these functions.

Even though `stmt₁` contains a statement called `halt`, we must separate it from `none`
(`some halt` steps to `none` and `none` actually halts) because there is a one step stutter in the
TM1 semantics.
-/

namespace TM1to0


/-- The base machine state space is a pair of an `option stmt₁` representing the current program
to be executed, or `none` for the halt state, and a `σ` which is the local state (stored in the TM,
not the tape). Because there are an infinite number of programs, this state space is infinite, but
for a finitely supported TM1 machine and a finite type `σ`, only finitely many of these states are
reachable. -/
-- because of the inhabited instance, but we could avoid the inhabited instances on Λ and σ here.

-- But they are parameters so we cannot easily skip them for just this definition.

def Λ' {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} [Inhabited Λ] {σ : Type u_3} [Inhabited σ] (M : Λ → TM1.stmt Γ Λ σ)  :=
  Option (TM1.stmt Γ Λ σ) × σ

protected instance Λ'.inhabited {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} [Inhabited Λ] {σ : Type u_3} [Inhabited σ] (M : Λ → TM1.stmt Γ Λ σ) : Inhabited (Λ' M) :=
  { default := (some (M Inhabited.default), Inhabited.default) }

/-- The core TM1 → TM0 translation function. Here `s` is the current value on the tape, and the
`stmt₁` is the TM1 statement to translate, with local state `v : σ`. We evaluate all regular
instructions recursively until we reach either a `move` or `write` command, or a `goto`; in the
latter case we emit a dummy `write s` step and transition to the new target location. -/
def tr_aux {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} [Inhabited Λ] {σ : Type u_3} [Inhabited σ] (M : Λ → TM1.stmt Γ Λ σ) (s : Γ) : TM1.stmt Γ Λ σ → σ → Λ' M × TM0.stmt Γ :=
  sorry

/-- The translated TM0 machine (given the TM1 machine input). -/
def tr {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} [Inhabited Λ] {σ : Type u_3} [Inhabited σ] (M : Λ → TM1.stmt Γ Λ σ) : TM0.machine Γ (Λ' M) :=
  sorry

/-- Translate configurations from TM1 to TM0. -/
def tr_cfg {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} [Inhabited Λ] {σ : Type u_3} [Inhabited σ] (M : Λ → TM1.stmt Γ Λ σ) : TM1.cfg Γ Λ σ → TM0.cfg Γ (Λ' M) :=
  sorry

theorem tr_respects {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} [Inhabited Λ] {σ : Type u_3} [Inhabited σ] (M : Λ → TM1.stmt Γ Λ σ) : respects (TM1.step M) (TM0.step (tr M)) fun (c₁ : TM1.cfg Γ Λ σ) (c₂ : TM0.cfg Γ (Λ' M)) => tr_cfg M c₁ = c₂ := sorry

theorem tr_eval {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} [Inhabited Λ] {σ : Type u_3} [Inhabited σ] (M : Λ → TM1.stmt Γ Λ σ) (l : List Γ) : TM0.eval (tr M) l = TM1.eval M l := sorry

/-- Given a finite set of accessible `Λ` machine states, there is a finite set of accessible
machine states in the target (even though the type `Λ'` is infinite). -/
def tr_stmts {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} [Inhabited Λ] {σ : Type u_3} [Inhabited σ] (M : Λ → TM1.stmt Γ Λ σ) [fintype σ] (S : finset Λ) : finset (Λ' M) :=
  finset.product (TM1.stmts M S) finset.univ

theorem tr_supports {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} [Inhabited Λ] {σ : Type u_3} [Inhabited σ] (M : Λ → TM1.stmt Γ Λ σ) [fintype σ] {S : finset Λ} (ss : TM1.supports M S) : TM0.supports (tr M) ↑(tr_stmts M S) := sorry

end TM1to0


/-!
## TM1(Γ) emulator in TM1(bool)

The most parsimonious Turing machine model that is still Turing complete is `TM0` with `Γ = bool`.
Because our construction in the previous section reducing `TM1` to `TM0` doesn't change the
alphabet, we can do the alphabet reduction on `TM1` instead of `TM0` directly.

The basic idea is to use a bijection between `Γ` and a subset of `vector bool n`, where `n` is a
fixed constant. Each tape element is represented as a block of `n` bools. Whenever the machine
wants to read a symbol from the tape, it traverses over the block, performing `n` `branch`
instructions to each any of the `2^n` results.

For the `write` instruction, we have to use a `goto` because we need to follow a different code
path depending on the local state, which is not available in the TM1 model, so instead we jump to
a label computed using the read value and the local state, which performs the writing and returns
to normal execution.

Emulation overhead is `O(1)`. If not for the above `write` behavior it would be 1-1 because we are
exploiting the 0-step behavior of regular commands to avoid taking steps, but there are
nevertheless a bounded number of `write` calls between `goto` statements because TM1 statements are
finitely long.
-/

namespace TM1to1


theorem exists_enc_dec {Γ : Type u_1} [Inhabited Γ] [fintype Γ] : ∃ (n : ℕ),
  ∃ (enc : Γ → vector Bool n),
    ∃ (dec : vector Bool n → Γ), enc Inhabited.default = vector.repeat false n ∧ ∀ (a : Γ), dec (enc a) = a := sorry

/-- The configuration state of the TM. -/
inductive Λ' {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} [Inhabited Λ] {σ : Type u_3} [Inhabited σ] 
where
| normal : Λ → Λ'
| write : Γ → TM1.stmt Γ Λ σ → Λ'

protected instance Λ'.inhabited {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} [Inhabited Λ] {σ : Type u_3} [Inhabited σ] : Inhabited Λ' :=
  { default := Λ'.normal Inhabited.default }

/-- Read a vector of length `n` from the tape. -/
def read_aux {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} [Inhabited Λ] {σ : Type u_3} [Inhabited σ] (n : ℕ) : (vector Bool n → TM1.stmt Bool Λ' σ) → TM1.stmt Bool Λ' σ :=
  sorry

/-- A move left or right corresponds to `n` moves across the super-cell. -/
def move {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} [Inhabited Λ] {σ : Type u_3} [Inhabited σ] {n : ℕ} (d : dir) (q : TM1.stmt Bool Λ' σ) : TM1.stmt Bool Λ' σ :=
  nat.iterate (TM1.stmt.move d) n q

/-- To read a symbol from the tape, we use `read_aux` to traverse the symbol,
then return to the original position with `n` moves to the left. -/
def read {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} [Inhabited Λ] {σ : Type u_3} [Inhabited σ] {n : ℕ} (dec : vector Bool n → Γ) (f : Γ → TM1.stmt Bool Λ' σ) : TM1.stmt Bool Λ' σ :=
  read_aux n fun (v : vector Bool n) => move dir.left (f (dec v))

/-- Write a list of bools on the tape. -/
def write {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} [Inhabited Λ] {σ : Type u_3} [Inhabited σ] : List Bool → TM1.stmt Bool Λ' σ → TM1.stmt Bool Λ' σ :=
  sorry

/-- Translate a normal instruction. For the `write` command, we use a `goto` indirection so that
we can access the current value of the tape. -/
def tr_normal {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} [Inhabited Λ] {σ : Type u_3} [Inhabited σ] {n : ℕ} (dec : vector Bool n → Γ) : TM1.stmt Γ Λ σ → TM1.stmt Bool Λ' σ :=
  sorry

theorem step_aux_move {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} [Inhabited Λ] {σ : Type u_3} [Inhabited σ] {n : ℕ} (d : dir) (q : TM1.stmt Bool Λ' σ) (v : σ) (T : tape Bool) : TM1.step_aux (move d q) v T = TM1.step_aux q v (nat.iterate (tape.move d) n T) := sorry

theorem supports_stmt_move {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} [Inhabited Λ] {σ : Type u_3} [Inhabited σ] {n : ℕ} {S : finset Λ'} {d : dir} {q : TM1.stmt Bool Λ' σ} : TM1.supports_stmt S (move d q) = TM1.supports_stmt S q := sorry

theorem supports_stmt_write {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} [Inhabited Λ] {σ : Type u_3} [Inhabited σ] {S : finset Λ'} {l : List Bool} {q : TM1.stmt Bool Λ' σ} : TM1.supports_stmt S (write l q) = TM1.supports_stmt S q := sorry

theorem supports_stmt_read {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} [Inhabited Λ] {σ : Type u_3} [Inhabited σ] {n : ℕ} (dec : vector Bool n → Γ) {S : finset Λ'} {f : Γ → TM1.stmt Bool Λ' σ} : (∀ (a : Γ), TM1.supports_stmt S (f a)) → TM1.supports_stmt S (read dec f) := sorry

/-- The low level tape corresponding to the given tape over alphabet `Γ`. -/
def tr_tape' {Γ : Type u_1} [Inhabited Γ] {n : ℕ} {enc : Γ → vector Bool n} (enc0 : enc Inhabited.default = vector.repeat false n) (L : list_blank Γ) (R : list_blank Γ) : tape Bool :=
  tape.mk' (list_blank.bind L (fun (x : Γ) => list.reverse (vector.to_list (enc x))) sorry)
    (list_blank.bind R (fun (x : Γ) => vector.to_list (enc x)) sorry)

/-- The low level tape corresponding to the given tape over alphabet `Γ`. -/
def tr_tape {Γ : Type u_1} [Inhabited Γ] {n : ℕ} {enc : Γ → vector Bool n} (enc0 : enc Inhabited.default = vector.repeat false n) (T : tape Γ) : tape Bool :=
  tr_tape' enc0 (tape.left T) (tape.right₀ T)

theorem tr_tape_mk' {Γ : Type u_1} [Inhabited Γ] {n : ℕ} {enc : Γ → vector Bool n} (enc0 : enc Inhabited.default = vector.repeat false n) (L : list_blank Γ) (R : list_blank Γ) : tr_tape enc0 (tape.mk' L R) = tr_tape' enc0 L R := sorry

/-- The top level program. -/
def tr {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} [Inhabited Λ] {σ : Type u_3} [Inhabited σ] {n : ℕ} (enc : Γ → vector Bool n) (dec : vector Bool n → Γ) (M : Λ → TM1.stmt Γ Λ σ) : Λ' → TM1.stmt Bool Λ' σ :=
  sorry

/-- The machine configuration translation. -/
def tr_cfg {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} [Inhabited Λ] {σ : Type u_3} [Inhabited σ] {n : ℕ} {enc : Γ → vector Bool n} (enc0 : enc Inhabited.default = vector.repeat false n) : TM1.cfg Γ Λ σ → TM1.cfg Bool Λ' σ :=
  sorry

theorem tr_tape'_move_left {Γ : Type u_1} [Inhabited Γ] {n : ℕ} {enc : Γ → vector Bool n} (enc0 : enc Inhabited.default = vector.repeat false n) (L : list_blank Γ) (R : list_blank Γ) : nat.iterate (tape.move dir.left) n (tr_tape' enc0 L R) =
  tr_tape' enc0 (list_blank.tail L) (list_blank.cons (list_blank.head L) R) := sorry

theorem tr_tape'_move_right {Γ : Type u_1} [Inhabited Γ] {n : ℕ} {enc : Γ → vector Bool n} (enc0 : enc Inhabited.default = vector.repeat false n) (L : list_blank Γ) (R : list_blank Γ) : nat.iterate (tape.move dir.right) n (tr_tape' enc0 L R) =
  tr_tape' enc0 (list_blank.cons (list_blank.head R) L) (list_blank.tail R) := sorry

theorem step_aux_write {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} [Inhabited Λ] {σ : Type u_3} [Inhabited σ] {n : ℕ} {enc : Γ → vector Bool n} (enc0 : enc Inhabited.default = vector.repeat false n) (q : TM1.stmt Bool Λ' σ) (v : σ) (a : Γ) (b : Γ) (L : list_blank Γ) (R : list_blank Γ) : TM1.step_aux (write (vector.to_list (enc a)) q) v (tr_tape' enc0 L (list_blank.cons b R)) =
  TM1.step_aux q v (tr_tape' enc0 (list_blank.cons a L) R) := sorry

theorem step_aux_read {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} [Inhabited Λ] {σ : Type u_3} [Inhabited σ] {n : ℕ} {enc : Γ → vector Bool n} (dec : vector Bool n → Γ) (enc0 : enc Inhabited.default = vector.repeat false n) (encdec : ∀ (a : Γ), dec (enc a) = a) (f : Γ → TM1.stmt Bool Λ' σ) (v : σ) (L : list_blank Γ) (R : list_blank Γ) : TM1.step_aux (read dec f) v (tr_tape' enc0 L R) = TM1.step_aux (f (list_blank.head R)) v (tr_tape' enc0 L R) := sorry

theorem tr_respects {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} [Inhabited Λ] {σ : Type u_3} [Inhabited σ] {n : ℕ} {enc : Γ → vector Bool n} (dec : vector Bool n → Γ) (enc0 : enc Inhabited.default = vector.repeat false n) (M : Λ → TM1.stmt Γ Λ σ) (encdec : ∀ (a : Γ), dec (enc a) = a) : respects (TM1.step M) (TM1.step (tr enc dec M)) fun (c₁ : TM1.cfg Γ Λ σ) (c₂ : TM1.cfg Bool Λ' σ) => tr_cfg enc0 c₁ = c₂ := sorry

/-- The set of accessible `Λ'.write` machine states. -/
def writes {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} [Inhabited Λ] {σ : Type u_3} [Inhabited σ] [fintype Γ] : TM1.stmt Γ Λ σ → finset Λ' :=
  sorry

/-- The set of accessible machine states, assuming that the input machine is supported on `S`,
are the normal states embedded from `S`, plus all write states accessible from these states. -/
def tr_supp {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} [Inhabited Λ] {σ : Type u_3} [Inhabited σ] (M : Λ → TM1.stmt Γ Λ σ) [fintype Γ] (S : finset Λ) : finset Λ' :=
  finset.bUnion S fun (l : Λ) => insert (Λ'.normal l) (writes (M l))

theorem tr_supports {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} [Inhabited Λ] {σ : Type u_3} [Inhabited σ] {n : ℕ} {enc : Γ → vector Bool n} (dec : vector Bool n → Γ) (M : Λ → TM1.stmt Γ Λ σ) [fintype Γ] {S : finset Λ} (ss : TM1.supports M S) : TM1.supports (tr enc dec M) (tr_supp M S) := sorry

end TM1to1


/-!
## TM0 emulator in TM1

To establish that TM0 and TM1 are equivalent computational models, we must also have a TM0 emulator
in TM1. The main complication here is that TM0 allows an action to depend on the value at the head
and local state, while TM1 doesn't (in order to have more programming language-like semantics).
So we use a computed `goto` to go to a state that performes the desired action and then returns to
normal execution.

One issue with this is that the `halt` instruction is supposed to halt immediately, not take a step
to a halting state. To resolve this we do a check for `halt` first, then `goto` (with an
unreachable branch).
-/

namespace TM0to1


/-- The machine states for a TM1 emulating a TM0 machine. States of the TM0 machine are embedded
as `normal q` states, but the actual operation is split into two parts, a jump to `act s q`
followed by the action and a jump to the next `normal` state.  -/
inductive Λ' {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} [Inhabited Λ] 
where
| normal : Λ → Λ'
| act : TM0.stmt Γ → Λ → Λ'

protected instance Λ'.inhabited {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} [Inhabited Λ] : Inhabited Λ' :=
  { default := Λ'.normal Inhabited.default }

/-- The program.  -/
def tr {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} [Inhabited Λ] (M : TM0.machine Γ Λ) : Λ' → TM1.stmt Γ Λ' Unit :=
  sorry

/-- The configuration translation. -/
def tr_cfg {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} [Inhabited Λ] (M : TM0.machine Γ Λ) : TM0.cfg Γ Λ → TM1.cfg Γ Λ' Unit :=
  sorry

theorem tr_respects {Γ : Type u_1} [Inhabited Γ] {Λ : Type u_2} [Inhabited Λ] (M : TM0.machine Γ Λ) : respects (TM0.step M) (TM1.step (tr M)) fun (a : TM0.cfg Γ Λ) (b : TM1.cfg Γ Λ' Unit) => tr_cfg M a = b := sorry

end TM0to1


/-!
## The TM2 model

The TM2 model removes the tape entirely from the TM1 model, replacing it with an arbitrary (finite)
collection of stacks, each with elements of different types (the alphabet of stack `k : K` is
`Γ k`). The statements are:

* `push k (f : σ → Γ k) q` puts `f a` on the `k`-th stack, then does `q`.
* `pop k (f : σ → option (Γ k) → σ) q` changes the state to `f a (S k).head`, where `S k` is the
  value of the `k`-th stack, and removes this element from the stack, then does `q`.
* `peek k (f : σ → option (Γ k) → σ) q` changes the state to `f a (S k).head`, where `S k` is the
  value of the `k`-th stack, then does `q`.
* `load (f : σ → σ) q` reads nothing but applies `f` to the internal state, then does `q`.
* `branch (f : σ → bool) qtrue qfalse` does `qtrue` or `qfalse` according to `f a`.
* `goto (f : σ → Λ)` jumps to label `f a`.
* `halt` halts on the next step.

The configuration is a tuple `(l, var, stk)` where `l : option Λ` is the current label to run or
`none` for the halting state, `var : σ` is the (finite) internal state, and `stk : ∀ k, list (Γ k)`
is the collection of stacks. (Note that unlike the `TM0` and `TM1` models, these are not
`list_blank`s, they have definite ends that can be detected by the `pop` command.)

Given a designated stack `k` and a value `L : list (Γ k)`, the initial configuration has all the
stacks empty except the designated "input" stack; in `eval` this designated stack also functions
as the output stack.
-/

namespace TM2


/-- The TM2 model removes the tape entirely from the TM1 model,
  replacing it with an arbitrary (finite) collection of stacks.
  The operation `push` puts an element on one of the stacks,
  and `pop` removes an element from a stack (and modifying the
  internal state based on the result). `peek` modifies the
  internal state but does not remove an element. -/
inductive stmt {K : Type u_1} [DecidableEq K] (Γ : K → Type u_2) (Λ : Type u_3) (σ : Type u_4) 
where
| push : (k : K) → (σ → Γ k) → stmt Γ Λ σ → stmt Γ Λ σ
| peek : (k : K) → (σ → Option (Γ k) → σ) → stmt Γ Λ σ → stmt Γ Λ σ
| pop : (k : K) → (σ → Option (Γ k) → σ) → stmt Γ Λ σ → stmt Γ Λ σ
| load : (σ → σ) → stmt Γ Λ σ → stmt Γ Λ σ
| branch : (σ → Bool) → stmt Γ Λ σ → stmt Γ Λ σ → stmt Γ Λ σ
| goto : (σ → Λ) → stmt Γ Λ σ
| halt : stmt Γ Λ σ

protected instance stmt.inhabited {K : Type u_1} [DecidableEq K] (Γ : K → Type u_2) (Λ : Type u_3) (σ : Type u_4) : Inhabited (stmt Γ Λ σ) :=
  { default := stmt.halt }

/-- A configuration in the TM2 model is a label (or `none` for the halt state), the state of
local variables, and the stacks. (Note that the stacks are not `list_blank`s, they have a definite
size.) -/
structure cfg {K : Type u_1} [DecidableEq K] (Γ : K → Type u_2) (Λ : Type u_3) (σ : Type u_4) 
where
  l : Option Λ
  var : σ
  stk : (k : K) → List (Γ k)

protected instance cfg.inhabited {K : Type u_1} [DecidableEq K] (Γ : K → Type u_2) (Λ : Type u_3) (σ : Type u_4) [Inhabited σ] : Inhabited (cfg Γ Λ σ) :=
  { default := cfg.mk Inhabited.default Inhabited.default Inhabited.default }

/-- The step function for the TM2 model. -/
@[simp] def step_aux {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} {Λ : Type u_3} {σ : Type u_4} : stmt Γ Λ σ → σ → ((k : K) → List (Γ k)) → cfg Γ Λ σ :=
  sorry

/-- The step function for the TM2 model. -/
@[simp] def step {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} {Λ : Type u_3} {σ : Type u_4} (M : Λ → stmt Γ Λ σ) : cfg Γ Λ σ → Option (cfg Γ Λ σ) :=
  sorry

/-- The (reflexive) reachability relation for the TM2 model. -/
def reaches {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} {Λ : Type u_3} {σ : Type u_4} (M : Λ → stmt Γ Λ σ) : cfg Γ Λ σ → cfg Γ Λ σ → Prop :=
  relation.refl_trans_gen fun (a b : cfg Γ Λ σ) => b ∈ step M a

/-- Given a set `S` of states, `support_stmt S q` means that `q` only jumps to states in `S`. -/
def supports_stmt {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} {Λ : Type u_3} {σ : Type u_4} (S : finset Λ) : stmt Γ Λ σ → Prop :=
  sorry

/-- The set of subtree statements in a statement. -/
def stmts₁ {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} {Λ : Type u_3} {σ : Type u_4} : stmt Γ Λ σ → finset (stmt Γ Λ σ) :=
  sorry

theorem stmts₁_self {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} {Λ : Type u_3} {σ : Type u_4} {q : stmt Γ Λ σ} : q ∈ stmts₁ q := sorry

theorem stmts₁_trans {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} {Λ : Type u_3} {σ : Type u_4} {q₁ : stmt Γ Λ σ} {q₂ : stmt Γ Λ σ} : q₁ ∈ stmts₁ q₂ → stmts₁ q₁ ⊆ stmts₁ q₂ := sorry

theorem stmts₁_supports_stmt_mono {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} {Λ : Type u_3} {σ : Type u_4} {S : finset Λ} {q₁ : stmt Γ Λ σ} {q₂ : stmt Γ Λ σ} (h : q₁ ∈ stmts₁ q₂) (hs : supports_stmt S q₂) : supports_stmt S q₁ := sorry

/-- The set of statements accessible from initial set `S` of labels. -/
def stmts {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} {Λ : Type u_3} {σ : Type u_4} (M : Λ → stmt Γ Λ σ) (S : finset Λ) : finset (Option (stmt Γ Λ σ)) :=
  finset.insert_none (finset.bUnion S fun (q : Λ) => stmts₁ (M q))

theorem stmts_trans {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} {Λ : Type u_3} {σ : Type u_4} {M : Λ → stmt Γ Λ σ} {S : finset Λ} {q₁ : stmt Γ Λ σ} {q₂ : stmt Γ Λ σ} (h₁ : q₁ ∈ stmts₁ q₂) : some q₂ ∈ stmts M S → some q₁ ∈ stmts M S := sorry

/-- Given a TM2 machine `M` and a set `S` of states, `supports M S` means that all states in
`S` jump only to other states in `S`. -/
def supports {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} {Λ : Type u_3} {σ : Type u_4} [Inhabited Λ] (M : Λ → stmt Γ Λ σ) (S : finset Λ)  :=
  Inhabited.default ∈ S ∧ ∀ (q : Λ), q ∈ S → supports_stmt S (M q)

theorem stmts_supports_stmt {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} {Λ : Type u_3} {σ : Type u_4} [Inhabited Λ] {M : Λ → stmt Γ Λ σ} {S : finset Λ} {q : stmt Γ Λ σ} (ss : supports M S) : some q ∈ stmts M S → supports_stmt S q := sorry

theorem step_supports {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} {Λ : Type u_3} {σ : Type u_4} [Inhabited Λ] (M : Λ → stmt Γ Λ σ) {S : finset Λ} (ss : supports M S) {c : cfg Γ Λ σ} {c' : cfg Γ Λ σ} : c' ∈ step M c → cfg.l c ∈ finset.insert_none S → cfg.l c' ∈ finset.insert_none S := sorry

/-- The initial state of the TM2 model. The input is provided on a designated stack. -/
def init {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} {Λ : Type u_3} {σ : Type u_4} [Inhabited Λ] [Inhabited σ] (k : K) (L : List (Γ k)) : cfg Γ Λ σ :=
  cfg.mk (some Inhabited.default) Inhabited.default (function.update (fun (_x : K) => []) k L)

/-- Evaluates a TM2 program to completion, with the output on the same stack as the input. -/
def eval {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} {Λ : Type u_3} {σ : Type u_4} [Inhabited Λ] [Inhabited σ] (M : Λ → stmt Γ Λ σ) (k : K) (L : List (Γ k)) : roption (List (Γ k)) :=
  roption.map (fun (c : cfg Γ Λ σ) => cfg.stk c k) (eval (step M) (init k L))

end TM2


/-!
## TM2 emulator in TM1

To prove that TM2 computable functions are TM1 computable, we need to reduce each TM2 program to a
TM1 program. So suppose a TM2 program is given. This program has to maintain a whole collection of
stacks, but we have only one tape, so we must "multiplex" them all together. Pictorially, if stack
1 contains `[a, b]` and stack 2 contains `[c, d, e, f]` then the tape looks like this:

```
 bottom:  ... | _ | T | _ | _ | _ | _ | ...
 stack 1: ... | _ | b | a | _ | _ | _ | ...
 stack 2: ... | _ | f | e | d | c | _ | ...
```

where a tape element is a vertical slice through the diagram. Here the alphabet is
`Γ' := bool × ∀ k, option (Γ k)`, where:

* `bottom : bool` is marked only in one place, the initial position of the TM, and represents the
  tail of all stacks. It is never modified.
* `stk k : option (Γ k)` is the value of the `k`-th stack, if in range, otherwise `none` (which is
  the blank value). Note that the head of the stack is at the far end; this is so that push and pop
  don't have to do any shifting.

In "resting" position, the TM is sitting at the position marked `bottom`. For non-stack actions,
it operates in place, but for the stack actions `push`, `peek`, and `pop`, it must shuttle to the
end of the appropriate stack, make its changes, and then return to the bottom. So the states are:

* `normal (l : Λ)`: waiting at `bottom` to execute function `l`
* `go k (s : st_act k) (q : stmt₂)`: travelling to the right to get to the end of stack `k` in
  order to perform stack action `s`, and later continue with executing `q`
* `ret (q : stmt₂)`: travelling to the left after having performed a stack action, and executing
  `q` once we arrive

Because of the shuttling, emulation overhead is `O(n)`, where `n` is the current maximum of the
length of all stacks. Therefore a program that takes `k` steps to run in TM2 takes `O((m+k)k)`
steps to run when emulated in TM1, where `m` is the length of the input.
-/

namespace TM2to1


-- A displaced lemma proved in unnecessary generality

theorem stk_nth_val {K : Type u_1} {Γ : K → Type u_2} {L : list_blank ((k : K) → Option (Γ k))} {k : K} {S : List (Γ k)} (n : ℕ) (hL : list_blank.map (proj k) L = list_blank.mk (list.reverse (list.map some S))) : list_blank.nth L n k = list.nth (list.reverse S) n := sorry

/-- The alphabet of the TM2 simulator on TM1 is a marker for the stack bottom,
plus a vector of stack elements for each stack, or none if the stack does not extend this far. -/
-- the decidable_eq assumption, and this is a local definition anyway so it's not important.

def Γ' {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2}  :=
  Bool × ((k : K) → Option (Γ k))

protected instance Γ'.inhabited {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} : Inhabited Γ' :=
  { default := (false, fun (_x : K) => none) }

protected instance Γ'.fintype {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} [fintype K] [(k : K) → fintype (Γ k)] : fintype Γ' :=
  prod.fintype Bool ((k : K) → Option (Γ k))

/-- The bottom marker is fixed throughout the calculation, so we use the `add_bottom` function
to express the program state in terms of a tape with only the stacks themselves. -/
def add_bottom {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} (L : list_blank ((k : K) → Option (Γ k))) : list_blank Γ' :=
  list_blank.cons (tt, list_blank.head L) (list_blank.map (pointed_map.mk (Prod.mk false) sorry) (list_blank.tail L))

theorem add_bottom_map {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} (L : list_blank ((k : K) → Option (Γ k))) : list_blank.map (pointed_map.mk prod.snd rfl) (add_bottom L) = L := sorry

theorem add_bottom_modify_nth {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} (f : ((k : K) → Option (Γ k)) → (k : K) → Option (Γ k)) (L : list_blank ((k : K) → Option (Γ k))) (n : ℕ) : list_blank.modify_nth (fun (a : Γ') => (prod.fst a, f (prod.snd a))) n (add_bottom L) =
  add_bottom (list_blank.modify_nth f n L) := sorry

theorem add_bottom_nth_snd {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} (L : list_blank ((k : K) → Option (Γ k))) (n : ℕ) : prod.snd (list_blank.nth (add_bottom L) n) = list_blank.nth L n := sorry

theorem add_bottom_nth_succ_fst {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} (L : list_blank ((k : K) → Option (Γ k))) (n : ℕ) : prod.fst (list_blank.nth (add_bottom L) (n + 1)) = false := sorry

theorem add_bottom_head_fst {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} (L : list_blank ((k : K) → Option (Γ k))) : prod.fst (list_blank.head (add_bottom L)) = tt := sorry

/-- A stack action is a command that interacts with the top of a stack. Our default position
is at the bottom of all the stacks, so we have to hold on to this action while going to the end
to modify the stack. -/
inductive st_act {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} {σ : Type u_4} [Inhabited σ] (k : K) 
where
| push : (σ → Γ k) → st_act k
| peek : (σ → Option (Γ k) → σ) → st_act k
| pop : (σ → Option (Γ k) → σ) → st_act k

protected instance st_act.inhabited {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} {σ : Type u_4} [Inhabited σ] {k : K} : Inhabited (st_act k) :=
  { default := st_act.peek fun (s : σ) (_x : Option (Γ k)) => s }

/-- The TM2 statement corresponding to a stack action. -/
-- it is worth to omit the typeclass assumption without breaking the parameters

def st_run {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} {Λ : Type u_3} [Inhabited Λ] {σ : Type u_4} [Inhabited σ] {k : K} : st_act k → TM2.stmt Γ Λ σ → TM2.stmt Γ Λ σ :=
  sorry

/-- The effect of a stack action on the local variables, given the value of the stack. -/
def st_var {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} {σ : Type u_4} [Inhabited σ] {k : K} (v : σ) (l : List (Γ k)) : st_act k → σ :=
  sorry

/-- The effect of a stack action on the stack. -/
def st_write {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} {σ : Type u_4} [Inhabited σ] {k : K} (v : σ) (l : List (Γ k)) : st_act k → List (Γ k) :=
  sorry

/-- We have partitioned the TM2 statements into "stack actions", which require going to the end
of the stack, and all other actions, which do not. This is a modified recursor which lumps the
stack actions into one. -/
def stmt_st_rec {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} {Λ : Type u_3} [Inhabited Λ] {σ : Type u_4} [Inhabited σ] {C : TM2.stmt Γ Λ σ → Sort l} (H₁ : (k : K) → (s : st_act k) → (q : TM2.stmt Γ Λ σ) → C q → C (st_run s q)) (H₂ : (a : σ → σ) → (q : TM2.stmt Γ Λ σ) → C q → C (TM2.stmt.load a q)) (H₃ : (p : σ → Bool) → (q₁ q₂ : TM2.stmt Γ Λ σ) → C q₁ → C q₂ → C (TM2.stmt.branch p q₁ q₂)) (H₄ : (l : σ → Λ) → C (TM2.stmt.goto l)) (H₅ : C TM2.stmt.halt) (n : TM2.stmt Γ Λ σ) : C n :=
  sorry

theorem supports_run {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} {Λ : Type u_3} [Inhabited Λ] {σ : Type u_4} [Inhabited σ] (S : finset Λ) {k : K} (s : st_act k) (q : TM2.stmt Γ Λ σ) : TM2.supports_stmt S (st_run s q) ↔ TM2.supports_stmt S q :=
  st_act.cases_on s (fun (s : σ → Γ k) => iff.refl (TM2.supports_stmt S (st_run (st_act.push s) q)))
    (fun (s : σ → Option (Γ k) → σ) => iff.refl (TM2.supports_stmt S (st_run (st_act.peek s) q)))
    fun (s : σ → Option (Γ k) → σ) => iff.refl (TM2.supports_stmt S (st_run (st_act.pop s) q))

/-- The machine states of the TM2 emulator. We can either be in a normal state when waiting for the
next TM2 action, or we can be in the "go" and "return" states to go to the top of the stack and
return to the bottom, respectively. -/
inductive Λ' {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} {Λ : Type u_3} [Inhabited Λ] {σ : Type u_4} [Inhabited σ] 
where
| normal : Λ → Λ'
| go : (k : K) → st_act k → TM2.stmt Γ Λ σ → Λ'
| ret : TM2.stmt Γ Λ σ → Λ'

protected instance Λ'.inhabited {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} {Λ : Type u_3} [Inhabited Λ] {σ : Type u_4} [Inhabited σ] : Inhabited Λ' :=
  { default := Λ'.normal Inhabited.default }

/-- The program corresponding to state transitions at the end of a stack. Here we start out just
after the top of the stack, and should end just after the new top of the stack. -/
def tr_st_act {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} {Λ : Type u_3} [Inhabited Λ] {σ : Type u_4} [Inhabited σ] {k : K} (q : TM1.stmt Γ' Λ' σ) : st_act k → TM1.stmt Γ' Λ' σ :=
  sorry

/-- The initial state for the TM2 emulator, given an initial TM2 state. All stacks start out empty
except for the input stack, and the stack bottom mark is set at the head. -/
def tr_init {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} (k : K) (L : List (Γ k)) : List Γ' :=
  let L' : List Γ' := list.map (fun (a : Γ k) => (false, function.update (fun (_x : K) => none) k ↑a)) (list.reverse L);
  (tt, prod.snd (list.head L')) :: list.tail L'

theorem step_run {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} {Λ : Type u_3} [Inhabited Λ] {σ : Type u_4} [Inhabited σ] {k : K} (q : TM2.stmt Γ Λ σ) (v : σ) (S : (k : K) → List (Γ k)) (s : st_act k) : TM2.step_aux (st_run s q) v S = TM2.step_aux q (st_var v (S k) s) (function.update S k (st_write v (S k) s)) := sorry

/-- The translation of TM2 statements to TM1 statements. regular actions have direct equivalents,
but stack actions are deferred by going to the corresponding `go` state, so that we can find the
appropriate stack top. -/
def tr_normal {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} {Λ : Type u_3} [Inhabited Λ] {σ : Type u_4} [Inhabited σ] : TM2.stmt Γ Λ σ → TM1.stmt Γ' Λ' σ :=
  sorry

theorem tr_normal_run {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} {Λ : Type u_3} [Inhabited Λ] {σ : Type u_4} [Inhabited σ] {k : K} (s : st_act k) (q : TM2.stmt Γ Λ σ) : tr_normal (st_run s q) = TM1.stmt.goto fun (_x : Γ') (_x : σ) => Λ'.go k s q :=
  st_act.cases_on s (fun (s : σ → Γ k) => Eq.refl (tr_normal (st_run (st_act.push s) q)))
    (fun (s : σ → Option (Γ k) → σ) => Eq.refl (tr_normal (st_run (st_act.peek s) q)))
    fun (s : σ → Option (Γ k) → σ) => Eq.refl (tr_normal (st_run (st_act.pop s) q))

/-- The set of machine states accessible from an initial TM2 statement. -/
def tr_stmts₁ {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} {Λ : Type u_3} [Inhabited Λ] {σ : Type u_4} [Inhabited σ] : TM2.stmt Γ Λ σ → finset Λ' :=
  sorry

theorem tr_stmts₁_run {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} {Λ : Type u_3} [Inhabited Λ] {σ : Type u_4} [Inhabited σ] {k : K} {s : st_act k} {q : TM2.stmt Γ Λ σ} : tr_stmts₁ (st_run s q) = insert (Λ'.go k s q) (singleton (Λ'.ret q)) ∪ tr_stmts₁ q := sorry

theorem tr_respects_aux₂ {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} {Λ : Type u_3} [Inhabited Λ] {σ : Type u_4} [Inhabited σ] {k : K} {q : TM1.stmt Γ' Λ' σ} {v : σ} {S : (k : K) → List (Γ k)} {L : list_blank ((k : K) → Option (Γ k))} (hL : ∀ (k : K), list_blank.map (proj k) L = list_blank.mk (list.reverse (list.map some (S k)))) (o : st_act k) : let v' : σ := st_var v (S k) o;
let Sk' : List (Γ k) := st_write v (S k) o;
let S' : (k : K) → List (Γ k) := function.update S k Sk';
∃ (L' : list_blank ((k : K) → Option (Γ k))),
  (∀ (k : K), list_blank.map (proj k) L' = list_blank.mk (list.reverse (list.map some (S' k)))) ∧
    TM1.step_aux (tr_st_act q o) v (nat.iterate (tape.move dir.right) (list.length (S k)) (tape.mk' ∅ (add_bottom L))) =
      TM1.step_aux q v' (nat.iterate (tape.move dir.right) (list.length (S' k)) (tape.mk' ∅ (add_bottom L'))) := sorry

/-- The TM2 emulator machine states written as a TM1 program.
This handles the `go` and `ret` states, which shuttle to and from a stack top. -/
def tr {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} {Λ : Type u_3} [Inhabited Λ] {σ : Type u_4} [Inhabited σ] (M : Λ → TM2.stmt Γ Λ σ) : Λ' → TM1.stmt Γ' Λ' σ :=
  sorry

/-- The relation between TM2 configurations and TM1 configurations of the TM2 emulator. -/
inductive tr_cfg {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} {Λ : Type u_3} [Inhabited Λ] {σ : Type u_4} [Inhabited σ] (M : Λ → TM2.stmt Γ Λ σ) : TM2.cfg Γ Λ σ → TM1.cfg Γ' Λ' σ → Prop
where
| mk : ∀ {q : Option Λ} {v : σ} {S : (k : K) → List (Γ k)} (L : list_blank ((k : K) → Option (Γ k))),
  (∀ (k : K), list_blank.map (proj k) L = list_blank.mk (list.reverse (list.map some (S k)))) →
    tr_cfg M (TM2.cfg.mk q v S) (TM1.cfg.mk (option.map Λ'.normal q) v (tape.mk' ∅ (add_bottom L)))

theorem tr_respects_aux₁ {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} {Λ : Type u_3} [Inhabited Λ] {σ : Type u_4} [Inhabited σ] (M : Λ → TM2.stmt Γ Λ σ) {k : K} (o : st_act k) (q : TM2.stmt Γ Λ σ) (v : σ) {S : List (Γ k)} {L : list_blank ((k : K) → Option (Γ k))} (hL : list_blank.map (proj k) L = list_blank.mk (list.reverse (list.map some S))) (n : ℕ) (H : n ≤ list.length S) : reaches₀ (TM1.step (tr M)) (TM1.cfg.mk (some (Λ'.go k o q)) v (tape.mk' ∅ (add_bottom L)))
  (TM1.cfg.mk (some (Λ'.go k o q)) v (nat.iterate (tape.move dir.right) n (tape.mk' ∅ (add_bottom L)))) := sorry

theorem tr_respects_aux₃ {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} {Λ : Type u_3} [Inhabited Λ] {σ : Type u_4} [Inhabited σ] (M : Λ → TM2.stmt Γ Λ σ) {q : TM2.stmt Γ Λ σ} {v : σ} {L : list_blank ((k : K) → Option (Γ k))} (n : ℕ) : reaches₀ (TM1.step (tr M))
  (TM1.cfg.mk (some (Λ'.ret q)) v (nat.iterate (tape.move dir.right) n (tape.mk' ∅ (add_bottom L))))
  (TM1.cfg.mk (some (Λ'.ret q)) v (tape.mk' ∅ (add_bottom L))) := sorry

theorem tr_respects_aux {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} {Λ : Type u_3} [Inhabited Λ] {σ : Type u_4} [Inhabited σ] (M : Λ → TM2.stmt Γ Λ σ) {q : TM2.stmt Γ Λ σ} {v : σ} {T : list_blank ((i : K) → Option (Γ i))} {k : K} {S : (k : K) → List (Γ k)} (hT : ∀ (k : K), list_blank.map (proj k) T = list_blank.mk (list.reverse (list.map some (S k)))) (o : st_act k) (IH : ∀ {v : σ} {S : (k : K) → List (Γ k)} {T : list_blank ((i : K) → Option (Γ i))},
  (∀ (k : K), list_blank.map (proj k) T = list_blank.mk (list.reverse (list.map some (S k)))) →
    ∃ (b : TM1.cfg Γ' Λ' σ),
      tr_cfg M (TM2.step_aux q v S) b ∧
        reaches (TM1.step (tr M)) (TM1.step_aux (tr_normal q) v (tape.mk' ∅ (add_bottom T))) b) : ∃ (b : TM1.cfg Γ' Λ' σ),
  tr_cfg M (TM2.step_aux (st_run o q) v S) b ∧
    reaches (TM1.step (tr M)) (TM1.step_aux (tr_normal (st_run o q)) v (tape.mk' ∅ (add_bottom T))) b := sorry

theorem tr_respects {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} {Λ : Type u_3} [Inhabited Λ] {σ : Type u_4} [Inhabited σ] (M : Λ → TM2.stmt Γ Λ σ) : respects (TM2.step M) (TM1.step (tr M)) (tr_cfg M) := sorry

theorem tr_cfg_init {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} {Λ : Type u_3} [Inhabited Λ] {σ : Type u_4} [Inhabited σ] (M : Λ → TM2.stmt Γ Λ σ) (k : K) (L : List (Γ k)) : tr_cfg M (TM2.init k L) (TM1.init (tr_init k L)) := sorry

theorem tr_eval_dom {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} {Λ : Type u_3} [Inhabited Λ] {σ : Type u_4} [Inhabited σ] (M : Λ → TM2.stmt Γ Λ σ) (k : K) (L : List (Γ k)) : roption.dom (TM1.eval (tr M) (tr_init k L)) ↔ roption.dom (TM2.eval M k L) :=
  tr_eval_dom (tr_respects M) (tr_cfg_init M k L)

theorem tr_eval {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} {Λ : Type u_3} [Inhabited Λ] {σ : Type u_4} [Inhabited σ] (M : Λ → TM2.stmt Γ Λ σ) (k : K) (L : List (Γ k)) {L₁ : list_blank Γ'} {L₂ : List (Γ k)} (H₁ : L₁ ∈ TM1.eval (tr M) (tr_init k L)) (H₂ : L₂ ∈ TM2.eval M k L) : ∃ (S : (k : K) → List (Γ k)),
  ∃ (L' : list_blank ((k : K) → Option (Γ k))),
    add_bottom L' = L₁ ∧
      (∀ (k : K), list_blank.map (proj k) L' = list_blank.mk (list.reverse (list.map some (S k)))) ∧ S k = L₂ := sorry

/-- The support of a set of TM2 states in the TM2 emulator. -/
def tr_supp {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} {Λ : Type u_3} [Inhabited Λ] {σ : Type u_4} [Inhabited σ] (M : Λ → TM2.stmt Γ Λ σ) (S : finset Λ) : finset Λ' :=
  finset.bUnion S fun (l : Λ) => insert (Λ'.normal l) (tr_stmts₁ (M l))

theorem tr_supports {K : Type u_1} [DecidableEq K] {Γ : K → Type u_2} {Λ : Type u_3} [Inhabited Λ] {σ : Type u_4} [Inhabited σ] (M : Λ → TM2.stmt Γ Λ σ) {S : finset Λ} (ss : TM2.supports M S) : TM1.supports (tr M) (tr_supp M S) := sorry

