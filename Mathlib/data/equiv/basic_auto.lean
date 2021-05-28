/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.set.function
import PostPort

universes u_1 u_2 l u v w u_3 u' v' u_4 u_5 u_6 ua1 ua2 ub1 ub2 ug1 ug2 z 

namespace Mathlib

/-!
# Equivalence between types

In this file we define two types:

* `equiv α β` a.k.a. `α ≃ β`: a bijective map `α → β` bundled with its inverse map; we use this (and
  not equality!) to express that various `Type`s or `Sort`s are equivalent.

* `equiv.perm α`: the group of permutations `α ≃ α`. More lemmas about `equiv.perm` can be found in
  `group_theory/perm`.

Then we define

* canonical isomorphisms between various types: e.g.,

  - `equiv.refl α` is the identity map interpreted as `α ≃ α`;

  - `equiv.sum_equiv_sigma_bool` is the canonical equivalence between the sum of two types `α ⊕ β`
    and the sigma-type `Σ b : bool, cond b α β`;

  - `equiv.prod_sum_distrib : α × (β ⊕ γ) ≃ (α × β) ⊕ (α × γ)` shows that type product and type sum
    satisfy the distributive law up to a canonical equivalence;

* operations on equivalences: e.g.,

  - `equiv.symm e : β ≃ α` is the inverse of `e : α ≃ β`;

  - `equiv.trans e₁ e₂ : α ≃ γ` is the composition of `e₁ : α ≃ β` and `e₂ : β ≃ γ` (note the order
    of the arguments!);

  - `equiv.prod_congr ea eb : α₁ × β₁ ≃ α₂ × β₂`: combine two equivalences `ea : α₁ ≃ α₂` and
    `eb : β₁ ≃ β₂` using `prod.map`.

* definitions that transfer some instances along an equivalence. By convention, we transfer
  instances from right to left.

  - `equiv.inhabited` takes `e : α ≃ β` and `[inhabited β]` and returns `inhabited α`;
  - `equiv.unique` takes `e : α ≃ β` and `[unique β]` and returns `unique α`;
  - `equiv.decidable_eq` takes `e : α ≃ β` and `[decidable_eq β]` and returns `decidable_eq α`.

  More definitions of this kind can be found in other files. E.g., `data/equiv/transfer_instance`
  does it for many algebraic type classes like `group`, `module`, etc.

## Tags

equivalence, congruence, bijective map
-/

/-- `α ≃ β` is the type of functions from `α → β` with a two-sided inverse. -/
structure equiv (α : Sort u_1) (β : Sort u_2) 
where
  to_fun : α → β
  inv_fun : β → α
  left_inv : function.left_inverse inv_fun to_fun
  right_inv : function.right_inverse inv_fun to_fun

infixl:25 " ≃ " => Mathlib.equiv

/-- Convert an involutive function `f` to an equivalence with `to_fun = inv_fun = f`. -/
def function.involutive.to_equiv {α : Sort u} (f : α → α) (h : function.involutive f) : α ≃ α :=
  equiv.mk f f (function.involutive.left_inverse h) (function.involutive.right_inverse h)

namespace equiv


/-- `perm α` is the type of bijections from `α` to itself. -/
def perm (α : Sort u_1)  :=
  α ≃ α

protected instance has_coe_to_fun {α : Sort u} {β : Sort v} : has_coe_to_fun (α ≃ β) :=
  has_coe_to_fun.mk (fun (x : α ≃ β) => α → β) to_fun

@[simp] theorem coe_fn_mk {α : Sort u} {β : Sort v} (f : α → β) (g : β → α) (l : function.left_inverse g f) (r : function.right_inverse g f) : ⇑(mk f g l r) = f :=
  rfl

/-- The map `coe_fn : (r ≃ s) → (r → s)` is injective. -/
theorem injective_coe_fn {α : Sort u} {β : Sort v} : function.injective fun (e : α ≃ β) (x : α) => coe_fn e x := sorry

@[simp] protected theorem coe_inj {α : Sort u} {β : Sort v} {e₁ : α ≃ β} {e₂ : α ≃ β} : ⇑e₁ = ⇑e₂ ↔ e₁ = e₂ :=
  function.injective.eq_iff injective_coe_fn

theorem ext {α : Sort u} {β : Sort v} {f : α ≃ β} {g : α ≃ β} (H : ∀ (x : α), coe_fn f x = coe_fn g x) : f = g :=
  injective_coe_fn (funext H)

protected theorem congr_arg {α : Sort u} {β : Sort v} {f : α ≃ β} {x : α} {x' : α} : x = x' → coe_fn f x = coe_fn f x' := sorry

protected theorem congr_fun {α : Sort u} {β : Sort v} {f : α ≃ β} {g : α ≃ β} (h : f = g) (x : α) : coe_fn f x = coe_fn g x :=
  h ▸ rfl

theorem ext_iff {α : Sort u} {β : Sort v} {f : α ≃ β} {g : α ≃ β} : f = g ↔ ∀ (x : α), coe_fn f x = coe_fn g x :=
  { mp := fun (h : f = g) (x : α) => h ▸ rfl, mpr := ext }

theorem perm.ext {α : Sort u} {σ : perm α} {τ : perm α} (H : ∀ (x : α), coe_fn σ x = coe_fn τ x) : σ = τ :=
  ext H

protected theorem perm.congr_arg {α : Sort u} {f : perm α} {x : α} {x' : α} : x = x' → coe_fn f x = coe_fn f x' :=
  equiv.congr_arg

protected theorem perm.congr_fun {α : Sort u} {f : perm α} {g : perm α} (h : f = g) (x : α) : coe_fn f x = coe_fn g x :=
  equiv.congr_fun h x

theorem perm.ext_iff {α : Sort u} {σ : perm α} {τ : perm α} : σ = τ ↔ ∀ (x : α), coe_fn σ x = coe_fn τ x :=
  ext_iff

/-- Any type is equivalent to itself. -/
protected def refl (α : Sort u_1) : α ≃ α :=
  mk id id sorry sorry

protected instance inhabited' {α : Sort u} : Inhabited (α ≃ α) :=
  { default := equiv.refl α }

/-- Inverse of an equivalence `e : α ≃ β`. -/
protected def symm {α : Sort u} {β : Sort v} (e : α ≃ β) : β ≃ α :=
  mk (inv_fun e) (to_fun e) (right_inv e) (left_inv e)

/-- See Note [custom simps projection] -/
def simps.inv_fun {α : Sort u} {β : Sort v} (e : α ≃ β) : β → α :=
  ⇑(equiv.symm e)

/-- Composition of equivalences `e₁ : α ≃ β` and `e₂ : β ≃ γ`. -/
protected def trans {α : Sort u} {β : Sort v} {γ : Sort w} (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
  mk (⇑e₂ ∘ ⇑e₁) (⇑(equiv.symm e₁) ∘ ⇑(equiv.symm e₂)) sorry sorry

@[simp] theorem to_fun_as_coe {α : Sort u} {β : Sort v} (e : α ≃ β) : to_fun e = ⇑e :=
  rfl

@[simp] theorem inv_fun_as_coe {α : Sort u} {β : Sort v} (e : α ≃ β) : inv_fun e = ⇑(equiv.symm e) :=
  rfl

protected theorem injective {α : Sort u} {β : Sort v} (e : α ≃ β) : function.injective ⇑e :=
  function.left_inverse.injective (left_inv e)

protected theorem surjective {α : Sort u} {β : Sort v} (e : α ≃ β) : function.surjective ⇑e :=
  function.right_inverse.surjective (right_inv e)

protected theorem bijective {α : Sort u} {β : Sort v} (f : α ≃ β) : function.bijective ⇑f :=
  { left := equiv.injective f, right := equiv.surjective f }

@[simp] theorem range_eq_univ {α : Type u_1} {β : Type u_2} (e : α ≃ β) : set.range ⇑e = set.univ :=
  set.eq_univ_of_forall (equiv.surjective e)

protected theorem subsingleton {α : Sort u} {β : Sort v} (e : α ≃ β) [subsingleton β] : subsingleton α :=
  function.injective.subsingleton (equiv.injective e)

protected theorem subsingleton.symm {α : Sort u} {β : Sort v} (e : α ≃ β) [subsingleton α] : subsingleton β :=
  function.injective.subsingleton (equiv.injective (equiv.symm e))

protected instance equiv_subsingleton_cod {α : Sort u} {β : Sort v} [subsingleton β] : subsingleton (α ≃ β) :=
  subsingleton.intro fun (f g : α ≃ β) => ext fun (x : α) => subsingleton.elim (coe_fn f x) (coe_fn g x)

protected instance equiv_subsingleton_dom {α : Sort u} {β : Sort v} [subsingleton α] : subsingleton (α ≃ β) :=
  subsingleton.intro fun (f g : α ≃ β) => ext fun (x : α) => subsingleton.elim (coe_fn f x) (coe_fn g x)

protected instance perm_subsingleton {α : Sort u} [subsingleton α] : subsingleton (perm α) :=
  equiv.equiv_subsingleton_cod

theorem perm.subsingleton_eq_refl {α : Sort u} [subsingleton α] (e : perm α) : e = equiv.refl α :=
  subsingleton.elim e (equiv.refl α)

/-- Transfer `decidable_eq` across an equivalence. -/
protected def decidable_eq {α : Sort u} {β : Sort v} (e : α ≃ β) [DecidableEq β] : DecidableEq α :=
  function.injective.decidable_eq (equiv.injective e)

theorem nonempty_iff_nonempty {α : Sort u} {β : Sort v} (e : α ≃ β) : Nonempty α ↔ Nonempty β :=
  nonempty.congr ⇑e ⇑(equiv.symm e)

/-- If `α ≃ β` and `β` is inhabited, then so is `α`. -/
protected def inhabited {α : Sort u} {β : Sort v} [Inhabited β] (e : α ≃ β) : Inhabited α :=
  { default := coe_fn (equiv.symm e) Inhabited.default }

/-- If `α ≃ β` and `β` is a singleton type, then so is `α`. -/
protected def unique {α : Sort u} {β : Sort v} [unique β] (e : α ≃ β) : unique α :=
  function.surjective.unique sorry

/-- Equivalence between equal types. -/
protected def cast {α : Sort u_1} {β : Sort u_1} (h : α = β) : α ≃ β :=
  mk (cast h) (cast sorry) sorry sorry

@[simp] theorem coe_fn_symm_mk {α : Sort u} {β : Sort v} (f : α → β) (g : β → α) (l : function.left_inverse g f) (r : function.right_inverse g f) : ⇑(equiv.symm (mk f g l r)) = g :=
  rfl

@[simp] theorem coe_refl {α : Sort u} : ⇑(equiv.refl α) = id :=
  rfl

@[simp] theorem perm.coe_subsingleton {α : Type u_1} [subsingleton α] (e : perm α) : ⇑e = id :=
  eq.mpr (id (Eq._oldrec (Eq.refl (⇑e = id)) (perm.subsingleton_eq_refl e)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (⇑(equiv.refl α) = id)) coe_refl)) (Eq.refl id))

theorem refl_apply {α : Sort u} (x : α) : coe_fn (equiv.refl α) x = x :=
  rfl

@[simp] theorem coe_trans {α : Sort u} {β : Sort v} {γ : Sort w} (f : α ≃ β) (g : β ≃ γ) : ⇑(equiv.trans f g) = ⇑g ∘ ⇑f :=
  rfl

theorem trans_apply {α : Sort u} {β : Sort v} {γ : Sort w} (f : α ≃ β) (g : β ≃ γ) (a : α) : coe_fn (equiv.trans f g) a = coe_fn g (coe_fn f a) :=
  rfl

@[simp] theorem apply_symm_apply {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β) : coe_fn e (coe_fn (equiv.symm e) x) = x :=
  right_inv e x

@[simp] theorem symm_apply_apply {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α) : coe_fn (equiv.symm e) (coe_fn e x) = x :=
  left_inv e x

@[simp] theorem symm_comp_self {α : Sort u} {β : Sort v} (e : α ≃ β) : ⇑(equiv.symm e) ∘ ⇑e = id :=
  funext (symm_apply_apply e)

@[simp] theorem self_comp_symm {α : Sort u} {β : Sort v} (e : α ≃ β) : ⇑e ∘ ⇑(equiv.symm e) = id :=
  funext (apply_symm_apply e)

@[simp] theorem symm_trans_apply {α : Sort u} {β : Sort v} {γ : Sort w} (f : α ≃ β) (g : β ≃ γ) (a : γ) : coe_fn (equiv.symm (equiv.trans f g)) a = coe_fn (equiv.symm f) (coe_fn (equiv.symm g) a) :=
  rfl

-- The `simp` attribute is needed to make this a `dsimp` lemma.

-- `simp` will always rewrite with `equiv.symm_symm` before this has a chance to fire.

@[simp] theorem symm_symm_apply {α : Sort u} {β : Sort v} (f : α ≃ β) (b : α) : coe_fn (equiv.symm (equiv.symm f)) b = coe_fn f b :=
  rfl

@[simp] theorem apply_eq_iff_eq {α : Sort u} {β : Sort v} (f : α ≃ β) {x : α} {y : α} : coe_fn f x = coe_fn f y ↔ x = y :=
  function.injective.eq_iff (equiv.injective f)

theorem apply_eq_iff_eq_symm_apply {α : Sort u_1} {β : Sort u_2} (f : α ≃ β) {x : α} {y : β} : coe_fn f x = y ↔ x = coe_fn (equiv.symm f) y := sorry

@[simp] theorem cast_apply {α : Sort u_1} {β : Sort u_1} (h : α = β) (x : α) : coe_fn (equiv.cast h) x = cast h x :=
  rfl

theorem symm_apply_eq {α : Sort u_1} {β : Sort u_2} (e : α ≃ β) {x : β} {y : α} : coe_fn (equiv.symm e) x = y ↔ x = coe_fn e y := sorry

theorem eq_symm_apply {α : Sort u_1} {β : Sort u_2} (e : α ≃ β) {x : β} {y : α} : y = coe_fn (equiv.symm e) x ↔ coe_fn e y = x :=
  iff.trans (iff.trans eq_comm (symm_apply_eq e)) eq_comm

@[simp] theorem symm_symm {α : Sort u} {β : Sort v} (e : α ≃ β) : equiv.symm (equiv.symm e) = e := sorry

@[simp] theorem trans_refl {α : Sort u} {β : Sort v} (e : α ≃ β) : equiv.trans e (equiv.refl β) = e := sorry

@[simp] theorem refl_symm {α : Sort u} : equiv.symm (equiv.refl α) = equiv.refl α :=
  rfl

@[simp] theorem refl_trans {α : Sort u} {β : Sort v} (e : α ≃ β) : equiv.trans (equiv.refl α) e = e := sorry

@[simp] theorem symm_trans {α : Sort u} {β : Sort v} (e : α ≃ β) : equiv.trans (equiv.symm e) e = equiv.refl β := sorry

@[simp] theorem trans_symm {α : Sort u} {β : Sort v} (e : α ≃ β) : equiv.trans e (equiv.symm e) = equiv.refl α := sorry

theorem trans_assoc {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort u_1} (ab : α ≃ β) (bc : β ≃ γ) (cd : γ ≃ δ) : equiv.trans (equiv.trans ab bc) cd = equiv.trans ab (equiv.trans bc cd) :=
  ext fun (a : α) => rfl

theorem left_inverse_symm {α : Sort u} {β : Sort v} (f : α ≃ β) : function.left_inverse ⇑(equiv.symm f) ⇑f :=
  left_inv f

theorem right_inverse_symm {α : Sort u} {β : Sort v} (f : α ≃ β) : function.right_inverse ⇑(equiv.symm f) ⇑f :=
  right_inv f

/-- If `α` is equivalent to `β` and `γ` is equivalent to `δ`, then the type of equivalences `α ≃ γ`
is equivalent to the type of equivalences `β ≃ δ`. -/
def equiv_congr {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort u_1} (ab : α ≃ β) (cd : γ ≃ δ) : α ≃ γ ≃ (β ≃ δ) :=
  mk (fun (ac : α ≃ γ) => equiv.trans (equiv.trans (equiv.symm ab) ac) cd)
    (fun (bd : β ≃ δ) => equiv.trans ab (equiv.trans bd (equiv.symm cd))) sorry sorry

@[simp] theorem equiv_congr_refl {α : Sort u_1} {β : Sort u_2} : equiv_congr (equiv.refl α) (equiv.refl β) = equiv.refl (α ≃ β) :=
  ext fun (x : α ≃ β) => ext fun (x_1 : α) => Eq.refl (coe_fn (coe_fn (equiv_congr (equiv.refl α) (equiv.refl β)) x) x_1)

@[simp] theorem equiv_congr_symm {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort u_1} (ab : α ≃ β) (cd : γ ≃ δ) : equiv.symm (equiv_congr ab cd) = equiv_congr (equiv.symm ab) (equiv.symm cd) :=
  ext fun (x : β ≃ δ) => ext fun (x_1 : α) => Eq.refl (coe_fn (coe_fn (equiv.symm (equiv_congr ab cd)) x) x_1)

@[simp] theorem equiv_congr_trans {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort u_1} {ε : Sort u_2} {ζ : Sort u_3} (ab : α ≃ β) (de : δ ≃ ε) (bc : β ≃ γ) (ef : ε ≃ ζ) : equiv.trans (equiv_congr ab de) (equiv_congr bc ef) = equiv_congr (equiv.trans ab bc) (equiv.trans de ef) :=
  ext
    fun (x : α ≃ δ) =>
      ext fun (x_1 : γ) => Eq.refl (coe_fn (coe_fn (equiv.trans (equiv_congr ab de) (equiv_congr bc ef)) x) x_1)

@[simp] theorem equiv_congr_refl_left {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (bg : β ≃ γ) (e : α ≃ β) : coe_fn (equiv_congr (equiv.refl α) bg) e = equiv.trans e bg :=
  rfl

@[simp] theorem equiv_congr_refl_right {α : Sort u_1} {β : Sort u_2} (ab : α ≃ β) (e : α ≃ β) : coe_fn (equiv_congr ab (equiv.refl β)) e = equiv.trans (equiv.symm ab) e :=
  rfl

@[simp] theorem equiv_congr_apply_apply {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort u_1} (ab : α ≃ β) (cd : γ ≃ δ) (e : α ≃ γ) (x : β) : coe_fn (coe_fn (equiv_congr ab cd) e) x = coe_fn cd (coe_fn e (coe_fn (equiv.symm ab) x)) :=
  rfl

/-- If `α` is equivalent to `β`, then `perm α` is equivalent to `perm β`. -/
def perm_congr {α : Type u_1} {β : Type u_2} (e : α ≃ β) : perm α ≃ perm β :=
  equiv_congr e e

theorem perm_congr_def {α : Type u_1} {β : Type u_2} (e : α ≃ β) (p : perm α) : coe_fn (perm_congr e) p = equiv.trans (equiv.trans (equiv.symm e) p) e :=
  rfl

@[simp] theorem perm_congr_symm {α : Type u_1} {β : Type u_2} (e : α ≃ β) : equiv.symm (perm_congr e) = perm_congr (equiv.symm e) :=
  rfl

@[simp] theorem perm_congr_apply {α : Type u_1} {β : Type u_2} (e : α ≃ β) (p : perm α) (x : β) : coe_fn (coe_fn (perm_congr e) p) x = coe_fn e (coe_fn p (coe_fn (equiv.symm e) x)) :=
  rfl

theorem perm_congr_symm_apply {α : Type u_1} {β : Type u_2} (e : α ≃ β) (p : perm β) (x : α) : coe_fn (coe_fn (equiv.symm (perm_congr e)) p) x = coe_fn (equiv.symm e) (coe_fn p (coe_fn e x)) :=
  rfl

protected theorem image_eq_preimage {α : Type u_1} {β : Type u_2} (e : α ≃ β) (s : set α) : ⇑e '' s = ⇑(equiv.symm e) ⁻¹' s :=
  set.ext fun (x : β) => set.mem_image_iff_of_inverse (left_inv e) (right_inv e)

protected theorem subset_image {α : Type u_1} {β : Type u_2} (e : α ≃ β) (s : set α) (t : set β) : t ⊆ ⇑e '' s ↔ ⇑(equiv.symm e) '' t ⊆ s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (t ⊆ ⇑e '' s ↔ ⇑(equiv.symm e) '' t ⊆ s)) (propext set.image_subset_iff)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (t ⊆ ⇑e '' s ↔ t ⊆ ⇑(equiv.symm e) ⁻¹' s)) (equiv.image_eq_preimage e s)))
      (iff.refl (t ⊆ ⇑(equiv.symm e) ⁻¹' s)))

@[simp] theorem symm_image_image {α : Type u_1} {β : Type u_2} (f : α ≃ β) (s : set α) : ⇑(equiv.symm f) '' (⇑f '' s) = s := sorry

@[simp] theorem image_preimage {α : Type u_1} {β : Type u_2} (e : α ≃ β) (s : set β) : ⇑e '' (⇑e ⁻¹' s) = s :=
  function.surjective.image_preimage (equiv.surjective e) s

@[simp] theorem preimage_image {α : Type u_1} {β : Type u_2} (e : α ≃ β) (s : set α) : ⇑e ⁻¹' (⇑e '' s) = s :=
  set.preimage_image_eq s (equiv.injective e)

protected theorem image_compl {α : Type u_1} {β : Type u_2} (f : α ≃ β) (s : set α) : ⇑f '' (sᶜ) = (⇑f '' sᶜ) :=
  set.image_compl_eq (equiv.bijective f)

/-- If `α` is an empty type, then it is equivalent to the `empty` type. -/
def equiv_empty {α : Sort u} (h : α → False) : α ≃ empty :=
  mk (fun (x : α) => false.elim (h x)) (fun (e : empty) => empty.rec (fun (e : empty) => α) e) sorry sorry

/-- `false` is equivalent to `empty`. -/
def false_equiv_empty : False ≃ empty :=
  equiv_empty id

/-- If `α` is an empty type, then it is equivalent to the `pempty` type in any universe. -/
def equiv_pempty {α : Sort v'} (h : α → False) : α ≃ pempty :=
  mk (fun (x : α) => false.elim (h x)) (fun (e : pempty) => pempty.rec (fun (e : pempty) => α) e) sorry sorry

/-- `false` is equivalent to `pempty`. -/
def false_equiv_pempty : False ≃ pempty :=
  equiv_pempty id

/-- `empty` is equivalent to `pempty`. -/
def empty_equiv_pempty : empty ≃ pempty :=
  equiv_pempty sorry

/-- `pempty` types from any two universes are equivalent. -/
def pempty_equiv_pempty : pempty ≃ pempty :=
  equiv_pempty pempty.elim

/-- If `α` is not `nonempty`, then it is equivalent to `empty`. -/
def empty_of_not_nonempty {α : Sort u_1} (h : ¬Nonempty α) : α ≃ empty :=
  equiv_empty sorry

/-- If `α` is not `nonempty`, then it is equivalent to `pempty`. -/
def pempty_of_not_nonempty {α : Sort u_1} (h : ¬Nonempty α) : α ≃ pempty :=
  equiv_pempty sorry

/-- The `Sort` of proofs of a true proposition is equivalent to `punit`. -/
def prop_equiv_punit {p : Prop} (h : p) : p ≃ PUnit :=
  mk (fun (x : p) => Unit.unit) sorry sorry sorry

/-- `true` is equivalent to `punit`. -/
def true_equiv_punit : True ≃ PUnit :=
  prop_equiv_punit trivial

/-- `ulift α` is equivalent to `α`. -/
@[simp] theorem ulift_symm_apply {α : Type v} : ⇑(equiv.symm equiv.ulift) = ulift.up :=
  Eq.refl ⇑(equiv.symm equiv.ulift)

/-- `plift α` is equivalent to `α`. -/
protected def plift {α : Sort u} : plift α ≃ α :=
  mk plift.down plift.up plift.up_down plift.down_up

/-- equivalence of propositions is the same as iff -/
def of_iff {P : Prop} {Q : Prop} (h : P ↔ Q) : P ≃ Q :=
  mk (iff.mp h) (iff.mpr h) sorry sorry

/-- If `α₁` is equivalent to `α₂` and `β₁` is equivalent to `β₂`, then the type of maps `α₁ → β₁`
is equivalent to the type of maps `α₂ → β₂`. -/
def arrow_congr {α₁ : Sort u_1} {β₁ : Sort u_2} {α₂ : Sort u_3} {β₂ : Sort u_4} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) : (α₁ → β₁) ≃ (α₂ → β₂) :=
  mk (fun (f : α₁ → β₁) => ⇑e₂ ∘ f ∘ ⇑(equiv.symm e₁)) (fun (f : α₂ → β₂) => ⇑(equiv.symm e₂) ∘ f ∘ ⇑e₁) sorry sorry

theorem arrow_congr_comp {α₁ : Sort u_1} {β₁ : Sort u_2} {γ₁ : Sort u_3} {α₂ : Sort u_4} {β₂ : Sort u_5} {γ₂ : Sort u_6} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) (ec : γ₁ ≃ γ₂) (f : α₁ → β₁) (g : β₁ → γ₁) : coe_fn (arrow_congr ea ec) (g ∘ f) = coe_fn (arrow_congr eb ec) g ∘ coe_fn (arrow_congr ea eb) f := sorry

@[simp] theorem arrow_congr_refl {α : Sort u_1} {β : Sort u_2} : arrow_congr (equiv.refl α) (equiv.refl β) = equiv.refl (α → β) :=
  rfl

@[simp] theorem arrow_congr_trans {α₁ : Sort u_1} {β₁ : Sort u_2} {α₂ : Sort u_3} {β₂ : Sort u_4} {α₃ : Sort u_5} {β₃ : Sort u_6} (e₁ : α₁ ≃ α₂) (e₁' : β₁ ≃ β₂) (e₂ : α₂ ≃ α₃) (e₂' : β₂ ≃ β₃) : arrow_congr (equiv.trans e₁ e₂) (equiv.trans e₁' e₂') = equiv.trans (arrow_congr e₁ e₁') (arrow_congr e₂ e₂') :=
  rfl

@[simp] theorem arrow_congr_symm {α₁ : Sort u_1} {β₁ : Sort u_2} {α₂ : Sort u_3} {β₂ : Sort u_4} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) : equiv.symm (arrow_congr e₁ e₂) = arrow_congr (equiv.symm e₁) (equiv.symm e₂) :=
  rfl

/--
A version of `equiv.arrow_congr` in `Type`, rather than `Sort`.

The `equiv_rw` tactic is not able to use the default `Sort` level `equiv.arrow_congr`,
because Lean's universe rules will not unify `?l_1` with `imax (1 ?m_1)`.
-/
def arrow_congr' {α₁ : Type u_1} {β₁ : Type u_2} {α₂ : Type u_3} {β₂ : Type u_4} (hα : α₁ ≃ α₂) (hβ : β₁ ≃ β₂) : (α₁ → β₁) ≃ (α₂ → β₂) :=
  arrow_congr hα hβ

@[simp] theorem arrow_congr'_refl {α : Type u_1} {β : Type u_2} : arrow_congr' (equiv.refl α) (equiv.refl β) = equiv.refl (α → β) :=
  rfl

@[simp] theorem arrow_congr'_trans {α₁ : Type u_1} {β₁ : Type u_2} {α₂ : Type u_3} {β₂ : Type u_4} {α₃ : Type u_5} {β₃ : Type u_6} (e₁ : α₁ ≃ α₂) (e₁' : β₁ ≃ β₂) (e₂ : α₂ ≃ α₃) (e₂' : β₂ ≃ β₃) : arrow_congr' (equiv.trans e₁ e₂) (equiv.trans e₁' e₂') = equiv.trans (arrow_congr' e₁ e₁') (arrow_congr' e₂ e₂') :=
  rfl

@[simp] theorem arrow_congr'_symm {α₁ : Type u_1} {β₁ : Type u_2} {α₂ : Type u_3} {β₂ : Type u_4} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) : equiv.symm (arrow_congr' e₁ e₂) = arrow_congr' (equiv.symm e₁) (equiv.symm e₂) :=
  rfl

/-- Conjugate a map `f : α → α` by an equivalence `α ≃ β`. -/
def conj {α : Sort u} {β : Sort v} (e : α ≃ β) : (α → α) ≃ (β → β) :=
  arrow_congr e e

@[simp] theorem conj_refl {α : Sort u} : conj (equiv.refl α) = equiv.refl (α → α) :=
  rfl

@[simp] theorem conj_symm {α : Sort u} {β : Sort v} (e : α ≃ β) : equiv.symm (conj e) = conj (equiv.symm e) :=
  rfl

@[simp] theorem conj_trans {α : Sort u} {β : Sort v} {γ : Sort w} (e₁ : α ≃ β) (e₂ : β ≃ γ) : conj (equiv.trans e₁ e₂) = equiv.trans (conj e₁) (conj e₂) :=
  rfl

-- This should not be a simp lemma as long as `(∘)` is reducible:

-- when `(∘)` is reducible, Lean can unify `f₁ ∘ f₂` with any `g` using

-- `f₁ := g` and `f₂ := λ x, x`.  This causes nontermination.

theorem conj_comp {α : Sort u} {β : Sort v} (e : α ≃ β) (f₁ : α → α) (f₂ : α → α) : coe_fn (conj e) (f₁ ∘ f₂) = coe_fn (conj e) f₁ ∘ coe_fn (conj e) f₂ :=
  arrow_congr_comp e e e f₂ f₁

theorem semiconj_conj {α₁ : Type u_1} {β₁ : Type u_2} (e : α₁ ≃ β₁) (f : α₁ → α₁) : function.semiconj (⇑e) f (coe_fn (conj e) f) := sorry

theorem semiconj₂_conj {α₁ : Type u_1} {β₁ : Type u_2} (e : α₁ ≃ β₁) (f : α₁ → α₁ → α₁) : function.semiconj₂ (⇑e) f (coe_fn (arrow_congr e (conj e)) f) := sorry

protected instance arrow_congr.is_associative {α₁ : Type u_1} {β₁ : Type u_2} (e : α₁ ≃ β₁) (f : α₁ → α₁ → α₁) [is_associative α₁ f] : is_associative β₁ (coe_fn (arrow_congr e (arrow_congr e e)) f) :=
  function.semiconj₂.is_associative_right (semiconj₂_conj e f) (equiv.surjective e)

protected instance arrow_congr.is_idempotent {α₁ : Type u_1} {β₁ : Type u_2} (e : α₁ ≃ β₁) (f : α₁ → α₁ → α₁) [is_idempotent α₁ f] : is_idempotent β₁ (coe_fn (arrow_congr e (arrow_congr e e)) f) :=
  function.semiconj₂.is_idempotent_right (semiconj₂_conj e f) (equiv.surjective e)

protected instance arrow_congr.is_left_cancel {α₁ : Type u_1} {β₁ : Type u_2} (e : α₁ ≃ β₁) (f : α₁ → α₁ → α₁) [is_left_cancel α₁ f] : is_left_cancel β₁ (coe_fn (arrow_congr e (arrow_congr e e)) f) := sorry

protected instance arrow_congr.is_right_cancel {α₁ : Type u_1} {β₁ : Type u_2} (e : α₁ ≃ β₁) (f : α₁ → α₁ → α₁) [is_right_cancel α₁ f] : is_right_cancel β₁ (coe_fn (arrow_congr e (arrow_congr e e)) f) := sorry

/-- `punit` sorts in any two universes are equivalent. -/
def punit_equiv_punit : PUnit ≃ PUnit :=
  mk (fun (_x : PUnit) => PUnit.unit) (fun (_x : PUnit) => PUnit.unit) sorry sorry

/-- The sort of maps to `punit.{v}` is equivalent to `punit.{w}`. -/
def arrow_punit_equiv_punit (α : Sort u_1) : (α → PUnit) ≃ PUnit :=
  mk (fun (f : α → PUnit) => PUnit.unit) (fun (u : PUnit) (f : α) => PUnit.unit) sorry sorry

/-- The sort of maps from `punit` is equivalent to the codomain. -/
def punit_arrow_equiv (α : Sort u_1) : (PUnit → α) ≃ α :=
  mk (fun (f : PUnit → α) => f PUnit.unit) (fun (a : α) (u : PUnit) => a) sorry sorry

/-- The sort of maps from `true` is equivalent to the codomain. -/
def true_arrow_equiv (α : Sort u_1) : (True → α) ≃ α :=
  mk (fun (f : True → α) => f trivial) (fun (a : α) (u : True) => a) sorry sorry

/-- The sort of maps from `empty` is equivalent to `punit`. -/
def empty_arrow_equiv_punit (α : Sort u_1) : (empty → α) ≃ PUnit :=
  mk (fun (f : empty → α) => PUnit.unit) (fun (u : PUnit) (e : empty) => empty.rec (fun (e : empty) => α) e) sorry sorry

/-- The sort of maps from `pempty` is equivalent to `punit`. -/
def pempty_arrow_equiv_punit (α : Sort u_1) : (pempty → α) ≃ PUnit :=
  mk (fun (f : pempty → α) => PUnit.unit) (fun (u : PUnit) (e : pempty) => pempty.rec (fun (e : pempty) => α) e) sorry
    sorry

/-- The sort of maps from `false` is equivalent to `punit`. -/
def false_arrow_equiv_punit (α : Sort u_1) : (False → α) ≃ PUnit :=
  equiv.trans (arrow_congr false_equiv_empty (equiv.refl α)) (empty_arrow_equiv_punit α)

/-- Product of two equivalences. If `α₁ ≃ α₂` and `β₁ ≃ β₂`, then `α₁ × β₁ ≃ α₂ × β₂`. -/
@[simp] theorem prod_congr_apply {α₁ : Type u_1} {β₁ : Type u_2} {α₂ : Type u_3} {β₂ : Type u_4} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) (x : α₁ × β₁) : coe_fn (prod_congr e₁ e₂) x = prod.map (⇑e₁) (⇑e₂) x :=
  Eq.refl (coe_fn (prod_congr e₁ e₂) x)

@[simp] theorem prod_congr_symm {α₁ : Type u_1} {β₁ : Type u_2} {α₂ : Type u_3} {β₂ : Type u_4} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) : equiv.symm (prod_congr e₁ e₂) = prod_congr (equiv.symm e₁) (equiv.symm e₂) :=
  rfl

/-- Type product is commutative up to an equivalence: `α × β ≃ β × α`. -/
@[simp] theorem prod_comm_apply (α : Type u_1) (β : Type u_2) : ∀ (ᾰ : α × β), coe_fn (prod_comm α β) ᾰ = prod.swap ᾰ :=
  fun (ᾰ : α × β) => Eq.refl (coe_fn (prod_comm α β) ᾰ)

@[simp] theorem prod_comm_symm (α : Type u_1) (β : Type u_2) : equiv.symm (prod_comm α β) = prod_comm β α :=
  rfl

/-- Type product is associative up to an equivalence. -/
@[simp] theorem prod_assoc_apply (α : Type u_1) (β : Type u_2) (γ : Type u_3) (p : (α × β) × γ) : coe_fn (prod_assoc α β γ) p = (prod.fst (prod.fst p), prod.snd (prod.fst p), prod.snd p) :=
  Eq.refl (coe_fn (prod_assoc α β γ) p)

theorem prod_assoc_preimage {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : set α} {t : set β} {u : set γ} : ⇑(prod_assoc α β γ) ⁻¹' set.prod s (set.prod t u) = set.prod (set.prod s t) u := sorry

/-- `punit` is a right identity for type product up to an equivalence. -/
@[simp] theorem prod_punit_apply (α : Type u_1) (p : α × PUnit) : coe_fn (prod_punit α) p = prod.fst p :=
  Eq.refl (coe_fn (prod_punit α) p)

/-- `punit` is a left identity for type product up to an equivalence. -/
@[simp] theorem punit_prod_apply (α : Type u_1) : ∀ (ᾰ : PUnit × α), coe_fn (punit_prod α) ᾰ = prod.snd ᾰ :=
  fun (ᾰ : PUnit × α) => Eq.refl (prod.snd ᾰ)

/-- `empty` type is a right absorbing element for type product up to an equivalence. -/
def prod_empty (α : Type u_1) : α × empty ≃ empty :=
  equiv_empty sorry

/-- `empty` type is a left absorbing element for type product up to an equivalence. -/
def empty_prod (α : Type u_1) : empty × α ≃ empty :=
  equiv_empty sorry

/-- `pempty` type is a right absorbing element for type product up to an equivalence. -/
def prod_pempty (α : Type u_1) : α × pempty ≃ pempty :=
  equiv_pempty sorry

/-- `pempty` type is a left absorbing element for type product up to an equivalence. -/
def pempty_prod (α : Type u_1) : pempty × α ≃ pempty :=
  equiv_pempty sorry

/-- `psum` is equivalent to `sum`. -/
def psum_equiv_sum (α : Type u_1) (β : Type u_2) : psum α β ≃ α ⊕ β :=
  mk (fun (s : psum α β) => psum.cases_on s sum.inl sum.inr) (fun (s : α ⊕ β) => sum.cases_on s psum.inl psum.inr) sorry
    sorry

/-- If `α ≃ α'` and `β ≃ β'`, then `α ⊕ β ≃ α' ⊕ β'`. -/
def sum_congr {α₁ : Type u_1} {β₁ : Type u_2} {α₂ : Type u_3} {β₂ : Type u_4} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) : α₁ ⊕ β₁ ≃ α₂ ⊕ β₂ :=
  mk (sum.map ⇑ea ⇑eb) (sum.map ⇑(equiv.symm ea) ⇑(equiv.symm eb)) sorry sorry

@[simp] theorem sum_congr_trans {α₁ : Type u_1} {α₂ : Type u_2} {β₁ : Type u_3} {β₂ : Type u_4} {γ₁ : Type u_5} {γ₂ : Type u_6} (e : α₁ ≃ β₁) (f : α₂ ≃ β₂) (g : β₁ ≃ γ₁) (h : β₂ ≃ γ₂) : equiv.trans (sum_congr e f) (sum_congr g h) = sum_congr (equiv.trans e g) (equiv.trans f h) := sorry

@[simp] theorem sum_congr_symm {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} (e : α ≃ β) (f : γ ≃ δ) : equiv.symm (sum_congr e f) = sum_congr (equiv.symm e) (equiv.symm f) :=
  rfl

@[simp] theorem sum_congr_refl {α : Type u_1} {β : Type u_2} : sum_congr (equiv.refl α) (equiv.refl β) = equiv.refl (α ⊕ β) := sorry

namespace perm


/-- Combine a permutation of `α` and of `β` into a permutation of `α ⊕ β`. -/
def sum_congr {α : Type u_1} {β : Type u_2} (ea : perm α) (eb : perm β) : perm (α ⊕ β) :=
  sum_congr ea eb

@[simp] theorem sum_congr_apply {α : Type u_1} {β : Type u_2} (ea : perm α) (eb : perm β) (x : α ⊕ β) : coe_fn (sum_congr ea eb) x = sum.map (⇑ea) (⇑eb) x :=
  sum_congr_apply ea eb x

@[simp] theorem sum_congr_trans {α : Type u_1} {β : Type u_2} (e : perm α) (f : perm β) (g : perm α) (h : perm β) : equiv.trans (sum_congr e f) (sum_congr g h) = sum_congr (equiv.trans e g) (equiv.trans f h) :=
  sum_congr_trans e f g h

@[simp] theorem sum_congr_symm {α : Type u_1} {β : Type u_2} (e : perm α) (f : perm β) : equiv.symm (sum_congr e f) = sum_congr (equiv.symm e) (equiv.symm f) :=
  sum_congr_symm e f

@[simp] theorem sum_congr_refl {α : Type u_1} {β : Type u_2} : sum_congr (equiv.refl α) (equiv.refl β) = equiv.refl (α ⊕ β) :=
  sum_congr_refl

end perm


/-- `bool` is equivalent the sum of two `punit`s. -/
def bool_equiv_punit_sum_punit : Bool ≃ PUnit ⊕ PUnit :=
  mk (fun (b : Bool) => cond b (sum.inr PUnit.unit) (sum.inl PUnit.unit))
    (fun (s : PUnit ⊕ PUnit) => sum.rec_on s (fun (_x : PUnit) => false) fun (_x : PUnit) => tt) sorry sorry

/-- `Prop` is noncomputably equivalent to `bool`. -/
def Prop_equiv_bool : Prop ≃ Bool :=
  mk (fun (p : Prop) => to_bool p) (fun (b : Bool) => ↥b) sorry sorry

/-- Sum of types is commutative up to an equivalence. -/
@[simp] theorem sum_comm_apply (α : Type u_1) (β : Type u_2) : ∀ (ᾰ : α ⊕ β), coe_fn (sum_comm α β) ᾰ = sum.swap ᾰ :=
  fun (ᾰ : α ⊕ β) => Eq.refl (coe_fn (sum_comm α β) ᾰ)

@[simp] theorem sum_comm_symm (α : Type u_1) (β : Type u_2) : equiv.symm (sum_comm α β) = sum_comm β α :=
  rfl

/-- Sum of types is associative up to an equivalence. -/
def sum_assoc (α : Type u_1) (β : Type u_2) (γ : Type u_3) : (α ⊕ β) ⊕ γ ≃ α ⊕ β ⊕ γ :=
  mk (sum.elim (sum.elim sum.inl (sum.inr ∘ sum.inl)) (sum.inr ∘ sum.inr))
    (sum.elim (sum.inl ∘ sum.inl) (sum.elim (sum.inl ∘ sum.inr) sum.inr)) sorry sorry

@[simp] theorem sum_assoc_apply_in1 {α : Type u_1} {β : Type u_2} {γ : Type u_3} (a : α) : coe_fn (sum_assoc α β γ) (sum.inl (sum.inl a)) = sum.inl a :=
  rfl

@[simp] theorem sum_assoc_apply_in2 {α : Type u_1} {β : Type u_2} {γ : Type u_3} (b : β) : coe_fn (sum_assoc α β γ) (sum.inl (sum.inr b)) = sum.inr (sum.inl b) :=
  rfl

@[simp] theorem sum_assoc_apply_in3 {α : Type u_1} {β : Type u_2} {γ : Type u_3} (c : γ) : coe_fn (sum_assoc α β γ) (sum.inr c) = sum.inr (sum.inr c) :=
  rfl

/-- Sum with `empty` is equivalent to the original type. -/
def sum_empty (α : Type u_1) : α ⊕ empty ≃ α :=
  mk (sum.elim id (empty.rec fun (n : empty) => α)) sum.inl sorry sorry

@[simp] theorem sum_empty_apply_inl {α : Type u_1} (a : α) : coe_fn (sum_empty α) (sum.inl a) = a :=
  rfl

/-- The sum of `empty` with any `Sort*` is equivalent to the right summand. -/
def empty_sum (α : Type u_1) : empty ⊕ α ≃ α :=
  equiv.trans (sum_comm empty α) (sum_empty α)

@[simp] theorem empty_sum_apply_inr {α : Type u_1} (a : α) : coe_fn (empty_sum α) (sum.inr a) = a :=
  rfl

/-- Sum with `pempty` is equivalent to the original type. -/
def sum_pempty (α : Type u_1) : α ⊕ pempty ≃ α :=
  mk (sum.elim id (pempty.rec fun (n : pempty) => α)) sum.inl sorry sorry

@[simp] theorem sum_pempty_apply_inl {α : Type u_1} (a : α) : coe_fn (sum_pempty α) (sum.inl a) = a :=
  rfl

/-- The sum of `pempty` with any `Sort*` is equivalent to the right summand. -/
def pempty_sum (α : Type u_1) : pempty ⊕ α ≃ α :=
  equiv.trans (sum_comm pempty α) (sum_pempty α)

@[simp] theorem pempty_sum_apply_inr {α : Type u_1} (a : α) : coe_fn (pempty_sum α) (sum.inr a) = a :=
  rfl

/-- `option α` is equivalent to `α ⊕ punit` -/
def option_equiv_sum_punit (α : Type u_1) : Option α ≃ α ⊕ PUnit :=
  mk (fun (o : Option α) => sorry) (fun (s : α ⊕ PUnit) => sorry) sorry sorry

@[simp] theorem option_equiv_sum_punit_none {α : Type u_1} : coe_fn (option_equiv_sum_punit α) none = sum.inr PUnit.unit :=
  rfl

@[simp] theorem option_equiv_sum_punit_some {α : Type u_1} (a : α) : coe_fn (option_equiv_sum_punit α) (some a) = sum.inl a :=
  rfl

@[simp] theorem option_equiv_sum_punit_coe {α : Type u_1} (a : α) : coe_fn (option_equiv_sum_punit α) ↑a = sum.inl a :=
  rfl

@[simp] theorem option_equiv_sum_punit_symm_inl {α : Type u_1} (a : α) : coe_fn (equiv.symm (option_equiv_sum_punit α)) (sum.inl a) = ↑a :=
  rfl

@[simp] theorem option_equiv_sum_punit_symm_inr {α : Type u_1} (a : PUnit) : coe_fn (equiv.symm (option_equiv_sum_punit α)) (sum.inr a) = none :=
  rfl

/-- The set of `x : option α` such that `is_some x` is equivalent to `α`. -/
def option_is_some_equiv (α : Type u_1) : (Subtype fun (x : Option α) => ↥(option.is_some x)) ≃ α :=
  mk (fun (o : Subtype fun (x : Option α) => ↥(option.is_some x)) => option.get sorry)
    (fun (x : α) => { val := some x, property := sorry }) sorry sorry

/-- `α ⊕ β` is equivalent to a `sigma`-type over `bool`. Note that this definition assumes `α` and
`β` to be types from the same universe, so it cannot by used directly to transfer theorems about
sigma types to theorems about sum types. In many cases one can use `ulift` to work around this
difficulty. -/
def sum_equiv_sigma_bool (α : Type u) (β : Type u) : α ⊕ β ≃ sigma fun (b : Bool) => cond b α β :=
  mk (fun (s : α ⊕ β) => sum.elim (fun (x : α) => sigma.mk tt x) (fun (x : β) => sigma.mk false x) s)
    (fun (s : sigma fun (b : Bool) => cond b α β) => sorry) sorry sorry

/-- `sigma_preimage_equiv f` for `f : α → β` is the natural equivalence between
the type of all fibres of `f` and the total space `α`. -/
@[simp] theorem sigma_preimage_equiv_symm_apply_fst {α : Type u_1} {β : Type u_2} (f : α → β) (x : α) : sigma.fst (coe_fn (equiv.symm (sigma_preimage_equiv f)) x) = f x :=
  Eq.refl (sigma.fst (coe_fn (equiv.symm (sigma_preimage_equiv f)) x))

/-- A set `s` in `α × β` is equivalent to the sigma-type `Σ x, {y | (x, y) ∈ s}`. -/
def set_prod_equiv_sigma {α : Type u_1} {β : Type u_2} (s : set (α × β)) : ↥s ≃ sigma fun (x : α) => ↥(set_of fun (y : β) => (x, y) ∈ s) :=
  mk (fun (x : ↥s) => sigma.mk (prod.fst (subtype.val x)) { val := prod.snd (subtype.val x), property := sorry })
    (fun (x : sigma fun (x : α) => ↥(set_of fun (y : β) => (x, y) ∈ s)) =>
      { val := (sigma.fst x, subtype.val (sigma.snd x)), property := sorry })
    sorry sorry

/-- For any predicate `p` on `α`,
the sum of the two subtypes `{a // p a}` and its complement `{a // ¬ p a}`
is naturally equivalent to `α`. -/
def sum_compl {α : Type u_1} (p : α → Prop) [decidable_pred p] : ((Subtype fun (a : α) => p a) ⊕ Subtype fun (a : α) => ¬p a) ≃ α :=
  mk (sum.elim coe coe)
    (fun (a : α) =>
      dite (p a) (fun (h : p a) => sum.inl { val := a, property := h })
        fun (h : ¬p a) => sum.inr { val := a, property := h })
    sorry sorry

@[simp] theorem sum_compl_apply_inl {α : Type u_1} (p : α → Prop) [decidable_pred p] (x : Subtype fun (a : α) => p a) : coe_fn (sum_compl p) (sum.inl x) = ↑x :=
  rfl

@[simp] theorem sum_compl_apply_inr {α : Type u_1} (p : α → Prop) [decidable_pred p] (x : Subtype fun (a : α) => ¬p a) : coe_fn (sum_compl p) (sum.inr x) = ↑x :=
  rfl

@[simp] theorem sum_compl_apply_symm_of_pos {α : Type u_1} (p : α → Prop) [decidable_pred p] (a : α) (h : p a) : coe_fn (equiv.symm (sum_compl p)) a = sum.inl { val := a, property := h } :=
  dif_pos h

@[simp] theorem sum_compl_apply_symm_of_neg {α : Type u_1} (p : α → Prop) [decidable_pred p] (a : α) (h : ¬p a) : coe_fn (equiv.symm (sum_compl p)) a = sum.inr { val := a, property := h } :=
  dif_neg h

/-- For a fixed function `x₀ : {a // p a} → β` defined on a subtype of `α`,
the subtype of functions `x : α → β` that agree with `x₀` on the subtype `{a // p a}`
is naturally equivalent to the type of functions `{a // ¬ p a} → β`. -/
@[simp] theorem subtype_preimage_apply {α : Sort u} {β : Sort v} (p : α → Prop) [decidable_pred p] (x₀ : (Subtype fun (a : α) => p a) → β) (x : Subtype fun (x : α → β) => x ∘ coe = x₀) (a : Subtype fun (a : α) => ¬p a) : coe_fn (subtype_preimage p x₀) x a = coe x ↑a :=
  Eq.refl (coe_fn (subtype_preimage p x₀) x a)

theorem subtype_preimage_symm_apply_coe_pos {α : Sort u} {β : Sort v} (p : α → Prop) [decidable_pred p] (x₀ : (Subtype fun (a : α) => p a) → β) (x : (Subtype fun (a : α) => ¬p a) → β) (a : α) (h : p a) : coe (coe_fn (equiv.symm (subtype_preimage p x₀)) x) a = x₀ { val := a, property := h } :=
  dif_pos h

theorem subtype_preimage_symm_apply_coe_neg {α : Sort u} {β : Sort v} (p : α → Prop) [decidable_pred p] (x₀ : (Subtype fun (a : α) => p a) → β) (x : (Subtype fun (a : α) => ¬p a) → β) (a : α) (h : ¬p a) : coe (coe_fn (equiv.symm (subtype_preimage p x₀)) x) a = x { val := a, property := h } :=
  dif_neg h

/-- If `α` has a unique term, then the type of function `α → β` is equivalent to `β`. -/
@[simp] theorem fun_unique_apply (α : Sort u) (β : Sort v) [unique α] (f : α → β) : coe_fn (fun_unique α β) f = f Inhabited.default :=
  Eq.refl (coe_fn (fun_unique α β) f)

/-- A family of equivalences `Π a, β₁ a ≃ β₂ a` generates an equivalence between `Π a, β₁ a` and
`Π a, β₂ a`. -/
def Pi_congr_right {α : Sort u_1} {β₁ : α → Sort u_2} {β₂ : α → Sort u_3} (F : (a : α) → β₁ a ≃ β₂ a) : ((a : α) → β₁ a) ≃ ((a : α) → β₂ a) :=
  mk (fun (H : (a : α) → β₁ a) (a : α) => coe_fn (F a) (H a))
    (fun (H : (a : α) → β₂ a) (a : α) => coe_fn (equiv.symm (F a)) (H a)) sorry sorry

/-- Dependent `curry` equivalence: the type of dependent functions on `Σ i, β i` is equivalent
to the type of dependent functions of two arguments (i.e., functions to the space of functions). -/
def Pi_curry {α : Type u_1} {β : α → Type u_2} (γ : (a : α) → β a → Sort u_3) : ((x : sigma fun (i : α) => β i) → γ (sigma.fst x) (sigma.snd x)) ≃ ((a : α) → (b : β a) → γ a b) :=
  mk (fun (f : (x : sigma fun (i : α) => β i) → γ (sigma.fst x) (sigma.snd x)) (x : α) (y : β x) => f (sigma.mk x y))
    (fun (f : (a : α) → (b : β a) → γ a b) (x : sigma fun (i : α) => β i) => f (sigma.fst x) (sigma.snd x)) sorry sorry

/-- A `psigma`-type is equivalent to the corresponding `sigma`-type. -/
def psigma_equiv_sigma {α : Type u_1} (β : α → Type u_2) : (psigma fun (i : α) => β i) ≃ sigma fun (i : α) => β i :=
  mk (fun (a : psigma fun (i : α) => β i) => sigma.mk (psigma.fst a) (psigma.snd a))
    (fun (a : sigma fun (i : α) => β i) => psigma.mk (sigma.fst a) (sigma.snd a)) sorry sorry

/-- A family of equivalences `Π a, β₁ a ≃ β₂ a` generates an equivalence between `Σ a, β₁ a` and
`Σ a, β₂ a`. -/
@[simp] theorem sigma_congr_right_apply {α : Type u_1} {β₁ : α → Type u_2} {β₂ : α → Type u_3} (F : (a : α) → β₁ a ≃ β₂ a) (a : sigma fun (a : α) => β₁ a) : coe_fn (sigma_congr_right F) a = sigma.mk (sigma.fst a) (coe_fn (F (sigma.fst a)) (sigma.snd a)) :=
  Eq.refl (coe_fn (sigma_congr_right F) a)

@[simp] theorem sigma_congr_right_trans {α : Type u_1} {β₁ : α → Type u_2} {β₂ : α → Type u_3} {β₃ : α → Type u_4} (F : (a : α) → β₁ a ≃ β₂ a) (G : (a : α) → β₂ a ≃ β₃ a) : equiv.trans (sigma_congr_right F) (sigma_congr_right G) = sigma_congr_right fun (a : α) => equiv.trans (F a) (G a) := sorry

@[simp] theorem sigma_congr_right_symm {α : Type u_1} {β₁ : α → Type u_2} {β₂ : α → Type u_3} (F : (a : α) → β₁ a ≃ β₂ a) : equiv.symm (sigma_congr_right F) = sigma_congr_right fun (a : α) => equiv.symm (F a) := sorry

@[simp] theorem sigma_congr_right_refl {α : Type u_1} {β : α → Type u_2} : (sigma_congr_right fun (a : α) => equiv.refl (β a)) = equiv.refl (sigma fun (a : α) => β a) := sorry

namespace perm


/-- A family of permutations `Π a, perm (β a)` generates a permuation `perm (Σ a, β₁ a)`. -/
def sigma_congr_right {α : Type u_1} {β : α → Type u_2} (F : (a : α) → perm (β a)) : perm (sigma fun (a : α) => β a) :=
  sigma_congr_right F

@[simp] theorem sigma_congr_right_trans {α : Type u_1} {β : α → Type u_2} (F : (a : α) → perm (β a)) (G : (a : α) → perm (β a)) : equiv.trans (sigma_congr_right F) (sigma_congr_right G) = sigma_congr_right fun (a : α) => equiv.trans (F a) (G a) :=
  sigma_congr_right_trans F G

@[simp] theorem sigma_congr_right_symm {α : Type u_1} {β : α → Type u_2} (F : (a : α) → perm (β a)) : equiv.symm (sigma_congr_right F) = sigma_congr_right fun (a : α) => equiv.symm (F a) :=
  sigma_congr_right_symm F

@[simp] theorem sigma_congr_right_refl {α : Type u_1} {β : α → Type u_2} : (sigma_congr_right fun (a : α) => equiv.refl (β a)) = equiv.refl (sigma fun (a : α) => β a) :=
  sigma_congr_right_refl

end perm


/-- An equivalence `f : α₁ ≃ α₂` generates an equivalence between `Σ a, β (f a)` and `Σ a, β a`. -/
def sigma_congr_left {α₁ : Type u_1} {α₂ : Type u_2} {β : α₂ → Type u_3} (e : α₁ ≃ α₂) : (sigma fun (a : α₁) => β (coe_fn e a)) ≃ sigma fun (a : α₂) => β a :=
  mk (fun (a : sigma fun (a : α₁) => β (coe_fn e a)) => sigma.mk (coe_fn e (sigma.fst a)) (sigma.snd a))
    (fun (a : sigma fun (a : α₂) => β a) =>
      sigma.mk (coe_fn (equiv.symm e) (sigma.fst a)) (Eq._oldrec (sigma.snd a) sorry))
    sorry sorry

/-- Transporting a sigma type through an equivalence of the base -/
def sigma_congr_left' {α₁ : Type u_1} {α₂ : Type u_2} {β : α₁ → Type u_3} (f : α₁ ≃ α₂) : (sigma fun (a : α₁) => β a) ≃ sigma fun (a : α₂) => β (coe_fn (equiv.symm f) a) :=
  equiv.symm (sigma_congr_left (equiv.symm f))

/-- Transporting a sigma type through an equivalence of the base and a family of equivalences
of matching fibers -/
def sigma_congr {α₁ : Type u_1} {α₂ : Type u_2} {β₁ : α₁ → Type u_3} {β₂ : α₂ → Type u_4} (f : α₁ ≃ α₂) (F : (a : α₁) → β₁ a ≃ β₂ (coe_fn f a)) : sigma β₁ ≃ sigma β₂ :=
  equiv.trans (sigma_congr_right F) (sigma_congr_left f)

/-- `sigma` type with a constant fiber is equivalent to the product. -/
@[simp] theorem sigma_equiv_prod_symm_apply (α : Type u_1) (β : Type u_2) (a : α × β) : coe_fn (equiv.symm (sigma_equiv_prod α β)) a = sigma.mk (prod.fst a) (prod.snd a) :=
  Eq.refl (coe_fn (equiv.symm (sigma_equiv_prod α β)) a)

/-- If each fiber of a `sigma` type is equivalent to a fixed type, then the sigma type
is equivalent to the product. -/
def sigma_equiv_prod_of_equiv {α : Type u_1} {β : Type u_2} {β₁ : α → Type u_3} (F : (a : α) → β₁ a ≃ β) : sigma β₁ ≃ α × β :=
  equiv.trans (sigma_congr_right F) (sigma_equiv_prod α β)

/-- A family of equivalences `Π (a : α₁), β₁ ≃ β₂` generates an equivalence
between `β₁ × α₁` and `β₂ × α₁`. -/
def prod_congr_left {α₁ : Type u_1} {β₁ : Type u_2} {β₂ : Type u_3} (e : α₁ → β₁ ≃ β₂) : β₁ × α₁ ≃ β₂ × α₁ :=
  mk (fun (ab : β₁ × α₁) => (coe_fn (e (prod.snd ab)) (prod.fst ab), prod.snd ab))
    (fun (ab : β₂ × α₁) => (coe_fn (equiv.symm (e (prod.snd ab))) (prod.fst ab), prod.snd ab)) sorry sorry

@[simp] theorem prod_congr_left_apply {α₁ : Type u_1} {β₁ : Type u_2} {β₂ : Type u_3} (e : α₁ → β₁ ≃ β₂) (b : β₁) (a : α₁) : coe_fn (prod_congr_left e) (b, a) = (coe_fn (e a) b, a) :=
  rfl

theorem prod_congr_refl_right {α₁ : Type u_1} {β₁ : Type u_2} {β₂ : Type u_3} (e : β₁ ≃ β₂) : prod_congr e (equiv.refl α₁) = prod_congr_left fun (_x : α₁) => e := sorry

/-- A family of equivalences `Π (a : α₁), β₁ ≃ β₂` generates an equivalence
between `α₁ × β₁` and `α₁ × β₂`. -/
def prod_congr_right {α₁ : Type u_1} {β₁ : Type u_2} {β₂ : Type u_3} (e : α₁ → β₁ ≃ β₂) : α₁ × β₁ ≃ α₁ × β₂ :=
  mk (fun (ab : α₁ × β₁) => (prod.fst ab, coe_fn (e (prod.fst ab)) (prod.snd ab)))
    (fun (ab : α₁ × β₂) => (prod.fst ab, coe_fn (equiv.symm (e (prod.fst ab))) (prod.snd ab))) sorry sorry

@[simp] theorem prod_congr_right_apply {α₁ : Type u_1} {β₁ : Type u_2} {β₂ : Type u_3} (e : α₁ → β₁ ≃ β₂) (a : α₁) (b : β₁) : coe_fn (prod_congr_right e) (a, b) = (a, coe_fn (e a) b) :=
  rfl

theorem prod_congr_refl_left {α₁ : Type u_1} {β₁ : Type u_2} {β₂ : Type u_3} (e : β₁ ≃ β₂) : prod_congr (equiv.refl α₁) e = prod_congr_right fun (_x : α₁) => e := sorry

@[simp] theorem prod_congr_left_trans_prod_comm {α₁ : Type u_1} {β₁ : Type u_2} {β₂ : Type u_3} (e : α₁ → β₁ ≃ β₂) : equiv.trans (prod_congr_left e) (prod_comm β₂ α₁) = equiv.trans (prod_comm β₁ α₁) (prod_congr_right e) := sorry

@[simp] theorem prod_congr_right_trans_prod_comm {α₁ : Type u_1} {β₁ : Type u_2} {β₂ : Type u_3} (e : α₁ → β₁ ≃ β₂) : equiv.trans (prod_congr_right e) (prod_comm α₁ β₂) = equiv.trans (prod_comm α₁ β₁) (prod_congr_left e) := sorry

theorem sigma_congr_right_sigma_equiv_prod {α₁ : Type u_1} {β₁ : Type u_2} {β₂ : Type u_3} (e : α₁ → β₁ ≃ β₂) : equiv.trans (sigma_congr_right e) (sigma_equiv_prod α₁ β₂) = equiv.trans (sigma_equiv_prod α₁ β₁) (prod_congr_right e) := sorry

theorem sigma_equiv_prod_sigma_congr_right {α₁ : Type u_1} {β₁ : Type u_2} {β₂ : Type u_3} (e : α₁ → β₁ ≃ β₂) : equiv.trans (equiv.symm (sigma_equiv_prod α₁ β₁)) (sigma_congr_right e) =
  equiv.trans (prod_congr_right e) (equiv.symm (sigma_equiv_prod α₁ β₂)) := sorry

/-- A variation on `equiv.prod_congr` where the equivalence in the second component can depend
  on the first component. A typical example is a shear mapping, explaining the name of this
  declaration. -/
@[simp] theorem prod_shear_symm_apply {α₁ : Type u_1} {β₁ : Type u_2} {α₂ : Type u_3} {β₂ : Type u_4} (e₁ : α₁ ≃ α₂) (e₂ : α₁ → β₁ ≃ β₂) : ⇑(equiv.symm (prod_shear e₁ e₂)) =
  fun (y : α₂ × β₂) =>
    (coe_fn (equiv.symm e₁) (prod.fst y), coe_fn (equiv.symm (e₂ (coe_fn (equiv.symm e₁) (prod.fst y)))) (prod.snd y)) :=
  Eq.refl ⇑(equiv.symm (prod_shear e₁ e₂))

namespace perm


/-- `prod_extend_right a e` extends `e : perm β` to `perm (α × β)` by sending `(a, b)` to
`(a, e b)` and keeping the other `(a', b)` fixed. -/
def prod_extend_right {α₁ : Type u_1} {β₁ : Type u_2} [DecidableEq α₁] (a : α₁) (e : perm β₁) : perm (α₁ × β₁) :=
  mk (fun (ab : α₁ × β₁) => ite (prod.fst ab = a) (a, coe_fn e (prod.snd ab)) ab)
    (fun (ab : α₁ × β₁) => ite (prod.fst ab = a) (a, coe_fn (equiv.symm e) (prod.snd ab)) ab) sorry sorry

@[simp] theorem prod_extend_right_apply_eq {α₁ : Type u_1} {β₁ : Type u_2} [DecidableEq α₁] (a : α₁) (e : perm β₁) (b : β₁) : coe_fn (prod_extend_right a e) (a, b) = (a, coe_fn e b) :=
  if_pos rfl

theorem prod_extend_right_apply_ne {α₁ : Type u_1} {β₁ : Type u_2} [DecidableEq α₁] (e : perm β₁) {a : α₁} {a' : α₁} (h : a' ≠ a) (b : β₁) : coe_fn (prod_extend_right a e) (a', b) = (a', b) :=
  if_neg h

theorem eq_of_prod_extend_right_ne {α₁ : Type u_1} {β₁ : Type u_2} [DecidableEq α₁] {e : perm β₁} {a : α₁} {a' : α₁} {b : β₁} (h : coe_fn (prod_extend_right a e) (a', b) ≠ (a', b)) : a' = a := sorry

@[simp] theorem fst_prod_extend_right {α₁ : Type u_1} {β₁ : Type u_2} [DecidableEq α₁] (a : α₁) (e : perm β₁) (ab : α₁ × β₁) : prod.fst (coe_fn (prod_extend_right a e) ab) = prod.fst ab := sorry

end perm


/-- The type of functions to a product `α × β` is equivalent to the type of pairs of functions
`γ → α` and `γ → β`. -/
def arrow_prod_equiv_prod_arrow (α : Type u_1) (β : Type u_2) (γ : Type u_3) : (γ → α × β) ≃ (γ → α) × (γ → β) :=
  mk (fun (f : γ → α × β) => (fun (c : γ) => prod.fst (f c), fun (c : γ) => prod.snd (f c)))
    (fun (p : (γ → α) × (γ → β)) (c : γ) => (prod.fst p c, prod.snd p c)) sorry sorry

/-- Functions `α → β → γ` are equivalent to functions on `α × β`. -/
def arrow_arrow_equiv_prod_arrow (α : Type u_1) (β : Type u_2) (γ : Type u_3) : (α → β → γ) ≃ (α × β → γ) :=
  mk function.uncurry function.curry function.curry_uncurry function.uncurry_curry

/-- The type of functions on a sum type `α ⊕ β` is equivalent to the type of pairs of functions
on `α` and on `β`. -/
def sum_arrow_equiv_prod_arrow (α : Type u_1) (β : Type u_2) (γ : Type u_3) : (α ⊕ β → γ) ≃ (α → γ) × (β → γ) :=
  mk (fun (f : α ⊕ β → γ) => (f ∘ sum.inl, f ∘ sum.inr))
    (fun (p : (α → γ) × (β → γ)) => sum.elim (prod.fst p) (prod.snd p)) sorry sorry

/-- Type product is right distributive with respect to type sum up to an equivalence. -/
def sum_prod_distrib (α : Type u_1) (β : Type u_2) (γ : Type u_3) : (α ⊕ β) × γ ≃ α × γ ⊕ β × γ :=
  mk (fun (p : (α ⊕ β) × γ) => sorry) (fun (s : α × γ ⊕ β × γ) => sorry) sorry sorry

@[simp] theorem sum_prod_distrib_apply_left {α : Type u_1} {β : Type u_2} {γ : Type u_3} (a : α) (c : γ) : coe_fn (sum_prod_distrib α β γ) (sum.inl a, c) = sum.inl (a, c) :=
  rfl

@[simp] theorem sum_prod_distrib_apply_right {α : Type u_1} {β : Type u_2} {γ : Type u_3} (b : β) (c : γ) : coe_fn (sum_prod_distrib α β γ) (sum.inr b, c) = sum.inr (b, c) :=
  rfl

/-- Type product is left distributive with respect to type sum up to an equivalence. -/
def prod_sum_distrib (α : Type u_1) (β : Type u_2) (γ : Type u_3) : α × (β ⊕ γ) ≃ α × β ⊕ α × γ :=
  equiv.trans (equiv.trans (prod_comm α (β ⊕ γ)) (sum_prod_distrib β γ α)) (sum_congr (prod_comm β α) (prod_comm γ α))

@[simp] theorem prod_sum_distrib_apply_left {α : Type u_1} {β : Type u_2} {γ : Type u_3} (a : α) (b : β) : coe_fn (prod_sum_distrib α β γ) (a, sum.inl b) = sum.inl (a, b) :=
  rfl

@[simp] theorem prod_sum_distrib_apply_right {α : Type u_1} {β : Type u_2} {γ : Type u_3} (a : α) (c : γ) : coe_fn (prod_sum_distrib α β γ) (a, sum.inr c) = sum.inr (a, c) :=
  rfl

/-- The product of an indexed sum of types (formally, a `sigma`-type `Σ i, α i`) by a type `β` is
equivalent to the sum of products `Σ i, (α i × β)`. -/
def sigma_prod_distrib {ι : Type u_1} (α : ι → Type u_2) (β : Type u_3) : (sigma fun (i : ι) => α i) × β ≃ sigma fun (i : ι) => α i × β :=
  mk (fun (p : (sigma fun (i : ι) => α i) × β) => sigma.mk (sigma.fst (prod.fst p)) (sigma.snd (prod.fst p), prod.snd p))
    (fun (p : sigma fun (i : ι) => α i × β) => (sigma.mk (sigma.fst p) (prod.fst (sigma.snd p)), prod.snd (sigma.snd p)))
    sorry sorry

/-- The product `bool × α` is equivalent to `α ⊕ α`. -/
def bool_prod_equiv_sum (α : Type u) : Bool × α ≃ α ⊕ α :=
  equiv.trans (equiv.trans (prod_congr bool_equiv_punit_sum_punit (equiv.refl α)) (sum_prod_distrib Unit Unit α))
    (sum_congr (punit_prod α) (punit_prod α))

/-- The function type `bool → α` is equivalent to `α × α`. -/
def bool_to_equiv_prod (α : Type u) : (Bool → α) ≃ α × α :=
  equiv.trans
    (equiv.trans (arrow_congr bool_equiv_punit_sum_punit (equiv.refl α)) (sum_arrow_equiv_prod_arrow Unit Unit α))
    (prod_congr (punit_arrow_equiv α) (punit_arrow_equiv α))

@[simp] theorem bool_to_equiv_prod_apply {α : Type u} (f : Bool → α) : coe_fn (bool_to_equiv_prod α) f = (f false, f tt) :=
  rfl

@[simp] theorem bool_to_equiv_prod_symm_apply_ff {α : Type u} (p : α × α) : coe_fn (equiv.symm (bool_to_equiv_prod α)) p false = prod.fst p :=
  rfl

@[simp] theorem bool_to_equiv_prod_symm_apply_tt {α : Type u} (p : α × α) : coe_fn (equiv.symm (bool_to_equiv_prod α)) p tt = prod.snd p :=
  rfl

/-- The set of natural numbers is equivalent to `ℕ ⊕ punit`. -/
def nat_equiv_nat_sum_punit : ℕ ≃ ℕ ⊕ PUnit :=
  mk (fun (n : ℕ) => sorry) (fun (s : ℕ ⊕ PUnit) => sorry) sorry sorry

/-- `ℕ ⊕ punit` is equivalent to `ℕ`. -/
def nat_sum_punit_equiv_nat : ℕ ⊕ PUnit ≃ ℕ :=
  equiv.symm nat_equiv_nat_sum_punit

/-- The type of integer numbers is equivalent to `ℕ ⊕ ℕ`. -/
def int_equiv_nat_sum_nat : ℤ ≃ ℕ ⊕ ℕ :=
  mk (fun (z : ℤ) => int.cases_on z (fun (z : ℕ) => sum.inl z) fun (z : ℕ) => sum.inr z)
    (fun (z : ℕ ⊕ ℕ) => sum.cases_on z (fun (z : ℕ) => Int.ofNat z) fun (z : ℕ) => Int.negSucc z) sorry sorry

/-- An equivalence between `α` and `β` generates an equivalence between `list α` and `list β`. -/
def list_equiv_of_equiv {α : Type u_1} {β : Type u_2} (e : α ≃ β) : List α ≃ List β :=
  mk (list.map ⇑e) (list.map ⇑(equiv.symm e)) sorry sorry

/-- `fin n` is equivalent to `{m // m < n}`. -/
def fin_equiv_subtype (n : ℕ) : fin n ≃ Subtype fun (m : ℕ) => m < n :=
  mk (fun (x : fin n) => { val := subtype.val x, property := sorry })
    (fun (x : Subtype fun (m : ℕ) => m < n) => { val := subtype.val x, property := sorry }) sorry sorry

/-- If `α` is equivalent to `β`, then `unique α` is equivalent to `β`. -/
def unique_congr {α : Sort u} {β : Sort v} (e : α ≃ β) : unique α ≃ unique β :=
  mk (fun (h : unique α) => equiv.unique (equiv.symm e)) (fun (h : unique β) => equiv.unique e) sorry sorry

/-- If `α` is equivalent to `β` and the predicates `p : α → Prop` and `q : β → Prop` are equivalent
at corresponding points, then `{a // p a}` is equivalent to `{b // q b}`. -/
def subtype_congr {α : Sort u} {β : Sort v} {p : α → Prop} {q : β → Prop} (e : α ≃ β) (h : ∀ (a : α), p a ↔ q (coe_fn e a)) : (Subtype fun (a : α) => p a) ≃ Subtype fun (b : β) => q b :=
  mk (fun (x : Subtype fun (a : α) => p a) => { val := coe_fn e ↑x, property := sorry })
    (fun (y : Subtype fun (b : β) => q b) => { val := coe_fn (equiv.symm e) ↑y, property := sorry }) sorry sorry

@[simp] theorem subtype_congr_apply {α : Sort u} {β : Sort v} {p : α → Prop} {q : β → Prop} (e : α ≃ β) (h : ∀ (a : α), p a ↔ q (coe_fn e a)) (x : Subtype fun (x : α) => p x) : coe_fn (subtype_congr e h) x = { val := coe_fn e ↑x, property := iff.mp (h ↑x) (subtype.property x) } :=
  rfl

@[simp] theorem subtype_congr_symm_apply {α : Sort u} {β : Sort v} {p : α → Prop} {q : β → Prop} (e : α ≃ β) (h : ∀ (a : α), p a ↔ q (coe_fn e a)) (y : Subtype fun (y : β) => q y) : coe_fn (equiv.symm (subtype_congr e h)) y =
  { val := coe_fn (equiv.symm e) ↑y,
    property := iff.mpr (h (coe_fn (equiv.symm e) ↑y)) (Eq.symm (apply_symm_apply e ↑y) ▸ subtype.property y) } :=
  rfl

/-- If two predicates `p` and `q` are pointwise equivalent, then `{x // p x}` is equivalent to
`{x // q x}`. -/
def subtype_congr_right {α : Sort u} {p : α → Prop} {q : α → Prop} (e : ∀ (x : α), p x ↔ q x) : (Subtype fun (x : α) => p x) ≃ Subtype fun (x : α) => q x :=
  subtype_congr (equiv.refl α) e

/-- If `α ≃ β`, then for any predicate `p : β → Prop` the subtype `{a // p (e a)}` is equivalent
to the subtype `{b // p b}`. -/
def subtype_equiv_of_subtype {α : Sort u} {β : Sort v} {p : β → Prop} (e : α ≃ β) : (Subtype fun (a : α) => p (coe_fn e a)) ≃ Subtype fun (b : β) => p b :=
  subtype_congr e sorry

/-- If `α ≃ β`, then for any predicate `p : α → Prop` the subtype `{a // p a}` is equivalent
to the subtype `{b // p (e.symm b)}`. This version is used by `equiv_rw`. -/
def subtype_equiv_of_subtype' {α : Sort u} {β : Sort v} {p : α → Prop} (e : α ≃ β) : (Subtype fun (a : α) => p a) ≃ Subtype fun (b : β) => p (coe_fn (equiv.symm e) b) :=
  equiv.symm (subtype_equiv_of_subtype (equiv.symm e))

/-- If two predicates are equal, then the corresponding subtypes are equivalent. -/
def subtype_congr_prop {α : Type u_1} {p : α → Prop} {q : α → Prop} (h : p = q) : Subtype p ≃ Subtype q :=
  subtype_congr (equiv.refl α) sorry

/-- The subtypes corresponding to equal sets are equivalent. -/
def set_congr {α : Type u_1} {s : set α} {t : set α} (h : s = t) : ↥s ≃ ↥t :=
  subtype_congr_prop h

/-- A subtype of a subtype is equivalent to the subtype of elements satisfying both predicates. This
version allows the “inner” predicate to depend on `h : p a`. -/
def subtype_subtype_equiv_subtype_exists {α : Type u} (p : α → Prop) (q : Subtype p → Prop) : Subtype q ≃ Subtype fun (a : α) => ∃ (h : p a), q { val := a, property := h } :=
  mk (fun (_x : Subtype q) => sorry)
    (fun (_x : Subtype fun (a : α) => ∃ (h : p a), q { val := a, property := h }) => sorry) sorry sorry

/-- A subtype of a subtype is equivalent to the subtype of elements satisfying both predicates. -/
def subtype_subtype_equiv_subtype_inter {α : Type u} (p : α → Prop) (q : α → Prop) : (Subtype fun (x : Subtype p) => q (subtype.val x)) ≃ Subtype fun (x : α) => p x ∧ q x :=
  equiv.trans (subtype_subtype_equiv_subtype_exists p fun (x : Subtype p) => q (subtype.val x))
    (subtype_congr_right sorry)

/-- If the outer subtype has more restrictive predicate than the inner one,
then we can drop the latter. -/
def subtype_subtype_equiv_subtype {α : Type u} {p : α → Prop} {q : α → Prop} (h : ∀ {x : α}, q x → p x) : (Subtype fun (x : Subtype p) => q (subtype.val x)) ≃ Subtype q :=
  equiv.trans (subtype_subtype_equiv_subtype_inter p q) (subtype_congr_right sorry)

/-- If a proposition holds for all elements, then the subtype is
equivalent to the original type. -/
def subtype_univ_equiv {α : Type u} {p : α → Prop} (h : ∀ (x : α), p x) : Subtype p ≃ α :=
  mk (fun (x : Subtype p) => ↑x) (fun (x : α) => { val := x, property := h x }) sorry sorry

/-- A subtype of a sigma-type is a sigma-type over a subtype. -/
def subtype_sigma_equiv {α : Type u} (p : α → Type v) (q : α → Prop) : (Subtype fun (y : sigma p) => q (sigma.fst y)) ≃ sigma fun (x : Subtype q) => p (subtype.val x) :=
  mk
    (fun (x : Subtype fun (y : sigma p) => q (sigma.fst y)) =>
      sigma.mk { val := sigma.fst (subtype.val x), property := sorry } (sigma.snd (subtype.val x)))
    (fun (x : sigma fun (x : Subtype q) => p (subtype.val x)) =>
      { val := sigma.mk (subtype.val (sigma.fst x)) (sigma.snd x), property := sorry })
    sorry sorry

/-- A sigma type over a subtype is equivalent to the sigma set over the original type,
if the fiber is empty outside of the subset -/
def sigma_subtype_equiv_of_subset {α : Type u} (p : α → Type v) (q : α → Prop) (h : ∀ (x : α), p x → q x) : (sigma fun (x : Subtype q) => p ↑x) ≃ sigma fun (x : α) => p x :=
  equiv.trans (equiv.symm (subtype_sigma_equiv p q)) (subtype_univ_equiv sorry)

/-- If a predicate `p : β → Prop` is true on the range of a map `f : α → β`, then
`Σ y : {y // p y}, {x // f x = y}` is equivalent to `α`. -/
def sigma_subtype_preimage_equiv {α : Type u} {β : Type v} (f : α → β) (p : β → Prop) (h : ∀ (x : α), p (f x)) : (sigma fun (y : Subtype p) => Subtype fun (x : α) => f x = ↑y) ≃ α :=
  equiv.trans (sigma_subtype_equiv_of_subset (fun (y : β) => Subtype fun (x : α) => f x = y) p sorry)
    (sigma_preimage_equiv f)

/-- If for each `x` we have `p x ↔ q (f x)`, then `Σ y : {y // q y}, f ⁻¹' {y}` is equivalent
to `{x // p x}`. -/
def sigma_subtype_preimage_equiv_subtype {α : Type u} {β : Type v} (f : α → β) {p : α → Prop} {q : β → Prop} (h : ∀ (x : α), p x ↔ q (f x)) : (sigma fun (y : Subtype q) => Subtype fun (x : α) => f x = ↑y) ≃ Subtype p :=
  equiv.trans
    (sigma_congr_right
      fun (y : Subtype q) =>
        equiv.symm
          (equiv.trans
            (subtype_subtype_equiv_subtype_exists p fun (x : Subtype p) => { val := f ↑x, property := sorry } = y)
            (subtype_congr_right sorry)))
    (sigma_preimage_equiv fun (x : Subtype p) => { val := f ↑x, property := sorry })

/-- The `pi`-type `Π i, π i` is equivalent to the type of sections `f : ι → Σ i, π i` of the
`sigma` type such that for all `i` we have `(f i).fst = i`. -/
def pi_equiv_subtype_sigma (ι : Type u_1) (π : ι → Type u_2) : ((i : ι) → π i) ≃ ↥(set_of fun (f : ι → sigma fun (i : ι) => π i) => ∀ (i : ι), sigma.fst (f i) = i) :=
  mk (fun (f : (i : ι) → π i) => { val := fun (i : ι) => sigma.mk i (f i), property := sorry })
    (fun (f : ↥(set_of fun (f : ι → sigma fun (i : ι) => π i) => ∀ (i : ι), sigma.fst (f i) = i)) (i : ι) =>
      eq.mpr sorry (sigma.snd (subtype.val f i)))
    sorry sorry

/-- The set of functions `f : Π a, β a` such that for all `a` we have `p a (f a)` is equivalent
to the set of functions `Π a, {b : β a // p a b}`. -/
def subtype_pi_equiv_pi {α : Sort u} {β : α → Sort v} {p : (a : α) → β a → Prop} : (Subtype fun (f : (a : α) → β a) => ∀ (a : α), p a (f a)) ≃ ((a : α) → Subtype fun (b : β a) => p a b) :=
  mk
    (fun (f : Subtype fun (f : (a : α) → β a) => ∀ (a : α), p a (f a)) (a : α) =>
      { val := subtype.val f a, property := sorry })
    (fun (f : (a : α) → Subtype fun (b : β a) => p a b) => { val := fun (a : α) => subtype.val (f a), property := sorry })
    sorry sorry

/-- A subtype of a product defined by componentwise conditions
is equivalent to a product of subtypes. -/
def subtype_prod_equiv_prod {α : Type u} {β : Type v} {p : α → Prop} {q : β → Prop} : (Subtype fun (c : α × β) => p (prod.fst c) ∧ q (prod.snd c)) ≃ (Subtype fun (a : α) => p a) × Subtype fun (b : β) => q b :=
  mk
    (fun (x : Subtype fun (c : α × β) => p (prod.fst c) ∧ q (prod.snd c)) =>
      ({ val := prod.fst (subtype.val x), property := sorry }, { val := prod.snd (subtype.val x), property := sorry }))
    (fun (x : (Subtype fun (a : α) => p a) × Subtype fun (b : β) => q b) =>
      { val := (subtype.val (prod.fst x), subtype.val (prod.snd x)), property := sorry })
    sorry sorry

/-- The type of all functions `X → Y` with prescribed values for all `x' ≠ x`
is equivalent to the codomain `Y`. -/
def subtype_equiv_codomain {X : Type u_1} {Y : Type u_2} [DecidableEq X] {x : X} (f : (Subtype fun (x' : X) => x' ≠ x) → Y) : (Subtype fun (g : X → Y) => g ∘ coe = f) ≃ Y :=
  equiv.trans (subtype_preimage (fun (x' : X) => x' ≠ x) f) (fun_unique (Subtype fun (a : X) => ¬a ≠ x) Y)

@[simp] theorem coe_subtype_equiv_codomain {X : Type u_1} {Y : Type u_2} [DecidableEq X] {x : X} (f : (Subtype fun (x' : X) => x' ≠ x) → Y) : ⇑(subtype_equiv_codomain f) = fun (g : Subtype fun (g : X → Y) => g ∘ coe = f) => coe g x :=
  rfl

@[simp] theorem subtype_equiv_codomain_apply {X : Type u_1} {Y : Type u_2} [DecidableEq X] {x : X} (f : (Subtype fun (x' : X) => x' ≠ x) → Y) (g : Subtype fun (g : X → Y) => g ∘ coe = f) : coe_fn (subtype_equiv_codomain f) g = coe g x :=
  rfl

theorem coe_subtype_equiv_codomain_symm {X : Type u_1} {Y : Type u_2} [DecidableEq X] {x : X} (f : (Subtype fun (x' : X) => x' ≠ x) → Y) : ⇑(equiv.symm (subtype_equiv_codomain f)) =
  fun (y : Y) =>
    { val := fun (x' : X) => dite (x' ≠ x) (fun (h : x' ≠ x) => f { val := x', property := h }) fun (h : ¬x' ≠ x) => y,
      property :=
        funext
          fun (x' : Subtype fun (x' : X) => x' ≠ x) =>
            id
              (eq.mpr
                (id
                  (Eq._oldrec
                    (Eq.refl
                      ((dite (¬↑x' = x) (fun (h : ¬↑x' = x) => f { val := ↑x', property := h })
                          fun (h : ¬¬↑x' = x) => y) =
                        f x'))
                    (dif_pos (subtype.property x'))))
                (eq.mpr
                  (id
                    (Eq._oldrec (Eq.refl (f { val := ↑x', property := subtype.property x' } = f x'))
                      (subtype.coe_eta x' (subtype.property x'))))
                  (Eq.refl (f x')))) } :=
  rfl

@[simp] theorem subtype_equiv_codomain_symm_apply {X : Type u_1} {Y : Type u_2} [DecidableEq X] {x : X} (f : (Subtype fun (x' : X) => x' ≠ x) → Y) (y : Y) (x' : X) : coe (coe_fn (equiv.symm (subtype_equiv_codomain f)) y) x' =
  dite (x' ≠ x) (fun (h : x' ≠ x) => f { val := x', property := h }) fun (h : ¬x' ≠ x) => y :=
  rfl

@[simp] theorem subtype_equiv_codomain_symm_apply_eq {X : Type u_1} {Y : Type u_2} [DecidableEq X] {x : X} (f : (Subtype fun (x' : X) => x' ≠ x) → Y) (y : Y) : coe (coe_fn (equiv.symm (subtype_equiv_codomain f)) y) x = y :=
  dif_neg (iff.mpr not_not rfl)

theorem subtype_equiv_codomain_symm_apply_ne {X : Type u_1} {Y : Type u_2} [DecidableEq X] {x : X} (f : (Subtype fun (x' : X) => x' ≠ x) → Y) (y : Y) (x' : X) (h : x' ≠ x) : coe (coe_fn (equiv.symm (subtype_equiv_codomain f)) y) x' = f { val := x', property := h } :=
  dif_pos h

namespace set


/-- `univ α` is equivalent to `α`. -/
@[simp] theorem univ_symm_apply (α : Type u_1) (a : α) : coe_fn (equiv.symm (set.univ α)) a = { val := a, property := trivial } :=
  Eq.refl (coe_fn (equiv.symm (set.univ α)) a)

/-- An empty set is equivalent to the `empty` type. -/
protected def empty (α : Type u_1) : ↥∅ ≃ empty :=
  equiv_empty sorry

/-- An empty set is equivalent to a `pempty` type. -/
protected def pempty (α : Type u_1) : ↥∅ ≃ pempty :=
  equiv_pempty sorry

/-- If sets `s` and `t` are separated by a decidable predicate, then `s ∪ t` is equivalent to
`s ⊕ t`. -/
protected def union' {α : Type u_1} {s : set α} {t : set α} (p : α → Prop) [decidable_pred p] (hs : ∀ (x : α), x ∈ s → p x) (ht : ∀ (x : α), x ∈ t → ¬p x) : ↥(s ∪ t) ≃ ↥s ⊕ ↥t :=
  mk
    (fun (x : ↥(s ∪ t)) =>
      dite (p ↑x) (fun (hp : p ↑x) => sum.inl { val := subtype.val x, property := sorry })
        fun (hp : ¬p ↑x) => sum.inr { val := subtype.val x, property := sorry })
    (fun (o : ↥s ⊕ ↥t) => sorry) sorry sorry

/-- If sets `s` and `t` are disjoint, then `s ∪ t` is equivalent to `s ⊕ t`. -/
protected def union {α : Type u_1} {s : set α} {t : set α} [decidable_pred fun (x : α) => x ∈ s] (H : s ∩ t ⊆ ∅) : ↥(s ∪ t) ≃ ↥s ⊕ ↥t :=
  set.union' (fun (x : α) => x ∈ s) sorry sorry

theorem union_apply_left {α : Type u_1} {s : set α} {t : set α} [decidable_pred fun (x : α) => x ∈ s] (H : s ∩ t ⊆ ∅) {a : ↥(s ∪ t)} (ha : ↑a ∈ s) : coe_fn (set.union H) a = sum.inl { val := ↑a, property := ha } :=
  dif_pos ha

theorem union_apply_right {α : Type u_1} {s : set α} {t : set α} [decidable_pred fun (x : α) => x ∈ s] (H : s ∩ t ⊆ ∅) {a : ↥(s ∪ t)} (ha : ↑a ∈ t) : coe_fn (set.union H) a = sum.inr { val := ↑a, property := ha } :=
  dif_neg fun (h : ↑a ∈ s) => H { left := h, right := ha }

@[simp] theorem union_symm_apply_left {α : Type u_1} {s : set α} {t : set α} [decidable_pred fun (x : α) => x ∈ s] (H : s ∩ t ⊆ ∅) (a : ↥s) : coe_fn (equiv.symm (set.union H)) (sum.inl a) =
  { val := ↑a, property := set.subset_union_left s t (subtype.property a) } :=
  rfl

@[simp] theorem union_symm_apply_right {α : Type u_1} {s : set α} {t : set α} [decidable_pred fun (x : α) => x ∈ s] (H : s ∩ t ⊆ ∅) (a : ↥t) : coe_fn (equiv.symm (set.union H)) (sum.inr a) =
  { val := ↑a, property := set.subset_union_right s t (subtype.property a) } :=
  rfl

-- TODO: Any reason to use the same universe?

/-- A singleton set is equivalent to a `punit` type. -/
protected def singleton {α : Type u_1} (a : α) : ↥(singleton a) ≃ PUnit :=
  mk (fun (_x : ↥(singleton a)) => PUnit.unit) (fun (_x : PUnit) => { val := a, property := set.mem_singleton a }) sorry
    sorry

/-- Equal sets are equivalent. -/
@[simp] theorem of_eq_symm_apply {α : Type u} {s : set α} {t : set α} (h : s = t) (x : ↥t) : coe_fn (equiv.symm (set.of_eq h)) x = { val := ↑x, property := of_eq._proof_2 h x } :=
  Eq.refl (coe_fn (equiv.symm (set.of_eq h)) x)

/-- If `a ∉ s`, then `insert a s` is equivalent to `s ⊕ punit`. -/
protected def insert {α : Type u} {s : set α} [decidable_pred s] {a : α} (H : ¬a ∈ s) : ↥(insert a s) ≃ ↥s ⊕ PUnit :=
  equiv.trans (equiv.trans (set.of_eq sorry) (set.union sorry)) (sum_congr (equiv.refl ↥s) (set.singleton a))

@[simp] theorem insert_symm_apply_inl {α : Type u} {s : set α} [decidable_pred s] {a : α} (H : ¬a ∈ s) (b : ↥s) : coe_fn (equiv.symm (set.insert H)) (sum.inl b) = { val := ↑b, property := Or.inr (subtype.property b) } :=
  rfl

@[simp] theorem insert_symm_apply_inr {α : Type u} {s : set α} [decidable_pred s] {a : α} (H : ¬a ∈ s) (b : PUnit) : coe_fn (equiv.symm (set.insert H)) (sum.inr b) = { val := a, property := Or.inl rfl } :=
  rfl

@[simp] theorem insert_apply_left {α : Type u} {s : set α} [decidable_pred s] {a : α} (H : ¬a ∈ s) : coe_fn (set.insert H) { val := a, property := Or.inl rfl } = sum.inr PUnit.unit :=
  iff.mpr (apply_eq_iff_eq_symm_apply (set.insert H)) rfl

@[simp] theorem insert_apply_right {α : Type u} {s : set α} [decidable_pred s] {a : α} (H : ¬a ∈ s) (b : ↥s) : coe_fn (set.insert H) { val := ↑b, property := Or.inr (subtype.property b) } = sum.inl b :=
  iff.mpr (apply_eq_iff_eq_symm_apply (set.insert H)) rfl

/-- If `s : set α` is a set with decidable membership, then `s ⊕ sᶜ` is equivalent to `α`. -/
protected def sum_compl {α : Type u_1} (s : set α) [decidable_pred s] : ↥s ⊕ ↥(sᶜ) ≃ α :=
  equiv.trans (equiv.trans (equiv.symm (set.union sorry)) (set.of_eq sorry)) (set.univ α)

@[simp] theorem sum_compl_apply_inl {α : Type u} (s : set α) [decidable_pred s] (x : ↥s) : coe_fn (set.sum_compl s) (sum.inl x) = ↑x :=
  rfl

@[simp] theorem sum_compl_apply_inr {α : Type u} (s : set α) [decidable_pred s] (x : ↥(sᶜ)) : coe_fn (set.sum_compl s) (sum.inr x) = ↑x :=
  rfl

theorem sum_compl_symm_apply_of_mem {α : Type u} {s : set α} [decidable_pred s] {x : α} (hx : x ∈ s) : coe_fn (equiv.symm (set.sum_compl s)) x = sum.inl { val := x, property := hx } := sorry

theorem sum_compl_symm_apply_of_not_mem {α : Type u} {s : set α} [decidable_pred s] {x : α} (hx : ¬x ∈ s) : coe_fn (equiv.symm (set.sum_compl s)) x = sum.inr { val := x, property := hx } := sorry

@[simp] theorem sum_compl_symm_apply {α : Type u_1} {s : set α} [decidable_pred s] {x : ↥s} : coe_fn (equiv.symm (set.sum_compl s)) ↑x = sum.inl x :=
  subtype.cases_on x fun (x : α) (hx : x ∈ s) => sum_compl_symm_apply_of_mem hx

@[simp] theorem sum_compl_symm_apply_compl {α : Type u_1} {s : set α} [decidable_pred s] {x : ↥(sᶜ)} : coe_fn (equiv.symm (set.sum_compl s)) ↑x = sum.inr x :=
  subtype.cases_on x fun (x : α) (hx : x ∈ (sᶜ)) => sum_compl_symm_apply_of_not_mem hx

/-- `sum_diff_subset s t` is the natural equivalence between
`s ⊕ (t \ s)` and `t`, where `s` and `t` are two sets. -/
protected def sum_diff_subset {α : Type u_1} {s : set α} {t : set α} (h : s ⊆ t) [decidable_pred s] : ↥s ⊕ ↥(t \ s) ≃ ↥t :=
  equiv.trans (equiv.symm (set.union sorry)) (set.of_eq sorry)

@[simp] theorem sum_diff_subset_apply_inl {α : Type u_1} {s : set α} {t : set α} (h : s ⊆ t) [decidable_pred s] (x : ↥s) : coe_fn (set.sum_diff_subset h) (sum.inl x) = set.inclusion h x :=
  rfl

@[simp] theorem sum_diff_subset_apply_inr {α : Type u_1} {s : set α} {t : set α} (h : s ⊆ t) [decidable_pred s] (x : ↥(t \ s)) : coe_fn (set.sum_diff_subset h) (sum.inr x) = set.inclusion (set.diff_subset t s) x :=
  rfl

theorem sum_diff_subset_symm_apply_of_mem {α : Type u_1} {s : set α} {t : set α} (h : s ⊆ t) [decidable_pred s] {x : ↥t} (hx : subtype.val x ∈ s) : coe_fn (equiv.symm (set.sum_diff_subset h)) x = sum.inl { val := ↑x, property := hx } := sorry

theorem sum_diff_subset_symm_apply_of_not_mem {α : Type u_1} {s : set α} {t : set α} (h : s ⊆ t) [decidable_pred s] {x : ↥t} (hx : ¬subtype.val x ∈ s) : coe_fn (equiv.symm (set.sum_diff_subset h)) x =
  sum.inr { val := ↑x, property := { left := subtype.property x, right := hx } } := sorry

/-- If `s` is a set with decidable membership, then the sum of `s ∪ t` and `s ∩ t` is equivalent
to `s ⊕ t`. -/
protected def union_sum_inter {α : Type u} (s : set α) (t : set α) [decidable_pred s] : ↥(s ∪ t) ⊕ ↥(s ∩ t) ≃ ↥s ⊕ ↥t :=
  equiv.trans
    (equiv.trans
      (equiv.trans
        (equiv.trans (eq.mpr sorry (equiv.refl (↥(s ∪ t) ⊕ ↥(s ∩ t))))
          (sum_congr (set.union sorry) (equiv.refl ↥(s ∩ t))))
        (sum_assoc ↥s ↥(t \ s) ↥(s ∩ t)))
      (sum_congr (equiv.refl ↥s) (equiv.symm (set.union' (fun (_x : α) => ¬_x ∈ s) sorry sorry))))
    (eq.mpr sorry (equiv.refl (↥s ⊕ ↥t)))

/-- Given an equivalence `e₀` between sets `s : set α` and `t : set β`, the set of equivalences
`e : α ≃ β` such that `e ↑x = ↑(e₀ x)` for each `x : s` is equivalent to the set of equivalences
between `sᶜ` and `tᶜ`. -/
protected def compl {α : Type u} {β : Type v} {s : set α} {t : set β} [decidable_pred s] [decidable_pred t] (e₀ : ↥s ≃ ↥t) : (Subtype fun (e : α ≃ β) => ∀ (x : ↥s), coe_fn e ↑x = ↑(coe_fn e₀ x)) ≃ (↥(sᶜ) ≃ ↥(tᶜ)) :=
  mk (fun (e : Subtype fun (e : α ≃ β) => ∀ (x : ↥s), coe_fn e ↑x = ↑(coe_fn e₀ x)) => subtype_congr ↑e sorry)
    (fun (e₁ : ↥(sᶜ) ≃ ↥(tᶜ)) =>
      { val := equiv.trans (equiv.trans (equiv.symm (set.sum_compl s)) (sum_congr e₀ e₁)) (set.sum_compl t),
        property := sorry })
    sorry sorry

/-- The set product of two sets is equivalent to the type product of their coercions to types. -/
protected def prod {α : Type u_1} {β : Type u_2} (s : set α) (t : set β) : ↥(set.prod s t) ≃ ↥s × ↥t :=
  subtype_prod_equiv_prod

/-- If a function `f` is injective on a set `s`, then `s` is equivalent to `f '' s`. -/
protected def image_of_inj_on {α : Type u_1} {β : Type u_2} (f : α → β) (s : set α) (H : set.inj_on f s) : ↥s ≃ ↥(f '' s) :=
  mk (fun (p : ↥s) => { val := f ↑p, property := sorry })
    (fun (p : ↥(f '' s)) => { val := classical.some sorry, property := sorry }) sorry sorry

/-- If `f` is an injective function, then `s` is equivalent to `f '' s`. -/
@[simp] theorem image_apply {α : Type u_1} {β : Type u_2} (f : α → β) (s : set α) (H : function.injective f) (p : ↥s) : coe_fn (set.image f s H) p = { val := f ↑p, property := image_of_inj_on._proof_1 f s p } :=
  Eq.refl { val := f ↑p, property := image_of_inj_on._proof_1 f s p }

theorem image_symm_preimage {α : Type u_1} {β : Type u_2} {f : α → β} (hf : function.injective f) (u : set α) (s : set α) : (fun (x : ↥(f '' s)) => ↑(coe_fn (equiv.symm (set.image f s hf)) x)) ⁻¹' u = coe ⁻¹' (f '' u) := sorry

/-- If `f : α → β` is an injective function, then `α` is equivalent to the range of `f`. -/
@[simp] theorem range_apply {α : Sort u_1} {β : Type u_2} (f : α → β) (H : function.injective f) (x : α) : coe_fn (set.range f H) x = { val := f x, property := set.mem_range_self x } :=
  Eq.refl (coe_fn (set.range f H) x)

theorem apply_range_symm {α : Sort u_1} {β : Type u_2} (f : α → β) (H : function.injective f) (b : ↥(set.range f)) : f (coe_fn (equiv.symm (set.range f H)) b) = ↑b := sorry

/-- If `α` is equivalent to `β`, then `set α` is equivalent to `set β`. -/
protected def congr {α : Type u_1} {β : Type u_2} (e : α ≃ β) : set α ≃ set β :=
  mk (fun (s : set α) => ⇑e '' s) (fun (t : set β) => ⇑(equiv.symm e) '' t) (symm_image_image e) sorry

/-- The set `{x ∈ s | t x}` is equivalent to the set of `x : s` such that `t x`. -/
protected def sep {α : Type u} (s : set α) (t : α → Prop) : ↥(has_sep.sep (fun (x : α) => t x) s) ≃ ↥(set_of fun (x : ↥s) => t ↑x) :=
  equiv.symm (subtype_subtype_equiv_subtype_inter s t)

/-- The set `𝒫 S := {x | x ⊆ S}` is equivalent to the type `set S`. -/
protected def powerset {α : Type u_1} (S : set α) : ↥(𝒫 S) ≃ set ↥S :=
  mk (fun (x : ↥(𝒫 S)) => coe ⁻¹' ↑x) (fun (x : set ↥S) => { val := coe '' x, property := sorry }) sorry sorry

end set


/-- If `f` is a bijective function, then its domain is equivalent to its codomain. -/
def of_bijective {α : Sort u_1} {β : Type u_2} (f : α → β) (hf : function.bijective f) : α ≃ β :=
  equiv.trans (set.range f sorry) (equiv.trans (set_congr sorry) (set.univ β))

theorem of_bijective_apply_symm_apply {α : Sort u_1} {β : Type u_2} (f : α → β) (hf : function.bijective f) (x : β) : f (coe_fn (equiv.symm (of_bijective f hf)) x) = x :=
  apply_symm_apply (of_bijective f hf) x

@[simp] theorem of_bijective_symm_apply_apply {α : Sort u_1} {β : Type u_2} (f : α → β) (hf : function.bijective f) (x : α) : coe_fn (equiv.symm (of_bijective f hf)) (f x) = x :=
  symm_apply_apply (of_bijective f hf) x

/-- If `f` is an injective function, then its domain is equivalent to its range. -/
@[simp] theorem of_injective_apply {α : Sort u_1} {β : Type u_2} (f : α → β) (hf : function.injective f) : ∀ (ᾰ : α), coe_fn (of_injective f hf) ᾰ = { val := f ᾰ, property := set.mem_range_self ᾰ } :=
  fun (ᾰ : α) => Eq.refl { val := f ᾰ, property := set.mem_range_self ᾰ }

/-- Subtype of the quotient is equivalent to the quotient of the subtype. Let `α` be a setoid with
equivalence relation `~`. Let `p₂` be a predicate on the quotient type `α/~`, and `p₁` be the lift
of this predicate to `α`: `p₁ a ↔ p₂ ⟦a⟧`. Let `~₂` be the restriction of `~` to `{x // p₁ x}`.
Then `{x // p₂ x}` is equivalent to the quotient of `{x // p₁ x}` by `~₂`. -/
def subtype_quotient_equiv_quotient_subtype {α : Sort u} (p₁ : α → Prop) [s₁ : setoid α] [s₂ : setoid (Subtype p₁)] (p₂ : quotient s₁ → Prop) (hp₂ : ∀ (a : α), p₁ a ↔ p₂ (quotient.mk a)) (h : ∀ (x y : Subtype p₁), setoid.r x y ↔ ↑x ≈ ↑y) : (Subtype fun (x : quotient s₁) => p₂ x) ≃ quotient s₂ :=
  mk
    (fun (a : Subtype fun (x : quotient s₁) => p₂ x) =>
      quotient.hrec_on (subtype.val a)
        (fun (a : α) (h : p₂ (quotient.mk a)) => quotient.mk { val := a, property := sorry }) sorry sorry)
    (fun (a : quotient s₂) =>
      quotient.lift_on a (fun (a : Subtype p₁) => { val := quotient.mk (subtype.val a), property := sorry }) sorry)
    sorry sorry

/-- A helper function for `equiv.swap`. -/
def swap_core {α : Sort u} [DecidableEq α] (a : α) (b : α) (r : α) : α :=
  ite (r = a) b (ite (r = b) a r)

theorem swap_core_self {α : Sort u} [DecidableEq α] (r : α) (a : α) : swap_core a a r = r := sorry

theorem swap_core_swap_core {α : Sort u} [DecidableEq α] (r : α) (a : α) (b : α) : swap_core a b (swap_core a b r) = r := sorry

theorem swap_core_comm {α : Sort u} [DecidableEq α] (r : α) (a : α) (b : α) : swap_core a b r = swap_core b a r := sorry

/-- `swap a b` is the permutation that swaps `a` and `b` and
  leaves other values as is. -/
def swap {α : Sort u} [DecidableEq α] (a : α) (b : α) : perm α :=
  mk (swap_core a b) (swap_core a b) sorry sorry

@[simp] theorem swap_self {α : Sort u} [DecidableEq α] (a : α) : swap a a = equiv.refl α :=
  ext fun (r : α) => swap_core_self r a

theorem swap_comm {α : Sort u} [DecidableEq α] (a : α) (b : α) : swap a b = swap b a :=
  ext fun (r : α) => swap_core_comm r a b

theorem swap_apply_def {α : Sort u} [DecidableEq α] (a : α) (b : α) (x : α) : coe_fn (swap a b) x = ite (x = a) b (ite (x = b) a x) :=
  rfl

@[simp] theorem swap_apply_left {α : Sort u} [DecidableEq α] (a : α) (b : α) : coe_fn (swap a b) a = b :=
  if_pos rfl

@[simp] theorem swap_apply_right {α : Sort u} [DecidableEq α] (a : α) (b : α) : coe_fn (swap a b) b = a := sorry

theorem swap_apply_of_ne_of_ne {α : Sort u} [DecidableEq α] {a : α} {b : α} {x : α} : x ≠ a → x ≠ b → coe_fn (swap a b) x = x := sorry

@[simp] theorem swap_swap {α : Sort u} [DecidableEq α] (a : α) (b : α) : equiv.trans (swap a b) (swap a b) = equiv.refl α :=
  ext fun (x : α) => swap_core_swap_core x a b

theorem swap_comp_apply {α : Sort u} [DecidableEq α] {a : α} {b : α} {x : α} (π : perm α) : coe_fn (equiv.trans π (swap a b)) x = ite (coe_fn π x = a) b (ite (coe_fn π x = b) a (coe_fn π x)) := sorry

theorem swap_eq_update {α : Sort u} [DecidableEq α] (i : α) (j : α) : ⇑(swap i j) = function.update (function.update id j i) i j := sorry

theorem comp_swap_eq_update {α : Sort u} {β : Sort v} [DecidableEq α] (i : α) (j : α) (f : α → β) : f ∘ ⇑(swap i j) = function.update (function.update f j (f i)) i (f j) := sorry

@[simp] theorem symm_trans_swap_trans {α : Sort u} {β : Sort v} [DecidableEq α] [DecidableEq β] (a : α) (b : α) (e : α ≃ β) : equiv.trans (equiv.trans (equiv.symm e) (swap a b)) e = swap (coe_fn e a) (coe_fn e b) := sorry

@[simp] theorem trans_swap_trans_symm {α : Sort u} {β : Sort v} [DecidableEq α] [DecidableEq β] (a : β) (b : β) (e : α ≃ β) : equiv.trans (equiv.trans e (swap a b)) (equiv.symm e) = swap (coe_fn (equiv.symm e) a) (coe_fn (equiv.symm e) b) :=
  symm_trans_swap_trans a b (equiv.symm e)

@[simp] theorem swap_apply_self {α : Sort u} [DecidableEq α] (i : α) (j : α) (a : α) : coe_fn (swap i j) (coe_fn (swap i j) a) = a := sorry

/-- A function is invariant to a swap if it is equal at both elements -/
theorem apply_swap_eq_self {α : Sort u} {β : Sort v} [DecidableEq α] {v : α → β} {i : α} {j : α} (hv : v i = v j) (k : α) : v (coe_fn (swap i j) k) = v k := sorry

namespace perm


@[simp] theorem sum_congr_swap_refl {α : Type u_1} {β : Type u_2} [DecidableEq α] [DecidableEq β] (i : α) (j : α) : sum_congr (swap i j) (equiv.refl β) = swap (sum.inl i) (sum.inl j) := sorry

@[simp] theorem sum_congr_refl_swap {α : Type u_1} {β : Type u_2} [DecidableEq α] [DecidableEq β] (i : β) (j : β) : sum_congr (equiv.refl α) (swap i j) = swap (sum.inr i) (sum.inr j) := sorry

end perm


/-- Augment an equivalence with a prescribed mapping `f a = b` -/
def set_value {α : Sort u} {β : Sort v} [DecidableEq α] (f : α ≃ β) (a : α) (b : β) : α ≃ β :=
  equiv.trans (swap a (coe_fn (equiv.symm f) b)) f

@[simp] theorem set_value_eq {α : Sort u} {β : Sort v} [DecidableEq α] (f : α ≃ β) (a : α) (b : β) : coe_fn (set_value f a b) a = b := sorry

protected theorem exists_unique_congr {α : Sort u} {β : Sort v} {p : α → Prop} {q : β → Prop} (f : α ≃ β) (h : ∀ {x : α}, p x ↔ q (coe_fn f x)) : (exists_unique fun (x : α) => p x) ↔ exists_unique fun (y : β) => q y := sorry

protected theorem exists_unique_congr_left' {α : Sort u} {β : Sort v} {p : α → Prop} (f : α ≃ β) : (exists_unique fun (x : α) => p x) ↔ exists_unique fun (y : β) => p (coe_fn (equiv.symm f) y) := sorry

protected theorem exists_unique_congr_left {α : Sort u} {β : Sort v} {p : β → Prop} (f : α ≃ β) : (exists_unique fun (x : α) => p (coe_fn f x)) ↔ exists_unique fun (y : β) => p y :=
  iff.symm (equiv.exists_unique_congr_left' (equiv.symm f))

protected theorem forall_congr {α : Sort u} {β : Sort v} {p : α → Prop} {q : β → Prop} (f : α ≃ β) (h : ∀ {x : α}, p x ↔ q (coe_fn f x)) : (∀ (x : α), p x) ↔ ∀ (y : β), q y := sorry

protected theorem forall_congr' {α : Sort u} {β : Sort v} {p : α → Prop} {q : β → Prop} (f : α ≃ β) (h : ∀ {x : β}, p (coe_fn (equiv.symm f) x) ↔ q x) : (∀ (x : α), p x) ↔ ∀ (y : β), q y :=
  iff.symm (equiv.forall_congr (equiv.symm f) fun (x : β) => iff.symm h)

-- We next build some higher arity versions of `equiv.forall_congr`.

-- Although they appear to just be repeated applications of `equiv.forall_congr`,

-- unification of metavariables works better with these versions.

-- In particular, they are necessary in `equiv_rw`.

-- (Stopping at ternary functions seems reasonable: at least in 1-categorical mathematics,

-- it's rare to have axioms involving more than 3 elements at once.)

protected theorem forall₂_congr {α₁ : Sort ua1} {α₂ : Sort ua2} {β₁ : Sort ub1} {β₂ : Sort ub2} {p : α₁ → β₁ → Prop} {q : α₂ → β₂ → Prop} (eα : α₁ ≃ α₂) (eβ : β₁ ≃ β₂) (h : ∀ {x : α₁} {y : β₁}, p x y ↔ q (coe_fn eα x) (coe_fn eβ y)) : (∀ (x : α₁) (y : β₁), p x y) ↔ ∀ (x : α₂) (y : β₂), q x y :=
  equiv.forall_congr eα fun (x : α₁) => equiv.forall_congr eβ fun (x_1 : β₁) => h

protected theorem forall₂_congr' {α₁ : Sort ua1} {α₂ : Sort ua2} {β₁ : Sort ub1} {β₂ : Sort ub2} {p : α₁ → β₁ → Prop} {q : α₂ → β₂ → Prop} (eα : α₁ ≃ α₂) (eβ : β₁ ≃ β₂) (h : ∀ {x : α₂} {y : β₂}, p (coe_fn (equiv.symm eα) x) (coe_fn (equiv.symm eβ) y) ↔ q x y) : (∀ (x : α₁) (y : β₁), p x y) ↔ ∀ (x : α₂) (y : β₂), q x y :=
  iff.symm (equiv.forall₂_congr (equiv.symm eα) (equiv.symm eβ) fun (x : α₂) (y : β₂) => iff.symm h)

protected theorem forall₃_congr {α₁ : Sort ua1} {α₂ : Sort ua2} {β₁ : Sort ub1} {β₂ : Sort ub2} {γ₁ : Sort ug1} {γ₂ : Sort ug2} {p : α₁ → β₁ → γ₁ → Prop} {q : α₂ → β₂ → γ₂ → Prop} (eα : α₁ ≃ α₂) (eβ : β₁ ≃ β₂) (eγ : γ₁ ≃ γ₂) (h : ∀ {x : α₁} {y : β₁} {z : γ₁}, p x y z ↔ q (coe_fn eα x) (coe_fn eβ y) (coe_fn eγ z)) : (∀ (x : α₁) (y : β₁) (z : γ₁), p x y z) ↔ ∀ (x : α₂) (y : β₂) (z : γ₂), q x y z :=
  equiv.forall₂_congr eα eβ fun (x : α₁) (y : β₁) => equiv.forall_congr eγ fun (x_1 : γ₁) => h

protected theorem forall₃_congr' {α₁ : Sort ua1} {α₂ : Sort ua2} {β₁ : Sort ub1} {β₂ : Sort ub2} {γ₁ : Sort ug1} {γ₂ : Sort ug2} {p : α₁ → β₁ → γ₁ → Prop} {q : α₂ → β₂ → γ₂ → Prop} (eα : α₁ ≃ α₂) (eβ : β₁ ≃ β₂) (eγ : γ₁ ≃ γ₂) (h : ∀ {x : α₂} {y : β₂} {z : γ₂},
  p (coe_fn (equiv.symm eα) x) (coe_fn (equiv.symm eβ) y) (coe_fn (equiv.symm eγ) z) ↔ q x y z) : (∀ (x : α₁) (y : β₁) (z : γ₁), p x y z) ↔ ∀ (x : α₂) (y : β₂) (z : γ₂), q x y z :=
  iff.symm
    (equiv.forall₃_congr (equiv.symm eα) (equiv.symm eβ) (equiv.symm eγ) fun (x : α₂) (y : β₂) (z : γ₂) => iff.symm h)

protected theorem forall_congr_left' {α : Sort u} {β : Sort v} {p : α → Prop} (f : α ≃ β) : (∀ (x : α), p x) ↔ ∀ (y : β), p (coe_fn (equiv.symm f) y) := sorry

protected theorem forall_congr_left {α : Sort u} {β : Sort v} {p : β → Prop} (f : α ≃ β) : (∀ (x : α), p (coe_fn f x)) ↔ ∀ (y : β), p y :=
  iff.symm (equiv.forall_congr_left' (equiv.symm f))

/--
Transport dependent functions through an equivalence of the base space.
-/
@[simp] theorem Pi_congr_left'_symm_apply {α : Sort u} {β : Sort v} (P : α → Sort w) (e : α ≃ β) (f : (b : β) → P (coe_fn (equiv.symm e) b)) (x : α) : coe_fn (equiv.symm (Pi_congr_left' P e)) f x = eq.mpr (Pi_congr_left'._proof_1 P e x) (f (coe_fn e x)) :=
  Eq.refl (coe_fn (equiv.symm (Pi_congr_left' P e)) f x)

/--
Transporting dependent functions through an equivalence of the base,
expressed as a "simplification".
-/
def Pi_congr_left {α : Sort u} {β : Sort v} (P : β → Sort w) (e : α ≃ β) : ((a : α) → P (coe_fn e a)) ≃ ((b : β) → P b) :=
  equiv.symm (Pi_congr_left' P (equiv.symm e))

/--
Transport dependent functions through
an equivalence of the base spaces and a family
of equivalences of the matching fibers.
-/
def Pi_congr {α : Sort u} {β : Sort v} {W : α → Sort w} {Z : β → Sort z} (h₁ : α ≃ β) (h₂ : (a : α) → W a ≃ Z (coe_fn h₁ a)) : ((a : α) → W a) ≃ ((b : β) → Z b) :=
  equiv.trans (Pi_congr_right h₂) (Pi_congr_left Z h₁)

/--
Transport dependent functions through
an equivalence of the base spaces and a family
of equivalences of the matching fibres.
-/
def Pi_congr' {α : Sort u} {β : Sort v} {W : α → Sort w} {Z : β → Sort z} (h₁ : α ≃ β) (h₂ : (b : β) → W (coe_fn (equiv.symm h₁) b) ≃ Z b) : ((a : α) → W a) ≃ ((b : β) → Z b) :=
  equiv.symm (Pi_congr (equiv.symm h₁) fun (b : β) => equiv.symm (h₂ b))

end equiv


theorem function.injective.swap_apply {α : Sort u} {β : Sort v} [DecidableEq α] [DecidableEq β] {f : α → β} (hf : function.injective f) (x : α) (y : α) (z : α) : coe_fn (equiv.swap (f x) (f y)) (f z) = f (coe_fn (equiv.swap x y) z) := sorry

theorem function.injective.swap_comp {α : Sort u} {β : Sort v} [DecidableEq α] [DecidableEq β] {f : α → β} (hf : function.injective f) (x : α) (y : α) : ⇑(equiv.swap (f x) (f y)) ∘ f = f ∘ ⇑(equiv.swap x y) :=
  funext fun (z : α) => function.injective.swap_apply hf x y z

protected instance ulift.subsingleton {α : Type u_1} [subsingleton α] : subsingleton (ulift α) :=
  equiv.subsingleton equiv.ulift

protected instance plift.subsingleton {α : Sort u_1} [subsingleton α] : subsingleton (plift α) :=
  equiv.subsingleton equiv.plift

protected instance ulift.decidable_eq {α : Type u_1} [DecidableEq α] : DecidableEq (ulift α) :=
  equiv.decidable_eq equiv.ulift

protected instance plift.decidable_eq {α : Sort u_1} [DecidableEq α] : DecidableEq (plift α) :=
  equiv.decidable_eq equiv.plift

/-- If both `α` and `β` are singletons, then `α ≃ β`. -/
def equiv_of_unique_of_unique {α : Sort u} {β : Sort v} [unique α] [unique β] : α ≃ β :=
  equiv.mk (fun (_x : α) => Inhabited.default) (fun (_x : β) => Inhabited.default) sorry sorry

/-- If `α` is a singleton, then it is equivalent to any `punit`. -/
def equiv_punit_of_unique {α : Sort u} [unique α] : α ≃ PUnit :=
  equiv_of_unique_of_unique

/-- If `α` is a subsingleton, then it is equivalent to `α × α`. -/
def subsingleton_prod_self_equiv {α : Type u_1} [subsingleton α] : α × α ≃ α :=
  equiv.mk (fun (p : α × α) => prod.fst p) (fun (a : α) => (a, a)) sorry sorry

/-- To give an equivalence between two subsingleton types, it is sufficient to give any two
    functions between them. -/
def equiv_of_subsingleton_of_subsingleton {α : Sort u} {β : Sort v} [subsingleton α] [subsingleton β] (f : α → β) (g : β → α) : α ≃ β :=
  equiv.mk f g sorry sorry

/-- `unique (unique α)` is equivalent to `unique α`. -/
def unique_unique_equiv {α : Sort u} : unique (unique α) ≃ unique α :=
  equiv_of_subsingleton_of_subsingleton (fun (h : unique (unique α)) => Inhabited.default)
    fun (h : unique α) => unique.mk { default := h } sorry

namespace quot


/-- An equivalence `e : α ≃ β` generates an equivalence between quotient spaces,
if `ra a₁ a₂ ↔ rb (e a₁) (e a₂). -/
protected def congr {α : Sort u} {β : Sort v} {ra : α → α → Prop} {rb : β → β → Prop} (e : α ≃ β) (eq : ∀ (a₁ a₂ : α), ra a₁ a₂ ↔ rb (coe_fn e a₁) (coe_fn e a₂)) : Quot ra ≃ Quot rb :=
  equiv.mk (quot.map ⇑e sorry) (quot.map ⇑(equiv.symm e) sorry) sorry sorry

/-- Quotients are congruent on equivalences under equality of their relation.
An alternative is just to use rewriting with `eq`, but then computational proofs get stuck. -/
protected def congr_right {α : Sort u} {r : α → α → Prop} {r' : α → α → Prop} (eq : ∀ (a₁ a₂ : α), r a₁ a₂ ↔ r' a₁ a₂) : Quot r ≃ Quot r' :=
  quot.congr (equiv.refl α) eq

/-- An equivalence `e : α ≃ β` generates an equivalence between the quotient space of `α`
by a relation `ra` and the quotient space of `β` by the image of this relation under `e`. -/
protected def congr_left {α : Sort u} {β : Sort v} {r : α → α → Prop} (e : α ≃ β) : Quot r ≃ Quot fun (b b' : β) => r (coe_fn (equiv.symm e) b) (coe_fn (equiv.symm e) b') :=
  quot.congr e sorry

end quot


namespace quotient


/-- An equivalence `e : α ≃ β` generates an equivalence between quotient spaces,
if `ra a₁ a₂ ↔ rb (e a₁) (e a₂). -/
protected def congr {α : Sort u} {β : Sort v} {ra : setoid α} {rb : setoid β} (e : α ≃ β) (eq : ∀ (a₁ a₂ : α), setoid.r a₁ a₂ ↔ setoid.r (coe_fn e a₁) (coe_fn e a₂)) : quotient ra ≃ quotient rb :=
  quot.congr e eq

/-- Quotients are congruent on equivalences under equality of their relation.
An alternative is just to use rewriting with `eq`, but then computational proofs get stuck. -/
protected def congr_right {α : Sort u} {r : setoid α} {r' : setoid α} (eq : ∀ (a₁ a₂ : α), setoid.r a₁ a₂ ↔ setoid.r a₁ a₂) : quotient r ≃ quotient r' :=
  quot.congr_right eq

end quotient


/-- If a function is a bijection between two sets `s` and `t`, then it induces an
equivalence between the the types `↥s` and ``↥t`. -/
def set.bij_on.equiv {α : Type u_1} {β : Type u_2} {s : set α} {t : set β} (f : α → β) (h : set.bij_on f s t) : ↥s ≃ ↥t :=
  equiv.of_bijective (set.cod_restrict (set.restrict f s) t sorry) (set.bij_on.bijective h)

namespace function


theorem update_comp_equiv {α : Sort u_1} {β : Sort u_2} {α' : Sort u_3} [DecidableEq α'] [DecidableEq α] (f : α → β) (g : α' ≃ α) (a : α) (v : β) : update f a v ∘ ⇑g = update (f ∘ ⇑g) (coe_fn (equiv.symm g) a) v := sorry

theorem update_apply_equiv_apply {α : Sort u_1} {β : Sort u_2} {α' : Sort u_3} [DecidableEq α'] [DecidableEq α] (f : α → β) (g : α' ≃ α) (a : α) (v : β) (a' : α') : update f a v (coe_fn g a') = update (f ∘ ⇑g) (coe_fn (equiv.symm g) a) v a' :=
  congr_fun (update_comp_equiv f g a v) a'

end function


/-- The composition of an updated function with an equiv on a subset can be expressed as an
updated function. -/
theorem dite_comp_equiv_update {α : Type u_1} {β : Sort u_2} {γ : Sort u_3} {s : set α} (e : β ≃ ↥s) (v : β → γ) (w : α → γ) (j : β) (x : γ) [DecidableEq β] [DecidableEq α] [(j : α) → Decidable (j ∈ s)] : (fun (i : α) =>
    dite (i ∈ s) (fun (h : i ∈ s) => function.update v j x (coe_fn (equiv.symm e) { val := i, property := h }))
      fun (h : ¬i ∈ s) => w i) =
  function.update
    (fun (i : α) =>
      dite (i ∈ s) (fun (h : i ∈ s) => v (coe_fn (equiv.symm e) { val := i, property := h })) fun (h : ¬i ∈ s) => w i)
    (↑(coe_fn e j)) x := sorry

