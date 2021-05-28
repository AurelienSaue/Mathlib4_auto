/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.pi
import Mathlib.data.prod
import Mathlib.logic.unique
import Mathlib.logic.function.basic
import Mathlib.PostPort

universes u_3 l u_1 u_2 u_4 

namespace Mathlib

/-!
# Nontrivial types

A type is *nontrivial* if it contains at least two elements. This is useful in particular for rings
(where it is equivalent to the fact that zero is different from one) and for vector spaces
(where it is equivalent to the fact that the dimension is positive).

We introduce a typeclass `nontrivial` formalizing this property.
-/

/-- Predicate typeclass for expressing that a type is not reduced to a single element. In rings,
this is equivalent to `0 ≠ 1`. In vector spaces, this is equivalent to positive dimension. -/
class nontrivial (α : Type u_3) 
where
  exists_pair_ne : ∃ (x : α), ∃ (y : α), x ≠ y

theorem nontrivial_iff {α : Type u_1} : nontrivial α ↔ ∃ (x : α), ∃ (y : α), x ≠ y :=
  { mp := fun (h : nontrivial α) => nontrivial.exists_pair_ne,
    mpr := fun (h : ∃ (x : α), ∃ (y : α), x ≠ y) => nontrivial.mk h }

theorem exists_pair_ne (α : Type u_1) [nontrivial α] : ∃ (x : α), ∃ (y : α), x ≠ y :=
  nontrivial.exists_pair_ne

theorem exists_ne {α : Type u_1} [nontrivial α] (x : α) : ∃ (y : α), y ≠ x := sorry

-- `x` and `y` are explicit here, as they are often needed to guide typechecking of `h`.

theorem nontrivial_of_ne {α : Type u_1} (x : α) (y : α) (h : x ≠ y) : nontrivial α :=
  nontrivial.mk (Exists.intro x (Exists.intro y h))

-- `x` and `y` are explicit here, as they are often needed to guide typechecking of `h`.

theorem nontrivial_of_lt {α : Type u_1} [preorder α] (x : α) (y : α) (h : x < y) : nontrivial α :=
  nontrivial.mk (Exists.intro x (Exists.intro y (ne_of_lt h)))

protected instance nontrivial.to_nonempty {α : Type u_1} [nontrivial α] : Nonempty α :=
  sorry

/-- An inhabited type is either nontrivial, or has a unique element. -/
def nontrivial_psum_unique (α : Type u_1) [Inhabited α] : psum (nontrivial α) (unique α) :=
  dite (nontrivial α) (fun (h : nontrivial α) => psum.inl h)
    fun (h : ¬nontrivial α) => psum.inr (unique.mk { default := Inhabited.default } sorry)

theorem subsingleton_iff {α : Type u_1} : subsingleton α ↔ ∀ (x y : α), x = y :=
  { mp := fun (h : subsingleton α) => subsingleton.elim, mpr := fun (h : ∀ (x y : α), x = y) => subsingleton.intro h }

theorem not_nontrivial_iff_subsingleton {α : Type u_1} : ¬nontrivial α ↔ subsingleton α := sorry

theorem not_subsingleton (α : Type u_1) [h : nontrivial α] : ¬subsingleton α := sorry

/-- A type is either a subsingleton or nontrivial. -/
theorem subsingleton_or_nontrivial (α : Type u_1) : subsingleton α ∨ nontrivial α :=
  eq.mpr (id (Eq._oldrec (Eq.refl (subsingleton α ∨ nontrivial α)) (Eq.symm (propext not_nontrivial_iff_subsingleton))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (¬nontrivial α ∨ nontrivial α)) (propext (or_comm (¬nontrivial α) (nontrivial α)))))
      (classical.em (nontrivial α)))

theorem false_of_nontrivial_of_subsingleton (α : Type u_1) [nontrivial α] [subsingleton α] : False := sorry

protected instance option.nontrivial {α : Type u_1} [Nonempty α] : nontrivial (Option α) :=
  nonempty.elim_to_inhabited
    fun (inst : Inhabited α) =>
      nontrivial.mk
        (Exists.intro none
          (Exists.intro (some Inhabited.default)
            (id (id fun (ᾰ : none = some Inhabited.default) => option.no_confusion ᾰ))))

/-- Pushforward a `nontrivial` instance along an injective function. -/
protected theorem function.injective.nontrivial {α : Type u_1} {β : Type u_2} [nontrivial α] {f : α → β} (hf : function.injective f) : nontrivial β := sorry

/-- Pullback a `nontrivial` instance along a surjective function. -/
protected theorem function.surjective.nontrivial {α : Type u_1} {β : Type u_2} [nontrivial β] {f : α → β} (hf : function.surjective f) : nontrivial α := sorry

/-- An injective function from a nontrivial type has an argument at
which it does not take a given value. -/
protected theorem function.injective.exists_ne {α : Type u_1} {β : Type u_2} [nontrivial α] {f : α → β} (hf : function.injective f) (y : β) : ∃ (x : α), f x ≠ y := sorry

protected instance nontrivial_prod_right {α : Type u_1} {β : Type u_2} [Nonempty α] [nontrivial β] : nontrivial (α × β) :=
  function.surjective.nontrivial prod.snd_surjective

protected instance nontrivial_prod_left {α : Type u_1} {β : Type u_2} [nontrivial α] [Nonempty β] : nontrivial (α × β) :=
  function.surjective.nontrivial prod.fst_surjective

namespace pi


/-- A pi type is nontrivial if it's nonempty everywhere and nontrivial somewhere. -/
theorem nontrivial_at {I : Type u_3} {f : I → Type u_4} (i' : I) [inst : ∀ (i : I), Nonempty (f i)] [nontrivial (f i')] : nontrivial ((i : I) → f i) :=
  function.injective.nontrivial (function.update_injective (fun (i : I) => Classical.choice (inst i)) i')

/--
As a convenience, provide an instance automatically if `(f (default I))` is nontrivial.

If a different index has the non-trivial type, then use `haveI := nontrivial_at that_index`.
-/
protected instance nontrivial {I : Type u_3} {f : I → Type u_4} [Inhabited I] [inst : ∀ (i : I), Nonempty (f i)] [nontrivial (f Inhabited.default)] : nontrivial ((i : I) → f i) :=
  nontrivial_at Inhabited.default

end pi


protected instance function.nontrivial {α : Type u_1} {β : Type u_2} [h : Nonempty α] [nontrivial β] : nontrivial (α → β) :=
  nonempty.elim h fun (a : α) => pi.nontrivial_at a

protected theorem subsingleton.le {α : Type u_1} [preorder α] [subsingleton α] (x : α) (y : α) : x ≤ y :=
  le_of_eq (subsingleton.elim x y)

namespace tactic


/--
Tries to generate a `nontrivial α` instance by performing case analysis on
`subsingleton_or_nontrivial α`,
attempting to discharge the subsingleton branch using lemmas with `@[nontriviality]` attribute,
including `subsingleton.le` and `eq_iff_true_of_subsingleton`.
-/
/--
Tries to generate a `nontrivial α` instance using `nontrivial_of_ne` or `nontrivial_of_lt`
and local hypotheses.
-/
end tactic


namespace tactic.interactive


/--
Attempts to generate a `nontrivial α` hypothesis.

The tactic first looks for an instance using `apply_instance`.

If the goal is an (in)equality, the type `α` is inferred from the goal.
Otherwise, the type needs to be specified in the tactic invocation, as `nontriviality α`.

The `nontriviality` tactic will first look for strict inequalities amongst the hypotheses,
and use these to derive the `nontrivial` instance directly.

Otherwise, it will perform a case split on `subsingleton α ∨ nontrivial α`, and attempt to discharge
the `subsingleton` goal using `simp [lemmas] with nontriviality`, where `[lemmas]` is a list of
additional `simp` lemmas that can be passed to `nontriviality` using the syntax
`nontriviality α using [lemmas]`.

```
example {R : Type} [ordered_ring R] {a : R} (h : 0 < a) : 0 < a :=
begin
  nontriviality, -- There is now a `nontrivial R` hypothesis available.
  assumption,
end
```

```
example {R : Type} [comm_ring R] {r s : R} : r * s = s * r :=
begin
  nontriviality, -- There is now a `nontrivial R` hypothesis available.
  apply mul_comm,
end
```

```
example {R : Type} [ordered_ring R] {a : R} (h : 0 < a) : (2 : ℕ) ∣ 4 :=
begin
  nontriviality R, -- there is now a `nontrivial R` hypothesis available.
  dec_trivial
end
```

```
def myeq {α : Type} (a b : α) : Prop := a = b

example {α : Type} (a b : α) (h : a = b) : myeq a b :=
begin
  success_if_fail { nontriviality α }, -- Fails
  nontriviality α using [myeq], -- There is now a `nontrivial α` hypothesis available
  assumption
end
```
-/
end tactic.interactive


namespace bool


protected instance nontrivial : nontrivial Bool :=
  nontrivial.mk (Exists.intro tt (Exists.intro false tt_eq_ff_eq_false))

