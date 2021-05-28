/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.limits.shapes.equalizers
import Mathlib.category_theory.limits.shapes.pullbacks
import Mathlib.category_theory.limits.shapes.regular_mono
import PostPort

universes v u l 

namespace Mathlib

/-!
# Kernel pairs

This file defines what it means for a parallel pair of morphisms `a b : R ⟶ X` to be the kernel pair
for a morphism `f`.
Some properties of kernel pairs are given, namely allowing one to transfer between
the kernel pair of `f₁ ≫ f₂` to the kernel pair of `f₁`.
It is also proved that if `f` is a coequalizer of some pair, and `a`,`b` is a kernel pair for `f` then
it is a coequalizer of `a`,`b`.

## Implementation

The definition is essentially just a wrapper for `is_limit (pullback_cone.mk _ _ _)`, but the
constructions given here are useful, yet awkward to present in that language, so a basic API
is developed here.

## TODO

- Internal equivalence relations (or congruences) and the fact that every kernel pair induces one,
  and the converse in an effective regular category (WIP by b-mehta).

-/

namespace category_theory


/--
`is_kernel_pair f a b` expresses that `(a, b)` is a kernel pair for `f`, i.e. `a ≫ f = b ≫ f`
and the square
  R → X
  ↓   ↓
  X → Y
is a pullback square.
This is essentially just a convenience wrapper over `is_limit (pullback_cone.mk _ _ _)`.
-/
structure is_kernel_pair {C : Type u} [category C] {R : C} {X : C} {Y : C} (f : X ⟶ Y) (a : R ⟶ X) (b : R ⟶ X) 
where
  comm : a ≫ f = b ≫ f
  is_limit : limits.is_limit (limits.pullback_cone.mk a b comm)

theorem is_kernel_pair.comm_assoc {C : Type u} [category C] {R : C} {X : C} {Y : C} {f : X ⟶ Y} {a : R ⟶ X} {b : R ⟶ X} (c : is_kernel_pair f a b) {X' : C} (f' : Y ⟶ X') : a ≫ f ≫ f' = b ≫ f ≫ f' := sorry

namespace is_kernel_pair


/-- The data expressing that `(a, b)` is a kernel pair is subsingleton. -/
protected instance subsingleton {C : Type u} [category C] {R : C} {X : C} {Y : C} (f : X ⟶ Y) (a : R ⟶ X) (b : R ⟶ X) : subsingleton (is_kernel_pair f a b) :=
  subsingleton.intro
    fun (P Q : is_kernel_pair f a b) =>
      cases_on P
        fun (P_comm : a ≫ f = b ≫ f) (P_is_limit : limits.is_limit (limits.pullback_cone.mk a b P_comm)) =>
          cases_on Q
            fun (Q_comm : a ≫ f = b ≫ f) (Q_is_limit : limits.is_limit (limits.pullback_cone.mk a b Q_comm)) =>
              (fun {f : X ⟶ Y} {a b : R ⟶ X} (comm comm_1 : a ≫ f = b ≫ f)
                  (is_limit : limits.is_limit (limits.pullback_cone.mk a b comm))
                  (is_limit_1 : limits.is_limit (limits.pullback_cone.mk a b comm_1)) =>
                  Eq.trans
                    ((fun {f : X ⟶ Y} {a b : R ⟶ X} (comm : a ≫ f = b ≫ f)
                        (is_limit : limits.is_limit (limits.pullback_cone.mk a b comm)) => Eq.refl (mk comm is_limit))
                      comm is_limit)
                    (congr (Eq.refl (mk comm)) (subsingleton.elim is_limit is_limit_1)))
                P_comm Q_comm P_is_limit Q_is_limit

/-- If `f` is a monomorphism, then `(𝟙 _, 𝟙 _)`  is a kernel pair for `f`. -/
def id_of_mono {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) [mono f] : is_kernel_pair f 𝟙 𝟙 :=
  mk sorry
    (limits.pullback_cone.is_limit_aux' (limits.pullback_cone.mk 𝟙 𝟙 sorry)
      fun (s : limits.pullback_cone f f) => { val := limits.pullback_cone.snd s, property := sorry })

protected instance inhabited {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) [mono f] : Inhabited (is_kernel_pair f 𝟙 𝟙) :=
  { default := id_of_mono f }

/--
Given a pair of morphisms `p`, `q` to `X` which factor through `f`, they factor through any kernel
pair of `f`.
-/
def lift' {C : Type u} [category C] {R : C} {X : C} {Y : C} {f : X ⟶ Y} {a : R ⟶ X} {b : R ⟶ X} {S : C} (k : is_kernel_pair f a b) (p : S ⟶ X) (q : S ⟶ X) (w : p ≫ f = q ≫ f) : Subtype fun (t : S ⟶ R) => t ≫ a = p ∧ t ≫ b = q :=
  limits.pullback_cone.is_limit.lift' (is_limit k) p q w

/--
If `(a,b)` is a kernel pair for `f₁ ≫ f₂` and `a ≫ f₁ = b ≫ f₁`, then `(a,b)` is a kernel pair for
just `f₁`.
That is, to show that `(a,b)` is a kernel pair for `f₁` it suffices to only show the square
commutes, rather than to additionally show it's a pullback.
-/
def cancel_right {C : Type u} [category C] {R : C} {X : C} {Y : C} {Z : C} {a : R ⟶ X} {b : R ⟶ X} {f₁ : X ⟶ Y} {f₂ : Y ⟶ Z} (comm : a ≫ f₁ = b ≫ f₁) (big_k : is_kernel_pair (f₁ ≫ f₂) a b) : is_kernel_pair f₁ a b :=
  mk comm
    (limits.pullback_cone.is_limit_aux' (limits.pullback_cone.mk a b comm)
      fun (s : limits.pullback_cone f₁ f₁) =>
        let s' : limits.pullback_cone (f₁ ≫ f₂) (f₁ ≫ f₂) :=
          limits.pullback_cone.mk (limits.pullback_cone.fst s) (limits.pullback_cone.snd s)
            (limits.pullback_cone.condition_assoc s f₂);
        { val := limits.is_limit.lift (is_limit big_k) s', property := sorry })

/--
If `(a,b)` is a kernel pair for `f₁ ≫ f₂` and `f₂` is mono, then `(a,b)` is a kernel pair for
just `f₁`.
The converse of `comp_of_mono`.
-/
def cancel_right_of_mono {C : Type u} [category C] {R : C} {X : C} {Y : C} {Z : C} {a : R ⟶ X} {b : R ⟶ X} {f₁ : X ⟶ Y} {f₂ : Y ⟶ Z} [mono f₂] (big_k : is_kernel_pair (f₁ ≫ f₂) a b) : is_kernel_pair f₁ a b :=
  cancel_right sorry big_k

/--
If `(a,b)` is a kernel pair for `f₁` and `f₂` is mono, then `(a,b)` is a kernel pair for `f₁ ≫ f₂`.
The converse of `cancel_right_of_mono`.
-/
def comp_of_mono {C : Type u} [category C] {R : C} {X : C} {Y : C} {Z : C} {a : R ⟶ X} {b : R ⟶ X} {f₁ : X ⟶ Y} {f₂ : Y ⟶ Z} [mono f₂] (small_k : is_kernel_pair f₁ a b) : is_kernel_pair (f₁ ≫ f₂) a b :=
  mk sorry
    (limits.pullback_cone.is_limit_aux' (limits.pullback_cone.mk a b sorry)
      fun (s : limits.pullback_cone (f₁ ≫ f₂) (f₁ ≫ f₂)) =>
        { val :=
            subtype.val
              (limits.pullback_cone.is_limit.lift' (is_limit small_k) (limits.pullback_cone.fst s)
                (limits.pullback_cone.snd s) sorry),
          property := sorry })

/--
If `(a,b)` is the kernel pair of `f`, and `f` is a coequalizer morphism for some parallel pair, then
`f` is a coequalizer morphism of `a` and `b`.
-/
def to_coequalizer {C : Type u} [category C] {R : C} {X : C} {Y : C} {f : X ⟶ Y} {a : R ⟶ X} {b : R ⟶ X} (k : is_kernel_pair f a b) [r : regular_epi f] : limits.is_colimit (limits.cofork.of_π f (comm k)) :=
  limits.cofork.is_colimit.mk (limits.cofork.of_π f (comm k))
    (fun (s : limits.cofork a b) =>
      subtype.val (limits.cofork.is_colimit.desc' regular_epi.is_colimit (limits.cofork.π s) sorry))
    sorry sorry

