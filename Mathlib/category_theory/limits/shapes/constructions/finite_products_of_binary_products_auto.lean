/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.limits.shapes.finite_products
import Mathlib.category_theory.limits.shapes.binary_products
import Mathlib.category_theory.limits.preserves.shapes.products
import Mathlib.category_theory.limits.preserves.shapes.binary_products
import Mathlib.category_theory.limits.shapes.pullbacks
import Mathlib.category_theory.pempty
import Mathlib.data.equiv.fin
import Mathlib.PostPort

universes v u u' 

namespace Mathlib

/-!
# Constructing finite products from binary products and terminal.

If a category has binary products and a terminal object then it has finite products.
If a functor preserves binary products and the terminal object then it preserves finite products.

# TODO

Provide the dual results.
Show the analogous results for functors which reflect or create (co)limits.
-/

namespace category_theory


/--
Given `n+1` objects of `C`, a fan for the last `n` with point `c₁.X` and a binary fan on `c₁.X` and
`f 0`, we can build a fan for all `n+1`.

In `extend_fan_is_limit` we show that if the two given fans are limits, then this fan is also a
limit.
-/
@[simp] theorem extend_fan_X {C : Type u} [category C] {n : ℕ} {f : ulift (fin (n + 1)) → C}
    (c₁ : limits.fan fun (i : ulift (fin n)) => f (ulift.up (fin.succ (ulift.down i))))
    (c₂ : limits.binary_fan (f (ulift.up 0)) (limits.cone.X c₁)) :
    limits.cone.X (extend_fan c₁ c₂) = limits.cone.X c₂ :=
  Eq.refl (limits.cone.X (extend_fan c₁ c₂))

/--
Show that if the two given fans in `extend_fan` are limits, then the constructed fan is also a
limit.
-/
def extend_fan_is_limit {C : Type u} [category C] {n : ℕ} (f : ulift (fin (n + 1)) → C)
    {c₁ : limits.fan fun (i : ulift (fin n)) => f (ulift.up (fin.succ (ulift.down i)))}
    {c₂ : limits.binary_fan (f (ulift.up 0)) (limits.cone.X c₁)} (t₁ : limits.is_limit c₁)
    (t₂ : limits.is_limit c₂) : limits.is_limit (extend_fan c₁ c₂) :=
  limits.is_limit.mk
    fun (s : limits.cone (discrete.functor f)) =>
      subtype.val
        (limits.binary_fan.is_limit.lift' t₂ (nat_trans.app (limits.cone.π s) (ulift.up 0))
          (limits.is_limit.lift t₁
            (limits.cone.mk (limits.cone.X s)
              (discrete.nat_trans
                fun (i : discrete (ulift (fin n))) =>
                  nat_trans.app (limits.cone.π s) (ulift.up (fin.succ (ulift.down i)))))))

/--
If `C` has a terminal object and binary products, then it has a product for objects indexed by
`ulift (fin n)`.
This is a helper lemma for `has_finite_products_of_has_binary_and_terminal`, which is more general
than this.
-/
/--
If `C` has a terminal object and binary products, then it has limits of shape
`discrete (ulift (fin n))` for any `n : ℕ`.
This is a helper lemma for `has_finite_products_of_has_binary_and_terminal`, which is more general
than this.
-/
/-- If `C` has a terminal object and binary products, then it has finite products. -/
theorem has_finite_products_of_has_binary_and_terminal {C : Type u} [category C]
    [limits.has_binary_products C] [limits.has_terminal C] : limits.has_finite_products C :=
  sorry

/--
If `F` preserves the terminal object and binary products, then it preserves products indexed by
`ulift (fin n)` for any `n`.
-/
def preserves_fin_of_preserves_binary_and_terminal {C : Type u} [category C] {D : Type u'}
    [category D] (F : C ⥤ D) [limits.preserves_limits_of_shape (discrete limits.walking_pair) F]
    [limits.preserves_limits_of_shape (discrete pempty) F] [limits.has_finite_products C] (n : ℕ)
    (f : ulift (fin n) → C) : limits.preserves_limit (discrete.functor f) F :=
  sorry

/--
If `F` preserves the terminal object and binary products, then it preserves limits of shape
`discrete (ulift (fin n))`.
-/
def preserves_ulift_fin_of_preserves_binary_and_terminal {C : Type u} [category C] {D : Type u'}
    [category D] (F : C ⥤ D) [limits.preserves_limits_of_shape (discrete limits.walking_pair) F]
    [limits.preserves_limits_of_shape (discrete pempty) F] [limits.has_finite_products C] (n : ℕ) :
    limits.preserves_limits_of_shape (discrete (ulift (fin n))) F :=
  limits.preserves_limits_of_shape.mk
    fun (K : discrete (ulift (fin n)) ⥤ C) =>
      let this : discrete.functor (functor.obj K) ≅ K :=
        discrete.nat_iso
          fun (i : discrete (discrete (ulift (fin n)))) =>
            iso.refl (functor.obj (discrete.functor (functor.obj K)) i);
      limits.preserves_limit_of_iso_diagram F this

/-- If `F` preserves the terminal object and binary products then it preserves finite products. -/
def preserves_finite_products_of_preserves_binary_and_terminal {C : Type u} [category C]
    {D : Type u'} [category D] (F : C ⥤ D)
    [limits.preserves_limits_of_shape (discrete limits.walking_pair) F]
    [limits.preserves_limits_of_shape (discrete pempty) F] [limits.has_finite_products C]
    (J : Type v) [fintype J] : limits.preserves_limits_of_shape (discrete J) F :=
  trunc.rec_on_subsingleton (fintype.equiv_fin J)
    fun (e : J ≃ fin (fintype.card J)) =>
      limits.preserves_limits_of_shape_of_equiv
        (equivalence.symm (discrete.equivalence (equiv.trans e (equiv.symm equiv.ulift)))) F

end Mathlib