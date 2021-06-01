/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury G. Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.set.intervals.ord_connected
import Mathlib.order.filter.lift
import Mathlib.order.filter.at_top_bot
import Mathlib.PostPort

universes u_1 l u_2 

namespace Mathlib

/-!
# Convergence of intervals

If both `a` and `b` tend to some filter `l₁`, sometimes this implies that `Ixx a b` tends to
`l₂.lift' powerset`, i.e., for any `s ∈ l₂` eventually `Ixx a b` becomes a subset of `s`.  Here and
below `Ixx` is one of `Icc`, `Ico`, `Ioc`, and `Ioo`. We define `filter.tendsto_Ixx_class Ixx l₁ l₂`
to be a typeclass representing this property.

The instances provide the best `l₂` for a given `l₁`. In many cases `l₁ = l₂` but sometimes we can
drop an endpoint from an interval: e.g., we prove `tendsto_Ixx_class Ico (𝓟 $ Iic a) (𝓟 $ Iio a)`,
i.e., if `u₁ n` and `u₂ n` belong eventually to `Iic a`, then the interval `Ico (u₁ n) (u₂ n)` is
eventually included in `Iio a`.

The next table shows “output” filters `l₂` for different values of `Ixx` and `l₁`. The instances
that need topology are defined in `topology/algebra/ordered`.

| Input filter |  `Ixx = Icc`  |  `Ixx = Ico`  |  `Ixx = Ioc`  |  `Ixx = Ioo`  |
| -----------: | :-----------: | :-----------: | :-----------: | :-----------: |
|     `at_top` |    `at_top`   |    `at_top`   |    `at_top`   |    `at_top`   |
|     `at_bot` |    `at_bot`   |    `at_bot`   |    `at_bot`   |    `at_bot`   |
|     `pure a` |    `pure a`   |      `⊥`      |      `⊥`      |      `⊥`      |
|  `𝓟 (Iic a)` |  `𝓟 (Iic a)`  |  `𝓟 (Iio a)`  |  `𝓟 (Iic a)`  |  `𝓟 (Iio a)`  |
|  `𝓟 (Ici a)` |  `𝓟 (Ici a)`  |  `𝓟 (Ici a)`  |  `𝓟 (Ioi a)`  |  `𝓟 (Ioi a)`  |
|  `𝓟 (Ioi a)` |  `𝓟 (Ioi a)`  |  `𝓟 (Ioi a)`  |  `𝓟 (Ioi a)`  |  `𝓟 (Ioi a)`  |
|  `𝓟 (Iio a)` |  `𝓟 (Iio a)`  |  `𝓟 (Iio a)`  |  `𝓟 (Iio a)`  |  `𝓟 (Iio a)`  |
|        `𝓝 a` |     `𝓝 a`     |     `𝓝 a`     |     `𝓝 a`     |     `𝓝 a`     |
| `𝓝[Iic a] b` |  `𝓝[Iic a] b` |  `𝓝[Iio a] b` |  `𝓝[Iic a] b` |  `𝓝[Iio a] b` |
| `𝓝[Ici a] b` |  `𝓝[Ici a] b` |  `𝓝[Ici a] b` |  `𝓝[Ioi a] b` |  `𝓝[Ioi a] b` |
| `𝓝[Ioi a] b` |  `𝓝[Ioi a] b` |  `𝓝[Ioi a] b` |  `𝓝[Ioi a] b` |  `𝓝[Ioi a] b` |
| `𝓝[Iio a] b` |  `𝓝[Iio a] b` |  `𝓝[Iio a] b` |  `𝓝[Iio a] b` |  `𝓝[Iio a] b` |

-/

namespace filter


/-- A pair of filters `l₁`, `l₂` has `tendsto_Ixx_class Ixx` property if `Ixx a b` tends to
`l₂.lift' powerset` as `a` and `b` tend to `l₁`. In all instances `Ixx` is one of `Icc`, `Ico`,
`Ioc`, or `Ioo`. The instances provide the best `l₂` for a given `l₁`. In many cases `l₁ = l₂` but
sometimes we can drop an endpoint from an interval: e.g., we prove `tendsto_Ixx_class Ico (𝓟 $ Iic
a) (𝓟 $ Iio a)`, i.e., if `u₁ n` and `u₂ n` belong eventually to `Iic a`, then the interval `Ico (u₁
n) (u₂ n)` is eventually included in `Iio a`.

We mark `l₂` as an `out_param` so that Lean can automatically find an appropriate `l₂` based on
`Ixx` and `l₁`. This way, e.g., `tendsto.Ico h₁ h₂` works without specifying explicitly `l₂`. -/
class tendsto_Ixx_class {α : Type u_1} [preorder α] (Ixx : α → α → set α) (l₁ : filter α)
    (l₂ : outParam (filter α))
    where
  tendsto_Ixx :
    tendsto (fun (p : α × α) => Ixx (prod.fst p) (prod.snd p)) (filter.prod l₁ l₁)
      (filter.lift' l₂ set.powerset)

theorem tendsto.Icc {α : Type u_1} {β : Type u_2} [preorder α] {l₁ : filter α} {l₂ : filter α}
    [tendsto_Ixx_class set.Icc l₁ l₂] {lb : filter β} {u₁ : β → α} {u₂ : β → α}
    (h₁ : tendsto u₁ lb l₁) (h₂ : tendsto u₂ lb l₁) :
    tendsto (fun (x : β) => set.Icc (u₁ x) (u₂ x)) lb (filter.lift' l₂ set.powerset) :=
  tendsto.comp tendsto_Ixx_class.tendsto_Ixx (tendsto.prod_mk h₁ h₂)

theorem tendsto.Ioc {α : Type u_1} {β : Type u_2} [preorder α] {l₁ : filter α} {l₂ : filter α}
    [tendsto_Ixx_class set.Ioc l₁ l₂] {lb : filter β} {u₁ : β → α} {u₂ : β → α}
    (h₁ : tendsto u₁ lb l₁) (h₂ : tendsto u₂ lb l₁) :
    tendsto (fun (x : β) => set.Ioc (u₁ x) (u₂ x)) lb (filter.lift' l₂ set.powerset) :=
  tendsto.comp tendsto_Ixx_class.tendsto_Ixx (tendsto.prod_mk h₁ h₂)

theorem tendsto.Ico {α : Type u_1} {β : Type u_2} [preorder α] {l₁ : filter α} {l₂ : filter α}
    [tendsto_Ixx_class set.Ico l₁ l₂] {lb : filter β} {u₁ : β → α} {u₂ : β → α}
    (h₁ : tendsto u₁ lb l₁) (h₂ : tendsto u₂ lb l₁) :
    tendsto (fun (x : β) => set.Ico (u₁ x) (u₂ x)) lb (filter.lift' l₂ set.powerset) :=
  tendsto.comp tendsto_Ixx_class.tendsto_Ixx (tendsto.prod_mk h₁ h₂)

theorem tendsto.Ioo {α : Type u_1} {β : Type u_2} [preorder α] {l₁ : filter α} {l₂ : filter α}
    [tendsto_Ixx_class set.Ioo l₁ l₂] {lb : filter β} {u₁ : β → α} {u₂ : β → α}
    (h₁ : tendsto u₁ lb l₁) (h₂ : tendsto u₂ lb l₁) :
    tendsto (fun (x : β) => set.Ioo (u₁ x) (u₂ x)) lb (filter.lift' l₂ set.powerset) :=
  tendsto.comp tendsto_Ixx_class.tendsto_Ixx (tendsto.prod_mk h₁ h₂)

theorem tendsto_Ixx_class_principal {α : Type u_1} [preorder α] {s : set α} {t : set α}
    {Ixx : α → α → set α} :
    tendsto_Ixx_class Ixx (principal s) (principal t) ↔
        ∀ (x : α), x ∈ s → ∀ (y : α), y ∈ s → Ixx x y ⊆ t :=
  sorry

theorem tendsto_Ixx_class_inf {α : Type u_1} [preorder α] {l₁ : filter α} {l₁' : filter α}
    {l₂ : filter α} {l₂' : filter α} {Ixx : α → α → set α} [h : tendsto_Ixx_class Ixx l₁ l₂]
    [h' : tendsto_Ixx_class Ixx l₁' l₂'] : tendsto_Ixx_class Ixx (l₁ ⊓ l₁') (l₂ ⊓ l₂') :=
  sorry

theorem tendsto_Ixx_class_of_subset {α : Type u_1} [preorder α] {l₁ : filter α} {l₂ : filter α}
    {Ixx : α → α → set α} {Ixx' : α → α → set α} (h : ∀ (a b : α), Ixx a b ⊆ Ixx' a b)
    [h' : tendsto_Ixx_class Ixx' l₁ l₂] : tendsto_Ixx_class Ixx l₁ l₂ :=
  tendsto_Ixx_class.mk
    (tendsto_lift'_powerset_mono tendsto_Ixx_class.tendsto_Ixx
      (eventually_of_forall (iff.mpr prod.forall h)))

theorem has_basis.tendsto_Ixx_class {α : Type u_1} [preorder α] {ι : Type u_2} {p : ι → Prop}
    {s : ι → set α} {l : filter α} (hl : has_basis l p s) {Ixx : α → α → set α}
    (H : ∀ (i : ι), p i → ∀ (x : α), x ∈ s i → ∀ (y : α), y ∈ s i → Ixx x y ⊆ s i) :
    tendsto_Ixx_class Ixx l l :=
  sorry

protected instance tendsto_Icc_at_top_at_top {α : Type u_1} [preorder α] :
    tendsto_Ixx_class set.Icc at_top at_top :=
  has_basis.tendsto_Ixx_class (has_basis_infi_principal_finite fun (a : α) => set.Ici a)
    fun (s : set α) (hs : set.finite s) =>
      set.ord_connected_bInter fun (i : α) (hi : i ∈ s) => set.ord_connected_Ici

protected instance tendsto_Ico_at_top_at_top {α : Type u_1} [preorder α] :
    tendsto_Ixx_class set.Ico at_top at_top :=
  tendsto_Ixx_class_of_subset fun (_x _x_1 : α) => set.Ico_subset_Icc_self

protected instance tendsto_Ioc_at_top_at_top {α : Type u_1} [preorder α] :
    tendsto_Ixx_class set.Ioc at_top at_top :=
  tendsto_Ixx_class_of_subset fun (_x _x_1 : α) => set.Ioc_subset_Icc_self

protected instance tendsto_Ioo_at_top_at_top {α : Type u_1} [preorder α] :
    tendsto_Ixx_class set.Ioo at_top at_top :=
  tendsto_Ixx_class_of_subset fun (_x _x_1 : α) => set.Ioo_subset_Icc_self

protected instance tendsto_Icc_at_bot_at_bot {α : Type u_1} [preorder α] :
    tendsto_Ixx_class set.Icc at_bot at_bot :=
  has_basis.tendsto_Ixx_class (has_basis_infi_principal_finite fun (a : α) => set.Iic a)
    fun (s : set α) (hs : set.finite s) =>
      set.ord_connected_bInter fun (i : α) (hi : i ∈ s) => set.ord_connected_Iic

protected instance tendsto_Ico_at_bot_at_bot {α : Type u_1} [preorder α] :
    tendsto_Ixx_class set.Ico at_bot at_bot :=
  tendsto_Ixx_class_of_subset fun (_x _x_1 : α) => set.Ico_subset_Icc_self

protected instance tendsto_Ioc_at_bot_at_bot {α : Type u_1} [preorder α] :
    tendsto_Ixx_class set.Ioc at_bot at_bot :=
  tendsto_Ixx_class_of_subset fun (_x _x_1 : α) => set.Ioc_subset_Icc_self

protected instance tendsto_Ioo_at_bot_at_bot {α : Type u_1} [preorder α] :
    tendsto_Ixx_class set.Ioo at_bot at_bot :=
  tendsto_Ixx_class_of_subset fun (_x _x_1 : α) => set.Ioo_subset_Icc_self

protected instance ord_connected.tendsto_Icc {α : Type u_1} [preorder α] {s : set α}
    [set.ord_connected s] : tendsto_Ixx_class set.Icc (principal s) (principal s) :=
  iff.mpr tendsto_Ixx_class_principal _inst_2

protected instance tendsto_Ico_Ici_Ici {α : Type u_1} [preorder α] {a : α} :
    tendsto_Ixx_class set.Ico (principal (set.Ici a)) (principal (set.Ici a)) :=
  tendsto_Ixx_class_of_subset fun (_x _x_1 : α) => set.Ico_subset_Icc_self

protected instance tendsto_Ico_Ioi_Ioi {α : Type u_1} [preorder α] {a : α} :
    tendsto_Ixx_class set.Ico (principal (set.Ioi a)) (principal (set.Ioi a)) :=
  tendsto_Ixx_class_of_subset fun (_x _x_1 : α) => set.Ico_subset_Icc_self

protected instance tendsto_Ico_Iic_Iio {α : Type u_1} [preorder α] {a : α} :
    tendsto_Ixx_class set.Ico (principal (set.Iic a)) (principal (set.Iio a)) :=
  iff.mpr tendsto_Ixx_class_principal
    fun (a_1 : α) (ha : a_1 ∈ set.Iic a) (b : α) (hb : b ∈ set.Iic a) (x : α)
      (hx : x ∈ set.Ico a_1 b) => lt_of_lt_of_le (and.right hx) hb

protected instance tendsto_Ico_Iio_Iio {α : Type u_1} [preorder α] {a : α} :
    tendsto_Ixx_class set.Ico (principal (set.Iio a)) (principal (set.Iio a)) :=
  tendsto_Ixx_class_of_subset fun (_x _x_1 : α) => set.Ico_subset_Icc_self

protected instance tendsto_Ioc_Ici_Ioi {α : Type u_1} [preorder α] {a : α} :
    tendsto_Ixx_class set.Ioc (principal (set.Ici a)) (principal (set.Ioi a)) :=
  iff.mpr tendsto_Ixx_class_principal
    fun (x : α) (hx : x ∈ set.Ici a) (y : α) (hy : y ∈ set.Ici a) (t : α) (ht : t ∈ set.Ioc x y) =>
      lt_of_le_of_lt hx (and.left ht)

protected instance tendsto_Ioc_Iic_Iic {α : Type u_1} [preorder α] {a : α} :
    tendsto_Ixx_class set.Ioc (principal (set.Iic a)) (principal (set.Iic a)) :=
  tendsto_Ixx_class_of_subset fun (_x _x_1 : α) => set.Ioc_subset_Icc_self

protected instance tendsto_Ioc_Iio_Iio {α : Type u_1} [preorder α] {a : α} :
    tendsto_Ixx_class set.Ioc (principal (set.Iio a)) (principal (set.Iio a)) :=
  tendsto_Ixx_class_of_subset fun (_x _x_1 : α) => set.Ioc_subset_Icc_self

protected instance tendsto_Ioc_Ioi_Ioi {α : Type u_1} [preorder α] {a : α} :
    tendsto_Ixx_class set.Ioc (principal (set.Ioi a)) (principal (set.Ioi a)) :=
  tendsto_Ixx_class_of_subset fun (_x _x_1 : α) => set.Ioc_subset_Icc_self

protected instance tendsto_Ioo_Ici_Ioi {α : Type u_1} [preorder α] {a : α} :
    tendsto_Ixx_class set.Ioo (principal (set.Ici a)) (principal (set.Ioi a)) :=
  tendsto_Ixx_class_of_subset fun (_x _x_1 : α) => set.Ioo_subset_Ioc_self

protected instance tendsto_Ioo_Iic_Iio {α : Type u_1} [preorder α] {a : α} :
    tendsto_Ixx_class set.Ioo (principal (set.Iic a)) (principal (set.Iio a)) :=
  tendsto_Ixx_class_of_subset fun (_x _x_1 : α) => set.Ioo_subset_Ico_self

protected instance tendsto_Ioo_Ioi_Ioi {α : Type u_1} [preorder α] {a : α} :
    tendsto_Ixx_class set.Ioo (principal (set.Ioi a)) (principal (set.Ioi a)) :=
  tendsto_Ixx_class_of_subset fun (_x _x_1 : α) => set.Ioo_subset_Ioc_self

protected instance tendsto_Ioo_Iio_Iio {α : Type u_1} [preorder α] {a : α} :
    tendsto_Ixx_class set.Ioo (principal (set.Iio a)) (principal (set.Iio a)) :=
  tendsto_Ixx_class_of_subset fun (_x _x_1 : α) => set.Ioo_subset_Ioc_self

protected instance tendsto_Icc_pure_pure {β : Type u_2} [partial_order β] {a : β} :
    tendsto_Ixx_class set.Icc (pure a) (pure a) :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (tendsto_Ixx_class set.Icc (pure a) (pure a)))
        (Eq.symm (principal_singleton a))))
    (iff.mpr tendsto_Ixx_class_principal set.ord_connected_singleton)

protected instance tendsto_Ico_pure_bot {β : Type u_2} [partial_order β] {a : β} :
    tendsto_Ixx_class set.Ico (pure a) ⊥ :=
  sorry

protected instance tendsto_Ioc_pure_bot {β : Type u_2} [partial_order β] {a : β} :
    tendsto_Ixx_class set.Ioc (pure a) ⊥ :=
  sorry

protected instance tendsto_Ioo_pure_bot {β : Type u_2} [partial_order β] {a : β} :
    tendsto_Ixx_class set.Ioo (pure a) ⊥ :=
  tendsto_Ixx_class_of_subset fun (_x _x_1 : β) => set.Ioo_subset_Ioc_self

end Mathlib