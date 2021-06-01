/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.analysis.normed_space.basic
import Mathlib.algebra.ring.basic
import Mathlib.analysis.asymptotics
import Mathlib.PostPort

universes u_1 l 

namespace Mathlib

/-!
# Ordered normed spaces

In this file, we define classes for fields and groups that are both normed and ordered.
These are mostly useful to avoid diamonds during type class inference.
-/

/-- A `normed_linear_ordered_group` is an additive group that is both a `normed_group` and
    a `linear_ordered_add_comm_group`. This class is necessary to avoid diamonds. -/
class normed_linear_ordered_group (α : Type u_1)
    extends has_norm α, linear_ordered_add_comm_group α, metric_space α where
  dist_eq : ∀ (x y : α), dist x y = norm (x - y)

protected instance normed_linear_ordered_group.to_normed_group (α : Type u_1)
    [normed_linear_ordered_group α] : normed_group α :=
  normed_group.mk normed_linear_ordered_group.dist_eq

/-- A `normed_linear_ordered_field` is a field that is both a `normed_field` and a
    `linear_ordered_field`. This class is necessary to avoid diamonds. -/
class normed_linear_ordered_field (α : Type u_1)
    extends linear_ordered_field α, metric_space α, has_norm α where
  dist_eq : ∀ (x y : α), dist x y = norm (x - y)
  norm_mul' : ∀ (a b : α), norm (a * b) = norm a * norm b

protected instance normed_linear_ordered_field.to_normed_field (α : Type u_1)
    [normed_linear_ordered_field α] : normed_field α :=
  normed_field.mk normed_linear_ordered_field.dist_eq normed_linear_ordered_field.norm_mul'

protected instance normed_linear_ordered_field.to_normed_linear_ordered_group (α : Type u_1)
    [normed_linear_ordered_field α] : normed_linear_ordered_group α :=
  normed_linear_ordered_group.mk normed_linear_ordered_field.dist_eq

theorem tendsto_pow_div_pow_at_top_of_lt {α : Type u_1} [normed_linear_ordered_field α]
    [order_topology α] {p : ℕ} {q : ℕ} (hpq : p < q) :
    filter.tendsto (fun (x : α) => x ^ p / x ^ q) filter.at_top (nhds 0) :=
  sorry

theorem is_o_pow_pow_at_top_of_lt {α : Type} [normed_linear_ordered_field α] [order_topology α]
    {p : ℕ} {q : ℕ} (hpq : p < q) :
    asymptotics.is_o (fun (x : α) => x ^ p) (fun (x : α) => x ^ q) filter.at_top :=
  sorry

end Mathlib