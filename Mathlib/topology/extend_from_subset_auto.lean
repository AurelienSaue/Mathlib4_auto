/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Anatole Dedecker
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.topology.separation
import PostPort

universes u_2 u_1 

namespace Mathlib

/-!
# Extending a function from a subset

The main definition of this file is `extend_from A f` where `f : X → Y`
and `A : set X`. This defines a new function `g : X → Y` which maps any
`x₀ : X` to the limit of `f` as `x` tends to `x₀`, if such a limit exists.

This is analoguous to the way `dense_inducing.extend` "extends" a function
`f : X → Z` to a function `g : Y → Z` along a dense inducing `i : X → Y`.

The main theorem we prove about this definition is `continuous_on_extend_from`
which states that, for `extend_from A f` to be continuous on a set `B ⊆ closure A`,
it suffices that `f` converges within `A` at any point of `B`, provided that
`f` is a function to a regular space.

-/

/-- Extend a function from a set `A`. The resulting function `g` is such that
at any `x₀`, if `f` converges to some `y` as `x` tends to `x₀` within `A`,
then `g x₀` is defined to be one of these `y`. Else, `g x₀` could be anything. -/
def extend_from {X : Type u_1} {Y : Type u_2} [topological_space X] [topological_space Y] (A : set X) (f : X → Y) : X → Y :=
  fun (x : X) => lim (nhds_within x A) f

/-- If `f` converges to some `y` as `x` tends to `x₀` within `A`,
then `f` tends to `extend_from A f x` as `x` tends to `x₀`. -/
theorem tendsto_extend_from {X : Type u_1} {Y : Type u_2} [topological_space X] [topological_space Y] {A : set X} {f : X → Y} {x : X} (h : ∃ (y : Y), filter.tendsto f (nhds_within x A) (nhds y)) : filter.tendsto f (nhds_within x A) (nhds (extend_from A f x)) :=
  tendsto_nhds_lim h

theorem extend_from_eq {X : Type u_1} {Y : Type u_2} [topological_space X] [topological_space Y] [t2_space Y] {A : set X} {f : X → Y} {x : X} {y : Y} (hx : x ∈ closure A) (hf : filter.tendsto f (nhds_within x A) (nhds y)) : extend_from A f x = y :=
  tendsto_nhds_unique (tendsto_nhds_lim (Exists.intro y hf)) hf

theorem extend_from_extends {X : Type u_1} {Y : Type u_2} [topological_space X] [topological_space Y] [t2_space Y] {f : X → Y} {A : set X} (hf : continuous_on f A) (x : X) (H : x ∈ A) : extend_from A f x = f x :=
  extend_from_eq (subset_closure x_in) (hf x x_in)

/-- If `f` is a function to a regular space `Y` which has a limit within `A` at any
point of a set `B ⊆ closure A`, then `extend_from A f` is continuous on `B`. -/
theorem continuous_on_extend_from {X : Type u_1} {Y : Type u_2} [topological_space X] [topological_space Y] [regular_space Y] {f : X → Y} {A : set X} {B : set X} (hB : B ⊆ closure A) (hf : ∀ (x : X), x ∈ B → ∃ (y : Y), filter.tendsto f (nhds_within x A) (nhds y)) : continuous_on (extend_from A f) B := sorry

/-- If a function `f` to a regular space `Y` has a limit within a
dense set `A` for any `x`, then `extend_from A f` is continuous. -/
theorem continuous_extend_from {X : Type u_1} {Y : Type u_2} [topological_space X] [topological_space Y] [regular_space Y] {f : X → Y} {A : set X} (hA : dense A) (hf : ∀ (x : X), ∃ (y : Y), filter.tendsto f (nhds_within x A) (nhds y)) : continuous (extend_from A f) := sorry

