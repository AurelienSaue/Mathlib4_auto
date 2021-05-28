/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.monoid_algebra
import Mathlib.algebra.invertible
import Mathlib.algebra.char_p.basic
import Mathlib.linear_algebra.basis
import Mathlib.PostPort

universes u 

namespace Mathlib

/-!
# Maschke's theorem

We prove Maschke's theorem for finite groups,
in the formulation that every submodule of a `k[G]` module has a complement,
when `k` is a field with `¬(ring_char k ∣ fintype.card G)`.

We do the core computation in greater generality.
For any `[comm_ring k]` in which  `[invertible (fintype.card G : k)]`,
and a `k[G]`-linear map `i : V → W` which admits a `k`-linear retraction `π`,
we produce a `k[G]`-linear retraction by
taking the average over `G` of the conjugates of `π`.

## Future work
It's not so far to give the usual statement, that every finite dimensional representation
of a finite group is semisimple (i.e. a direct sum of irreducibles).
-/

-- At first we work with any `[comm_ring k]`, and add the assumption that

-- `[invertible (fintype.card G : k)]` when it is required.

/-!
We now do the key calculation in Maschke's theorem.

Given `V → W`, an inclusion of `k[G]` modules,,
assume we have some retraction `π` (i.e. `∀ v, π (i v) = v`),
just as a `k`-linear map.
(When `k` is a field, this will be available cheaply, by choosing a basis.)

We now construct a retraction of the inclusion as a `k[G]`-linear map,
by the formula
$$ \frac{1}{|G|} \sum_{g \in G} g⁻¹ • π(g • -). $$
-/

namespace linear_map


/--
We define the conjugate of `π` by `g`, as a `k`-linear map.
-/
def conjugate {k : Type u} [comm_ring k] {G : Type u} [group G] {V : Type u} [add_comm_group V] [module k V] [module (monoid_algebra k G) V] [is_scalar_tower k (monoid_algebra k G) V] {W : Type u} [add_comm_group W] [module k W] [module (monoid_algebra k G) W] [is_scalar_tower k (monoid_algebra k G) W] (π : linear_map k W V) (g : G) : linear_map k W V :=
  comp (comp (monoid_algebra.group_smul.linear_map k V (g⁻¹)) π) (monoid_algebra.group_smul.linear_map k W g)

theorem conjugate_i {k : Type u} [comm_ring k] {G : Type u} [group G] {V : Type u} [add_comm_group V] [module k V] [module (monoid_algebra k G) V] [is_scalar_tower k (monoid_algebra k G) V] {W : Type u} [add_comm_group W] [module k W] [module (monoid_algebra k G) W] [is_scalar_tower k (monoid_algebra k G) W] (π : linear_map k W V) (i : linear_map (monoid_algebra k G) V W) (h : ∀ (v : V), coe_fn π (coe_fn i v) = v) (g : G) (v : V) : coe_fn (conjugate π g) (coe_fn i v) = v := sorry

/--
The sum of the conjugates of `π` by each element `g : G`, as a `k`-linear map.

(We postpone dividing by the size of the group as long as possible.)
-/
def sum_of_conjugates {k : Type u} [comm_ring k] (G : Type u) [group G] {V : Type u} [add_comm_group V] [module k V] [module (monoid_algebra k G) V] [is_scalar_tower k (monoid_algebra k G) V] {W : Type u} [add_comm_group W] [module k W] [module (monoid_algebra k G) W] [is_scalar_tower k (monoid_algebra k G) W] (π : linear_map k W V) [fintype G] : linear_map k W V :=
  finset.sum finset.univ fun (g : G) => conjugate π g

/--
In fact, the sum over `g : G` of the conjugate of `π` by `g` is a `k[G]`-linear map.
-/
def sum_of_conjugates_equivariant {k : Type u} [comm_ring k] (G : Type u) [group G] {V : Type u} [add_comm_group V] [module k V] [module (monoid_algebra k G) V] [is_scalar_tower k (monoid_algebra k G) V] {W : Type u} [add_comm_group W] [module k W] [module (monoid_algebra k G) W] [is_scalar_tower k (monoid_algebra k G) W] (π : linear_map k W V) [fintype G] : linear_map (monoid_algebra k G) W V :=
  monoid_algebra.equivariant_of_linear_of_comm (sum_of_conjugates G π) sorry

/--
We construct our `k[G]`-linear retraction of `i` as
$$ \frac{1}{|G|} \sum_{g \in G} g⁻¹ • π(g • -). $$
-/
def equivariant_projection {k : Type u} [comm_ring k] (G : Type u) [group G] {V : Type u} [add_comm_group V] [module k V] [module (monoid_algebra k G) V] [is_scalar_tower k (monoid_algebra k G) V] {W : Type u} [add_comm_group W] [module k W] [module (monoid_algebra k G) W] [is_scalar_tower k (monoid_algebra k G) W] (π : linear_map k W V) [fintype G] [inv : invertible ↑(fintype.card G)] : linear_map (monoid_algebra k G) W V :=
  ⅟ • sum_of_conjugates_equivariant G π

theorem equivariant_projection_condition {k : Type u} [comm_ring k] (G : Type u) [group G] {V : Type u} [add_comm_group V] [module k V] [module (monoid_algebra k G) V] [is_scalar_tower k (monoid_algebra k G) V] {W : Type u} [add_comm_group W] [module k W] [module (monoid_algebra k G) W] [is_scalar_tower k (monoid_algebra k G) W] (π : linear_map k W V) (i : linear_map (monoid_algebra k G) V W) (h : ∀ (v : V), coe_fn π (coe_fn i v) = v) [fintype G] [inv : invertible ↑(fintype.card G)] (v : V) : coe_fn (equivariant_projection G π) (coe_fn i v) = v := sorry

end linear_map


-- Now we work over a `[field k]`, and replace the assumption `[invertible (fintype.card G : k)]`

-- with `¬(ring_char k ∣ fintype.card G)`.

theorem monoid_algebra.exists_left_inverse_of_injective {k : Type u} [field k] {G : Type u} [fintype G] [group G] {V : Type u} [add_comm_group V] [module k V] [module (monoid_algebra k G) V] [is_scalar_tower k (monoid_algebra k G) V] {W : Type u} [add_comm_group W] [module k W] [module (monoid_algebra k G) W] [is_scalar_tower k (monoid_algebra k G) W] (not_dvd : ¬ring_char k ∣ fintype.card G) (f : linear_map (monoid_algebra k G) V W) (hf : linear_map.ker f = ⊥) : ∃ (g : linear_map (monoid_algebra k G) W V), linear_map.comp g f = linear_map.id := sorry

theorem monoid_algebra.submodule.exists_is_compl {k : Type u} [field k] {G : Type u} [fintype G] [group G] {V : Type u} [add_comm_group V] [module k V] [module (monoid_algebra k G) V] [is_scalar_tower k (monoid_algebra k G) V] (not_dvd : ¬ring_char k ∣ fintype.card G) (p : submodule (monoid_algebra k G) V) : ∃ (q : submodule (monoid_algebra k G) V), is_compl p q := sorry

