/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury G. Kudryashov
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.dynamics.fixed_points.basic
import Mathlib.data.set.lattice
import Mathlib.data.pnat.basic
import PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Periodic points

A point `x : α` is a periodic point of `f : α → α` of period `n` if `f^[n] x = x`.

## Main definitions

* `is_periodic_pt f n x` : `x` is a periodic point of `f` of period `n`, i.e. `f^[n] x = x`.
  We do not require `n > 0` in the definition.
* `pts_of_period f n` : the set `{x | is_periodic_pt f n x}`. Note that `n` is not required to
  be the minimal period of `x`.
* `periodic_pts f` : the set of all periodic points of `f`.
* `minimal_period f x` : the minimal period of a point `x` under an endomorphism `f` or zero
  if `x` is not a periodic point of `f`.

## Main statements

We provide “dot syntax”-style operations on terms of the form `h : is_periodic_pt f n x` including
arithmetic operations on `n` and `h.map (hg : semiconj_by g f f')`. We also prove that `f`
is bijective on each set `pts_of_period f n` and on `periodic_pts f`. Finally, we prove that `x`
is a periodic point of `f` of period `n` if and only if `minimal_period f x | n`.

## References

* https://en.wikipedia.org/wiki/Periodic_point

-/

namespace function


/-- A point `x` is a periodic point of `f : α → α` of period `n` if `f^[n] x = x`.
Note that we do not require `0 < n` in this definition. Many theorems about periodic points
need this assumption. -/
def is_periodic_pt {α : Type u_1} (f : α → α) (n : ℕ) (x : α)  :=
  is_fixed_pt (nat.iterate f n) x

/-- A fixed point of `f` is a periodic point of `f` of any prescribed period. -/
theorem is_fixed_pt.is_periodic_pt {α : Type u_1} {f : α → α} {x : α} (hf : is_fixed_pt f x) (n : ℕ) : is_periodic_pt f n x :=
  is_fixed_pt.iterate hf n

/-- For the identity map, all points are periodic. -/
theorem is_periodic_id {α : Type u_1} (n : ℕ) (x : α) : is_periodic_pt id n x :=
  is_fixed_pt.is_periodic_pt (is_fixed_pt_id x) n

/-- Any point is a periodic point of period `0`. -/
theorem is_periodic_pt_zero {α : Type u_1} (f : α → α) (x : α) : is_periodic_pt f 0 x :=
  is_fixed_pt_id x

namespace is_periodic_pt


protected instance decidable {α : Type u_1} [DecidableEq α] {f : α → α} {n : ℕ} {x : α} : Decidable (is_periodic_pt f n x) :=
  is_fixed_pt.decidable

protected theorem is_fixed_pt {α : Type u_1} {f : α → α} {x : α} {n : ℕ} (hf : is_periodic_pt f n x) : is_fixed_pt (nat.iterate f n) x :=
  hf

protected theorem map {α : Type u_1} {β : Type u_2} {fa : α → α} {fb : β → β} {x : α} {n : ℕ} (hx : is_periodic_pt fa n x) {g : α → β} (hg : semiconj g fa fb) : is_periodic_pt fb n (g x) :=
  is_fixed_pt.map hx (semiconj.iterate_right hg n)

theorem apply_iterate {α : Type u_1} {f : α → α} {x : α} {n : ℕ} (hx : is_periodic_pt f n x) (m : ℕ) : is_periodic_pt f n (nat.iterate f m x) :=
  is_periodic_pt.map hx (commute.iterate_self f m)

protected theorem apply {α : Type u_1} {f : α → α} {x : α} {n : ℕ} (hx : is_periodic_pt f n x) : is_periodic_pt f n (f x) :=
  apply_iterate hx 1

protected theorem add {α : Type u_1} {f : α → α} {x : α} {m : ℕ} {n : ℕ} (hn : is_periodic_pt f n x) (hm : is_periodic_pt f m x) : is_periodic_pt f (n + m) x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_periodic_pt f (n + m) x)) (equations._eqn_1 f (n + m) x)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (is_fixed_pt (nat.iterate f (n + m)) x)) (iterate_add f n m)))
      (is_fixed_pt.comp hn hm))

theorem left_of_add {α : Type u_1} {f : α → α} {x : α} {m : ℕ} {n : ℕ} (hn : is_periodic_pt f (n + m) x) (hm : is_periodic_pt f m x) : is_periodic_pt f n x := sorry

theorem right_of_add {α : Type u_1} {f : α → α} {x : α} {m : ℕ} {n : ℕ} (hn : is_periodic_pt f (n + m) x) (hm : is_periodic_pt f n x) : is_periodic_pt f m x :=
  left_of_add (eq.mp (Eq._oldrec (Eq.refl (is_periodic_pt f (n + m) x)) (add_comm n m)) hn) hm

protected theorem sub {α : Type u_1} {f : α → α} {x : α} {m : ℕ} {n : ℕ} (hm : is_periodic_pt f m x) (hn : is_periodic_pt f n x) : is_periodic_pt f (m - n) x := sorry

protected theorem mul_const {α : Type u_1} {f : α → α} {x : α} {m : ℕ} (hm : is_periodic_pt f m x) (n : ℕ) : is_periodic_pt f (m * n) x := sorry

protected theorem const_mul {α : Type u_1} {f : α → α} {x : α} {m : ℕ} (hm : is_periodic_pt f m x) (n : ℕ) : is_periodic_pt f (n * m) x := sorry

theorem trans_dvd {α : Type u_1} {f : α → α} {x : α} {m : ℕ} (hm : is_periodic_pt f m x) {n : ℕ} (hn : m ∣ n) : is_periodic_pt f n x := sorry

protected theorem iterate {α : Type u_1} {f : α → α} {x : α} {n : ℕ} (hf : is_periodic_pt f n x) (m : ℕ) : is_periodic_pt (nat.iterate f m) n x := sorry

protected theorem mod {α : Type u_1} {f : α → α} {x : α} {m : ℕ} {n : ℕ} (hm : is_periodic_pt f m x) (hn : is_periodic_pt f n x) : is_periodic_pt f (m % n) x :=
  left_of_add (eq.mp (Eq._oldrec (Eq.refl (is_periodic_pt f m x)) (Eq.symm (nat.mod_add_div m n))) hm)
    (is_periodic_pt.mul_const hn (m / n))

protected theorem gcd {α : Type u_1} {f : α → α} {x : α} {m : ℕ} {n : ℕ} (hm : is_periodic_pt f m x) (hn : is_periodic_pt f n x) : is_periodic_pt f (nat.gcd m n) x := sorry

/-- If `f` sends two periodic points `x` and `y` of the same positive period to the same point,
then `x = y`. For a similar statement about points of different periods see `eq_of_apply_eq`. -/
theorem eq_of_apply_eq_same {α : Type u_1} {f : α → α} {x : α} {y : α} {n : ℕ} (hx : is_periodic_pt f n x) (hy : is_periodic_pt f n y) (hn : 0 < n) (h : f x = f y) : x = y := sorry

/-- If `f` sends two periodic points `x` and `y` of positive periods to the same point,
then `x = y`. -/
theorem eq_of_apply_eq {α : Type u_1} {f : α → α} {x : α} {y : α} {m : ℕ} {n : ℕ} (hx : is_periodic_pt f m x) (hy : is_periodic_pt f n y) (hm : 0 < m) (hn : 0 < n) (h : f x = f y) : x = y :=
  eq_of_apply_eq_same (is_periodic_pt.mul_const hx n) (is_periodic_pt.const_mul hy m) (mul_pos hm hn) h

end is_periodic_pt


/-- The set of periodic points of a given (possibly non-minimal) period. -/
def pts_of_period {α : Type u_1} (f : α → α) (n : ℕ) : set α :=
  set_of fun (x : α) => is_periodic_pt f n x

@[simp] theorem mem_pts_of_period {α : Type u_1} {f : α → α} {x : α} {n : ℕ} : x ∈ pts_of_period f n ↔ is_periodic_pt f n x :=
  iff.rfl

theorem semiconj.maps_to_pts_of_period {α : Type u_1} {β : Type u_2} {fa : α → α} {fb : β → β} {g : α → β} (h : semiconj g fa fb) (n : ℕ) : set.maps_to g (pts_of_period fa n) (pts_of_period fb n) :=
  semiconj.maps_to_fixed_pts (semiconj.iterate_right h n)

theorem bij_on_pts_of_period {α : Type u_1} (f : α → α) {n : ℕ} (hn : 0 < n) : set.bij_on f (pts_of_period f n) (pts_of_period f n) := sorry

theorem directed_pts_of_period_pnat {α : Type u_1} (f : α → α) : directed has_subset.subset fun (n : ℕ+) => pts_of_period f ↑n := sorry

/-- The set of periodic points of a map `f : α → α`. -/
def periodic_pts {α : Type u_1} (f : α → α) : set α :=
  set_of fun (x : α) => ∃ (n : ℕ), ∃ (H : n > 0), is_periodic_pt f n x

theorem mk_mem_periodic_pts {α : Type u_1} {f : α → α} {x : α} {n : ℕ} (hn : 0 < n) (hx : is_periodic_pt f n x) : x ∈ periodic_pts f :=
  Exists.intro n (Exists.intro hn hx)

theorem mem_periodic_pts {α : Type u_1} {f : α → α} {x : α} : x ∈ periodic_pts f ↔ ∃ (n : ℕ), ∃ (H : n > 0), is_periodic_pt f n x :=
  iff.rfl

theorem bUnion_pts_of_period {α : Type u_1} (f : α → α) : (set.Union fun (n : ℕ) => set.Union fun (H : n > 0) => pts_of_period f n) = periodic_pts f := sorry

theorem Union_pnat_pts_of_period {α : Type u_1} (f : α → α) : (set.Union fun (n : ℕ+) => pts_of_period f ↑n) = periodic_pts f :=
  Eq.trans supr_subtype (bUnion_pts_of_period f)

theorem bij_on_periodic_pts {α : Type u_1} (f : α → α) : set.bij_on f (periodic_pts f) (periodic_pts f) :=
  Union_pnat_pts_of_period f ▸
    set.bij_on_Union_of_directed (directed_pts_of_period_pnat f) fun (i : ℕ+) => bij_on_pts_of_period f (pnat.pos i)

theorem semiconj.maps_to_periodic_pts {α : Type u_1} {β : Type u_2} {fa : α → α} {fb : β → β} {g : α → β} (h : semiconj g fa fb) : set.maps_to g (periodic_pts fa) (periodic_pts fb) := sorry

/-- Minimal period of a point `x` under an endomorphism `f`. If `x` is not a periodic point of `f`,
then `minimal_period f x = 0`. -/
def minimal_period {α : Type u_1} (f : α → α) (x : α) : ℕ :=
  dite (x ∈ periodic_pts f) (fun (h : x ∈ periodic_pts f) => nat.find h) fun (h : ¬x ∈ periodic_pts f) => 0

theorem is_periodic_pt_minimal_period {α : Type u_1} (f : α → α) (x : α) : is_periodic_pt f (minimal_period f x) x := sorry

theorem minimal_period_pos_of_mem_periodic_pts {α : Type u_1} {f : α → α} {x : α} (hx : x ∈ periodic_pts f) : 0 < minimal_period f x := sorry

theorem is_periodic_pt.minimal_period_pos {α : Type u_1} {f : α → α} {x : α} {n : ℕ} (hn : 0 < n) (hx : is_periodic_pt f n x) : 0 < minimal_period f x :=
  minimal_period_pos_of_mem_periodic_pts (mk_mem_periodic_pts hn hx)

theorem minimal_period_pos_iff_mem_periodic_pts {α : Type u_1} {f : α → α} {x : α} : 0 < minimal_period f x ↔ x ∈ periodic_pts f := sorry

theorem is_periodic_pt.minimal_period_le {α : Type u_1} {f : α → α} {x : α} {n : ℕ} (hn : 0 < n) (hx : is_periodic_pt f n x) : minimal_period f x ≤ n := sorry

theorem is_periodic_pt.eq_zero_of_lt_minimal_period {α : Type u_1} {f : α → α} {x : α} {n : ℕ} (hx : is_periodic_pt f n x) (hn : n < minimal_period f x) : n = 0 :=
  Eq.symm
    (or.resolve_right (eq_or_lt_of_le (nat.zero_le n))
      fun (hn0 : 0 < n) => iff.mpr not_lt (is_periodic_pt.minimal_period_le hn0 hx) hn)

theorem is_periodic_pt.minimal_period_dvd {α : Type u_1} {f : α → α} {x : α} {n : ℕ} (hx : is_periodic_pt f n x) : minimal_period f x ∣ n := sorry

theorem is_periodic_pt_iff_minimal_period_dvd {α : Type u_1} {f : α → α} {x : α} {n : ℕ} : is_periodic_pt f n x ↔ minimal_period f x ∣ n :=
  { mp := is_periodic_pt.minimal_period_dvd,
    mpr := fun (h : minimal_period f x ∣ n) => is_periodic_pt.trans_dvd (is_periodic_pt_minimal_period f x) h }

