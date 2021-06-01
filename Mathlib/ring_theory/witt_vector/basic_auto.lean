/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.mv_polynomial.counit
import Mathlib.data.mv_polynomial.invertible
import Mathlib.ring_theory.witt_vector.defs
import Mathlib.PostPort

universes u_4 u_5 u_1 u_2 

namespace Mathlib

/-!
# Witt vectors

This file verifies that the ring operations on `witt_vector p R`
satisfy the axioms of a commutative ring.

## Main definitions

* `witt_vector.map`: lifts a ring homomorphism `R →+* S` to a ring homomorphism `𝕎 R →+* 𝕎 S`.
* `witt_vector.ghost_component n x`: evaluates the `n`th Witt polynomial
  on the first `n` coefficients of `x`, producing a value in `R`.
  This is a ring homomorphism.
* `witt_vector.ghost_map`: a ring homomorphism `𝕎 R →+* (ℕ → R)`, obtained by packaging
  all the ghost components together.
  If `p` is invertible in `R`, then the ghost map is an equivalence,
  which we use to define the ring operations on `𝕎 R`.
* `witt_vector.comm_ring`: the ring structure induced by the ghost components.

## Notation

We use notation `𝕎 R`, entered `\bbW`, for the Witt vectors over `R`.

## Implementation details

As we prove that the ghost components respect the ring operations, we face a number of repetitive
proofs. To avoid duplicating code we factor these proofs into a custom tactic, only slightly more
powerful than a tactic macro. This tactic is not particularly useful outside of its applications
in this file.
-/

namespace witt_vector


/-- `f : α → β` induces a map from `𝕎 α` to `𝕎 β` by applying `f` componentwise.
If `f` is a ring homomorphism, then so is `f`, see `witt_vector.map f`. -/
def map_fun {p : ℕ} {α : Type u_4} {β : Type u_5} (f : α → β) : witt_vector p α → witt_vector p β :=
  fun (x : witt_vector p α) => f ∘ x

namespace map_fun


theorem injective {p : ℕ} {α : Type u_4} {β : Type u_5} (f : α → β) (hf : function.injective f) :
    function.injective (map_fun f) :=
  fun (x y : witt_vector p α) (h : map_fun f x = map_fun f y) =>
    funext fun (n : ℕ) => hf (congr_fun h n)

theorem surjective {p : ℕ} {α : Type u_4} {β : Type u_5} (f : α → β) (hf : function.surjective f) :
    function.surjective (map_fun f) :=
  sorry

/-- Auxiliary tactic for showing that `map_fun` respects the ring operations. -/
/- We do not tag these lemmas as `@[simp]` because they will be bundled in `map` later on. -/

theorem zero {p : ℕ} {R : Type u_1} {S : Type u_2} [hp : fact (nat.prime p)] [comm_ring R]
    [comm_ring S] (f : R →+* S) : map_fun (⇑f) 0 = 0 :=
  sorry

theorem one {p : ℕ} {R : Type u_1} {S : Type u_2} [hp : fact (nat.prime p)] [comm_ring R]
    [comm_ring S] (f : R →+* S) : map_fun (⇑f) 1 = 1 :=
  sorry

theorem add {p : ℕ} {R : Type u_1} {S : Type u_2} [hp : fact (nat.prime p)] [comm_ring R]
    [comm_ring S] (f : R →+* S) (x : witt_vector p R) (y : witt_vector p R) :
    map_fun (⇑f) (x + y) = map_fun (⇑f) x + map_fun (⇑f) y :=
  sorry

theorem sub {p : ℕ} {R : Type u_1} {S : Type u_2} [hp : fact (nat.prime p)] [comm_ring R]
    [comm_ring S] (f : R →+* S) (x : witt_vector p R) (y : witt_vector p R) :
    map_fun (⇑f) (x - y) = map_fun (⇑f) x - map_fun (⇑f) y :=
  sorry

theorem mul {p : ℕ} {R : Type u_1} {S : Type u_2} [hp : fact (nat.prime p)] [comm_ring R]
    [comm_ring S] (f : R →+* S) (x : witt_vector p R) (y : witt_vector p R) :
    map_fun (⇑f) (x * y) = map_fun (⇑f) x * map_fun (⇑f) y :=
  sorry

theorem neg {p : ℕ} {R : Type u_1} {S : Type u_2} [hp : fact (nat.prime p)] [comm_ring R]
    [comm_ring S] (f : R →+* S) (x : witt_vector p R) : map_fun (⇑f) (-x) = -map_fun (⇑f) x :=
  sorry

end map_fun


end witt_vector


/-- An auxiliary tactic for proving that `ghost_fun` respects the ring operations. -/
namespace witt_vector


/-- Evaluates the `n`th Witt polynomial on the first `n` coefficients of `x`,
producing a value in `R`.
This function will be bundled as the ring homomorphism `witt_vector.ghost_map`
once the ring structure is available,
but we rely on it to set up the ring structure in the first place. -/
/- The following lemmas are not `@[simp]` because they will be bundled in `ghost_map` later on. -/

/-- The bijection between `𝕎 R` and `ℕ → R`, under the assumption that `p` is invertible in `R`.
In `witt_vector.ghost_equiv` we upgrade this to an isomorphism of rings. -/
/-- The commutative ring structure on `𝕎 R`. -/
protected instance comm_ring (p : ℕ) (R : Type u_1) [hp : fact (nat.prime p)] [comm_ring R] :
    comm_ring (witt_vector p R) :=
  function.surjective.comm_ring_sub (map_fun ⇑(mv_polynomial.counit R)) sorry sorry sorry sorry
    sorry sorry sorry

/-- `witt_vector.map f` is the ring homomorphism `𝕎 R →+* 𝕎 S` naturally induced
by a ring homomorphism `f : R →+* S`. It acts coefficientwise. -/
def map {p : ℕ} {R : Type u_1} {S : Type u_2} [hp : fact (nat.prime p)] [comm_ring R] [comm_ring S]
    (f : R →+* S) : witt_vector p R →+* witt_vector p S :=
  ring_hom.mk (map_fun ⇑f) (map_fun.one f) (map_fun.mul f) (map_fun.zero f) (map_fun.add f)

theorem map_injective {p : ℕ} {R : Type u_1} {S : Type u_2} [hp : fact (nat.prime p)] [comm_ring R]
    [comm_ring S] (f : R →+* S) (hf : function.injective ⇑f) : function.injective ⇑(map f) :=
  map_fun.injective (⇑f) hf

theorem map_surjective {p : ℕ} {R : Type u_1} {S : Type u_2} [hp : fact (nat.prime p)] [comm_ring R]
    [comm_ring S] (f : R →+* S) (hf : function.surjective ⇑f) : function.surjective ⇑(map f) :=
  map_fun.surjective (⇑f) hf

@[simp] theorem map_coeff {p : ℕ} {R : Type u_1} {S : Type u_2} [hp : fact (nat.prime p)]
    [comm_ring R] [comm_ring S] (f : R →+* S) (x : witt_vector p R) (n : ℕ) :
    coeff (coe_fn (map f) x) n = coe_fn f (coeff x n) :=
  rfl

/-- `witt_vector.ghost_map` is a ring homomorphism that maps each Witt vector
to the sequence of its ghost components. -/
def ghost_map {p : ℕ} {R : Type u_1} [hp : fact (nat.prime p)] [comm_ring R] :
    witt_vector p R →+* ℕ → R :=
  ring_hom.mk ghost_fun ghost_fun_one ghost_fun_mul ghost_fun_zero ghost_fun_add

/-- Evaluates the `n`th Witt polynomial on the first `n` coefficients of `x`,
producing a value in `R`. -/
def ghost_component {p : ℕ} {R : Type u_1} [hp : fact (nat.prime p)] [comm_ring R] (n : ℕ) :
    witt_vector p R →+* R :=
  ring_hom.comp (ring_hom.apply (fun (i : ℕ) => R) n) ghost_map

theorem ghost_component_apply {p : ℕ} {R : Type u_1} [hp : fact (nat.prime p)] [comm_ring R] (n : ℕ)
    (x : witt_vector p R) :
    coe_fn (ghost_component n) x = coe_fn (mv_polynomial.aeval (coeff x)) (witt_polynomial p ℤ n) :=
  rfl

@[simp] theorem ghost_map_apply {p : ℕ} {R : Type u_1} [hp : fact (nat.prime p)] [comm_ring R]
    (x : witt_vector p R) (n : ℕ) : coe_fn ghost_map x n = coe_fn (ghost_component n) x :=
  rfl

/-- `witt_vector.ghost_map` is a ring isomorphism when `p` is invertible in `R`. -/
def ghost_equiv (p : ℕ) (R : Type u_1) [hp : fact (nat.prime p)] [comm_ring R] [invertible ↑p] :
    witt_vector p R ≃+* (ℕ → R) :=
  ring_equiv.mk (ring_hom.to_fun ghost_map) (equiv.inv_fun (ghost_equiv' p R)) sorry sorry sorry
    sorry

@[simp] theorem ghost_equiv_coe (p : ℕ) (R : Type u_1) [hp : fact (nat.prime p)] [comm_ring R]
    [invertible ↑p] : ↑(ghost_equiv p R) = ghost_map :=
  rfl

theorem ghost_map.bijective_of_invertible (p : ℕ) (R : Type u_1) [hp : fact (nat.prime p)]
    [comm_ring R] [invertible ↑p] : function.bijective ⇑ghost_map :=
  ring_equiv.bijective (ghost_equiv p R)

end Mathlib