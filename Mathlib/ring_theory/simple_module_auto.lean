/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors : Aaron Anderson
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.linear_algebra.basic
import Mathlib.order.atoms
import PostPort

universes u_1 u_2 u_3 

namespace Mathlib

/-!
# Simple Modules

## Main Definitions
  * `is_simple_module` indicates that a module has no proper submodules
  (the only submodules are `⊥` and `⊤`).
  * A `division_ring` structure on the endomorphism ring of a simple module.

## Main Results
  * Schur's Lemma: `bijective_or_eq_zero` shows that a linear map between simple modules
  is either bijective or 0, leading to a `division_ring` structure on the endomorphism ring.

## TODO
  * Semisimple modules, Artin-Wedderburn Theory
  * Unify with the work on Schur's Lemma in a category theory context

-/

/-- A module is simple when it has only two submodules, `⊥` and `⊤`. -/
def is_simple_module (R : Type u_1) [comm_ring R] (M : Type u_2) [add_comm_group M] [module R M]  :=
  is_simple_lattice (submodule R M)

-- Making this an instance causes the linter to complain of "dangerous instances"

theorem is_simple_module.nontrivial (R : Type u_1) [comm_ring R] (M : Type u_2) [add_comm_group M] [module R M] [is_simple_module R M] : nontrivial M := sorry

namespace linear_map


theorem injective_or_eq_zero {R : Type u_1} [comm_ring R] {M : Type u_2} [add_comm_group M] [module R M] {N : Type u_3} [add_comm_group N] [module R N] [is_simple_module R M] (f : linear_map R M N) : function.injective ⇑f ∨ f = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (function.injective ⇑f ∨ f = 0)) (Eq.symm (propext ker_eq_bot))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (ker f = ⊥ ∨ f = 0)) (Eq.symm (propext ker_eq_top)))) (eq_bot_or_eq_top (ker f)))

theorem injective_of_ne_zero {R : Type u_1} [comm_ring R] {M : Type u_2} [add_comm_group M] [module R M] {N : Type u_3} [add_comm_group N] [module R N] [is_simple_module R M] {f : linear_map R M N} (h : f ≠ 0) : function.injective ⇑f :=
  or.resolve_right (injective_or_eq_zero f) h

theorem surjective_or_eq_zero {R : Type u_1} [comm_ring R] {M : Type u_2} [add_comm_group M] [module R M] {N : Type u_3} [add_comm_group N] [module R N] [is_simple_module R N] (f : linear_map R M N) : function.surjective ⇑f ∨ f = 0 := sorry

theorem surjective_of_ne_zero {R : Type u_1} [comm_ring R] {M : Type u_2} [add_comm_group M] [module R M] {N : Type u_3} [add_comm_group N] [module R N] [is_simple_module R N] {f : linear_map R M N} (h : f ≠ 0) : function.surjective ⇑f :=
  or.resolve_right (surjective_or_eq_zero f) h

/-- Schur's Lemma for linear maps between (possibly distinct) simple modules -/
theorem bijective_or_eq_zero {R : Type u_1} [comm_ring R] {M : Type u_2} [add_comm_group M] [module R M] {N : Type u_3} [add_comm_group N] [module R N] [is_simple_module R M] [is_simple_module R N] (f : linear_map R M N) : function.bijective ⇑f ∨ f = 0 :=
  dite (f = 0) (fun (h : f = 0) => Or.inr h)
    fun (h : ¬f = 0) => or.intro_left (f = 0) { left := injective_of_ne_zero h, right := surjective_of_ne_zero h }

theorem bijective_of_ne_zero {R : Type u_1} [comm_ring R] {M : Type u_2} [add_comm_group M] [module R M] {N : Type u_3} [add_comm_group N] [module R N] [is_simple_module R M] [is_simple_module R N] {f : linear_map R M N} (h : f ≠ 0) : function.bijective ⇑f :=
  or.resolve_right (bijective_or_eq_zero f) h

/-- Schur's Lemma makes the endomorphism ring of a simple module a division ring. -/
protected instance module.End.division_ring {R : Type u_1} [comm_ring R] {M : Type u_2} [add_comm_group M] [module R M] [DecidableEq (module.End R M)] [is_simple_module R M] : division_ring (module.End R M) :=
  division_ring.mk ring.add sorry ring.zero sorry sorry ring.neg ring.sub sorry sorry ring.mul sorry ring.one sorry sorry
    sorry sorry
    (fun (f : module.End R M) =>
      dite (f = 0) (fun (h : f = 0) => 0)
        fun (h : ¬f = 0) => inverse f (equiv.inv_fun (equiv.of_bijective (⇑f) (bijective_of_ne_zero h))) sorry sorry)
    (div_inv_monoid.div._default ring.mul sorry ring.one sorry sorry
      fun (f : module.End R M) =>
        dite (f = 0) (fun (h : f = 0) => 0)
          fun (h : ¬f = 0) => inverse f (equiv.inv_fun (equiv.of_bijective (⇑f) (bijective_of_ne_zero h))) sorry sorry)
    sorry sorry sorry

