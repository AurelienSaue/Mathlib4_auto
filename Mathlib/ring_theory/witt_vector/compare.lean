/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.ring_theory.witt_vector.truncated
import Mathlib.ring_theory.witt_vector.identities
import Mathlib.data.padics.ring_homs
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!

# Comparison isomorphism between `witt_vector p (zmod p)` and `ℤ_[p]`

We construct a ring isomorphism between `witt_vector p (zmod p)` and `ℤ_[p]`.
This isomorphism follows from the fact that both satisfy the universal property
of the inverse limit of `zmod (p^n)`.

## Main declarations

* `witt_vector.to_zmod_pow`: a family of compatible ring homs `𝕎 (zmod p) → zmod (p^k)`
* `witt_vector.equiv`: the isomorphism

-/

namespace truncated_witt_vector


theorem eq_of_le_of_cast_pow_eq_zero (p : ℕ) [hp : fact (nat.prime p)] (n : ℕ) (R : Type u_1) [comm_ring R] [char_p R p] (i : ℕ) (hin : i ≤ n) (hpi : ↑p ^ i = 0) : i = n := sorry

theorem card_zmod (p : ℕ) [hp : fact (nat.prime p)] (n : ℕ) : fintype.card (truncated_witt_vector p n (zmod p)) = p ^ n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (fintype.card (truncated_witt_vector p n (zmod p)) = p ^ n)) (card p n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (fintype.card (zmod p) ^ n = p ^ n)) (zmod.card p))) (Eq.refl (p ^ n)))

theorem char_p_zmod (p : ℕ) [hp : fact (nat.prime p)] (n : ℕ) : char_p (truncated_witt_vector p n (zmod p)) (p ^ n) :=
  char_p_of_prime_pow_injective (truncated_witt_vector p n (zmod p)) p n (card_zmod p n)
    (eq_of_le_of_cast_pow_eq_zero p n (zmod p))

/--
The unique isomorphism between `zmod p^n` and `truncated_witt_vector p n (zmod p)`.

This isomorphism exists, because `truncated_witt_vector p n (zmod p)` is a finite ring
with characteristic and cardinality `p^n`.
-/
def zmod_equiv_trunc (p : ℕ) [hp : fact (nat.prime p)] (n : ℕ) : zmod (p ^ n) ≃+* truncated_witt_vector p n (zmod p) :=
  zmod.ring_equiv (truncated_witt_vector p n (zmod p)) (card_zmod p n)

theorem zmod_equiv_trunc_apply (p : ℕ) [hp : fact (nat.prime p)] (n : ℕ) {x : zmod (p ^ n)} : coe_fn (zmod_equiv_trunc p n) x = coe_fn (zmod.cast_hom (dvd_refl (p ^ n)) (truncated_witt_vector p n (zmod p))) x :=
  rfl

/--
The following diagram commutes:
```text
          zmod (p^n) ----------------------------> zmod (p^m)
            |                                        |
            |                                        |
            v                                        v
truncated_witt_vector p n (zmod p) ----> truncated_witt_vector p m (zmod p)
```
Here the vertical arrows are `truncated_witt_vector.zmod_equiv_trunc`,
the horizontal arrow at the top is `zmod.cast_hom`,
and the horizontal arrow at the bottom is `truncated_witt_vector.truncate`.
-/
theorem commutes (p : ℕ) [hp : fact (nat.prime p)] (n : ℕ) {m : ℕ} (hm : n ≤ m) : ring_hom.comp (truncate hm) (ring_equiv.to_ring_hom (zmod_equiv_trunc p m)) =
  ring_hom.comp (ring_equiv.to_ring_hom (zmod_equiv_trunc p n)) (zmod.cast_hom (pow_dvd_pow p hm) (zmod (p ^ n))) :=
  ring_hom.ext_zmod (ring_hom.comp (truncate hm) (ring_equiv.to_ring_hom (zmod_equiv_trunc p m)))
    (ring_hom.comp (ring_equiv.to_ring_hom (zmod_equiv_trunc p n)) (zmod.cast_hom (pow_dvd_pow p hm) (zmod (p ^ n))))

theorem commutes' (p : ℕ) [hp : fact (nat.prime p)] (n : ℕ) {m : ℕ} (hm : n ≤ m) (x : zmod (p ^ m)) : coe_fn (truncate hm) (coe_fn (zmod_equiv_trunc p m) x) =
  coe_fn (zmod_equiv_trunc p n) (coe_fn (zmod.cast_hom (pow_dvd_pow p hm) (zmod (p ^ n))) x) := sorry

theorem commutes_symm' (p : ℕ) [hp : fact (nat.prime p)] (n : ℕ) {m : ℕ} (hm : n ≤ m) (x : truncated_witt_vector p m (zmod p)) : coe_fn (ring_equiv.symm (zmod_equiv_trunc p n)) (coe_fn (truncate hm) x) =
  coe_fn (zmod.cast_hom (pow_dvd_pow p hm) (zmod (p ^ n))) (coe_fn (ring_equiv.symm (zmod_equiv_trunc p m)) x) := sorry

/--
The following diagram commutes:
```text
truncated_witt_vector p n (zmod p) ----> truncated_witt_vector p m (zmod p)
            |                                        |
            |                                        |
            v                                        v
          zmod (p^n) ----------------------------> zmod (p^m)
```
Here the vertical arrows are `(truncated_witt_vector.zmod_equiv_trunc p _).symm`,
the horizontal arrow at the top is `zmod.cast_hom`,
and the horizontal arrow at the bottom is `truncated_witt_vector.truncate`.
-/
theorem commutes_symm (p : ℕ) [hp : fact (nat.prime p)] (n : ℕ) {m : ℕ} (hm : n ≤ m) : ring_hom.comp (ring_equiv.to_ring_hom (ring_equiv.symm (zmod_equiv_trunc p n))) (truncate hm) =
  ring_hom.comp (zmod.cast_hom (pow_dvd_pow p hm) (zmod (p ^ n)))
    (ring_equiv.to_ring_hom (ring_equiv.symm (zmod_equiv_trunc p m))) :=
  ring_hom.ext fun (x : truncated_witt_vector p m (zmod p)) => commutes_symm' p n hm x

end truncated_witt_vector


namespace witt_vector


/--
`to_zmod_pow` is a family of compatible ring homs. We get this family by composing
`truncated_witt_vector.zmod_equiv_trunc` (in right-to-left direction)
with `witt_vector.truncate`.
-/
def to_zmod_pow (p : ℕ) [hp : fact (nat.prime p)] (k : ℕ) : witt_vector p (zmod p) →+* zmod (p ^ k) :=
  ring_hom.comp (ring_equiv.to_ring_hom (ring_equiv.symm (truncated_witt_vector.zmod_equiv_trunc p k))) (truncate k)

theorem to_zmod_pow_compat (p : ℕ) [hp : fact (nat.prime p)] (m : ℕ) (n : ℕ) (h : m ≤ n) : ring_hom.comp (zmod.cast_hom (pow_dvd_pow p h) (zmod (p ^ m))) (to_zmod_pow p n) = to_zmod_pow p m := sorry

/--
`to_padic_int` lifts `to_zmod_pow : 𝕎 (zmod p) →+* zmod (p ^ k)` to a ring hom to `ℤ_[p]`
using `padic_int.lift`, the universal property of `ℤ_[p]`.
-/
def to_padic_int (p : ℕ) [hp : fact (nat.prime p)] : witt_vector p (zmod p) →+* padic_int p :=
  padic_int.lift (to_zmod_pow_compat p)

theorem zmod_equiv_trunc_compat (p : ℕ) [hp : fact (nat.prime p)] (k₁ : ℕ) (k₂ : ℕ) (hk : k₁ ≤ k₂) : ring_hom.comp (truncated_witt_vector.truncate hk)
    (ring_hom.comp (ring_equiv.to_ring_hom (truncated_witt_vector.zmod_equiv_trunc p k₂)) (padic_int.to_zmod_pow k₂)) =
  ring_hom.comp (ring_equiv.to_ring_hom (truncated_witt_vector.zmod_equiv_trunc p k₁)) (padic_int.to_zmod_pow k₁) := sorry

/--
`from_padic_int` uses `witt_vector.lift` to lift `truncated_witt_vector.zmod_equiv_trunc`
composed with `padic_int.to_zmod_pow` to a ring hom `ℤ_[p] →+* 𝕎 (zmod p)`.
-/
def from_padic_int (p : ℕ) [hp : fact (nat.prime p)] : padic_int p →+* witt_vector p (zmod p) :=
  lift
    (fun (k : ℕ) =>
      ring_hom.comp (ring_equiv.to_ring_hom (truncated_witt_vector.zmod_equiv_trunc p k)) (padic_int.to_zmod_pow k))
    (zmod_equiv_trunc_compat p)

theorem to_padic_int_comp_from_padic_int (p : ℕ) [hp : fact (nat.prime p)] : ring_hom.comp (to_padic_int p) (from_padic_int p) = ring_hom.id (padic_int p) := sorry

theorem to_padic_int_comp_from_padic_int_ext (p : ℕ) [hp : fact (nat.prime p)] (x : padic_int p) : coe_fn (ring_hom.comp (to_padic_int p) (from_padic_int p)) x = coe_fn (ring_hom.id (padic_int p)) x := sorry

theorem from_padic_int_comp_to_padic_int (p : ℕ) [hp : fact (nat.prime p)] : ring_hom.comp (from_padic_int p) (to_padic_int p) = ring_hom.id (witt_vector p (zmod p)) := sorry

theorem from_padic_int_comp_to_padic_int_ext (p : ℕ) [hp : fact (nat.prime p)] (x : witt_vector p (zmod p)) : coe_fn (ring_hom.comp (from_padic_int p) (to_padic_int p)) x = coe_fn (ring_hom.id (witt_vector p (zmod p))) x := sorry

/--
The ring of Witt vectors over `zmod p` is isomorphic to the ring of `p`-adic integers. This
equivalence is witnessed by `witt_vector.to_padic_int` with inverse `witt_vector.from_padic_int`.
-/
def equiv (p : ℕ) [hp : fact (nat.prime p)] : witt_vector p (zmod p) ≃+* padic_int p :=
  ring_equiv.mk (⇑(to_padic_int p)) (⇑(from_padic_int p)) (from_padic_int_comp_to_padic_int_ext p)
    (to_padic_int_comp_from_padic_int_ext p) sorry sorry

