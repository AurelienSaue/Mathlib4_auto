/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.char_p.basic
import Mathlib.data.equiv.ring
import Mathlib.algebra.group_with_zero.power
import Mathlib.algebra.iterate_hom
import Mathlib.PostPort

universes u l v u_1 

namespace Mathlib

/-!
# The perfect closure of a field
-/

/-- A perfect ring is a ring of characteristic p that has p-th root. -/
class perfect_ring (R : Type u) [comm_semiring R] (p : ℕ) [fact (nat.prime p)] [char_p R p] 
where
  pth_root' : R → R
  frobenius_pth_root' : ∀ (x : R), coe_fn (frobenius R p) (pth_root' x) = x
  pth_root_frobenius' : ∀ (x : R), pth_root' (coe_fn (frobenius R p) x) = x

/-- Frobenius automorphism of a perfect ring. -/
def frobenius_equiv (R : Type u) [comm_semiring R] (p : ℕ) [fact (nat.prime p)] [char_p R p] [perfect_ring R p] : R ≃+* R :=
  ring_equiv.mk (ring_hom.to_fun (frobenius R p)) (perfect_ring.pth_root' p) perfect_ring.pth_root_frobenius'
    perfect_ring.frobenius_pth_root' sorry sorry

/-- `p`-th root of an element in a `perfect_ring` as a `ring_hom`. -/
def pth_root (R : Type u) [comm_semiring R] (p : ℕ) [fact (nat.prime p)] [char_p R p] [perfect_ring R p] : R →+* R :=
  ↑(ring_equiv.symm (frobenius_equiv R p))

@[simp] theorem coe_frobenius_equiv {R : Type u} [comm_semiring R] {p : ℕ} [fact (nat.prime p)] [char_p R p] [perfect_ring R p] : ⇑(frobenius_equiv R p) = ⇑(frobenius R p) :=
  rfl

@[simp] theorem coe_frobenius_equiv_symm {R : Type u} [comm_semiring R] {p : ℕ} [fact (nat.prime p)] [char_p R p] [perfect_ring R p] : ⇑(ring_equiv.symm (frobenius_equiv R p)) = ⇑(pth_root R p) :=
  rfl

@[simp] theorem frobenius_pth_root {R : Type u} [comm_semiring R] {p : ℕ} [fact (nat.prime p)] [char_p R p] [perfect_ring R p] (x : R) : coe_fn (frobenius R p) (coe_fn (pth_root R p) x) = x :=
  ring_equiv.apply_symm_apply (frobenius_equiv R p) x

@[simp] theorem pth_root_pow_p {R : Type u} [comm_semiring R] {p : ℕ} [fact (nat.prime p)] [char_p R p] [perfect_ring R p] (x : R) : coe_fn (pth_root R p) x ^ p = x :=
  frobenius_pth_root x

@[simp] theorem pth_root_frobenius {R : Type u} [comm_semiring R] {p : ℕ} [fact (nat.prime p)] [char_p R p] [perfect_ring R p] (x : R) : coe_fn (pth_root R p) (coe_fn (frobenius R p) x) = x :=
  ring_equiv.symm_apply_apply (frobenius_equiv R p) x

@[simp] theorem pth_root_pow_p' {R : Type u} [comm_semiring R] {p : ℕ} [fact (nat.prime p)] [char_p R p] [perfect_ring R p] (x : R) : coe_fn (pth_root R p) (x ^ p) = x :=
  pth_root_frobenius x

theorem left_inverse_pth_root_frobenius {R : Type u} [comm_semiring R] {p : ℕ} [fact (nat.prime p)] [char_p R p] [perfect_ring R p] : function.left_inverse ⇑(pth_root R p) ⇑(frobenius R p) :=
  pth_root_frobenius

theorem right_inverse_pth_root_frobenius {R : Type u} [comm_semiring R] {p : ℕ} [fact (nat.prime p)] [char_p R p] [perfect_ring R p] : function.right_inverse ⇑(pth_root R p) ⇑(frobenius R p) :=
  frobenius_pth_root

theorem commute_frobenius_pth_root {R : Type u} [comm_semiring R] {p : ℕ} [fact (nat.prime p)] [char_p R p] [perfect_ring R p] : function.commute ⇑(frobenius R p) ⇑(pth_root R p) :=
  fun (x : R) => Eq.trans (frobenius_pth_root x) (Eq.symm (pth_root_frobenius x))

theorem eq_pth_root_iff {R : Type u} [comm_semiring R] {p : ℕ} [fact (nat.prime p)] [char_p R p] [perfect_ring R p] {x : R} {y : R} : x = coe_fn (pth_root R p) y ↔ coe_fn (frobenius R p) x = y :=
  equiv.eq_symm_apply (ring_equiv.to_equiv (frobenius_equiv R p))

theorem pth_root_eq_iff {R : Type u} [comm_semiring R] {p : ℕ} [fact (nat.prime p)] [char_p R p] [perfect_ring R p] {x : R} {y : R} : coe_fn (pth_root R p) x = y ↔ x = coe_fn (frobenius R p) y :=
  equiv.symm_apply_eq (ring_equiv.to_equiv (frobenius_equiv R p))

theorem monoid_hom.map_pth_root {R : Type u} [comm_semiring R] {S : Type v} [comm_semiring S] (f : R →* S) {p : ℕ} [fact (nat.prime p)] [char_p R p] [perfect_ring R p] [char_p S p] [perfect_ring S p] (x : R) : coe_fn f (coe_fn (pth_root R p) x) = coe_fn (pth_root S p) (coe_fn f x) := sorry

theorem monoid_hom.map_iterate_pth_root {R : Type u} [comm_semiring R] {S : Type v} [comm_semiring S] (f : R →* S) {p : ℕ} [fact (nat.prime p)] [char_p R p] [perfect_ring R p] [char_p S p] [perfect_ring S p] (x : R) (n : ℕ) : coe_fn f (nat.iterate (⇑(pth_root R p)) n x) = nat.iterate (⇑(pth_root S p)) n (coe_fn f x) :=
  function.semiconj.iterate_right (monoid_hom.map_pth_root f) n x

theorem ring_hom.map_pth_root {R : Type u} [comm_semiring R] {S : Type v} [comm_semiring S] (g : R →+* S) {p : ℕ} [fact (nat.prime p)] [char_p R p] [perfect_ring R p] [char_p S p] [perfect_ring S p] (x : R) : coe_fn g (coe_fn (pth_root R p) x) = coe_fn (pth_root S p) (coe_fn g x) :=
  monoid_hom.map_pth_root (ring_hom.to_monoid_hom g) x

theorem ring_hom.map_iterate_pth_root {R : Type u} [comm_semiring R] {S : Type v} [comm_semiring S] (g : R →+* S) {p : ℕ} [fact (nat.prime p)] [char_p R p] [perfect_ring R p] [char_p S p] [perfect_ring S p] (x : R) (n : ℕ) : coe_fn g (nat.iterate (⇑(pth_root R p)) n x) = nat.iterate (⇑(pth_root S p)) n (coe_fn g x) :=
  monoid_hom.map_iterate_pth_root (ring_hom.to_monoid_hom g) x n

theorem injective_pow_p {R : Type u} [comm_semiring R] (p : ℕ) [fact (nat.prime p)] [char_p R p] [perfect_ring R p] {x : R} {y : R} (hxy : x ^ p = y ^ p) : x = y :=
  function.left_inverse.injective left_inverse_pth_root_frobenius hxy

/-- `perfect_closure K p` is the quotient by this relation. -/
inductive perfect_closure.r (K : Type u) [comm_ring K] (p : ℕ) [fact (nat.prime p)] [char_p K p] : ℕ × K → ℕ × K → Prop
where
| intro : ∀ (n : ℕ) (x : K), perfect_closure.r K p (n, x) (n + 1, coe_fn (frobenius K p) x)

/-- The perfect closure is the smallest extension that makes frobenius surjective. -/
def perfect_closure (K : Type u) [comm_ring K] (p : ℕ) [fact (nat.prime p)] [char_p K p]  :=
  Quot sorry

namespace perfect_closure


/-- Constructor for `perfect_closure`. -/
def mk (K : Type u) [comm_ring K] (p : ℕ) [fact (nat.prime p)] [char_p K p] (x : ℕ × K) : perfect_closure K p :=
  Quot.mk (r K p) x

@[simp] theorem quot_mk_eq_mk (K : Type u) [comm_ring K] (p : ℕ) [fact (nat.prime p)] [char_p K p] (x : ℕ × K) : Quot.mk (r K p) x = mk K p x :=
  rfl

/-- Lift a function `ℕ × K → L` to a function on `perfect_closure K p`. -/
def lift_on {K : Type u} [comm_ring K] {p : ℕ} [fact (nat.prime p)] [char_p K p] {L : Type u_1} (x : perfect_closure K p) (f : ℕ × K → L) (hf : ∀ (x y : ℕ × K), r K p x y → f x = f y) : L :=
  quot.lift_on x f hf

@[simp] theorem lift_on_mk {K : Type u} [comm_ring K] {p : ℕ} [fact (nat.prime p)] [char_p K p] {L : Type u_1} (f : ℕ × K → L) (hf : ∀ (x y : ℕ × K), r K p x y → f x = f y) (x : ℕ × K) : lift_on (mk K p x) f hf = f x :=
  rfl

theorem induction_on {K : Type u} [comm_ring K] {p : ℕ} [fact (nat.prime p)] [char_p K p] (x : perfect_closure K p) {q : perfect_closure K p → Prop} (h : ∀ (x : ℕ × K), q (mk K p x)) : q x :=
  quot.induction_on x h

protected instance has_mul (K : Type u) [comm_ring K] (p : ℕ) [fact (nat.prime p)] [char_p K p] : Mul (perfect_closure K p) :=
  { mul :=
      Quot.lift
        (fun (x : ℕ × K) =>
          Quot.lift
            (fun (y : ℕ × K) =>
              mk K p
                (prod.fst x + prod.fst y,
                nat.iterate (⇑(frobenius K p)) (prod.fst y) (prod.snd x) *
                  nat.iterate (⇑(frobenius K p)) (prod.fst x) (prod.snd y)))
            (mul_aux_right K p x))
        sorry }

@[simp] theorem mk_mul_mk (K : Type u) [comm_ring K] (p : ℕ) [fact (nat.prime p)] [char_p K p] (x : ℕ × K) (y : ℕ × K) : mk K p x * mk K p y =
  mk K p
    (prod.fst x + prod.fst y,
    nat.iterate (⇑(frobenius K p)) (prod.fst y) (prod.snd x) * nat.iterate (⇑(frobenius K p)) (prod.fst x) (prod.snd y)) :=
  rfl

protected instance comm_monoid (K : Type u) [comm_ring K] (p : ℕ) [fact (nat.prime p)] [char_p K p] : comm_monoid (perfect_closure K p) :=
  comm_monoid.mk Mul.mul sorry (mk K p (0, 1)) sorry sorry sorry

theorem one_def (K : Type u) [comm_ring K] (p : ℕ) [fact (nat.prime p)] [char_p K p] : 1 = mk K p (0, 1) :=
  rfl

protected instance inhabited (K : Type u) [comm_ring K] (p : ℕ) [fact (nat.prime p)] [char_p K p] : Inhabited (perfect_closure K p) :=
  { default := 1 }

protected instance has_add (K : Type u) [comm_ring K] (p : ℕ) [fact (nat.prime p)] [char_p K p] : Add (perfect_closure K p) :=
  { add :=
      Quot.lift
        (fun (x : ℕ × K) =>
          Quot.lift
            (fun (y : ℕ × K) =>
              mk K p
                (prod.fst x + prod.fst y,
                nat.iterate (⇑(frobenius K p)) (prod.fst y) (prod.snd x) +
                  nat.iterate (⇑(frobenius K p)) (prod.fst x) (prod.snd y)))
            (add_aux_right K p x))
        sorry }

@[simp] theorem mk_add_mk (K : Type u) [comm_ring K] (p : ℕ) [fact (nat.prime p)] [char_p K p] (x : ℕ × K) (y : ℕ × K) : mk K p x + mk K p y =
  mk K p
    (prod.fst x + prod.fst y,
    nat.iterate (⇑(frobenius K p)) (prod.fst y) (prod.snd x) + nat.iterate (⇑(frobenius K p)) (prod.fst x) (prod.snd y)) :=
  rfl

protected instance has_neg (K : Type u) [comm_ring K] (p : ℕ) [fact (nat.prime p)] [char_p K p] : Neg (perfect_closure K p) :=
  { neg := Quot.lift (fun (x : ℕ × K) => mk K p (prod.fst x, -prod.snd x)) sorry }

@[simp] theorem neg_mk (K : Type u) [comm_ring K] (p : ℕ) [fact (nat.prime p)] [char_p K p] (x : ℕ × K) : -mk K p x = mk K p (prod.fst x, -prod.snd x) :=
  rfl

protected instance has_zero (K : Type u) [comm_ring K] (p : ℕ) [fact (nat.prime p)] [char_p K p] : HasZero (perfect_closure K p) :=
  { zero := mk K p (0, 0) }

theorem zero_def (K : Type u) [comm_ring K] (p : ℕ) [fact (nat.prime p)] [char_p K p] : 0 = mk K p (0, 0) :=
  rfl

theorem mk_zero (K : Type u) [comm_ring K] (p : ℕ) [fact (nat.prime p)] [char_p K p] (n : ℕ) : mk K p (n, 0) = 0 := sorry

theorem r.sound (K : Type u) [comm_ring K] (p : ℕ) [fact (nat.prime p)] [char_p K p] (m : ℕ) (n : ℕ) (x : K) (y : K) (H : nat.iterate (⇑(frobenius K p)) m x = y) : mk K p (n, x) = mk K p (m + n, y) := sorry

protected instance comm_ring (K : Type u) [comm_ring K] (p : ℕ) [fact (nat.prime p)] [char_p K p] : comm_ring (perfect_closure K p) :=
  comm_ring.mk Add.add sorry 0 sorry sorry Neg.neg (ring.sub._default Add.add sorry 0 sorry sorry Neg.neg) sorry sorry
    comm_monoid.mul sorry comm_monoid.one sorry sorry sorry sorry sorry

theorem eq_iff' (K : Type u) [comm_ring K] (p : ℕ) [fact (nat.prime p)] [char_p K p] (x : ℕ × K) (y : ℕ × K) : mk K p x = mk K p y ↔
  ∃ (z : ℕ),
    nat.iterate (⇑(frobenius K p)) (prod.fst y + z) (prod.snd x) =
      nat.iterate (⇑(frobenius K p)) (prod.fst x + z) (prod.snd y) := sorry

theorem nat_cast (K : Type u) [comm_ring K] (p : ℕ) [fact (nat.prime p)] [char_p K p] (n : ℕ) (x : ℕ) : ↑x = mk K p (n, ↑x) := sorry

theorem int_cast (K : Type u) [comm_ring K] (p : ℕ) [fact (nat.prime p)] [char_p K p] (x : ℤ) : ↑x = mk K p (0, ↑x) := sorry

theorem nat_cast_eq_iff (K : Type u) [comm_ring K] (p : ℕ) [fact (nat.prime p)] [char_p K p] (x : ℕ) (y : ℕ) : ↑x = ↑y ↔ ↑x = ↑y := sorry

protected instance char_p (K : Type u) [comm_ring K] (p : ℕ) [fact (nat.prime p)] [char_p K p] : char_p (perfect_closure K p) p :=
  char_p.mk
    fun (x : ℕ) =>
      eq.mpr (id (Eq._oldrec (Eq.refl (↑x = 0 ↔ p ∣ x)) (Eq.symm (propext (char_p.cast_eq_zero_iff K p x)))))
        (eq.mpr (id (Eq._oldrec (Eq.refl (↑x = 0 ↔ ↑x = 0)) (Eq.symm nat.cast_zero)))
          (eq.mpr (id (Eq._oldrec (Eq.refl (↑x = ↑0 ↔ ↑x = 0)) (propext (nat_cast_eq_iff K p x 0))))
            (eq.mpr (id (Eq._oldrec (Eq.refl (↑x = ↑0 ↔ ↑x = 0)) nat.cast_zero)) (iff.refl (↑x = 0)))))

theorem frobenius_mk (K : Type u) [comm_ring K] (p : ℕ) [fact (nat.prime p)] [char_p K p] (x : ℕ × K) : coe_fn (frobenius (perfect_closure K p) p) (mk K p x) = mk K p (prod.fst x, prod.snd x ^ p) := sorry

/-- Embedding of `K` into `perfect_closure K p` -/
def of (K : Type u) [comm_ring K] (p : ℕ) [fact (nat.prime p)] [char_p K p] : K →+* perfect_closure K p :=
  ring_hom.mk (fun (x : K) => mk K p (0, x)) sorry sorry sorry sorry

theorem of_apply (K : Type u) [comm_ring K] (p : ℕ) [fact (nat.prime p)] [char_p K p] (x : K) : coe_fn (of K p) x = mk K p (0, x) :=
  rfl

theorem eq_iff (K : Type u) [integral_domain K] (p : ℕ) [fact (nat.prime p)] [char_p K p] (x : ℕ × K) (y : ℕ × K) : Quot.mk (r K p) x = Quot.mk (r K p) y ↔
  nat.iterate (⇑(frobenius K p)) (prod.fst y) (prod.snd x) = nat.iterate (⇑(frobenius K p)) (prod.fst x) (prod.snd y) := sorry

protected instance has_inv (K : Type u) [field K] (p : ℕ) [fact (nat.prime p)] [char_p K p] : has_inv (perfect_closure K p) :=
  has_inv.mk (Quot.lift (fun (x : ℕ × K) => Quot.mk (r K p) (prod.fst x, prod.snd x⁻¹)) sorry)

protected instance field (K : Type u) [field K] (p : ℕ) [fact (nat.prime p)] [char_p K p] : field (perfect_closure K p) :=
  field.mk comm_ring.add sorry comm_ring.zero sorry sorry comm_ring.neg comm_ring.sub sorry sorry comm_ring.mul sorry
    comm_ring.one sorry sorry sorry sorry sorry has_inv.inv sorry sorry sorry

protected instance perfect_ring (K : Type u) [field K] (p : ℕ) [fact (nat.prime p)] [char_p K p] : perfect_ring (perfect_closure K p) p :=
  perfect_ring.mk
    (fun (e : perfect_closure K p) => lift_on e (fun (x : ℕ × K) => mk K p (prod.fst x + 1, prod.snd x)) sorry) sorry
    sorry

theorem eq_pth_root (K : Type u) [field K] (p : ℕ) [fact (nat.prime p)] [char_p K p] (x : ℕ × K) : mk K p x = nat.iterate (⇑(pth_root (perfect_closure K p) p)) (prod.fst x) (coe_fn (of K p) (prod.snd x)) := sorry

/-- Given a field `K` of characteristic `p` and a perfect ring `L` of the same characteristic,
any homomorphism `K →+* L` can be lifted to `perfect_closure K p`. -/
def lift (K : Type u) [field K] (p : ℕ) [fact (nat.prime p)] [char_p K p] (L : Type v) [comm_semiring L] [char_p L p] [perfect_ring L p] : (K →+* L) ≃ (perfect_closure K p →+* L) :=
  equiv.mk
    (fun (f : K →+* L) =>
      ring_hom.mk
        (fun (e : perfect_closure K p) =>
          lift_on e (fun (x : ℕ × K) => nat.iterate (⇑(pth_root L p)) (prod.fst x) (coe_fn f (prod.snd x))) sorry)
        sorry sorry sorry sorry)
    (fun (f : perfect_closure K p →+* L) => ring_hom.comp f (of K p)) sorry sorry

