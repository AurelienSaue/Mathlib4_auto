/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Keeley Hoek
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.nat.cast
import Mathlib.tactic.localized
import Mathlib.order.rel_iso
import Mathlib.PostPort

universes u u_1 u_2 v 

namespace Mathlib

/-!
# The finite type with `n` elements

`fin n` is the type whose elements are natural numbers smaller than `n`.
This file expands on the development in the core library.

## Main definitions

### Induction principles

* `fin_zero_elim` : Elimination principle for the empty set `fin 0`, generalizes `fin.elim0`.
* `fin.succ_rec` : Define `C n i` by induction on  `i : fin n` interpreted
  as `(0 : fin (n - i)).succ.succ…`. This function has two arguments: `H0 n` defines
  `0`-th element `C (n+1) 0` of an `(n+1)`-tuple, and `Hs n i` defines `(i+1)`-st element
  of `(n+1)`-tuple based on `n`, `i`, and `i`-th element of `n`-tuple.
* `fin.succ_rec_on` : same as `fin.succ_rec` but `i : fin n` is the first argument;
* `fin.induction` : Define `C i` by induction on `i : fin (n + 1)`, separating into the
  `nat`-like base cases of `C 0` and `C (i.succ)`.
* `fin.induction_on` : same as `fin.induction` but with `i : fin (n + 1)` as the first argument.

### Casts

* `cast_lt i h` : embed `i` into a `fin` where `h` proves it belongs into;
* `cast_le h` : embed `fin n` into `fin m`, `h : n ≤ m`;
* `cast eq` : embed `fin n` into `fin m`, `eq : n = m`;
* `cast_add m` : embed `fin n` into `fin (n+m)`;
* `cast_succ` : embed `fin n` into `fin (n+1)`;
* `succ_above p` : embed `fin n` into `fin (n + 1)` with a hole around `p`;
* `pred_above p i h` : embed `i : fin (n+1)` into `fin n` by ignoring `p`;
* `sub_nat i h` : subtract `m` from `i ≥ m`, generalizes `fin.pred`;
* `add_nat i h` : add `m` on `i` on the right, generalizes `fin.succ`;
* `nat_add i h` adds `n` on `i` on the left;
* `clamp n m` : `min n m` as an element of `fin (m + 1)`;

### Operation on tuples

We interpret maps `Π i : fin n, α i` as tuples `(α 0, …, α (n-1))`.
If `α i` is a constant map, then tuples are isomorphic (but not definitionally equal)
to `vector`s.

We define the following operations:

* `tail` : the tail of an `n+1` tuple, i.e., its last `n` entries;
* `cons` : adding an element at the beginning of an `n`-tuple, to get an `n+1`-tuple;
* `init` : the beginning of an `n+1` tuple, i.e., its first `n` entries;
* `snoc` : adding an element at the end of an `n`-tuple, to get an `n+1`-tuple. The name `snoc`
  comes from `cons` (i.e., adding an element to the left of a tuple) read in reverse order.
* `insert_nth` : insert an element to a tuple at a given position.
* `find p` : returns the first index `n` where `p n` is satisfied, and `none` if it is never
  satisfied.

### Misc definitions

* `fin.last n` : The greatest value of `fin (n+1)`.

-/

/-- Elimination principle for the empty set `fin 0`, dependent version. -/
def fin_zero_elim {α : fin 0 → Sort u} (x : fin 0) : α x := fin.elim0 x

theorem fact.succ.pos {n : ℕ} : fact (0 < Nat.succ n) := nat.zero_lt_succ n

theorem fact.bit0.pos {n : ℕ} [h : fact (0 < n)] : fact (0 < bit0 n) :=
  nat.zero_lt_bit0 (ne_of_gt h)

theorem fact.bit1.pos {n : ℕ} : fact (0 < bit1 n) := nat.zero_lt_bit1 n

theorem fact.pow.pos {p : ℕ} {n : ℕ} [h : fact (0 < p)] : fact (0 < p ^ n) := pow_pos h n

namespace fin


protected instance fin_to_nat (n : ℕ) : has_coe (fin n) ℕ := has_coe.mk subtype.val

theorem is_lt {n : ℕ} (i : fin n) : ↑i < n := subtype.property i

/-- convert a `ℕ` to `fin n`, provided `n` is positive -/
def of_nat' {n : ℕ} [h : fact (0 < n)] (i : ℕ) : fin n :=
  { val := i % n, property := nat.mod_lt i h }

@[simp] protected theorem eta {n : ℕ} (a : fin n) (h : ↑a < n) : { val := ↑a, property := h } = a :=
  sorry

theorem ext {n : ℕ} {a : fin n} {b : fin n} (h : ↑a = ↑b) : a = b := eq_of_veq h

theorem ext_iff {n : ℕ} (a : fin n) (b : fin n) : a = b ↔ ↑a = ↑b :=
  { mp := congr_arg fun (a : fin n) => ↑a, mpr := eq_of_veq }

theorem coe_injective {n : ℕ} : function.injective coe := subtype.coe_injective

theorem eq_iff_veq {n : ℕ} (a : fin n) (b : fin n) : a = b ↔ subtype.val a = subtype.val b :=
  { mp := veq_of_eq, mpr := eq_of_veq }

theorem ne_iff_vne {n : ℕ} (a : fin n) (b : fin n) : a ≠ b ↔ subtype.val a ≠ subtype.val b :=
  { mp := vne_of_ne, mpr := ne_of_vne }

@[simp] theorem mk_eq_subtype_mk {n : ℕ} (a : ℕ) (h : a < n) :
    mk a h = { val := a, property := h } :=
  rfl

protected theorem mk.inj_iff {n : ℕ} {a : ℕ} {b : ℕ} {ha : a < n} {hb : b < n} :
    { val := a, property := ha } = { val := b, property := hb } ↔ a = b :=
  subtype.mk_eq_mk

theorem mk_val {m : ℕ} {n : ℕ} (h : m < n) : subtype.val { val := m, property := h } = m := rfl

theorem eq_mk_iff_coe_eq {n : ℕ} {a : fin n} {k : ℕ} {hk : k < n} :
    a = { val := k, property := hk } ↔ ↑a = k :=
  eq_iff_veq a { val := k, property := hk }

@[simp] theorem coe_mk {m : ℕ} {n : ℕ} (h : m < n) : ↑{ val := m, property := h } = m := rfl

theorem mk_coe {n : ℕ} (i : fin n) : { val := ↑i, property := is_lt i } = i := fin.eta i (is_lt i)

theorem coe_eq_val {n : ℕ} (a : fin n) : ↑a = subtype.val a := rfl

@[simp] theorem val_eq_coe {n : ℕ} (a : fin n) : subtype.val a = ↑a := rfl

@[simp] theorem val_one {n : ℕ} : subtype.val 1 = 1 := rfl

@[simp] theorem val_two {n : ℕ} : subtype.val (bit0 1) = bit0 1 := rfl

@[simp] theorem coe_zero {n : ℕ} : ↑0 = 0 := rfl

@[simp] theorem coe_one {n : ℕ} : ↑1 = 1 := rfl

@[simp] theorem coe_two {n : ℕ} : ↑(bit0 1) = bit0 1 := rfl

/-- `a < b` as natural numbers if and only if `a < b` in `fin n`. -/
@[simp] theorem coe_fin_lt {n : ℕ} {a : fin n} {b : fin n} : ↑a < ↑b ↔ a < b := iff.rfl

/-- `a ≤ b` as natural numbers if and only if `a ≤ b` in `fin n`. -/
@[simp] theorem coe_fin_le {n : ℕ} {a : fin n} {b : fin n} : ↑a ≤ ↑b ↔ a ≤ b := iff.rfl

theorem val_add {n : ℕ} (a : fin n) (b : fin n) :
    subtype.val (a + b) = (subtype.val a + subtype.val b) % n :=
  sorry

theorem coe_add {n : ℕ} (a : fin n) (b : fin n) : ↑(a + b) = (↑a + ↑b) % n := sorry

theorem val_mul {n : ℕ} (a : fin n) (b : fin n) :
    subtype.val (a * b) = subtype.val a * subtype.val b % n :=
  sorry

theorem coe_mul {n : ℕ} (a : fin n) (b : fin n) : ↑(a * b) = ↑a * ↑b % n := sorry

theorem one_val {n : ℕ} : subtype.val 1 = 1 % (n + 1) := rfl

theorem coe_one' {n : ℕ} : ↑1 = 1 % (n + 1) := rfl

@[simp] theorem val_zero' (n : ℕ) : subtype.val 0 = 0 := rfl

@[simp] theorem mk_zero {n : ℕ} : { val := 0, property := nat.succ_pos' } = 0 := rfl

@[simp] theorem mk_one {n : ℕ} : { val := 1, property := nat.succ_lt_succ (nat.succ_pos n) } = 1 :=
  rfl

@[simp] theorem mk_bit0 {m : ℕ} {n : ℕ} (h : bit0 m < n) :
    { val := bit0 m, property := h } =
        bit0 { val := m, property := has_le.le.trans_lt (nat.le_add_right m m) h } :=
  eq_of_veq (Eq.symm (nat.mod_eq_of_lt h))

@[simp] theorem mk_bit1 {m : ℕ} {n : ℕ} (h : bit1 m < n + 1) :
    { val := bit1 m, property := h } =
        bit1
          { val := m,
            property :=
              has_le.le.trans_lt (nat.le_add_right m m)
                (has_lt.lt.trans (nat.lt_succ_self (m + m)) h) } :=
  sorry

@[simp] theorem of_nat_eq_coe (n : ℕ) (a : ℕ) : of_nat a = ↑a := sorry

/-- Converting an in-range number to `fin (n + 1)` produces a result
whose value is the original number.  -/
theorem coe_val_of_lt {n : ℕ} {a : ℕ} (h : a < n + 1) : subtype.val ↑a = a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (subtype.val ↑a = a)) (Eq.symm (of_nat_eq_coe n a))))
    (nat.mod_eq_of_lt h)

/-- Converting the value of a `fin (n + 1)` to `fin (n + 1)` results
in the same value.  -/
theorem coe_val_eq_self {n : ℕ} (a : fin (n + 1)) : ↑(subtype.val a) = a :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (↑(subtype.val a) = a)) (propext (eq_iff_veq (↑(subtype.val a)) a))))
    (coe_val_of_lt (subtype.property a))

/-- Coercing an in-range number to `fin (n + 1)`, and converting back
to `ℕ`, results in that number. -/
theorem coe_coe_of_lt {n : ℕ} {a : ℕ} (h : a < n + 1) : ↑↑a = a := coe_val_of_lt h

/-- Converting a `fin (n + 1)` to `ℕ` and back results in the same
value. -/
@[simp] theorem coe_coe_eq_self {n : ℕ} (a : fin (n + 1)) : ↑↑a = a := coe_val_eq_self a

/-- Assume `k = l`. If two functions defined on `fin k` and `fin l` are equal on each element,
then they coincide (in the heq sense). -/
protected theorem heq_fun_iff {α : Type u_1} {k : ℕ} {l : ℕ} (h : k = l) {f : fin k → α}
    {g : fin l → α} :
    f == g ↔ ∀ (i : fin k), f i = g { val := ↑i, property := h ▸ subtype.property i } :=
  sorry

protected theorem heq_ext_iff {k : ℕ} {l : ℕ} (h : k = l) {i : fin k} {j : fin l} :
    i == j ↔ ↑i = ↑j :=
  sorry

protected instance nontrivial {n : ℕ} : nontrivial (fin (n + bit0 1)) :=
  nontrivial.mk (Exists.intro 0 (Exists.intro 1 (of_as_true trivial)))

protected instance linear_order {n : ℕ} : linear_order (fin n) :=
  linear_order.mk LessEq Less sorry sorry sorry sorry fin.decidable_le (fin.decidable_eq n)
    fin.decidable_lt

theorem exists_iff {n : ℕ} {p : fin n → Prop} :
    (∃ (i : fin n), p i) ↔ ∃ (i : ℕ), ∃ (h : i < n), p { val := i, property := h } :=
  sorry

theorem forall_iff {n : ℕ} {p : fin n → Prop} :
    (∀ (i : fin n), p i) ↔ ∀ (i : ℕ) (h : i < n), p { val := i, property := h } :=
  sorry

theorem lt_iff_coe_lt_coe {n : ℕ} {a : fin n} {b : fin n} : a < b ↔ ↑a < ↑b := iff.rfl

theorem le_iff_coe_le_coe {n : ℕ} {a : fin n} {b : fin n} : a ≤ b ↔ ↑a ≤ ↑b := iff.rfl

theorem mk_lt_of_lt_coe {n : ℕ} {b : fin n} {a : ℕ} (h : a < ↑b) :
    { val := a, property := has_lt.lt.trans h (is_lt b) } < b :=
  h

theorem mk_le_of_le_coe {n : ℕ} {b : fin n} {a : ℕ} (h : a ≤ ↑b) :
    { val := a, property := has_le.le.trans_lt h (is_lt b) } ≤ b :=
  h

theorem zero_le {n : ℕ} (a : fin (n + 1)) : 0 ≤ a := nat.zero_le (subtype.val a)

@[simp] theorem coe_succ {n : ℕ} (j : fin n) : ↑(fin.succ j) = ↑j + 1 := sorry

theorem succ_pos {n : ℕ} (a : fin n) : 0 < fin.succ a := sorry

/-- The greatest value of `fin (n+1)` -/
def last (n : ℕ) : fin (n + 1) := { val := n, property := nat.lt_succ_self n }

@[simp] theorem coe_last (n : ℕ) : ↑(last n) = n := rfl

theorem last_val (n : ℕ) : subtype.val (last n) = n := rfl

theorem le_last {n : ℕ} (i : fin (n + 1)) : i ≤ last n := nat.le_of_lt_succ (is_lt i)

protected instance bounded_lattice {n : ℕ} : bounded_lattice (fin (n + 1)) :=
  bounded_lattice.mk lattice.sup linear_order.le linear_order.lt sorry sorry sorry sorry sorry sorry
    lattice.inf sorry sorry sorry (last n) le_last 0 zero_le

/-- `fin.succ` as an `order_embedding` -/
def succ_embedding (n : ℕ) : fin n ↪o fin (n + 1) := order_embedding.of_strict_mono fin.succ sorry

@[simp] theorem coe_succ_embedding {n : ℕ} : ⇑(succ_embedding n) = fin.succ := rfl

@[simp] theorem succ_le_succ_iff {n : ℕ} {a : fin n} {b : fin n} :
    fin.succ a ≤ fin.succ b ↔ a ≤ b :=
  order_embedding.le_iff_le (succ_embedding n)

@[simp] theorem succ_lt_succ_iff {n : ℕ} {a : fin n} {b : fin n} :
    fin.succ a < fin.succ b ↔ a < b :=
  order_embedding.lt_iff_lt (succ_embedding n)

theorem succ_injective (n : ℕ) : function.injective fin.succ :=
  rel_embedding.injective (succ_embedding n)

@[simp] theorem succ_inj {n : ℕ} {a : fin n} {b : fin n} : fin.succ a = fin.succ b ↔ a = b :=
  function.injective.eq_iff (succ_injective n)

theorem succ_ne_zero {n : ℕ} (k : fin n) : fin.succ k ≠ 0 := sorry

@[simp] theorem succ_zero_eq_one {n : ℕ} : fin.succ 0 = 1 := rfl

theorem mk_succ_pos {n : ℕ} (i : ℕ) (h : i < n) :
    0 < { val := Nat.succ i, property := add_lt_add_right h 1 } :=
  sorry

theorem one_lt_succ_succ {n : ℕ} (a : fin n) : 1 < fin.succ (fin.succ a) := sorry

theorem succ_succ_ne_one {n : ℕ} (a : fin n) : fin.succ (fin.succ a) ≠ 1 :=
  ne_of_gt (one_lt_succ_succ a)

@[simp] theorem coe_pred {n : ℕ} (j : fin (n + 1)) (h : j ≠ 0) : ↑(pred j h) = ↑j - 1 := sorry

@[simp] theorem succ_pred {n : ℕ} (i : fin (n + 1)) (h : i ≠ 0) : fin.succ (pred i h) = i := sorry

@[simp] theorem pred_succ {n : ℕ} (i : fin n) {h : fin.succ i ≠ 0} : pred (fin.succ i) h = i :=
  sorry

@[simp] theorem pred_mk_succ {n : ℕ} (i : ℕ) (h : i < n + 1) :
    pred { val := i + 1, property := add_lt_add_right h 1 }
          (ne_of_vne (ne_of_gt (mk_succ_pos i h))) =
        { val := i, property := h } :=
  sorry

@[simp] theorem pred_le_pred_iff {n : ℕ} {a : fin (Nat.succ n)} {b : fin (Nat.succ n)} {ha : a ≠ 0}
    {hb : b ≠ 0} : pred a ha ≤ pred b hb ↔ a ≤ b :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (pred a ha ≤ pred b hb ↔ a ≤ b)) (Eq.symm (propext succ_le_succ_iff))))
    (eq.mpr
      (id
        (Eq._oldrec (Eq.refl (fin.succ (pred a ha) ≤ fin.succ (pred b hb) ↔ a ≤ b))
          (succ_pred a ha)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a ≤ fin.succ (pred b hb) ↔ a ≤ b)) (succ_pred b hb)))
        (iff.refl (a ≤ b))))

@[simp] theorem pred_lt_pred_iff {n : ℕ} {a : fin (Nat.succ n)} {b : fin (Nat.succ n)} {ha : a ≠ 0}
    {hb : b ≠ 0} : pred a ha < pred b hb ↔ a < b :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (pred a ha < pred b hb ↔ a < b)) (Eq.symm (propext succ_lt_succ_iff))))
    (eq.mpr
      (id
        (Eq._oldrec (Eq.refl (fin.succ (pred a ha) < fin.succ (pred b hb) ↔ a < b))
          (succ_pred a ha)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a < fin.succ (pred b hb) ↔ a < b)) (succ_pred b hb)))
        (iff.refl (a < b))))

@[simp] theorem pred_inj {n : ℕ} {a : fin (n + 1)} {b : fin (n + 1)} {ha : a ≠ 0} {hb : b ≠ 0} :
    pred a ha = pred b hb ↔ a = b :=
  sorry

/-- The inclusion map `fin n → ℕ` is a relation embedding. -/
def coe_embedding (n : ℕ) : fin n ↪o ℕ :=
  rel_embedding.mk (function.embedding.mk coe eq_of_veq) sorry

/-- The ordering on `fin n` is a well order. -/
protected instance fin.lt.is_well_order (n : ℕ) : is_well_order (fin n) Less :=
  order_embedding.is_well_order (coe_embedding n)

/-- `cast_lt i h` embeds `i` into a `fin` where `h` proves it belongs into.  -/
def cast_lt {n : ℕ} {m : ℕ} (i : fin m) (h : subtype.val i < n) : fin n :=
  { val := subtype.val i, property := h }

@[simp] theorem coe_cast_lt {n : ℕ} {m : ℕ} (i : fin m) (h : subtype.val i < n) :
    ↑(cast_lt i h) = ↑i :=
  rfl

/-- `cast_le h i` embeds `i` into a larger `fin` type.  -/
def cast_le {n : ℕ} {m : ℕ} (h : n ≤ m) : fin n ↪o fin m :=
  order_embedding.of_strict_mono (fun (a : fin n) => cast_lt a sorry) sorry

@[simp] theorem coe_cast_le {n : ℕ} {m : ℕ} (h : n ≤ m) (i : fin n) :
    ↑(coe_fn (cast_le h) i) = ↑i :=
  rfl

/-- `cast eq i` embeds `i` into a equal `fin` type. -/
def cast {n : ℕ} {m : ℕ} (eq : n = m) : fin n ≃o fin m :=
  rel_iso.mk (equiv.mk ⇑(cast_le sorry) ⇑(cast_le sorry) sorry sorry) sorry

@[simp] theorem symm_cast {n : ℕ} {m : ℕ} (h : n = m) :
    order_iso.symm (cast h) = cast (Eq.symm h) :=
  rfl

theorem coe_cast {n : ℕ} {m : ℕ} (h : n = m) (i : fin n) : ↑(coe_fn (cast h) i) = ↑i := rfl

@[simp] theorem cast_trans {n : ℕ} {m : ℕ} {k : ℕ} (h : n = m) (h' : m = k) {i : fin n} :
    coe_fn (cast h') (coe_fn (cast h) i) = coe_fn (cast (Eq.trans h h')) i :=
  rfl

@[simp] theorem cast_refl {n : ℕ} {i : fin n} : coe_fn (cast rfl) i = i :=
  ext (Eq.refl ↑(coe_fn (cast rfl) i))

/-- `cast_add m i` embeds `i : fin n` in `fin (n+m)`. -/
def cast_add {n : ℕ} (m : ℕ) : fin n ↪o fin (n + m) := cast_le (nat.le_add_right n m)

@[simp] theorem coe_cast_add {n : ℕ} (m : ℕ) (i : fin n) : ↑(coe_fn (cast_add m) i) = ↑i := rfl

/-- `cast_succ i` embeds `i : fin n` in `fin (n+1)`. -/
def cast_succ {n : ℕ} : fin n ↪o fin (n + 1) := cast_add 1

@[simp] theorem coe_cast_succ {n : ℕ} (i : fin n) : ↑(coe_fn cast_succ i) = ↑i := rfl

theorem cast_succ_lt_succ {n : ℕ} (i : fin n) : coe_fn cast_succ i < fin.succ i := sorry

theorem succ_above_aux {n : ℕ} (p : fin (n + 1)) :
    strict_mono fun (i : fin n) => ite (coe_fn cast_succ i < p) (coe_fn cast_succ i) (fin.succ i) :=
  sorry

/-- `succ_above p i` embeds `fin n` into `fin (n + 1)` with a hole around `p`. -/
def succ_above {n : ℕ} (p : fin (n + 1)) : fin n ↪o fin (n + 1) :=
  order_embedding.of_strict_mono
    (fun (a : fin n) =>
      (fun (i : fin n) => ite (coe_fn cast_succ i < p) (coe_fn cast_succ i) (fin.succ i)) a)
    (succ_above_aux p)

/-- `pred_above p i h` embeds `i : fin (n+1)` into `fin n` by ignoring `p`. -/
def pred_above {n : ℕ} (p : fin (n + 1)) (i : fin (n + 1)) (hi : i ≠ p) : fin n :=
  dite (i < p) (fun (h : i < p) => cast_lt i sorry) fun (h : ¬i < p) => pred i sorry

/-- `sub_nat i h` subtracts `m` from `i`, generalizes `fin.pred`. -/
def sub_nat {n : ℕ} (m : ℕ) (i : fin (n + m)) (h : m ≤ ↑i) : fin n :=
  { val := ↑i - m, property := sorry }

@[simp] theorem coe_sub_nat {n : ℕ} {m : ℕ} (i : fin (n + m)) (h : m ≤ ↑i) :
    ↑(sub_nat m i h) = ↑i - m :=
  rfl

/-- `add_nat i h` adds `m` to `i`, generalizes `fin.succ`. -/
def add_nat {n : ℕ} (m : ℕ) : fin n ↪o fin (n + m) :=
  order_embedding.of_strict_mono (fun (i : fin n) => { val := ↑i + m, property := sorry }) sorry

@[simp] theorem coe_add_nat {n : ℕ} (m : ℕ) (i : fin n) : ↑(coe_fn (add_nat m) i) = ↑i + m := rfl

/-- `nat_add i h` adds `n` to `i` "on the left". -/
def nat_add (n : ℕ) {m : ℕ} : fin m ↪o fin (n + m) :=
  order_embedding.of_strict_mono (fun (i : fin m) => { val := n + ↑i, property := sorry }) sorry

@[simp] theorem coe_nat_add (n : ℕ) {m : ℕ} (i : fin m) : ↑(coe_fn (nat_add n) i) = n + ↑i := rfl

/-- If `e` is an `order_iso` between `fin n` and `fin m`, then `n = m` and `e` is the identity
map. In this lemma we state that for each `i : fin n` we have `(e i : ℕ) = (i : ℕ)`. -/
@[simp] theorem coe_order_iso_apply {n : ℕ} {m : ℕ} (e : fin n ≃o fin m) (i : fin n) :
    ↑(coe_fn e i) = ↑i :=
  sorry

protected instance order_iso_subsingleton {n : ℕ} {α : Type u_1} [preorder α] :
    subsingleton (fin n ≃o α) :=
  sorry

protected instance order_iso_subsingleton' {n : ℕ} {α : Type u_1} [preorder α] :
    subsingleton (α ≃o fin n) :=
  function.injective.subsingleton order_iso.symm_injective

protected instance order_iso_unique {n : ℕ} : unique (fin n ≃o fin n) := unique.mk' (fin n ≃o fin n)

/-- Two strictly monotone functions from `fin n` are equal provided that their ranges
are equal. -/
theorem strict_mono_unique {n : ℕ} {α : Type u_1} [preorder α] {f : fin n → α} {g : fin n → α}
    (hf : strict_mono f) (hg : strict_mono g) (h : set.range f = set.range g) : f = g :=
  sorry

/-- Two order embeddings of `fin n` are equal provided that their ranges are equal. -/
theorem order_embedding_eq {n : ℕ} {α : Type u_1} [preorder α] {f : fin n ↪o α} {g : fin n ↪o α}
    (h : set.range ⇑f = set.range ⇑g) : f = g :=
  rel_embedding.ext
    (iff.mp function.funext_iff
      (strict_mono_unique (order_embedding.strict_mono f) (order_embedding.strict_mono g) h))

@[simp] theorem succ_last (n : ℕ) : fin.succ (last n) = last (Nat.succ n) := rfl

@[simp] theorem cast_succ_cast_lt {n : ℕ} (i : fin (n + 1)) (h : ↑i < n) :
    coe_fn cast_succ (cast_lt i h) = i :=
  eq_of_veq rfl

@[simp] theorem cast_lt_cast_succ {n : ℕ} (a : fin n) (h : ↑a < n) :
    cast_lt (coe_fn cast_succ a) h = a :=
  sorry

theorem cast_succ_injective (n : ℕ) : function.injective ⇑cast_succ :=
  rel_embedding.injective cast_succ

theorem cast_succ_inj {n : ℕ} {a : fin n} {b : fin n} :
    coe_fn cast_succ a = coe_fn cast_succ b ↔ a = b :=
  function.injective.eq_iff (cast_succ_injective n)

theorem cast_succ_lt_last {n : ℕ} (a : fin n) : coe_fn cast_succ a < last n :=
  iff.mpr lt_iff_coe_lt_coe (is_lt a)

@[simp] theorem cast_succ_zero {n : ℕ} : coe_fn cast_succ 0 = 0 := rfl

/-- `cast_succ i` is positive when `i` is positive -/
theorem cast_succ_pos {n : ℕ} (i : fin (n + 1)) (h : 0 < i) : 0 < coe_fn cast_succ i := sorry

theorem last_pos {n : ℕ} : 0 < last (n + 1) := sorry

theorem coe_nat_eq_last (n : ℕ) : ↑n = last n := sorry

theorem le_coe_last {n : ℕ} (i : fin (n + 1)) : i ≤ ↑n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (i ≤ ↑n)) (coe_nat_eq_last n))) (le_last i)

theorem eq_last_of_not_lt {n : ℕ} {i : fin (n + 1)} (h : ¬↑i < n) : i = last n :=
  le_antisymm (le_last i) (iff.mp not_lt h)

theorem add_one_pos {n : ℕ} (i : fin (n + 1)) (h : i < last n) : 0 < i + 1 := sorry

theorem one_pos {n : ℕ} : 0 < 1 := succ_pos 0

theorem zero_ne_one {n : ℕ} : 0 ≠ 1 := ne_of_lt one_pos

@[simp] theorem zero_eq_one_iff {n : ℕ} : 0 = 1 ↔ n = 0 :=
  { mp :=
      nat.cases_on n (fun (h : 0 = 1) => Eq.refl 0) fun (n : ℕ) (h : 0 = 1) => absurd h zero_ne_one,
    mpr := fun (ᾰ : n = 0) => Eq._oldrec (Eq.refl 0) (Eq.symm ᾰ) }

@[simp] theorem one_eq_zero_iff {n : ℕ} : 1 = 0 ↔ n = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (1 = 0 ↔ n = 0)) (propext eq_comm)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (0 = 1 ↔ n = 0)) (propext zero_eq_one_iff)))
      (iff.refl (n = 0)))

theorem cast_succ_fin_succ (n : ℕ) (j : fin n) :
    coe_fn cast_succ (fin.succ j) = fin.succ (coe_fn cast_succ j) :=
  sorry

@[simp] theorem coe_eq_cast_succ {n : ℕ} {a : fin n} : ↑a = coe_fn cast_succ a :=
  ext (coe_val_of_lt (nat.lt.step (is_lt a)))

@[simp] theorem coe_succ_eq_succ {n : ℕ} {a : fin n} : coe_fn cast_succ a + 1 = fin.succ a := sorry

theorem lt_succ {n : ℕ} {a : fin n} : coe_fn cast_succ a < fin.succ a := sorry

@[simp] theorem pred_one {n : ℕ} : pred 1 (ne.symm (ne_of_lt one_pos)) = 0 := rfl

theorem pred_add_one {n : ℕ} (i : fin (n + bit0 1)) (h : ↑i < n + 1) :
    pred (i + 1) (ne_of_gt (add_one_pos i (iff.mpr lt_iff_coe_lt_coe h))) = cast_lt i h :=
  sorry

theorem nat_add_zero {n : ℕ} : nat_add 0 = rel_iso.to_rel_embedding (cast (Eq.symm (zero_add n))) :=
  rel_embedding.ext fun (x : fin n) => ext (zero_add ↑x)

/-- `min n m` as an element of `fin (m + 1)` -/
def clamp (n : ℕ) (m : ℕ) : fin (m + 1) := of_nat (min n m)

@[simp] theorem coe_clamp (n : ℕ) (m : ℕ) : ↑(clamp n m) = min n m :=
  nat.mod_eq_of_lt (iff.mpr nat.lt_succ_iff (min_le_right n m))

/-- Embedding `i : fin n` into `fin (n + 1)` with a hole around `p : fin (n + 1)`
embeds `i` by `cast_succ` when the resulting `i.cast_succ < p`. -/
theorem succ_above_below {n : ℕ} (p : fin (n + 1)) (i : fin n) (h : coe_fn cast_succ i < p) :
    coe_fn (succ_above p) i = coe_fn cast_succ i :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (coe_fn (succ_above p) i = coe_fn cast_succ i))
        (succ_above.equations._eqn_1 p)))
    (if_pos h)

/-- Embedding `fin n` into `fin (n + 1)` with a hole around zero embeds by `succ`. -/
@[simp] theorem succ_above_zero {n : ℕ} : ⇑(succ_above 0) = fin.succ := rfl

/-- Embedding `fin n` into `fin (n + 1)` with a hole around `last n` embeds by `cast_succ`. -/
@[simp] theorem succ_above_last {n : ℕ} : succ_above (last n) = cast_succ := sorry

theorem succ_above_last_apply {n : ℕ} (i : fin n) :
    coe_fn (succ_above (last n)) i = coe_fn cast_succ i :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (coe_fn (succ_above (last n)) i = coe_fn cast_succ i)) succ_above_last))
    (Eq.refl (coe_fn cast_succ i))

/-- Embedding `i : fin n` into `fin (n + 1)` with a hole around `p : fin (n + 1)`
embeds `i` by `succ` when the resulting `p < i.succ`. -/
theorem succ_above_above {n : ℕ} (p : fin (n + 1)) (i : fin n) (h : p ≤ coe_fn cast_succ i) :
    coe_fn (succ_above p) i = fin.succ i :=
  sorry

/-- Embedding `i : fin n` into `fin (n + 1)` is always about some hole `p`. -/
theorem succ_above_lt_ge {n : ℕ} (p : fin (n + 1)) (i : fin n) :
    coe_fn cast_succ i < p ∨ p ≤ coe_fn cast_succ i :=
  lt_or_ge (coe_fn cast_succ i) p

/-- Embedding `i : fin n` into `fin (n + 1)` is always about some hole `p`. -/
theorem succ_above_lt_gt {n : ℕ} (p : fin (n + 1)) (i : fin n) :
    coe_fn cast_succ i < p ∨ p < fin.succ i :=
  or.cases_on (succ_above_lt_ge p i) (fun (h : coe_fn cast_succ i < p) => Or.inl h)
    fun (h : p ≤ coe_fn cast_succ i) => Or.inr (lt_of_le_of_lt h (cast_succ_lt_succ i))

/-- Embedding `i : fin n` into `fin (n + 1)` using a pivot `p` that is greater
results in a value that is less than `p`. -/
@[simp] theorem succ_above_lt_iff {n : ℕ} (p : fin (n + 1)) (i : fin n) :
    coe_fn (succ_above p) i < p ↔ coe_fn cast_succ i < p :=
  sorry

/-- Embedding `i : fin n` into `fin (n + 1)` using a pivot `p` that is lesser
results in a value that is greater than `p`. -/
theorem lt_succ_above_iff {n : ℕ} (p : fin (n + 1)) (i : fin n) :
    p < coe_fn (succ_above p) i ↔ p ≤ coe_fn cast_succ i :=
  sorry

/-- Embedding `i : fin n` into `fin (n + 1)` with a hole around `p : fin (n + 1)`
never results in `p` itself -/
theorem succ_above_ne {n : ℕ} (p : fin (n + 1)) (i : fin n) : coe_fn (succ_above p) i ≠ p := sorry

/-- Embedding a positive `fin n`  results in a positive fin (n + 1)` -/
theorem succ_above_pos {n : ℕ} (p : fin (n + bit0 1)) (i : fin (n + 1)) (h : 0 < i) :
    0 < coe_fn (succ_above p) i :=
  sorry

/-- Given a fixed pivot `x : fin (n + 1)`, `x.succ_above` is injective -/
theorem succ_above_right_injective {n : ℕ} {x : fin (n + 1)} : function.injective ⇑(succ_above x) :=
  rel_embedding.injective (succ_above x)

/-- Given a fixed pivot `x : fin (n + 1)`, `x.succ_above` is injective -/
theorem succ_above_right_inj {n : ℕ} {a : fin n} {b : fin n} {x : fin (n + 1)} :
    coe_fn (succ_above x) a = coe_fn (succ_above x) b ↔ a = b :=
  function.injective.eq_iff succ_above_right_injective

/-- Embedding a `fin (n + 1)` into `fin n` and embedding it back around the same hole
gives the starting `fin (n + 1)` -/
@[simp] theorem succ_above_pred_above {n : ℕ} (p : fin (n + 1)) (i : fin (n + 1)) (h : i ≠ p) :
    coe_fn (succ_above p) (pred_above p i h) = i :=
  sorry

/-- Embedding a `fin n` into `fin (n + 1)` and embedding it back around the same hole
gives the starting `fin n` -/
@[simp] theorem pred_above_succ_above {n : ℕ} (p : fin (n + 1)) (i : fin n) :
    pred_above p (coe_fn (succ_above p) i) (succ_above_ne p i) = i :=
  sorry

@[simp] theorem pred_above_zero {n : ℕ} {i : fin (n + 1)} (hi : i ≠ 0) :
    pred_above 0 i hi = pred i hi :=
  rfl

theorem forall_iff_succ_above {n : ℕ} {p : fin (n + 1) → Prop} (i : fin (n + 1)) :
    (∀ (j : fin (n + 1)), p j) ↔ p i ∧ ∀ (j : fin n), p (coe_fn (succ_above i) j) :=
  sorry

/-- `succ_above` is injective at the pivot -/
theorem succ_above_left_injective {n : ℕ} : function.injective succ_above := sorry

/-- `succ_above` is injective at the pivot -/
theorem succ_above_left_inj {n : ℕ} {x : fin (n + 1)} {y : fin (n + 1)} :
    succ_above x = succ_above y ↔ x = y :=
  function.injective.eq_iff succ_above_left_injective

/-- A function `f` on `fin n` is strictly monotone if and only if `f i < f (i+1)` for all `i`. -/
theorem strict_mono_iff_lt_succ {n : ℕ} {α : Type u_1} [preorder α] {f : fin n → α} :
    strict_mono f ↔
        ∀ (i : ℕ) (h : i + 1 < n),
          f { val := i, property := lt_of_le_of_lt (nat.le_succ i) h } <
            f { val := i + 1, property := h } :=
  sorry

/-- Define `C n i` by induction on `i : fin n` interpreted as `(0 : fin (n - i)).succ.succ…`.
This function has two arguments: `H0 n` defines `0`-th element `C (n+1) 0` of an `(n+1)`-tuple,
and `Hs n i` defines `(i+1)`-st element of `(n+1)`-tuple based on `n`, `i`, and `i`-th element
of `n`-tuple. -/
def succ_rec {C : (n : ℕ) → fin n → Sort u_1} (H0 : (n : ℕ) → C (Nat.succ n) 0)
    (Hs : (n : ℕ) → (i : fin n) → C n i → C (Nat.succ n) (fin.succ i)) {n : ℕ} (i : fin n) :
    C n i :=
  sorry

/-- Define `C n i` by induction on `i : fin n` interpreted as `(0 : fin (n - i)).succ.succ…`.
This function has two arguments: `H0 n` defines `0`-th element `C (n+1) 0` of an `(n+1)`-tuple,
and `Hs n i` defines `(i+1)`-st element of `(n+1)`-tuple based on `n`, `i`, and `i`-th element
of `n`-tuple.

A version of `fin.succ_rec` taking `i : fin n` as the first argument. -/
def succ_rec_on {n : ℕ} (i : fin n) {C : (n : ℕ) → fin n → Sort u_1}
    (H0 : (n : ℕ) → C (Nat.succ n) 0)
    (Hs : (n : ℕ) → (i : fin n) → C n i → C (Nat.succ n) (fin.succ i)) : C n i :=
  succ_rec H0 Hs i

@[simp] theorem succ_rec_on_zero {C : (n : ℕ) → fin n → Sort u_1} {H0 : (n : ℕ) → C (Nat.succ n) 0}
    {Hs : (n : ℕ) → (i : fin n) → C n i → C (Nat.succ n) (fin.succ i)} (n : ℕ) :
    succ_rec_on 0 H0 Hs = H0 n :=
  rfl

@[simp] theorem succ_rec_on_succ {C : (n : ℕ) → fin n → Sort u_1} {H0 : (n : ℕ) → C (Nat.succ n) 0}
    {Hs : (n : ℕ) → (i : fin n) → C n i → C (Nat.succ n) (fin.succ i)} {n : ℕ} (i : fin n) :
    succ_rec_on (fin.succ i) H0 Hs = Hs n i (succ_rec_on i H0 Hs) :=
  subtype.cases_on i
    fun (i_val : ℕ) (i_property : i_val < n) =>
      Eq.refl (succ_rec_on (fin.succ { val := i_val, property := i_property }) H0 Hs)

/--
Define `C i` by induction on `i : fin (n + 1)` via induction on the underlying `nat` value.
This function has two arguments: `h0` handles the base case on `C 0`,
and `hs` defines the inductive step using `C i.cast_succ`.
-/
def induction {n : ℕ} {C : fin (n + 1) → Sort u_1} (h0 : C 0)
    (hs : (i : fin n) → C (coe_fn cast_succ i) → C (fin.succ i)) (i : fin (n + 1)) : C i :=
  subtype.cases_on i
    fun (i : ℕ) (hi : i < n + 1) =>
      Nat.rec (fun (hi : 0 < n + 1) => eq.mpr sorry h0)
        (fun (i : ℕ) (IH : (hi : i < n + 1) → C { val := i, property := hi })
          (hi : Nat.succ i < n + 1) =>
          hs { val := i, property := nat.lt_of_succ_lt_succ hi } (IH sorry))
        i hi

/--
Define `C i` by induction on `i : fin (n + 1)` via induction on the underlying `nat` value.
This function has two arguments: `h0` handles the base case on `C 0`,
and `hs` defines the inductive step using `C i.cast_succ`.

A version of `fin.induction` taking `i : fin (n + 1)` as the first argument.
-/
def induction_on {n : ℕ} (i : fin (n + 1)) {C : fin (n + 1) → Sort u_1} (h0 : C 0)
    (hs : (i : fin n) → C (coe_fn cast_succ i) → C (fin.succ i)) : C i :=
  induction h0 hs i

/-- Define `f : Π i : fin n.succ, C i` by separately handling the cases `i = 0` and
`i = j.succ`, `j : fin n`. -/
def cases {n : ℕ} {C : fin (Nat.succ n) → Sort u_1} (H0 : C 0) (Hs : (i : fin n) → C (fin.succ i))
    (i : fin (Nat.succ n)) : C i :=
  induction H0 fun (i : fin n) (_x : C (coe_fn cast_succ i)) => Hs i

@[simp] theorem cases_zero {n : ℕ} {C : fin (Nat.succ n) → Sort u_1} {H0 : C 0}
    {Hs : (i : fin n) → C (fin.succ i)} : cases H0 Hs 0 = H0 :=
  rfl

@[simp] theorem cases_succ {n : ℕ} {C : fin (Nat.succ n) → Sort u_1} {H0 : C 0}
    {Hs : (i : fin n) → C (fin.succ i)} (i : fin n) : cases H0 Hs (fin.succ i) = Hs i :=
  subtype.cases_on i
    fun (i_val : ℕ) (i_property : i_val < n) =>
      Eq.refl (cases H0 Hs (fin.succ { val := i_val, property := i_property }))

@[simp] theorem cases_succ' {n : ℕ} {C : fin (Nat.succ n) → Sort u_1} {H0 : C 0}
    {Hs : (i : fin n) → C (fin.succ i)} {i : ℕ} (h : i + 1 < n + 1) :
    cases H0 Hs { val := Nat.succ i, property := h } =
        Hs { val := i, property := nat.lt_of_succ_lt_succ h } :=
  nat.cases_on i (fun (h : 0 + 1 < n + 1) => Eq.refl (cases H0 Hs { val := 1, property := h }))
    (fun (i : ℕ) (h : Nat.succ i + 1 < n + 1) =>
      Eq.refl (cases H0 Hs { val := Nat.succ (Nat.succ i), property := h }))
    h

theorem forall_fin_succ {n : ℕ} {P : fin (n + 1) → Prop} :
    (∀ (i : fin (n + 1)), P i) ↔ P 0 ∧ ∀ (i : fin n), P (fin.succ i) :=
  sorry

theorem exists_fin_succ {n : ℕ} {P : fin (n + 1) → Prop} :
    (∃ (i : fin (n + 1)), P i) ↔ P 0 ∨ ∃ (i : fin n), P (fin.succ i) :=
  sorry

/-!
### Tuples

We can think of the type `Π(i : fin n), α i` as `n`-tuples of elements of possibly varying type
`α i`. A particular case is `fin n → α` of elements with all the same type. Here are some relevant
operations, first about adding or removing elements at the beginning of a tuple.
-/

/-- There is exactly one tuple of size zero. -/
protected instance tuple0_unique (α : fin 0 → Type u) : unique ((i : fin 0) → α i) :=
  unique.mk { default := fin_zero_elim } sorry

@[simp] theorem tuple0_le {α : fin 0 → Type u_1} [(i : fin 0) → preorder (α i)]
    (f : (i : fin 0) → α i) (g : (i : fin 0) → α i) : f ≤ g :=
  fin_zero_elim

/-- The tail of an `n+1` tuple, i.e., its last `n` entries. -/
def tail {n : ℕ} {α : fin (n + 1) → Type u} (q : (i : fin (n + 1)) → α i) (i : fin n) :
    α (fin.succ i) :=
  q (fin.succ i)

/-- Adding an element at the beginning of an `n`-tuple, to get an `n+1`-tuple. -/
def cons {n : ℕ} {α : fin (n + 1) → Type u} (x : α 0) (p : (i : fin n) → α (fin.succ i))
    (i : fin (n + 1)) : α i :=
  cases x p j

@[simp] theorem tail_cons {n : ℕ} {α : fin (n + 1) → Type u} (x : α 0)
    (p : (i : fin n) → α (fin.succ i)) : tail (cons x p) = p :=
  sorry

@[simp] theorem cons_succ {n : ℕ} {α : fin (n + 1) → Type u} (x : α 0)
    (p : (i : fin n) → α (fin.succ i)) (i : fin n) : cons x p (fin.succ i) = p i :=
  sorry

@[simp] theorem cons_zero {n : ℕ} {α : fin (n + 1) → Type u} (x : α 0)
    (p : (i : fin n) → α (fin.succ i)) : cons x p 0 = x :=
  sorry

/-- Updating a tuple and adding an element at the beginning commute. -/
@[simp] theorem cons_update {n : ℕ} {α : fin (n + 1) → Type u} (x : α 0)
    (p : (i : fin n) → α (fin.succ i)) (i : fin n) (y : α (fin.succ i)) :
    cons x (function.update p i y) = function.update (cons x p) (fin.succ i) y :=
  sorry

/-- Adding an element at the beginning of a tuple and then updating it amounts to adding it
directly. -/
theorem update_cons_zero {n : ℕ} {α : fin (n + 1) → Type u} (x : α 0)
    (p : (i : fin n) → α (fin.succ i)) (z : α 0) : function.update (cons x p) 0 z = cons z p :=
  sorry

/-- Concatenating the first element of a tuple with its tail gives back the original tuple -/
@[simp] theorem cons_self_tail {n : ℕ} {α : fin (n + 1) → Type u} (q : (i : fin (n + 1)) → α i) :
    cons (q 0) (tail q) = q :=
  sorry

/-- Updating the first element of a tuple does not change the tail. -/
@[simp] theorem tail_update_zero {n : ℕ} {α : fin (n + 1) → Type u} (q : (i : fin (n + 1)) → α i)
    (z : α 0) : tail (function.update q 0 z) = tail q :=
  sorry

/-- Updating a nonzero element and taking the tail commute. -/
@[simp] theorem tail_update_succ {n : ℕ} {α : fin (n + 1) → Type u} (q : (i : fin (n + 1)) → α i)
    (i : fin n) (y : α (fin.succ i)) :
    tail (function.update q (fin.succ i) y) = function.update (tail q) i y :=
  sorry

theorem comp_cons {n : ℕ} {α : Type u_1} {β : Type u_2} (g : α → β) (y : α) (q : fin n → α) :
    g ∘ cons y q = cons (g y) (g ∘ q) :=
  sorry

theorem comp_tail {n : ℕ} {α : Type u_1} {β : Type u_2} (g : α → β) (q : fin (Nat.succ n) → α) :
    g ∘ tail q = tail (g ∘ q) :=
  sorry

theorem le_cons {n : ℕ} {α : fin (n + 1) → Type u} [(i : fin (n + 1)) → preorder (α i)] {x : α 0}
    {q : (i : fin (n + 1)) → α i} {p : (i : fin n) → α (fin.succ i)} :
    q ≤ cons x p ↔ q 0 ≤ x ∧ tail q ≤ p :=
  sorry

theorem cons_le {n : ℕ} {α : fin (n + 1) → Type u} [(i : fin (n + 1)) → preorder (α i)] {x : α 0}
    {q : (i : fin (n + 1)) → α i} {p : (i : fin n) → α (fin.succ i)} :
    cons x p ≤ q ↔ x ≤ q 0 ∧ p ≤ tail q :=
  le_cons

/-- `fin.append ho u v` appends two vectors of lengths `m` and `n` to produce
one of length `o = m + n`.  `ho` provides control of definitional equality
for the vector length. -/
def append {n : ℕ} {m : ℕ} {α : Type u_1} {o : ℕ} (ho : o = m + n) (u : fin m → α) (v : fin n → α) :
    fin o → α :=
  fun (i : fin o) =>
    dite (↑i < m) (fun (h : ↑i < m) => u { val := ↑i, property := h })
      fun (h : ¬↑i < m) => v { val := ↑i - m, property := sorry }

@[simp] theorem fin_append_apply_zero {n : ℕ} {m : ℕ} {α : Type u_1} {o : ℕ}
    (ho : o + 1 = m + 1 + n) (u : fin (m + 1) → α) (v : fin n → α) : append ho u v 0 = u 0 :=
  rfl

/-! In the previous section, we have discussed inserting or removing elements on the left of a
tuple. In this section, we do the same on the right. A difference is that `fin (n+1)` is constructed
inductively from `fin n` starting from the left, not from the right. This implies that Lean needs
more help to realize that elements belong to the right types, i.e., we need to insert casts at
several places. -/

/-- The beginning of an `n+1` tuple, i.e., its first `n` entries -/
def init {n : ℕ} {α : fin (n + 1) → Type u} (q : (i : fin (n + 1)) → α i) (i : fin n) :
    α (coe_fn cast_succ i) :=
  q (coe_fn cast_succ i)

/-- Adding an element at the end of an `n`-tuple, to get an `n+1`-tuple. The name `snoc` comes from
`cons` (i.e., adding an element to the left of a tuple) read in reverse order. -/
def snoc {n : ℕ} {α : fin (n + 1) → Type u} (p : (i : fin n) → α (coe_fn cast_succ i))
    (x : α (last n)) (i : fin (n + 1)) : α i :=
  dite (subtype.val i < n) (fun (h : subtype.val i < n) => cast sorry (p (cast_lt i h)))
    fun (h : ¬subtype.val i < n) => cast sorry x

@[simp] theorem init_snoc {n : ℕ} {α : fin (n + 1) → Type u} (x : α (last n))
    (p : (i : fin n) → α (coe_fn cast_succ i)) : init (snoc p x) = p :=
  sorry

@[simp] theorem snoc_cast_succ {n : ℕ} {α : fin (n + 1) → Type u} (x : α (last n))
    (p : (i : fin n) → α (coe_fn cast_succ i)) (i : fin n) : snoc p x (coe_fn cast_succ i) = p i :=
  sorry

@[simp] theorem snoc_last {n : ℕ} {α : fin (n + 1) → Type u} (x : α (last n))
    (p : (i : fin n) → α (coe_fn cast_succ i)) : snoc p x (last n) = x :=
  sorry

/-- Updating a tuple and adding an element at the end commute. -/
@[simp] theorem snoc_update {n : ℕ} {α : fin (n + 1) → Type u} (x : α (last n))
    (p : (i : fin n) → α (coe_fn cast_succ i)) (i : fin n) (y : α (coe_fn cast_succ i)) :
    snoc (function.update p i y) x = function.update (snoc p x) (coe_fn cast_succ i) y :=
  sorry

/-- Adding an element at the beginning of a tuple and then updating it amounts to adding it
directly. -/
theorem update_snoc_last {n : ℕ} {α : fin (n + 1) → Type u} (x : α (last n))
    (p : (i : fin n) → α (coe_fn cast_succ i)) (z : α (last n)) :
    function.update (snoc p x) (last n) z = snoc p z :=
  sorry

/-- Concatenating the first element of a tuple with its tail gives back the original tuple -/
@[simp] theorem snoc_init_self {n : ℕ} {α : fin (n + 1) → Type u} (q : (i : fin (n + 1)) → α i) :
    snoc (init q) (q (last n)) = q :=
  sorry

/-- Updating the last element of a tuple does not change the beginning. -/
@[simp] theorem init_update_last {n : ℕ} {α : fin (n + 1) → Type u} (q : (i : fin (n + 1)) → α i)
    (z : α (last n)) : init (function.update q (last n) z) = init q :=
  sorry

/-- Updating an element and taking the beginning commute. -/
@[simp] theorem init_update_cast_succ {n : ℕ} {α : fin (n + 1) → Type u}
    (q : (i : fin (n + 1)) → α i) (i : fin n) (y : α (coe_fn cast_succ i)) :
    init (function.update q (coe_fn cast_succ i) y) = function.update (init q) i y :=
  sorry

/-- `tail` and `init` commute. We state this lemma in a non-dependent setting, as otherwise it
would involve a cast to convince Lean that the two types are equal, making it harder to use. -/
theorem tail_init_eq_init_tail {n : ℕ} {β : Type u_1} (q : fin (n + bit0 1) → β) :
    tail (init q) = init (tail q) :=
  sorry

/-- `cons` and `snoc` commute. We state this lemma in a non-dependent setting, as otherwise it
would involve a cast to convince Lean that the two types are equal, making it harder to use. -/
theorem cons_snoc_eq_snoc_cons {n : ℕ} {β : Type u_1} (a : β) (q : fin n → β) (b : β) :
    cons a (snoc q b) = snoc (cons a q) b :=
  sorry

theorem comp_snoc {n : ℕ} {α : Type u_1} {β : Type u_2} (g : α → β) (q : fin n → α) (y : α) :
    g ∘ snoc q y = snoc (g ∘ q) (g y) :=
  sorry

theorem comp_init {n : ℕ} {α : Type u_1} {β : Type u_2} (g : α → β) (q : fin (Nat.succ n) → α) :
    g ∘ init q = init (g ∘ q) :=
  sorry

/-- Insert an element into a tuple at a given position. For `i = 0` see `fin.cons`,
for `i = fin.last n` see `fin.snoc`. -/
def insert_nth {n : ℕ} {α : fin (n + 1) → Type u} (i : fin (n + 1)) (x : α i)
    (p : (j : fin n) → α (coe_fn (succ_above i) j)) (j : fin (n + 1)) : α j :=
  dite (j = i) (fun (h : j = i) => cast sorry x)
    fun (h : ¬j = i) => cast sorry (p (pred_above i j h))

@[simp] theorem insert_nth_apply_same {n : ℕ} {α : fin (n + 1) → Type u} (i : fin (n + 1)) (x : α i)
    (p : (j : fin n) → α (coe_fn (succ_above i) j)) : insert_nth i x p i = x :=
  sorry

@[simp] theorem insert_nth_apply_succ_above {n : ℕ} {α : fin (n + 1) → Type u} (i : fin (n + 1))
    (x : α i) (p : (j : fin n) → α (coe_fn (succ_above i) j)) (j : fin n) :
    insert_nth i x p (coe_fn (succ_above i) j) = p j :=
  sorry

@[simp] theorem insert_nth_comp_succ_above {n : ℕ} {β : Type v} (i : fin (n + 1)) (x : β)
    (p : fin n → β) : insert_nth i x p ∘ ⇑(succ_above i) = p :=
  funext (insert_nth_apply_succ_above i x p)

theorem insert_nth_eq_iff {n : ℕ} {α : fin (n + 1) → Type u} {i : fin (n + 1)} {x : α i}
    {p : (j : fin n) → α (coe_fn (succ_above i) j)} {q : (j : fin (n + 1)) → α j} :
    insert_nth i x p = q ↔ q i = x ∧ p = fun (j : fin n) => q (coe_fn (succ_above i) j) :=
  sorry

theorem eq_insert_nth_iff {n : ℕ} {α : fin (n + 1) → Type u} {i : fin (n + 1)} {x : α i}
    {p : (j : fin n) → α (coe_fn (succ_above i) j)} {q : (j : fin (n + 1)) → α j} :
    q = insert_nth i x p ↔ q i = x ∧ p = fun (j : fin n) => q (coe_fn (succ_above i) j) :=
  iff.trans eq_comm insert_nth_eq_iff

theorem insert_nth_zero {n : ℕ} {α : fin (n + 1) → Type u} (x : α 0)
    (p : (j : fin n) → α (coe_fn (succ_above 0) j)) :
    insert_nth 0 x p =
        cons x fun (j : fin n) => cast (congr_arg α (congr_fun succ_above_zero j)) (p j) :=
  sorry

@[simp] theorem insert_nth_zero' {n : ℕ} {β : Type v} (x : β) (p : fin n → β) :
    insert_nth 0 x p = cons x p :=
  sorry

theorem insert_nth_last {n : ℕ} {α : fin (n + 1) → Type u} (x : α (last n))
    (p : (j : fin n) → α (coe_fn (succ_above (last n)) j)) :
    insert_nth (last n) x p =
        snoc (fun (j : fin n) => cast (congr_arg α (succ_above_last_apply j)) (p j)) x :=
  sorry

@[simp] theorem insert_nth_last' {n : ℕ} {β : Type v} (x : β) (p : fin n → β) :
    insert_nth (last n) x p = snoc p x :=
  sorry

theorem insert_nth_le_iff {n : ℕ} {α : fin (n + 1) → Type u} [(i : fin (n + 1)) → preorder (α i)]
    {i : fin (n + 1)} {x : α i} {p : (j : fin n) → α (coe_fn (succ_above i) j)}
    {q : (j : fin (n + 1)) → α j} :
    insert_nth i x p ≤ q ↔ x ≤ q i ∧ p ≤ fun (j : fin n) => q (coe_fn (succ_above i) j) :=
  sorry

theorem le_insert_nth_iff {n : ℕ} {α : fin (n + 1) → Type u} [(i : fin (n + 1)) → preorder (α i)]
    {i : fin (n + 1)} {x : α i} {p : (j : fin n) → α (coe_fn (succ_above i) j)}
    {q : (j : fin (n + 1)) → α j} :
    q ≤ insert_nth i x p ↔ q i ≤ x ∧ (fun (j : fin n) => q (coe_fn (succ_above i) j)) ≤ p :=
  sorry

theorem insert_nth_mem_Icc {n : ℕ} {α : fin (n + 1) → Type u} [(i : fin (n + 1)) → preorder (α i)]
    {i : fin (n + 1)} {x : α i} {p : (j : fin n) → α (coe_fn (succ_above i) j)}
    {q₁ : (j : fin (n + 1)) → α j} {q₂ : (j : fin (n + 1)) → α j} :
    insert_nth i x p ∈ set.Icc q₁ q₂ ↔
        x ∈ set.Icc (q₁ i) (q₂ i) ∧
          p ∈
            set.Icc (fun (j : fin n) => q₁ (coe_fn (succ_above i) j))
              fun (j : fin n) => q₂ (coe_fn (succ_above i) j) :=
  sorry

theorem preimage_insert_nth_Icc_of_mem {n : ℕ} {α : fin (n + 1) → Type u}
    [(i : fin (n + 1)) → preorder (α i)] {i : fin (n + 1)} {x : α i} {q₁ : (j : fin (n + 1)) → α j}
    {q₂ : (j : fin (n + 1)) → α j} (hx : x ∈ set.Icc (q₁ i) (q₂ i)) :
    insert_nth i x ⁻¹' set.Icc q₁ q₂ =
        set.Icc (fun (j : fin n) => q₁ (coe_fn (succ_above i) j))
          fun (j : fin n) => q₂ (coe_fn (succ_above i) j) :=
  sorry

theorem preimage_insert_nth_Icc_of_not_mem {n : ℕ} {α : fin (n + 1) → Type u}
    [(i : fin (n + 1)) → preorder (α i)] {i : fin (n + 1)} {x : α i} {q₁ : (j : fin (n + 1)) → α j}
    {q₂ : (j : fin (n + 1)) → α j} (hx : ¬x ∈ set.Icc (q₁ i) (q₂ i)) :
    insert_nth i x ⁻¹' set.Icc q₁ q₂ = ∅ :=
  sorry

/-- `find p` returns the first index `n` where `p n` is satisfied, and `none` if it is never
satisfied. -/
def find {n : ℕ} (p : fin n → Prop) [decidable_pred p] : Option (fin n) := sorry

/-- If `find p = some i`, then `p i` holds -/
theorem find_spec {n : ℕ} (p : fin n → Prop) [decidable_pred p] {i : fin n} (hi : i ∈ find p) :
    p i :=
  sorry

/-- `find p` does not return `none` if and only if `p i` holds at some index `i`. -/
theorem is_some_find_iff {n : ℕ} {p : fin n → Prop} [decidable_pred p] :
    ↥(option.is_some (find p)) ↔ ∃ (i : fin n), p i :=
  sorry

/-- `find p` returns `none` if and only if `p i` never holds. -/
theorem find_eq_none_iff {n : ℕ} {p : fin n → Prop} [decidable_pred p] :
    find p = none ↔ ∀ (i : fin n), ¬p i :=
  sorry

/-- If `find p` returns `some i`, then `p j` does not hold for `j < i`, i.e., `i` is minimal among
the indices where `p` holds. -/
theorem find_min {n : ℕ} {p : fin n → Prop} [decidable_pred p] {i : fin n} (hi : i ∈ find p)
    {j : fin n} (hj : j < i) : ¬p j :=
  sorry

theorem find_min' {n : ℕ} {p : fin n → Prop} [decidable_pred p] {i : fin n} (h : i ∈ find p)
    {j : fin n} (hj : p j) : i ≤ j :=
  le_of_not_gt fun (hij : i > j) => find_min h hij hj

theorem nat_find_mem_find {n : ℕ} {p : fin n → Prop} [decidable_pred p]
    (h : ∃ (i : ℕ), ∃ (hin : i < n), p { val := i, property := hin }) :
    { val := nat.find h, property := Exists.fst (nat.find_spec h) } ∈ find p :=
  sorry

theorem mem_find_iff {n : ℕ} {p : fin n → Prop} [decidable_pred p] {i : fin n} :
    i ∈ find p ↔ p i ∧ ∀ (j : fin n), p j → i ≤ j :=
  sorry

theorem find_eq_some_iff {n : ℕ} {p : fin n → Prop} [decidable_pred p] {i : fin n} :
    find p = some i ↔ p i ∧ ∀ (j : fin n), p j → i ≤ j :=
  mem_find_iff

theorem mem_find_of_unique {n : ℕ} {p : fin n → Prop} [decidable_pred p]
    (h : ∀ (i j : fin n), p i → p j → i = j) {i : fin n} (hi : p i) : i ∈ find p :=
  iff.mpr mem_find_iff { left := hi, right := fun (j : fin n) (hj : p j) => le_of_eq (h i j hi hj) }

@[simp] theorem coe_of_nat_eq_mod (m : ℕ) (n : ℕ) : ↑↑n = n % Nat.succ m :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑↑n = n % Nat.succ m)) (Eq.symm (of_nat_eq_coe m n))))
    (Eq.refl ↑(of_nat n))

@[simp] theorem coe_of_nat_eq_mod' (m : ℕ) (n : ℕ) [I : fact (0 < m)] : ↑(of_nat' n) = n % m := rfl

@[simp] protected theorem add_zero {n : ℕ} (k : fin (n + 1)) : k + 0 = k := sorry

@[simp] protected theorem zero_add {n : ℕ} (k : fin (n + 1)) : 0 + k = k := sorry

@[simp] protected theorem mul_one {n : ℕ} (k : fin (n + 1)) : k * 1 = k := sorry

@[simp] protected theorem one_mul {n : ℕ} (k : fin (n + 1)) : 1 * k = k := sorry

@[simp] protected theorem mul_zero {n : ℕ} (k : fin (n + 1)) : k * 0 = 0 := sorry

@[simp] protected theorem zero_mul {n : ℕ} (k : fin (n + 1)) : 0 * k = 0 := sorry

protected instance add_comm_monoid (n : ℕ) : add_comm_monoid (fin (n + 1)) :=
  add_comm_monoid.mk Add.add sorry 0 fin.zero_add fin.add_zero sorry

end Mathlib