/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.fintype.basic
import Mathlib.algebra.big_operators.order
import Mathlib.PostPort

universes u v w 

namespace Mathlib

/-!
# Pigeonhole principles

Given pigeons (possibly infinitely many) in pigeonholes, the
pigeonhole principle states that, if there are more pigeons than
pigeonholes, then there is a pigeonhole with two or more pigeons.

There are a few variations on this statement, and the conclusion can
be made stronger depending on how many pigeons you know you might
have.

The basic statements of the pigeonhole principle appear in the
following locations:

* `data.finset.basic` has `finset.exists_ne_map_eq_of_card_lt_of_maps_to`
* `data.fintype.basic` has `fintype.exists_ne_map_eq_of_card_lt`
* `data.fintype.basic` has `fintype.exists_ne_map_eq_of_infinite`
* `data.fintype.basic` has `fintype.exists_infinite_fiber`

This module gives access to these pigeonhole principles along with 20 more.
The versions vary by:

* using a function between `fintype`s or a function between possibly infinite types restricted to
  `finset`s;
* counting pigeons by a general weight function (`∑ x in s, w x`) or by heads (`finset.card s`);
* using strict or non-strict inequalities;
* establishing upper or lower estimate on the number (or the total weight) of the pigeons in one
  pigeonhole;
* in case when we count pigeons by some weight function `w` and consider a function `f` between
  `finset`s `s` and `t`, we can either assume that each pigeon is in one of the pigeonholes
  (`∀ x ∈ s, f x ∈ t`), or assume that for `y ∉ t`, the total weight of the pigeons in this
  pigeonhole `∑ x in s.filter (λ x, f x = y), w x` is nonpositive or nonnegative depending on
  the inequality we are proving.

Lemma names follow `mathlib` convention (e.g.,
`finset.exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum`); "pigeonhole principle" is mentioned in the
docstrings instead of the names.

## See also

* `ordinal.infinite_pigeonhole`: pigeonhole principle for cardinals, formulated using cofinality;

* `measure_theory.exists_nonempty_inter_of_measure_univ_lt_tsum_measure`,
  `measure_theory.exists_nonempty_inter_of_measure_univ_lt_sum_measure`: pigeonhole principle in a
  measure space.

## Tags

pigeonhole principle
-/

namespace finset


/-!
### The pigeonhole principles on `finset`s, pigeons counted by weight

In this section we prove the following version of the pigeonhole principle: if the total weight of a
finite set of pigeons is greater than `n •ℕ b`, and they are sorted into `n` pigeonholes, then for
some pigeonhole, the total weight of the pigeons in this pigeonhole is greateer than `b`, and a few
variations of this theorem.

The principle is formalized in the following way, see
`finset.exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum`: if `f : α → β` is a function which maps all
elements of `s : finset α` to `t : finset β` and `card t •ℕ b < ∑ x in s, w x`, where `w : α → M` is
a weight function taking values in a `linear_ordered_cancel_add_comm_monoid`, then for
some `y ∈ t`, the sum of the weights of all `x ∈ s` such that `f x = y` is greater than `b`.

There are a few bits we can change in this theorem:

* reverse all inequalities, with obvious adjustments to the name;
* replace the assumption `∀ a ∈ s, f a ∈ t` with
  `∀ y ∉ t, (∑ x in s.filter (λ x, f x = y), w x) ≤ 0`,
  and replace `of_maps_to` with `of_sum_fiber_nonpos` in the name;
* use non-strict inequalities assuming `t` is nonempty.

We can do all these variations independently, so we have eight versions of the theorem.
-/

/-!
#### Strict inequality versions
-/

/-- The pigeonhole principle for finitely many pigeons counted by weight, strict inequality version:
if the total weight of a finite set of pigeons is greater than `n •ℕ b`, and they are sorted into
`n` pigeonholes, then for some pigeonhole, the total weight of the pigeons in this pigeonhole is
greater than `b`. -/
theorem exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum {α : Type u} {β : Type v} {M : Type w} [linear_ordered_cancel_add_comm_monoid M] [DecidableEq β] {s : finset α} {t : finset β} {f : α → β} {w : α → M} {b : M} (hf : ∀ (a : α), a ∈ s → f a ∈ t) (hb : card t •ℕ b < finset.sum s fun (x : α) => w x) : ∃ (y : β), ∃ (H : y ∈ t), b < finset.sum (filter (fun (x : α) => f x = y) s) fun (x : α) => w x := sorry

/-- The pigeonhole principle for finitely many pigeons counted by weight, strict inequality version:
if the total weight of a finite set of pigeons is less than `n •ℕ b`, and they are sorted into `n`
pigeonholes, then for some pigeonhole, the total weight of the pigeons in this pigeonhole is less
than `b`. -/
theorem exists_sum_fiber_lt_of_maps_to_of_sum_lt_nsmul {α : Type u} {β : Type v} {M : Type w} [linear_ordered_cancel_add_comm_monoid M] [DecidableEq β] {s : finset α} {t : finset β} {f : α → β} {w : α → M} {b : M} (hf : ∀ (a : α), a ∈ s → f a ∈ t) (hb : (finset.sum s fun (x : α) => w x) < card t •ℕ b) : ∃ (y : β), ∃ (H : y ∈ t), (finset.sum (filter (fun (x : α) => f x = y) s) fun (x : α) => w x) < b :=
  exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum hf hb

/-- The pigeonhole principle for finitely many pigeons counted by weight, strict inequality version:
if the total weight of a finite set of pigeons is greater than `n •ℕ b`, they are sorted into some
pigeonholes, and for all but `n` pigeonholes the total weight of the pigeons there is nonpositive,
then for at least one of these `n` pigeonholes, the total weight of the pigeons in this pigeonhole
is greater than `b`. -/
theorem exists_lt_sum_fiber_of_sum_fiber_nonpos_of_nsmul_lt_sum {α : Type u} {β : Type v} {M : Type w} [linear_ordered_cancel_add_comm_monoid M] [DecidableEq β] {s : finset α} {t : finset β} {f : α → β} {w : α → M} {b : M} (ht : ∀ (y : β), ¬y ∈ t → (finset.sum (filter (fun (x : α) => f x = y) s) fun (x : α) => w x) ≤ 0) (hb : card t •ℕ b < finset.sum s fun (x : α) => w x) : ∃ (y : β), ∃ (H : y ∈ t), b < finset.sum (filter (fun (x : α) => f x = y) s) fun (x : α) => w x := sorry

/-- The pigeonhole principle for finitely many pigeons counted by weight, strict inequality version:
if the total weight of a finite set of pigeons is less than `n •ℕ b`, they are sorted into some
pigeonholes, and for all but `n` pigeonholes the total weight of the pigeons there is nonnegative,
then for at least one of these `n` pigeonholes, the total weight of the pigeons in this pigeonhole
is less than `b`. -/
theorem exists_sum_fiber_lt_of_sum_fiber_nonneg_of_sum_lt_nsmul {α : Type u} {β : Type v} {M : Type w} [linear_ordered_cancel_add_comm_monoid M] [DecidableEq β] {s : finset α} {t : finset β} {f : α → β} {w : α → M} {b : M} (ht : ∀ (y : β), ¬y ∈ t → 0 ≤ finset.sum (filter (fun (x : α) => f x = y) s) fun (x : α) => w x) (hb : (finset.sum s fun (x : α) => w x) < card t •ℕ b) : ∃ (y : β), ∃ (H : y ∈ t), (finset.sum (filter (fun (x : α) => f x = y) s) fun (x : α) => w x) < b :=
  exists_lt_sum_fiber_of_sum_fiber_nonpos_of_nsmul_lt_sum ht hb

/-!
#### Non-strict inequality versions
-/

/-- The pigeonhole principle for finitely many pigeons counted by weight, non-strict inequality
version: if the total weight of a finite set of pigeons is greater than or equal to `n •ℕ b`, and
they are sorted into `n > 0` pigeonholes, then for some pigeonhole, the total weight of the pigeons
in this pigeonhole is greater than or equal to `b`. -/
theorem exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum {α : Type u} {β : Type v} {M : Type w} [linear_ordered_cancel_add_comm_monoid M] [DecidableEq β] {s : finset α} {t : finset β} {f : α → β} {w : α → M} {b : M} (hf : ∀ (a : α), a ∈ s → f a ∈ t) (ht : finset.nonempty t) (hb : card t •ℕ b ≤ finset.sum s fun (x : α) => w x) : ∃ (y : β), ∃ (H : y ∈ t), b ≤ finset.sum (filter (fun (x : α) => f x = y) s) fun (x : α) => w x := sorry

/-- The pigeonhole principle for finitely many pigeons counted by weight, non-strict inequality
version: if the total weight of a finite set of pigeons is less than or equal to `n •ℕ b`, and they
are sorted into `n > 0` pigeonholes, then for some pigeonhole, the total weight of the pigeons in
this pigeonhole is less than or equal to `b`. -/
theorem exists_sum_fiber_le_of_maps_to_of_sum_le_nsmul {α : Type u} {β : Type v} {M : Type w} [linear_ordered_cancel_add_comm_monoid M] [DecidableEq β] {s : finset α} {t : finset β} {f : α → β} {w : α → M} {b : M} (hf : ∀ (a : α), a ∈ s → f a ∈ t) (ht : finset.nonempty t) (hb : (finset.sum s fun (x : α) => w x) ≤ card t •ℕ b) : ∃ (y : β), ∃ (H : y ∈ t), (finset.sum (filter (fun (x : α) => f x = y) s) fun (x : α) => w x) ≤ b :=
  exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum hf ht hb

/-- The pigeonhole principle for finitely many pigeons counted by weight, non-strict inequality
version: if the total weight of a finite set of pigeons is greater than or equal to `n •ℕ b`, they
are sorted into some pigeonholes, and for all but `n > 0` pigeonholes the total weight of the
pigeons there is nonpositive, then for at least one of these `n` pigeonholes, the total weight of
the pigeons in this pigeonhole is greater than or equal to `b`. -/
theorem exists_le_sum_fiber_of_sum_fiber_nonpos_of_nsmul_le_sum {α : Type u} {β : Type v} {M : Type w} [linear_ordered_cancel_add_comm_monoid M] [DecidableEq β] {s : finset α} {t : finset β} {f : α → β} {w : α → M} {b : M} (hf : ∀ (y : β), ¬y ∈ t → (finset.sum (filter (fun (x : α) => f x = y) s) fun (x : α) => w x) ≤ 0) (ht : finset.nonempty t) (hb : card t •ℕ b ≤ finset.sum s fun (x : α) => w x) : ∃ (y : β), ∃ (H : y ∈ t), b ≤ finset.sum (filter (fun (x : α) => f x = y) s) fun (x : α) => w x := sorry

/-- The pigeonhole principle for finitely many pigeons counted by weight, non-strict inequality
version: if the total weight of a finite set of pigeons is less than or equal to `n •ℕ b`, they are
sorted into some pigeonholes, and for all but `n > 0` pigeonholes the total weight of the pigeons
there is nonnegative, then for at least one of these `n` pigeonholes, the total weight of the
pigeons in this pigeonhole is less than or equal to `b`. -/
theorem exists_sum_fiber_le_of_sum_fiber_nonneg_of_sum_le_nsmul {α : Type u} {β : Type v} {M : Type w} [linear_ordered_cancel_add_comm_monoid M] [DecidableEq β] {s : finset α} {t : finset β} {f : α → β} {w : α → M} {b : M} (hf : ∀ (y : β), ¬y ∈ t → 0 ≤ finset.sum (filter (fun (x : α) => f x = y) s) fun (x : α) => w x) (ht : finset.nonempty t) (hb : (finset.sum s fun (x : α) => w x) ≤ card t •ℕ b) : ∃ (y : β), ∃ (H : y ∈ t), (finset.sum (filter (fun (x : α) => f x = y) s) fun (x : α) => w x) ≤ b :=
  exists_le_sum_fiber_of_sum_fiber_nonpos_of_nsmul_le_sum hf ht hb

/-!
### The pigeonhole principles on `finset`s, pigeons counted by heads

In this section we formalize a few versions of the following pigeonhole principle: there is a
pigeonhole with at least as many pigeons as the ceiling of the average number of pigeons across all
pigeonholes.

First, we can use strict or non-strict inequalities. While the versions with non-strict inequalities
are weaker than those with strict inequalities, sometimes it might be more convenient to apply the
weaker version. Second, we can either state that there exists a pigeonhole with at least `n`
pigeons, or state that there exists a pigeonhole with at most `n` pigeons. In the latter case we do
not need the assumption `∀ a ∈ s, f a ∈ t`.

So, we prove four theorems: `finset.exists_lt_card_fiber_of_maps_to_of_mul_lt_card`,
`finset.exists_le_card_fiber_of_maps_to_of_mul_le_card`,
`finset.exists_card_fiber_lt_of_card_lt_mul`, and `finset.exists_card_fiber_le_of_card_le_mul`. -/

/-- The pigeonhole principle for finitely many pigeons counted by heads: there is a pigeonhole with
at least as many pigeons as the ceiling of the average number of pigeons across all pigeonholes.
("The maximum is at least the mean" specialized to integers.)

More formally, given a function between finite sets `s` and `t` and a natural number `n` such that
`card t * n < card s`, there exists `y ∈ t` such that its preimage in `s` has more than `n`
elements. -/
theorem exists_lt_card_fiber_of_mul_lt_card_of_maps_to {α : Type u} {β : Type v} [DecidableEq β] {s : finset α} {t : finset β} {f : α → β} {n : ℕ} (hf : ∀ (a : α), a ∈ s → f a ∈ t) (hn : card t * n < card s) : ∃ (y : β), ∃ (H : y ∈ t), n < card (filter (fun (x : α) => f x = y) s) := sorry

/-- The pigeonhole principle for finitely many pigeons counted by heads: there is a pigeonhole with
at most as many pigeons as the floor of the average number of pigeons across all pigeonholes.  ("The
minimum is at most the mean" specialized to integers.)

More formally, given a function `f`, a finite sets `s` in its domain, a finite set `t` in its
codomain, and a natural number `n` such that `card s < card t * n`, there exists `y ∈ t` such that
its preimage in `s` has less than `n` elements. -/
theorem exists_card_fiber_lt_of_card_lt_mul {α : Type u} {β : Type v} [DecidableEq β] {s : finset α} {t : finset β} {f : α → β} {n : ℕ} (hn : card s < card t * n) : ∃ (y : β), ∃ (H : y ∈ t), card (filter (fun (x : α) => f x = y) s) < n := sorry

/-- The pigeonhole principle for finitely many pigeons counted by heads: given a function between
finite sets `s` and `t` and a natural number `n` such that `card t * n ≤ card s`, there exists `y ∈
t` such that its preimage in `s` has at least `n` elements. See also
`finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to` for a stronger statement. -/
theorem exists_le_card_fiber_of_mul_le_card_of_maps_to {α : Type u} {β : Type v} [DecidableEq β] {s : finset α} {t : finset β} {f : α → β} {n : ℕ} (hf : ∀ (a : α), a ∈ s → f a ∈ t) (ht : finset.nonempty t) (hn : card t * n ≤ card s) : ∃ (y : β), ∃ (H : y ∈ t), n ≤ card (filter (fun (x : α) => f x = y) s) := sorry

/-- The pigeonhole principle for finitely many pigeons counted by heads: given a function `f`, a
finite sets `s` in its domain, a finite set `t` in its codomain, and a natural number `n` such that
`card s ≤ card t * n`, there exists `y ∈ t` such that its preimage in `s` has no more than `n`
elements. See also `finset.exists_card_fiber_lt_of_card_lt_mul` for a stronger statement. -/
theorem exists_card_fiber_le_of_card_le_mul {α : Type u} {β : Type v} [DecidableEq β] {s : finset α} {t : finset β} {f : α → β} {n : ℕ} (ht : finset.nonempty t) (hn : card s ≤ card t * n) : ∃ (y : β), ∃ (H : y ∈ t), card (filter (fun (x : α) => f x = y) s) ≤ n := sorry

end finset


namespace fintype


/-!
### The pigeonhole principles on `fintypes`s, pigeons counted by weight

In this section we specialize theorems from the previous section to the special case of functions
between `fintype`s and `s = univ`, `t = univ`. In this case the assumption `∀ x ∈ s, f x ∈ t` always
holds, so we have four theorems instead of eight. -/

/-- The pigeonhole principle for finitely many pigeons of different weights, strict inequality
version: there is a pigeonhole with the total weight of pigeons in it greater than `b` provided that
the total number of pigeonholes times `b` is less than the total weight of all pigeons. -/
theorem exists_lt_sum_fiber_of_nsmul_lt_sum {α : Type u} {β : Type v} {M : Type w} [linear_ordered_cancel_add_comm_monoid M] [DecidableEq β] [fintype α] [fintype β] (f : α → β) {w : α → M} {b : M} (hb : card β •ℕ b < finset.sum finset.univ fun (x : α) => w x) : ∃ (y : β), b < finset.sum (finset.filter (fun (x : α) => f x = y) finset.univ) fun (x : α) => w x := sorry

/-- The pigeonhole principle for finitely many pigeons of different weights, non-strict inequality
version: there is a pigeonhole with the total weight of pigeons in it greater than or equal to `b`
provided that the total number of pigeonholes times `b` is less than or equal to the total weight of
all pigeons. -/
theorem exists_le_sum_fiber_of_nsmul_le_sum {α : Type u} {β : Type v} {M : Type w} [linear_ordered_cancel_add_comm_monoid M] [DecidableEq β] [fintype α] [fintype β] (f : α → β) {w : α → M} {b : M} [Nonempty β] (hb : card β •ℕ b ≤ finset.sum finset.univ fun (x : α) => w x) : ∃ (y : β), b ≤ finset.sum (finset.filter (fun (x : α) => f x = y) finset.univ) fun (x : α) => w x := sorry

/-- The pigeonhole principle for finitely many pigeons of different weights, strict inequality
version: there is a pigeonhole with the total weight of pigeons in it less than `b` provided that
the total number of pigeonholes times `b` is greater than the total weight of all pigeons. -/
theorem exists_sum_fiber_lt_of_sum_lt_nsmul {α : Type u} {β : Type v} {M : Type w} [linear_ordered_cancel_add_comm_monoid M] [DecidableEq β] [fintype α] [fintype β] (f : α → β) {w : α → M} {b : M} (hb : (finset.sum finset.univ fun (x : α) => w x) < card β •ℕ b) : ∃ (y : β), (finset.sum (finset.filter (fun (x : α) => f x = y) finset.univ) fun (x : α) => w x) < b :=
  exists_lt_sum_fiber_of_nsmul_lt_sum (fun (x : α) => f x) hb

/-- The pigeonhole principle for finitely many pigeons of different weights, non-strict inequality
version: there is a pigeonhole with the total weight of pigeons in it less than or equal to `b`
provided that the total number of pigeonholes times `b` is greater than or equal to the total weight
of all pigeons. -/
theorem exists_sum_fiber_le_of_sum_le_nsmul {α : Type u} {β : Type v} {M : Type w} [linear_ordered_cancel_add_comm_monoid M] [DecidableEq β] [fintype α] [fintype β] (f : α → β) {w : α → M} {b : M} [Nonempty β] (hb : (finset.sum finset.univ fun (x : α) => w x) ≤ card β •ℕ b) : ∃ (y : β), (finset.sum (finset.filter (fun (x : α) => f x = y) finset.univ) fun (x : α) => w x) ≤ b :=
  exists_le_sum_fiber_of_nsmul_le_sum (fun (x : α) => f x) hb

/--
The strong pigeonhole principle for finitely many pigeons and pigeonholes.
There is a pigeonhole with at least as many pigeons as
the ceiling of the average number of pigeons across all pigeonholes.
("The maximum is at least the mean" specialized to integers.)

More formally, given a function `f` between finite types `α` and `β` and a number `n` such that
`card β * n < card α`, there exists an element `y : β` such that its preimage has more than `n`
elements. -/
theorem exists_lt_card_fiber_of_mul_lt_card {α : Type u} {β : Type v} [DecidableEq β] [fintype α] [fintype β] (f : α → β) {n : ℕ} (hn : card β * n < card α) : ∃ (y : β), n < finset.card (finset.filter (fun (x : α) => f x = y) finset.univ) := sorry

/--
The strong pigeonhole principle for finitely many pigeons and pigeonholes.
There is a pigeonhole with at most as many pigeons as
the floor of the average number of pigeons across all pigeonholes.
("The minimum is at most the mean" specialized to integers.)

More formally, given a function `f` between finite types `α` and `β` and a number `n` such that
`card α < card β * n`, there exists an element `y : β` such that its preimage has less than `n`
elements. -/
theorem exists_card_fiber_lt_of_card_lt_mul {α : Type u} {β : Type v} [DecidableEq β] [fintype α] [fintype β] (f : α → β) {n : ℕ} (hn : card α < card β * n) : ∃ (y : β), finset.card (finset.filter (fun (x : α) => f x = y) finset.univ) < n := sorry

/-- The strong pigeonhole principle for finitely many pigeons and pigeonholes.  Given a function `f`
between finite types `α` and `β` and a number `n` such that `card β * n ≤ card α`, there exists an
element `y : β` such that its preimage has at least `n` elements. See also
`fintype.exists_lt_card_fiber_of_mul_lt_card` for a stronger statement. -/
theorem exists_le_card_fiber_of_mul_le_card {α : Type u} {β : Type v} [DecidableEq β] [fintype α] [fintype β] (f : α → β) {n : ℕ} [Nonempty β] (hn : card β * n ≤ card α) : ∃ (y : β), n ≤ finset.card (finset.filter (fun (x : α) => f x = y) finset.univ) := sorry

/-- The strong pigeonhole principle for finitely many pigeons and pigeonholes.  Given a function `f`
between finite types `α` and `β` and a number `n` such that `card α ≤ card β * n`, there exists an
element `y : β` such that its preimage has at most `n` elements. See also
`fintype.exists_card_fiber_lt_of_card_lt_mul` for a stronger statement. -/
theorem exists_card_fiber_le_of_card_le_mul {α : Type u} {β : Type v} [DecidableEq β] [fintype α] [fintype β] (f : α → β) {n : ℕ} [Nonempty β] (hn : card α ≤ card β * n) : ∃ (y : β), finset.card (finset.filter (fun (x : α) => f x = y) finset.univ) ≤ n := sorry

