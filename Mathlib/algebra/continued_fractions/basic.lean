/-
Copyright (c) 2019 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.seq.seq
import Mathlib.algebra.field
import Mathlib.PostPort

universes u_1 l u_2 

namespace Mathlib

/-!
# Basic Definitions/Theorems for Continued Fractions

## Summary

We define generalised, simple, and regular continued fractions and functions to evaluate their
convergents. We follow the naming conventions from Wikipedia and [wall2018analytic], Chapter 1.

## Main definitions

1. Generalised continued fractions (gcfs)
2. Simple continued fractions (scfs)
3. (Regular) continued fractions ((r)cfs)
4. Computation of convergents using the recurrence relation in `convergents`.
5. Computation of convergents by directly evaluating the fraction described by the gcf in
`convergents'`.

## Implementation notes

1. The most commonly used kind of continued fractions in the literature are regular continued
fractions. We hence just call them `continued_fractions` in the library.
2. We use sequences from `data.seq` to encode potentially infinite sequences.

## References

- <https://en.wikipedia.org/wiki/Generalized_continued_fraction>
- [Wall, H.S., *Analytic Theory of Continued Fractions*][wall2018analytic]

## Tags

numerics, number theory, approximations, fractions
-/

-- Fix a carrier `α`.

/-- We collect a partial numerator `aᵢ` and partial denominator `bᵢ` in a pair `⟨aᵢ,bᵢ⟩`. -/
structure generalized_continued_fraction.pair (α : Type u_1) 
where
  a : α
  b : α

/- Interlude: define some expected coercions and instances. -/

namespace generalized_continued_fraction.pair


/-- Make a `gcf.pair` printable. -/
protected instance has_repr {α : Type u_1} [has_repr α] : has_repr (pair α) := sorry

/-- Maps a function `f` on both components of a given pair. -/
def map {α : Type u_1} {β : Type u_2} (f : α → β) (gp : pair α) : pair β :=
  mk (f (a gp)) (f (b gp))

/-! Interlude: define some expected coercions. -/

/- Fix another type `β` which we will convert to. -/

/-- Coerce a pair by elementwise coercion. -/
protected instance has_coe_to_generalized_continued_fraction_pair {α : Type u_1} {β : Type u_2} [has_coe α β] : has_coe (pair α) (pair β) :=
  has_coe.mk (map coe)

@[simp] theorem coe_to_generalized_continued_fraction_pair {α : Type u_1} {β : Type u_2} [has_coe α β] {a : α} {b : α} : ↑(mk a b) = mk ↑a ↑b :=
  rfl

end generalized_continued_fraction.pair


/--
A *generalised continued fraction* (gcf) is a potentially infinite expression of the form

                                a₀
                h + ---------------------------
                                  a₁
                      b₀ + --------------------
                                    a₂
                            b₁ + --------------
                                        a₃
                                  b₂ + --------
                                      b₃ + ...

where `h` is called the *head term* or *integer part*, the `aᵢ` are called the
*partial numerators* and the `bᵢ` the *partial denominators* of the gcf.
We store the sequence of partial numerators and denominators in a sequence of
generalized_continued_fraction.pairs `s`.
For convenience, one often writes `[h; (a₀, b₀), (a₁, b₁), (a₂, b₂),...]`.
-/
structure generalized_continued_fraction (α : Type u_1) 
where
  h : α
  s : seq (generalized_continued_fraction.pair α)

namespace generalized_continued_fraction


/-- Constructs a generalized continued fraction without fractional part. -/
def of_integer {α : Type u_1} (a : α) : generalized_continued_fraction α :=
  mk a seq.nil

protected instance inhabited {α : Type u_1} [Inhabited α] : Inhabited (generalized_continued_fraction α) :=
  { default := of_integer Inhabited.default }

/-- Returns the sequence of partial numerators `aᵢ` of `g`. -/
/-- Returns the sequence of partial denominators `bᵢ` of `g`. -/
def partial_numerators {α : Type u_1} (g : generalized_continued_fraction α) : seq α :=
  seq.map pair.a (s g)

def partial_denominators {α : Type u_1} (g : generalized_continued_fraction α) : seq α :=
  seq.map pair.b (s g)

/-- A gcf terminated at position `n` if its sequence terminates at position `n`. -/
def terminated_at {α : Type u_1} (g : generalized_continued_fraction α) (n : ℕ) :=
  seq.terminated_at (s g) n

/-- It is decidable whether a gcf terminated at a given position. -/
protected instance terminated_at_decidable {α : Type u_1} (g : generalized_continued_fraction α) (n : ℕ) : Decidable (terminated_at g n) :=
  eq.mpr sorry (seq.terminated_at_decidable (s g) n)

/-- A gcf terminates if its sequence terminates. -/
def terminates {α : Type u_1} (g : generalized_continued_fraction α) :=
  seq.terminates (s g)

/-! Interlude: define some expected coercions. -/

/- Fix another type `β` which we will convert to. -/

/-- Coerce a gcf by elementwise coercion. -/
protected instance has_coe_to_generalized_continued_fraction {α : Type u_1} {β : Type u_2} [has_coe α β] : has_coe (generalized_continued_fraction α) (generalized_continued_fraction β) :=
  has_coe.mk fun (g : generalized_continued_fraction α) => mk (↑(h g)) (seq.map coe (s g))

@[simp] theorem coe_to_generalized_continued_fraction {α : Type u_1} {β : Type u_2} [has_coe α β] {g : generalized_continued_fraction α} : ↑g = mk (↑(h g)) (seq.map coe (s g)) :=
  rfl

end generalized_continued_fraction


/--
A generalized continued fraction is a *simple continued fraction* if all partial numerators are
equal to one.

                                1
                h + ---------------------------
                                  1
                      b₀ + --------------------
                                    1
                            b₁ + --------------
                                        1
                                  b₂ + --------
                                      b₃ + ...

-/
def generalized_continued_fraction.is_simple_continued_fraction {α : Type u_1} (g : generalized_continued_fraction α) [HasOne α] :=
  ∀ (n : ℕ) (aₙ : α), seq.nth (generalized_continued_fraction.partial_numerators g) n = some aₙ → aₙ = 1

/--
A *simple continued fraction* (scf) is a generalized continued fraction (gcf) whose partial
numerators are equal to one.

                                1
                h + ---------------------------
                                  1
                      b₀ + --------------------
                                    1
                            b₁ + --------------
                                        1
                                  b₂ + --------
                                      b₃ + ...

For convenience, one often writes `[h; b₀, b₁, b₂,...]`.
It is encoded as the subtype of gcfs that satisfy
`generalized_continued_fraction.is_simple_continued_fraction`.
 -/
def simple_continued_fraction (α : Type u_1) [HasOne α] :=
  Subtype fun (g : generalized_continued_fraction α) => generalized_continued_fraction.is_simple_continued_fraction g

/- Interlude: define some expected coercions. -/

namespace simple_continued_fraction


/-- Constructs a simple continued fraction without fractional part. -/
def of_integer {α : Type u_1} [HasOne α] (a : α) : simple_continued_fraction α :=
  { val := generalized_continued_fraction.of_integer a, property := sorry }

protected instance inhabited {α : Type u_1} [HasOne α] : Inhabited (simple_continued_fraction α) :=
  { default := of_integer 1 }

/-- Lift a scf to a gcf using the inclusion map. -/
protected instance has_coe_to_generalized_continued_fraction {α : Type u_1} [HasOne α] : has_coe (simple_continued_fraction α) (generalized_continued_fraction α) :=
  eq.mpr sorry Mathlib.coe_subtype

theorem coe_to_generalized_continued_fraction {α : Type u_1} [HasOne α] {s : simple_continued_fraction α} : ↑s = subtype.val s :=
  rfl

end simple_continued_fraction


/--
A simple continued fraction is a *(regular) continued fraction* ((r)cf) if all partial denominators
`bᵢ` are positive, i.e. `0 < bᵢ`.
-/
def simple_continued_fraction.is_regular_continued_fraction {α : Type u_1} [HasOne α] [HasZero α] [HasLess α] (s : simple_continued_fraction α) :=
  ∀ (n : ℕ) (bₙ : α), seq.nth (generalized_continued_fraction.partial_denominators ↑s) n = some bₙ → 0 < bₙ

/--
A *(regular) continued fraction* ((r)cf) is a simple continued fraction (scf) whose partial
denominators are all positive. It is the subtype of scfs that satisfy
`simple_continued_fraction.is_regular_continued_fraction`.
 -/
def continued_fraction (α : Type u_1) [HasOne α] [HasZero α] [HasLess α] :=
  Subtype fun (s : simple_continued_fraction α) => simple_continued_fraction.is_regular_continued_fraction s

/- Interlude: define some expected coercions. -/

namespace continued_fraction


/-- Constructs a continued fraction without fractional part. -/
def of_integer {α : Type u_1} [HasOne α] [HasZero α] [HasLess α] (a : α) : continued_fraction α :=
  { val := simple_continued_fraction.of_integer a, property := sorry }

protected instance inhabited {α : Type u_1} [HasOne α] [HasZero α] [HasLess α] : Inhabited (continued_fraction α) :=
  { default := of_integer 0 }

/-- Lift a cf to a scf using the inclusion map. -/
protected instance has_coe_to_simple_continued_fraction {α : Type u_1} [HasOne α] [HasZero α] [HasLess α] : has_coe (continued_fraction α) (simple_continued_fraction α) :=
  eq.mpr sorry Mathlib.coe_subtype

theorem coe_to_simple_continued_fraction {α : Type u_1} [HasOne α] [HasZero α] [HasLess α] {c : continued_fraction α} : ↑c = subtype.val c :=
  rfl

/-- Lift a cf to a scf using the inclusion map. -/
protected instance has_coe_to_generalized_continued_fraction {α : Type u_1} [HasOne α] [HasZero α] [HasLess α] : has_coe (continued_fraction α) (generalized_continued_fraction α) :=
  has_coe.mk fun (c : continued_fraction α) => ↑↑c

theorem coe_to_generalized_continued_fraction {α : Type u_1} [HasOne α] [HasZero α] [HasLess α] {c : continued_fraction α} : ↑c = ↑(subtype.val c) :=
  rfl

end continued_fraction


/-
We now define how to compute the convergents of a gcf. There are two standard ways to do this:
directly evaluating the (infinite) fraction described by the gcf or using a recurrence relation.
For (r)cfs, these computations are equivalent as shown in
`algebra.continued_fractions.convergents_equiv`.
-/

namespace generalized_continued_fraction


-- Fix a division ring for the computations.

/-
We start with the definition of the recurrence relation. Given a gcf `g`, for all `n ≥ 1`, we define
- `A₋₁ = 1,  A₀ = h,  Aₙ = bₙ₋₁ * Aₙ₋₁ + aₙ₋₁ * Aₙ₋₂`, and
- `B₋₁ = 0,  B₀ = 1,  Bₙ = bₙ₋₁ * Bₙ₋₁ + aₙ₋₁ * Bₙ₋₂`.

`Aₙ, `Bₙ` are called the *nth continuants*, Aₙ the *nth numerator*, and `Bₙ` the
*nth denominator* of `g`. The *nth convergent* of `g` is given by `Aₙ / Bₙ`.
-/

/--
Returns the next numerator `Aₙ = bₙ₋₁ * Aₙ₋₁ + aₙ₋₁ * Aₙ₋₂`, where `predA` is `Aₙ₋₁`,
`ppredA` is `Aₙ₋₂`, `a` is `aₙ₋₁`, and `b` is `bₙ₋₁`.
-/
def next_numerator {K : Type u_2} [division_ring K] (a : K) (b : K) (ppredA : K) (predA : K) : K :=
  b * predA + a * ppredA

/--
Returns the next denominator `Bₙ = bₙ₋₁ * Bₙ₋₁ + aₙ₋₁ * Bₙ₋₂``, where `predB` is `Bₙ₋₁` and
`ppredB` is `Bₙ₋₂`, `a` is `aₙ₋₁`, and `b` is `bₙ₋₁`.
-/
def next_denominator {K : Type u_2} [division_ring K] (aₙ : K) (bₙ : K) (ppredB : K) (predB : K) : K :=
  bₙ * predB + aₙ * ppredB

/--
Returns the next continuants `⟨Aₙ, Bₙ⟩` using `next_numerator` and `next_denominator`, where `pred`
is `⟨Aₙ₋₁, Bₙ₋₁⟩`, `ppred` is `⟨Aₙ₋₂, Bₙ₋₂⟩`, `a` is `aₙ₋₁`, and `b` is `bₙ₋₁`.
-/
def next_continuants {K : Type u_2} [division_ring K] (a : K) (b : K) (ppred : pair K) (pred : pair K) : pair K :=
  pair.mk (next_numerator a b (pair.a ppred) (pair.a pred)) (next_denominator a b (pair.b ppred) (pair.b pred))

/-- Returns the continuants `⟨Aₙ₋₁, Bₙ₋₁⟩` of `g`. -/
def continuants_aux {K : Type u_2} [division_ring K] (g : generalized_continued_fraction K) : stream (pair K) :=
  sorry

/-- Returns the continuants `⟨Aₙ, Bₙ⟩` of `g`. -/
def continuants {K : Type u_2} [division_ring K] (g : generalized_continued_fraction K) : stream (pair K) :=
  stream.tail (continuants_aux g)

/-- Returns the numerators `Aₙ` of `g`. -/
def numerators {K : Type u_2} [division_ring K] (g : generalized_continued_fraction K) : stream K :=
  stream.map pair.a (continuants g)

/-- Returns the denominators `Bₙ` of `g`. -/
def denominators {K : Type u_2} [division_ring K] (g : generalized_continued_fraction K) : stream K :=
  stream.map pair.b (continuants g)

/-- Returns the convergents `Aₙ / Bₙ` of `g`, where `Aₙ, Bₙ` are the nth continuants of `g`. -/
def convergents {K : Type u_2} [division_ring K] (g : generalized_continued_fraction K) : stream K :=
  fun (n : ℕ) => numerators g n / denominators g n

/--
Returns the approximation of the fraction described by the given sequence up to a given position n.
For example, `convergents'_aux [(1, 2), (3, 4), (5, 6)] 2 = 1 / (2 + 3 / 4)` and
`convergents'_aux [(1, 2), (3, 4), (5, 6)] 0 = 0`.
-/
def convergents'_aux {K : Type u_2} [division_ring K] : seq (pair K) → ℕ → K :=
  sorry

/--
Returns the convergents of `g` by evaluating the fraction described by `g` up to a given
position `n`. For example, `convergents' [9; (1, 2), (3, 4), (5, 6)] 2 = 9 + 1 / (2 + 3 / 4)` and
`convergents' [9; (1, 2), (3, 4), (5, 6)] 0 = 9`
-/
def convergents' {K : Type u_2} [division_ring K] (g : generalized_continued_fraction K) (n : ℕ) : K :=
  h g + convergents'_aux (s g) n

end generalized_continued_fraction


-- Now, some basic, general theorems

namespace generalized_continued_fraction


/-- Two gcfs `g` and `g'` are equal if and only if their components are equal. -/
protected theorem ext_iff {α : Type u_1} {g : generalized_continued_fraction α} {g' : generalized_continued_fraction α} : g = g' ↔ h g = h g' ∧ s g = s g' := sorry

protected theorem ext {α : Type u_1} {g : generalized_continued_fraction α} {g' : generalized_continued_fraction α} (hyp : h g = h g' ∧ s g = s g') : g = g' :=
  iff.elim_right generalized_continued_fraction.ext_iff hyp

