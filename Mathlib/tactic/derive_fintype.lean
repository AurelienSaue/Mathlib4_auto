/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.logic.basic
import Mathlib.data.fintype.basic
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Derive handler for `fintype` instances

This file introduces a derive handler to automatically generate `fintype`
instances for structures and inductives.

## Implementation notes

To construct a fintype instance, we need 3 things:

  1. A list `l` of elements
  2. A proof that `l` has no duplicates
  3. A proof that every element in the type is in `l`

Now fintype is defined as a finset which enumerates all elements, so steps (1) and (2) are
bundled together. It is possible to use finset operations that remove duplicates to avoid the need
to prove (2), but this adds unnecessary functions to the constructed term, which makes it more
expensive to compute the list, and it also adds a dependence on decidable equality for the type,
which we want to avoid.

Because we will rely on fintype instances for constructor arguments, we can't actually build a list
directly, so (1) and (2) are necessarily somewhat intertwined. The inductive types we will be
proving instances for look something like this:

```
@[derive fintype]
inductive foo
| zero : foo
| one : bool → foo
| two : ∀ x : fin 3, bar x → foo
```

The list of elements that we generate is
```
{foo.zero}
∪ (finset.univ : bool).map (λ b, finset.one b)
∪ (finset.univ : Σ' x : fin 3, bar x).map (λ ⟨x, y⟩, finset.two x y)
```
except that instead of `∪`, that is `finset.union`, we use `finset.disj_union` which doesn't
require any deduplication, but does require a proof that the two parts of the union are disjoint.
We use `finset.cons` to append singletons like `foo.zero`.

The proofs of disjointness would be somewhat expensive since there are quadratically many of them,
so instead we use a "discriminant" function. Essentially, we define
```
def foo.enum : foo → ℕ
| foo.zero := 0
| (foo.one _) := 1
| (foo.two _ _) := 2
```
and now the existence of this function implies that foo.zero is not foo.two and so on because they
map to different natural numbers. We can prove that sets of natural numbers are mutually disjoint
more easily because they have a linear order: `0 < 1 < 2` so `0 ≠ 2`.

To package this argument up, we define `finset_above foo foo.enum n` to be a finset `s` together
with a proof that all elements `a ∈ s` have `n ≤ enum a`. Now we only have to prove that
`enum foo.zero = 0`, `enum (foo.one _) = 1`, etc. (linearly many proofs, all `rfl`) in order to
prove that all variants are mutually distinct.

We mirror the `finset.cons` and `finset.disj_union` functions into `finset_above.cons` and
`finset_above.union`, and this forms the main part of the finset construction.

This only handles distinguishing variants of a finset. Now we must enumerate the elements of a
variant, for example `{foo.one ff, foo.one tt}`, while at the same time proving that all these
elements have discriminant `1` in this case. To do that, we use the `finset_in` type, which
is a finset satisfying a property `P`, here `λ a, foo.enum a = 1`.

We could use `finset.bind` many times to construct the finset but it turns out to be somewhat
complicated to get good side goals for a naturally nodup version of `finset.bind` in the same way
as we did with `finset.cons` and `finset.union`. Instead, we tuple up all arguments into one type,
leveraging the `fintype` instance on `psigma`, and then define a map from this type to the
inductive type that untuples them and applies the constructor. The injectivity property of the
constructor ensures that this function is injective, so we can use `finset.map` to apply it. This
is the content of the constructor `finset_in.mk`.

That completes the proofs of (1) and (2). To prove (3), we perform one case analysis over the
inductive type, proving theorems like
```
foo.one a ∈ {foo.zero}
  ∪ (finset.univ : bool).map (λ b, finset.one b)
  ∪ (finset.univ : Σ' x : fin 3, bar x).map (λ ⟨x, y⟩, finset.two x y)
```
by seeking to the relevant disjunct and then supplying the constructor arguments. This part of the
proof is quadratic, but quite simple. (We could do it in `O(n log n)` if we used a balanced tree
for the unions.)

The tactics perform the following parts of this proof scheme:
* `mk_sigma` constructs the type `Γ` in `finset_in.mk`
* `mk_sigma_elim` constructs the function `f` in `finset_in.mk`
* `mk_sigma_elim_inj` proves that `f` is injective
* `mk_sigma_elim_eq` proves that `∀ a, enum (f a) = k`
* `mk_finset` constructs the finset `S = {foo.zero} ∪ ...` by recursion on the variants
* `mk_finset_total` constructs the proof `|- foo.zero ∈ S; |- foo.one a ∈ S; |- foo.two a b ∈ S`
  by recursion on the subgoals coming out of the initial `cases`
* `mk_fintype_instance` puts it all together to produce a proof of `fintype foo`.
  The construction of `foo.enum` is also done in this function.

-/

namespace derive_fintype


/-- A step in the construction of `finset.univ` for a finite inductive type.
We will set `enum` to the discriminant of the inductive type, so a `finset_above`
represents a finset that enumerates all elements in a tail of the constructor list. -/
def finset_above (α : Type u_1) (enum : α → ℕ) (n : ℕ) :=
  Subtype fun (s : finset α) => ∀ (x : α), x ∈ s → n ≤ enum x

/-- Construct a fintype instance from a completed `finset_above`. -/
def mk_fintype {α : Type u_1} (enum : α → ℕ) (s : finset_above α enum 0) (H : ∀ (x : α), x ∈ subtype.val s) : fintype α :=
  fintype.mk (subtype.val s) H

/-- This is the case for a simple variant (no arguments) in an inductive type. -/
def finset_above.cons {α : Type u_1} {enum : α → ℕ} (n : ℕ) (a : α) (h : enum a = n) (s : finset_above α enum (n + 1)) : finset_above α enum n :=
  { val := finset.cons a (subtype.val s) sorry, property := sorry }

theorem finset_above.mem_cons_self {α : Type u_1} {enum : α → ℕ} {n : ℕ} {a : α} {h : enum a = n} {s : finset_above α enum (n + 1)} : a ∈ subtype.val (finset_above.cons n a h s) :=
  multiset.mem_cons_self a (finset.val (subtype.val s))

theorem finset_above.mem_cons_of_mem {α : Type u_1} {enum : α → ℕ} {n : ℕ} {a : α} {h : enum a = n} {s : finset_above α enum (n + 1)} {b : α} : b ∈ subtype.val s → b ∈ subtype.val (finset_above.cons n a h s) :=
  multiset.mem_cons_of_mem

/-- The base case is when we run out of variants; we just put an empty finset at the end. -/
def finset_above.nil {α : Type u_1} {enum : α → ℕ} (n : ℕ) : finset_above α enum n :=
  { val := ∅, property := sorry }

protected instance finset_above.inhabited (α : Type u_1) (enum : α → ℕ) (n : ℕ) : Inhabited (finset_above α enum n) :=
  { default := finset_above.nil n }

/-- This is a finset covering a nontrivial variant (with one or more constructor arguments).
The property `P` here is `λ a, enum a = n` where `n` is the discriminant for the current
variant. -/
def finset_in {α : Type u_1} (P : α → Prop) :=
  Subtype fun (s : finset α) => ∀ (x : α), x ∈ s → P x

/-- To construct the finset, we use an injective map from the type `Γ`, which will be the
sigma over all constructor arguments. We use sigma instances and existing fintype instances
to prove that `Γ` is a fintype, and construct the function `f` that maps `⟨a, b, c, ...⟩`
to `C_n a b c ...` where `C_n` is the nth constructor, and `mem` asserts
`enum (C_n a b c ...) = n`. -/
def finset_in.mk {α : Type u_1} {P : α → Prop} (Γ : Type u_2) [fintype Γ] (f : Γ → α) (inj : function.injective f) (mem : ∀ (x : Γ), P (f x)) : finset_in P :=
  { val := finset.map (function.embedding.mk f inj) finset.univ, property := sorry }

theorem finset_in.mem_mk {α : Type u_1} {P : α → Prop} {Γ : Type u_2} {s : fintype Γ} {f : Γ → α} {inj : function.injective f} {mem : ∀ (x : Γ), P (f x)} {a : α} (b : Γ) (H : f b = a) : a ∈ subtype.val (finset_in.mk Γ f inj mem) :=
  iff.mpr finset.mem_map (Exists.intro b (Exists.intro (finset.mem_univ b) H))

/-- For nontrivial variants, we split the constructor list into a `finset_in` component for the
current constructor and a `finset_above` for the rest. -/
def finset_above.union {α : Type u_1} {enum : α → ℕ} (n : ℕ) (s : finset_in fun (a : α) => enum a = n) (t : finset_above α enum (n + 1)) : finset_above α enum n :=
  { val := finset.disj_union (subtype.val s) (subtype.val t) sorry, property := sorry }

theorem finset_above.mem_union_left {α : Type u_1} {enum : α → ℕ} {n : ℕ} {s : finset_in fun (a : α) => enum a = n} {t : finset_above α enum (n + 1)} {a : α} (H : a ∈ subtype.val s) : a ∈ subtype.val (finset_above.union n s t) :=
  iff.mpr multiset.mem_add (Or.inl H)

theorem finset_above.mem_union_right {α : Type u_1} {enum : α → ℕ} {n : ℕ} {s : finset_in fun (a : α) => enum a = n} {t : finset_above α enum (n + 1)} {a : α} (H : a ∈ subtype.val t) : a ∈ subtype.val (finset_above.union n s t) :=
  iff.mpr multiset.mem_add (Or.inr H)

