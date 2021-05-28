/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Simon Hudon
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.lazy_list.basic
import Mathlib.data.tree
import Mathlib.data.int.basic
import Mathlib.control.bifunctor
import Mathlib.tactic.linarith.default
import Mathlib.testing.slim_check.gen
import PostPort

universes u_1 u l v w u_2 u_3 

namespace Mathlib

/-!
# `sampleable` Class

This class permits the creation samples of a given type
controlling the size of those values using the `gen` monad`. It also
helps minimize examples by creating smaller versions of given values.

When testing a proposition like `∀ n : ℕ, prime n → n ≤ 100`,
`slim_check` requires that `ℕ` have an instance of `sampleable` and for
`prime n` to be decidable.  `slim_check` will then use the instance of
`sampleable` to generate small examples of ℕ and progressively increase
in size. For each example `n`, `prime n` is tested. If it is false,
the example will be rejected (not a test success nor a failure) and
`slim_check` will move on to other examples. If `prime n` is true, `n
≤ 100` will be tested. If it is false, `n` is a counter-example of `∀
n : ℕ, prime n → n ≤ 100` and the test fails. If `n ≤ 100` is true,
the test passes and `slim_check` moves on to trying more examples.

This is a port of the Haskell QuickCheck library.

## Main definitions
  * `sampleable` class
  * `sampleable_functor` and `sampleable_bifunctor` class
  * `sampleable_ext` class

### `sampleable`

`sampleable α` provides ways of creating examples of type `α`,
and given such an example `x : α`, gives us a way to shrink it
and find simpler examples.

### `sampleable_ext`

`sampleable_ext` generalizes the behavior of `sampleable`
and makes it possible to express instances for types that
do not lend themselves to introspection, such as `ℕ → ℕ`.
If we test a quantification over functions the
counter-examples cannot be shrunken or printed meaningfully.

For that purpose, `sampleable_ext` provides a proxy representation
`proxy_repr` that can be printed and shrunken as well
as interpreted (using `interp`) as an object of the right type.

### `sampleable_functor` and `sampleable_bifunctor`

`sampleable_functor F` and `sampleable_bifunctor F` makes it possible
to create samples of and shrink `F α` given a sampling function and a
shrinking function for arbitrary `α`.

This allows us to separate the logic for generating the shape of a
collection from the logic for generating its contents. Specifically,
the contents could be generated using either `sampleable` or
`sampleable_ext` instance and the `sampleable_(bi)functor` does not
need to use that information

## Shrinking

Shrinking happens when `slim_check` find a counter-example to a
property.  It is likely that the example will be more complicated than
necessary so `slim_check` proceeds to shrink it as much as
possible. Although equally valid, a smaller counter-example is easier
for a user to understand and use.

The `sampleable` class, beside having the `sample` function, has a
`shrink` function so that we can use specialized knowledge while
shrinking a value. It is not responsible for the whole shrinking process
however. It only has to take one step in the shrinking process.
`slim_check` will repeatedly call `shrink` until no more steps can
be taken. Because `shrink` guarantees that the size of the candidates
it produces is strictly smaller than the argument, we know that
`slim_check` is guaranteed to terminate.

## Tags

random testing

## References

  * https://hackage.haskell.org/package/QuickCheck

-/

namespace slim_check


/-- `sizeof_lt x y` compares the sizes of `x` and `y`. -/
def sizeof_lt {α : Sort u_1} [SizeOf α] (x : α) (y : α)  :=
  sizeof x < sizeof y

/-- `shrink_fn α` is the type of functions that shrink an
argument of type `α` -/
def shrink_fn (α : Type u_1) [SizeOf α]  :=
  (x : α) → lazy_list (Subtype fun (y : α) => sizeof_lt y x)

/-- `sampleable α` provides ways of creating examples of type `α`,
and given such an example `x : α`, gives us a way to shrink it
and find simpler examples.  -/
class sampleable (α : Type u) 
where
  wf : SizeOf α
  sample : gen α
  shrink : (x : α) → lazy_list (Subtype fun (y : α) => sizeof y < sizeof x)

/-- `sampleable_functor F` makes it possible to create samples of and
shrink `F α` given a sampling function and a shrinking function for
arbitrary `α` -/
class sampleable_functor (F : Type u → Type v) [Functor F] 
where
  wf : (α : Type u) → [_inst_1 : SizeOf α] → SizeOf (F α)
  sample : {α : Type u} → gen α → gen (F α)
  shrink : (α : Type u) → [_inst_1 : SizeOf α] → shrink_fn α → shrink_fn (F α)
  p_repr : (α : Type u) → has_repr α → has_repr (F α)

/-- `sampleable_bifunctor F` makes it possible to create samples of
and shrink `F α β` given a sampling function and a shrinking function
for arbitrary `α` and `β` -/
class sampleable_bifunctor (F : Type u → Type v → Type w) [bifunctor F] 
where
  wf : (α : Type u) → (β : Type v) → [_inst_1 : SizeOf α] → [_inst_2 : SizeOf β] → SizeOf (F α β)
  sample : {α : Type u} → {β : Type v} → gen α → gen β → gen (F α β)
  shrink : (α : Type u) →
  (β : Type v) → [_inst_1 : SizeOf α] → [_inst_2 : SizeOf β] → shrink_fn α → shrink_fn β → shrink_fn (F α β)
  p_repr : (α : Type u) → (β : Type v) → has_repr α → has_repr β → has_repr (F α β)

/-- This function helps infer the proxy representation and
interpretation in `sampleable_ext` instances. -/
/-- `sampleable_ext` generalizes the behavior of `sampleable`
and makes it possible to express instances for types that
do not lend themselves to introspection, such as `ℕ → ℕ`.
If we test a quantification over functions the
counter-examples cannot be shrunken or printed meaningfully.

For that purpose, `sampleable_ext` provides a proxy representation
`proxy_repr` that can be printed and shrunken as well
as interpreted (using `interp`) as an object of the right type. -/
class sampleable_ext (α : Sort u) 
where
  proxy_repr : Type v
  wf : SizeOf proxy_repr
  interp : autoParam (proxy_repr → α)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.slim_check.sampleable.mk_trivial_interp")
    (Lean.Name.mkStr
      (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "slim_check") "sampleable")
      "mk_trivial_interp")
    [])
  p_repr : has_repr proxy_repr
  sample : gen proxy_repr
  shrink : shrink_fn proxy_repr

protected instance sampleable_ext.of_sampleable {α : Type u_1} [sampleable α] [has_repr α] : sampleable_ext α :=
  sampleable_ext.mk α (sample α) shrink

protected instance sampleable.functor {α : Type u_1} {F : Type u_1 → Type u_2} [Functor F] [sampleable_functor F] [sampleable α] : sampleable (F α) :=
  sampleable.mk (sampleable_functor.sample F (sample α)) (sampleable_functor.shrink α shrink)

protected instance sampleable.bifunctor {α : Type u_1} {β : Type u_2} {F : Type u_1 → Type u_2 → Type u_3} [bifunctor F] [sampleable_bifunctor F] [sampleable α] [sampleable β] : sampleable (F α β) :=
  sampleable.mk (sampleable_bifunctor.sample F (sample α) (sample β)) (sampleable_bifunctor.shrink α β shrink shrink)

protected instance sampleable_ext.functor {α : Type u_1} {F : Type u_1 → Type u_2} [Functor F] [sampleable_functor F] [sampleable_ext α] : sampleable_ext (F α) :=
  sampleable_ext.mk (F (sampleable_ext.proxy_repr α)) (sampleable_functor.sample F (sampleable_ext.sample α))
    (sampleable_functor.shrink (sampleable_ext.proxy_repr α) sampleable_ext.shrink)

protected instance sampleable_ext.bifunctor {α : Type u_1} {β : Type u_2} {F : Type u_1 → Type u_2 → Type u_3} [bifunctor F] [sampleable_bifunctor F] [sampleable_ext α] [sampleable_ext β] : sampleable_ext (F α β) :=
  sampleable_ext.mk (F (sampleable_ext.proxy_repr α) (sampleable_ext.proxy_repr β))
    (sampleable_bifunctor.sample F (sampleable_ext.sample α) (sampleable_ext.sample β))
    (sampleable_bifunctor.shrink (sampleable_ext.proxy_repr α) (sampleable_ext.proxy_repr β) sampleable_ext.shrink
      sampleable_ext.shrink)

/-- `nat.shrink' k n` creates a list of smaller natural numbers by
successively dividing `n` by 2 and subtracting the difference from
`k`. For example, `nat.shrink 100 = [50, 75, 88, 94, 97, 99]`. -/
def nat.shrink' (k : ℕ) (n : ℕ) : n ≤ k → List (Subtype fun (m : ℕ) => has_well_founded.r m k) → List (Subtype fun (m : ℕ) => has_well_founded.r m k) :=
  sorry

/-- `nat.shrink n` creates a list of smaller natural numbers by
successively dividing by 2 and subtracting the difference from
`n`. For example, `nat.shrink 100 = [50, 75, 88, 94, 97, 99]`. -/
def nat.shrink (n : ℕ) : List (Subtype fun (m : ℕ) => has_well_founded.r m n) :=
  dite (n > 0)
    (fun (h : n > 0) =>
      (fun (this : ∀ (k : ℕ), 1 < k → n / k < n) =>
          { val := n / bit1 (bit1 (bit0 1)), property := sorry } ::
            { val := n / bit1 1, property := sorry } :: nat.shrink' n n sorry [])
        sorry)
    fun (h : ¬n > 0) => []

/--
Transport a `sampleable` instance from a type `α` to a type `β` using
functions between the two, going in both directions.

Function `g` is used to define the well-founded order that
`shrink` is expected to follow.
-/
def sampleable.lift (α : Type u) {β : Type u} [sampleable α] (f : α → β) (g : β → α) (h : ∀ (a : α), sizeof (g (f a)) ≤ sizeof a) : sampleable β :=
  sampleable.mk (f <$> sample α)
    fun (x : β) =>
      (fun (this : ∀ (a : α), sizeof a < sizeof (g x) → sizeof (g (f a)) < sizeof (g x)) =>
          subtype.map f this <$> shrink (g x))
        sorry

protected instance nat.sampleable : sampleable ℕ :=
  sampleable.mk
    (gen.sized
      fun (sz : ℕ) =>
        gen.freq
          [(1, coe <$> gen.choose_any (fin (Nat.succ (sz ^ bit1 1)))),
            (bit1 1, coe <$> gen.choose_any (fin (Nat.succ sz)))]
          sorry)
    fun (x : ℕ) => lazy_list.of_list (nat.shrink x)

/-- `iterate_shrink p x` takes a decidable predicate `p` and a
value `x` of some sampleable type and recursively shrinks `x`.
It first calls `shrink x` to get a list of candidate sample,
finds the first that satisfies `p` and recursively tries
to shrink that one. -/
def iterate_shrink {α : Type} [has_to_string α] [sampleable α] (p : α → Prop) [decidable_pred p] : α → Option α :=
  well_founded.fix sorry
    fun (x : α) (f_rec : (y : α) → has_well_founded.r y x → Option α) =>
      do 
        trace
            (string.empty ++ to_string x ++
              (string.str
                    (string.str (string.str string.empty (char.of_nat (bit0 (bit0 (bit0 (bit0 (bit0 1)))))))
                      (char.of_nat (bit0 (bit1 (bit0 (bit1 (bit1 1)))))))
                    (char.of_nat (bit0 (bit0 (bit0 (bit0 (bit0 1)))))) ++
                  to_string (lazy_list.to_list (shrink x)) ++
                string.empty))
            fun (_ : Unit) => pure Unit.unit 
        let y ← lazy_list.find (fun (a : Subtype fun (y : α) => sizeof y < sizeof x) => p ↑a) (shrink x)
        f_rec ↑y sorry <|> some (subtype.val y)

protected instance fin.sampleable {n : ℕ} [fact (0 < n)] : sampleable (fin n) :=
  sampleable.lift ℕ fin.of_nat' subtype.val sorry

protected instance fin.sampleable' {n : ℕ} : sampleable (fin (Nat.succ n)) :=
  sampleable.lift ℕ fin.of_nat subtype.val sorry

protected instance pnat.sampleable : sampleable ℕ+ :=
  sampleable.lift ℕ nat.succ_pnat pnat.nat_pred sorry

/-- Redefine `sizeof` for `int` to make it easier to use with `nat` -/
def int.has_sizeof : SizeOf ℤ :=
  { sizeOf := int.nat_abs }

protected instance int.sampleable : sampleable ℤ :=
  sampleable.mk
    (gen.sized
      fun (sz : ℕ) =>
        gen.freq
          [(1, subtype.val <$> gen.choose (-(↑sz ^ bit1 1 + 1)) (↑sz ^ bit1 1 + 1) sorry),
            (bit1 1, subtype.val <$> gen.choose (-(↑sz + 1)) (↑sz + 1) sorry)]
          sorry)
    fun (x : ℤ) =>
      lazy_list.of_list
        (list.bind (nat.shrink (int.nat_abs x))
          fun (_x : Subtype fun (m : ℕ) => has_well_founded.r m (int.nat_abs x)) => sorry)

protected instance bool.sampleable : sampleable Bool :=
  sampleable.mk
    (do 
      let x ← gen.choose_any Bool 
      return x)
    fun (b : Bool) =>
      dite (↥b) (fun (h : ↥b) => lazy_list.singleton { val := false, property := sorry }) fun (h : ¬↥b) => lazy_list.nil

/--
Provided two shrinking functions `prod.shrink` shrinks a pair `(x, y)` by
first shrinking `x` and pairing the results with `y` and then shrinking
`y` and pairing the results with `x`.

All pairs either contain `x` untouched or `y` untouched. We rely on
shrinking being repeated for `x` to get maximally shrunken and then
for `y` to get shrunken too.
-/
def prod.shrink {α : Type u_1} {β : Type u_2} [SizeOf α] [SizeOf β] (shr_a : shrink_fn α) (shr_b : shrink_fn β) : shrink_fn (α × β) :=
  sorry

protected instance prod.sampleable : sampleable_bifunctor Prod :=
  sampleable_bifunctor.mk
    (fun (α : Type u) (β : Type v) (sama : gen α) (samb : gen β) =>
      do 
        uliftable.up sama 
        sorry)
    prod.shrink prod.has_repr

protected instance sigma.sampleable {α : Type u_1} {β : Type u_2} [sampleable α] [sampleable β] : sampleable (sigma fun (_x : α) => β) :=
  sampleable.lift (α × β) (fun (_x : α × β) => sorry) (fun (_x : sigma fun (_x : α) => β) => sorry) sorry

/-- shrinking function for sum types -/
def sum.shrink {α : Type u_1} {β : Type u_2} [SizeOf α] [SizeOf β] (shrink_α : shrink_fn α) (shrink_β : shrink_fn β) : shrink_fn (α ⊕ β) :=
  sorry

protected instance sum.sampleable : sampleable_bifunctor sum :=
  sampleable_bifunctor.mk
    (fun (α : Type u) (β : Type v) (sam_α : gen α) (sam_β : gen β) =>
      uliftable.up_map sum.inl sam_α <|> uliftable.up_map sum.inr sam_β)
    (fun (α : Type u) (β : Type v) (Iα : SizeOf α) (Iβ : SizeOf β) (shr_α : shrink_fn α) (shr_β : shrink_fn β) =>
      sum.shrink shr_α shr_β)
    sum.has_repr

protected instance rat.sampleable : sampleable ℚ :=
  sampleable.lift (ℤ × ℕ+) (fun (x : ℤ × ℕ+) => prod.cases_on x rat.mk_pnat)
    (fun (r : ℚ) => (rat.num r, { val := rat.denom r, property := rat.pos r })) sorry

/-- `sampleable_char` can be specialized into customized `sampleable char` instances.

The resulting instance has `1 / length` chances of making an unrestricted choice of characters
and it otherwise chooses a character from `characters` with uniform probabilities.  -/
def sampleable_char (length : ℕ) (characters : string) : sampleable char :=
  sampleable.mk
    (do 
      let x ← gen.choose_nat 0 length sorry 
      ite (subtype.val x = 0)
          (do 
            let n ← sample ℕ 
            pure (char.of_nat n))
          (do 
            let i ← gen.choose_nat 0 (string.length characters - 1) sorry 
            pure (string.iterator.curr (string.iterator.nextn (string.mk_iterator characters) ↑i))))
    fun (_x : char) => lazy_list.nil

protected instance char.sampleable : sampleable char := sorry

theorem list.sizeof_drop_lt_sizeof_of_lt_length {α : Type u} [SizeOf α] {xs : List α} {k : ℕ} (hk : 0 < k) (hk' : k < list.length xs) : sizeof (list.drop k xs) < sizeof xs := sorry

theorem list.sizeof_cons_lt_right {α : Type u} [SizeOf α] (a : α) (b : α) {xs : List α} (h : sizeof a < sizeof b) : sizeof (a :: xs) < sizeof (b :: xs) := sorry

theorem list.sizeof_cons_lt_left {α : Type u} [SizeOf α] (x : α) {xs : List α} {xs' : List α} (h : sizeof xs < sizeof xs') : sizeof (x :: xs) < sizeof (x :: xs') := sorry

theorem list.sizeof_append_lt_left {α : Type u} [SizeOf α] {xs : List α} {ys : List α} {ys' : List α} (h : sizeof ys < sizeof ys') : sizeof (xs ++ ys) < sizeof (xs ++ ys') := sorry

theorem list.one_le_sizeof {α : Type u} [SizeOf α] (xs : List α) : 1 ≤ sizeof xs := sorry

/--
`list.shrink_removes` shrinks a list by removing chunks of size `k` in
the middle of the list.
-/
def list.shrink_removes {α : Type u} [SizeOf α] (k : ℕ) (hk : 0 < k) (xs : List α) (n : ℕ) : n = list.length xs → lazy_list (Subtype fun (ys : List α) => sizeof_lt ys xs) :=
  sorry

/--
`list.shrink_one xs` shrinks list `xs` by shrinking only one item in
the list.
-/
def list.shrink_one {α : Type u} [SizeOf α] (shr : (x : α) → lazy_list (Subtype fun (y : α) => sizeof_lt y x)) : shrink_fn (List α) :=
  sorry

/-- `list.shrink_with shrink_f xs` shrinks `xs` by first
considering `xs` with chunks removed in the middle (starting with
chunks of size `xs.length` and halving down to `1`) and then
shrinks only one element of the list.

This strategy is taken directly from Haskell's QuickCheck -/
def list.shrink_with {α : Type u} [SizeOf α] (shr : (x : α) → lazy_list (Subtype fun (y : α) => sizeof_lt y x)) (xs : List α) : lazy_list (Subtype fun (ys : List α) => sizeof_lt ys xs) :=
  let n : ℕ := list.length xs;
  lazy_list.append
    (lazy_list.bind (lazy_list.cons n fun (_ : Unit) => lazy_list.map subtype.val (lazy_list.reverse (shrink n)))
      fun (k : ℕ) =>
        dite (0 < k) (fun (hk : 0 < k) => list.shrink_removes k hk xs n rfl) fun (hk : ¬0 < k) => lazy_list.nil)
    fun (_ : Unit) => list.shrink_one shr xs

protected instance list.sampleable : sampleable_functor List :=
  sampleable_functor.mk (fun (α : Type u) (sam_α : gen α) => gen.list_of sam_α)
    (fun (α : Type u) (Iα : SizeOf α) (shr_α : shrink_fn α) => list.shrink_with shr_α) list.has_repr

protected instance prop.sampleable_ext : sampleable_ext Prop :=
  sampleable_ext.mk Bool (gen.choose_any Bool) fun (_x : Bool) => lazy_list.nil

/-- `no_shrink` is a type annotation to signal that
a certain type is not to be shrunk. It can be useful in
combination with other types: e.g. `xs : list (no_shrink ℤ)`
will result in the list being cut down but individual
integers being kept as is. -/
def no_shrink (α : Type u_1)  :=
  α

protected instance no_shrink.inhabited {α : Type u_1} [Inhabited α] : Inhabited (no_shrink α) :=
  { default := Inhabited.default }

/-- Introduction of the `no_shrink` type. -/
def no_shrink.mk {α : Type u_1} (x : α) : no_shrink α :=
  x

/-- Selector of the `no_shrink` type. -/
def no_shrink.get {α : Type u_1} (x : no_shrink α) : α :=
  x

protected instance no_shrink.sampleable {α : Type u_1} [sampleable α] : sampleable (no_shrink α) :=
  sampleable.mk (no_shrink.mk <$> sample α) fun (_x : no_shrink α) => lazy_list.nil

protected instance string.sampleable : sampleable string :=
  sampleable.mk
    (do 
      let x ← gen.list_of (sample char)
      pure (list.as_string x))
    shrink

/-- implementation of `sampleable (tree α)` -/
def tree.sample {α : Type u} (sample : gen α) : ℕ → gen (tree α) :=
  sorry

/-- `rec_shrink x f_rec` takes the recursive call `f_rec` introduced
by `well_founded.fix` and turns it into a shrinking function whose
result is adequate to use in a recursive call. -/
def rec_shrink {α : Type u_1} [SizeOf α] (t : α) (sh : (x : α) → sizeof_lt x t → lazy_list (Subtype fun (y : α) => sizeof_lt y x)) : shrink_fn (Subtype fun (t' : α) => sizeof_lt t' t) :=
  sorry

theorem tree.one_le_sizeof {α : Type u_1} [SizeOf α] (t : tree α) : 1 ≤ sizeof t := sorry

protected instance tree.functor : Functor tree :=
  { map := tree.map, mapConst := fun (α β : Type u_1) => tree.map ∘ function.const β }

/--
Recursion principle for shrinking tree-like structures.
-/
def rec_shrink_with {α : Type u} [SizeOf α] (shrink_a : (x : α) → shrink_fn (Subtype fun (y : α) => sizeof_lt y x) → List (lazy_list (Subtype fun (y : α) => sizeof_lt y x))) : shrink_fn α :=
  well_founded.fix (sizeof_measure_wf α)
    fun (t : α) (f_rec : (y : α) → sizeof_measure α y t → lazy_list (Subtype fun (y_1 : α) => sizeof_lt y_1 y)) =>
      lazy_list.join (lazy_list.of_list (shrink_a t fun (_x : Subtype fun (y : α) => sizeof_lt y t) => sorry))

theorem rec_shrink_with_eq {α : Type u} [SizeOf α] (shrink_a : (x : α) → shrink_fn (Subtype fun (y : α) => sizeof_lt y x) → List (lazy_list (Subtype fun (y : α) => sizeof_lt y x))) (x : α) : rec_shrink_with shrink_a x =
  lazy_list.join
    (lazy_list.of_list
      (shrink_a x
        fun (t' : Subtype fun (y : α) => sizeof_lt y x) =>
          rec_shrink x (fun (x_1 : α) (h' : sizeof_lt x_1 x) => rec_shrink_with shrink_a x_1) t')) := sorry

/-- `tree.shrink_with shrink_f t` shrinks `xs` by using the empty tree,
each subtrees, and by shrinking the subtree to recombine them.

This strategy is taken directly from Haskell's QuickCheck -/
def tree.shrink_with {α : Type u} [SizeOf α] (shrink_a : shrink_fn α) : shrink_fn (tree α) :=
  rec_shrink_with fun (t : tree α) => sorry

protected instance sampleable_tree : sampleable_functor tree :=
  sampleable_functor.mk (fun (α : Type u_1) (sam_α : gen α) => gen.sized (tree.sample sam_α))
    (fun (α : Type u_1) (Iα : SizeOf α) (shr_α : shrink_fn α) => tree.shrink_with shr_α) tree.has_repr

/-- Type tag that signals to `slim_check` to use small values for a given type. -/
def small (α : Type u_1)  :=
  α

/-- Add the `small` type tag -/
def small.mk {α : Type u_1} (x : α) : small α :=
  x

/-- Type tag that signals to `slim_check` to use large values for a given type. -/
def large (α : Type u_1)  :=
  α

/-- Add the `large` type tag -/
def large.mk {α : Type u_1} (x : α) : large α :=
  x

protected instance small.functor : Functor small :=
  applicative.to_functor

protected instance large.functor : Functor large :=
  applicative.to_functor

protected instance small.inhabited {α : Type u} [Inhabited α] : Inhabited (small α) :=
  { default := Inhabited.default }

protected instance large.inhabited {α : Type u} [Inhabited α] : Inhabited (large α) :=
  { default := Inhabited.default }

protected instance small.sampleable_functor : sampleable_functor small :=
  sampleable_functor.mk
    (fun (α : Type u_1) (samp : gen α) => gen.resize (fun (n : ℕ) => n / bit1 (bit0 1) + bit1 (bit0 1)) samp)
    (fun (α : Type u_1) (_x : SizeOf α) => id) fun (α : Type u_1) => id

protected instance large.sampleable_functor : sampleable_functor large :=
  sampleable_functor.mk (fun (α : Type u_1) (samp : gen α) => gen.resize (fun (n : ℕ) => n * bit1 (bit0 1)) samp)
    (fun (α : Type u_1) (_x : SizeOf α) => id) fun (α : Type u_1) => id

protected instance ulift.sampleable_functor : sampleable_functor ulift :=
  sampleable_functor.mk (fun (α : Type v) (samp : gen α) => uliftable.up_map ulift.up samp)
    (fun (α : Type v) (_x : SizeOf α) (shr : shrink_fn α) (_x : ulift α) => sorry)
    fun (α : Type v) (h : has_repr α) => has_repr.mk (repr ∘ ulift.down)

/-!
## Subtype instances

The following instances are meant to improve the testing of properties of the form
`∀ i j, i ≤ j, ...`

The naive way to test them is to choose two numbers `i` and `j` and check that
the proper ordering is satisfied. Instead, the following instances make it
so that `j` will be chosen with considerations to the required ordering
constraints. The benefit is that we will not have to discard any choice
of `j`.
 -/

/-! ### Subtypes of `ℕ` -/

protected instance nat_le.sampleable {y : ℕ} : sampleable (Subtype fun (x : ℕ) => x ≤ y) :=
  sampleable.mk
    (do 
      gen.choose_nat 0 y sorry 
      sorry)
    fun (_x : Subtype fun (x : ℕ) => x ≤ y) => sorry

protected instance nat_ge.sampleable {x : ℕ} : sampleable (Subtype fun (y : ℕ) => x ≤ y) :=
  sampleable.mk
    (do 
      sample ℕ 
      sorry)
    fun (_x : Subtype fun (y : ℕ) => x ≤ y) => sorry

/- there is no `nat_lt.sampleable` instance because if `y = 0`, there is no valid choice
to satisfy `x < y` -/

protected instance nat_gt.sampleable {x : ℕ} : sampleable (Subtype fun (y : ℕ) => x < y) :=
  sampleable.mk
    (do 
      sample ℕ 
      sorry)
    fun (x_1 : Subtype fun (y : ℕ) => x < y) => shrink x_1

/-! ### Subtypes of any `linear_ordered_add_comm_group` -/

protected instance le.sampleable {α : Type u} {y : α} [sampleable α] [linear_ordered_add_comm_group α] : sampleable (Subtype fun (x : α) => x ≤ y) :=
  sampleable.mk
    (do 
      let x ← sample α 
      pure { val := y - abs x, property := sorry })
    fun (_x : Subtype fun (x : α) => x ≤ y) => lazy_list.nil

protected instance ge.sampleable {α : Type u} {x : α} [sampleable α] [linear_ordered_add_comm_group α] : sampleable (Subtype fun (y : α) => x ≤ y) :=
  sampleable.mk
    (do 
      let y ← sample α 
      pure { val := x + abs y, property := sorry })
    fun (_x : Subtype fun (y : α) => x ≤ y) => lazy_list.nil

/-!
### Subtypes of `ℤ`

Specializations of `le.sampleable` and `ge.sampleable` for `ℤ` to help instance search.
-/

protected instance int_le.sampleable {y : ℤ} : sampleable (Subtype fun (x : ℤ) => x ≤ y) :=
  sampleable.lift ℕ (fun (n : ℕ) => { val := y - ↑n, property := sorry })
    (fun (_x : Subtype fun (x : ℤ) => x ≤ y) => sorry) sorry

protected instance int_ge.sampleable {x : ℤ} : sampleable (Subtype fun (y : ℤ) => x ≤ y) :=
  sampleable.lift ℕ (fun (n : ℕ) => { val := x + ↑n, property := sorry })
    (fun (_x : Subtype fun (y : ℤ) => x ≤ y) => sorry) sorry

protected instance int_lt.sampleable {y : ℤ} : sampleable (Subtype fun (x : ℤ) => x < y) :=
  sampleable.lift ℕ (fun (n : ℕ) => { val := y - (↑n + 1), property := sorry })
    (fun (_x : Subtype fun (x : ℤ) => x < y) => sorry) sorry

protected instance int_gt.sampleable {x : ℤ} : sampleable (Subtype fun (y : ℤ) => x < y) :=
  sampleable.lift ℕ (fun (n : ℕ) => { val := x + (↑n + 1), property := sorry })
    (fun (_x : Subtype fun (y : ℤ) => x < y) => sorry) sorry

/-! ### Subtypes of any `list` -/

protected instance perm.slim_check {α : Type u} {xs : List α} : sampleable (Subtype fun (ys : List α) => xs ~ ys) :=
  sampleable.mk (gen.permutation_of xs) fun (_x : Subtype fun (ys : List α) => xs ~ ys) => lazy_list.nil

protected instance perm'.slim_check {α : Type u} {xs : List α} : sampleable (Subtype fun (ys : List α) => ys ~ xs) :=
  sampleable.mk (subtype.map id list.perm.symm <$> gen.permutation_of xs)
    fun (_x : Subtype fun (ys : List α) => ys ~ xs) => lazy_list.nil

/--
Print (at most) 10 samples of a given type to stdout for debugging.
-/
def print_samples {t : Type u} [has_repr t] (g : gen t) : io Unit :=
  do 
    let xs ←
      io.run_rand
        (uliftable.down
          (do 
            let xs ← mmap (reader_t.run g ∘ ulift.up) (list.range (bit0 (bit1 (bit0 1))))
            pure (ulift.up (list.map repr xs))))
    mmap' io.put_str_ln xs

