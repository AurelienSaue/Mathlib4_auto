/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.computability.halting
import Mathlib.computability.turing_machine
import Mathlib.data.num.lemmas
import Mathlib.PostPort

universes l u_1 

namespace Mathlib

/-!
# Modelling partial recursive functions using Turing machines

This file defines a simplified basis for partial recursive functions, and a `turing.TM2` model
Turing machine for evaluating these functions. This amounts to a constructive proof that every
`partrec` function can be evaluated by a Turing machine.

## Main definitions

* `to_partrec.code`: a simplified basis for partial recursive functions, valued in
  `list ℕ →. list ℕ`.
  * `to_partrec.code.eval`: semantics for a `to_partrec.code` program
* `partrec_to_TM2.tr`: A TM2 turing machine which can evaluate `code` programs
-/

namespace turing


/-!
## A simplified basis for partrec

This section constructs the type `code`, which is a data type of programs with `list ℕ` input and
output, with enough expressivity to write any partial recursive function. The primitives are:

* `zero'` appends a `0` to the input. That is, `zero' v = 0 :: v`.
* `succ` returns the successor of the head of the input, defaulting to zero if there is no head:
  * `succ [] = [1]`
  * `succ (n :: v) = [n + 1]`
* `tail` returns the tail of the input
  * `tail [] = []`
  * `tail (n :: v) = v`
* `cons f fs` calls `f` and `fs` on the input and conses the results:
  * `cons f fs v = (f v).head :: fs v`
* `comp f g` calls `f` on the output of `g`:
  * `comp f g v = f (g v)`
* `case f g` cases on the head of the input, calling `f` or `g` depending on whether it is zero or
  a successor (similar to `nat.cases_on`).
  * `case f g [] = f []`
  * `case f g (0 :: v) = f v`
  * `case f g (n+1 :: v) = g (n :: v)`
* `fix f` calls `f` repeatedly, using the head of the result of `f` to decide whether to call `f`
  again or finish:
  * `fix f v = []` if `f v = []`
  * `fix f v = w` if `f v = 0 :: w`
  * `fix f v = fix f w` if `f v = n+1 :: w` (the exact value of `n` is discarded)

This basis is convenient because it is closer to the Turing machine model - the key operations are
splitting and merging of lists of unknown length, while the messy `n`-ary composition operation
from the traditional basis for partial recursive functions is absent - but it retains a
compositional semantics. The first step in transitioning to Turing machines is to make a sequential
evaluator for this basis, which we take up in the next section.
-/

namespace to_partrec


/-- The type of codes for primitive recursive functions. Unlike `nat.partrec.code`, this uses a set
of operations on `list ℕ`. See `code.eval` for a description of the behavior of the primitives. -/
inductive code where
| zero' : code
| succ : code
| tail : code
| cons : code → code → code
| comp : code → code → code
| case : code → code → code
| fix : code → code

/-- The semantics of the `code` primitives, as partial functions `list ℕ →. list ℕ`. By convention
we functions that return a single result return a singleton `[n]`, or in some cases `n :: v` where
`v` will be ignored by a subsequent function.

* `zero'` appends a `0` to the input. That is, `zero' v = 0 :: v`.
* `succ` returns the successor of the head of the input, defaulting to zero if there is no head:
  * `succ [] = [1]`
  * `succ (n :: v) = [n + 1]`
* `tail` returns the tail of the input
  * `tail [] = []`
  * `tail (n :: v) = v`
* `cons f fs` calls `f` and `fs` on the input and conses the results:
  * `cons f fs v = (f v).head :: fs v`
* `comp f g` calls `f` on the output of `g`:
  * `comp f g v = f (g v)`
* `case f g` cases on the head of the input, calling `f` or `g` depending on whether it is zero or
  a successor (similar to `nat.cases_on`).
  * `case f g [] = f []`
  * `case f g (0 :: v) = f v`
  * `case f g (n+1 :: v) = g (n :: v)`
* `fix f` calls `f` repeatedly, using the head of the result of `f` to decide whether to call `f`
  again or finish:
  * `fix f v = []` if `f v = []`
  * `fix f v = w` if `f v = 0 :: w`
  * `fix f v = fix f w` if `f v = n+1 :: w` (the exact value of `n` is discarded)
-/
@[simp] def code.eval : code → List ℕ →. List ℕ := sorry

namespace code


/-- `nil` is the constant nil function: `nil v = []`. -/
def nil : code := comp tail succ

@[simp] theorem nil_eval (v : List ℕ) : eval nil v = pure [] := sorry

/-- `id` is the identity function: `id v = v`. -/
def id : code := comp tail zero'

@[simp] theorem id_eval (v : List ℕ) : eval id v = pure v := sorry

/-- `head` gets the head of the input list: `head [] = [0]`, `head (n :: v) = [n]`. -/
def head : code := cons id nil

@[simp] theorem head_eval (v : List ℕ) : eval head v = pure [list.head v] := sorry

/-- `zero` is the constant zero function: `zero v = [0]`. -/
def zero : code := cons zero' nil

@[simp] theorem zero_eval (v : List ℕ) : eval zero v = pure [0] := sorry

/-- `pred` returns the predecessor of the head of the input:
`pred [] = [0]`, `pred (0 :: v) = [0]`, `pred (n+1 :: v) = [n]`. -/
def pred : code := case zero head

@[simp] theorem pred_eval (v : List ℕ) : eval pred v = pure [Nat.pred (list.head v)] := sorry

/-- `rfind f` performs the function of the `rfind` primitive of partial recursive functions.
`rfind f v` returns the smallest `n` such that `(f (n :: v)).head = 0`.

It is implemented as:

    rfind f v = pred (fix (λ (n::v), f (n::v) :: n+1 :: v) (0 :: v))

The idea is that the initial state is `0 :: v`, and the `fix` keeps `n :: v` as its internal state;
it calls `f (n :: v)` as the exit test and `n+1 :: v` as the next state. At the end we get
`n+1 :: v` where `n` is the desired output, and `pred (n+1 :: v) = [n]` returns the result.
 -/
def rfind (f : code) : code := comp pred (comp (fix (cons f (cons succ tail))) zero')

/-- `prec f g` implements the `prec` (primitive recursion) operation of partial recursive
functions. `prec f g` evaluates as:

* `prec f g [] = [f []]`
* `prec f g (0 :: v) = [f v]`
* `prec f g (n+1 :: v) = [g (n :: prec f g (n :: v) :: v)]`

It is implemented as:

    G (a :: b :: IH :: v) = (b :: a+1 :: b-1 :: g (a :: IH :: v) :: v)
    F (0 :: f_v :: v) = (f_v :: v)
    F (n+1 :: f_v :: v) = (fix G (0 :: n :: f_v :: v)).tail.tail
    prec f g (a :: v) = [(F (a :: f v :: v)).head]

Because `fix` always evaluates its body at least once, we must special case the `0` case to avoid
calling `g` more times than necessary (which could be bad if `g` diverges). If the input is
`0 :: v`, then `F (0 :: f v :: v) = (f v :: v)` so we return `[f v]`. If the input is `n+1 :: v`,
we evaluate the function from the bottom up, with initial state `0 :: n :: f v :: v`. The first
number counts up, providing arguments for the applications to `g`, while the second number counts
down, providing the exit condition (this is the initial `b` in the return value of `G`, which is
stripped by `fix`). After the `fix` is complete, the final state is `n :: 0 :: res :: v` where
`res` is the desired result, and the rest reduces this to `[res]`. -/
def prec (f : code) (g : code) : code :=
  let G : code :=
    cons tail
      (cons succ
        (cons (comp pred tail)
          (cons (comp g (cons id (comp tail tail))) (comp tail (comp tail tail)))));
  let F : code := case id (comp (comp (comp tail tail) (fix G)) zero');
  cons (comp F (cons head (cons (comp f tail) tail))) nil

theorem exists_code.comp {m : ℕ} {n : ℕ} {f : vector ℕ n →. ℕ} {g : fin n → vector ℕ m →. ℕ}
    (hf : ∃ (c : code), ∀ (v : vector ℕ n), eval c (subtype.val v) = pure <$> f v)
    (hg :
      ∀ (i : fin n), ∃ (c : code), ∀ (v : vector ℕ m), eval c (subtype.val v) = pure <$> g i v) :
    ∃ (c : code),
        ∀ (v : vector ℕ m),
          eval c (subtype.val v) = pure <$> ((vector.m_of_fn fun (i : fin n) => g i v) >>= f) :=
  sorry

theorem exists_code {n : ℕ} {f : vector ℕ n →. ℕ} (hf : nat.partrec' f) :
    ∃ (c : code), ∀ (v : vector ℕ n), eval c (subtype.val v) = pure <$> f v :=
  sorry

end code


/-!
## From compositional semantics to sequential semantics

Our initial sequential model is designed to be as similar as possible to the compositional
semantics in terms of its primitives, but it is a sequential semantics, meaning that rather than
defining an `eval c : list ℕ →. list ℕ` function for each program, defined by recursion on
programs, we have a type `cfg` with a step function `step : cfg → option cfg` that provides a
deterministic evaluation order. In order to do this, we introduce the notion of a *continuation*,
which can be viewed as a `code` with a hole in it where evaluation is currently taking place.
Continuations can be assigned a `list ℕ →. list ℕ` semantics as well, with the interpretation
being that given a `list ℕ` result returned from the code in the hole, the remainder of the
program will evaluate to a `list ℕ` final value.

The continuations are:

* `halt`: the empty continuation: the hole is the whole program, whatever is returned is the
  final result. In our notation this is just `_`.
* `cons₁ fs v k`: evaluating the first part of a `cons`, that is `k (_ :: fs v)`, where `k` is the
  outer continuation.
* `cons₂ ns k`: evaluating the second part of a `cons`: `k (ns.head :: _)`. (Technically we don't
  need to hold on to all of `ns` here since we are already committed to taking the head, but this
  is more regular.)
* `comp f k`: evaluating the first part of a composition: `k (f _)`.
* `fix f k`: waiting for the result of `f` in a `fix f` expression:
  `k (if _.head = 0 then _.tail else fix f (_.tail))`

The type `cfg` of evaluation states is:

* `ret k v`: we have received a result, and are now evaluating the continuation `k` with result
  `v`; that is, `k v` where `k` is ready to evaluate.
* `halt v`: we are done and the result is `v`.

The main theorem of this section is that for each code `c`, the state `step_normal c halt v` steps
to `v'` in finitely many steps if and only if `code.eval c v = some v'`.
-/

/-- The type of continuations, built up during evaluation of a `code` expression. -/
inductive cont where
| halt : cont
| cons₁ : code → List ℕ → cont → cont
| cons₂ : List ℕ → cont → cont
| comp : code → cont → cont
| fix : code → cont → cont

/-- The semantics of a continuation. -/
def cont.eval : cont → List ℕ →. List ℕ := sorry

/-- The semantics of a continuation. -/
inductive cfg where
| halt : List ℕ → cfg
| ret : cont → List ℕ → cfg

/-- Evaluating `c : code` in a continuation `k : cont` and input `v : list ℕ`. This goes by
recursion on `c`, building an augmented continuation and a value to pass to it.

* `zero' v = 0 :: v` evaluates immediately, so we return it to the parent continuation
* `succ v = [v.head.succ]` evaluates immediately, so we return it to the parent continuation
* `tail v = v.tail` evaluates immediately, so we return it to the parent continuation
* `cons f fs v = (f v).head :: fs v` requires two sub-evaluations, so we evaluate
  `f v` in the continuation `k (_.head :: fs v)` (called `cont.cons₁ fs v k`)
* `comp f g v = f (g v)` requires two sub-evaluations, so we evaluate
  `g v` in the continuation `k (f _)` (called `cont.comp f k`)
* `case f g v = v.head.cases_on (f v.tail) (λ n, g (n :: v.tail))` has the information needed to
  evaluate the case statement, so we do that and transition to either `f v` or `g (n :: v.tail)`.
* `fix f v = let v' := f v in if v'.head = 0 then k v'.tail else fix f v'.tail`
  needs to first evaluate `f v`, so we do that and leave the rest for the continuation (called
  `cont.fix f k`)
-/
def step_normal : code → cont → List ℕ → cfg := sorry

/-- Evaluating a continuation `k : cont` on input `v : list ℕ`. This is the second part of
evaluation, when we receive results from continuations built by `step_normal`.

* `cont.halt v = v`, so we are done and transition to the `cfg.halt v` state
* `cont.cons₁ fs as k v = k (v.head :: fs as)`, so we evaluate `fs as` now with the continuation
  `k (v.head :: _)` (called `cons₂ v k`).
* `cont.cons₂ ns k v = k (ns.head :: v)`, where we now have everything we need to evaluate
  `ns.head :: v`, so we return it to `k`.
* `cont.comp f k v = k (f v)`, so we call `f v` with `k` as the continuation.
* `cont.fix f k v = k (if v.head = 0 then k v.tail else fix f v.tail)`, where `v` is a value,
  so we evaluate the if statement and either call `k` with `v.tail`, or call `fix f v` with `k` as
  the continuation (which immediately calls `f` with `cont.fix f k` as the continuation).
-/
def step_ret : cont → List ℕ → cfg := sorry

/-- If we are not done (in `cfg.halt` state), then we must be still stuck on a continuation, so
this main loop calls `step_ret` with the new continuation. The overall `step` function transitions
from one `cfg` to another, only halting at the `cfg.halt` state. -/
def step : cfg → Option cfg := sorry

/-- In order to extract a compositional semantics from the sequential execution behavior of
configurations, we observe that continuations have a monoid structure, with `cont.halt` as the unit
and `cont.then` as the multiplication. `cont.then k₁ k₂` runs `k₁` until it halts, and then takes
the result of `k₁` and passes it to `k₂`.

We will not prove it is associative (although it is), but we are instead interested in the
associativity law `k₂ (eval c k₁) = eval c (k₁.then k₂)`. This holds at both the sequential and
compositional levels, and allows us to express running a machine without the ambient continuation
and relate it to the original machine's evaluation steps. In the literature this is usually
where one uses Turing machines embedded inside other Turing machines, but this approach allows us
to avoid changing the ambient type `cfg` in the middle of the recursion.
-/
def cont.then : cont → cont → cont := sorry

theorem cont.then_eval {k : cont} {k' : cont} {v : List ℕ} :
    cont.eval (cont.then k k') v = cont.eval k v >>= cont.eval k' :=
  sorry

/-- The `then k` function is a "configuration homomorphism". Its operation on states is to append
`k` to the continuation of a `cfg.ret` state, and to run `k` on `v` if we are in the `cfg.halt v`
state. -/
def cfg.then : cfg → cont → cfg := sorry

/-- The `step_normal` function respects the `then k'` homomorphism. Note that this is an exact
equality, not a simulation; the original and embedded machines move in lock-step until the
embedded machine reaches the halt state. -/
theorem step_normal_then (c : code) (k : cont) (k' : cont) (v : List ℕ) :
    step_normal c (cont.then k k') v = cfg.then (step_normal c k v) k' :=
  sorry

/-- The `step_ret` function respects the `then k'` homomorphism. Note that this is an exact
equality, not a simulation; the original and embedded machines move in lock-step until the
embedded machine reaches the halt state. -/
theorem step_ret_then {k : cont} {k' : cont} {v : List ℕ} :
    step_ret (cont.then k k') v = cfg.then (step_ret k v) k' :=
  sorry

/-- This is a temporary definition, because we will prove in `code_is_ok` that it always holds.
It asserts that `c` is semantically correct; that is, for any `k` and `v`,
`eval (step_normal c k v) = eval (cfg.ret k (code.eval c v))`, as an equality of partial values
(so one diverges iff the other does).

In particular, we can let `k = cont.halt`, and then this asserts that `step_normal c cont.halt v`
evaluates to `cfg.halt (code.eval c v)`. -/
def code.ok (c : code) :=
  ∀ (k : cont) (v : List ℕ),
    eval step (step_normal c k v) =
      do 
        let v ← code.eval c v 
        eval step (cfg.ret k v)

theorem code.ok.zero {c : code} (h : code.ok c) {v : List ℕ} :
    eval step (step_normal c cont.halt v) = cfg.halt <$> code.eval c v :=
  sorry

theorem step_normal.is_ret (c : code) (k : cont) (v : List ℕ) :
    ∃ (k' : cont), ∃ (v' : List ℕ), step_normal c k v = cfg.ret k' v' :=
  sorry

theorem cont_eval_fix {f : code} {k : cont} {v : List ℕ} (fok : code.ok f) :
    eval step (step_normal f (cont.fix f k) v) =
        do 
          let v ← code.eval (code.fix f) v 
          eval step (cfg.ret k v) :=
  sorry

theorem code_is_ok (c : code) : code.ok c := sorry

theorem step_normal_eval (c : code) (v : List ℕ) :
    eval step (step_normal c cont.halt v) = cfg.halt <$> code.eval c v :=
  code.ok.zero (code_is_ok c)

theorem step_ret_eval {k : cont} {v : List ℕ} :
    eval step (step_ret k v) = cfg.halt <$> cont.eval k v :=
  sorry

end to_partrec


/-!
## Simulating sequentialized partial recursive functions in TM2

At this point we have a sequential model of partial recursive functions: the `cfg` type and
`step : cfg → option cfg` function from the previous section. The key feature of this model is that
it does a finite amount of computation (in fact, an amount which is statically bounded by the size
of the program) between each step, and no individual step can diverge (unlike the compositional
semantics, where every sub-part of the computation is potentially divergent). So we can utilize the
same techniques as in the other TM simulations in `computability.turing_machine` to prove that
each step corresponds to a finite number of steps in a lower level model. (We don't prove it here,
but in anticipation of the complexity class P, the simulation is actually polynomial-time as well.)

The target model is `turing.TM2`, which has a fixed finite set of stacks, a bit of local storage,
with programs selected from a potentially infinite (but finitely accessible) set of program
positions, or labels `Λ`, each of which executes a finite sequence of basic stack commands.

For this program we will need four stacks, each on an alphabet `Γ'` like so:

    inductive Γ'  | Cons | cons | bit0 | bit1

We represent a number as a bit sequence, lists of numbers by putting `cons` after each element, and
lists of lists of natural numbers by putting `Cons` after each list. For example:

    0 ~> []
    1 ~> [bit1]
    6 ~> [bit0, bit1, bit1]
    [1, 2] ~> [bit1, cons, bit0, bit1, cons]
    [[], [1, 2]] ~> [Cons, bit1, cons, bit0, bit1, cons, Cons]

The four stacks are `main`, `rev`, `aux`, `stack`. In normal mode, `main` contains the input to the
current program (a `list ℕ`) and `stack` contains data (a `list (list ℕ)`) associated to the
current continuation, and in `ret` mode `main` contains the value that is being passed to the
continuation and `stack` contains the data for the continuation. The `rev` and `aux` stacks are
usually empty; `rev` is used to store reversed data when e.g. moving a value from one stack to
another, while `aux` is used as a temporary for a `main`/`stack` swap that happens during `cons₁`
evaluation.

The only local store we need is `option Γ'`, which stores the result of the last pop
operation. (Most of our working data are natural numbers, which are too large to fit in the local
store.)

The continuations from the previous section are data-carrying, containing all the values that have
been computed and are awaiting other arguments. In order to have only a finite number of
continuations appear in the program so that they can be used in machine states, we separate the
data part (anything with type `list ℕ`) from the `cont` type, producing a `cont'` type that lacks
this information. The data is kept on the `stack` stack.

Because we want to have subroutines for e.g. moving an entire stack to another place, we use an
infinite inductive type `Λ'` so that we can execute a program and then return to do something else
without having to define too many different kinds of intermediate states. (We must nevertheless
prove that only finitely many labels are accessible.) The labels are:

* `move p k₁ k₂ q`: move elements from stack `k₁` to `k₂` while `p` holds of the value being moved.
  The last element, that fails `p`, is placed in neither stack but left in the local store.
  At the end of the operation, `k₂` will have the elements of `k₁` in reverse order. Then do `q`.
* `clear p k q`: delete elements from stack `k` until `p` is true. Like `move`, the last element is
  left in the local storage. Then do `q`.
* `copy q`: Move all elements from `rev` to both `main` and `stack` (in reverse order),
  then do `q`. That is, it takes `(a, b, c, d)` to `(b.reverse ++ a, [], c, b.reverse ++ d)`.
* `push k f q`: push `f s`, where `s` is the local store, to stack `k`, then do `q`. This is a
  duplicate of the `push` instruction that is part of the TM2 model, but by having a subroutine
  just for this purpose we can build up programs to execute inside a `goto` statement, where we
  have the flexibility to be general recursive.
* `read (f : option Γ' → Λ')`: go to state `f s` where `s` is the local store. Again this is only
  here for convenience.
* `succ q`: perform a successor operation. Assuming `[n]` is encoded on `main` before,
  `[n+1]` will be on main after. This implements successor for binary natural numbers.
* `pred q₁ q₂`: perform a predecessor operation or `case` statement. If `[]` is encoded on
  `main` before, then we transition to `q₁` with `[]` on main; if `(0 :: v)` is on `main` before
  then `v` will be on `main` after and we transition to `q₁`; and if `(n+1 :: v)` is on `main`
  before then `n :: v` will be on `main` after and we transition to `q₂`.
* `ret k`: call continuation `k`. Each continuation has its own interpretation of the data in
  `stack` and sets up the data for the next continuation.
  * `ret (cons₁ fs k)`: `v :: k_data` on `stack` and `ns` on `main`, and the next step expects
    `v` on `main` and `ns :: k_data` on `stack`. So we have to do a little dance here with six
    reverse-moves using the `aux` stack to perform a three-point swap, each of which involves two
    reversals.
  * `ret (cons₂ k)`: `ns :: k_data` is on `stack` and `v` is on `main`, and we have to put
    `ns.head :: v` on `main` and `k_data` on `stack`. This is done using the `head` subroutine.
  * `ret (fix f k)`: This stores no data, so we just check if `main` starts with `0` and
    if so, remove it and call `k`, otherwise `clear` the first value and call `f`.
  * `ret halt`: the stack is empty, and `main` has the output. Do nothing and halt.

In addition to these basic states, we define some additional subroutines that are used in the
above:
* `push'`, `peek'`, `pop'` are special versions of the builtins that use the local store to supply
  inputs and outputs.
* `unrev`: special case `move ff rev main` to move everything from `rev` back to `main`. Used as a
  cleanup operation in several functions.
* `move_excl p k₁ k₂ q`: same as `move` but pushes the last value read back onto the source stack.
* `move₂ p k₁ k₂ q`: double `move`, so that the result comes out in the right order at the target
  stack. Implemented as `move_excl p k rev; move ff rev k₂`. Assumes that neither `k₁` nor `k₂` is
  `rev` and `rev` is initially empty.
* `head k q`: get the first natural number from stack `k` and reverse-move it to `rev`, then clear
  the rest of the list at `k` and then `unrev` to reverse-move the head value to `main`. This is
  used with `k = main` to implement regular `head`, i.e. if `v` is on `main` before then `[v.head]`
  will be on `main` after; and also with `k = stack` for the `cons` operation, which has `v` on
  `main` and `ns :: k_data` on `stack`, and results in `k_data` on `stack` and `ns.head :: v` on
  `main`.
* `tr_normal` is the main entry point, defining states that perform a given `code` computation.
  It mostly just dispatches to functions written above.

The main theorem of this section is `tr_eval`, which asserts that for each that for each code `c`,
the state `init c v` steps to `halt v'` in finitely many steps if and only if
`code.eval c v = some v'`.
-/

namespace partrec_to_TM2


/-- The alphabet for the stacks in the program. `bit0` and `bit1` are used to represent `ℕ` values
as lists of binary digits, `cons` is used to separate `list ℕ` values, and `Cons` is used to
separate `list (list ℕ)` values. See the section documentation. -/
inductive Γ' where
| Cons : Γ'
| cons : Γ'
| bit0 : Γ'
| bit1 : Γ'

/-- The four stacks used by the program. `main` is used to store the input value in `tr_normal`
mode and the output value in `Λ'.ret` mode, while `stack` is used to keep all the data for the
continuations. `rev` is used to store reversed lists when transferring values between stacks, and
`aux` is only used once in `cons₁`. See the section documentation. -/
inductive K' where
| main : K'
| rev : K'
| aux : K'
| stack : K'

/-- Continuations as in `to_partrec.cont` but with the data removed. This is done because we want
the set of all continuations in the program to be finite (so that it can ultimately be encoded into
the finite state machine of a Turing machine), but a continuation can handle a potentially infinite
number of data values during execution. -/
inductive cont' where
| halt : cont'
| cons₁ : to_partrec.code → cont' → cont'
| cons₂ : cont' → cont'
| comp : to_partrec.code → cont' → cont'
| fix : to_partrec.code → cont' → cont'

/-- The set of program positions. We make extensive use of inductive types here to let us describe
"subroutines"; for example `clear p k q` is a program that clears stack `k`, then does `q` where
`q` is another label. In order to prevent this from resulting in an infinite number of distinct
accessible states, we are careful to be non-recursive (although loops are okay). See the section
documentation for a description of all the programs. -/
inductive Λ' where
| move : (Γ' → Bool) → K' → K' → Λ' → Λ'
| clear : (Γ' → Bool) → K' → Λ' → Λ'
| copy : Λ' → Λ'
| push : K' → (Option Γ' → Option Γ') → Λ' → Λ'
| read : (Option Γ' → Λ') → Λ'
| succ : Λ' → Λ'
| pred : Λ' → Λ' → Λ'
| ret : cont' → Λ'

protected instance Λ'.inhabited : Inhabited Λ' := { default := Λ'.ret cont'.halt }

/-- The type of TM2 statements used by this machine. -/
/-- The type of TM2 configurations used by this machine. -/
def stmt' := TM2.stmt (fun (_x : K') => Γ') Λ' (Option Γ')

def cfg' := TM2.cfg (fun (_x : K') => Γ') Λ' (Option Γ')

/-- A predicate that detects the end of a natural number, either `Γ'.cons` or `Γ'.Cons` (or
implicitly the end of the list), for use in predicate-taking functions like `move` and `clear`. -/
def nat_end : Γ' → Bool := sorry

/-- Pop a value from the stack and place the result in local store. -/
/-- Peek a value from the stack and place the result in local store. -/
@[simp] def pop' (k : K') : stmt' → stmt' := TM2.stmt.pop k fun (x v : Option Γ') => v

/-- Push the value in the local store to the given stack. -/
@[simp] def peek' (k : K') : stmt' → stmt' := TM2.stmt.peek k fun (x v : Option Γ') => v

@[simp] def push' (k : K') : stmt' → stmt' := TM2.stmt.push k fun (x : Option Γ') => option.iget x

/-- Move everything from the `rev` stack to the `main` stack (reversed). -/
def unrev (q : Λ') : Λ' := Λ'.move (fun (_x : Γ') => false) K'.rev K'.main

/-- Move elements from `k₁` to `k₂` while `p` holds, with the last element being left on `k₁`. -/
def move_excl (p : Γ' → Bool) (k₁ : K') (k₂ : K') (q : Λ') : Λ' := Λ'.move p k₁ k₂ (Λ'.push k₁ id q)

/-- Move elements from `k₁` to `k₂` without reversion, by performing a double move via the `rev`
stack. -/
def move₂ (p : Γ' → Bool) (k₁ : K') (k₂ : K') (q : Λ') : Λ' :=
  move_excl p k₁ K'.rev (Λ'.move (fun (_x : Γ') => false) K'.rev k₂ q)

/-- Assuming `tr_list v` is on the front of stack `k`, remove it, and push `v.head` onto `main`.
See the section documentation. -/
def head (k : K') (q : Λ') : Λ' :=
  Λ'.move nat_end k K'.rev
    (Λ'.push K'.rev (fun (_x : Option Γ') => some Γ'.cons)
      (Λ'.read
        fun (s : Option Γ') =>
          ite (s = some Γ'.Cons) id (Λ'.clear (fun (x : Γ') => to_bool (x = Γ'.Cons)) k) (unrev q)))

/-- The program that evaluates code `c` with continuation `k`. This expects an initial state where
`tr_list v` is on `main`, `tr_cont_stack k` is on `stack`, and `aux` and `rev` are empty.
See the section documentation for details. -/
@[simp] def tr_normal : to_partrec.code → cont' → Λ' := sorry

/-- The main program. See the section documentation for details. -/
@[simp] def tr : Λ' → stmt' := sorry

/-- Translating a `cont` continuation to a `cont'` continuation simply entails dropping all the
data. This data is instead encoded in `tr_cont_stack` in the configuration. -/
def tr_cont : to_partrec.cont → cont' := sorry

/-- We use `pos_num` to define the translation of binary natural numbers. A natural number is
represented as a little-endian list of `bit0` and `bit1` elements:

    1 = [bit1]
    2 = [bit0, bit1]
    3 = [bit1, bit1]
    4 = [bit0, bit0, bit1]

In particular, this representation guarantees no trailing `bit0`'s at the end of the list. -/
def tr_pos_num : pos_num → List Γ' := sorry

/-- We use `num` to define the translation of binary natural numbers. Positive numbers are
translated using `tr_pos_num`, and `tr_num 0 = []`. So there are never any trailing `bit0`'s in
a translated `num`.

    0 = []
    1 = [bit1]
    2 = [bit0, bit1]
    3 = [bit1, bit1]
    4 = [bit0, bit0, bit1]
-/
def tr_num : num → List Γ' := sorry

/-- Because we use binary encoding, we define `tr_nat` in terms of `tr_num`, using `num`, which are
binary natural numbers. (We could also use `nat.binary_rec_on`, but `num` and `pos_num` make for
easy inductions.) -/
def tr_nat (n : ℕ) : List Γ' := tr_num ↑n

@[simp] theorem tr_nat_zero : tr_nat 0 = [] := rfl

/-- Lists are translated with a `cons` after each encoded number.
For example:

    [] = []
    [0] = [cons]
    [1] = [bit1, cons]
    [6, 0] = [bit0, bit1, bit1, cons, cons]
-/
@[simp] def tr_list : List ℕ → List Γ' := sorry

/-- Lists of lists are translated with a `Cons` after each encoded list.
For example:

    [] = []
    [[]] = [Cons]
    [[], []] = [Cons, Cons]
    [[0]] = [cons, Cons]
    [[1, 2], [0]] = [bit1, cons, bit0, bit1, cons, Cons, cons, Cons]
-/
@[simp] def tr_llist : List (List ℕ) → List Γ' := sorry

/-- The data part of a continuation is a list of lists, which is encoded on the `stack` stack
using `tr_llist`. -/
@[simp] def cont_stack : to_partrec.cont → List (List ℕ) := sorry

/-- The data part of a continuation is a list of lists, which is encoded on the `stack` stack
using `tr_llist`. -/
def tr_cont_stack (k : to_partrec.cont) : List Γ' := tr_llist (cont_stack k)

/-- This is the nondependent eliminator for `K'`, but we use it specifically here in order to
represent the stack data as four lists rather than as a function `K' → list Γ'`, because this makes
rewrites easier. The theorems `K'.elim_update_main` et. al. show how such a function is updated
after an `update` to one of the components. -/
@[simp] def K'.elim (a : List Γ') (b : List Γ') (c : List Γ') (d : List Γ') : K' → List Γ' := sorry

@[simp] theorem K'.elim_update_main {a : List Γ'} {b : List Γ'} {c : List Γ'} {d : List Γ'}
    {a' : List Γ'} : function.update (K'.elim a b c d) K'.main a' = K'.elim a' b c d :=
  sorry

@[simp] theorem K'.elim_update_rev {a : List Γ'} {b : List Γ'} {c : List Γ'} {d : List Γ'}
    {b' : List Γ'} : function.update (K'.elim a b c d) K'.rev b' = K'.elim a b' c d :=
  sorry

@[simp] theorem K'.elim_update_aux {a : List Γ'} {b : List Γ'} {c : List Γ'} {d : List Γ'}
    {c' : List Γ'} : function.update (K'.elim a b c d) K'.aux c' = K'.elim a b c' d :=
  sorry

@[simp] theorem K'.elim_update_stack {a : List Γ'} {b : List Γ'} {c : List Γ'} {d : List Γ'}
    {d' : List Γ'} : function.update (K'.elim a b c d) K'.stack d' = K'.elim a b c d' :=
  sorry

/-- The halting state corresponding to a `list ℕ` output value. -/
def halt (v : List ℕ) : cfg' := TM2.cfg.mk none none (K'.elim (tr_list v) [] [] [])

/-- The `cfg` states map to `cfg'` states almost one to one, except that in normal operation the
local store contains an arbitrary garbage value. To make the final theorem cleaner we explicitly
clear it in the halt state so that there is exactly one configuration corresponding to output `v`.
-/
def tr_cfg : to_partrec.cfg → cfg' → Prop := sorry

/-- This could be a general list definition, but it is also somewhat specialized to this
application. `split_at_pred p L` will search `L` for the first element satisfying `p`.
If it is found, say `L = l₁ ++ a :: l₂` where `a` satisfies `p` but `l₁` does not, then it returns
`(l₁, some a, l₂)`. Otherwise, if there is no such element, it returns `(L, none, [])`. -/
def split_at_pred {α : Type u_1} (p : α → Bool) : List α → List α × Option α × List α := sorry

theorem split_at_pred_eq {α : Type u_1} (p : α → Bool) (L : List α) (l₁ : List α) (o : Option α)
    (l₂ : List α) :
    (∀ (x : α), x ∈ l₁ → p x = false) →
        (option.elim o (L = l₁ ∧ l₂ = []) fun (a : α) => p a = tt ∧ L = l₁ ++ a :: l₂) →
          split_at_pred p L = (l₁, o, l₂) :=
  sorry

theorem split_at_pred_ff {α : Type u_1} (L : List α) :
    split_at_pred (fun (_x : α) => false) L = (L, none, []) :=
  split_at_pred_eq (fun (_x : α) => false) L L none [] (fun (_x : α) (_x : _x ∈ L) => rfl)
    { left := rfl, right := rfl }

theorem move_ok {p : Γ' → Bool} {k₁ : K'} {k₂ : K'} {q : Λ'} {s : Option Γ'} {L₁ : List Γ'}
    {o : Option Γ'} {L₂ : List Γ'} {S : K' → List Γ'} (h₁ : k₁ ≠ k₂)
    (e : split_at_pred p (S k₁) = (L₁, o, L₂)) :
    reaches₁ (TM2.step tr) (TM2.cfg.mk (some (Λ'.move p k₁ k₂ q)) s S)
        (TM2.cfg.mk (some q) o
          (function.update (function.update S k₁ L₂) k₂ (list.reverse_core L₁ (S k₂)))) :=
  sorry

theorem unrev_ok {q : Λ'} {s : Option Γ'} {S : K' → List Γ'} :
    reaches₁ (TM2.step tr) (TM2.cfg.mk (some (unrev q)) s S)
        (TM2.cfg.mk (some q) none
          (function.update (function.update S K'.rev []) K'.main
            (list.reverse_core (S K'.rev) (S K'.main)))) :=
  move_ok (of_as_true trivial) (split_at_pred_ff (S K'.rev))

theorem move₂_ok {p : Γ' → Bool} {k₁ : K'} {k₂ : K'} {q : Λ'} {s : Option Γ'} {L₁ : List Γ'}
    {o : Option Γ'} {L₂ : List Γ'} {S : K' → List Γ'} (h₁ : k₁ ≠ K'.rev ∧ k₂ ≠ K'.rev ∧ k₁ ≠ k₂)
    (h₂ : S K'.rev = []) (e : split_at_pred p (S k₁) = (L₁, o, L₂)) :
    reaches₁ (TM2.step tr) (TM2.cfg.mk (some (move₂ p k₁ k₂ q)) s S)
        (TM2.cfg.mk (some q) none
          (function.update (function.update S k₁ (option.elim o id List.cons L₂)) k₂
            (L₁ ++ S k₂))) :=
  sorry

theorem clear_ok {p : Γ' → Bool} {k : K'} {q : Λ'} {s : Option Γ'} {L₁ : List Γ'} {o : Option Γ'}
    {L₂ : List Γ'} {S : K' → List Γ'} (e : split_at_pred p (S k) = (L₁, o, L₂)) :
    reaches₁ (TM2.step tr) (TM2.cfg.mk (some (Λ'.clear p k q)) s S)
        (TM2.cfg.mk (some q) o (function.update S k L₂)) :=
  sorry

theorem copy_ok (q : Λ') (s : Option Γ') (a : List Γ') (b : List Γ') (c : List Γ') (d : List Γ') :
    reaches₁ (TM2.step tr) (TM2.cfg.mk (some (Λ'.copy q)) s (K'.elim a b c d))
        (TM2.cfg.mk (some q) none (K'.elim (list.reverse_core b a) [] c (list.reverse_core b d))) :=
  sorry

theorem tr_pos_num_nat_end (n : pos_num) (x : Γ') (H : x ∈ tr_pos_num n) : nat_end x = false :=
  sorry

theorem tr_num_nat_end (n : num) (x : Γ') (H : x ∈ tr_num n) : nat_end x = false := sorry

theorem tr_nat_nat_end (n : ℕ) (x : Γ') (H : x ∈ tr_nat n) : nat_end x = false := tr_num_nat_end ↑n

theorem tr_list_ne_Cons (l : List ℕ) (x : Γ') (H : x ∈ tr_list l) : x ≠ Γ'.Cons := sorry

theorem head_main_ok {q : Λ'} {s : Option Γ'} {L : List ℕ} {c : List Γ'} {d : List Γ'} :
    reaches₁ (TM2.step tr) (TM2.cfg.mk (some (head K'.main q)) s (K'.elim (tr_list L) [] c d))
        (TM2.cfg.mk (some q) none (K'.elim (tr_list [list.head L]) [] c d)) :=
  sorry

theorem head_stack_ok {q : Λ'} {s : Option Γ'} {L₁ : List ℕ} {L₂ : List ℕ} {L₃ : List Γ'} :
    reaches₁ (TM2.step tr)
        (TM2.cfg.mk (some (head K'.stack q)) s
          (K'.elim (tr_list L₁) [] [] (tr_list L₂ ++ Γ'.Cons :: L₃)))
        (TM2.cfg.mk (some q) none (K'.elim (tr_list (list.head L₂ :: L₁)) [] [] L₃)) :=
  sorry

theorem succ_ok {q : Λ'} {s : Option Γ'} {n : ℕ} {c : List Γ'} {d : List Γ'} :
    reaches₁ (TM2.step tr) (TM2.cfg.mk (some (Λ'.succ q)) s (K'.elim (tr_list [n]) [] c d))
        (TM2.cfg.mk (some q) none (K'.elim (tr_list [Nat.succ n]) [] c d)) :=
  sorry

theorem pred_ok (q₁ : Λ') (q₂ : Λ') (s : Option Γ') (v : List ℕ) (c : List Γ') (d : List Γ') :
    ∃ (s' : Option Γ'),
        reaches₁ (TM2.step tr) (TM2.cfg.mk (some (Λ'.pred q₁ q₂)) s (K'.elim (tr_list v) [] c d))
          (nat.elim (TM2.cfg.mk (some q₁) s' (K'.elim (tr_list (list.tail v)) [] c d))
            (fun (n : ℕ) (_x : TM2.cfg (fun (_x : K') => Γ') Λ' (Option Γ')) =>
              TM2.cfg.mk (some q₂) s' (K'.elim (tr_list (n :: list.tail v)) [] c d))
            (list.head v)) :=
  sorry

theorem tr_normal_respects (c : to_partrec.code) (k : to_partrec.cont) (v : List ℕ)
    (s : Option Γ') :
    ∃ (b₂ : cfg'),
        tr_cfg (to_partrec.step_normal c k v) b₂ ∧
          reaches₁ (TM2.step tr)
            (TM2.cfg.mk (some (tr_normal c (tr_cont k))) s
              (K'.elim (tr_list v) [] [] (tr_cont_stack k)))
            b₂ :=
  sorry

theorem tr_ret_respects (k : to_partrec.cont) (v : List ℕ) (s : Option Γ') :
    ∃ (b₂ : cfg'),
        tr_cfg (to_partrec.step_ret k v) b₂ ∧
          reaches₁ (TM2.step tr)
            (TM2.cfg.mk (some (Λ'.ret (tr_cont k))) s (K'.elim (tr_list v) [] [] (tr_cont_stack k)))
            b₂ :=
  sorry

theorem tr_respects : respects to_partrec.step (TM2.step tr) tr_cfg := sorry

/-- The initial state, evaluating function `c` on input `v`. -/
def init (c : to_partrec.code) (v : List ℕ) : cfg' :=
  TM2.cfg.mk (some (tr_normal c cont'.halt)) none (K'.elim (tr_list v) [] [] [])

theorem tr_init (c : to_partrec.code) (v : List ℕ) :
    ∃ (b : cfg'),
        tr_cfg (to_partrec.step_normal c to_partrec.cont.halt v) b ∧
          reaches₁ (TM2.step tr) (init c v) b :=
  tr_normal_respects c to_partrec.cont.halt v none

theorem tr_eval (c : to_partrec.code) (v : List ℕ) :
    eval (TM2.step tr) (init c v) = halt <$> to_partrec.code.eval c v :=
  sorry

end Mathlib