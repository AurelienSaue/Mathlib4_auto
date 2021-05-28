/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jannis Limperg
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.core
import Mathlib.PostPort

namespace Mathlib

/-!
# The `generalizes` tactic

This module defines the `tactic.generalizes'` tactic and its interactive version
`tactic.interactive.generalizes`. These work like `generalize`, but they can
generalize over multiple expressions at once. This is particularly handy when
there are dependencies between the expressions, in which case `generalize` will
usually fail but `generalizes` may succeed.

## Implementation notes

To generalize the target `T` over expressions `j₁ : J₁, ..., jₙ : Jₙ`, we first
create the new target type

    T' = ∀ (k₁ : J₁) ... (kₙ : Jₙ) (k₁_eq : k₁ = j₁) ... (kₙ_eq : kₙ == jₙ), U

where `U` is `T` with any occurrences of the `jᵢ` replaced by the corresponding
`kᵢ`. Note that some of the `kᵢ_eq` may be heterogeneous; this happens when
there are dependencies between the `jᵢ`. The construction of `T'` is performed
by `generalizes.step1` and `generalizes.step2`.

Having constructed `T'`, we can `assert` it and use it to construct a proof of
the original target by instantiating the binders with

    j₁ ... jₙ (eq.refl j₁) ... (heq.refl jₙ).

This leaves us with a generalized goal. This construction is performed by
`generalizes.step3`.
-/

namespace tactic


namespace generalizes


/--
Input:

- Target expression `e`.
- List of expressions `jᵢ` to be generalised, along with a name for the local
  const that will replace them. The `jᵢ` must be in dependency order:
  `[n, fin n]` is okay but `[fin n, n]` is not.

Output:

- List of new local constants `kᵢ`, one for each `jᵢ`.
- `e` with the `jᵢ` replaced by the `kᵢ`, i.e. `e[jᵢ := kᵢ]...[j₀ := k₀]`.

Note that the substitution also affects the types of the `kᵢ`: If `jᵢ : Jᵢ` then
`kᵢ : Jᵢ[jᵢ₋₁ := kᵢ₋₁]...[j₀ := k₀]`.

The transparency `md` and the boolean `unify` are passed to `kabstract` when we
abstract over occurrences of the `jᵢ` in `e`.
-/
/--
Input: for each equation that should be generated: the equation name, the
argument `jᵢ` and the corresponding local constant `kᵢ` from step 1.

Output: for each element of the input list a new local constant of type
`jᵢ = kᵢ` or `jᵢ == kᵢ` and a proof of `jᵢ = jᵢ` or `jᵢ == jᵢ`.

The transparency `md` is used when determining whether the type of `jᵢ` is defeq
to the type of `kᵢ` (and thus whether to generate a homogeneous or heterogeneous
equation).
-/
/--
Input: The `jᵢ`; the local constants `kᵢ` from step 1; the equations and their
proofs from step 2.

This step is the first one that changes the goal (and also the last one
overall). It asserts the generalized goal, then derives the current goal from
it. This leaves us with the generalized goal.
-/
end generalizes


/--
Generalizes the target over each of the expressions in `args`. Given
`args = [(a₁, h₁, arg₁), ...]`, this changes the target to

    ∀ (a₁ : T₁) ... (h₁ : a₁ = arg₁) ..., U

where `U` is the current target with every occurrence of `argᵢ` replaced by
`aᵢ`. A similar effect can be achieved by using `generalize` once for each of
the `args`, but if there are dependencies between the `args`, this may fail to
perform some generalizations.

The replacement is performed using keyed matching/unification with transparency
`md`. `unify` determines whether matching or unification is used. See
`kabstract`.

The `args` must be given in dependency order, so `[n, fin n]` is okay but
`[fin n, n]` will result in an error.

After generalizing the `args`, the target type may no longer type check.
`generalizes'` will then raise an error.
-/
/--
Like `generalizes'`, but also introduces the generalized constants and their
associated equations into the context.
-/
namespace interactive


/--
Generalizes the target over multiple expressions. For example, given the goal

    P : ∀ n, fin n → Prop
    n : ℕ
    f : fin n
    ⊢ P (nat.succ n) (fin.succ f)

you can use `generalizes [n'_eq : nat.succ n = n', f'_eq : fin.succ f == f']` to
get

    P : ∀ n, fin n → Prop
    n : ℕ
    f : fin n
    n' : ℕ
    n'_eq : n' = nat.succ n
    f' : fin n'
    f'_eq : f' == fin.succ f
    ⊢ P n' f'

The expressions must be given in dependency order, so
`[f'_eq : fin.succ f == f', n'_eq : nat.succ n = n']` would fail since the type
of `fin.succ f` is `nat.succ n`.

You can choose to omit some or all of the generated equations. For the above
example, `generalizes [nat.succ n = n', fin.succ f == f']` gets you

    P : ∀ n, fin n → Prop
    n : ℕ
    f : fin n
    n' : ℕ
    f' : fin n'
    ⊢ P n' f'

After generalization, the target type may no longer type check. `generalizes`
will then raise an error.
-/
