/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.option.defs
import Mathlib.meta.expr
import PostPort

namespace Mathlib

/-!
# Matching expressions with leading binders

This module defines a family of tactics for matching expressions with leading Π
or λ binders, similar to Core's `mk_local_pis`. They all iterate over an
expression, processing one leading binder at a time. The bound variable is
replaced by either a fresh local constant or a fresh metavariable in the binder
body, 'opening' the binder. We then recurse into this new body. This scheme is
implemented by `tactic.open_binders` and `tactic.open_n_binders`.

Based on these general tactics, we define many variations of this recipe:

- `open_pis` opens all leading Π binders and replaces them with
  fresh local constants. This is defined in core.
- `open_lambdas` opens leading λ binders instead. Example:

  ```
  open_lambdas `(λ (x : X) (y : Y), f x y) =
    ([`(_fresh.1), `(_fresh.2)], `(f _fresh.1 _fresh.2))
  ```

  `_fresh.1` and `_fresh.2` are fresh local constants (with types `X` and `Y`,
  respectively). The second component of the pair is the lambda body with
  `x` replaced by `_fresh.1` and `y` replaced by `_fresh.2`.
- `open_pis_metas` opens all leading Π binders and replaces them with fresh
  metavariables (instead of local constants).
- `open_n_pis` opens only the first `n` leading Π binders and fails if there are
  not at least `n` leading binders. Example:

  ```
  open_n_pis `(Π (x : X) (y : Y), P x y) 1 =
    ([`(_fresh.1)], `(Π (y : Y), P _fresh.1 y))
  ```
- `open_lambdas_whnf` normalises the input expression each time before trying to
  match a binder. Example:

  ```
  open_lambdas_whnf `(let f := λ (x : X), g x y in f) =
    ([`(_fresh.1)], `(g _fresh.1 y))
  ```
- Any combination of these features is also provided, e.g.
  `open_n_lambdas_metas_whnf` to open `n` λ binders up to normalisation,
  replacing them with fresh metavariables.

The `open_*` functions are commonly used like this:

1. Open (some of) the binders of an expression `e`, producing local constants
   `lcs` and the 'body' `e'` of `e`.
2. Process `e'` in some way.
3. Reconstruct the binders using `tactic.pis` or `tactic.lambdas`, which
   Π/λ-bind the `lcs` in `e'`. This reverts the effect of `open_*`.
-/

namespace tactic


/--
`get_binder do_whnf pi_or_lambda e` matches `e` of the form `λ x, e'` or
`Π x, e`. Returns information about the leading binder (its name, `binder_info`,
type and body), or `none` if `e` does not start with a binder.

If `do_whnf = some (md, unfold_ginductive)`, then `e` is weak head normalised
with transparency `md` before matching on it. `unfold_ginductive` controls
whether constructors of generalised inductive data types are unfolded during
normalisation.

If `pi_or_lambda` is `tt`, we match a leading Π binder; otherwise a leading λ
binder.
-/
