/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl (CMU)
-/
import PrePort
import Lean3Lib.init.meta.tactic
import Lean3Lib.init.meta.match_tactic
import Lean3Lib.init.meta.mk_dec_eq_instance
import Lean3Lib.init.data.list.instances
import Mathlib.logic.relator
import PostPort

namespace Mathlib

namespace transfer


/- Transfer rules are of the shape:

  rel_t : {u} Πx, R t₁ t₂

where `u` is a list of universe parameters, `x` is a list of dependent variables, and `R` is a
relation.  Then this rule will translate `t₁` (depending on `u` and `x`) into `t₂`.  `u` and `x`
will be called parameters. When `R` is a relation on functions lifted from `S` and `R` the variables
bound by `S` are called arguments. `R` is generally constructed using `⇒` (i.e. `relator.lift_fun`).

As example:

  rel_eq : (R ⇒ R ⇒ iff) eq t

transfer will match this rule when it sees:

  (@eq α a b)      and transfer it to    (t a b)

Here `α` is a parameter and `a` and `b` are arguments.


TODO: add trace statements

TODO: currently the used relation must be fixed by the matched rule or through type class
  inference. Maybe we want to replace this by type inference similar to Isabelle's transfer.

-/

