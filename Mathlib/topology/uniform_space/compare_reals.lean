/-
Copyright (c) 2019 Patrick MAssot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.uniform_space.absolute_value
import Mathlib.topology.instances.real
import Mathlib.topology.uniform_space.completion
import Mathlib.PostPort

namespace Mathlib

/-!
# Comparison of Cauchy reals and Bourbaki reals

In `data.real.basic` real numbers are defined using the so called Cauchy construction (although
it is due to Georg Cantor). More precisely, this construction applies to commutative rings equipped
with an absolute value with values in a linear ordered field.

On the other hand, in the `uniform_space` folder, we construct completions of general uniform
spaces, which allows to construct the Bourbaki real numbers. In this file we build uniformly
continuous bijections from Cauchy reals to Bourbaki reals and back. This is a cross sanity check of
both constructions. Of course those two constructions are variations on the completion idea, simply
with different level of generality. Comparing with Dedekind cuts or quasi-morphisms would be of a
completely different nature.

Note that `metric_space/cau_seq_filter` also relates the notions of Cauchy sequences in metric
spaces and Cauchy filters in general uniform spaces, and `metric_space/completion` makes sure
the completion (as a uniform space) of a metric space is a metric space.

Historical note: mathlib used to define real numbers in an intermediate way, using completion
of uniform spaces but extending multiplication in an ad-hoc way.

TODO:
* Upgrade this isomorphism to a topological ring isomorphism.
* Do the same comparison for p-adic numbers

## Implementation notes

The heavy work is done in `topology/uniform_space/abstract_completion` which provides an abstract
caracterization of completions of uniform spaces, and isomorphisms between them. The only work left
here is to prove the uniform space structure coming from the absolute value on ℚ (with values in ℚ,
not referring to ℝ) coincides with the one coming from the metric space structure (which of course
does use ℝ).

## References

* [N. Bourbaki, *Topologie générale*][bourbaki1966]

## Tags

real numbers, completion, uniform spaces
-/

/-- The metric space uniform structure on ℚ (which presupposes the existence
of real numbers) agrees with the one coming directly from (abs : ℚ → ℚ). -/
theorem rat.uniform_space_eq : is_absolute_value.uniform_space abs = metric_space.to_uniform_space' := sorry

/-- Cauchy reals packaged as a completion of ℚ using the absolute value route. -/
def rational_cau_seq_pkg : abstract_completion ℚ :=
  abstract_completion.mk ℝ coe metric_space.to_uniform_space' real.complete_space metric_space.to_separated sorry sorry

namespace compare_reals


/-- Type wrapper around ℚ to make sure the absolute value uniform space instance is picked up
instead of the metric space one. We proved in rat.uniform_space_eq that they are equal,
but they are not definitionaly equal, so it would confuse the type class system (and probably
also human readers). -/
def Q :=
  ℚ

protected instance Q.uniform_space : uniform_space Q :=
  is_absolute_value.uniform_space abs

/-- Real numbers constructed as in Bourbaki. -/
def Bourbakiℝ :=
  uniform_space.completion Q

protected instance bourbaki.uniform_space : uniform_space Bourbakiℝ :=
  uniform_space.completion.uniform_space Q

/-- Bourbaki reals packaged as a completion of Q using the general theory. -/
def Bourbaki_pkg : abstract_completion Q :=
  uniform_space.completion.cpkg

/-- The equivalence between Bourbaki and Cauchy reals-/
def compare_equiv : Bourbakiℝ ≃ ℝ :=
  abstract_completion.compare_equiv Bourbaki_pkg rational_cau_seq_pkg

theorem compare_uc : uniform_continuous ⇑compare_equiv :=
  abstract_completion.uniform_continuous_compare_equiv Bourbaki_pkg rational_cau_seq_pkg

theorem compare_uc_symm : uniform_continuous ⇑(equiv.symm compare_equiv) :=
  abstract_completion.uniform_continuous_compare_equiv_symm Bourbaki_pkg rational_cau_seq_pkg

