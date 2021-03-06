/-
Copyright (c) 2019 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.metric_space.hausdorff_distance
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Riesz's lemma

Riesz's lemma, stated for a normed space over a normed field: for any
closed proper subspace F of E, there is a nonzero x such that âĽx - FâĽ
is at least r * âĽxâĽ for any r < 1.
-/

/-- Riesz's lemma, which usually states that it is possible to find a
vector with norm 1 whose distance to a closed proper subspace is
arbitrarily close to 1. The statement here is in terms of multiples of
norms, since in general the existence of an element of norm exactly 1
is not guaranteed. -/
theorem riesz_lemma {đ : Type u_1} [normed_field đ] {E : Type u_2} [normed_group E] [normed_space đ E] {F : subspace đ E} (hFc : is_closed âF) (hF : â (x : E), ÂŹx â F) {r : â} (hr : r < 1) : â (xâ : E), ÂŹxâ â F â§ â (y : E), y â F â r * norm xâ â¤ norm (xâ - y) := sorry

