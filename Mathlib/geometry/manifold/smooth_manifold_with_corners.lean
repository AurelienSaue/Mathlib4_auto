/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.analysis.calculus.times_cont_diff
import Mathlib.geometry.manifold.charted_space
import Mathlib.PostPort

universes u_1 u_2 u_3 l u_4 u v v' w w' u_6 u_8 u_7 u_5 

namespace Mathlib

/-!
# Smooth manifolds (possibly with boundary or corners)

A smooth manifold is a manifold modelled on a normed vector space, or a subset like a
half-space (to get manifolds with boundaries) for which the changes of coordinates are smooth maps.
We define a model with corners as a map `I : H → E` embedding nicely the topological space `H` in
the vector space `E` (or more precisely as a structure containing all the relevant properties).
Given such a model with corners `I` on `(E, H)`, we define the groupoid of local
homeomorphisms of `H` which are smooth when read in `E` (for any regularity `n : with_top ℕ`).
With this groupoid at hand and the general machinery of charted spaces, we thus get the notion
of `C^n` manifold with respect to any model with corners `I` on `(E, H)`. We also introduce a
specific type class for `C^∞` manifolds as these are the most commonly used.

## Main definitions

* `model_with_corners 𝕜 E H` :
  a structure containing informations on the way a space `H` embeds in a
  model vector space E over the field `𝕜`. This is all that is needed to
  define a smooth manifold with model space `H`, and model vector space `E`.
* `model_with_corners_self 𝕜 E` :
  trivial model with corners structure on the space `E` embedded in itself by the identity.
* `times_cont_diff_groupoid n I` :
  when `I` is a model with corners on `(𝕜, E, H)`, this is the groupoid of local homeos of `H`
  which are of class `C^n` over the normed field `𝕜`, when read in `E`.
* `smooth_manifold_with_corners I M` :
  a type class saying that the charted space `M`, modelled on the space `H`, has `C^∞` changes of
  coordinates with respect to the model with corners `I` on `(𝕜, E, H)`. This type class is just
  a shortcut for `has_groupoid M (times_cont_diff_groupoid ∞ I)`.
* `ext_chart_at I x`:
  in a smooth manifold with corners with the model `I` on `(E, H)`, the charts take values in `H`,
  but often we may want to use their `E`-valued version, obtained by composing the charts with `I`.
  Since the target is in general not open, we can not register them as local homeomorphisms, but
  we register them as local equivs. `ext_chart_at I x` is the canonical such local equiv around `x`.

As specific examples of models with corners, we define (in the file `real_instances.lean`)
* `model_with_corners_self ℝ (euclidean_space (fin n))` for the model space used to define
  `n`-dimensional real manifolds without boundary (with notation `𝓡 n` in the locale `manifold`)
* `model_with_corners ℝ (euclidean_space (fin n)) (euclidean_half_space n)` for the model space
  used to define `n`-dimensional real manifolds with boundary (with notation `𝓡∂ n` in the locale
  `manifold`)
* `model_with_corners ℝ (euclidean_space (fin n)) (euclidean_quadrant n)` for the model space used
  to define `n`-dimensional real manifolds with corners

With these definitions at hand, to invoke an `n`-dimensional real manifold without boundary,
one could use

  `variables {n : ℕ} {M : Type*} [topological_space M] [charted_space (euclidean_space (fin n)) M]
   [smooth_manifold_with_corners (𝓡 n) M]`.

However, this is not the recommended way: a theorem proved using this assumption would not apply
for instance to the tangent space of such a manifold, which is modelled on
`(euclidean_space (fin n)) × (euclidean_space (fin n))` and not on `euclidean_space (fin (2 * n))`!
In the same way, it would not apply to product manifolds, modelled on
`(euclidean_space (fin n)) × (euclidean_space (fin m))`.
The right invocation does not focus on one specific construction, but on all constructions sharing
the right properties, like

  `variables {E : Type*} [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
  {I : model_with_corners ℝ E E} [I.boundaryless]
  {M : Type*} [topological_space M] [charted_space E M] [smooth_manifold_with_corners I M]`

Here, `I.boundaryless` is a typeclass property ensuring that there is no boundary (this is for
instance the case for `model_with_corners_self`, or products of these). Note that one could consider
as a natural assumption to only use the trivial model with corners `model_with_corners_self ℝ E`,
but again in product manifolds the natural model with corners will not be this one but the product
one (and they are not defeq as `(λp : E × F, (p.1, p.2))` is not defeq to the identity). So, it is
important to use the above incantation to maximize the applicability of theorems.

## Implementation notes

We want to talk about manifolds modelled on a vector space, but also on manifolds with
boundary, modelled on a half space (or even manifolds with corners). For the latter examples,
we still want to define smooth functions, tangent bundles, and so on. As smooth functions are
well defined on vector spaces or subsets of these, one could take for model space a subtype of a
vector space. With the drawback that the whole vector space itself (which is the most basic
example) is not directly a subtype of itself: the inclusion of `univ : set E` in `set E` would
show up in the definition, instead of `id`.

A good abstraction covering both cases it to have a vector
space `E` (with basic example the Euclidean space), a model space `H` (with basic example the upper
half space), and an embedding of `H` into `E` (which can be the identity for `H = E`, or
`subtype.val` for manifolds with corners). We say that the pair `(E, H)` with their embedding is a
model with corners, and we encompass all the relevant properties (in particular the fact that the
image of `H` in `E` should have unique differentials) in the definition of `model_with_corners`.

We concentrate on `C^∞` manifolds: all the definitions work equally well for `C^n` manifolds, but
later on it is a pain to carry all over the smoothness parameter, especially when one wants to deal
with `C^k` functions as there would be additional conditions `k ≤ n` everywhere. Since one deals
almost all the time with `C^∞` (or analytic) manifolds, this seems to be a reasonable choice that
one could revisit later if needed. `C^k` manifolds are still available, but they should be called
using `has_groupoid M (times_cont_diff_groupoid k I)` where `I` is the model with corners.

I have considered using the model with corners `I` as a typeclass argument, possibly `out_param`, to
get lighter notations later on, but it did not turn out right, as on `E × F` there are two natural
model with corners, the trivial (identity) one, and the product one, and they are not defeq and one
needs to indicate to Lean which one we want to use.
This means that when talking on objects on manifolds one will most often need to specify the model
with corners one is using. For instance, the tangent bundle will be `tangent_bundle I M` and the
derivative will be `mfderiv I I' f`, instead of the more natural notations `tangent_bundle 𝕜 M` and
`mfderiv 𝕜 f` (the field has to be explicit anyway, as some manifolds could be considered both as
real and complex manifolds).
-/

/-! ### Models with corners. -/

/-- A structure containing informations on the way a space `H` embeds in a
model vector space `E` over the field `𝕜`. This is all what is needed to
define a smooth manifold with model space `H`, and model vector space `E`.
-/
structure model_with_corners (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] (E : Type u_2) [normed_group E] [normed_space 𝕜 E] (H : Type u_3) [topological_space H] 
extends local_equiv H E
where
  source_eq : local_equiv.source _to_local_equiv = set.univ
  unique_diff' : unique_diff_on 𝕜 (set.range (local_equiv.to_fun _to_local_equiv))
  continuous_to_fun : autoParam (continuous (local_equiv.to_fun _to_local_equiv))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.tactic.interactive.continuity'")
    (Lean.Name.mkStr
      (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "tactic") "interactive")
      "continuity'")
    [])
  continuous_inv_fun : autoParam (continuous (local_equiv.inv_fun _to_local_equiv))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.tactic.interactive.continuity'")
    (Lean.Name.mkStr
      (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "tactic") "interactive")
      "continuity'")
    [])

/-- A vector space is a model with corners. -/
def model_with_corners_self (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] (E : Type u_2) [normed_group E] [normed_space 𝕜 E] : model_with_corners 𝕜 E E :=
  model_with_corners.mk (local_equiv.mk id id set.univ set.univ sorry sorry sorry sorry) sorry sorry

protected instance model_with_corners.has_coe_to_fun {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] : has_coe_to_fun (model_with_corners 𝕜 E H) :=
  has_coe_to_fun.mk (fun (e : model_with_corners 𝕜 E H) => H → E)
    fun (e : model_with_corners 𝕜 E H) => local_equiv.to_fun (model_with_corners.to_local_equiv e)

/-- The inverse to a model with corners, only registered as a local equiv. -/
protected def model_with_corners.symm {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) : local_equiv E H :=
  local_equiv.symm (model_with_corners.to_local_equiv I)

/- Register a few lemmas to make sure that `simp` puts expressions in normal form -/

@[simp] theorem model_with_corners.to_local_equiv_coe {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) : ⇑(model_with_corners.to_local_equiv I) = ⇑I :=
  rfl

@[simp] theorem model_with_corners.mk_coe {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (e : local_equiv H E) (a : local_equiv.source e = set.univ) (b : unique_diff_on 𝕜 (set.range (local_equiv.to_fun e))) (c : autoParam (continuous (local_equiv.to_fun e))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.tactic.interactive.continuity'")
    (Lean.Name.mkStr
      (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "tactic") "interactive")
      "continuity'")
    [])) (d : autoParam (continuous (local_equiv.inv_fun e))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.tactic.interactive.continuity'")
    (Lean.Name.mkStr
      (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "tactic") "interactive")
      "continuity'")
    [])) : ⇑(model_with_corners.mk e a b) = ⇑e :=
  rfl

@[simp] theorem model_with_corners.to_local_equiv_coe_symm {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) : ⇑(local_equiv.symm (model_with_corners.to_local_equiv I)) = ⇑(model_with_corners.symm I) :=
  rfl

@[simp] theorem model_with_corners.mk_coe_symm {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (e : local_equiv H E) (a : local_equiv.source e = set.univ) (b : unique_diff_on 𝕜 (set.range (local_equiv.to_fun e))) (c : autoParam (continuous (local_equiv.to_fun e))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.tactic.interactive.continuity'")
    (Lean.Name.mkStr
      (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "tactic") "interactive")
      "continuity'")
    [])) (d : autoParam (continuous (local_equiv.inv_fun e))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.tactic.interactive.continuity'")
    (Lean.Name.mkStr
      (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "tactic") "interactive")
      "continuity'")
    [])) : ⇑(model_with_corners.symm (model_with_corners.mk e a b)) = ⇑(local_equiv.symm e) :=
  rfl

theorem model_with_corners.unique_diff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) : unique_diff_on 𝕜 (set.range ⇑I) :=
  model_with_corners.unique_diff' I

protected theorem model_with_corners.continuous {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) : continuous ⇑I :=
  model_with_corners.continuous_to_fun I

theorem model_with_corners.continuous_symm {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) : continuous ⇑(model_with_corners.symm I) :=
  model_with_corners.continuous_inv_fun I

/-- In the trivial model with corners, the associated local equiv is the identity. -/
@[simp] theorem model_with_corners_self_local_equiv (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] (E : Type u_2) [normed_group E] [normed_space 𝕜 E] : model_with_corners.to_local_equiv (model_with_corners_self 𝕜 E) = local_equiv.refl E :=
  rfl

@[simp] theorem model_with_corners_self_coe (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] (E : Type u_2) [normed_group E] [normed_space 𝕜 E] : ⇑(model_with_corners_self 𝕜 E) = id :=
  rfl

@[simp] theorem model_with_corners_self_coe_symm (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] (E : Type u_2) [normed_group E] [normed_space 𝕜 E] : ⇑(model_with_corners.symm (model_with_corners_self 𝕜 E)) = id :=
  rfl

@[simp] theorem model_with_corners.target {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) : local_equiv.target (model_with_corners.to_local_equiv I) = set.range ⇑I := sorry

@[simp] theorem model_with_corners.left_inv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) (x : H) : coe_fn (model_with_corners.symm I) (coe_fn I x) = x := sorry

@[simp] theorem model_with_corners.left_inv' {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) : ⇑(model_with_corners.symm I) ∘ ⇑I = id :=
  funext fun (x : H) => model_with_corners.left_inv I x

@[simp] theorem model_with_corners.right_inv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {x : E} (hx : x ∈ set.range ⇑I) : coe_fn I (coe_fn (model_with_corners.symm I) x) = x := sorry

theorem model_with_corners.image {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) (s : set H) : ⇑I '' s = ⇑(model_with_corners.symm I) ⁻¹' s ∩ set.range ⇑I := sorry

theorem model_with_corners.unique_diff_preimage {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {s : set H} (hs : is_open s) : unique_diff_on 𝕜 (⇑(model_with_corners.symm I) ⁻¹' s ∩ set.range ⇑I) := sorry

theorem model_with_corners.unique_diff_preimage_source {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {β : Type u_4} [topological_space β] {e : local_homeomorph H β} : unique_diff_on 𝕜
  (⇑(model_with_corners.symm I) ⁻¹' local_equiv.source (local_homeomorph.to_local_equiv e) ∩ set.range ⇑I) :=
  model_with_corners.unique_diff_preimage I (local_homeomorph.open_source e)

theorem model_with_corners.unique_diff_at_image {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {x : H} : unique_diff_within_at 𝕜 (set.range ⇑I) (coe_fn I x) :=
  model_with_corners.unique_diff I (coe_fn I x) (set.mem_range_self x)

/-- Given two model_with_corners `I` on `(E, H)` and `I'` on `(E', H')`, we define the model with
corners `I.prod I'` on `(E × E', H × H')`. This appears in particular for the manifold structure on
the tangent bundle to a manifold modelled on `(E, H)`: it will be modelled on `(E × E, H × E)`. -/
def model_with_corners.prod {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {E : Type v} [normed_group E] [normed_space 𝕜 E] {H : Type w} [topological_space H] (I : model_with_corners 𝕜 E H) {E' : Type v'} [normed_group E'] [normed_space 𝕜 E'] {H' : Type w'} [topological_space H'] (I' : model_with_corners 𝕜 E' H') : model_with_corners 𝕜 (E × E') (model_prod H H') :=
  model_with_corners.mk
    (local_equiv.mk (fun (p : model_prod H H') => (coe_fn I (prod.fst p), coe_fn I' (prod.snd p)))
      (fun (p : E × E') =>
        (coe_fn (model_with_corners.symm I) (prod.fst p), coe_fn (model_with_corners.symm I') (prod.snd p)))
      set.univ (set.prod (set.range ⇑I) (set.range ⇑I')) sorry sorry sorry sorry)
    sorry sorry

/-- Special case of product model with corners, which is trivial on the second factor. This shows up
as the model to tangent bundles. -/
def model_with_corners.tangent {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {E : Type v} [normed_group E] [normed_space 𝕜 E] {H : Type w} [topological_space H] (I : model_with_corners 𝕜 E H) : model_with_corners 𝕜 (E × E) (model_prod H E) :=
  model_with_corners.prod I (model_with_corners_self 𝕜 E)

@[simp] theorem model_with_corners_prod_to_local_equiv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_4} [normed_group F] [normed_space 𝕜 F] {H : Type u_6} [topological_space H] {G : Type u_8} [topological_space G] {I : model_with_corners 𝕜 E H} {J : model_with_corners 𝕜 F G} : model_with_corners.to_local_equiv (model_with_corners.prod I J) =
  local_equiv.prod (model_with_corners.to_local_equiv I) (model_with_corners.to_local_equiv J) := sorry

@[simp] theorem model_with_corners_prod_coe {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {H : Type u_6} [topological_space H] {H' : Type u_7} [topological_space H'] (I : model_with_corners 𝕜 E H) (I' : model_with_corners 𝕜 E' H') : ⇑(model_with_corners.prod I I') = prod.map ⇑I ⇑I' :=
  rfl

@[simp] theorem model_with_corners_prod_coe_symm {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {H : Type u_6} [topological_space H] {H' : Type u_7} [topological_space H'] (I : model_with_corners 𝕜 E H) (I' : model_with_corners 𝕜 E' H') : ⇑(model_with_corners.symm (model_with_corners.prod I I')) =
  prod.map ⇑(model_with_corners.symm I) ⇑(model_with_corners.symm I') :=
  rfl

/-- Property ensuring that the model with corners `I` defines manifolds without boundary. -/
class model_with_corners.boundaryless {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) 
where
  range_eq_univ : set.range ⇑I = set.univ

/-- The trivial model with corners has no boundary -/
protected instance model_with_corners_self_boundaryless (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] (E : Type u_2) [normed_group E] [normed_space 𝕜 E] : model_with_corners.boundaryless (model_with_corners_self 𝕜 E) :=
  model_with_corners.boundaryless.mk
    (eq.mpr
      (id
        (Eq.trans
          ((fun (a a_1 : set E) (e_1 : a = a_1) (ᾰ ᾰ_1 : set E) (e_2 : ᾰ = ᾰ_1) => congr (congr_arg Eq e_1) e_2)
            (set.range ⇑(model_with_corners_self 𝕜 E)) set.univ
            (Eq.trans
              ((fun (f f_1 : E → E) (e_1 : f = f_1) => congr_arg set.range e_1) (⇑(model_with_corners_self 𝕜 E)) id
                (model_with_corners_self_coe 𝕜 E))
              set.range_id)
            set.univ set.univ (Eq.refl set.univ))
          (propext (eq_self_iff_true set.univ))))
      trivial)

/-- If two model with corners are boundaryless, their product also is -/
protected instance model_with_corners.range_eq_univ_prod {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {E : Type v} [normed_group E] [normed_space 𝕜 E] {H : Type w} [topological_space H] (I : model_with_corners 𝕜 E H) [model_with_corners.boundaryless I] {E' : Type v'} [normed_group E'] [normed_space 𝕜 E'] {H' : Type w'} [topological_space H'] (I' : model_with_corners 𝕜 E' H') [model_with_corners.boundaryless I'] : model_with_corners.boundaryless (model_with_corners.prod I I') :=
  model_with_corners.boundaryless.mk
    (id
      (eq.mpr
        (id
          (Eq._oldrec
            (Eq.refl ((set.range fun (p : H × H') => (coe_fn I (prod.fst p), coe_fn I' (prod.snd p))) = set.univ))
            (Eq.symm set.prod_range_range_eq)))
        (eq.mpr
          (id
            (Eq._oldrec (Eq.refl (set.prod (set.range ⇑I) (set.range ⇑I') = set.univ))
              model_with_corners.boundaryless.range_eq_univ))
          (eq.mpr
            (id
              (Eq._oldrec (Eq.refl (set.prod set.univ (set.range ⇑I') = set.univ))
                model_with_corners.boundaryless.range_eq_univ))
            (eq.mpr (id (Eq._oldrec (Eq.refl (set.prod set.univ set.univ = set.univ)) set.univ_prod_univ))
              (Eq.refl set.univ))))))

/-! ### Smooth functions on models with corners -/

/-- Given a model with corners `(E, H)`, we define the groupoid of `C^n` transformations of `H` as
the maps that are `C^n` when read in `E` through `I`. -/
def times_cont_diff_groupoid (n : with_top ℕ) {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) : structure_groupoid H :=
  pregroupoid.groupoid
    (pregroupoid.mk
      (fun (f : H → H) (s : set H) =>
        times_cont_diff_on 𝕜 n (⇑I ∘ f ∘ ⇑(model_with_corners.symm I))
          (⇑(model_with_corners.symm I) ⁻¹' s ∩ set.range ⇑I))
      sorry sorry sorry sorry)

/-- Inclusion of the groupoid of `C^n` local diffeos in the groupoid of `C^m` local diffeos when
`m ≤ n` -/
theorem times_cont_diff_groupoid_le {m : with_top ℕ} {n : with_top ℕ} {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) (h : m ≤ n) : times_cont_diff_groupoid n I ≤ times_cont_diff_groupoid m I := sorry

/-- The groupoid of `0`-times continuously differentiable maps is just the groupoid of all
local homeomorphisms -/
theorem times_cont_diff_groupoid_zero_eq {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) : times_cont_diff_groupoid 0 I = continuous_groupoid H := sorry

/-- An identity local homeomorphism belongs to the `C^n` groupoid. -/
theorem of_set_mem_times_cont_diff_groupoid (n : with_top ℕ) {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {s : set H} (hs : is_open s) : local_homeomorph.of_set s hs ∈ times_cont_diff_groupoid n I := sorry

/-- The composition of a local homeomorphism from `H` to `M` and its inverse belongs to
the `C^n` groupoid. -/
theorem symm_trans_mem_times_cont_diff_groupoid (n : with_top ℕ) {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] (e : local_homeomorph M H) : local_homeomorph.trans (local_homeomorph.symm e) e ∈ times_cont_diff_groupoid n I :=
  structure_groupoid.eq_on_source (times_cont_diff_groupoid n I)
    (of_set_mem_times_cont_diff_groupoid n I (local_homeomorph.open_target e)) (local_homeomorph.trans_symm_self e)

/-- The product of two smooth local homeomorphisms is smooth. -/
theorem times_cont_diff_groupoid_prod {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I : model_with_corners 𝕜 E H} {I' : model_with_corners 𝕜 E' H'} {e : local_homeomorph H H} {e' : local_homeomorph H' H'} (he : e ∈ times_cont_diff_groupoid ⊤ I) (he' : e' ∈ times_cont_diff_groupoid ⊤ I') : local_homeomorph.prod e e' ∈ times_cont_diff_groupoid ⊤ (model_with_corners.prod I I') := sorry

/-- The `C^n` groupoid is closed under restriction. -/
protected instance times_cont_diff_groupoid.closed_under_restriction (n : with_top ℕ) {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) : closed_under_restriction (times_cont_diff_groupoid n I) :=
  iff.mpr (closed_under_restriction_iff_id_le (times_cont_diff_groupoid n I))
    (iff.mpr structure_groupoid.le_iff
      fun (e : local_homeomorph H H) (ᾰ : e ∈ id_restr_groupoid) =>
        Exists.dcases_on ᾰ
          fun (s : set H) (ᾰ_h : ∃ (h : is_open s), e ≈ local_homeomorph.of_set s h) =>
            Exists.dcases_on ᾰ_h
              fun (hs : is_open s) (hes : e ≈ local_homeomorph.of_set s hs) =>
                structure_groupoid.eq_on_source' (times_cont_diff_groupoid n I) (local_homeomorph.of_set s hs) e
                  (of_set_mem_times_cont_diff_groupoid n I hs) hes)

/-! ### Smooth manifolds with corners -/

/-- Typeclass defining smooth manifolds with corners with respect to a model with corners, over a
field `𝕜` and with infinite smoothness to simplify typeclass search and statements later on. -/
class smooth_manifold_with_corners {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) (M : Type u_4) [topological_space M] [charted_space H M] 
extends has_groupoid M (times_cont_diff_groupoid ⊤ I)
where

theorem smooth_manifold_with_corners_of_times_cont_diff_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) (M : Type u_4) [topological_space M] [charted_space H M] (h : ∀ (e e' : local_homeomorph M H),
  e ∈ charted_space.atlas H M →
    e' ∈ charted_space.atlas H M →
      times_cont_diff_on 𝕜 ⊤
        (⇑I ∘ ⇑(local_homeomorph.trans (local_homeomorph.symm e) e') ∘ ⇑(model_with_corners.symm I))
        (⇑(model_with_corners.symm I) ⁻¹'
            local_equiv.source (local_homeomorph.to_local_equiv (local_homeomorph.trans (local_homeomorph.symm e) e')) ∩
          set.range ⇑I)) : smooth_manifold_with_corners I M :=
  smooth_manifold_with_corners.mk (structure_groupoid.compatible (times_cont_diff_groupoid ⊤ I))

/-- For any model with corners, the model space is a smooth manifold -/
protected instance model_space_smooth {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} : smooth_manifold_with_corners I H :=
  smooth_manifold_with_corners.mk (has_groupoid.compatible (times_cont_diff_groupoid ⊤ I))

namespace smooth_manifold_with_corners


/- We restate in the namespace `smooth_manifolds_with_corners` some lemmas that hold for general
charted space with a structure groupoid, avoiding the need to specify the groupoid
`times_cont_diff_groupoid ∞ I` explicitly. -/

/-- The maximal atlas of `M` for the smooth manifold with corners structure corresponding to the
model with corners `I`. -/
def maximal_atlas {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) (M : Type u_4) [topological_space M] [charted_space H M] : set (local_homeomorph M H) :=
  structure_groupoid.maximal_atlas M (times_cont_diff_groupoid ⊤ I)

theorem mem_maximal_atlas_of_mem_atlas {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {e : local_homeomorph M H} (he : e ∈ charted_space.atlas H M) : e ∈ maximal_atlas I M :=
  structure_groupoid.mem_maximal_atlas_of_mem_atlas (times_cont_diff_groupoid ⊤ I) he

theorem chart_mem_maximal_atlas {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] (x : M) : charted_space.chart_at H x ∈ maximal_atlas I M :=
  structure_groupoid.chart_mem_maximal_atlas (times_cont_diff_groupoid ⊤ I) x

theorem compatible_of_mem_maximal_atlas {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {e : local_homeomorph M H} {e' : local_homeomorph M H} (he : e ∈ maximal_atlas I M) (he' : e' ∈ maximal_atlas I M) : local_homeomorph.trans (local_homeomorph.symm e) e' ∈ times_cont_diff_groupoid ⊤ I :=
  structure_groupoid.compatible_of_mem_maximal_atlas he he'

/-- The product of two smooth manifolds with corners is naturally a smooth manifold with corners. -/
protected instance prod {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {H : Type u_4} [topological_space H] {I : model_with_corners 𝕜 E H} {H' : Type u_5} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} (M : Type u_6) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] (M' : Type u_7) [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] : smooth_manifold_with_corners (model_with_corners.prod I I') (M × M') := sorry

end smooth_manifold_with_corners


/-!
### Extended charts

In a smooth manifold with corners, the model space is the space `H`. However, we will also
need to use extended charts taking values in the model vector space `E`. These extended charts are
not `local_homeomorph` as the target is not open in `E` in general, but we can still register them
as `local_equiv`.
-/

/-- The preferred extended chart on a manifold with corners around a point `x`, from a neighborhood
of `x` to the model vector space. -/
@[simp] def ext_chart_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] (x : M) : local_equiv M E :=
  local_equiv.trans (local_homeomorph.to_local_equiv (charted_space.chart_at H x)) (model_with_corners.to_local_equiv I)

theorem ext_chart_at_source {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] (x : M) : local_equiv.source (ext_chart_at I x) =
  local_equiv.source (local_homeomorph.to_local_equiv (charted_space.chart_at H x)) := sorry

theorem ext_chart_at_open_source {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] (x : M) : is_open (local_equiv.source (ext_chart_at I x)) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_open (local_equiv.source (ext_chart_at I x)))) (ext_chart_at_source I x)))
    (local_homeomorph.open_source (charted_space.chart_at H x))

theorem mem_ext_chart_source {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] (x : M) : x ∈ local_equiv.source (ext_chart_at I x) := sorry

theorem ext_chart_at_to_inv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] (x : M) : coe_fn (local_equiv.symm (ext_chart_at I x)) (coe_fn (ext_chart_at I x) x) = x := sorry

theorem ext_chart_at_source_mem_nhds {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] (x : M) : local_equiv.source (ext_chart_at I x) ∈ nhds x :=
  mem_nhds_sets (ext_chart_at_open_source I x) (mem_ext_chart_source I x)

theorem ext_chart_at_continuous_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] (x : M) : continuous_on (⇑(ext_chart_at I x)) (local_equiv.source (ext_chart_at I x)) := sorry

theorem ext_chart_at_continuous_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] (x : M) : continuous_at (⇑(ext_chart_at I x)) x :=
  continuous_within_at.continuous_at (ext_chart_at_continuous_on I x x (mem_ext_chart_source I x))
    (ext_chart_at_source_mem_nhds I x)

theorem ext_chart_at_continuous_on_symm {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] (x : M) : continuous_on (⇑(local_equiv.symm (ext_chart_at I x))) (local_equiv.target (ext_chart_at I x)) := sorry

theorem ext_chart_at_target_mem_nhds_within {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] (x : M) : local_equiv.target (ext_chart_at I x) ∈ nhds_within (coe_fn (ext_chart_at I x) x) (set.range ⇑I) := sorry

theorem ext_chart_at_coe {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] (x : M) (p : M) : coe_fn (ext_chart_at I x) p = coe_fn I (coe_fn (charted_space.chart_at H x) p) :=
  rfl

theorem ext_chart_at_coe_symm {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] (x : M) (p : E) : coe_fn (local_equiv.symm (ext_chart_at I x)) p =
  coe_fn (local_homeomorph.symm (charted_space.chart_at H x)) (coe_fn (model_with_corners.symm I) p) :=
  rfl

theorem nhds_within_ext_chart_target_eq {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] (x : M) : nhds_within (coe_fn (ext_chart_at I x) x) (local_equiv.target (ext_chart_at I x)) =
  nhds_within (coe_fn (ext_chart_at I x) x) (set.range ⇑I) := sorry

theorem ext_chart_continuous_at_symm' {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] (x : M) {x' : M} (h : x' ∈ local_equiv.source (ext_chart_at I x)) : continuous_at (⇑(local_equiv.symm (ext_chart_at I x))) (coe_fn (ext_chart_at I x) x') := sorry

theorem ext_chart_continuous_at_symm {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] (x : M) : continuous_at (⇑(local_equiv.symm (ext_chart_at I x))) (coe_fn (ext_chart_at I x) x) :=
  ext_chart_continuous_at_symm' I x (mem_ext_chart_source I x)

/-- Technical lemma ensuring that the preimage under an extended chart of a neighborhood of a point
in the source is a neighborhood of the preimage, within a set. -/
theorem ext_chart_preimage_mem_nhds_within' {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] (x : M) {s : set M} {t : set M} {x' : M} (h : x' ∈ local_equiv.source (ext_chart_at I x)) (ht : t ∈ nhds_within x' s) : ⇑(local_equiv.symm (ext_chart_at I x)) ⁻¹' t ∈
  nhds_within (coe_fn (ext_chart_at I x) x') (⇑(local_equiv.symm (ext_chart_at I x)) ⁻¹' s ∩ set.range ⇑I) := sorry

/-- Technical lemma ensuring that the preimage under an extended chart of a neighborhood of the
base point is a neighborhood of the preimage, within a set. -/
theorem ext_chart_preimage_mem_nhds_within {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] (x : M) {s : set M} {t : set M} (ht : t ∈ nhds_within x s) : ⇑(local_equiv.symm (ext_chart_at I x)) ⁻¹' t ∈
  nhds_within (coe_fn (ext_chart_at I x) x) (⇑(local_equiv.symm (ext_chart_at I x)) ⁻¹' s ∩ set.range ⇑I) :=
  ext_chart_preimage_mem_nhds_within' I x (mem_ext_chart_source I x) ht

/-- Technical lemma ensuring that the preimage under an extended chart of a neighborhood of a point
is a neighborhood of the preimage. -/
theorem ext_chart_preimage_mem_nhds {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] (x : M) {t : set M} (ht : t ∈ nhds x) : ⇑(local_equiv.symm (ext_chart_at I x)) ⁻¹' t ∈ nhds (coe_fn (ext_chart_at I x) x) := sorry

/-- Technical lemma to rewrite suitably the preimage of an intersection under an extended chart, to
bring it into a convenient form to apply derivative lemmas. -/
theorem ext_chart_preimage_inter_eq {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] (x : M) {s : set M} {t : set M} : ⇑(local_equiv.symm (ext_chart_at I x)) ⁻¹' (s ∩ t) ∩ set.range ⇑I =
  ⇑(local_equiv.symm (ext_chart_at I x)) ⁻¹' s ∩ set.range ⇑I ∩ ⇑(local_equiv.symm (ext_chart_at I x)) ⁻¹' t := sorry

/-- In the case of the manifold structure on a vector space, the extended charts are just the
identity.-/
theorem ext_chart_model_space_eq_id (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] (x : E) : ext_chart_at (model_with_corners_self 𝕜 E) x = local_equiv.refl E := sorry

