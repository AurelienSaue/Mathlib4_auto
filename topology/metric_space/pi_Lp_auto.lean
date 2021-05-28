/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.analysis.mean_inequalities
import PostPort

universes u_1 u_2 u_3 

namespace Mathlib

/-!
# `L^p` distance on finite products of metric spaces
Given finitely many metric spaces, one can put the max distance on their product, but there is also
a whole family of natural distances, indexed by a real parameter `p ∈ [1, ∞)`, that also induce
the product topology. We define them in this file. The distance on `Π i, α i` is given by
$$
d(x, y) = \left(\sum d(x_i, y_i)^p\right)^{1/p}.
$$

We give instances of this construction for emetric spaces, metric spaces, normed groups and normed
spaces.

To avoid conflicting instances, all these are defined on a copy of the original Pi type, named
`pi_Lp p hp α`, where `hp : 1 ≤ p`. This assumption is included in the definition of the type
to make sure that it is always available to typeclass inference to construct the instances.

We ensure that the topology and uniform structure on `pi_Lp p hp α` are (defeq to) the product
topology and product uniformity, to be able to use freely continuity statements for the coordinate
functions, for instance.

## Implementation notes

We only deal with the `L^p` distance on a product of finitely many metric spaces, which may be
distinct. A closely related construction is the `L^p` norm on the space of
functions from a measure space to a normed space, where the norm is
$$
\left(\int ∥f (x)∥^p dμ\right)^{1/p}.
$$
However, the topology induced by this construction is not the product topology, this only
defines a seminorm (as almost everywhere zero functions have zero `L^p` norm), and some functions
have infinite `L^p` norm. All these subtleties are not present in the case of finitely many
metric spaces (which corresponds to the basis which is a finite space with the counting measure),
hence it is worth devoting a file to this specific case which is particularly well behaved.
The general case is not yet formalized in mathlib.

To prove that the topology (and the uniform structure) on a finite product with the `L^p` distance
are the same as those coming from the `L^∞` distance, we could argue that the `L^p` and `L^∞` norms
are equivalent on `ℝ^n` for abstract (norm equivalence) reasons. Instead, we give a more explicit
(easy) proof which provides a comparison between these two norms with explicit constants.
-/

/-- A copy of a Pi type, on which we will put the `L^p` distance. Since the Pi type itself is
already endowed with the `L^∞` distance, we need the type synonym to avoid confusing typeclass
resolution. Also, we let it depend on `p`, to get a whole family of type on which we can put
different distances, and we provide the assumption `hp` in the definition, to make it available
to typeclass resolution when it looks for a distance on `pi_Lp p hp α`. -/
def pi_Lp {ι : Type u_1} (p : ℝ) (hp : 1 ≤ p) (α : ι → Type u_2)  :=
  (i : ι) → α i

protected instance pi_Lp.inhabited {ι : Type u_1} (p : ℝ) (hp : 1 ≤ p) (α : ι → Type u_2) [(i : ι) → Inhabited (α i)] : Inhabited (pi_Lp p hp α) :=
  { default := fun (i : ι) => Inhabited.default }

namespace pi_Lp


/-- Canonical bijection between `pi_Lp p hp α` and the original Pi type. We introduce it to be able
to compare the `L^p` and `L^∞` distances through it. -/
protected def equiv {ι : Type u_1} (p : ℝ) (hp : 1 ≤ p) (α : ι → Type u_2) : pi_Lp p hp α ≃ ((i : ι) → α i) :=
  equiv.refl (pi_Lp p hp α)

/-!
### The uniformity on finite `L^p` products is the product uniformity

In this section, we put the `L^p` edistance on `pi_Lp p hp α`, and we check that the uniformity
coming from this edistance coincides with the product uniformity, by showing that the canonical
map to the Pi type (with the `L^∞` distance) is a uniform embedding, as it is both Lipschitz and
antiLipschitz.

We only register this emetric space structure as a temporary instance, as the true instance (to be
registered later) will have as uniformity exactly the product uniformity, instead of the one coming
from the edistance (which is equal to it, but not defeq). See Note [forgetful inheritance]
explaining why having definitionally the right uniformity is often important.
-/

/-- Endowing the space `pi_Lp p hp α` with the `L^p` edistance. This definition is not satisfactory,
as it does not register the fact that the topology and the uniform structure coincide with the
product one. Therefore, we do not register it as an instance. Using this as a temporary emetric
space instance, we will show that the uniform structure is equal (but not defeq) to the product one,
and then register an instance in which we replace the uniform structure by the product one using
this emetric space and `emetric_space.replace_uniformity`. -/
def emetric_aux {ι : Type u_1} (p : ℝ) (hp : 1 ≤ p) (α : ι → Type u_2) [(i : ι) → emetric_space (α i)] [fintype ι] : emetric_space (pi_Lp p hp α) :=
  (fun (pos : 0 < p) =>
      emetric_space.mk sorry sorry sorry sorry
        (uniform_space_of_edist
          (fun (f g : pi_Lp p hp α) => (finset.sum finset.univ fun (i : ι) => edist (f i) (g i) ^ p) ^ (1 / p)) sorry
          sorry sorry))
    sorry

theorem lipschitz_with_equiv {ι : Type u_1} (p : ℝ) (hp : 1 ≤ p) (α : ι → Type u_2) [(i : ι) → emetric_space (α i)] [fintype ι] : lipschitz_with 1 ⇑(pi_Lp.equiv p hp α) := sorry

theorem antilipschitz_with_equiv {ι : Type u_1} (p : ℝ) (hp : 1 ≤ p) (α : ι → Type u_2) [(i : ι) → emetric_space (α i)] [fintype ι] : antilipschitz_with (↑(fintype.card ι) ^ (1 / p)) ⇑(pi_Lp.equiv p hp α) := sorry

theorem aux_uniformity_eq {ι : Type u_1} (p : ℝ) (hp : 1 ≤ p) (α : ι → Type u_2) [(i : ι) → emetric_space (α i)] [fintype ι] : uniformity (pi_Lp p hp α) = uniformity ((i : ι) → α i) := sorry

/-! ### Instances on finite `L^p` products -/

protected instance uniform_space {ι : Type u_1} (p : ℝ) (hp : 1 ≤ p) (α : ι → Type u_2) [(i : ι) → uniform_space (α i)] : uniform_space (pi_Lp p hp α) :=
  Pi.uniform_space fun (i : ι) => α i

/-- emetric space instance on the product of finitely many emetric spaces, using the `L^p`
edistance, and having as uniformity the product uniformity. -/
protected instance emetric_space {ι : Type u_1} (p : ℝ) (hp : 1 ≤ p) (α : ι → Type u_2) [fintype ι] [(i : ι) → emetric_space (α i)] : emetric_space (pi_Lp p hp α) :=
  emetric_space.replace_uniformity (emetric_aux p hp α) sorry

protected theorem edist {ι : Type u_1} [fintype ι] {p : ℝ} {hp : 1 ≤ p} {α : ι → Type u_2} [(i : ι) → emetric_space (α i)] (x : pi_Lp p hp α) (y : pi_Lp p hp α) : edist x y = (finset.sum finset.univ fun (i : ι) => edist (x i) (y i) ^ p) ^ (1 / p) :=
  rfl

/-- metric space instance on the product of finitely many metric spaces, using the `L^p` distance,
and having as uniformity the product uniformity. -/
protected instance metric_space {ι : Type u_1} (p : ℝ) (hp : 1 ≤ p) (α : ι → Type u_2) [fintype ι] [(i : ι) → metric_space (α i)] : metric_space (pi_Lp p hp α) :=
  emetric_space.to_metric_space_of_dist
    (fun (f g : pi_Lp p hp α) => (finset.sum finset.univ fun (i : ι) => dist (f i) (g i) ^ p) ^ (1 / p)) sorry sorry

protected theorem dist {ι : Type u_1} [fintype ι] {p : ℝ} {hp : 1 ≤ p} {α : ι → Type u_2} [(i : ι) → metric_space (α i)] (x : pi_Lp p hp α) (y : pi_Lp p hp α) : dist x y = (finset.sum finset.univ fun (i : ι) => dist (x i) (y i) ^ p) ^ (1 / p) :=
  rfl

/-- normed group instance on the product of finitely many normed groups, using the `L^p` norm. -/
protected instance normed_group {ι : Type u_1} (p : ℝ) (hp : 1 ≤ p) (α : ι → Type u_2) [fintype ι] [(i : ι) → normed_group (α i)] : normed_group (pi_Lp p hp α) :=
  normed_group.mk sorry

theorem norm_eq {ι : Type u_1} [fintype ι] {p : ℝ} {hp : 1 ≤ p} {α : ι → Type u_2} [(i : ι) → normed_group (α i)] (f : pi_Lp p hp α) : norm f = (finset.sum finset.univ fun (i : ι) => norm (f i) ^ p) ^ (1 / p) :=
  rfl

/-- The product of finitely many normed spaces is a normed space, with the `L^p` norm. -/
protected instance normed_space {ι : Type u_1} (p : ℝ) (hp : 1 ≤ p) (α : ι → Type u_2) [fintype ι] (𝕜 : Type u_3) [normed_field 𝕜] [(i : ι) → normed_group (α i)] [(i : ι) → normed_space 𝕜 (α i)] : normed_space 𝕜 (pi_Lp p hp α) :=
  normed_space.mk sorry

/- Register simplification lemmas for the applications of `pi_Lp` elements, as the usual lemmas
for Pi types will not trigger. -/

@[simp] theorem add_apply {ι : Type u_1} {p : ℝ} {hp : 1 ≤ p} {α : ι → Type u_2} [fintype ι] [(i : ι) → normed_group (α i)] (x : pi_Lp p hp α) (y : pi_Lp p hp α) (i : ι) : Add.add x y i = x i + y i :=
  rfl

@[simp] theorem sub_apply {ι : Type u_1} {p : ℝ} {hp : 1 ≤ p} {α : ι → Type u_2} [fintype ι] [(i : ι) → normed_group (α i)] (x : pi_Lp p hp α) (y : pi_Lp p hp α) (i : ι) : Sub.sub x y i = x i - y i :=
  rfl

@[simp] theorem smul_apply {ι : Type u_1} {p : ℝ} {hp : 1 ≤ p} {α : ι → Type u_2} [fintype ι] {𝕜 : Type u_3} [normed_field 𝕜] [(i : ι) → normed_group (α i)] [(i : ι) → normed_space 𝕜 (α i)] (c : 𝕜) (x : pi_Lp p hp α) (i : ι) : has_scalar.smul c x i = c • x i :=
  rfl

@[simp] theorem neg_apply {ι : Type u_1} {p : ℝ} {hp : 1 ≤ p} {α : ι → Type u_2} [fintype ι] [(i : ι) → normed_group (α i)] (x : pi_Lp p hp α) (i : ι) : Neg.neg x i = -x i :=
  rfl

