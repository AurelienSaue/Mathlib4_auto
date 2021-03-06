/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes HΓΆlzl

Continuous linear functions -- functions between normed vector spaces which are bounded and linear.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.analysis.normed_space.multilinear
import Mathlib.PostPort

universes u_5 u_6 u_7 l u_1 u_2 u_3 u_4 

namespace Mathlib

/-- A function `f` satisfies `is_bounded_linear_map π f` if it is linear and satisfies the
inequality `β₯ f x β₯ β€ M * β₯ x β₯` for some positive constant `M`. -/
structure is_bounded_linear_map (π : Type u_5) [normed_field π] {E : Type u_6} [normed_group E]
    [normed_space π E] {F : Type u_7} [normed_group F] [normed_space π F] (f : E β F)
    extends is_linear_map π f where
  bound : β (M : β), 0 < M β§ β (x : E), norm (f x) β€ M * norm x

theorem is_linear_map.with_bound {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2}
    [normed_group E] [normed_space π E] {F : Type u_3} [normed_group F] [normed_space π F]
    {f : E β F} (hf : is_linear_map π f) (M : β) (h : β (x : E), norm (f x) β€ M * norm x) :
    is_bounded_linear_map π f :=
  sorry

/-- A continuous linear map satisfies `is_bounded_linear_map` -/
theorem continuous_linear_map.is_bounded_linear_map {π : Type u_1} [nondiscrete_normed_field π]
    {E : Type u_2} [normed_group E] [normed_space π E] {F : Type u_3} [normed_group F]
    [normed_space π F] (f : continuous_linear_map π E F) : is_bounded_linear_map π βf :=
  sorry

namespace is_bounded_linear_map


/-- Construct a linear map from a function `f` satisfying `is_bounded_linear_map π f`. -/
def to_linear_map {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E]
    [normed_space π E] {F : Type u_3} [normed_group F] [normed_space π F] (f : E β F)
    (h : is_bounded_linear_map π f) : linear_map π E F :=
  is_linear_map.mk' f sorry

/-- Construct a continuous linear map from is_bounded_linear_map -/
def to_continuous_linear_map {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2}
    [normed_group E] [normed_space π E] {F : Type u_3} [normed_group F] [normed_space π F]
    {f : E β F} (hf : is_bounded_linear_map π f) : continuous_linear_map π E F :=
  continuous_linear_map.mk (linear_map.mk (linear_map.to_fun (to_linear_map f hf)) sorry sorry)

theorem zero {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E]
    [normed_space π E] {F : Type u_3} [normed_group F] [normed_space π F] :
    is_bounded_linear_map π fun (x : E) => 0 :=
  sorry

theorem id {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E]
    [normed_space π E] : is_bounded_linear_map π fun (x : E) => x :=
  sorry

theorem fst {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E]
    [normed_space π E] {F : Type u_3} [normed_group F] [normed_space π F] :
    is_bounded_linear_map π fun (x : E Γ F) => prod.fst x :=
  sorry

theorem snd {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E]
    [normed_space π E] {F : Type u_3} [normed_group F] [normed_space π F] :
    is_bounded_linear_map π fun (x : E Γ F) => prod.snd x :=
  sorry

theorem smul {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E]
    [normed_space π E] {F : Type u_3} [normed_group F] [normed_space π F] {f : E β F} (c : π)
    (hf : is_bounded_linear_map π f) : is_bounded_linear_map π fun (e : E) => c β’ f e :=
  sorry

theorem neg {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E]
    [normed_space π E] {F : Type u_3} [normed_group F] [normed_space π F] {f : E β F}
    (hf : is_bounded_linear_map π f) : is_bounded_linear_map π fun (e : E) => -f e :=
  sorry

theorem add {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E]
    [normed_space π E] {F : Type u_3} [normed_group F] [normed_space π F] {f : E β F} {g : E β F}
    (hf : is_bounded_linear_map π f) (hg : is_bounded_linear_map π g) :
    is_bounded_linear_map π fun (e : E) => f e + g e :=
  sorry

theorem sub {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E]
    [normed_space π E] {F : Type u_3} [normed_group F] [normed_space π F] {f : E β F} {g : E β F}
    (hf : is_bounded_linear_map π f) (hg : is_bounded_linear_map π g) :
    is_bounded_linear_map π fun (e : E) => f e - g e :=
  sorry

theorem comp {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E]
    [normed_space π E] {F : Type u_3} [normed_group F] [normed_space π F] {G : Type u_4}
    [normed_group G] [normed_space π G] {f : E β F} {g : F β G} (hg : is_bounded_linear_map π g)
    (hf : is_bounded_linear_map π f) : is_bounded_linear_map π (g β f) :=
  continuous_linear_map.is_bounded_linear_map
    (continuous_linear_map.comp (to_continuous_linear_map hg) (to_continuous_linear_map hf))

protected theorem tendsto {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2}
    [normed_group E] [normed_space π E] {F : Type u_3} [normed_group F] [normed_space π F]
    {f : E β F} (x : E) (hf : is_bounded_linear_map π f) : filter.tendsto f (nhds x) (nhds (f x)) :=
  sorry

theorem continuous {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E]
    [normed_space π E] {F : Type u_3} [normed_group F] [normed_space π F] {f : E β F}
    (hf : is_bounded_linear_map π f) : continuous f :=
  iff.mpr continuous_iff_continuous_at fun (_x : E) => is_bounded_linear_map.tendsto _x hf

theorem lim_zero_bounded_linear_map {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2}
    [normed_group E] [normed_space π E] {F : Type u_3} [normed_group F] [normed_space π F]
    {f : E β F} (hf : is_bounded_linear_map π f) : filter.tendsto f (nhds 0) (nhds 0) :=
  linear_map.map_zero (is_linear_map.mk' f (to_is_linear_map hf)) βΈ
    iff.mp continuous_iff_continuous_at (continuous hf) 0

theorem is_O_id {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E]
    [normed_space π E] {F : Type u_3} [normed_group F] [normed_space π F] {f : E β F}
    (h : is_bounded_linear_map π f) (l : filter E) : asymptotics.is_O f (fun (x : E) => x) l :=
  sorry

theorem is_O_comp {π : Type u_1} [nondiscrete_normed_field π] {F : Type u_3} [normed_group F]
    [normed_space π F] {G : Type u_4} [normed_group G] [normed_space π G] {E : Type u_2} {g : F β G}
    (hg : is_bounded_linear_map π g) {f : E β F} (l : filter E) :
    asymptotics.is_O (fun (x' : E) => g (f x')) f l :=
  asymptotics.is_O.comp_tendsto (is_O_id hg β€) le_top

theorem is_O_sub {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E]
    [normed_space π E] {F : Type u_3} [normed_group F] [normed_space π F] {f : E β F}
    (h : is_bounded_linear_map π f) (l : filter E) (x : E) :
    asymptotics.is_O (fun (x' : E) => f (x' - x)) (fun (x' : E) => x' - x) l :=
  is_O_comp h l

end is_bounded_linear_map


/-- Taking the cartesian product of two continuous linear maps is a bounded linear operation. -/
theorem is_bounded_linear_map_prod_iso {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2}
    [normed_group E] [normed_space π E] {F : Type u_3} [normed_group F] [normed_space π F]
    {G : Type u_4} [normed_group G] [normed_space π G] :
    is_bounded_linear_map π
        fun (p : continuous_linear_map π E F Γ continuous_linear_map π E G) =>
          continuous_linear_map.prod (prod.fst p) (prod.snd p) :=
  sorry

/-- Taking the cartesian product of two continuous multilinear maps is a bounded linear operation. -/
theorem is_bounded_linear_map_prod_multilinear {π : Type u_1} [nondiscrete_normed_field π]
    {F : Type u_3} [normed_group F] [normed_space π F] {G : Type u_4} [normed_group G]
    [normed_space π G] {ΞΉ : Type u_5} [DecidableEq ΞΉ] [fintype ΞΉ] {E : ΞΉ β Type u_2}
    [(i : ΞΉ) β normed_group (E i)] [(i : ΞΉ) β normed_space π (E i)] :
    is_bounded_linear_map π
        fun (p : continuous_multilinear_map π E F Γ continuous_multilinear_map π E G) =>
          continuous_multilinear_map.prod (prod.fst p) (prod.snd p) :=
  sorry

/-- Given a fixed continuous linear map `g`, associating to a continuous multilinear map `f` the
continuous multilinear map `f (g mβ, ..., g mβ)` is a bounded linear operation. -/
theorem is_bounded_linear_map_continuous_multilinear_map_comp_linear {π : Type u_1}
    [nondiscrete_normed_field π] {E : Type u_2} [normed_group E] [normed_space π E] {F : Type u_3}
    [normed_group F] [normed_space π F] {G : Type u_4} [normed_group G] [normed_space π G]
    {ΞΉ : Type u_5} [DecidableEq ΞΉ] [fintype ΞΉ] (g : continuous_linear_map π G E) :
    is_bounded_linear_map π
        fun (f : continuous_multilinear_map π (fun (i : ΞΉ) => E) F) =>
          continuous_multilinear_map.comp_continuous_linear_map f fun (_x : ΞΉ) => g :=
  sorry

/-- A map `f : E Γ F β G` satisfies `is_bounded_bilinear_map π f` if it is bilinear and
continuous. -/
structure is_bounded_bilinear_map (π : Type u_1) [nondiscrete_normed_field π] {E : Type u_2}
    [normed_group E] [normed_space π E] {F : Type u_3} [normed_group F] [normed_space π F]
    {G : Type u_4} [normed_group G] [normed_space π G] (f : E Γ F β G)
    where
  add_left : β (xβ xβ : E) (y : F), f (xβ + xβ, y) = f (xβ, y) + f (xβ, y)
  smul_left : β (c : π) (x : E) (y : F), f (c β’ x, y) = c β’ f (x, y)
  add_right : β (x : E) (yβ yβ : F), f (x, yβ + yβ) = f (x, yβ) + f (x, yβ)
  smul_right : β (c : π) (x : E) (y : F), f (x, c β’ y) = c β’ f (x, y)
  bound : β (C : β), β (H : C > 0), β (x : E) (y : F), norm (f (x, y)) β€ C * norm x * norm y

protected theorem is_bounded_bilinear_map.is_O {π : Type u_1} [nondiscrete_normed_field π]
    {E : Type u_2} [normed_group E] [normed_space π E] {F : Type u_3} [normed_group F]
    [normed_space π F] {G : Type u_4} [normed_group G] [normed_space π G] {f : E Γ F β G}
    (h : is_bounded_bilinear_map π f) :
    asymptotics.is_O f (fun (p : E Γ F) => norm (prod.fst p) * norm (prod.snd p)) β€ :=
  sorry

theorem is_bounded_bilinear_map.is_O_comp {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2}
    [normed_group E] [normed_space π E] {F : Type u_3} [normed_group F] [normed_space π F]
    {G : Type u_4} [normed_group G] [normed_space π G] {f : E Γ F β G} {Ξ± : Type u_5}
    (H : is_bounded_bilinear_map π f) {g : Ξ± β E} {h : Ξ± β F} {l : filter Ξ±} :
    asymptotics.is_O (fun (x : Ξ±) => f (g x, h x)) (fun (x : Ξ±) => norm (g x) * norm (h x)) l :=
  asymptotics.is_O.comp_tendsto (is_bounded_bilinear_map.is_O H) le_top

protected theorem is_bounded_bilinear_map.is_O' {π : Type u_1} [nondiscrete_normed_field π]
    {E : Type u_2} [normed_group E] [normed_space π E] {F : Type u_3} [normed_group F]
    [normed_space π F] {G : Type u_4} [normed_group G] [normed_space π G] {f : E Γ F β G}
    (h : is_bounded_bilinear_map π f) : asymptotics.is_O f (fun (p : E Γ F) => norm p * norm p) β€ :=
  asymptotics.is_O.trans (is_bounded_bilinear_map.is_O h)
    (asymptotics.is_O.mul (asymptotics.is_O.norm_norm asymptotics.is_O_fst_prod')
      (asymptotics.is_O.norm_norm asymptotics.is_O_snd_prod'))

theorem is_bounded_bilinear_map.map_sub_left {π : Type u_1} [nondiscrete_normed_field π]
    {E : Type u_2} [normed_group E] [normed_space π E] {F : Type u_3} [normed_group F]
    [normed_space π F] {G : Type u_4} [normed_group G] [normed_space π G] {f : E Γ F β G}
    (h : is_bounded_bilinear_map π f) {x : E} {y : E} {z : F} :
    f (x - y, z) = f (x, z) - f (y, z) :=
  sorry

theorem is_bounded_bilinear_map.map_sub_right {π : Type u_1} [nondiscrete_normed_field π]
    {E : Type u_2} [normed_group E] [normed_space π E] {F : Type u_3} [normed_group F]
    [normed_space π F] {G : Type u_4} [normed_group G] [normed_space π G] {f : E Γ F β G}
    (h : is_bounded_bilinear_map π f) {x : E} {y : F} {z : F} :
    f (x, y - z) = f (x, y) - f (x, z) :=
  sorry

theorem is_bounded_bilinear_map.is_bounded_linear_map_left {π : Type u_1}
    [nondiscrete_normed_field π] {E : Type u_2} [normed_group E] [normed_space π E] {F : Type u_3}
    [normed_group F] [normed_space π F] {G : Type u_4} [normed_group G] [normed_space π G]
    {f : E Γ F β G} (h : is_bounded_bilinear_map π f) (y : F) :
    is_bounded_linear_map π fun (x : E) => f (x, y) :=
  sorry

theorem is_bounded_bilinear_map.is_bounded_linear_map_right {π : Type u_1}
    [nondiscrete_normed_field π] {E : Type u_2} [normed_group E] [normed_space π E] {F : Type u_3}
    [normed_group F] [normed_space π F] {G : Type u_4} [normed_group G] [normed_space π G]
    {f : E Γ F β G} (h : is_bounded_bilinear_map π f) (x : E) :
    is_bounded_linear_map π fun (y : F) => f (x, y) :=
  sorry

theorem is_bounded_bilinear_map_smul {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2}
    [normed_group E] [normed_space π E] :
    is_bounded_bilinear_map π fun (p : π Γ E) => prod.fst p β’ prod.snd p :=
  sorry

theorem is_bounded_bilinear_map_smul_algebra {π : Type u_1} [nondiscrete_normed_field π]
    {π' : Type u_2} [normed_field π'] [normed_algebra π π'] {E : Type u_3} [normed_group E]
    [normed_space π E] [normed_space π' E] [is_scalar_tower π π' E] :
    is_bounded_bilinear_map π fun (p : π' Γ E) => prod.fst p β’ prod.snd p :=
  sorry

theorem is_bounded_bilinear_map_mul {π : Type u_1} [nondiscrete_normed_field π] :
    is_bounded_bilinear_map π fun (p : π Γ π) => prod.fst p * prod.snd p :=
  is_bounded_bilinear_map_smul

theorem is_bounded_bilinear_map_comp {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2}
    [normed_group E] [normed_space π E] {F : Type u_3} [normed_group F] [normed_space π F]
    {G : Type u_4} [normed_group G] [normed_space π G] :
    is_bounded_bilinear_map π
        fun (p : continuous_linear_map π E F Γ continuous_linear_map π F G) =>
          continuous_linear_map.comp (prod.snd p) (prod.fst p) :=
  sorry

theorem continuous_linear_map.is_bounded_linear_map_comp_left {π : Type u_1}
    [nondiscrete_normed_field π] {E : Type u_2} [normed_group E] [normed_space π E] {F : Type u_3}
    [normed_group F] [normed_space π F] {G : Type u_4} [normed_group G] [normed_space π G]
    (g : continuous_linear_map π F G) :
    is_bounded_linear_map π
        fun (f : continuous_linear_map π E F) => continuous_linear_map.comp g f :=
  is_bounded_bilinear_map.is_bounded_linear_map_left is_bounded_bilinear_map_comp g

theorem continuous_linear_map.is_bounded_linear_map_comp_right {π : Type u_1}
    [nondiscrete_normed_field π] {E : Type u_2} [normed_group E] [normed_space π E] {F : Type u_3}
    [normed_group F] [normed_space π F] {G : Type u_4} [normed_group G] [normed_space π G]
    (f : continuous_linear_map π E F) :
    is_bounded_linear_map π
        fun (g : continuous_linear_map π F G) => continuous_linear_map.comp g f :=
  is_bounded_bilinear_map.is_bounded_linear_map_right is_bounded_bilinear_map_comp f

theorem is_bounded_bilinear_map_apply {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2}
    [normed_group E] [normed_space π E] {F : Type u_3} [normed_group F] [normed_space π F] :
    is_bounded_bilinear_map π
        fun (p : continuous_linear_map π E F Γ E) => coe_fn (prod.fst p) (prod.snd p) :=
  sorry

/-- The function `continuous_linear_map.smul_right`, associating to a continuous linear map
`f : E β π` and a scalar `c : F` the tensor product `f β c` as a continuous linear map from `E` to
`F`, is a bounded bilinear map. -/
theorem is_bounded_bilinear_map_smul_right {π : Type u_1} [nondiscrete_normed_field π]
    {E : Type u_2} [normed_group E] [normed_space π E] {F : Type u_3} [normed_group F]
    [normed_space π F] :
    is_bounded_bilinear_map π
        fun (p : continuous_linear_map π E π Γ F) =>
          continuous_linear_map.smul_right (prod.fst p) (prod.snd p) :=
  sorry

/-- The composition of a continuous linear map with a continuous multilinear map is a bounded
bilinear operation. -/
theorem is_bounded_bilinear_map_comp_multilinear {π : Type u_1} [nondiscrete_normed_field π]
    {F : Type u_3} [normed_group F] [normed_space π F] {G : Type u_4} [normed_group G]
    [normed_space π G] {ΞΉ : Type u_2} {E : ΞΉ β Type u_5} [DecidableEq ΞΉ] [fintype ΞΉ]
    [(i : ΞΉ) β normed_group (E i)] [(i : ΞΉ) β normed_space π (E i)] :
    is_bounded_bilinear_map π
        fun (p : continuous_linear_map π F G Γ continuous_multilinear_map π E F) =>
          continuous_linear_map.comp_continuous_multilinear_map (prod.fst p) (prod.snd p) :=
  sorry

/-- Definition of the derivative of a bilinear map `f`, given at a point `p` by
`q β¦ f(p.1, q.2) + f(q.1, p.2)` as in the standard formula for the derivative of a product.
We define this function here a bounded linear map from `E Γ F` to `G`. The fact that this
is indeed the derivative of `f` is proved in `is_bounded_bilinear_map.has_fderiv_at` in
`fderiv.lean`-/
def is_bounded_bilinear_map.linear_deriv {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2}
    [normed_group E] [normed_space π E] {F : Type u_3} [normed_group F] [normed_space π F]
    {G : Type u_4} [normed_group G] [normed_space π G] {f : E Γ F β G}
    (h : is_bounded_bilinear_map π f) (p : E Γ F) : linear_map π (E Γ F) G :=
  linear_map.mk (fun (q : E Γ F) => f (prod.fst p, prod.snd q) + f (prod.fst q, prod.snd p)) sorry
    sorry

/-- The derivative of a bounded bilinear map at a point `p : E Γ F`, as a continuous linear map
from `E Γ F` to `G`. -/
def is_bounded_bilinear_map.deriv {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2}
    [normed_group E] [normed_space π E] {F : Type u_3} [normed_group F] [normed_space π F]
    {G : Type u_4} [normed_group G] [normed_space π G] {f : E Γ F β G}
    (h : is_bounded_bilinear_map π f) (p : E Γ F) : continuous_linear_map π (E Γ F) G :=
  linear_map.mk_continuous_of_exists_bound (is_bounded_bilinear_map.linear_deriv h p) sorry

@[simp] theorem is_bounded_bilinear_map_deriv_coe {π : Type u_1} [nondiscrete_normed_field π]
    {E : Type u_2} [normed_group E] [normed_space π E] {F : Type u_3} [normed_group F]
    [normed_space π F] {G : Type u_4} [normed_group G] [normed_space π G] {f : E Γ F β G}
    (h : is_bounded_bilinear_map π f) (p : E Γ F) (q : E Γ F) :
    coe_fn (is_bounded_bilinear_map.deriv h p) q =
        f (prod.fst p, prod.snd q) + f (prod.fst q, prod.snd p) :=
  rfl

/-- The function `lmul_left_right : π' Γ π' β (π' βL[π] π')` is a bounded bilinear map. -/
theorem continuous_linear_map.lmul_left_right_is_bounded_bilinear (π : Type u_1)
    [nondiscrete_normed_field π] (π' : Type u_2) [normed_ring π'] [normed_algebra π π'] :
    is_bounded_bilinear_map π (continuous_linear_map.lmul_left_right π π') :=
  sorry

/-- Given a bounded bilinear map `f`, the map associating to a point `p` the derivative of `f` at
`p` is itself a bounded linear map. -/
theorem is_bounded_bilinear_map.is_bounded_linear_map_deriv {π : Type u_1}
    [nondiscrete_normed_field π] {E : Type u_2} [normed_group E] [normed_space π E] {F : Type u_3}
    [normed_group F] [normed_space π F] {G : Type u_4} [normed_group G] [normed_space π G]
    {f : E Γ F β G} (h : is_bounded_bilinear_map π f) :
    is_bounded_linear_map π fun (p : E Γ F) => is_bounded_bilinear_map.deriv h p :=
  sorry

/-- A linear isometry preserves the norm. -/
theorem linear_map.norm_apply_of_isometry {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2}
    [normed_group E] [normed_space π E] {F : Type u_3} [normed_group F] [normed_space π F]
    (f : linear_map π E F) {x : E} (hf : isometry βf) : norm (coe_fn f x) = norm x :=
  sorry

/-- Construct a continuous linear equiv from a linear map that is also an isometry with full range. -/
def continuous_linear_equiv.of_isometry {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2}
    [normed_group E] [normed_space π E] {F : Type u_3} [normed_group F] [normed_space π F]
    (f : linear_map π E F) (hf : isometry βf) (hfr : linear_map.range f = β€) :
    continuous_linear_equiv π E F :=
  continuous_linear_equiv.of_homothety π (linear_equiv.of_bijective f sorry hfr) 1 zero_lt_one sorry

end Mathlib