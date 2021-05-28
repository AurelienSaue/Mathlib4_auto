/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury Kudryashov
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.topology.metric_space.isometry
import PostPort

universes u_6 u_7 u_8 l u_1 u_2 u_3 u_4 u_5 

namespace Mathlib

/-!
# Linear isometries

In this file we define `linear_isometry R E F` (notation: `E →ₗᵢ[R] F`) to be a linear isometric
embedding of `E` into `F` and `linear_isometry_equiv` (notation: `E ≃ₗᵢ[R] F`) to be a linear
isometric equivalence between `E` and `F`.

We also prove some trivial lemmas and provide convenience constructors.
-/

/-- An `R`-linear isometric embedding of one normed `R`-module into another. -/
structure linear_isometry (R : Type u_6) (E : Type u_7) (F : Type u_8) [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] 
extends linear_map R E F
where
  norm_map' : ∀ (x : E), norm (coe_fn _to_linear_map x) = norm x

namespace linear_isometry


protected instance has_coe_to_fun {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] : has_coe_to_fun (linear_isometry R E F) :=
  has_coe_to_fun.mk (fun (f : linear_isometry R E F) => E → F)
    fun (f : linear_isometry R E F) => linear_map.to_fun (to_linear_map f)

@[simp] theorem coe_to_linear_map {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (f : linear_isometry R E F) : ⇑(to_linear_map f) = ⇑f :=
  rfl

theorem to_linear_map_injective {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] : function.injective to_linear_map := sorry

theorem coe_fn_injective {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] : function.injective fun (f : linear_isometry R E F) (x : E) => coe_fn f x :=
  function.injective.comp linear_map.coe_injective to_linear_map_injective

theorem ext {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] {f : linear_isometry R E F} {g : linear_isometry R E F} (h : ∀ (x : E), coe_fn f x = coe_fn g x) : f = g :=
  coe_fn_injective (funext h)

@[simp] theorem map_zero {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (f : linear_isometry R E F) : coe_fn f 0 = 0 :=
  linear_map.map_zero (to_linear_map f)

@[simp] theorem map_add {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (f : linear_isometry R E F) (x : E) (y : E) : coe_fn f (x + y) = coe_fn f x + coe_fn f y :=
  linear_map.map_add (to_linear_map f) x y

@[simp] theorem map_sub {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (f : linear_isometry R E F) (x : E) (y : E) : coe_fn f (x - y) = coe_fn f x - coe_fn f y :=
  linear_map.map_sub (to_linear_map f) x y

@[simp] theorem map_smul {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (f : linear_isometry R E F) (c : R) (x : E) : coe_fn f (c • x) = c • coe_fn f x :=
  linear_map.map_smul (to_linear_map f) c x

@[simp] theorem norm_map {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (f : linear_isometry R E F) (x : E) : norm (coe_fn f x) = norm x :=
  norm_map' f x

@[simp] theorem nnnorm_map {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (f : linear_isometry R E F) (x : E) : nnnorm (coe_fn f x) = nnnorm x :=
  nnreal.eq (norm_map f x)

protected theorem isometry {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (f : linear_isometry R E F) : isometry ⇑f :=
  add_monoid_hom.isometry_of_norm (linear_map.to_add_monoid_hom (to_linear_map f)) (norm_map f)

@[simp] theorem dist_map {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (f : linear_isometry R E F) (x : E) (y : E) : dist (coe_fn f x) (coe_fn f y) = dist x y :=
  isometry.dist_eq (linear_isometry.isometry f) x y

@[simp] theorem edist_map {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (f : linear_isometry R E F) (x : E) (y : E) : edist (coe_fn f x) (coe_fn f y) = edist x y :=
  isometry.edist_eq (linear_isometry.isometry f) x y

protected theorem injective {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (f : linear_isometry R E F) : function.injective ⇑f :=
  isometry.injective (linear_isometry.isometry f)

theorem map_eq_iff {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (f : linear_isometry R E F) {x : E} {y : E} : coe_fn f x = coe_fn f y ↔ x = y :=
  function.injective.eq_iff (linear_isometry.injective f)

theorem map_ne {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (f : linear_isometry R E F) {x : E} {y : E} (h : x ≠ y) : coe_fn f x ≠ coe_fn f y :=
  function.injective.ne (linear_isometry.injective f) h

protected theorem lipschitz {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (f : linear_isometry R E F) : lipschitz_with 1 ⇑f :=
  isometry.lipschitz (linear_isometry.isometry f)

protected theorem antilipschitz {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (f : linear_isometry R E F) : antilipschitz_with 1 ⇑f :=
  isometry.antilipschitz (linear_isometry.isometry f)

protected theorem continuous {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (f : linear_isometry R E F) : continuous ⇑f :=
  isometry.continuous (linear_isometry.isometry f)

theorem ediam_image {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (f : linear_isometry R E F) (s : set E) : emetric.diam (⇑f '' s) = emetric.diam s :=
  isometry.ediam_image (linear_isometry.isometry f) s

theorem ediam_range {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (f : linear_isometry R E F) : emetric.diam (set.range ⇑f) = emetric.diam set.univ :=
  isometry.ediam_range (linear_isometry.isometry f)

theorem diam_image {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (f : linear_isometry R E F) (s : set E) : metric.diam (⇑f '' s) = metric.diam s :=
  isometry.diam_image (linear_isometry.isometry f) s

theorem diam_range {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (f : linear_isometry R E F) : metric.diam (set.range ⇑f) = metric.diam set.univ :=
  isometry.diam_range (linear_isometry.isometry f)

/-- Interpret a linear isometry as a continuous linear map. -/
def to_continuous_linear_map {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (f : linear_isometry R E F) : continuous_linear_map R E F :=
  continuous_linear_map.mk (to_linear_map f)

@[simp] theorem coe_to_continuous_linear_map {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (f : linear_isometry R E F) : ⇑(to_continuous_linear_map f) = ⇑f :=
  rfl

@[simp] theorem comp_continuous_iff {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (f : linear_isometry R E F) {α : Type u_4} [topological_space α] {g : α → E} : continuous (⇑f ∘ g) ↔ continuous g := sorry

/-- The identity linear isometry. -/
def id {R : Type u_1} {E : Type u_2} [semiring R] [normed_group E] [semimodule R E] : linear_isometry R E E :=
  mk linear_map.id sorry

@[simp] theorem coe_id {R : Type u_1} {E : Type u_2} [semiring R] [normed_group E] [semimodule R E] : ⇑id = ⇑id :=
  rfl

protected instance inhabited {R : Type u_1} {E : Type u_2} [semiring R] [normed_group E] [semimodule R E] : Inhabited (linear_isometry R E E) :=
  { default := id }

/-- Composition of linear isometries. -/
def comp {R : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} [semiring R] [normed_group E] [normed_group F] [normed_group G] [semimodule R E] [semimodule R F] [semimodule R G] (g : linear_isometry R F G) (f : linear_isometry R E F) : linear_isometry R E G :=
  mk (linear_map.comp (to_linear_map g) (to_linear_map f)) sorry

@[simp] theorem coe_comp {R : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} [semiring R] [normed_group E] [normed_group F] [normed_group G] [semimodule R E] [semimodule R F] [semimodule R G] (g : linear_isometry R F G) (f : linear_isometry R E F) : ⇑(comp g f) = ⇑g ∘ ⇑f :=
  rfl

@[simp] theorem id_comp {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (f : linear_isometry R E F) : comp id f = f :=
  ext fun (x : E) => rfl

@[simp] theorem comp_id {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (f : linear_isometry R E F) : comp f id = f :=
  ext fun (x : E) => rfl

theorem comp_assoc {R : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} {G' : Type u_5} [semiring R] [normed_group E] [normed_group F] [normed_group G] [normed_group G'] [semimodule R E] [semimodule R F] [semimodule R G] [semimodule R G'] (f : linear_isometry R G G') (g : linear_isometry R F G) (h : linear_isometry R E F) : comp (comp f g) h = comp f (comp g h) :=
  rfl

protected instance monoid {R : Type u_1} {E : Type u_2} [semiring R] [normed_group E] [semimodule R E] : monoid (linear_isometry R E E) :=
  monoid.mk comp comp_assoc id id_comp comp_id

@[simp] theorem coe_one {R : Type u_1} {E : Type u_2} [semiring R] [normed_group E] [semimodule R E] : ⇑1 = ⇑id :=
  rfl

@[simp] theorem coe_mul {R : Type u_1} {E : Type u_2} [semiring R] [normed_group E] [semimodule R E] (f : linear_isometry R E E) (g : linear_isometry R E E) : ⇑(f * g) = ⇑f ∘ ⇑g :=
  rfl

end linear_isometry


/-- A linear isometric equivalence between two normed vector spaces. -/
structure linear_isometry_equiv (R : Type u_6) (E : Type u_7) (F : Type u_8) [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] 
extends linear_equiv R E F
where
  norm_map' : ∀ (x : E), norm (coe_fn _to_linear_equiv x) = norm x

namespace linear_isometry_equiv


protected instance has_coe_to_fun {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] : has_coe_to_fun (linear_isometry_equiv R E F) :=
  has_coe_to_fun.mk (fun (f : linear_isometry_equiv R E F) => E → F)
    fun (f : linear_isometry_equiv R E F) => linear_equiv.to_fun (to_linear_equiv f)

@[simp] theorem coe_mk {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (e : linear_equiv R E F) (he : ∀ (x : E), norm (coe_fn e x) = norm x) : ⇑(mk e he) = ⇑e :=
  rfl

@[simp] theorem coe_to_linear_equiv {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (e : linear_isometry_equiv R E F) : ⇑(to_linear_equiv e) = ⇑e :=
  rfl

theorem to_linear_equiv_injective {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] : function.injective to_linear_equiv := sorry

theorem ext {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] {e : linear_isometry_equiv R E F} {e' : linear_isometry_equiv R E F} (h : ∀ (x : E), coe_fn e x = coe_fn e' x) : e = e' :=
  to_linear_equiv_injective (linear_equiv.ext h)

/-- Construct a `linear_isometry_equiv` from a `linear_equiv` and two inequalities:
`∀ x, ∥e x∥ ≤ ∥x∥` and `∀ y, ∥e.symm y∥ ≤ ∥y∥`. -/
def of_bounds {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (e : linear_equiv R E F) (h₁ : ∀ (x : E), norm (coe_fn e x) ≤ norm x) (h₂ : ∀ (y : F), norm (coe_fn (linear_equiv.symm e) y) ≤ norm y) : linear_isometry_equiv R E F :=
  mk e sorry

@[simp] theorem norm_map {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (e : linear_isometry_equiv R E F) (x : E) : norm (coe_fn e x) = norm x :=
  norm_map' e x

/-- Reinterpret a `linear_isometry_equiv` as a `linear_isometry`. -/
def to_linear_isometry {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (e : linear_isometry_equiv R E F) : linear_isometry R E F :=
  linear_isometry.mk (↑(to_linear_equiv e)) (norm_map' e)

protected theorem isometry {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (e : linear_isometry_equiv R E F) : isometry ⇑e :=
  linear_isometry.isometry (to_linear_isometry e)

/-- Reinterpret a `linear_isometry_equiv` as an `isometric`. -/
def to_isometric {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (e : linear_isometry_equiv R E F) : E ≃ᵢ F :=
  isometric.mk (linear_equiv.to_equiv (to_linear_equiv e)) (linear_isometry_equiv.isometry e)

protected theorem continuous {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (e : linear_isometry_equiv R E F) : continuous ⇑e :=
  isometry.continuous (linear_isometry_equiv.isometry e)

/-- Identity map as a `linear_isometry_equiv`. -/
def refl (R : Type u_1) (E : Type u_2) [semiring R] [normed_group E] [semimodule R E] : linear_isometry_equiv R E E :=
  mk (linear_equiv.refl R E) sorry

protected instance inhabited {R : Type u_1} {E : Type u_2} [semiring R] [normed_group E] [semimodule R E] : Inhabited (linear_isometry_equiv R E E) :=
  { default := refl R E }

@[simp] theorem coe_refl {R : Type u_1} {E : Type u_2} [semiring R] [normed_group E] [semimodule R E] : ⇑(refl R E) = id :=
  rfl

/-- The inverse `linear_isometry_equiv`. -/
def symm {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (e : linear_isometry_equiv R E F) : linear_isometry_equiv R F E :=
  mk (linear_equiv.symm (to_linear_equiv e)) sorry

@[simp] theorem apply_symm_apply {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (e : linear_isometry_equiv R E F) (x : F) : coe_fn e (coe_fn (symm e) x) = x :=
  linear_equiv.apply_symm_apply (to_linear_equiv e) x

@[simp] theorem symm_apply_apply {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (e : linear_isometry_equiv R E F) (x : E) : coe_fn (symm e) (coe_fn e x) = x :=
  linear_equiv.symm_apply_apply (to_linear_equiv e) x

@[simp] theorem map_eq_zero_iff {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (e : linear_isometry_equiv R E F) {x : E} : coe_fn e x = 0 ↔ x = 0 :=
  linear_equiv.map_eq_zero_iff (to_linear_equiv e)

@[simp] theorem symm_symm {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (e : linear_isometry_equiv R E F) : symm (symm e) = e :=
  ext fun (x : E) => rfl

@[simp] theorem coe_symm_to_linear_equiv {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (e : linear_isometry_equiv R E F) : ⇑(linear_equiv.symm (to_linear_equiv e)) = ⇑(symm e) :=
  rfl

/-- Composition of `linear_isometry_equiv`s as a `linear_isometry_equiv`. -/
def trans {R : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} [semiring R] [normed_group E] [normed_group F] [normed_group G] [semimodule R E] [semimodule R F] [semimodule R G] (e : linear_isometry_equiv R E F) (e' : linear_isometry_equiv R F G) : linear_isometry_equiv R E G :=
  mk (linear_equiv.trans (to_linear_equiv e) (to_linear_equiv e')) sorry

@[simp] theorem coe_trans {R : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} [semiring R] [normed_group E] [normed_group F] [normed_group G] [semimodule R E] [semimodule R F] [semimodule R G] (e₁ : linear_isometry_equiv R E F) (e₂ : linear_isometry_equiv R F G) : ⇑(trans e₁ e₂) = ⇑e₂ ∘ ⇑e₁ :=
  rfl

@[simp] theorem trans_refl {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (e : linear_isometry_equiv R E F) : trans e (refl R F) = e :=
  ext fun (x : E) => rfl

@[simp] theorem refl_trans {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (e : linear_isometry_equiv R E F) : trans (refl R E) e = e :=
  ext fun (x : E) => rfl

@[simp] theorem trans_symm {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (e : linear_isometry_equiv R E F) : trans e (symm e) = refl R E :=
  ext (symm_apply_apply e)

@[simp] theorem symm_trans {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (e : linear_isometry_equiv R E F) : trans (symm e) e = refl R F :=
  ext (apply_symm_apply e)

@[simp] theorem coe_symm_trans {R : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} [semiring R] [normed_group E] [normed_group F] [normed_group G] [semimodule R E] [semimodule R F] [semimodule R G] (e₁ : linear_isometry_equiv R E F) (e₂ : linear_isometry_equiv R F G) : ⇑(symm (trans e₁ e₂)) = ⇑(symm e₁) ∘ ⇑(symm e₂) :=
  rfl

theorem trans_assoc {R : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} {G' : Type u_5} [semiring R] [normed_group E] [normed_group F] [normed_group G] [normed_group G'] [semimodule R E] [semimodule R F] [semimodule R G] [semimodule R G'] (eEF : linear_isometry_equiv R E F) (eFG : linear_isometry_equiv R F G) (eGG' : linear_isometry_equiv R G G') : trans eEF (trans eFG eGG') = trans (trans eEF eFG) eGG' :=
  rfl

protected instance group {R : Type u_1} {E : Type u_2} [semiring R] [normed_group E] [semimodule R E] : group (linear_isometry_equiv R E E) :=
  group.mk (fun (e₁ e₂ : linear_isometry_equiv R E E) => trans e₂ e₁) sorry (refl R E) trans_refl refl_trans symm
    (div_inv_monoid.div._default (fun (e₁ e₂ : linear_isometry_equiv R E E) => trans e₂ e₁) sorry (refl R E) trans_refl
      refl_trans symm)
    trans_symm

@[simp] theorem coe_one {R : Type u_1} {E : Type u_2} [semiring R] [normed_group E] [semimodule R E] : ⇑1 = id :=
  rfl

@[simp] theorem coe_mul {R : Type u_1} {E : Type u_2} [semiring R] [normed_group E] [semimodule R E] (e : linear_isometry_equiv R E E) (e' : linear_isometry_equiv R E E) : ⇑(e * e') = ⇑e ∘ ⇑e' :=
  rfl

@[simp] theorem coe_inv {R : Type u_1} {E : Type u_2} [semiring R] [normed_group E] [semimodule R E] (e : linear_isometry_equiv R E E) : ⇑(e⁻¹) = ⇑(symm e) :=
  rfl

/-- Reinterpret a `linear_isometry_equiv` as a `continuous_linear_equiv`. -/
def to_continuous_linear_equiv {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (e : linear_isometry_equiv R E F) : continuous_linear_equiv R E F :=
  continuous_linear_equiv.mk (to_linear_equiv e)

@[simp] theorem map_zero {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (e : linear_isometry_equiv R E F) : coe_fn e 0 = 0 :=
  linear_equiv.map_zero (to_linear_equiv e)

@[simp] theorem map_add {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (e : linear_isometry_equiv R E F) (x : E) (y : E) : coe_fn e (x + y) = coe_fn e x + coe_fn e y :=
  linear_equiv.map_add (to_linear_equiv e) x y

@[simp] theorem map_sub {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (e : linear_isometry_equiv R E F) (x : E) (y : E) : coe_fn e (x - y) = coe_fn e x - coe_fn e y :=
  linear_equiv.map_sub (to_linear_equiv e) x y

@[simp] theorem map_smul {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (e : linear_isometry_equiv R E F) (c : R) (x : E) : coe_fn e (c • x) = c • coe_fn e x :=
  linear_equiv.map_smul (to_linear_equiv e) c x

@[simp] theorem nnnorm_map {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (e : linear_isometry_equiv R E F) (x : E) : nnnorm (coe_fn e x) = nnnorm x :=
  linear_isometry.nnnorm_map (to_linear_isometry e) x

@[simp] theorem dist_map {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (e : linear_isometry_equiv R E F) (x : E) (y : E) : dist (coe_fn e x) (coe_fn e y) = dist x y :=
  linear_isometry.dist_map (to_linear_isometry e) x y

@[simp] theorem edist_map {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (e : linear_isometry_equiv R E F) (x : E) (y : E) : edist (coe_fn e x) (coe_fn e y) = edist x y :=
  linear_isometry.edist_map (to_linear_isometry e) x y

protected theorem bijective {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (e : linear_isometry_equiv R E F) : function.bijective ⇑e :=
  linear_equiv.bijective (to_linear_equiv e)

protected theorem injective {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (e : linear_isometry_equiv R E F) : function.injective ⇑e :=
  linear_equiv.injective (to_linear_equiv e)

protected theorem surjective {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (e : linear_isometry_equiv R E F) : function.surjective ⇑e :=
  linear_equiv.surjective (to_linear_equiv e)

theorem map_eq_iff {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (e : linear_isometry_equiv R E F) {x : E} {y : E} : coe_fn e x = coe_fn e y ↔ x = y :=
  function.injective.eq_iff (linear_isometry_equiv.injective e)

theorem map_ne {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (e : linear_isometry_equiv R E F) {x : E} {y : E} (h : x ≠ y) : coe_fn e x ≠ coe_fn e y :=
  function.injective.ne (linear_isometry_equiv.injective e) h

protected theorem lipschitz {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (e : linear_isometry_equiv R E F) : lipschitz_with 1 ⇑e :=
  isometry.lipschitz (linear_isometry_equiv.isometry e)

protected theorem antilipschitz {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (e : linear_isometry_equiv R E F) : antilipschitz_with 1 ⇑e :=
  isometry.antilipschitz (linear_isometry_equiv.isometry e)

theorem ediam_image {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (e : linear_isometry_equiv R E F) (s : set E) : emetric.diam (⇑e '' s) = emetric.diam s :=
  isometry.ediam_image (linear_isometry_equiv.isometry e) s

theorem diam_image {R : Type u_1} {E : Type u_2} {F : Type u_3} [semiring R] [normed_group E] [normed_group F] [semimodule R E] [semimodule R F] (e : linear_isometry_equiv R E F) (s : set E) : metric.diam (⇑e '' s) = metric.diam s :=
  isometry.diam_image (linear_isometry_equiv.isometry e) s

