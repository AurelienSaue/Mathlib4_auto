/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Isometries of emetric and metric spaces
Authors: Sébastien Gouëzel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.bounded_continuous_function
import Mathlib.topology.compacts
import Mathlib.PostPort

universes u v w u_1 u_2 l 

namespace Mathlib

/-!
# Isometries

We define isometries, i.e., maps between emetric spaces that preserve
the edistance (on metric spaces, these are exactly the maps that preserve distances),
and prove their basic properties. We also introduce isometric bijections.
-/

/-- An isometry (also known as isometric embedding) is a map preserving the edistance
between emetric spaces, or equivalently the distance between metric space.  -/
def isometry {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] (f : α → β) :=
  ∀ (x1 x2 : α), edist (f x1) (f x2) = edist x1 x2

/-- On metric spaces, a map is an isometry if and only if it preserves distances. -/
theorem isometry_emetric_iff_metric {α : Type u} {β : Type v} [metric_space α] [metric_space β]
    {f : α → β} : isometry f ↔ ∀ (x y : α), dist (f x) (f y) = dist x y :=
  sorry

/-- An isometry preserves edistances. -/
theorem isometry.edist_eq {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] {f : α → β}
    (hf : isometry f) (x : α) (y : α) : edist (f x) (f y) = edist x y :=
  hf x y

/-- An isometry preserves distances. -/
theorem isometry.dist_eq {α : Type u} {β : Type v} [metric_space α] [metric_space β] {f : α → β}
    (hf : isometry f) (x : α) (y : α) : dist (f x) (f y) = dist x y :=
  sorry

theorem isometry.lipschitz {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] {f : α → β}
    (h : isometry f) : lipschitz_with 1 f :=
  lipschitz_with.of_edist_le fun (x y : α) => le_of_eq (h x y)

theorem isometry.antilipschitz {α : Type u} {β : Type v} [emetric_space α] [emetric_space β]
    {f : α → β} (h : isometry f) : antilipschitz_with 1 f :=
  sorry

/-- An isometry is injective -/
theorem isometry.injective {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] {f : α → β}
    (h : isometry f) : function.injective f :=
  antilipschitz_with.injective (isometry.antilipschitz h)

/-- Any map on a subsingleton is an isometry -/
theorem isometry_subsingleton {α : Type u} {β : Type v} [emetric_space α] [emetric_space β]
    {f : α → β} [subsingleton α] : isometry f :=
  sorry

/-- The identity is an isometry -/
theorem isometry_id {α : Type u} [emetric_space α] : isometry id := fun (x y : α) => rfl

/-- The composition of isometries is an isometry -/
theorem isometry.comp {α : Type u} {β : Type v} {γ : Type w} [emetric_space α] [emetric_space β]
    [emetric_space γ] {g : β → γ} {f : α → β} (hg : isometry g) (hf : isometry f) :
    isometry (g ∘ f) :=
  fun (x y : α) => Eq.trans (hg (f x) (f y)) (hf x y)

/-- An isometry is an embedding -/
theorem isometry.uniform_embedding {α : Type u} {β : Type v} [emetric_space α] [emetric_space β]
    {f : α → β} (hf : isometry f) : uniform_embedding f :=
  antilipschitz_with.uniform_embedding (isometry.antilipschitz hf)
    (lipschitz_with.uniform_continuous (isometry.lipschitz hf))

/-- An isometry is continuous. -/
theorem isometry.continuous {α : Type u} {β : Type v} [emetric_space α] [emetric_space β]
    {f : α → β} (hf : isometry f) : continuous f :=
  lipschitz_with.continuous (isometry.lipschitz hf)

/-- The right inverse of an isometry is an isometry. -/
theorem isometry.right_inv {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] {f : α → β}
    {g : β → α} (h : isometry f) (hg : function.right_inverse g f) : isometry g :=
  sorry

/-- Isometries preserve the diameter in emetric spaces. -/
theorem isometry.ediam_image {α : Type u} {β : Type v} [emetric_space α] [emetric_space β]
    {f : α → β} (hf : isometry f) (s : set α) : emetric.diam (f '' s) = emetric.diam s :=
  sorry

theorem isometry.ediam_range {α : Type u} {β : Type v} [emetric_space α] [emetric_space β]
    {f : α → β} (hf : isometry f) : emetric.diam (set.range f) = emetric.diam set.univ :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (emetric.diam (set.range f) = emetric.diam set.univ))
        (Eq.symm set.image_univ)))
    (isometry.ediam_image hf set.univ)

/-- The injection from a subtype is an isometry -/
theorem isometry_subtype_coe {α : Type u} [emetric_space α] {s : set α} : isometry coe :=
  fun (x y : ↥s) => rfl

/-- An isometry preserves the diameter in metric spaces. -/
theorem isometry.diam_image {α : Type u} {β : Type v} [metric_space α] [metric_space β] {f : α → β}
    (hf : isometry f) (s : set α) : metric.diam (f '' s) = metric.diam s :=
  sorry

theorem isometry.diam_range {α : Type u} {β : Type v} [metric_space α] [metric_space β] {f : α → β}
    (hf : isometry f) : metric.diam (set.range f) = metric.diam set.univ :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (metric.diam (set.range f) = metric.diam set.univ))
        (Eq.symm set.image_univ)))
    (isometry.diam_image hf set.univ)

namespace add_monoid_hom


theorem isometry_iff_norm {E : Type u_1} {F : Type u_2} [normed_group E] [normed_group F]
    (f : E →+ F) : isometry ⇑f ↔ ∀ (x : E), norm (coe_fn f x) = norm x :=
  sorry

theorem isometry_of_norm {E : Type u_1} {F : Type u_2} [normed_group E] [normed_group F]
    (f : E →+ F) (hf : ∀ (x : E), norm (coe_fn f x) = norm x) : isometry ⇑f :=
  iff.mpr (isometry_iff_norm f) hf

end add_monoid_hom


/-- `α` and `β` are isometric if there is an isometric bijection between them. -/
structure isometric (α : Type u_1) (β : Type u_2) [emetric_space α] [emetric_space β] extends α ≃ β
    where
  isometry_to_fun : isometry (equiv.to_fun _to_equiv)

infixl:25 " ≃ᵢ " => Mathlib.isometric

namespace isometric


protected instance has_coe_to_fun {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] :
    has_coe_to_fun (α ≃ᵢ β) :=
  has_coe_to_fun.mk (fun (_x : α ≃ᵢ β) => α → β) fun (e : α ≃ᵢ β) => ⇑(to_equiv e)

theorem coe_eq_to_equiv {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] (h : α ≃ᵢ β)
    (a : α) : coe_fn h a = coe_fn (to_equiv h) a :=
  rfl

@[simp] theorem coe_to_equiv {α : Type u} {β : Type v} [emetric_space α] [emetric_space β]
    (h : α ≃ᵢ β) : ⇑(to_equiv h) = ⇑h :=
  rfl

protected theorem isometry {α : Type u} {β : Type v} [emetric_space α] [emetric_space β]
    (h : α ≃ᵢ β) : isometry ⇑h :=
  isometry_to_fun h

protected theorem edist_eq {α : Type u} {β : Type v} [emetric_space α] [emetric_space β]
    (h : α ≃ᵢ β) (x : α) (y : α) : edist (coe_fn h x) (coe_fn h y) = edist x y :=
  isometry.edist_eq (isometric.isometry h) x y

protected theorem dist_eq {α : Type u_1} {β : Type u_2} [metric_space α] [metric_space β]
    (h : α ≃ᵢ β) (x : α) (y : α) : dist (coe_fn h x) (coe_fn h y) = dist x y :=
  isometry.dist_eq (isometric.isometry h) x y

protected theorem continuous {α : Type u} {β : Type v} [emetric_space α] [emetric_space β]
    (h : α ≃ᵢ β) : continuous ⇑h :=
  isometry.continuous (isometric.isometry h)

@[simp] theorem ediam_image {α : Type u} {β : Type v} [emetric_space α] [emetric_space β]
    (h : α ≃ᵢ β) (s : set α) : emetric.diam (⇑h '' s) = emetric.diam s :=
  isometry.ediam_image (isometric.isometry h) s

theorem to_equiv_inj {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] {h₁ : α ≃ᵢ β}
    {h₂ : α ≃ᵢ β} : to_equiv h₁ = to_equiv h₂ → h₁ = h₂ :=
  sorry

theorem ext {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] {h₁ : α ≃ᵢ β}
    {h₂ : α ≃ᵢ β} (H : ∀ (x : α), coe_fn h₁ x = coe_fn h₂ x) : h₁ = h₂ :=
  to_equiv_inj (equiv.ext H)

/-- Alternative constructor for isometric bijections,
taking as input an isometry, and a right inverse. -/
def mk' {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] (f : α → β) (g : β → α)
    (hfg : ∀ (x : β), f (g x) = x) (hf : isometry f) : α ≃ᵢ β :=
  mk (equiv.mk f g sorry hfg) hf

/-- The identity isometry of a space. -/
protected def refl (α : Type u_1) [emetric_space α] : α ≃ᵢ α :=
  mk (equiv.mk (equiv.to_fun (equiv.refl α)) (equiv.inv_fun (equiv.refl α)) sorry sorry) isometry_id

/-- The composition of two isometric isomorphisms, as an isometric isomorphism. -/
protected def trans {α : Type u} {β : Type v} {γ : Type w} [emetric_space α] [emetric_space β]
    [emetric_space γ] (h₁ : α ≃ᵢ β) (h₂ : β ≃ᵢ γ) : α ≃ᵢ γ :=
  mk
    (equiv.mk (equiv.to_fun (equiv.trans (to_equiv h₁) (to_equiv h₂)))
      (equiv.inv_fun (equiv.trans (to_equiv h₁) (to_equiv h₂))) sorry sorry)
    sorry

@[simp] theorem trans_apply {α : Type u} {β : Type v} {γ : Type w} [emetric_space α]
    [emetric_space β] [emetric_space γ] (h₁ : α ≃ᵢ β) (h₂ : β ≃ᵢ γ) (x : α) :
    coe_fn (isometric.trans h₁ h₂) x = coe_fn h₂ (coe_fn h₁ x) :=
  rfl

/-- The inverse of an isometric isomorphism, as an isometric isomorphism. -/
protected def symm {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] (h : α ≃ᵢ β) :
    β ≃ᵢ α :=
  mk (equiv.symm (to_equiv h)) sorry

@[simp] theorem symm_symm {α : Type u} {β : Type v} [emetric_space α] [emetric_space β]
    (h : α ≃ᵢ β) : isometric.symm (isometric.symm h) = h :=
  to_equiv_inj (equiv.symm_symm (to_equiv h))

@[simp] theorem apply_symm_apply {α : Type u} {β : Type v} [emetric_space α] [emetric_space β]
    (h : α ≃ᵢ β) (y : β) : coe_fn h (coe_fn (isometric.symm h) y) = y :=
  equiv.apply_symm_apply (to_equiv h) y

@[simp] theorem symm_apply_apply {α : Type u} {β : Type v} [emetric_space α] [emetric_space β]
    (h : α ≃ᵢ β) (x : α) : coe_fn (isometric.symm h) (coe_fn h x) = x :=
  equiv.symm_apply_apply (to_equiv h) x

theorem symm_apply_eq {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] (h : α ≃ᵢ β)
    {x : α} {y : β} : coe_fn (isometric.symm h) y = x ↔ y = coe_fn h x :=
  equiv.symm_apply_eq (to_equiv h)

theorem eq_symm_apply {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] (h : α ≃ᵢ β)
    {x : α} {y : β} : x = coe_fn (isometric.symm h) y ↔ coe_fn h x = y :=
  equiv.eq_symm_apply (to_equiv h)

theorem symm_comp_self {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] (h : α ≃ᵢ β) :
    ⇑(isometric.symm h) ∘ ⇑h = id :=
  funext fun (a : α) => equiv.left_inv (to_equiv h) a

theorem self_comp_symm {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] (h : α ≃ᵢ β) :
    ⇑h ∘ ⇑(isometric.symm h) = id :=
  funext fun (a : β) => equiv.right_inv (to_equiv h) a

@[simp] theorem range_eq_univ {α : Type u} {β : Type v} [emetric_space α] [emetric_space β]
    (h : α ≃ᵢ β) : set.range ⇑h = set.univ :=
  set.eq_univ_of_forall
    fun (b : β) => Exists.intro (coe_fn (isometric.symm h) b) (congr_fun (self_comp_symm h) b)

theorem image_symm {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] (h : α ≃ᵢ β) :
    set.image ⇑(isometric.symm h) = set.preimage ⇑h :=
  set.image_eq_preimage_of_inverse (equiv.left_inv (to_equiv (isometric.symm h)))
    (equiv.right_inv (to_equiv (isometric.symm h)))

theorem preimage_symm {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] (h : α ≃ᵢ β) :
    set.preimage ⇑(isometric.symm h) = set.image ⇑h :=
  Eq.symm
    (set.image_eq_preimage_of_inverse (equiv.left_inv (to_equiv h)) (equiv.right_inv (to_equiv h)))

@[simp] theorem symm_trans_apply {α : Type u} {β : Type v} {γ : Type w} [emetric_space α]
    [emetric_space β] [emetric_space γ] (h₁ : α ≃ᵢ β) (h₂ : β ≃ᵢ γ) (x : γ) :
    coe_fn (isometric.symm (isometric.trans h₁ h₂)) x =
        coe_fn (isometric.symm h₁) (coe_fn (isometric.symm h₂) x) :=
  rfl

theorem ediam_univ {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] (h : α ≃ᵢ β) :
    emetric.diam set.univ = emetric.diam set.univ :=
  sorry

@[simp] theorem ediam_preimage {α : Type u} {β : Type v} [emetric_space α] [emetric_space β]
    (h : α ≃ᵢ β) (s : set β) : emetric.diam (⇑h ⁻¹' s) = emetric.diam s :=
  sorry

/-- The (bundled) homeomorphism associated to an isometric isomorphism. -/
protected def to_homeomorph {α : Type u} {β : Type v} [emetric_space α] [emetric_space β]
    (h : α ≃ᵢ β) : α ≃ₜ β :=
  homeomorph.mk (to_equiv h)

@[simp] theorem coe_to_homeomorph {α : Type u} {β : Type v} [emetric_space α] [emetric_space β]
    (h : α ≃ᵢ β) : ⇑(isometric.to_homeomorph h) = ⇑h :=
  rfl

@[simp] theorem coe_to_homeomorph_symm {α : Type u} {β : Type v} [emetric_space α] [emetric_space β]
    (h : α ≃ᵢ β) : ⇑(homeomorph.symm (isometric.to_homeomorph h)) = ⇑(isometric.symm h) :=
  rfl

@[simp] theorem to_homeomorph_to_equiv {α : Type u} {β : Type v} [emetric_space α] [emetric_space β]
    (h : α ≃ᵢ β) : homeomorph.to_equiv (isometric.to_homeomorph h) = to_equiv h :=
  rfl

@[simp] theorem comp_continuous_on_iff {α : Type u} {β : Type v} [emetric_space α] [emetric_space β]
    {γ : Type u_1} [topological_space γ] (h : α ≃ᵢ β) {f : γ → α} {s : set γ} :
    continuous_on (⇑h ∘ f) s ↔ continuous_on f s :=
  homeomorph.comp_continuous_on_iff (isometric.to_homeomorph h) f s

@[simp] theorem comp_continuous_iff {α : Type u} {β : Type v} [emetric_space α] [emetric_space β]
    {γ : Type u_1} [topological_space γ] (h : α ≃ᵢ β) {f : γ → α} :
    continuous (⇑h ∘ f) ↔ continuous f :=
  homeomorph.comp_continuous_iff (isometric.to_homeomorph h)

@[simp] theorem comp_continuous_iff' {α : Type u} {β : Type v} [emetric_space α] [emetric_space β]
    {γ : Type u_1} [topological_space γ] (h : α ≃ᵢ β) {f : β → γ} :
    continuous (f ∘ ⇑h) ↔ continuous f :=
  homeomorph.comp_continuous_iff' (isometric.to_homeomorph h)

/-- The group of isometries. -/
protected instance group {α : Type u} [emetric_space α] : group (α ≃ᵢ α) :=
  group.mk (fun (e₁ e₂ : α ≃ᵢ α) => isometric.trans e₂ e₁) sorry (isometric.refl α) sorry sorry
    isometric.symm
    (div_inv_monoid.div._default (fun (e₁ e₂ : α ≃ᵢ α) => isometric.trans e₂ e₁) sorry
      (isometric.refl α) sorry sorry isometric.symm)
    sorry

@[simp] theorem coe_one {α : Type u} [emetric_space α] : ⇑1 = id := rfl

@[simp] theorem coe_mul {α : Type u} [emetric_space α] (e₁ : α ≃ᵢ α) (e₂ : α ≃ᵢ α) :
    ⇑(e₁ * e₂) = ⇑e₁ ∘ ⇑e₂ :=
  rfl

theorem mul_apply {α : Type u} [emetric_space α] (e₁ : α ≃ᵢ α) (e₂ : α ≃ᵢ α) (x : α) :
    coe_fn (e₁ * e₂) x = coe_fn e₁ (coe_fn e₂ x) :=
  rfl

@[simp] theorem inv_apply_self {α : Type u} [emetric_space α] (e : α ≃ᵢ α) (x : α) :
    coe_fn (e⁻¹) (coe_fn e x) = x :=
  symm_apply_apply e x

@[simp] theorem apply_inv_self {α : Type u} [emetric_space α] (e : α ≃ᵢ α) (x : α) :
    coe_fn e (coe_fn (e⁻¹) x) = x :=
  apply_symm_apply e x

/-- Addition `y ↦ y + x` as an `isometry`. -/
protected def add_right {G : Type u_1} [normed_group G] (x : G) : G ≃ᵢ G :=
  mk (equiv.mk (equiv.to_fun (equiv.add_right x)) (equiv.inv_fun (equiv.add_right x)) sorry sorry)
    sorry

@[simp] theorem add_right_to_equiv {G : Type u_1} [normed_group G] (x : G) :
    to_equiv (isometric.add_right x) = equiv.add_right x :=
  rfl

@[simp] theorem coe_add_right {G : Type u_1} [normed_group G] (x : G) :
    ⇑(isometric.add_right x) = fun (y : G) => y + x :=
  rfl

theorem add_right_apply {G : Type u_1} [normed_group G] (x : G) (y : G) :
    coe_fn (isometric.add_right x) y = y + x :=
  rfl

@[simp] theorem add_right_symm {G : Type u_1} [normed_group G] (x : G) :
    isometric.symm (isometric.add_right x) = isometric.add_right (-x) :=
  ext fun (y : G) => rfl

/-- Addition `y ↦ x + y` as an `isometry`. -/
protected def add_left {G : Type u_1} [normed_group G] (x : G) : G ≃ᵢ G :=
  mk (equiv.add_left x) sorry

@[simp] theorem add_left_to_equiv {G : Type u_1} [normed_group G] (x : G) :
    to_equiv (isometric.add_left x) = equiv.add_left x :=
  rfl

@[simp] theorem coe_add_left {G : Type u_1} [normed_group G] (x : G) :
    ⇑(isometric.add_left x) = Add.add x :=
  rfl

@[simp] theorem add_left_symm {G : Type u_1} [normed_group G] (x : G) :
    isometric.symm (isometric.add_left x) = isometric.add_left (-x) :=
  ext fun (y : G) => rfl

/-- Negation `x ↦ -x` as an `isometry`. -/
protected def neg (G : Type u_1) [normed_group G] : G ≃ᵢ G := mk (equiv.neg G) sorry

@[simp] theorem neg_symm {G : Type u_1} [normed_group G] :
    isometric.symm (isometric.neg G) = isometric.neg G :=
  rfl

@[simp] theorem neg_to_equiv {G : Type u_1} [normed_group G] :
    to_equiv (isometric.neg G) = equiv.neg G :=
  rfl

@[simp] theorem coe_neg {G : Type u_1} [normed_group G] : ⇑(isometric.neg G) = Neg.neg := rfl

end isometric


namespace isometric


@[simp] theorem diam_image {α : Type u} {β : Type v} [metric_space α] [metric_space β] (h : α ≃ᵢ β)
    (s : set α) : metric.diam (⇑h '' s) = metric.diam s :=
  isometry.diam_image (isometric.isometry h) s

@[simp] theorem diam_preimage {α : Type u} {β : Type v} [metric_space α] [metric_space β]
    (h : α ≃ᵢ β) (s : set β) : metric.diam (⇑h ⁻¹' s) = metric.diam s :=
  sorry

theorem diam_univ {α : Type u} {β : Type v} [metric_space α] [metric_space β] (h : α ≃ᵢ β) :
    metric.diam set.univ = metric.diam set.univ :=
  congr_arg ennreal.to_real (ediam_univ h)

end isometric


/-- An isometry induces an isometric isomorphism between the source space and the
range of the isometry. -/
def isometry.isometric_on_range {α : Type u} {β : Type v} [emetric_space α] [emetric_space β]
    {f : α → β} (h : isometry f) : α ≃ᵢ ↥(set.range f) :=
  isometric.mk
    (equiv.mk (equiv.to_fun (equiv.set.range f (isometry.injective h)))
      (equiv.inv_fun (equiv.set.range f (isometry.injective h))) sorry sorry)
    sorry

@[simp] theorem isometry.isometric_on_range_apply {α : Type u} {β : Type v} [emetric_space α]
    [emetric_space β] {f : α → β} (h : isometry f) (x : α) :
    coe_fn (isometry.isometric_on_range h) x = { val := f x, property := set.mem_range_self x } :=
  rfl

/-- In a normed algebra, the inclusion of the base field in the extended field is an isometry. -/
theorem algebra_map_isometry (𝕜 : Type u_1) (𝕜' : Type u_2) [normed_field 𝕜] [normed_ring 𝕜']
    [normed_algebra 𝕜 𝕜'] : isometry ⇑(algebra_map 𝕜 𝕜') :=
  sorry

/-- The space of bounded sequences, with its sup norm -/
def ℓ_infty_ℝ := bounded_continuous_function ℕ ℝ

namespace Kuratowski_embedding


/-! ### In this section, we show that any separable metric space can be embedded isometrically in ℓ^∞(ℝ) -/

/-- A metric space can be embedded in `l^∞(ℝ)` via the distances to points in
a fixed countable set, if this set is dense. This map is given in the next definition,
without density assumptions. -/
def embedding_of_subset {α : Type u} [metric_space α] (x : ℕ → α) (a : α) : ℓ_infty_ℝ :=
  bounded_continuous_function.of_normed_group_discrete
    (fun (n : ℕ) => dist a (x n) - dist (x 0) (x n)) (dist a (x 0)) sorry

theorem embedding_of_subset_coe {α : Type u} {n : ℕ} [metric_space α] (x : ℕ → α) (a : α) :
    coe_fn (embedding_of_subset x a) n = dist a (x n) - dist (x 0) (x n) :=
  rfl

/-- The embedding map is always a semi-contraction. -/
theorem embedding_of_subset_dist_le {α : Type u} [metric_space α] (x : ℕ → α) (a : α) (b : α) :
    dist (embedding_of_subset x a) (embedding_of_subset x b) ≤ dist a b :=
  sorry

/-- When the reference set is dense, the embedding map is an isometry on its image. -/
theorem embedding_of_subset_isometry {α : Type u} [metric_space α] (x : ℕ → α) (H : dense_range x) :
    isometry (embedding_of_subset x) :=
  sorry

/-- Every separable metric space embeds isometrically in ℓ_infty_ℝ. -/
theorem exists_isometric_embedding (α : Type u) [metric_space α]
    [topological_space.separable_space α] : ∃ (f : α → ℓ_infty_ℝ), isometry f :=
  sorry

end Kuratowski_embedding


/-- The Kuratowski embedding is an isometric embedding of a separable metric space in ℓ^∞(ℝ) -/
def Kuratowski_embedding (α : Type u) [metric_space α] [topological_space.separable_space α] :
    α → ℓ_infty_ℝ :=
  classical.some sorry

/-- The Kuratowski embedding is an isometry -/
protected theorem Kuratowski_embedding.isometry (α : Type u) [metric_space α]
    [topological_space.separable_space α] : isometry (Kuratowski_embedding α) :=
  classical.some_spec (Kuratowski_embedding.exists_isometric_embedding α)

/-- Version of the Kuratowski embedding for nonempty compacts -/
def nonempty_compacts.Kuratowski_embedding (α : Type u) [metric_space α] [compact_space α]
    [Nonempty α] : topological_space.nonempty_compacts ℓ_infty_ℝ :=
  { val := set.range (Kuratowski_embedding α), property := sorry }

end Mathlib