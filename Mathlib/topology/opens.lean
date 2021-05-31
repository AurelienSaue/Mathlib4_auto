/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.bases
import Mathlib.topology.homeomorph
import Mathlib.PostPort

universes u_1 u_2 u_3 

namespace Mathlib

/-!
# Open sets

## Summary

We define the subtype of open sets in a topological space.

## Main Definitions

- `opens α` is the type of open subsets of a topological space `α`.
- `open_nhds_of x` is the type of open subsets of a topological space `α` containing `x : α`.
-
-/

namespace topological_space


/-- The type of open subsets of a topological space. -/
def opens (α : Type u_1) [topological_space α] :=
  Subtype fun (s : set α) => is_open s

namespace opens


protected instance set.has_coe {α : Type u_1} [topological_space α] : has_coe (opens α) (set α) :=
  has_coe.mk subtype.val

theorem val_eq_coe {α : Type u_1} [topological_space α] (U : opens α) : subtype.val U = ↑U :=
  rfl

/-- the coercion `opens α → set α` applied to a pair is the same as taking the first component -/
theorem coe_mk {α : Type u_1} [topological_space α] {U : set α} {hU : is_open U} : ↑{ val := U, property := hU } = U :=
  rfl

protected instance has_subset {α : Type u_1} [topological_space α] : has_subset (opens α) :=
  has_subset.mk fun (U V : opens α) => ↑U ⊆ ↑V

protected instance has_mem {α : Type u_1} [topological_space α] : has_mem α (opens α) :=
  has_mem.mk fun (a : α) (U : opens α) => a ∈ ↑U

@[simp] theorem subset_coe {α : Type u_1} [topological_space α] {U : opens α} {V : opens α} : ↑U ⊆ ↑V = (U ⊆ V) :=
  rfl

@[simp] theorem mem_coe {α : Type u_1} [topological_space α] {x : α} {U : opens α} : x ∈ ↑U = (x ∈ U) :=
  rfl

theorem ext {α : Type u_1} [topological_space α] {U : opens α} {V : opens α} (h : ↑U = ↑V) : U = V :=
  iff.mpr subtype.ext_iff h

theorem ext_iff {α : Type u_1} [topological_space α] {U : opens α} {V : opens α} : ↑U = ↑V ↔ U = V :=
  { mp := ext, mpr := congr_arg coe }

protected instance partial_order {α : Type u_1} [topological_space α] : partial_order (opens α) :=
  subtype.partial_order fun (s : set α) => is_open s

/-- The interior of a set, as an element of `opens`. -/
def interior {α : Type u_1} [topological_space α] (s : set α) : opens α :=
  { val := interior s, property := is_open_interior }

theorem gc {α : Type u_1} [topological_space α] : galois_connection coe interior :=
  fun (U : opens α) (s : set α) =>
    { mp := fun (h : ↑U ≤ s) => interior_maximal h (subtype.property U),
      mpr := fun (h : U ≤ interior s) => le_trans h interior_subset }

/-- The galois insertion between sets and opens, but ordered by reverse inclusion. -/
def gi {α : Type u_1} [topological_space α] : galois_insertion interior subtype.val :=
  galois_insertion.mk
    (fun (s : order_dual (set α)) (hs : subtype.val (interior s) ≤ s) => { val := s, property := sorry }) sorry sorry
    sorry

@[simp] theorem gi_choice_val {α : Type u_1} [topological_space α] {s : order_dual (set α)} {hs : subtype.val (interior s) ≤ s} : subtype.val (galois_insertion.choice gi s hs) = s :=
  rfl

protected instance complete_lattice {α : Type u_1} [topological_space α] : complete_lattice (opens α) :=
  complete_lattice.copy (order_dual.complete_lattice (order_dual (opens α))) (fun (U V : opens α) => U ⊆ V) sorry
    { val := set.univ, property := is_open_univ } sorry { val := ∅, property := is_open_empty } sorry
    (fun (U V : opens α) => { val := ↑U ∪ ↑V, property := sorry }) sorry
    (fun (U V : opens α) => { val := ↑U ∩ ↑V, property := sorry }) sorry
    (fun (Us : set (opens α)) => { val := ⋃₀(coe '' Us), property := sorry }) sorry complete_lattice.Inf sorry

/- le  -/ (λ U V, U ⊆ V) rfl
/- top -/ ⟨set.univ, is_open_univ⟩ (subtype.ext_iff_val.mpr interior_univ.symm)
/- bot -/ ⟨∅, is_open_empty⟩ rfl
/- sup -/ (λ U V, ⟨↑U ∪ ↑V, is_open_union U.2 V.2⟩) rfl
/- inf -/ (λ U V, ⟨↑U ∩ ↑V, is_open_inter U.2 V.2⟩)
begin
  funext,
  apply subtype.ext_iff_val.mpr,
  exact (is_open_inter U.2 V.2).interior_eq.symm,
end
/- Sup -/ (λ Us, ⟨⋃₀ (coe '' Us), is_open_sUnion $ λ U hU,
by { rcases hU with ⟨⟨V, hV⟩, h, h'⟩, dsimp at h', subst h', exact hV}⟩)
begin
  funext,
  apply subtype.ext_iff_val.mpr,
  simp [Sup_range],
  refl,
end
/- Inf -/ _ rfl

lemma le_def {U V : opens α} : U ≤ V ↔ (U : set α) ≤ (V : set α) :=
by refl
theorem le_def {α : Type u_1} [topological_space α] {U : opens α} {V : opens α} : U ≤ V ↔ ↑U ≤ ↑V :=
  iff.refl (U ≤ V)


@[simp] lemma mk_inf_mk {U V : set α} {hU : is_open U} {hV : is_open V} :
  (⟨U, hU⟩ ⊓ ⟨V, hV⟩ : opens α) = ⟨U ⊓ V, is_open_inter hU hV⟩ := rfl
@[simp] theorem mk_inf_mk {α : Type u_1} [topological_space α] {U : set α} {V : set α} {hU : is_open U} {hV : is_open V} : { val := U, property := hU } ⊓ { val := V, property := hV } = { val := U ⊓ V, property := is_open_inter hU hV } :=
  rfl

@[simp,norm_cast] lemma coe_inf {U V : opens α} :
  ((U ⊓ V : opens α) : set α) = (U : set α) ⊓ (V : set α) := rfl
@[simp] theorem coe_inf {α : Type u_1} [topological_space α] {U : opens α} {V : opens α} : ↑(U ⊓ V) = ↑U ⊓ ↑V :=
  rfl


instance : has_inter (opens α) := ⟨λ U V, U ⊓ V⟩
instance : has_union (opens α) := ⟨λ U V, U ⊔ V⟩
protected instance has_inter {α : Type u_1} [topological_space α] : has_inter (opens α) :=
  has_inter.mk fun (U V : opens α) => U ⊓ V

instance : has_emptyc (opens α) := ⟨⊥⟩
protected instance has_union {α : Type u_1} [topological_space α] : has_union (opens α) :=
  has_union.mk fun (U V : opens α) => U ⊔ V

instance : inhabited (opens α) := ⟨∅⟩
protected instance has_emptyc {α : Type u_1} [topological_space α] : has_emptyc (opens α) :=
  has_emptyc.mk ⊥


protected instance inhabited {α : Type u_1} [topological_space α] : Inhabited (opens α) :=
  { default := ∅ }

@[simp] lemma inter_eq (U V : opens α) : U ∩ V = U ⊓ V := rfl
@[simp] lemma union_eq (U V : opens α) : U ∪ V = U ⊔ V := rfl
@[simp] theorem inter_eq {α : Type u_1} [topological_space α] (U : opens α) (V : opens α) : U ∩ V = U ⊓ V :=
  rfl

@[simp] lemma empty_eq : (∅ : opens α) = ⊥ := rfl
@[simp] theorem union_eq {α : Type u_1} [topological_space α] (U : opens α) (V : opens α) : U ∪ V = U ⊔ V :=
  rfl


@[simp] theorem empty_eq {α : Type u_1} [topological_space α] : ∅ = ⊥ :=
  rfl

@[simp] lemma Sup_s {Us : set (opens α)} : ↑(Sup Us) = ⋃₀ ((coe : _ → set α) '' Us) :=
begin
@[simp] theorem Sup_s {α : Type u_1} [topological_space α] {Us : set (opens α)} : ↑(Sup Us) = ⋃₀(coe '' Us) := sorry

  rw [@galois_connection.l_Sup (opens α) (set α) _ _ (coe : opens α → set α) interior gc Us],
  rw [set.sUnion_image]
end

lemma supr_def {ι} (s : ι → opens α) : (⨆ i, s i) = ⟨⋃ i, s i, is_open_Union $ λ i, (s i).2⟩ :=
by { ext, simp only [supr, opens.Sup_s, sUnion_image, bUnion_range], refl }
theorem supr_def {α : Type u_1} [topological_space α] {ι : Sort u_2} (s : ι → opens α) : (supr fun (i : ι) => s i) =
  { val := set.Union fun (i : ι) => ↑(s i), property := is_open_Union fun (i : ι) => subtype.property (s i) } := sorry


@[simp] lemma supr_mk {ι} (s : ι → set α) (h : Π i, is_open (s i)) :
  (⨆ i, ⟨s i, h i⟩ : opens α) = ⟨⨆ i, s i, is_open_Union h⟩ :=
@[simp] theorem supr_mk {α : Type u_1} [topological_space α] {ι : Sort u_2} (s : ι → set α) (h : ∀ (i : ι), is_open (s i)) : (supr fun (i : ι) => { val := s i, property := h i }) = { val := supr fun (i : ι) => s i, property := is_open_Union h } := sorry

by { rw supr_def, simp }

@[simp] lemma supr_s {ι} (s : ι → opens α) : ((⨆ i, s i : opens α) : set α) = ⋃ i, s i :=
by simp [supr_def]
@[simp] theorem supr_s {α : Type u_1} [topological_space α] {ι : Sort u_2} (s : ι → opens α) : ↑(supr fun (i : ι) => s i) = set.Union fun (i : ι) => ↑(s i) := sorry


theorem mem_supr {ι} {x : α} {s : ι → opens α} : x ∈ supr s ↔ ∃ i, x ∈ s i :=
by { rw [←mem_coe], simp, }
theorem mem_supr {α : Type u_1} [topological_space α] {ι : Sort u_2} {x : α} {s : ι → opens α} : x ∈ supr s ↔ ∃ (i : ι), x ∈ s i := sorry


lemma open_embedding_of_le {U V : opens α} (i : U ≤ V) :
  open_embedding (set.inclusion i) :=
theorem open_embedding_of_le {α : Type u_1} [topological_space α] {U : opens α} {V : opens α} (i : U ≤ V) : open_embedding (set.inclusion i) :=
  open_embedding.mk (embedding.mk (inducing.mk (Eq.symm induced_compose)) (set.inclusion_injective i))
    (eq.mpr (id (Eq._oldrec (Eq.refl (is_open (set.range (set.inclusion i)))) (set.range_inclusion i)))
      (is_open.preimage continuous_subtype_val (subtype.property U)))

{ inj := set.inclusion_injective i,
  induced := (@induced_compose _ _ _ _ (set.inclusion i) coe).symm,
  open_range :=
  begin
    rw set.range_inclusion i,
    exact U.property.preimage continuous_subtype_val
  end, }

def is_basis (B : set (opens α)) : Prop := is_topological_basis ((coe : _ → set α) '' B)

def is_basis {α : Type u_1} [topological_space α] (B : set (opens α)) :=
  is_topological_basis (coe '' B)

lemma is_basis_iff_nbhd {B : set (opens α)} :
  is_basis B ↔ ∀ {U : opens α} {x}, x ∈ U → ∃ U' ∈ B, x ∈ U' ∧ U' ⊆ U :=
theorem is_basis_iff_nbhd {α : Type u_1} [topological_space α] {B : set (opens α)} : is_basis B ↔ ∀ {U : opens α} {x : α}, x ∈ U → ∃ (U' : opens α), ∃ (H : U' ∈ B), x ∈ U' ∧ U' ⊆ U := sorry

begin
  split; intro h,
  { rintros ⟨sU, hU⟩ x hx,
    rcases (mem_nhds_of_is_topological_basis h).mp (mem_nhds_sets hU hx)
      with ⟨sV, ⟨⟨V, H₁, H₂⟩, hsV⟩⟩,
    refine ⟨V, H₁, _⟩,
    cases V, dsimp at H₂, subst H₂, exact hsV },
  { refine is_topological_basis_of_open_of_nhds _ _,
    { rintros sU ⟨U, ⟨H₁, H₂⟩⟩, subst H₂, exact U.property },
    { intros x sU hx hsU,
      rcases @h (⟨sU, hsU⟩ : opens α) x hx with ⟨V, hV, H⟩,
      exact ⟨V, ⟨V, hV, rfl⟩, H⟩ } }
end

lemma is_basis_iff_cover {B : set (opens α)} :
  is_basis B ↔ ∀ U : opens α, ∃ Us ⊆ B, U = Sup Us :=
theorem is_basis_iff_cover {α : Type u_1} [topological_space α] {B : set (opens α)} : is_basis B ↔ ∀ (U : opens α), ∃ (Us : set (opens α)), ∃ (H : Us ⊆ B), U = Sup Us := sorry

begin
  split,
  { intros hB U,
    rcases sUnion_basis_of_is_open hB U.prop with ⟨sUs, H, hU⟩,
    existsi {U : opens α | U ∈ B ∧ ↑U ∈ sUs},
    split,
    { intros U hU, exact hU.left },
    { apply ext,
      rw [Sup_s, hU],
      congr' with s; split; intro hs,
      { rcases H hs with ⟨V, hV⟩,
        rw ← hV.right at hs,
        refine ⟨V, ⟨⟨hV.left, hs⟩, hV.right⟩⟩ },
      { rcases hs with ⟨V, ⟨⟨H₁, H₂⟩, H₃⟩⟩,
        subst H₃, exact H₂ } } },
  { intro h,
    rw is_basis_iff_nbhd,
    intros U x hx,
    rcases h U with ⟨Us, hUs, H⟩,
    replace H := congr_arg (coe : _ → set α) H,
    rw Sup_s at H,
    change x ∈ ↑U at hx,
    rw H at hx,
    rcases set.mem_sUnion.mp hx with ⟨sV, ⟨⟨V, H₁, H₂⟩, hsV⟩⟩,
    refine ⟨V,hUs H₁,_⟩,
    cases V with V hV,
    dsimp at H₂, subst H₂,
    refine ⟨hsV,_⟩,
    change V ⊆ U, rw H,
    exact set.subset_sUnion_of_mem ⟨⟨V, _⟩, ⟨H₁, rfl⟩⟩ }
end

/-- The preimage of an open set, as an open set. -/

def comap {f : α → β} (hf : continuous f) (V : opens β) : opens α :=
⟨f ⁻¹' V.1, V.2.preimage hf⟩
def comap {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} (hf : continuous f) (V : opens β) : opens α :=
  { val := f ⁻¹' subtype.val V, property := sorry }


@[simp] lemma comap_id (U : opens α) : U.comap continuous_id = U := by { ext, refl }

@[simp] theorem comap_id {α : Type u_1} [topological_space α] (U : opens α) : comap continuous_id U = U :=
  ext (set.ext fun (x : α) => iff.refl (x ∈ ↑(comap continuous_id U)))

lemma comap_mono {f : α → β} (hf : continuous f) {V W : opens β} (hVW : V ⊆ W) :
  V.comap hf ⊆ W.comap hf :=
theorem comap_mono {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} (hf : continuous f) {V : opens β} {W : opens β} (hVW : V ⊆ W) : comap hf V ⊆ comap hf W :=
  fun (_x : α) (h : _x ∈ ↑(comap hf V)) => hVW h

λ _ h, hVW h

@[simp] lemma coe_comap {f : α → β} (hf : continuous f) (U : opens β) :
  ↑(U.comap hf) = f ⁻¹' U := rfl
@[simp] theorem coe_comap {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} (hf : continuous f) (U : opens β) : ↑(comap hf U) = f ⁻¹' ↑U :=
  rfl


@[simp] lemma comap_val {f : α → β} (hf : continuous f) (U : opens β) :
  (U.comap hf).1 = f ⁻¹' U := rfl
@[simp] theorem comap_val {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} (hf : continuous f) (U : opens β) : subtype.val (comap hf U) = f ⁻¹' ↑U :=
  rfl


protected lemma comap_comp {g : β → γ} {f : α → β} (hg : continuous g) (hf : continuous f)
  (U : opens γ) : U.comap (hg.comp hf) = (U.comap hg).comap hf :=
protected theorem comap_comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α] [topological_space β] [topological_space γ] {g : β → γ} {f : α → β} (hg : continuous g) (hf : continuous f) (U : opens γ) : comap (continuous.comp hg hf) U = comap hf (comap hg U) := sorry

by { ext1, simp only [coe_comap, preimage_preimage] }

/-- A homeomorphism induces an equivalence on open sets, by taking comaps. -/
@[simp] protected def equiv {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (f : α ≃ₜ β) : opens α ≃ opens β :=
  equiv.mk (comap sorry) (comap (homeomorph.continuous f)) sorry sorry

end opens


/-- The open neighborhoods of a point. See also `opens` or `nhds`. -/
def open_nhds_of {α : Type u_1} [topological_space α] (x : α) :=
  Subtype fun (s : set α) => is_open s ∧ x ∈ s

protected instance open_nhds_of.inhabited {α : Type u_1} [topological_space α] (x : α) : Inhabited (open_nhds_of x) :=
  { default := { val := set.univ, property := sorry } }

