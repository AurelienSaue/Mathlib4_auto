/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.order.filter.bases
import PostPort

universes u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 

namespace Mathlib

/-!
# Lift filters along filter and set functions
-/

namespace filter


/-- A variant on `bind` using a function `g` taking a set instead of a member of `α`.
This is essentially a push-forward along a function mapping each set to a filter. -/
protected def lift {α : Type u_1} {β : Type u_2} (f : filter α) (g : set α → filter β) : filter β :=
  infi fun (s : set α) => infi fun (H : s ∈ f) => g s

/-- If `(p : ι → Prop, s : ι → set α)` is a basis of a filter `f`, `g` is a monotone function
`set α → filter γ`, and for each `i`, `(pg : β i → Prop, sg : β i → set α)` is a basis
of the filter `g (s i)`, then `(λ (i : ι) (x : β i), p i ∧ pg i x, λ (i : ι) (x : β i), sg i x)`
is a basis of the filter `f.lift g`.

This basis is parametrized by `i : ι` and `x : β i`, so in order to formulate this fact using
`has_basis` one has to use `Σ i, β i` as the index type, see `filter.has_basis.lift`.
This lemma states the corresponding `mem_iff` statement without using a sigma type. -/
theorem has_basis.mem_lift_iff {α : Type u_1} {γ : Type u_3} {ι : Type u_2} {p : ι → Prop} {s : ι → set α} {f : filter α} (hf : has_basis f p s) {β : ι → Type u_4} {pg : (i : ι) → β i → Prop} {sg : (i : ι) → β i → set γ} {g : set α → filter γ} (hg : ∀ (i : ι), has_basis (g (s i)) (pg i) (sg i)) (gm : monotone g) : ∀ {s : set γ}, s ∈ filter.lift f g ↔ ∃ (i : ι), ∃ (hi : p i), ∃ (x : β i), ∃ (hx : pg i x), sg i x ⊆ s := sorry

/-- If `(p : ι → Prop, s : ι → set α)` is a basis of a filter `f`, `g` is a monotone function
`set α → filter γ`, and for each `i`, `(pg : β i → Prop, sg : β i → set α)` is a basis
of the filter `g (s i)`, then `(λ (i : ι) (x : β i), p i ∧ pg i x, λ (i : ι) (x : β i), sg i x)`
is a basis of the filter `f.lift g`.

This basis is parametrized by `i : ι` and `x : β i`, so in order to formulate this fact using
`has_basis` one has to use `Σ i, β i` as the index type. See also `filter.has_basis.mem_lift_iff`
for the corresponding `mem_iff` statement formulated without using a sigma type. -/
theorem has_basis.lift {α : Type u_1} {γ : Type u_3} {ι : Type u_2} {p : ι → Prop} {s : ι → set α} {f : filter α} (hf : has_basis f p s) {β : ι → Type u_4} {pg : (i : ι) → β i → Prop} {sg : (i : ι) → β i → set γ} {g : set α → filter γ} (hg : ∀ (i : ι), has_basis (g (s i)) (pg i) (sg i)) (gm : monotone g) : has_basis (filter.lift f g) (fun (i : sigma fun (i : ι) => β i) => p (sigma.fst i) ∧ pg (sigma.fst i) (sigma.snd i))
  fun (i : sigma fun (i : ι) => β i) => sg (sigma.fst i) (sigma.snd i) := sorry

theorem mem_lift_sets {α : Type u_1} {β : Type u_2} {f : filter α} {g : set α → filter β} (hg : monotone g) {s : set β} : s ∈ filter.lift f g ↔ ∃ (t : set α), ∃ (H : t ∈ f), s ∈ g t := sorry

theorem mem_lift {α : Type u_1} {β : Type u_2} {f : filter α} {g : set α → filter β} {s : set β} {t : set α} (ht : t ∈ f) (hs : s ∈ g t) : s ∈ filter.lift f g :=
  iff.mp le_principal_iff
    ((fun (this : filter.lift f g ≤ principal s) => this)
      (infi_le_of_le t (infi_le_of_le ht (iff.mpr le_principal_iff hs))))

theorem lift_le {α : Type u_1} {β : Type u_2} {f : filter α} {g : set α → filter β} {h : filter β} {s : set α} (hs : s ∈ f) (hg : g s ≤ h) : filter.lift f g ≤ h :=
  infi_le_of_le s (infi_le_of_le hs hg)

theorem le_lift {α : Type u_1} {β : Type u_2} {f : filter α} {g : set α → filter β} {h : filter β} (hh : ∀ (s : set α), s ∈ f → h ≤ g s) : h ≤ filter.lift f g :=
  le_infi fun (s : set α) => le_infi fun (hs : s ∈ f) => hh s hs

theorem lift_mono {α : Type u_1} {β : Type u_2} {f₁ : filter α} {f₂ : filter α} {g₁ : set α → filter β} {g₂ : set α → filter β} (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) : filter.lift f₁ g₁ ≤ filter.lift f₂ g₂ :=
  infi_le_infi fun (s : set α) => infi_le_infi2 fun (hs : s ∈ f₂) => Exists.intro (hf hs) (hg s)

theorem lift_mono' {α : Type u_1} {β : Type u_2} {f : filter α} {g₁ : set α → filter β} {g₂ : set α → filter β} (hg : ∀ (s : set α), s ∈ f → g₁ s ≤ g₂ s) : filter.lift f g₁ ≤ filter.lift f g₂ :=
  infi_le_infi fun (s : set α) => infi_le_infi fun (hs : s ∈ f) => hg s hs

theorem tendsto_lift {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : filter α} {g : set α → filter β} {m : γ → β} {l : filter γ} : tendsto m l (filter.lift f g) ↔ ∀ (s : set α), s ∈ f → tendsto m l (g s) := sorry

theorem map_lift_eq {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : filter α} {g : set α → filter β} {m : β → γ} (hg : monotone g) : map m (filter.lift f g) = filter.lift f (map m ∘ g) := sorry

theorem comap_lift_eq {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : filter α} {g : set α → filter β} {m : γ → β} (hg : monotone g) : comap m (filter.lift f g) = filter.lift f (comap m ∘ g) := sorry

theorem comap_lift_eq2 {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : filter α} {m : β → α} {g : set β → filter γ} (hg : monotone g) : filter.lift (comap m f) g = filter.lift f (g ∘ set.preimage m) := sorry

theorem map_lift_eq2 {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : filter α} {g : set β → filter γ} {m : α → β} (hg : monotone g) : filter.lift (map m f) g = filter.lift f (g ∘ set.image m) := sorry

theorem lift_comm {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : filter α} {g : filter β} {h : set α → set β → filter γ} : (filter.lift f fun (s : set α) => filter.lift g (h s)) =
  filter.lift g fun (t : set β) => filter.lift f fun (s : set α) => h s t := sorry

theorem lift_assoc {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : filter α} {g : set α → filter β} {h : set β → filter γ} (hg : monotone g) : filter.lift (filter.lift f g) h = filter.lift f fun (s : set α) => filter.lift (g s) h := sorry

theorem lift_lift_same_le_lift {α : Type u_1} {β : Type u_2} {f : filter α} {g : set α → set α → filter β} : (filter.lift f fun (s : set α) => filter.lift f (g s)) ≤ filter.lift f fun (s : set α) => g s s := sorry

theorem lift_lift_same_eq_lift {α : Type u_1} {β : Type u_2} {f : filter α} {g : set α → set α → filter β} (hg₁ : ∀ (s : set α), monotone fun (t : set α) => g s t) (hg₂ : ∀ (t : set α), monotone fun (s : set α) => g s t) : (filter.lift f fun (s : set α) => filter.lift f (g s)) = filter.lift f fun (s : set α) => g s s := sorry

theorem lift_principal {α : Type u_1} {β : Type u_2} {g : set α → filter β} {s : set α} (hg : monotone g) : filter.lift (principal s) g = g s :=
  le_antisymm (infi_le_of_le s (infi_le (fun (H : s ∈ principal s) => g s) (set.subset.refl s)))
    (le_infi fun (t : set α) => le_infi fun (hi : t ∈ principal s) => hg hi)

theorem monotone_lift {α : Type u_1} {β : Type u_2} {γ : Type u_3} [preorder γ] {f : γ → filter α} {g : γ → set α → filter β} (hf : monotone f) (hg : monotone g) : monotone fun (c : γ) => filter.lift (f c) (g c) :=
  fun (a b : γ) (h : a ≤ b) => lift_mono (hf h) (hg h)

theorem lift_ne_bot_iff {α : Type u_1} {β : Type u_2} {f : filter α} {g : set α → filter β} (hm : monotone g) : ne_bot (filter.lift f g) ↔ ∀ (s : set α), s ∈ f → ne_bot (g s) := sorry

@[simp] theorem lift_const {α : Type u_1} {β : Type u_2} {f : filter α} {g : filter β} : (filter.lift f fun (x : set α) => g) = g :=
  le_antisymm (lift_le univ_mem_sets (le_refl g)) (le_lift fun (s : set α) (hs : s ∈ f) => le_refl g)

@[simp] theorem lift_inf {α : Type u_1} {β : Type u_2} {f : filter α} {g : set α → filter β} {h : set α → filter β} : (filter.lift f fun (x : set α) => g x ⊓ h x) = filter.lift f g ⊓ filter.lift f h := sorry

@[simp] theorem lift_principal2 {α : Type u_1} {f : filter α} : filter.lift f principal = f := sorry

theorem lift_infi {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {f : ι → filter α} {g : set α → filter β} [hι : Nonempty ι] (hg : ∀ {s t : set α}, g s ⊓ g t = g (s ∩ t)) : filter.lift (infi f) g = infi fun (i : ι) => filter.lift (f i) g := sorry

/-- Specialize `lift` to functions `set α → set β`. This can be viewed as a generalization of `map`.
This is essentially a push-forward along a function mapping each set to a set. -/
protected def lift' {α : Type u_1} {β : Type u_2} (f : filter α) (h : set α → set β) : filter β :=
  filter.lift f (principal ∘ h)

theorem mem_lift' {α : Type u_1} {β : Type u_2} {f : filter α} {h : set α → set β} {t : set α} (ht : t ∈ f) : h t ∈ filter.lift' f h :=
  iff.mp le_principal_iff
    ((fun (this : filter.lift' f h ≤ principal (h t)) => this)
      (infi_le_of_le t (infi_le_of_le ht (le_refl (function.comp principal h t)))))

theorem tendsto_lift' {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : filter α} {h : set α → set β} {m : γ → β} {l : filter γ} : tendsto m l (filter.lift' f h) ↔ ∀ (s : set α), s ∈ f → filter.eventually (fun (a : γ) => m a ∈ h s) l := sorry

theorem has_basis.lift' {α : Type u_1} {β : Type u_2} {f : filter α} {h : set α → set β} {ι : Type u_3} {p : ι → Prop} {s : ι → set α} (hf : has_basis f p s) (hh : monotone h) : has_basis (filter.lift' f h) p (h ∘ s) := sorry

theorem mem_lift'_sets {α : Type u_1} {β : Type u_2} {f : filter α} {h : set α → set β} (hh : monotone h) {s : set β} : s ∈ filter.lift' f h ↔ ∃ (t : set α), ∃ (H : t ∈ f), h t ⊆ s :=
  mem_lift_sets (monotone.comp monotone_principal hh)

theorem eventually_lift'_iff {α : Type u_1} {β : Type u_2} {f : filter α} {h : set α → set β} (hh : monotone h) {p : β → Prop} : filter.eventually (fun (y : β) => p y) (filter.lift' f h) ↔ ∃ (t : set α), ∃ (H : t ∈ f), ∀ (y : β), y ∈ h t → p y :=
  mem_lift'_sets hh

theorem lift'_le {α : Type u_1} {β : Type u_2} {f : filter α} {g : set α → set β} {h : filter β} {s : set α} (hs : s ∈ f) (hg : principal (g s) ≤ h) : filter.lift' f g ≤ h :=
  lift_le hs hg

theorem lift'_mono {α : Type u_1} {β : Type u_2} {f₁ : filter α} {f₂ : filter α} {h₁ : set α → set β} {h₂ : set α → set β} (hf : f₁ ≤ f₂) (hh : h₁ ≤ h₂) : filter.lift' f₁ h₁ ≤ filter.lift' f₂ h₂ :=
  lift_mono hf fun (s : set α) => iff.mpr principal_mono (hh s)

theorem lift'_mono' {α : Type u_1} {β : Type u_2} {f : filter α} {h₁ : set α → set β} {h₂ : set α → set β} (hh : ∀ (s : set α), s ∈ f → h₁ s ⊆ h₂ s) : filter.lift' f h₁ ≤ filter.lift' f h₂ :=
  infi_le_infi fun (s : set α) => infi_le_infi fun (hs : s ∈ f) => iff.mpr principal_mono (hh s hs)

theorem lift'_cong {α : Type u_1} {β : Type u_2} {f : filter α} {h₁ : set α → set β} {h₂ : set α → set β} (hh : ∀ (s : set α), s ∈ f → h₁ s = h₂ s) : filter.lift' f h₁ = filter.lift' f h₂ :=
  le_antisymm (lift'_mono' fun (s : set α) (hs : s ∈ f) => le_of_eq (hh s hs))
    (lift'_mono' fun (s : set α) (hs : s ∈ f) => le_of_eq (Eq.symm (hh s hs)))

theorem map_lift'_eq {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : filter α} {h : set α → set β} {m : β → γ} (hh : monotone h) : map m (filter.lift' f h) = filter.lift' f (set.image m ∘ h) := sorry

theorem map_lift'_eq2 {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : filter α} {g : set β → set γ} {m : α → β} (hg : monotone g) : filter.lift' (map m f) g = filter.lift' f (g ∘ set.image m) :=
  map_lift_eq2 (monotone.comp monotone_principal hg)

theorem comap_lift'_eq {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : filter α} {h : set α → set β} {m : γ → β} (hh : monotone h) : comap m (filter.lift' f h) = filter.lift' f (set.preimage m ∘ h) := sorry

theorem comap_lift'_eq2 {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : filter α} {m : β → α} {g : set β → set γ} (hg : monotone g) : filter.lift' (comap m f) g = filter.lift' f (g ∘ set.preimage m) :=
  comap_lift_eq2 (monotone.comp monotone_principal hg)

theorem lift'_principal {α : Type u_1} {β : Type u_2} {h : set α → set β} {s : set α} (hh : monotone h) : filter.lift' (principal s) h = principal (h s) :=
  lift_principal (monotone.comp monotone_principal hh)

theorem lift'_pure {α : Type u_1} {β : Type u_2} {h : set α → set β} {a : α} (hh : monotone h) : filter.lift' (pure a) h = principal (h (singleton a)) := sorry

theorem lift'_bot {α : Type u_1} {β : Type u_2} {h : set α → set β} (hh : monotone h) : filter.lift' ⊥ h = principal (h ∅) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (filter.lift' ⊥ h = principal (h ∅))) (Eq.symm principal_empty)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (filter.lift' (principal ∅) h = principal (h ∅))) (lift'_principal hh)))
      (Eq.refl (principal (h ∅))))

theorem principal_le_lift' {α : Type u_1} {β : Type u_2} {f : filter α} {h : set α → set β} {t : set β} (hh : ∀ (s : set α), s ∈ f → t ⊆ h s) : principal t ≤ filter.lift' f h :=
  le_infi fun (s : set α) => le_infi fun (hs : s ∈ f) => iff.mpr principal_mono (hh s hs)

theorem monotone_lift' {α : Type u_1} {β : Type u_2} {γ : Type u_3} [preorder γ] {f : γ → filter α} {g : γ → set α → set β} (hf : monotone f) (hg : monotone g) : monotone fun (c : γ) => filter.lift' (f c) (g c) :=
  fun (a b : γ) (h : a ≤ b) => lift'_mono (hf h) (hg h)

theorem lift_lift'_assoc {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : filter α} {g : set α → set β} {h : set β → filter γ} (hg : monotone g) (hh : monotone h) : filter.lift (filter.lift' f g) h = filter.lift f fun (s : set α) => h (g s) := sorry

theorem lift'_lift'_assoc {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : filter α} {g : set α → set β} {h : set β → set γ} (hg : monotone g) (hh : monotone h) : filter.lift' (filter.lift' f g) h = filter.lift' f fun (s : set α) => h (g s) :=
  lift_lift'_assoc hg (monotone.comp monotone_principal hh)

theorem lift'_lift_assoc {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : filter α} {g : set α → filter β} {h : set β → set γ} (hg : monotone g) : filter.lift' (filter.lift f g) h = filter.lift f fun (s : set α) => filter.lift' (g s) h :=
  lift_assoc hg

theorem lift_lift'_same_le_lift' {α : Type u_1} {β : Type u_2} {f : filter α} {g : set α → set α → set β} : (filter.lift f fun (s : set α) => filter.lift' f (g s)) ≤ filter.lift' f fun (s : set α) => g s s :=
  lift_lift_same_le_lift

theorem lift_lift'_same_eq_lift' {α : Type u_1} {β : Type u_2} {f : filter α} {g : set α → set α → set β} (hg₁ : ∀ (s : set α), monotone fun (t : set α) => g s t) (hg₂ : ∀ (t : set α), monotone fun (s : set α) => g s t) : (filter.lift f fun (s : set α) => filter.lift' f (g s)) = filter.lift' f fun (s : set α) => g s s :=
  lift_lift_same_eq_lift (fun (s : set α) => monotone.comp monotone_principal (hg₁ s))
    fun (t : set α) => monotone.comp monotone_principal (hg₂ t)

theorem lift'_inf_principal_eq {α : Type u_1} {β : Type u_2} {f : filter α} {h : set α → set β} {s : set β} : filter.lift' f h ⊓ principal s = filter.lift' f fun (t : set α) => h t ∩ s := sorry

theorem lift'_ne_bot_iff {α : Type u_1} {β : Type u_2} {f : filter α} {h : set α → set β} (hh : monotone h) : ne_bot (filter.lift' f h) ↔ ∀ (s : set α), s ∈ f → set.nonempty (h s) := sorry

@[simp] theorem lift'_id {α : Type u_1} {f : filter α} : filter.lift' f id = f :=
  lift_principal2

theorem le_lift' {α : Type u_1} {β : Type u_2} {f : filter α} {h : set α → set β} {g : filter β} (h_le : ∀ (s : set α), s ∈ f → h s ∈ g) : g ≤ filter.lift' f h := sorry

theorem lift_infi' {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {f : ι → filter α} {g : set α → filter β} [Nonempty ι] (hf : directed ge f) (hg : monotone g) : filter.lift (infi f) g = infi fun (i : ι) => filter.lift (f i) g := sorry

theorem lift'_infi {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {f : ι → filter α} {g : set α → set β} [Nonempty ι] (hg : ∀ {s t : set α}, g s ∩ g t = g (s ∩ t)) : filter.lift' (infi f) g = infi fun (i : ι) => filter.lift' (f i) g := sorry

theorem lift'_inf {α : Type u_1} {β : Type u_2} (f : filter α) (g : filter α) {s : set α → set β} (hs : ∀ {t₁ t₂ : set α}, s t₁ ∩ s t₂ = s (t₁ ∩ t₂)) : filter.lift' (f ⊓ g) s = filter.lift' f s ⊓ filter.lift' g s := sorry

theorem comap_eq_lift' {α : Type u_1} {β : Type u_2} {f : filter β} {m : α → β} : comap m f = filter.lift' f (set.preimage m) :=
  filter.ext fun (s : set α) => iff.symm (mem_lift'_sets set.monotone_preimage)

theorem lift'_infi_powerset {α : Type u_1} {ι : Sort u_4} [Nonempty ι] {f : ι → filter α} : filter.lift' (infi f) set.powerset = infi fun (i : ι) => filter.lift' (f i) set.powerset :=
  lift'_infi fun (_x _x_1 : set α) => Eq.symm (set.powerset_inter _x _x_1)

theorem lift'_inf_powerset {α : Type u_1} (f : filter α) (g : filter α) : filter.lift' (f ⊓ g) set.powerset = filter.lift' f set.powerset ⊓ filter.lift' g set.powerset :=
  lift'_inf f g fun (_x _x_1 : set α) => Eq.symm (set.powerset_inter _x _x_1)

theorem eventually_lift'_powerset {α : Type u_1} {f : filter α} {p : set α → Prop} : filter.eventually (fun (s : set α) => p s) (filter.lift' f set.powerset) ↔
  ∃ (s : set α), ∃ (H : s ∈ f), ∀ (t : set α), t ⊆ s → p t :=
  eventually_lift'_iff set.monotone_powerset

theorem eventually_lift'_powerset' {α : Type u_1} {f : filter α} {p : set α → Prop} (hp : ∀ {s t : set α}, s ⊆ t → p t → p s) : filter.eventually (fun (s : set α) => p s) (filter.lift' f set.powerset) ↔ ∃ (s : set α), ∃ (H : s ∈ f), p s := sorry

protected instance lift'_powerset_ne_bot {α : Type u_1} (f : filter α) : ne_bot (filter.lift' f set.powerset) :=
  iff.mpr (lift'_ne_bot_iff set.monotone_powerset) fun (_x : set α) (_x_1 : _x ∈ f) => set.powerset_nonempty

theorem tendsto_lift'_powerset_mono {α : Type u_1} {β : Type u_2} {la : filter α} {lb : filter β} {s : α → set β} {t : α → set β} (ht : tendsto t la (filter.lift' lb set.powerset)) (hst : filter.eventually (fun (x : α) => s x ⊆ t x) la) : tendsto s la (filter.lift' lb set.powerset) := sorry

@[simp] theorem eventually_lift'_powerset_forall {α : Type u_1} {f : filter α} {p : α → Prop} : filter.eventually (fun (s : set α) => ∀ (x : α), x ∈ s → p x) (filter.lift' f set.powerset) ↔
  filter.eventually (fun (x : α) => p x) f := sorry

theorem eventually.lift'_powerset {α : Type u_1} {f : filter α} {p : α → Prop} : filter.eventually (fun (x : α) => p x) f →
  filter.eventually (fun (s : set α) => ∀ (x : α), x ∈ s → p x) (filter.lift' f set.powerset) :=
  iff.mpr eventually_lift'_powerset_forall

@[simp] theorem eventually_lift'_powerset_eventually {α : Type u_1} {f : filter α} {g : filter α} {p : α → Prop} : filter.eventually (fun (s : set α) => filter.eventually (fun (x : α) => x ∈ s → p x) g) (filter.lift' f set.powerset) ↔
  filter.eventually (fun (x : α) => p x) (f ⊓ g) := sorry

theorem prod_def {α : Type u_1} {β : Type u_2} {f : filter α} {g : filter β} : filter.prod f g = filter.lift f fun (s : set α) => filter.lift' g (set.prod s) := sorry

theorem prod_same_eq {α : Type u_1} {f : filter α} : filter.prod f f = filter.lift' f fun (t : set α) => set.prod t t :=
  eq.mpr (id (Eq._oldrec (Eq.refl (filter.prod f f = filter.lift' f fun (t : set α) => set.prod t t)) prod_def))
    (lift_lift'_same_eq_lift' (fun (s : set α) => set.monotone_prod monotone_const monotone_id)
      fun (t : set α) => set.monotone_prod monotone_id monotone_const)

theorem mem_prod_same_iff {α : Type u_1} {f : filter α} {s : set (α × α)} : s ∈ filter.prod f f ↔ ∃ (t : set α), ∃ (H : t ∈ f), set.prod t t ⊆ s := sorry

theorem tendsto_prod_self_iff {α : Type u_1} {β : Type u_2} {f : α × α → β} {x : filter α} {y : filter β} : tendsto f (filter.prod x x) y ↔
  ∀ (W : set β) (H : W ∈ y), ∃ (U : set α), ∃ (H : U ∈ x), ∀ (x x' : α), x ∈ U → x' ∈ U → f (x, x') ∈ W := sorry

theorem prod_lift_lift {α₁ : Type u_5} {α₂ : Type u_6} {β₁ : Type u_7} {β₂ : Type u_8} {f₁ : filter α₁} {f₂ : filter α₂} {g₁ : set α₁ → filter β₁} {g₂ : set α₂ → filter β₂} (hg₁ : monotone g₁) (hg₂ : monotone g₂) : filter.prod (filter.lift f₁ g₁) (filter.lift f₂ g₂) =
  filter.lift f₁ fun (s : set α₁) => filter.lift f₂ fun (t : set α₂) => filter.prod (g₁ s) (g₂ t) := sorry

theorem prod_lift'_lift' {α₁ : Type u_5} {α₂ : Type u_6} {β₁ : Type u_7} {β₂ : Type u_8} {f₁ : filter α₁} {f₂ : filter α₂} {g₁ : set α₁ → set β₁} {g₂ : set α₂ → set β₂} (hg₁ : monotone g₁) (hg₂ : monotone g₂) : filter.prod (filter.lift' f₁ g₁) (filter.lift' f₂ g₂) =
  filter.lift f₁ fun (s : set α₁) => filter.lift' f₂ fun (t : set α₂) => set.prod (g₁ s) (g₂ t) := sorry

