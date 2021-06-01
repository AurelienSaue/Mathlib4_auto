/-
Copyright (c) 2020 Thomas Browning and Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning and Patrick Lutz
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.field_theory.intermediate_field
import Mathlib.field_theory.splitting_field
import Mathlib.field_theory.separable
import Mathlib.PostPort

universes u_1 u_2 u_3 l 

namespace Mathlib

/-!
# Adjoining Elements to Fields

In this file we introduce the notion of adjoining elements to fields.
This isn't quite the same as adjoining elements to rings.
For example, `algebra.adjoin K {x}` might not include `x⁻¹`.

## Main results

- `adjoin_adjoin_left`: adjoining S and then T is the same as adjoining `S ∪ T`.
- `bot_eq_top_of_dim_adjoin_eq_one`: if `F⟮x⟯` has dimension `1` over `F` for every `x`
  in `E` then `F = E`

## Notation

 - `F⟮α⟯`: adjoin a single element `α` to `F`.
-/

namespace intermediate_field


/-- `adjoin F S` extends a field `F` by adjoining a set `S ⊆ E`. -/
def adjoin (F : Type u_1) [field F] {E : Type u_2} [field E] [algebra F E] (S : set E) :
    intermediate_field F E :=
  mk (subfield.carrier (subfield.closure (set.range ⇑(algebra_map F E) ∪ S))) sorry sorry sorry
    sorry sorry sorry sorry

@[simp] theorem adjoin_le_iff {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E]
    {S : set E} {T : intermediate_field F E} : adjoin F S ≤ T ↔ S ≤ ↑T :=
  sorry

theorem gc {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E] :
    galois_connection (adjoin F) coe :=
  fun (_x : set E) (_x_1 : intermediate_field F E) => adjoin_le_iff

/-- Galois insertion between `adjoin` and `coe`. -/
def gi {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E] :
    galois_insertion (adjoin F) coe :=
  galois_insertion.mk (fun (S : set E) (_x : ↑(adjoin F S) ≤ S) => adjoin F S) gc sorry sorry

protected instance complete_lattice {F : Type u_1} [field F] {E : Type u_2} [field E]
    [algebra F E] : complete_lattice (intermediate_field F E) :=
  galois_insertion.lift_complete_lattice gi

protected instance inhabited {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E] :
    Inhabited (intermediate_field F E) :=
  { default := ⊤ }

theorem mem_bot {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E] {x : E} :
    x ∈ ⊥ ↔ x ∈ set.range ⇑(algebra_map F E) :=
  sorry

theorem mem_top {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E] {x : E} : x ∈ ⊤ :=
  subfield.subset_closure (Or.inr trivial)

@[simp] theorem bot_to_subalgebra {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E] :
    to_subalgebra ⊥ = ⊥ :=
  sorry

@[simp] theorem top_to_subalgebra {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E] :
    to_subalgebra ⊤ = ⊤ :=
  sorry

/--  Construct an algebra isomorphism from an equality of subalgebras -/
def subalgebra.equiv_of_eq {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E]
    {X : subalgebra F E} {Y : subalgebra F E} (h : X = Y) : alg_equiv F ↥X ↥Y :=
  alg_equiv.mk (fun (x : ↥X) => { val := ↑x, property := sorry })
    (fun (x : ↥Y) => { val := ↑x, property := sorry }) sorry sorry sorry sorry sorry

/-- The bottom intermediate_field is isomorphic to the field. -/
def bot_equiv {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E] :
    alg_equiv F (↥⊥) F :=
  alg_equiv.trans (subalgebra.equiv_of_eq bot_to_subalgebra) (algebra.bot_equiv F E)

@[simp] theorem bot_equiv_def {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E]
    (x : F) : coe_fn bot_equiv (coe_fn (algebra_map F ↥⊥) x) = x :=
  alg_equiv.commutes bot_equiv x

protected instance algebra_over_bot {F : Type u_1} [field F] {E : Type u_2} [field E]
    [algebra F E] : algebra (↥⊥) F :=
  ring_hom.to_algebra (alg_hom.to_ring_hom (alg_equiv.to_alg_hom bot_equiv))

protected instance is_scalar_tower_over_bot {F : Type u_1} [field F] {E : Type u_2} [field E]
    [algebra F E] : is_scalar_tower (↥⊥) F E :=
  is_scalar_tower.of_algebra_map_eq
    fun (x : ↥⊥) =>
      let ϕ : alg_hom F F ↥⊥ := algebra.of_id F ↥⊥;
      let ψ : alg_equiv F F ↥⊥ :=
        alg_equiv.of_bijective ϕ (alg_equiv.bijective (alg_equiv.symm (algebra.bot_equiv F E)));
      id
        (eq.mpr
          (id
            (Eq._oldrec
              (Eq.refl
                (↑x =
                  ↑(coe_fn ψ
                      (coe_fn (alg_equiv.symm ψ)
                        { val := ↑x,
                          property := subalgebra.equiv_of_eq._proof_1 bot_to_subalgebra x }))))
              (alg_equiv.apply_symm_apply ψ
                { val := ↑x, property := subalgebra.equiv_of_eq._proof_1 bot_to_subalgebra x })))
          (Eq.refl ↑x))

/-- The top intermediate_field is isomorphic to the field. -/
def top_equiv {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E] :
    alg_equiv F (↥⊤) E :=
  alg_equiv.trans (subalgebra.equiv_of_eq top_to_subalgebra) algebra.top_equiv

@[simp] theorem top_equiv_def {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E]
    (x : ↥⊤) : coe_fn top_equiv x = ↑x :=
  sorry

@[simp] theorem coe_bot_eq_self {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E]
    (K : intermediate_field F E) : ↑⊥ = K :=
  sorry

@[simp] theorem coe_top_eq_top {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E]
    (K : intermediate_field F E) : ↑⊤ = ⊤ :=
  iff.mpr intermediate_field.ext'_iff
    (iff.mpr set.ext_iff fun (_x : E) => iff_of_true mem_top mem_top)

theorem adjoin_eq_range_algebra_map_adjoin (F : Type u_1) [field F] {E : Type u_2} [field E]
    [algebra F E] (S : set E) : ↑(adjoin F S) = set.range ⇑(algebra_map (↥(adjoin F S)) E) :=
  Eq.symm subtype.range_coe

theorem adjoin.algebra_map_mem (F : Type u_1) [field F] {E : Type u_2} [field E] [algebra F E]
    (S : set E) (x : F) : coe_fn (algebra_map F E) x ∈ adjoin F S :=
  algebra_map_mem (adjoin F S) x

theorem adjoin.range_algebra_map_subset (F : Type u_1) [field F] {E : Type u_2} [field E]
    [algebra F E] (S : set E) : set.range ⇑(algebra_map F E) ⊆ ↑(adjoin F S) :=
  sorry

protected instance adjoin.field_coe (F : Type u_1) [field F] {E : Type u_2} [field E] [algebra F E]
    (S : set E) : has_coe_t F ↥(adjoin F S) :=
  has_coe_t.mk
    fun (x : F) => { val := coe_fn (algebra_map F E) x, property := adjoin.algebra_map_mem F S x }

theorem subset_adjoin (F : Type u_1) [field F] {E : Type u_2} [field E] [algebra F E] (S : set E) :
    S ⊆ ↑(adjoin F S) :=
  fun (x : E) (hx : x ∈ S) => subfield.subset_closure (Or.inr hx)

protected instance adjoin.set_coe (F : Type u_1) [field F] {E : Type u_2} [field E] [algebra F E]
    (S : set E) : has_coe_t ↥S ↥(adjoin F S) :=
  has_coe_t.mk fun (x : ↥S) => { val := ↑x, property := sorry }

theorem adjoin.mono (F : Type u_1) [field F] {E : Type u_2} [field E] [algebra F E] (S : set E)
    (T : set E) (h : S ⊆ T) : adjoin F S ≤ adjoin F T :=
  galois_connection.monotone_l gc h

theorem adjoin_contains_field_as_subfield {E : Type u_2} [field E] (S : set E) (F : subfield E) :
    ↑F ⊆ ↑(adjoin (↥F) S) :=
  fun (x : E) (hx : x ∈ ↑F) => adjoin.algebra_map_mem (↥F) S { val := x, property := hx }

theorem subset_adjoin_of_subset_left {E : Type u_2} [field E] (S : set E) {F : subfield E}
    {T : set E} (HT : T ⊆ ↑F) : T ⊆ ↑(adjoin (↥F) S) :=
  fun (x : E) (hx : x ∈ T) => algebra_map_mem (adjoin (↥F) S) { val := x, property := HT hx }

theorem subset_adjoin_of_subset_right (F : Type u_1) [field F] {E : Type u_2} [field E]
    [algebra F E] (S : set E) {T : set E} (H : T ⊆ S) : T ⊆ ↑(adjoin F S) :=
  fun (x : E) (hx : x ∈ T) => subset_adjoin F S (H hx)

@[simp] theorem adjoin_empty (F : Type u_1) (E : Type u_2) [field F] [field E] [algebra F E] :
    adjoin F ∅ = ⊥ :=
  iff.mpr eq_bot_iff (iff.mpr adjoin_le_iff (set.empty_subset ↑⊥))

/-- If `K` is a field with `F ⊆ K` and `S ⊆ K` then `adjoin F S ≤ K`. -/
theorem adjoin_le_subfield (F : Type u_1) [field F] {E : Type u_2} [field E] [algebra F E]
    (S : set E) {K : subfield E} (HF : set.range ⇑(algebra_map F E) ⊆ ↑K) (HS : S ⊆ ↑K) :
    to_subfield (adjoin F S) ≤ K :=
  iff.mpr subfield.closure_le
    (eq.mpr
      (id
        (Eq._oldrec (Eq.refl (set.range ⇑(algebra_map F E) ∪ S ⊆ ↑K))
          (propext set.union_subset_iff)))
      { left := HF, right := HS })

theorem adjoin_subset_adjoin_iff (F : Type u_1) [field F] {E : Type u_2} [field E] [algebra F E]
    {F' : Type u_3} [field F'] [algebra F' E] {S : set E} {S' : set E} :
    ↑(adjoin F S) ⊆ ↑(adjoin F' S') ↔
        set.range ⇑(algebra_map F E) ⊆ ↑(adjoin F' S') ∧ S ⊆ ↑(adjoin F' S') :=
  sorry

/-- `F[S][T] = F[S ∪ T]` -/
theorem adjoin_adjoin_left (F : Type u_1) [field F] {E : Type u_2} [field E] [algebra F E]
    (S : set E) (T : set E) : ↑(adjoin (↥(adjoin F S)) T) = adjoin F (S ∪ T) :=
  sorry

@[simp] theorem adjoin_insert_adjoin (F : Type u_1) [field F] {E : Type u_2} [field E] [algebra F E]
    (S : set E) (x : E) : adjoin F (insert x ↑(adjoin F S)) = adjoin F (insert x S) :=
  sorry

/-- `F[S][T] = F[T][S]` -/
theorem adjoin_adjoin_comm (F : Type u_1) [field F] {E : Type u_2} [field E] [algebra F E]
    (S : set E) (T : set E) : ↑(adjoin (↥(adjoin F S)) T) = ↑(adjoin (↥(adjoin F T)) S) :=
  sorry

theorem adjoin_map (F : Type u_1) [field F] {E : Type u_2} [field E] [algebra F E] (S : set E)
    {E' : Type u_3} [field E'] [algebra F E'] (f : alg_hom F E E') :
    map (adjoin F S) f = adjoin F (⇑f '' S) :=
  sorry

theorem algebra_adjoin_le_adjoin (F : Type u_1) [field F] {E : Type u_2} [field E] [algebra F E]
    (S : set E) : algebra.adjoin F S ≤ to_subalgebra (adjoin F S) :=
  algebra.adjoin_le (subset_adjoin F S)

theorem adjoin_eq_algebra_adjoin (F : Type u_1) [field F] {E : Type u_2} [field E] [algebra F E]
    (S : set E) (inv_mem : ∀ (x : E), x ∈ algebra.adjoin F S → x⁻¹ ∈ algebra.adjoin F S) :
    to_subalgebra (adjoin F S) = algebra.adjoin F S :=
  sorry

theorem eq_adjoin_of_eq_algebra_adjoin (F : Type u_1) [field F] {E : Type u_2} [field E]
    [algebra F E] (S : set E) (K : intermediate_field F E)
    (h : to_subalgebra K = algebra.adjoin F S) : K = adjoin F S :=
  sorry

theorem adjoin_induction (F : Type u_1) [field F] {E : Type u_2} [field E] [algebra F E] {s : set E}
    {p : E → Prop} {x : E} (h : x ∈ adjoin F s) (Hs : ∀ (x : E), x ∈ s → p x)
    (Hmap : ∀ (x : F), p (coe_fn (algebra_map F E) x)) (Hadd : ∀ (x y : E), p x → p y → p (x + y))
    (Hneg : ∀ (x : E), p x → p (-x)) (Hinv : ∀ (x : E), p x → p (x⁻¹))
    (Hmul : ∀ (x y : E), p x → p y → p (x * y)) : p x :=
  sorry

/--
Variation on `set.insert` to enable good notation for adjoining elements to fields.
Used to preferentially use `singleton` rather than `insert` when adjoining one element.
-/
--this definition of notation is courtesy of Kyle Miller on zulip

class insert {α : Type u_3} (s : set α) where
  insert : α → set α

protected instance insert_empty {α : Type u_1} : insert ∅ := insert.mk fun (x : α) => singleton x

protected instance insert_nonempty {α : Type u_1} (s : set α) : insert s :=
  insert.mk fun (x : α) => set.insert x s

theorem mem_adjoin_simple_self (F : Type u_1) [field F] {E : Type u_2} [field E] [algebra F E]
    (α : E) : α ∈ adjoin F (insert.insert ∅ α) :=
  subset_adjoin F (singleton α) (set.mem_singleton α)

/-- generator of `F⟮α⟯` -/
def adjoin_simple.gen (F : Type u_1) [field F] {E : Type u_2} [field E] [algebra F E] (α : E) :
    ↥(adjoin F (insert.insert ∅ α)) :=
  { val := α, property := mem_adjoin_simple_self F α }

@[simp] theorem adjoin_simple.algebra_map_gen (F : Type u_1) [field F] {E : Type u_2} [field E]
    [algebra F E] (α : E) :
    coe_fn (algebra_map (↥(adjoin F (insert.insert ∅ α))) E) (adjoin_simple.gen F α) = α :=
  rfl

theorem adjoin_simple_adjoin_simple (F : Type u_1) [field F] {E : Type u_2} [field E] [algebra F E]
    (α : E) (β : E) :
    ↑(adjoin (↥(adjoin F (insert.insert ∅ α))) (insert.insert ∅ β)) =
        adjoin F (insert.insert (insert.insert ∅ β) α) :=
  adjoin_adjoin_left F (insert.insert ∅ α) (insert.insert ∅ β)

theorem adjoin_simple_comm (F : Type u_1) [field F] {E : Type u_2} [field E] [algebra F E] (α : E)
    (β : E) :
    ↑(adjoin (↥(adjoin F (insert.insert ∅ α))) (insert.insert ∅ β)) =
        ↑(adjoin (↥(adjoin F (insert.insert ∅ β))) (insert.insert ∅ α)) :=
  adjoin_adjoin_comm F (insert.insert ∅ α) (insert.insert ∅ β)

-- TODO: develop the API for `subalgebra.is_field_of_algebraic` so it can be used here

theorem adjoin_simple_to_subalgebra_of_integral (F : Type u_1) [field F] {E : Type u_2} [field E]
    [algebra F E] (α : E) (hα : is_integral F α) :
    to_subalgebra (adjoin F (insert.insert ∅ α)) = algebra.adjoin F (singleton α) :=
  sorry

@[simp] theorem adjoin_eq_bot_iff {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E]
    {S : set E} : adjoin F S = ⊥ ↔ S ⊆ ↑⊥ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (adjoin F S = ⊥ ↔ S ⊆ ↑⊥)) (propext eq_bot_iff)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (adjoin F S ≤ ⊥ ↔ S ⊆ ↑⊥)) (propext adjoin_le_iff)))
      (iff.refl (S ≤ ↑⊥)))

@[simp] theorem adjoin_simple_eq_bot_iff {F : Type u_1} [field F] {E : Type u_2} [field E]
    [algebra F E] {α : E} : adjoin F (insert.insert ∅ α) = ⊥ ↔ α ∈ ⊥ :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (adjoin F (insert.insert ∅ α) = ⊥ ↔ α ∈ ⊥)) (propext adjoin_eq_bot_iff)))
    set.singleton_subset_iff

@[simp] theorem adjoin_zero {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E] :
    adjoin F (insert.insert ∅ 0) = ⊥ :=
  iff.mpr adjoin_simple_eq_bot_iff (zero_mem ⊥)

@[simp] theorem adjoin_one {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E] :
    adjoin F (insert.insert ∅ 1) = ⊥ :=
  iff.mpr adjoin_simple_eq_bot_iff (one_mem ⊥)

@[simp] theorem adjoin_int {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E] (n : ℤ) :
    adjoin F (insert.insert ∅ ↑n) = ⊥ :=
  iff.mpr adjoin_simple_eq_bot_iff (coe_int_mem ⊥ n)

@[simp] theorem adjoin_nat {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E] (n : ℕ) :
    adjoin F (insert.insert ∅ ↑n) = ⊥ :=
  iff.mpr adjoin_simple_eq_bot_iff (coe_int_mem ⊥ ↑n)

@[simp] theorem dim_eq_one_iff {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E]
    {K : intermediate_field F E} : vector_space.dim F ↥K = 1 ↔ K = ⊥ :=
  sorry

@[simp] theorem findim_eq_one_iff {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E]
    {K : intermediate_field F E} : finite_dimensional.findim F ↥K = 1 ↔ K = ⊥ :=
  sorry

theorem dim_adjoin_eq_one_iff {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E]
    {S : set E} : vector_space.dim F ↥(adjoin F S) = 1 ↔ S ⊆ ↑⊥ :=
  iff.trans dim_eq_one_iff adjoin_eq_bot_iff

theorem dim_adjoin_simple_eq_one_iff {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E]
    {α : E} : vector_space.dim F ↥(adjoin F (insert.insert ∅ α)) = 1 ↔ α ∈ ⊥ :=
  sorry

theorem findim_adjoin_eq_one_iff {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E]
    {S : set E} : finite_dimensional.findim F ↥(adjoin F S) = 1 ↔ S ⊆ ↑⊥ :=
  iff.trans findim_eq_one_iff adjoin_eq_bot_iff

theorem findim_adjoin_simple_eq_one_iff {F : Type u_1} [field F] {E : Type u_2} [field E]
    [algebra F E] {α : E} :
    finite_dimensional.findim F ↥(adjoin F (insert.insert ∅ α)) = 1 ↔ α ∈ ⊥ :=
  sorry

/-- If `F⟮x⟯` has dimension `1` over `F` for every `x ∈ E` then `F = E`. -/
theorem bot_eq_top_of_dim_adjoin_eq_one {F : Type u_1} [field F] {E : Type u_2} [field E]
    [algebra F E] (h : ∀ (x : E), vector_space.dim F ↥(adjoin F (insert.insert ∅ x)) = 1) : ⊥ = ⊤ :=
  sorry

theorem bot_eq_top_of_findim_adjoin_eq_one {F : Type u_1} [field F] {E : Type u_2} [field E]
    [algebra F E] (h : ∀ (x : E), finite_dimensional.findim F ↥(adjoin F (insert.insert ∅ x)) = 1) :
    ⊥ = ⊤ :=
  sorry

theorem subsingleton_of_dim_adjoin_eq_one {F : Type u_1} [field F] {E : Type u_2} [field E]
    [algebra F E] (h : ∀ (x : E), vector_space.dim F ↥(adjoin F (insert.insert ∅ x)) = 1) :
    subsingleton (intermediate_field F E) :=
  subsingleton_of_bot_eq_top (bot_eq_top_of_dim_adjoin_eq_one h)

theorem subsingleton_of_findim_adjoin_eq_one {F : Type u_1} [field F] {E : Type u_2} [field E]
    [algebra F E] (h : ∀ (x : E), finite_dimensional.findim F ↥(adjoin F (insert.insert ∅ x)) = 1) :
    subsingleton (intermediate_field F E) :=
  subsingleton_of_bot_eq_top (bot_eq_top_of_findim_adjoin_eq_one h)

/-- If `F⟮x⟯` has dimension `≤1` over `F` for every `x ∈ E` then `F = E`. -/
theorem bot_eq_top_of_findim_adjoin_le_one {F : Type u_1} [field F] {E : Type u_2} [field E]
    [algebra F E] [finite_dimensional F E]
    (h : ∀ (x : E), finite_dimensional.findim F ↥(adjoin F (insert.insert ∅ x)) ≤ 1) : ⊥ = ⊤ :=
  sorry

theorem subsingleton_of_findim_adjoin_le_one {F : Type u_1} [field F] {E : Type u_2} [field E]
    [algebra F E] [finite_dimensional F E]
    (h : ∀ (x : E), finite_dimensional.findim F ↥(adjoin F (insert.insert ∅ x)) ≤ 1) :
    subsingleton (intermediate_field F E) :=
  subsingleton_of_bot_eq_top (bot_eq_top_of_findim_adjoin_le_one h)

theorem aeval_gen_minpoly (F : Type u_1) [field F] {E : Type u_2} [field E] [algebra F E] (α : E) :
    coe_fn (polynomial.aeval (adjoin_simple.gen F α)) (minpoly F α) = 0 :=
  sorry

/-- algebra isomorphism between `adjoin_root` and `F⟮α⟯` -/
def adjoin_root_equiv_adjoin (F : Type u_1) [field F] {E : Type u_2} [field E] [algebra F E] {α : E}
    (h : is_integral F α) :
    alg_equiv F (adjoin_root (minpoly F α)) ↥(adjoin F (insert.insert ∅ α)) :=
  alg_equiv.of_bijective
    (alg_hom.mk
      ⇑(adjoin_root.lift (algebra_map F ↥(adjoin F (insert.insert ∅ α))) (adjoin_simple.gen F α)
          (aeval_gen_minpoly F α))
      sorry sorry sorry sorry sorry)
    sorry

theorem adjoin_root_equiv_adjoin_apply_root (F : Type u_1) [field F] {E : Type u_2} [field E]
    [algebra F E] {α : E} (h : is_integral F α) :
    coe_fn (adjoin_root_equiv_adjoin F h) (adjoin_root.root (minpoly F α)) =
        adjoin_simple.gen F α :=
  adjoin_root.lift_root

/-- Algebra homomorphism `F⟮α⟯ →ₐ[F] K` are in bijection with the set of roots
of `minpoly α` in `K`. -/
def alg_hom_adjoin_integral_equiv (F : Type u_1) [field F] {E : Type u_2} [field E] [algebra F E]
    {α : E} {K : Type u_3} [field K] [algebra F K] (h : is_integral F α) :
    alg_hom F (↥(adjoin F (insert.insert ∅ α))) K ≃
        Subtype
          fun (x : K) => x ∈ polynomial.roots (polynomial.map (algebra_map F K) (minpoly F α)) :=
  let ϕ : alg_equiv F (adjoin_root (minpoly F α)) ↥(adjoin F (insert.insert ∅ α)) :=
    adjoin_root_equiv_adjoin F h;
  let swap1 :
    alg_hom F (↥(adjoin F (insert.insert ∅ α))) K ≃ alg_hom F (adjoin_root (minpoly F α)) K :=
    equiv.mk
      (fun (f : alg_hom F (↥(adjoin F (insert.insert ∅ α))) K) =>
        alg_hom.comp f (alg_equiv.to_alg_hom ϕ))
      (fun (f : alg_hom F (adjoin_root (minpoly F α)) K) =>
        alg_hom.comp f (alg_equiv.to_alg_hom (alg_equiv.symm ϕ)))
      sorry sorry;
  let swap2 :
    alg_hom F (adjoin_root (minpoly F α)) K ≃
      Subtype
        fun (x : K) => x ∈ polynomial.roots (polynomial.map (algebra_map F K) (minpoly F α)) :=
    adjoin_root.equiv F K (minpoly F α) sorry;
  equiv.trans swap1 swap2

/-- Fintype of algebra homomorphism `F⟮α⟯ →ₐ[F] K` -/
def fintype_of_alg_hom_adjoin_integral (F : Type u_1) [field F] {E : Type u_2} [field E]
    [algebra F E] {α : E} {K : Type u_3} [field K] [algebra F K] (h : is_integral F α) :
    fintype (alg_hom F (↥(adjoin F (insert.insert ∅ α))) K) :=
  fintype.of_equiv
    (Subtype fun (x : K) => x ∈ polynomial.roots (polynomial.map (algebra_map F K) (minpoly F α)))
    (equiv.symm (alg_hom_adjoin_integral_equiv F h))

theorem card_alg_hom_adjoin_integral (F : Type u_1) [field F] {E : Type u_2} [field E] [algebra F E]
    {α : E} {K : Type u_3} [field K] [algebra F K] (h : is_integral F α)
    (h_sep : polynomial.separable (minpoly F α))
    (h_splits : polynomial.splits (algebra_map F K) (minpoly F α)) :
    fintype.card (alg_hom F (↥(adjoin F (insert.insert ∅ α))) K) =
        polynomial.nat_degree (minpoly F α) :=
  sorry

/-- An intermediate field `S` is finitely generated if there exists `t : finset E` such that
`intermediate_field.adjoin F t = S`. -/
def fg {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E]
    (S : intermediate_field F E) :=
  ∃ (t : finset E), adjoin F ↑t = S

theorem fg_adjoin_finset {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E]
    (t : finset E) : fg (adjoin F ↑t) :=
  Exists.intro t rfl

theorem fg_def {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E]
    {S : intermediate_field F E} : fg S ↔ ∃ (t : set E), set.finite t ∧ adjoin F t = S :=
  sorry

theorem fg_bot {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E] : fg ⊥ :=
  Exists.intro ∅ (adjoin_empty F E)

theorem fg_of_fg_to_subalgebra {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E]
    (S : intermediate_field F E) (h : subalgebra.fg (to_subalgebra S)) : fg S :=
  Exists.dcases_on h
    fun (t : finset E) (ht : algebra.adjoin F ↑t = to_subalgebra S) =>
      Exists.intro t (Eq.symm (eq_adjoin_of_eq_algebra_adjoin F (↑t) S (Eq.symm ht)))

theorem fg_of_noetherian {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E]
    (S : intermediate_field F E) [is_noetherian F E] : fg S :=
  fg_of_fg_to_subalgebra S (subalgebra.fg_of_noetherian (to_subalgebra S))

theorem induction_on_adjoin_finset {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E]
    (S : finset E) (P : intermediate_field F E → Prop) (base : P ⊥)
    (ih :
      ∀ (K : intermediate_field F E) (x : E), x ∈ S → P K → P ↑(adjoin (↥K) (insert.insert ∅ x))) :
    P (adjoin F ↑S) :=
  sorry

theorem induction_on_adjoin_fg {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E]
    (P : intermediate_field F E → Prop) (base : P ⊥)
    (ih : ∀ (K : intermediate_field F E) (x : E), P K → P ↑(adjoin (↥K) (insert.insert ∅ x)))
    (K : intermediate_field F E) (hK : fg K) : P K :=
  sorry

theorem induction_on_adjoin {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E]
    [fd : finite_dimensional F E] (P : intermediate_field F E → Prop) (base : P ⊥)
    (ih : ∀ (K : intermediate_field F E) (x : E), P K → P ↑(adjoin (↥K) (insert.insert ∅ x)))
    (K : intermediate_field F E) : P K :=
  induction_on_adjoin_fg P base ih K (fg_of_noetherian K)

/-- Lifts `L → K` of `F → K` -/
def lifts (F : Type u_1) (E : Type u_2) (K : Type u_3) [field F] [field E] [field K] [algebra F E]
    [algebra F K] :=
  sigma fun (L : intermediate_field F E) => alg_hom F (↥L) K

protected instance lifts.order_bot {F : Type u_1} {E : Type u_2} {K : Type u_3} [field F] [field E]
    [field K] [algebra F E] [algebra F K] : order_bot (lifts F E K) :=
  order_bot.mk (sigma.mk ⊥ (alg_hom.comp (algebra.of_id F K) (alg_equiv.to_alg_hom bot_equiv)))
    (fun (x y : lifts F E K) =>
      sigma.fst x ≤ sigma.fst y ∧
        ∀ (s : ↥(sigma.fst x)) (t : ↥(sigma.fst y)),
          ↑s = ↑t → coe_fn (sigma.snd x) s = coe_fn (sigma.snd y) t)
    (partial_order.lt._default
      fun (x y : lifts F E K) =>
        sigma.fst x ≤ sigma.fst y ∧
          ∀ (s : ↥(sigma.fst x)) (t : ↥(sigma.fst y)),
            ↑s = ↑t → coe_fn (sigma.snd x) s = coe_fn (sigma.snd y) t)
    sorry sorry sorry sorry

protected instance lifts.inhabited {F : Type u_1} {E : Type u_2} {K : Type u_3} [field F] [field E]
    [field K] [algebra F E] [algebra F K] : Inhabited (lifts F E K) :=
  { default := ⊥ }

theorem lifts.eq_of_le {F : Type u_1} {E : Type u_2} {K : Type u_3} [field F] [field E] [field K]
    [algebra F E] [algebra F K] {x : lifts F E K} {y : lifts F E K} (hxy : x ≤ y)
    (s : ↥(sigma.fst x)) :
    coe_fn (sigma.snd x) s =
        coe_fn (sigma.snd y) { val := ↑s, property := and.left hxy (↑s) (subtype.mem s) } :=
  and.right hxy s { val := ↑s, property := and.left hxy (↑s) (subtype.mem s) } rfl

theorem lifts.exists_max_two {F : Type u_1} {E : Type u_2} {K : Type u_3} [field F] [field E]
    [field K] [algebra F E] [algebra F K] {c : set (lifts F E K)} {x : lifts F E K}
    {y : lifts F E K} (hc : zorn.chain LessEq c) (hx : x ∈ set.insert ⊥ c)
    (hy : y ∈ set.insert ⊥ c) : ∃ (z : lifts F E K), z ∈ set.insert ⊥ c ∧ x ≤ z ∧ y ≤ z :=
  sorry

theorem lifts.exists_max_three {F : Type u_1} {E : Type u_2} {K : Type u_3} [field F] [field E]
    [field K] [algebra F E] [algebra F K] {c : set (lifts F E K)} {x : lifts F E K}
    {y : lifts F E K} {z : lifts F E K} (hc : zorn.chain LessEq c) (hx : x ∈ set.insert ⊥ c)
    (hy : y ∈ set.insert ⊥ c) (hz : z ∈ set.insert ⊥ c) :
    ∃ (w : lifts F E K), w ∈ set.insert ⊥ c ∧ x ≤ w ∧ y ≤ w ∧ z ≤ w :=
  sorry

/-- An upper bound on a chain of lifts -/
def lifts.upper_bound_intermediate_field {F : Type u_1} {E : Type u_2} {K : Type u_3} [field F]
    [field E] [field K] [algebra F E] [algebra F K] {c : set (lifts F E K)}
    (hc : zorn.chain LessEq c) : intermediate_field F E :=
  mk (fun (s : E) => ∃ (x : lifts F E K), x ∈ set.insert ⊥ c ∧ s ∈ sigma.fst x) sorry sorry sorry
    sorry sorry sorry sorry

/-- The lift on the upper bound on a chain of lifts -/
def lifts.upper_bound_alg_hom {F : Type u_1} {E : Type u_2} {K : Type u_3} [field F] [field E]
    [field K] [algebra F E] [algebra F K] {c : set (lifts F E K)} (hc : zorn.chain LessEq c) :
    alg_hom F (↥(lifts.upper_bound_intermediate_field hc)) K :=
  alg_hom.mk
    (fun (s : ↥(lifts.upper_bound_intermediate_field hc)) =>
      coe_fn (sigma.snd (classical.some sorry)) { val := ↑s, property := sorry })
    sorry sorry sorry sorry sorry

/-- An upper bound on a chain of lifts -/
def lifts.upper_bound {F : Type u_1} {E : Type u_2} {K : Type u_3} [field F] [field E] [field K]
    [algebra F E] [algebra F K] {c : set (lifts F E K)} (hc : zorn.chain LessEq c) : lifts F E K :=
  sigma.mk (lifts.upper_bound_intermediate_field hc) (lifts.upper_bound_alg_hom hc)

theorem lifts.exists_upper_bound {F : Type u_1} {E : Type u_2} {K : Type u_3} [field F] [field E]
    [field K] [algebra F E] [algebra F K] (c : set (lifts F E K)) (hc : zorn.chain LessEq c) :
    ∃ (ub : lifts F E K), ∀ (a : lifts F E K), a ∈ c → a ≤ ub :=
  sorry

/-- Extend a lift `x : lifts F E K` to an element `s : E` whose conjugates are all in `K` -/
def lifts.lift_of_splits {F : Type u_1} {E : Type u_2} {K : Type u_3} [field F] [field E] [field K]
    [algebra F E] [algebra F K] (x : lifts F E K) {s : E} (h1 : is_integral F s)
    (h2 : polynomial.splits (algebra_map F K) (minpoly F s)) : lifts F E K :=
  let h3 : is_integral (↥(sigma.fst x)) s := sorry;
  let key : polynomial.splits (alg_hom.to_ring_hom (sigma.snd x)) (minpoly (↥(sigma.fst x)) s) :=
    sorry;
  sigma.mk (↑(adjoin (↥(sigma.fst x)) (insert.insert ∅ s)))
    (equiv.inv_fun alg_hom_equiv_sigma
      (sigma.mk (sigma.snd x)
        (equiv.inv_fun (alg_hom_adjoin_integral_equiv (↥(sigma.fst x)) h3)
          { val := polynomial.root_of_splits (alg_hom.to_ring_hom (sigma.snd x)) key sorry,
            property := sorry })))

theorem lifts.le_lifts_of_splits {F : Type u_1} {E : Type u_2} {K : Type u_3} [field F] [field E]
    [field K] [algebra F E] [algebra F K] (x : lifts F E K) {s : E} (h1 : is_integral F s)
    (h2 : polynomial.splits (algebra_map F K) (minpoly F s)) : x ≤ lifts.lift_of_splits x h1 h2 :=
  sorry

theorem lifts.mem_lifts_of_splits {F : Type u_1} {E : Type u_2} {K : Type u_3} [field F] [field E]
    [field K] [algebra F E] [algebra F K] (x : lifts F E K) {s : E} (h1 : is_integral F s)
    (h2 : polynomial.splits (algebra_map F K) (minpoly F s)) :
    s ∈ sigma.fst (lifts.lift_of_splits x h1 h2) :=
  mem_adjoin_simple_self (↥(sigma.fst x)) s

theorem lifts.exists_lift_of_splits {F : Type u_1} {E : Type u_2} {K : Type u_3} [field F] [field E]
    [field K] [algebra F E] [algebra F K] (x : lifts F E K) {s : E} (h1 : is_integral F s)
    (h2 : polynomial.splits (algebra_map F K) (minpoly F s)) :
    ∃ (y : lifts F E K), x ≤ y ∧ s ∈ sigma.fst y :=
  Exists.intro (lifts.lift_of_splits x h1 h2)
    { left := lifts.le_lifts_of_splits x h1 h2, right := lifts.mem_lifts_of_splits x h1 h2 }

theorem alg_hom_mk_adjoin_splits {F : Type u_1} {E : Type u_2} {K : Type u_3} [field F] [field E]
    [field K] [algebra F E] [algebra F K] {S : set E}
    (hK : ∀ (s : E), s ∈ S → is_integral F s ∧ polynomial.splits (algebra_map F K) (minpoly F s)) :
    Nonempty (alg_hom F (↥(adjoin F S)) K) :=
  sorry

theorem alg_hom_mk_adjoin_splits' {F : Type u_1} {E : Type u_2} {K : Type u_3} [field F] [field E]
    [field K] [algebra F E] [algebra F K] {S : set E} (hS : adjoin F S = ⊤)
    (hK : ∀ (x : E), x ∈ S → is_integral F x ∧ polynomial.splits (algebra_map F K) (minpoly F x)) :
    Nonempty (alg_hom F E K) :=
  sorry

end Mathlib