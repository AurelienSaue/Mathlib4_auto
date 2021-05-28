/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.topology.instances.real
import Mathlib.topology.algebra.ordered.proj_Icc
import PostPort

universes u_1 l u_2 u_3 

namespace Mathlib

/-!
# Path connectedness

## Main definitions

In the file the unit interval `[0, 1]` in `ℝ` is denoted by `I`, and `X` is a topological space.

* `path (x y : X)` is the type of paths from `x` to `y`, i.e., continuous maps from `I` to `X`
  mapping `0` to `x` and `1` to `y`.
* `path.map` is the image of a path under a continuous map.
* `joined (x y : X)` means there is a path between `x` and `y`.
* `joined.some_path (h : joined x y)` selects some path between two points `x` and `y`.
* `path_component (x : X)` is the set of points joined to `x`.
* `path_connected_space X` is a predicate class asserting that `X` is non-empty and every two
  points of `X` are joined.

Then there are corresponding relative notions for `F : set X`.

* `joined_in F (x y : X)` means there is a path `γ` joining `x` to `y` with values in `F`.
* `joined_in.some_path (h : joined_in F x y)` selects a path from `x` to `y` inside `F`.
* `path_component_in F (x : X)` is the set of points joined to `x` in `F`.
* `is_path_connected F` asserts that `F` is non-empty and every two
  points of `F` are joined in `F`.
* `loc_path_connected_space X` is a predicate class asserting that `X` is locally path-connected:
  each point has a basis of path-connected neighborhoods (we do *not* ask these to be open).

## Main theorems

* `joined` and `joined_in F` are transitive relations.

One can link the absolute and relative version in two directions, using `(univ : set X)` or the
subtype `↥F`.

* `path_connected_space_iff_univ : path_connected_space X ↔ is_path_connected (univ : set X)`
* `is_path_connected_iff_path_connected_space : is_path_connected F ↔ path_connected_space ↥F`

For locally path connected spaces, we have
* `path_connected_space_iff_connected_space : path_connected_space X ↔ connected_space X`
* `is_connected_iff_is_path_connected (U_op : is_open U) : is_path_connected U ↔ is_connected U`

## Implementation notes

By default, all paths have `I` as their source and `X` as their target, but there is an
operation `set.Icc_extend` that will extend any continuous map `γ : I → X` into a continuous map
`Icc_extend zero_le_one γ : ℝ → X` that is constant before `0` and after `1`.

This is used to define `path.extend` that turns `γ : path x y` into a continuous map
`γ.extend : ℝ → X` whose restriction to `I` is the original `γ`, and is equal to `x`
on `(-∞, 0]` and to `y` on `[1, +∞)`.
-/

/-! ### The unit interval -/

theorem Icc_zero_one_symm {t : ℝ} : t ∈ set.Icc 0 1 ↔ 1 - t ∈ set.Icc 0 1 := sorry

protected instance I_has_zero : HasZero ↥(set.Icc 0 1) :=
  { zero := { val := 0, property := sorry } }

@[simp] theorem coe_I_zero : ↑0 = 0 :=
  rfl

protected instance I_has_one : HasOne ↥(set.Icc 0 1) :=
  { one := { val := 1, property := sorry } }

@[simp] theorem coe_I_one : ↑1 = 1 :=
  rfl

/-- Unit interval central symmetry. -/
def I_symm : ↥(set.Icc 0 1) → ↥(set.Icc 0 1) :=
  fun (t : ↥(set.Icc 0 1)) => { val := 1 - subtype.val t, property := sorry }

@[simp] theorem I_symm_zero : I_symm 0 = 1 := sorry

@[simp] theorem I_symm_one : I_symm 1 = 0 := sorry

theorem continuous_I_symm : continuous I_symm :=
  continuous_subtype_mk (fun (x : ↥(set.Icc 0 1)) => I_symm._proof_1 x)
    (continuous.sub continuous_const continuous_subtype_val)

protected instance set.Icc.connected_space : connected_space ↥(set.Icc 0 1) :=
  subtype.connected_space { left := iff.mpr set.nonempty_Icc zero_le_one, right := is_preconnected_Icc }

protected instance set.Icc.compact_space : compact_space ↥(set.Icc 0 1) :=
  iff.mp compact_iff_compact_space compact_Icc

/-! ### Paths -/

/-- Continuous path connecting two points `x` and `y` in a topological space -/
structure path {X : Type u_1} [topological_space X] (x : X) (y : X) 
where
  to_fun : ↥(set.Icc 0 1) → X
  continuous' : continuous to_fun
  source' : to_fun 0 = x
  target' : to_fun 1 = y

protected instance path.has_coe_to_fun {X : Type u_1} [topological_space X] {x : X} {y : X} : has_coe_to_fun (path x y) :=
  has_coe_to_fun.mk (fun (x : path x y) => ↥(set.Icc 0 1) → X) path.to_fun

protected theorem path.ext {X : Type u_1} [topological_space X] {x : X} {y : X} {γ₁ : path x y} {γ₂ : path x y} : ⇑γ₁ = ⇑γ₂ → γ₁ = γ₂ := sorry

namespace path


@[simp] theorem coe_mk {X : Type u_1} [topological_space X] {x : X} {y : X} (f : ↥(set.Icc 0 1) → X) (h₁ : continuous f) (h₂ : f 0 = x) (h₃ : f 1 = y) : ⇑(mk f h₁ h₂ h₃) = f :=
  rfl

protected theorem continuous {X : Type u_1} [topological_space X] {x : X} {y : X} (γ : path x y) : continuous ⇑γ :=
  continuous' γ

@[simp] protected theorem source {X : Type u_1} [topological_space X] {x : X} {y : X} (γ : path x y) : coe_fn γ 0 = x :=
  source' γ

@[simp] protected theorem target {X : Type u_1} [topological_space X] {x : X} {y : X} (γ : path x y) : coe_fn γ 1 = y :=
  target' γ

/-- Any function `φ : Π (a : α), path (x a) (y a)` can be seen as a function `α × I → X`. -/
protected instance has_uncurry_path {X : Type u_1} {α : Type u_2} [topological_space X] {x : α → X} {y : α → X} : function.has_uncurry ((a : α) → path (x a) (y a)) (α × ↥(set.Icc 0 1)) X :=
  function.has_uncurry.mk
    fun (φ : (a : α) → path (x a) (y a)) (p : α × ↥(set.Icc 0 1)) => coe_fn (φ (prod.fst p)) (prod.snd p)

/-- The constant path from a point to itself -/
def refl {X : Type u_1} [topological_space X] (x : X) : path x x :=
  mk (fun (t : ↥(set.Icc 0 1)) => x) sorry rfl rfl

@[simp] theorem refl_range {X : Type u_1} [topological_space X] {a : X} : set.range ⇑(refl a) = singleton a := sorry

/-- The reverse of a path from `x` to `y`, as a path from `y` to `x` -/
def symm {X : Type u_1} [topological_space X] {x : X} {y : X} (γ : path x y) : path y x :=
  mk (⇑γ ∘ I_symm) sorry sorry sorry

@[simp] theorem refl_symm {X : Type u_1} [topological_space X] {a : X} : symm (refl a) = refl a :=
  path.ext (funext fun (x : ↥(set.Icc 0 1)) => Eq.refl (coe_fn (symm (refl a)) x))

@[simp] theorem symm_range {X : Type u_1} [topological_space X] {a : X} {b : X} (γ : path a b) : set.range ⇑(symm γ) = set.range ⇑γ := sorry

/-- A continuous map extending a path to `ℝ`, constant before `0` and after `1`. -/
def extend {X : Type u_1} [topological_space X] {x : X} {y : X} (γ : path x y) : ℝ → X :=
  set.Icc_extend zero_le_one ⇑γ

theorem continuous_extend {X : Type u_1} [topological_space X] {x : X} {y : X} (γ : path x y) : continuous (extend γ) :=
  continuous.Icc_extend (path.continuous γ)

@[simp] theorem extend_zero {X : Type u_1} [topological_space X] {x : X} {y : X} (γ : path x y) : extend γ 0 = x :=
  Eq.trans (set.Icc_extend_left zero_le_one ⇑γ) (path.source γ)

@[simp] theorem extend_one {X : Type u_1} [topological_space X] {x : X} {y : X} (γ : path x y) : extend γ 1 = y :=
  Eq.trans (set.Icc_extend_right zero_le_one ⇑γ) (path.target γ)

@[simp] theorem extend_extends {X : Type u_1} [topological_space X] {a : X} {b : X} (γ : path a b) {t : ℝ} (ht : t ∈ set.Icc 0 1) : extend γ t = coe_fn γ { val := t, property := ht } :=
  set.Icc_extend_of_mem zero_le_one (⇑γ) ht

@[simp] theorem extend_extends' {X : Type u_1} [topological_space X] {a : X} {b : X} (γ : path a b) (t : ↥(set.Icc 0 1)) : extend γ ↑t = coe_fn γ t :=
  set.Icc_extend_coe zero_le_one (⇑γ) t

@[simp] theorem extend_range {X : Type u_1} [topological_space X] {a : X} {b : X} (γ : path a b) : set.range (extend γ) = set.range ⇑γ :=
  set.Icc_extend_range zero_le_one ⇑γ

theorem extend_of_le_zero {X : Type u_1} [topological_space X] {a : X} {b : X} (γ : path a b) {t : ℝ} (ht : t ≤ 0) : extend γ t = a :=
  Eq.trans (set.Icc_extend_of_le_left zero_le_one (⇑γ) ht) (path.source γ)

theorem extend_of_one_le {X : Type u_1} [topological_space X] {a : X} {b : X} (γ : path a b) {t : ℝ} (ht : 1 ≤ t) : extend γ t = b :=
  Eq.trans (set.Icc_extend_of_right_le zero_le_one (⇑γ) ht) (path.target γ)

@[simp] theorem refl_extend {X : Type u_1} [topological_space X] {a : X} : extend (refl a) = fun (_x : ℝ) => a :=
  rfl

/-- The path obtained from a map defined on `ℝ` by restriction to the unit interval. -/
def of_line {X : Type u_1} [topological_space X] {x : X} {y : X} {f : ℝ → X} (hf : continuous_on f (set.Icc 0 1)) (h₀ : f 0 = x) (h₁ : f 1 = y) : path x y :=
  mk (f ∘ coe) sorry h₀ h₁

theorem of_line_mem {X : Type u_1} [topological_space X] {x : X} {y : X} {f : ℝ → X} (hf : continuous_on f (set.Icc 0 1)) (h₀ : f 0 = x) (h₁ : f 1 = y) (t : ↥(set.Icc 0 1)) : coe_fn (of_line hf h₀ h₁) t ∈ f '' set.Icc 0 1 := sorry

/-- Concatenation of two paths from `x` to `y` and from `y` to `z`, putting the first
path on `[0, 1/2]` and the second one on `[1/2, 1]`. -/
def trans {X : Type u_1} [topological_space X] {x : X} {y : X} {z : X} (γ : path x y) (γ' : path y z) : path x z :=
  mk ((fun (t : ℝ) => ite (t ≤ 1 / bit0 1) (extend γ (bit0 1 * t)) (extend γ' (bit0 1 * t - 1))) ∘ coe) sorry sorry sorry

@[simp] theorem refl_trans_refl {X : Type u_1} [topological_space X] {a : X} : trans (refl a) (refl a) = refl a := sorry

theorem trans_range {X : Type u_1} [topological_space X] {a : X} {b : X} {c : X} (γ₁ : path a b) (γ₂ : path b c) : set.range ⇑(trans γ₁ γ₂) = set.range ⇑γ₁ ∪ set.range ⇑γ₂ := sorry

/-- Image of a path from `x` to `y` by a continuous map -/
def map {X : Type u_1} [topological_space X] {x : X} {y : X} (γ : path x y) {Y : Type u_2} [topological_space Y] {f : X → Y} (h : continuous f) : path (f x) (f y) :=
  mk (f ∘ ⇑γ) sorry sorry sorry

@[simp] theorem map_coe {X : Type u_1} [topological_space X] {x : X} {y : X} (γ : path x y) {Y : Type u_2} [topological_space Y] {f : X → Y} (h : continuous f) : ⇑(map γ h) = f ∘ ⇑γ :=
  funext fun (t : ↥(set.Icc 0 1)) => Eq.refl (coe_fn (map γ h) t)

/-- Casting a path from `x` to `y` to a path from `x'` to `y'` when `x' = x` and `y' = y` -/
def cast {X : Type u_1} [topological_space X] {x : X} {y : X} (γ : path x y) {x' : X} {y' : X} (hx : x' = x) (hy : y' = y) : path x' y' :=
  mk (⇑γ) (path.continuous γ) sorry sorry

@[simp] theorem symm_cast {X : Type u_1} [topological_space X] {a₁ : X} {a₂ : X} {b₁ : X} {b₂ : X} (γ : path a₂ b₂) (ha : a₁ = a₂) (hb : b₁ = b₂) : symm (cast γ ha hb) = cast (symm γ) hb ha :=
  rfl

@[simp] theorem trans_cast {X : Type u_1} [topological_space X] {a₁ : X} {a₂ : X} {b₁ : X} {b₂ : X} {c₁ : X} {c₂ : X} (γ : path a₂ b₂) (γ' : path b₂ c₂) (ha : a₁ = a₂) (hb : b₁ = b₂) (hc : c₁ = c₂) : trans (cast γ ha hb) (cast γ' hb hc) = cast (trans γ γ') ha hc :=
  rfl

@[simp] theorem cast_coe {X : Type u_1} [topological_space X] {x : X} {y : X} (γ : path x y) {x' : X} {y' : X} (hx : x' = x) (hy : y' = y) : ⇑(cast γ hx hy) = ⇑γ :=
  rfl

theorem symm_continuous_family {X : Type u_1} {ι : Type u_2} [topological_space X] [topological_space ι] {a : ι → X} {b : ι → X} (γ : (t : ι) → path (a t) (b t)) (h : continuous ↿γ) : continuous ↿fun (t : ι) => symm (γ t) :=
  continuous.comp h (continuous.prod_map continuous_id continuous_I_symm)

theorem continuous_uncurry_extend_of_continuous_family {X : Type u_1} {ι : Type u_2} [topological_space X] [topological_space ι] {a : ι → X} {b : ι → X} (γ : (t : ι) → path (a t) (b t)) (h : continuous ↿γ) : continuous ↿fun (t : ι) => extend (γ t) :=
  continuous.comp h (continuous.prod_map continuous_id continuous_proj_Icc)

theorem trans_continuous_family {X : Type u_1} {ι : Type u_2} [topological_space X] [topological_space ι] {a : ι → X} {b : ι → X} {c : ι → X} (γ₁ : (t : ι) → path (a t) (b t)) (h₁ : continuous ↿γ₁) (γ₂ : (t : ι) → path (b t) (c t)) (h₂ : continuous ↿γ₂) : continuous ↿fun (t : ι) => trans (γ₁ t) (γ₂ t) := sorry

/-! #### Truncating a path -/

/-- `γ.truncate t₀ t₁` is the path which follows the path `γ` on the
  time interval `[t₀, t₁]` and stays still otherwise. -/
def truncate {X : Type u_1} [topological_space X] {a : X} {b : X} (γ : path a b) (t₀ : ℝ) (t₁ : ℝ) : path (extend γ (min t₀ t₁)) (extend γ t₁) :=
  mk (fun (s : ↥(set.Icc 0 1)) => extend γ (min (max (↑s) t₀) t₁)) sorry sorry sorry

/-- `γ.truncate_of_le t₀ t₁ h`, where `h : t₀ ≤ t₁` is `γ.truncate t₀ t₁`
  casted as a path from `γ.extend t₀` to `γ.extend t₁`. -/
def truncate_of_le {X : Type u_1} [topological_space X] {a : X} {b : X} (γ : path a b) {t₀ : ℝ} {t₁ : ℝ} (h : t₀ ≤ t₁) : path (extend γ t₀) (extend γ t₁) :=
  cast (truncate γ t₀ t₁) sorry sorry

theorem truncate_range {X : Type u_1} [topological_space X] {a : X} {b : X} (γ : path a b) {t₀ : ℝ} {t₁ : ℝ} : set.range ⇑(truncate γ t₀ t₁) ⊆ set.range ⇑γ := sorry

/-- For a path `γ`, `γ.truncate` gives a "continuous family of paths", by which we
  mean the uncurried function which maps `(t₀, t₁, s)` to `γ.truncate t₀ t₁ s` is continuous. -/
theorem truncate_continuous_family {X : Type u_1} [topological_space X] {a : X} {b : X} (γ : path a b) : continuous
  fun (x : ℝ × ℝ × ↥(set.Icc 0 1)) => coe_fn (truncate γ (prod.fst x) (prod.fst (prod.snd x))) (prod.snd (prod.snd x)) := sorry

/- TODO : When `continuity` gets quicker, change the proof back to :
    `begin`
      `simp only [has_coe_to_fun.coe, coe_fn, path.truncate],`
      `continuity,`
      `exact continuous_subtype_coe`
    `end` -/

theorem truncate_const_continuous_family {X : Type u_1} [topological_space X] {a : X} {b : X} (γ : path a b) (t : ℝ) : continuous ↿(truncate γ t) := sorry

@[simp] theorem truncate_self {X : Type u_1} [topological_space X] {a : X} {b : X} (γ : path a b) (t : ℝ) : truncate γ t t =
  cast (refl (extend γ t))
    (eq.mpr (id (Eq._oldrec (Eq.refl (extend γ (min t t) = extend γ t)) (min_self t))) (Eq.refl (extend γ t))) rfl := sorry

@[simp] theorem truncate_zero_zero {X : Type u_1} [topological_space X] {a : X} {b : X} (γ : path a b) : truncate γ 0 0 =
  cast (refl a)
    (eq.mpr (id (Eq._oldrec (Eq.refl (extend γ (min 0 0) = a)) (min_self 0)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (extend γ 0 = a)) (extend_zero γ))) (Eq.refl a)))
    (extend_zero γ) := sorry

@[simp] theorem truncate_one_one {X : Type u_1} [topological_space X] {a : X} {b : X} (γ : path a b) : truncate γ 1 1 =
  cast (refl b)
    (eq.mpr (id (Eq._oldrec (Eq.refl (extend γ (min 1 1) = b)) (min_self 1)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (extend γ 1 = b)) (extend_one γ))) (Eq.refl b)))
    (extend_one γ) := sorry

@[simp] theorem truncate_zero_one {X : Type u_1} [topological_space X] {a : X} {b : X} (γ : path a b) : truncate γ 0 1 =
  cast γ
    (eq.mpr
      (id
        (Eq.trans
          ((fun (a a_1 : X) (e_1 : a = a_1) (ᾰ ᾰ_1 : X) (e_2 : ᾰ = ᾰ_1) => congr (congr_arg Eq e_1) e_2)
            (extend γ (min 0 1)) a
            (Eq.trans
              ((fun (γ γ_1 : path a b) (e_1 : γ = γ_1) (ᾰ ᾰ_1 : ℝ) (e_2 : ᾰ = ᾰ_1) => congr (congr_arg extend e_1) e_2)
                γ γ (Eq.refl γ) (min 0 1) 0 (min_eq_left (iff.mpr (iff_true_intro zero_le_one) True.intro)))
              (extend_zero γ))
            a a (Eq.refl a))
          (propext (eq_self_iff_true a))))
      trivial)
    (eq.mpr
      (id
        (Eq.trans
          ((fun (a a_1 : X) (e_1 : a = a_1) (ᾰ ᾰ_1 : X) (e_2 : ᾰ = ᾰ_1) => congr (congr_arg Eq e_1) e_2) (extend γ 1) b
            (extend_one γ) b b (Eq.refl b))
          (propext (eq_self_iff_true b))))
      trivial) := sorry

end path


/-! ### Being joined by a path -/

/-- The relation "being joined by a path". This is an equivalence relation. -/
def joined {X : Type u_1} [topological_space X] (x : X) (y : X)  :=
  Nonempty (path x y)

theorem joined.refl {X : Type u_1} [topological_space X] (x : X) : joined x x :=
  Nonempty.intro (path.refl x)

/-- When two points are joined, choose some path from `x` to `y`. -/
def joined.some_path {X : Type u_1} [topological_space X] {x : X} {y : X} (h : joined x y) : path x y :=
  nonempty.some h

theorem joined.symm {X : Type u_1} [topological_space X] {x : X} {y : X} (h : joined x y) : joined y x :=
  Nonempty.intro (path.symm (joined.some_path h))

theorem joined.trans {X : Type u_1} [topological_space X] {x : X} {y : X} {z : X} (hxy : joined x y) (hyz : joined y z) : joined x z :=
  Nonempty.intro (path.trans (joined.some_path hxy) (joined.some_path hyz))

/-- The setoid corresponding the equivalence relation of being joined by a continuous path. -/
def path_setoid (X : Type u_1) [topological_space X] : setoid X :=
  setoid.mk joined sorry

/-- The quotient type of points of a topological space modulo being joined by a continuous path. -/
def zeroth_homotopy (X : Type u_1) [topological_space X]  :=
  quotient (path_setoid X)

protected instance zeroth_homotopy.inhabited : Inhabited (zeroth_homotopy ℝ) :=
  { default := quotient.mk 0 }

/-! ### Being joined by a path inside a set -/

/-- The relation "being joined by a path in `F`". Not quite an equivalence relation since it's not
reflexive for points that do not belong to `F`. -/
def joined_in {X : Type u_1} [topological_space X] (F : set X) (x : X) (y : X)  :=
  ∃ (γ : path x y), ∀ (t : ↥(set.Icc 0 1)), coe_fn γ t ∈ F

theorem joined_in.mem {X : Type u_1} [topological_space X] {x : X} {y : X} {F : set X} (h : joined_in F x y) : x ∈ F ∧ y ∈ F := sorry

theorem joined_in.source_mem {X : Type u_1} [topological_space X] {x : X} {y : X} {F : set X} (h : joined_in F x y) : x ∈ F :=
  and.left (joined_in.mem h)

theorem joined_in.target_mem {X : Type u_1} [topological_space X] {x : X} {y : X} {F : set X} (h : joined_in F x y) : y ∈ F :=
  and.right (joined_in.mem h)

/-- When `x` and `y` are joined in `F`, choose a path from `x` to `y` inside `F` -/
def joined_in.some_path {X : Type u_1} [topological_space X] {x : X} {y : X} {F : set X} (h : joined_in F x y) : path x y :=
  classical.some h

theorem joined_in.some_path_mem {X : Type u_1} [topological_space X] {x : X} {y : X} {F : set X} (h : joined_in F x y) (t : ↥(set.Icc 0 1)) : coe_fn (joined_in.some_path h) t ∈ F :=
  classical.some_spec h t

/-- If `x` and `y` are joined in the set `F`, then they are joined in the subtype `F`. -/
theorem joined_in.joined_subtype {X : Type u_1} [topological_space X] {x : X} {y : X} {F : set X} (h : joined_in F x y) : joined { val := x, property := joined_in.source_mem h } { val := y, property := joined_in.target_mem h } := sorry

theorem joined_in.of_line {X : Type u_1} [topological_space X] {x : X} {y : X} {F : set X} {f : ℝ → X} (hf : continuous_on f (set.Icc 0 1)) (h₀ : f 0 = x) (h₁ : f 1 = y) (hF : f '' set.Icc 0 1 ⊆ F) : joined_in F x y :=
  Exists.intro (path.of_line hf h₀ h₁) fun (t : ↥(set.Icc 0 1)) => hF (path.of_line_mem hf h₀ h₁ t)

theorem joined_in.joined {X : Type u_1} [topological_space X] {x : X} {y : X} {F : set X} (h : joined_in F x y) : joined x y :=
  Nonempty.intro (joined_in.some_path h)

theorem joined_in_iff_joined {X : Type u_1} [topological_space X] {x : X} {y : X} {F : set X} (x_in : x ∈ F) (y_in : y ∈ F) : joined_in F x y ↔ joined { val := x, property := x_in } { val := y, property := y_in } := sorry

@[simp] theorem joined_in_univ {X : Type u_1} [topological_space X] {x : X} {y : X} : joined_in set.univ x y ↔ joined x y := sorry

theorem joined_in.mono {X : Type u_1} [topological_space X] {x : X} {y : X} {U : set X} {V : set X} (h : joined_in U x y) (hUV : U ⊆ V) : joined_in V x y :=
  Exists.intro (joined_in.some_path h) fun (t : ↥(set.Icc 0 1)) => hUV (joined_in.some_path_mem h t)

theorem joined_in.refl {X : Type u_1} [topological_space X] {x : X} {F : set X} (h : x ∈ F) : joined_in F x x :=
  Exists.intro (path.refl x) fun (t : ↥(set.Icc 0 1)) => h

theorem joined_in.symm {X : Type u_1} [topological_space X] {x : X} {y : X} {F : set X} (h : joined_in F x y) : joined_in F y x := sorry

theorem joined_in.trans {X : Type u_1} [topological_space X] {x : X} {y : X} {z : X} {F : set X} (hxy : joined_in F x y) (hyz : joined_in F y z) : joined_in F x z := sorry

/-! ### Path component -/

/-- The path component of `x` is the set of points that can be joined to `x`. -/
def path_component {X : Type u_1} [topological_space X] (x : X) : set X :=
  set_of fun (y : X) => joined x y

@[simp] theorem mem_path_component_self {X : Type u_1} [topological_space X] (x : X) : x ∈ path_component x :=
  joined.refl x

@[simp] theorem path_component.nonempty {X : Type u_1} [topological_space X] (x : X) : set.nonempty (path_component x) :=
  Exists.intro x (mem_path_component_self x)

theorem mem_path_component_of_mem {X : Type u_1} [topological_space X] {x : X} {y : X} (h : x ∈ path_component y) : y ∈ path_component x :=
  joined.symm h

theorem path_component_symm {X : Type u_1} [topological_space X] {x : X} {y : X} : x ∈ path_component y ↔ y ∈ path_component x :=
  { mp := fun (h : x ∈ path_component y) => mem_path_component_of_mem h,
    mpr := fun (h : y ∈ path_component x) => mem_path_component_of_mem h }

theorem path_component_congr {X : Type u_1} [topological_space X] {x : X} {y : X} (h : x ∈ path_component y) : path_component x = path_component y := sorry

theorem path_component_subset_component {X : Type u_1} [topological_space X] (x : X) : path_component x ⊆ connected_component x := sorry

/-- The path component of `x` in `F` is the set of points that can be joined to `x` in `F`. -/
def path_component_in {X : Type u_1} [topological_space X] (x : X) (F : set X) : set X :=
  set_of fun (y : X) => joined_in F x y

@[simp] theorem path_component_in_univ {X : Type u_1} [topological_space X] (x : X) : path_component_in x set.univ = path_component x := sorry

theorem joined.mem_path_component {X : Type u_1} [topological_space X] {x : X} {y : X} {z : X} (hyz : joined y z) (hxy : y ∈ path_component x) : z ∈ path_component x :=
  joined.trans hxy hyz

/-! ### Path connected sets -/

/-- A set `F` is path connected if it contains a point that can be joined to all other in `F`. -/
def is_path_connected {X : Type u_1} [topological_space X] (F : set X)  :=
  ∃ (x : X), ∃ (H : x ∈ F), ∀ {y : X}, y ∈ F → joined_in F x y

theorem is_path_connected_iff_eq {X : Type u_1} [topological_space X] {F : set X} : is_path_connected F ↔ ∃ (x : X), ∃ (H : x ∈ F), path_component_in x F = F := sorry

theorem is_path_connected.joined_in {X : Type u_1} [topological_space X] {F : set X} (h : is_path_connected F) (x : X) (y : X) (H : x ∈ F) : y ∈ F → joined_in F x y := sorry

theorem is_path_connected_iff {X : Type u_1} [topological_space X] {F : set X} : is_path_connected F ↔ set.nonempty F ∧ ∀ (x y : X), x ∈ F → y ∈ F → joined_in F x y := sorry

theorem is_path_connected.image {X : Type u_1} [topological_space X] {F : set X} {Y : Type u_2} [topological_space Y] (hF : is_path_connected F) {f : X → Y} (hf : continuous f) : is_path_connected (f '' F) := sorry

theorem is_path_connected.mem_path_component {X : Type u_1} [topological_space X] {x : X} {y : X} {F : set X} (h : is_path_connected F) (x_in : x ∈ F) (y_in : y ∈ F) : y ∈ path_component x :=
  joined_in.joined (is_path_connected.joined_in h x y x_in y_in)

theorem is_path_connected.subset_path_component {X : Type u_1} [topological_space X] {x : X} {F : set X} (h : is_path_connected F) (x_in : x ∈ F) : F ⊆ path_component x :=
  fun (y : X) (y_in : y ∈ F) => is_path_connected.mem_path_component h x_in y_in

theorem is_path_connected.union {X : Type u_1} [topological_space X] {U : set X} {V : set X} (hU : is_path_connected U) (hV : is_path_connected V) (hUV : set.nonempty (U ∩ V)) : is_path_connected (U ∪ V) := sorry

/-- If a set `W` is path-connected, then it is also path-connected when seen as a set in a smaller
ambient type `U` (when `U` contains `W`). -/
theorem is_path_connected.preimage_coe {X : Type u_1} [topological_space X] {U : set X} {W : set X} (hW : is_path_connected W) (hWU : W ⊆ U) : is_path_connected (coe ⁻¹' W) := sorry

theorem is_path_connected.exists_path_through_family {X : Type u_1} [topological_space X] {n : ℕ} {s : set X} (h : is_path_connected s) (p : fin (n + 1) → X) (hp : ∀ (i : fin (n + 1)), p i ∈ s) : ∃ (γ : path (p 0) (p ↑n)), set.range ⇑γ ⊆ s ∧ ∀ (i : fin (n + 1)), p i ∈ set.range ⇑γ := sorry

theorem is_path_connected.exists_path_through_family' {X : Type u_1} [topological_space X] {n : ℕ} {s : set X} (h : is_path_connected s) (p : fin (n + 1) → X) (hp : ∀ (i : fin (n + 1)), p i ∈ s) : ∃ (γ : path (p 0) (p ↑n)),
  ∃ (t : fin (n + 1) → ↥(set.Icc 0 1)),
    (∀ (t : ↥(set.Icc 0 1)), coe_fn γ t ∈ s) ∧ ∀ (i : fin (n + 1)), coe_fn γ (t i) = p i := sorry

/-! ### Path connected spaces -/

/-- A topological space is path-connected if it is non-empty and every two points can be
joined by a continuous path. -/
class path_connected_space (X : Type u_3) [topological_space X] 
where
  nonempty : Nonempty X
  joined : ∀ (x y : X), joined x y

theorem path_connected_space_iff_zeroth_homotopy {X : Type u_1} [topological_space X] : path_connected_space X ↔ Nonempty (zeroth_homotopy X) ∧ subsingleton (zeroth_homotopy X) := sorry

namespace path_connected_space


/-- Use path-connectedness to build a path between two points. -/
def some_path {X : Type u_1} [topological_space X] [path_connected_space X] (x : X) (y : X) : path x y :=
  nonempty.some (joined x y)

end path_connected_space


theorem is_path_connected_iff_path_connected_space {X : Type u_1} [topological_space X] {F : set X} : is_path_connected F ↔ path_connected_space ↥F := sorry

theorem path_connected_space_iff_univ {X : Type u_1} [topological_space X] : path_connected_space X ↔ is_path_connected set.univ := sorry

theorem path_connected_space_iff_eq {X : Type u_1} [topological_space X] : path_connected_space X ↔ ∃ (x : X), path_component x = set.univ := sorry

protected instance path_connected_space.connected_space {X : Type u_1} [topological_space X] [path_connected_space X] : connected_space X := sorry

namespace path_connected_space


theorem exists_path_through_family {X : Type u_1} [topological_space X] [path_connected_space X] {n : ℕ} (p : fin (n + 1) → X) : ∃ (γ : path (p 0) (p ↑n)), ∀ (i : fin (n + 1)), p i ∈ set.range ⇑γ := sorry

theorem exists_path_through_family' {X : Type u_1} [topological_space X] [path_connected_space X] {n : ℕ} (p : fin (n + 1) → X) : ∃ (γ : path (p 0) (p ↑n)), ∃ (t : fin (n + 1) → ↥(set.Icc 0 1)), ∀ (i : fin (n + 1)), coe_fn γ (t i) = p i := sorry

end path_connected_space


/-! ### Locally path connected spaces -/

/-- A topological space is locally path connected, at every point, path connected
neighborhoods form a neighborhood basis. -/
class loc_path_connected_space (X : Type u_3) [topological_space X] 
where
  path_connected_basis : ∀ (x : X), filter.has_basis (nhds x) (fun (s : set X) => s ∈ nhds x ∧ is_path_connected s) id

theorem loc_path_connected_of_bases {X : Type u_1} [topological_space X] {ι : Type u_2} {p : ι → Prop} {s : X → ι → set X} (h : ∀ (x : X), filter.has_basis (nhds x) p (s x)) (h' : ∀ (x : X) (i : ι), p i → is_path_connected (s x i)) : loc_path_connected_space X := sorry

theorem path_connected_space_iff_connected_space {X : Type u_1} [topological_space X] [loc_path_connected_space X] : path_connected_space X ↔ connected_space X := sorry

theorem path_connected_subset_basis {X : Type u_1} [topological_space X] {x : X} [loc_path_connected_space X] {U : set X} (h : is_open U) (hx : x ∈ U) : filter.has_basis (nhds x) (fun (s : set X) => s ∈ nhds x ∧ is_path_connected s ∧ s ⊆ U) id :=
  filter.has_basis.has_basis_self_subset (path_connected_basis x) (mem_nhds_sets h hx)

theorem loc_path_connected_of_is_open {X : Type u_1} [topological_space X] [loc_path_connected_space X] {U : set X} (h : is_open U) : loc_path_connected_space ↥U := sorry

theorem is_open.is_connected_iff_is_path_connected {X : Type u_1} [topological_space X] [loc_path_connected_space X] {U : set X} (U_op : is_open U) : is_path_connected U ↔ is_connected U := sorry

