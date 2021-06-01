/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Johan Commelin
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.analysis.analytic.basic
import Mathlib.combinatorics.composition
import Mathlib.PostPort

universes u_1 u_2 u_3 u_4 u_5 

namespace Mathlib

/-!
# Composition of analytic functions

in this file we prove that the composition of analytic functions is analytic.

The argument is the following. Assume `g z = ∑' qₙ (z, ..., z)` and `f y = ∑' pₖ (y, ..., y)`. Then

`g (f y) = ∑' qₙ (∑' pₖ (y, ..., y), ..., ∑' pₖ (y, ..., y))
= ∑' qₙ (p_{i₁} (y, ..., y), ..., p_{iₙ} (y, ..., y))`.

For each `n` and `i₁, ..., iₙ`, define a `i₁ + ... + iₙ` multilinear function mapping
`(y₀, ..., y_{i₁ + ... + iₙ - 1})` to
`qₙ (p_{i₁} (y₀, ..., y_{i₁-1}), p_{i₂} (y_{i₁}, ..., y_{i₁ + i₂ - 1}), ..., p_{iₙ} (....)))`.
Then `g ∘ f` is obtained by summing all these multilinear functions.

To formalize this, we use compositions of an integer `N`, i.e., its decompositions into
a sum `i₁ + ... + iₙ` of positive integers. Given such a composition `c` and two formal
multilinear series `q` and `p`, let `q.comp_along_composition p c` be the above multilinear
function. Then the `N`-th coefficient in the power series expansion of `g ∘ f` is the sum of these
terms over all `c : composition N`.

To complete the proof, we need to show that this power series has a positive radius of convergence.
This follows from the fact that `composition N` has cardinality `2^(N-1)` and estimates on
the norm of `qₙ` and `pₖ`, which give summability. We also need to show that it indeed converges to
`g ∘ f`. For this, we note that the composition of partial sums converges to `g ∘ f`, and that it
corresponds to a part of the whole sum, on a subset that increases to the whole space. By
summability of the norms, this implies the overall convergence.

## Main results

* `q.comp p` is the formal composition of the formal multilinear series `q` and `p`.
* `has_fpower_series_at.comp` states that if two functions `g` and `f` admit power series expansions
  `q` and `p`, then `g ∘ f` admits a power series expansion given by `q.comp p`.
* `analytic_at.comp` states that the composition of analytic functions is analytic.
* `formal_multilinear_series.comp_assoc` states that composition is associative on formal
  multilinear series.

## Implementation details

The main technical difficulty is to write down things. In particular, we need to define precisely
`q.comp_along_composition p c` and to show that it is indeed a continuous multilinear
function. This requires a whole interface built on the class `composition`. Once this is set,
the main difficulty is to reorder the sums, writing the composition of the partial sums as a sum
over some subset of `Σ n, composition n`. We need to check that the reordering is a bijection,
running over difficulties due to the dependent nature of the types under consideration, that are
controlled thanks to the interface for `composition`.

The associativity of composition on formal multilinear series is a nontrivial result: it does not
follow from the associativity of composition of analytic functions, as there is no uniqueness for
the formal multilinear series representing a function (and also, it holds even when the radius of
convergence of the series is `0`). Instead, we give a direct proof, which amounts to reordering
double sums in a careful way. The change of variables is a canonical (combinatorial) bijection
`composition.sigma_equiv_sigma_pi` between `(Σ (a : composition n), composition a.length)` and
`(Σ (c : composition n), Π (i : fin c.length), composition (c.blocks_fun i))`, and is described
in more details below in the paragraph on associativity.
-/

/-! ### Composing formal multilinear series -/

namespace formal_multilinear_series


/-!
In this paragraph, we define the composition of formal multilinear series, by summing over all
possible compositions of `n`.
-/

/-- Given a formal multilinear series `p`, a composition `c` of `n` and the index `i` of a
block of `c`, we may define a function on `fin n → E` by picking the variables in the `i`-th block
of `n`, and applying the corresponding coefficient of `p` to these variables. This function is
called `p.apply_composition c v i` for `v : fin n → E` and `i : fin c.length`. -/
def apply_composition {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    (p : formal_multilinear_series 𝕜 E F) {n : ℕ} (c : composition n) :
    (fin n → E) → fin (composition.length c) → F :=
  fun (v : fin n → E) (i : fin (composition.length c)) =>
    coe_fn (p (composition.blocks_fun c i)) (v ∘ ⇑(composition.embedding c i))

theorem apply_composition_ones {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    (p : formal_multilinear_series 𝕜 E F) (n : ℕ) :
    apply_composition p (composition.ones n) =
        fun (v : fin n → E) (i : fin (composition.length (composition.ones n))) =>
          coe_fn (p 1)
            fun (_x : fin 1) =>
              v (coe_fn (fin.cast_le (composition.length_le (composition.ones n))) i) :=
  sorry

theorem apply_composition_single {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    (p : formal_multilinear_series 𝕜 E F) {n : ℕ} (hn : 0 < n) (v : fin n → E) :
    apply_composition p (composition.single n hn) v =
        fun (j : fin (composition.length (composition.single n hn))) => coe_fn (p n) v :=
  sorry

@[simp] theorem remove_zero_apply_composition {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] (p : formal_multilinear_series 𝕜 E F) {n : ℕ} (c : composition n) :
    apply_composition (remove_zero p) c = apply_composition p c :=
  sorry

/-- Technical lemma stating how `p.apply_composition` commutes with updating variables. This
will be the key point to show that functions constructed from `apply_composition` retain
multilinearity. -/
theorem apply_composition_update {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    (p : formal_multilinear_series 𝕜 E F) {n : ℕ} (c : composition n) (j : fin n) (v : fin n → E)
    (z : E) :
    apply_composition p c (function.update v j z) =
        function.update (apply_composition p c v) (composition.index c j)
          (coe_fn (p (composition.blocks_fun c (composition.index c j)))
            (function.update (v ∘ ⇑(composition.embedding c (composition.index c j)))
              (composition.inv_embedding c j) z)) :=
  sorry

@[simp] theorem comp_continuous_linear_map_apply_composition {𝕜 : Type u_1}
    [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3}
    [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {n : ℕ}
    (p : formal_multilinear_series 𝕜 F G) (f : continuous_linear_map 𝕜 E F) (c : composition n)
    (v : fin n → E) :
    apply_composition (comp_continuous_linear_map p f) c v = apply_composition p c (⇑f ∘ v) :=
  sorry

end formal_multilinear_series


namespace continuous_multilinear_map


/-- Given a formal multilinear series `p`, a composition `c` of `n` and a continuous multilinear
map `f` in `c.length` variables, one may form a multilinear map in `n` variables by applying
the right coefficient of `p` to each block of the composition, and then applying `f` to the
resulting vector. It is called `f.comp_along_composition_aux p c`.
This function admits a version as a continuous multilinear map, called
`f.comp_along_composition p c` below. -/
def comp_along_composition_aux {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {n : ℕ} (p : formal_multilinear_series 𝕜 E F)
    (c : composition n)
    (f : continuous_multilinear_map 𝕜 (fun (i : fin (composition.length c)) => F) G) :
    multilinear_map 𝕜 (fun (i : fin n) => E) G :=
  multilinear_map.mk
    (fun (v : fin n → E) => coe_fn f (formal_multilinear_series.apply_composition p c v)) sorry
    sorry

/-- The norm of `f.comp_along_composition_aux p c` is controlled by the product of
the norms of the relevant bits of `f` and `p`. -/
theorem comp_along_composition_aux_bound {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {n : ℕ} (p : formal_multilinear_series 𝕜 E F)
    (c : composition n)
    (f : continuous_multilinear_map 𝕜 (fun (i : fin (composition.length c)) => F) G)
    (v : fin n → E) :
    norm (coe_fn (comp_along_composition_aux p c f) v) ≤
        (norm f *
            finset.prod finset.univ
              fun (i : fin (composition.length c)) => norm (p (composition.blocks_fun c i))) *
          finset.prod finset.univ fun (i : fin n) => norm (v i) :=
  sorry

/-- Given a formal multilinear series `p`, a composition `c` of `n` and a continuous multilinear
map `f` in `c.length` variables, one may form a continuous multilinear map in `n` variables by
applying the right coefficient of `p` to each block of the composition, and then applying `f` to
the resulting vector. It is called `f.comp_along_composition p c`. It is constructed from the
analogous multilinear function `f.comp_along_composition_aux p c`, together with a norm
control to get the continuity. -/
def comp_along_composition {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {n : ℕ} (p : formal_multilinear_series 𝕜 E F)
    (c : composition n)
    (f : continuous_multilinear_map 𝕜 (fun (i : fin (composition.length c)) => F) G) :
    continuous_multilinear_map 𝕜 (fun (i : fin n) => E) G :=
  multilinear_map.mk_continuous (comp_along_composition_aux p c f)
    (norm f *
      finset.prod finset.univ
        fun (i : fin (composition.length c)) => norm (p (composition.blocks_fun c i)))
    (comp_along_composition_aux_bound p c f)

@[simp] theorem comp_along_composition_apply {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {n : ℕ}
    (p : formal_multilinear_series 𝕜 E F) (c : composition n)
    (f : continuous_multilinear_map 𝕜 (fun (i : fin (composition.length c)) => F) G)
    (v : fin n → E) :
    coe_fn (comp_along_composition p c f) v =
        coe_fn f (formal_multilinear_series.apply_composition p c v) :=
  rfl

end continuous_multilinear_map


namespace formal_multilinear_series


/-- Given two formal multilinear series `q` and `p` and a composition `c` of `n`, one may
form a continuous multilinear map in `n` variables by applying the right coefficient of `p` to each
block of the composition, and then applying `q c.length` to the resulting vector. It is
called `q.comp_along_composition p c`. It is constructed from the analogous multilinear
function `q.comp_along_composition_aux p c`, together with a norm control to get
the continuity. -/
def comp_along_composition {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {n : ℕ} (q : formal_multilinear_series 𝕜 F G)
    (p : formal_multilinear_series 𝕜 E F) (c : composition n) :
    continuous_multilinear_map 𝕜 (fun (i : fin n) => E) G :=
  continuous_multilinear_map.comp_along_composition p c (q (composition.length c))

@[simp] theorem comp_along_composition_apply {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {n : ℕ}
    (q : formal_multilinear_series 𝕜 F G) (p : formal_multilinear_series 𝕜 E F) (c : composition n)
    (v : fin n → E) :
    coe_fn (comp_along_composition q p c) v =
        coe_fn (q (composition.length c)) (apply_composition p c v) :=
  rfl

/-- The norm of `q.comp_along_composition p c` is controlled by the product of
the norms of the relevant bits of `q` and `p`. -/
theorem comp_along_composition_norm {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {n : ℕ} (q : formal_multilinear_series 𝕜 F G)
    (p : formal_multilinear_series 𝕜 E F) (c : composition n) :
    norm (comp_along_composition q p c) ≤
        norm (q (composition.length c)) *
          finset.prod finset.univ
            fun (i : fin (composition.length c)) => norm (p (composition.blocks_fun c i)) :=
  sorry

theorem comp_along_composition_nnnorm {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {n : ℕ} (q : formal_multilinear_series 𝕜 F G)
    (p : formal_multilinear_series 𝕜 E F) (c : composition n) :
    nnnorm (comp_along_composition q p c) ≤
        nnnorm (q (composition.length c)) *
          finset.prod finset.univ
            fun (i : fin (composition.length c)) => nnnorm (p (composition.blocks_fun c i)) :=
  sorry

/-- Formal composition of two formal multilinear series. The `n`-th coefficient in the composition
is defined to be the sum of `q.comp_along_composition p c` over all compositions of
`n`. In other words, this term (as a multilinear function applied to `v_0, ..., v_{n-1}`) is
`∑'_{k} ∑'_{i₁ + ... + iₖ = n} pₖ (q_{i_1} (...), ..., q_{i_k} (...))`, where one puts all variables
`v_0, ..., v_{n-1}` in increasing order in the dots.-/
protected def comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4}
    [normed_group G] [normed_space 𝕜 G] (q : formal_multilinear_series 𝕜 F G)
    (p : formal_multilinear_series 𝕜 E F) : formal_multilinear_series 𝕜 E G :=
  fun (n : ℕ) => finset.sum finset.univ fun (c : composition n) => comp_along_composition q p c

/-- The `0`-th coefficient of `q.comp p` is `q 0`. Since these maps are multilinear maps in zero
variables, but on different spaces, we can not state this directly, so we state it when applied to
arbitrary vectors (which have to be the zero vector). -/
theorem comp_coeff_zero {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4}
    [normed_group G] [normed_space 𝕜 G] (q : formal_multilinear_series 𝕜 F G)
    (p : formal_multilinear_series 𝕜 E F) (v : fin 0 → E) (v' : fin 0 → F) :
    coe_fn
          (formal_multilinear_series.comp 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 G _inst_6
            _inst_7 q p 0)
          v =
        coe_fn (q 0) v' :=
  sorry

@[simp] theorem comp_coeff_zero' {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {G : Type u_4} [normed_group G] [normed_space 𝕜 G] (q : formal_multilinear_series 𝕜 F G)
    (p : formal_multilinear_series 𝕜 E F) (v : fin 0 → E) :
    coe_fn
          (formal_multilinear_series.comp 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 G _inst_6
            _inst_7 q p 0)
          v =
        coe_fn (q 0) fun (i : fin 0) => 0 :=
  comp_coeff_zero 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 G _inst_6 _inst_7 q p v
    fun (i : fin 0) => 0

/-- The `0`-th coefficient of `q.comp p` is `q 0`. When `p` goes from `E` to `E`, this can be
expressed as a direct equality -/
theorem comp_coeff_zero'' {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    (q : formal_multilinear_series 𝕜 E F) (p : formal_multilinear_series 𝕜 E E) :
    formal_multilinear_series.comp 𝕜 _inst_1 E _inst_2 _inst_3 E _inst_2 _inst_3 F _inst_4 _inst_5 q
          p 0 =
        q 0 :=
  continuous_multilinear_map.ext
    fun (v : fin 0 → E) =>
      comp_coeff_zero 𝕜 _inst_1 E _inst_2 _inst_3 E _inst_2 _inst_3 F _inst_4 _inst_5 q p v v

/-- The first coefficient of a composition of formal multilinear series is the composition of the
first coefficients seen as continuous linear maps. -/
theorem comp_coeff_one {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4}
    [normed_group G] [normed_space 𝕜 G] (q : formal_multilinear_series 𝕜 F G)
    (p : formal_multilinear_series 𝕜 E F) (v : fin 1 → E) :
    coe_fn
          (formal_multilinear_series.comp 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 G _inst_6
            _inst_7 q p 1)
          v =
        coe_fn (q 1) fun (i : fin 1) => coe_fn (p 1) v :=
  sorry

theorem remove_zero_comp_of_pos {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {G : Type u_4} [normed_group G] [normed_space 𝕜 G] (q : formal_multilinear_series 𝕜 F G)
    (p : formal_multilinear_series 𝕜 E F) {n : ℕ} (hn : 0 < n) :
    formal_multilinear_series.comp 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 G _inst_6 _inst_7
          (remove_zero q) p n =
        formal_multilinear_series.comp 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 G _inst_6
          _inst_7 q p n :=
  sorry

@[simp] theorem comp_remove_zero {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {G : Type u_4} [normed_group G] [normed_space 𝕜 G] (q : formal_multilinear_series 𝕜 F G)
    (p : formal_multilinear_series 𝕜 E F) :
    formal_multilinear_series.comp 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 G _inst_6 _inst_7 q
          (remove_zero p) =
        formal_multilinear_series.comp 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 G _inst_6
          _inst_7 q p :=
  sorry

/-!
### The identity formal power series

We will now define the identity power series, and show that it is a neutral element for left and
right composition.
-/

/-- The identity formal multilinear series, with all coefficients equal to `0` except for `n = 1`
where it is (the continuous multilinear version of) the identity. -/
def id (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] (E : Type u_2) [normed_group E]
    [normed_space 𝕜 E] : formal_multilinear_series 𝕜 E E :=
  sorry

/-- The first coefficient of `id 𝕜 E` is the identity. -/
@[simp] theorem id_apply_one (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] (E : Type u_2)
    [normed_group E] [normed_space 𝕜 E] (v : fin 1 → E) : coe_fn (id 𝕜 E 1) v = v 0 :=
  rfl

/-- The `n`th coefficient of `id 𝕜 E` is the identity when `n = 1`. We state this in a dependent
way, as it will often appear in this form. -/
theorem id_apply_one' (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] (E : Type u_2) [normed_group E]
    [normed_space 𝕜 E] {n : ℕ} (h : n = 1) (v : fin n → E) :
    coe_fn (id 𝕜 E n) v = v { val := 0, property := Eq.symm h ▸ zero_lt_one } :=
  eq.drec (fun (v : fin 1 → E) => id_apply_one 𝕜 E v) (Eq.symm h) v

/-- For `n ≠ 1`, the `n`-th coefficient of `id 𝕜 E` is zero, by definition. -/
@[simp] theorem id_apply_ne_one (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] (E : Type u_2)
    [normed_group E] [normed_space 𝕜 E] {n : ℕ} (h : n ≠ 1) : id 𝕜 E n = 0 :=
  sorry

@[simp] theorem comp_id {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    (p : formal_multilinear_series 𝕜 E F) :
    formal_multilinear_series.comp 𝕜 _inst_1 E _inst_2 _inst_3 E _inst_2 _inst_3 F _inst_4 _inst_5 p
          (id 𝕜 E) =
        p :=
  sorry

@[simp] theorem id_comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    (p : formal_multilinear_series 𝕜 E F) (h : p 0 = 0) :
    formal_multilinear_series.comp 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 F _inst_4 _inst_5
          (id 𝕜 F) p =
        p :=
  sorry

/-! ### Summability properties of the composition of formal power series-/

/-- If two formal multilinear series have positive radius of convergence, then the terms appearing
in the definition of their composition are also summable (when multiplied by a suitable positive
geometric term). -/
theorem comp_summable_nnreal {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {G : Type u_4} [normed_group G] [normed_space 𝕜 G] (q : formal_multilinear_series 𝕜 F G)
    (p : formal_multilinear_series 𝕜 E F) (hq : 0 < radius q) (hp : 0 < radius p) :
    ∃ (r : nnreal),
        ∃ (H : r > 0),
          summable
            fun (i : sigma fun (n : ℕ) => composition n) =>
              nnnorm (comp_along_composition q p (sigma.snd i)) * r ^ sigma.fst i :=
  sorry

/-- Bounding below the radius of the composition of two formal multilinear series assuming
summability over all compositions. -/
theorem le_comp_radius_of_summable {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {G : Type u_4} [normed_group G] [normed_space 𝕜 G] (q : formal_multilinear_series 𝕜 F G)
    (p : formal_multilinear_series 𝕜 E F) (r : nnreal)
    (hr :
      summable
        fun (i : sigma fun (n : ℕ) => composition n) =>
          nnnorm (comp_along_composition q p (sigma.snd i)) * r ^ sigma.fst i) :
    ↑r ≤
        radius
          (formal_multilinear_series.comp 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 G _inst_6
            _inst_7 q p) :=
  sorry

/-!
### Composing analytic functions

Now, we will prove that the composition of the partial sums of `q` and `p` up to order `N` is
given by a sum over some large subset of `Σ n, composition n` of `q.comp_along_composition p`, to
deduce that the series for `q.comp p` indeed converges to `g ∘ f` when `q` is a power series for
`g` and `p` is a power series for `f`.

This proof is a big reindexing argument of a sum. Since it is a bit involved, we define first
the source of the change of variables (`comp_partial_source`), its target
(`comp_partial_target`) and the change of variables itself (`comp_change_of_variables`) before
giving the main statement in `comp_partial_sum`. -/

/-- Source set in the change of variables to compute the composition of partial sums of formal
power series.
See also `comp_partial_sum`. -/
def comp_partial_sum_source (m : ℕ) (M : ℕ) (N : ℕ) : finset (sigma fun (n : ℕ) => fin n → ℕ) :=
  finset.sigma (finset.Ico m M) fun (n : ℕ) => fintype.pi_finset fun (i : fin n) => finset.Ico 1 N

@[simp] theorem mem_comp_partial_sum_source_iff (m : ℕ) (M : ℕ) (N : ℕ)
    (i : sigma fun (n : ℕ) => fin n → ℕ) :
    i ∈ comp_partial_sum_source m M N ↔
        (m ≤ sigma.fst i ∧ sigma.fst i < M) ∧
          ∀ (a : fin (sigma.fst i)), 1 ≤ sigma.snd i a ∧ sigma.snd i a < N :=
  sorry

/-- Change of variables appearing to compute the composition of partial sums of formal
power series -/
def comp_change_of_variables (m : ℕ) (M : ℕ) (N : ℕ) (i : sigma fun (n : ℕ) => fin n → ℕ)
    (hi : i ∈ comp_partial_sum_source m M N) : sigma fun (n : ℕ) => composition n :=
  sigma.cases_on i
    (fun (n : ℕ) (f : fin n → ℕ) (hi : sigma.mk n f ∈ comp_partial_sum_source m M N) =>
      sigma.mk (finset.sum finset.univ fun (j : fin n) => f j)
        (composition.mk (list.of_fn fun (j : fin n) => f j) sorry sorry))
    hi

@[simp] theorem comp_change_of_variables_length (m : ℕ) (M : ℕ) (N : ℕ)
    {i : sigma fun (n : ℕ) => fin n → ℕ} (hi : i ∈ comp_partial_sum_source m M N) :
    composition.length (sigma.snd (comp_change_of_variables m M N i hi)) = sigma.fst i :=
  sorry

theorem comp_change_of_variables_blocks_fun (m : ℕ) (M : ℕ) (N : ℕ)
    {i : sigma fun (n : ℕ) => fin n → ℕ} (hi : i ∈ comp_partial_sum_source m M N)
    (j : fin (sigma.fst i)) :
    composition.blocks_fun (sigma.snd (comp_change_of_variables m M N i hi))
          { val := ↑j,
            property := Eq.symm (comp_change_of_variables_length m M N hi) ▸ subtype.property j } =
        sigma.snd i j :=
  sorry

/-- Target set in the change of variables to compute the composition of partial sums of formal
power series, here given a a set. -/
def comp_partial_sum_target_set (m : ℕ) (M : ℕ) (N : ℕ) :
    set (sigma fun (n : ℕ) => composition n) :=
  set_of
    fun (i : sigma fun (n : ℕ) => composition n) =>
      m ≤ composition.length (sigma.snd i) ∧
        composition.length (sigma.snd i) < M ∧
          ∀ (j : fin (composition.length (sigma.snd i))), composition.blocks_fun (sigma.snd i) j < N

theorem comp_partial_sum_target_subset_image_comp_partial_sum_source (m : ℕ) (M : ℕ) (N : ℕ)
    (i : sigma fun (n : ℕ) => composition n) (hi : i ∈ comp_partial_sum_target_set m M N) :
    ∃ (j : sigma fun (n : ℕ) => fin n → ℕ),
        ∃ (hj : j ∈ comp_partial_sum_source m M N), i = comp_change_of_variables m M N j hj :=
  sorry

/-- Target set in the change of variables to compute the composition of partial sums of formal
power series, here given a a finset.
See also `comp_partial_sum`. -/
def comp_partial_sum_target (m : ℕ) (M : ℕ) (N : ℕ) : finset (sigma fun (n : ℕ) => composition n) :=
  set.finite.to_finset sorry

@[simp] theorem mem_comp_partial_sum_target_iff {m : ℕ} {M : ℕ} {N : ℕ}
    {a : sigma fun (n : ℕ) => composition n} :
    a ∈ comp_partial_sum_target m M N ↔
        m ≤ composition.length (sigma.snd a) ∧
          composition.length (sigma.snd a) < M ∧
            ∀ (j : fin (composition.length (sigma.snd a))),
              composition.blocks_fun (sigma.snd a) j < N :=
  sorry

/-- `comp_change_of_variables m M N` is a bijection between `comp_partial_sum_source m M N`
and `comp_partial_sum_target m M N`, yielding equal sums for functions that correspond to each
other under the bijection. As `comp_change_of_variables m M N` is a dependent function, stating
that it is a bijection is not directly possible, but the consequence on sums can be stated
more easily. -/
theorem comp_change_of_variables_sum {α : Type u_1} [add_comm_monoid α] (m : ℕ) (M : ℕ) (N : ℕ)
    (f : (sigma fun (n : ℕ) => fin n → ℕ) → α) (g : (sigma fun (n : ℕ) => composition n) → α)
    (h :
      ∀ (e : sigma fun (n : ℕ) => fin n → ℕ) (he : e ∈ comp_partial_sum_source m M N),
        f e = g (comp_change_of_variables m M N e he)) :
    (finset.sum (comp_partial_sum_source m M N) fun (e : sigma fun (n : ℕ) => fin n → ℕ) => f e) =
        finset.sum (comp_partial_sum_target m M N)
          fun (e : sigma fun (n : ℕ) => composition n) => g e :=
  sorry

/-- The auxiliary set corresponding to the composition of partial sums asymptotically contains
all possible compositions. -/
theorem comp_partial_sum_target_tendsto_at_top :
    filter.tendsto (fun (N : ℕ) => comp_partial_sum_target 0 N N) filter.at_top filter.at_top :=
  sorry

/-- Composing the partial sums of two multilinear series coincides with the sum over all
compositions in `comp_partial_sum_target 0 N N`. This is precisely the motivation for the
definition of `comp_partial_sum_target`. -/
theorem comp_partial_sum {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4}
    [normed_group G] [normed_space 𝕜 G] (q : formal_multilinear_series 𝕜 F G)
    (p : formal_multilinear_series 𝕜 E F) (N : ℕ) (z : E) :
    partial_sum q N (finset.sum (finset.Ico 1 N) fun (i : ℕ) => coe_fn (p i) fun (j : fin i) => z) =
        finset.sum (comp_partial_sum_target 0 N N)
          fun (i : sigma fun (n : ℕ) => composition n) =>
            coe_fn (comp_along_composition q p (sigma.snd i)) fun (j : fin (sigma.fst i)) => z :=
  sorry

end formal_multilinear_series


/-- If two functions `g` and `f` have power series `q` and `p` respectively at `f x` and `x`, then
`g ∘ f` admits the power series `q.comp p` at `x`. -/
theorem has_fpower_series_at.comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {g : F → G} {f : E → F}
    {q : formal_multilinear_series 𝕜 F G} {p : formal_multilinear_series 𝕜 E F} {x : E}
    (hg : has_fpower_series_at g q (f x)) (hf : has_fpower_series_at f p x) :
    has_fpower_series_at (g ∘ f)
        (formal_multilinear_series.comp 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 G _inst_6
          _inst_7 q p)
        x :=
  sorry

/-- If two functions `g` and `f` are analytic respectively at `f x` and `x`, then `g ∘ f` is
analytic at `x`. -/
theorem analytic_at.comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4}
    [normed_group G] [normed_space 𝕜 G] {g : F → G} {f : E → F} {x : E} (hg : analytic_at 𝕜 g (f x))
    (hf : analytic_at 𝕜 f x) : analytic_at 𝕜 (g ∘ f) x :=
  sorry

/-!
### Associativity of the composition of formal multilinear series

In this paragraph, we us prove the associativity of the composition of formal power series.
By definition,
```
(r.comp q).comp p n v
= ∑_{i₁ + ... + iₖ = n} (r.comp q)ₖ (p_{i₁} (v₀, ..., v_{i₁ -1}), p_{i₂} (...), ..., p_{iₖ}(...))
= ∑_{a : composition n} (r.comp q) a.length (apply_composition p a v)
```
decomposing `r.comp q` in the same way, we get
```
(r.comp q).comp p n v
= ∑_{a : composition n} ∑_{b : composition a.length}
  r b.length (apply_composition q b (apply_composition p a v))
```
On the other hand,
```
r.comp (q.comp p) n v = ∑_{c : composition n} r c.length (apply_composition (q.comp p) c v)
```
Here, `apply_composition (q.comp p) c v` is a vector of length `c.length`, whose `i`-th term is
given by `(q.comp p) (c.blocks_fun i) (v_l, v_{l+1}, ..., v_{m-1})` where `{l, ..., m-1}` is the
`i`-th block in the composition `c`, of length `c.blocks_fun i` by definition. To compute this term,
we expand it as `∑_{dᵢ : composition (c.blocks_fun i)} q dᵢ.length (apply_composition p dᵢ v')`,
where `v' = (v_l, v_{l+1}, ..., v_{m-1})`. Therefore, we get
```
r.comp (q.comp p) n v =
∑_{c : composition n} ∑_{d₀ : composition (c.blocks_fun 0),
  ..., d_{c.length - 1} : composition (c.blocks_fun (c.length - 1))}
  r c.length (λ i, q dᵢ.length (apply_composition p dᵢ v'ᵢ))
```
To show that these terms coincide, we need to explain how to reindex the sums to put them in
bijection (and then the terms we are summing will correspond to each other). Suppose we have a
composition `a` of `n`, and a composition `b` of `a.length`. Then `b` indicates how to group
together some blocks of `a`, giving altogether `b.length` blocks of blocks. These blocks of blocks
can be called `d₀, ..., d_{a.length - 1}`, and one obtains a composition `c` of `n` by saying that
each `dᵢ` is one single block. Conversely, if one starts from `c` and the `dᵢ`s, one can concatenate
the `dᵢ`s to obtain a composition `a` of `n`, and register the lengths of the `dᵢ`s in a composition
`b` of `a.length`.

An example might be enlightening. Suppose `a = [2, 2, 3, 4, 2]`. It is a composition of
length 5 of 13. The content of the blocks may be represented as `0011222333344`.
Now take `b = [2, 3]` as a composition of `a.length = 5`. It says that the first 2 blocks of `a`
should be merged, and the last 3 blocks of `a` should be merged, giving a new composition of `13`
made of two blocks of length `4` and `9`, i.e., `c = [4, 9]`. But one can also remember that
the new first block was initially made of two blocks of size `2`, so `d₀ = [2, 2]`, and the new
second block was initially made of three blocks of size `3`, `4` and `2`, so `d₁ = [3, 4, 2]`.

This equivalence is called `composition.sigma_equiv_sigma_pi n` below.

We start with preliminary results on compositions, of a very specialized nature, then define the
equivalence `composition.sigma_equiv_sigma_pi n`, and we deduce finally the associativity of
composition of formal multilinear series in `formal_multilinear_series.comp_assoc`.
-/

namespace composition


/-- Rewriting equality in the dependent type `Σ (a : composition n), composition a.length)` in
non-dependent terms with lists, requiring that the blocks coincide. -/
theorem sigma_composition_eq_iff {n : ℕ}
    (i : sigma fun (a : composition n) => composition (length a))
    (j : sigma fun (a : composition n) => composition (length a)) :
    i = j ↔
        blocks (sigma.fst i) = blocks (sigma.fst j) ∧ blocks (sigma.snd i) = blocks (sigma.snd j) :=
  sorry

/-- Rewriting equality in the dependent type
`Σ (c : composition n), Π (i : fin c.length), composition (c.blocks_fun i)` in
non-dependent terms with lists, requiring that the lists of blocks coincide. -/
theorem sigma_pi_composition_eq_iff {n : ℕ}
    (u : sigma fun (c : composition n) => (i : fin (length c)) → composition (blocks_fun c i))
    (v : sigma fun (c : composition n) => (i : fin (length c)) → composition (blocks_fun c i)) :
    u = v ↔
        (list.of_fn fun (i : fin (length (sigma.fst u))) => blocks (sigma.snd u i)) =
          list.of_fn fun (i : fin (length (sigma.fst v))) => blocks (sigma.snd v i) :=
  sorry

/-- When `a` is a composition of `n` and `b` is a composition of `a.length`, `a.gather b` is the
composition of `n` obtained by gathering all the blocks of `a` corresponding to a block of `b`.
For instance, if `a = [6, 5, 3, 5, 2]` and `b = [2, 3]`, one should gather together
the first two blocks of `a` and its last three blocks, giving `a.gather b = [11, 10]`. -/
def gather {n : ℕ} (a : composition n) (b : composition (length a)) : composition n :=
  mk (list.map list.sum (list.split_wrt_composition (blocks a) b)) sorry sorry

theorem length_gather {n : ℕ} (a : composition n) (b : composition (length a)) :
    length (gather a b) = length b :=
  sorry

/-- An auxiliary function used in the definition of `sigma_equiv_sigma_pi` below, associating to
two compositions `a` of `n` and `b` of `a.length`, and an index `i` bounded by the length of
`a.gather b`, the subcomposition of `a` made of those blocks belonging to the `i`-th block of
`a.gather b`. -/
def sigma_composition_aux {n : ℕ} (a : composition n) (b : composition (length a))
    (i : fin (length (gather a b))) : composition (blocks_fun (gather a b) i) :=
  mk (list.nth_le (list.split_wrt_composition (blocks a) b) ↑i sorry) sorry sorry

theorem length_sigma_composition_aux {n : ℕ} (a : composition n) (b : composition (length a))
    (i : fin (length b)) :
    length
          (sigma_composition_aux a b
            { val := ↑i, property := Eq.symm (length_gather a b) ▸ subtype.property i }) =
        blocks_fun b i :=
  sorry

theorem blocks_fun_sigma_composition_aux {n : ℕ} (a : composition n) (b : composition (length a))
    (i : fin (length b)) (j : fin (blocks_fun b i)) :
    blocks_fun
          (sigma_composition_aux a b
            { val := ↑i, property := Eq.symm (length_gather a b) ▸ subtype.property i })
          { val := ↑j,
            property := Eq.symm (length_sigma_composition_aux a b i) ▸ subtype.property j } =
        blocks_fun a (coe_fn (embedding b i) j) :=
  sorry

/-- Auxiliary lemma to prove that the composition of formal multilinear series is associative.

Consider a composition `a` of `n` and a composition `b` of `a.length`. Grouping together some
blocks of `a` according to `b` as in `a.gather b`, one can compute the total size of the blocks
of `a` up to an index `size_up_to b i + j` (where the `j` corresponds to a set of blocks of `a`
that do not fill a whole block of `a.gather b`). The first part corresponds to a sum of blocks
in `a.gather b`, and the second one to a sum of blocks in the next block of
`sigma_composition_aux a b`. This is the content of this lemma. -/
theorem size_up_to_size_up_to_add {n : ℕ} (a : composition n) (b : composition (length a)) {i : ℕ}
    {j : ℕ} (hi : i < length b) (hj : j < blocks_fun b { val := i, property := hi }) :
    size_up_to a (size_up_to b i + j) =
        size_up_to (gather a b) i +
          size_up_to
            (sigma_composition_aux a b { val := i, property := Eq.symm (length_gather a b) ▸ hi })
            j :=
  sorry

/--
Natural equivalence between `(Σ (a : composition n), composition a.length)` and
`(Σ (c : composition n), Π (i : fin c.length), composition (c.blocks_fun i))`, that shows up as a
change of variables in the proof that composition of formal multilinear series is associative.

Consider a composition `a` of `n` and a composition `b` of `a.length`. Then `b` indicates how to
group together some blocks of `a`, giving altogether `b.length` blocks of blocks. These blocks of
blocks can be called `d₀, ..., d_{a.length - 1}`, and one obtains a composition `c` of `n` by
saying that each `dᵢ` is one single block. The map `⟨a, b⟩ → ⟨c, (d₀, ..., d_{a.length - 1})⟩` is
the direct map in the equiv.

Conversely, if one starts from `c` and the `dᵢ`s, one can join the `dᵢ`s to obtain a composition
`a` of `n`, and register the lengths of the `dᵢ`s in a composition `b` of `a.length`. This is the
inverse map of the equiv.
-/
def sigma_equiv_sigma_pi (n : ℕ) :
    (sigma fun (a : composition n) => composition (length a)) ≃
        sigma fun (c : composition n) => (i : fin (length c)) → composition (blocks_fun c i) :=
  equiv.mk
    (fun (i : sigma fun (a : composition n) => composition (length a)) =>
      sigma.mk (gather (sigma.fst i) (sigma.snd i))
        (sigma_composition_aux (sigma.fst i) (sigma.snd i)))
    (fun
      (i : sigma fun (c : composition n) => (i : fin (length c)) → composition (blocks_fun c i)) =>
      sigma.mk
        (mk (list.join (list.of_fn fun (j : fin (length (sigma.fst i))) => blocks (sigma.snd i j)))
          sorry sorry)
        (mk (list.of_fn fun (j : fin (length (sigma.fst i))) => length (sigma.snd i j)) sorry
          sorry))
    sorry sorry

end composition


namespace formal_multilinear_series


theorem comp_assoc {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4}
    [normed_group G] [normed_space 𝕜 G] {H : Type u_5} [normed_group H] [normed_space 𝕜 H]
    (r : formal_multilinear_series 𝕜 G H) (q : formal_multilinear_series 𝕜 F G)
    (p : formal_multilinear_series 𝕜 E F) :
    formal_multilinear_series.comp 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 H _inst_8 _inst_9
          (formal_multilinear_series.comp 𝕜 _inst_1 F _inst_4 _inst_5 G _inst_6 _inst_7 H _inst_8
            _inst_9 r q)
          p =
        formal_multilinear_series.comp 𝕜 _inst_1 E _inst_2 _inst_3 G _inst_6 _inst_7 H _inst_8
          _inst_9 r
          (formal_multilinear_series.comp 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 G _inst_6
            _inst_7 q p) :=
  sorry

end Mathlib