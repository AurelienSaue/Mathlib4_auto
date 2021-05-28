/-
Copyright (c) 2020 Yury Kudryashov All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.linear_algebra.basic
import PostPort

universes u v w l u_1 u_2 u_3 u_4 

namespace Mathlib

/-!
# Partially defined linear maps

A `linear_pmap R E F` is a linear map from a submodule of `E` to `F`. We define
a `semilattice_inf_bot` instance on this this, and define three operations:

* `mk_span_singleton` defines a partial linear map defined on the span of a singleton.
* `sup` takes two partial linear maps `f`, `g` that agree on the intersection of their
  domains, and returns the unique partial linear map on `f.domain ⊔ g.domain` that
  extends both `f` and `g`.
* `Sup` takes a `directed_on (≤)` set of partial linear maps, and returns the unique
  partial linear map on the `Sup` of their domains that extends all these maps.

Partially defined maps are currently used in `mathlib` to prove Hahn-Banach theorem
and its variations. Namely, `linear_pmap.Sup` implies that every chain of `linear_pmap`s
is bounded above.

Another possible use (not yet in `mathlib`) would be the theory of unbounded linear operators.
-/

/-- A `linear_pmap R E F` is a linear map from a submodule of `E` to `F`. -/
structure linear_pmap (R : Type u) [ring R] (E : Type v) [add_comm_group E] [module R E] (F : Type w) [add_comm_group F] [module R F] 
where
  domain : submodule R E
  to_fun : linear_map R (↥domain) F

namespace linear_pmap


protected instance has_coe_to_fun {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] : has_coe_to_fun (linear_pmap R E F) :=
  has_coe_to_fun.mk (fun (f : linear_pmap R E F) => ↥(domain f) → F) fun (f : linear_pmap R E F) => ⇑(to_fun f)

@[simp] theorem to_fun_eq_coe {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] (f : linear_pmap R E F) (x : ↥(domain f)) : coe_fn (to_fun f) x = coe_fn f x :=
  rfl

@[simp] theorem map_zero {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] (f : linear_pmap R E F) : coe_fn f 0 = 0 :=
  linear_map.map_zero (to_fun f)

theorem map_add {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] (f : linear_pmap R E F) (x : ↥(domain f)) (y : ↥(domain f)) : coe_fn f (x + y) = coe_fn f x + coe_fn f y :=
  linear_map.map_add (to_fun f) x y

theorem map_neg {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] (f : linear_pmap R E F) (x : ↥(domain f)) : coe_fn f (-x) = -coe_fn f x :=
  linear_map.map_neg (to_fun f) x

theorem map_sub {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] (f : linear_pmap R E F) (x : ↥(domain f)) (y : ↥(domain f)) : coe_fn f (x - y) = coe_fn f x - coe_fn f y :=
  linear_map.map_sub (to_fun f) x y

theorem map_smul {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] (f : linear_pmap R E F) (c : R) (x : ↥(domain f)) : coe_fn f (c • x) = c • coe_fn f x :=
  linear_map.map_smul (to_fun f) c x

@[simp] theorem mk_apply {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] (p : submodule R E) (f : linear_map R (↥p) F) (x : ↥p) : coe_fn (mk p f) x = coe_fn f x :=
  rfl

/-- The unique `linear_pmap` on `R ∙ x` that sends `x` to `y`. This version works for modules
over rings, and requires a proof of `∀ c, c • x = 0 → c • y = 0`. -/
def mk_span_singleton' {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] (x : E) (y : F) (H : ∀ (c : R), c • x = 0 → c • y = 0) : linear_pmap R E F :=
  mk (submodule.span R (singleton x))
    (linear_map.mk (fun (z : ↥(submodule.span R (singleton x))) => classical.some sorry • y) sorry sorry)

@[simp] theorem domain_mk_span_singleton {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] (x : E) (y : F) (H : ∀ (c : R), c • x = 0 → c • y = 0) : domain (mk_span_singleton' x y H) = submodule.span R (singleton x) :=
  rfl

@[simp] theorem mk_span_singleton_apply {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] (x : E) (y : F) (H : ∀ (c : R), c • x = 0 → c • y = 0) (c : R) (h : c • x ∈ domain (mk_span_singleton' x y H)) : coe_fn (mk_span_singleton' x y H) { val := c • x, property := h } = c • y := sorry

/-- The unique `linear_pmap` on `span R {x}` that sends a non-zero vector `x` to `y`.
This version works for modules over division rings. -/
def mk_span_singleton {K : Type u_1} {E : Type u_2} {F : Type u_3} [division_ring K] [add_comm_group E] [module K E] [add_comm_group F] [module K F] (x : E) (y : F) (hx : x ≠ 0) : linear_pmap K E F :=
  mk_span_singleton' x y sorry

/-- Projection to the first coordinate as a `linear_pmap` -/
protected def fst {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] (p : submodule R E) (p' : submodule R F) : linear_pmap R (E × F) E :=
  mk (submodule.prod p p') (linear_map.comp (linear_map.fst R E F) (submodule.subtype (submodule.prod p p')))

@[simp] theorem fst_apply {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] (p : submodule R E) (p' : submodule R F) (x : ↥(submodule.prod p p')) : coe_fn (linear_pmap.fst p p') x = prod.fst ↑x :=
  rfl

/-- Projection to the second coordinate as a `linear_pmap` -/
protected def snd {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] (p : submodule R E) (p' : submodule R F) : linear_pmap R (E × F) F :=
  mk (submodule.prod p p') (linear_map.comp (linear_map.snd R E F) (submodule.subtype (submodule.prod p p')))

@[simp] theorem snd_apply {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] (p : submodule R E) (p' : submodule R F) (x : ↥(submodule.prod p p')) : coe_fn (linear_pmap.snd p p') x = prod.snd ↑x :=
  rfl

protected instance has_neg {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] : Neg (linear_pmap R E F) :=
  { neg := fun (f : linear_pmap R E F) => mk (domain f) (-to_fun f) }

@[simp] theorem neg_apply {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] (f : linear_pmap R E F) (x : ↥(domain (-f))) : coe_fn (-f) x = -coe_fn f x :=
  rfl

protected instance has_le {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] : HasLessEq (linear_pmap R E F) :=
  { LessEq :=
      fun (f g : linear_pmap R E F) =>
        domain f ≤ domain g ∧ ∀ {x : ↥(domain f)} {y : ↥(domain g)}, ↑x = ↑y → coe_fn f x = coe_fn g y }

theorem eq_of_le_of_domain_eq {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] {f : linear_pmap R E F} {g : linear_pmap R E F} (hle : f ≤ g) (heq : domain f = domain g) : f = g := sorry

/-- Given two partial linear maps `f`, `g`, the set of points `x` such that
both `f` and `g` are defined at `x` and `f x = g x` form a submodule. -/
def eq_locus {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] (f : linear_pmap R E F) (g : linear_pmap R E F) : submodule R E :=
  submodule.mk
    (set_of
      fun (x : E) =>
        ∃ (hf : x ∈ domain f),
          ∃ (hg : x ∈ domain g), coe_fn f { val := x, property := hf } = coe_fn g { val := x, property := hg })
    sorry sorry sorry

protected instance has_inf {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] : has_inf (linear_pmap R E F) :=
  has_inf.mk fun (f g : linear_pmap R E F) => mk (eq_locus f g) (linear_map.comp (to_fun f) (submodule.of_le sorry))

protected instance has_bot {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] : has_bot (linear_pmap R E F) :=
  has_bot.mk (mk ⊥ 0)

protected instance inhabited {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] : Inhabited (linear_pmap R E F) :=
  { default := ⊥ }

protected instance semilattice_inf_bot {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] : semilattice_inf_bot (linear_pmap R E F) :=
  semilattice_inf_bot.mk ⊥ LessEq (order_bot.lt._default LessEq) sorry sorry sorry sorry has_inf.inf sorry sorry sorry

theorem le_of_eq_locus_ge {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] {f : linear_pmap R E F} {g : linear_pmap R E F} (H : domain f ≤ eq_locus f g) : f ≤ g := sorry

theorem domain_mono {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] : strict_mono domain :=
  fun (f g : linear_pmap R E F) (hlt : f < g) =>
    lt_of_le_of_ne (and.left (and.left hlt))
      fun (heq : domain f = domain g) => ne_of_lt hlt (eq_of_le_of_domain_eq (le_of_lt hlt) heq)

/-- Given two partial linear maps that agree on the intersection of their domains,
`f.sup g h` is the unique partial linear map on `f.domain ⊔ g.domain` that agrees
with `f` and `g`. -/
protected def sup {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] (f : linear_pmap R E F) (g : linear_pmap R E F) (h : ∀ (x : ↥(domain f)) (y : ↥(domain g)), ↑x = ↑y → coe_fn f x = coe_fn g y) : linear_pmap R E F :=
  mk (domain f ⊔ domain g) (classical.some (sup_aux f g h))

@[simp] theorem domain_sup {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] (f : linear_pmap R E F) (g : linear_pmap R E F) (h : ∀ (x : ↥(domain f)) (y : ↥(domain g)), ↑x = ↑y → coe_fn f x = coe_fn g y) : domain (linear_pmap.sup f g h) = domain f ⊔ domain g :=
  rfl

theorem sup_apply {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] {f : linear_pmap R E F} {g : linear_pmap R E F} (H : ∀ (x : ↥(domain f)) (y : ↥(domain g)), ↑x = ↑y → coe_fn f x = coe_fn g y) (x : ↥(domain f)) (y : ↥(domain g)) (z : ↥(domain (linear_pmap.sup f g H))) (hz : ↑x + ↑y = ↑z) : coe_fn (linear_pmap.sup f g H) z = coe_fn f x + coe_fn g y :=
  classical.some_spec (sup_aux f g H) x y z hz

protected theorem left_le_sup {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] (f : linear_pmap R E F) (g : linear_pmap R E F) (h : ∀ (x : ↥(domain f)) (y : ↥(domain g)), ↑x = ↑y → coe_fn f x = coe_fn g y) : f ≤ linear_pmap.sup f g h := sorry

protected theorem right_le_sup {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] (f : linear_pmap R E F) (g : linear_pmap R E F) (h : ∀ (x : ↥(domain f)) (y : ↥(domain g)), ↑x = ↑y → coe_fn f x = coe_fn g y) : g ≤ linear_pmap.sup f g h := sorry

protected theorem sup_le {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] {f : linear_pmap R E F} {g : linear_pmap R E F} {h : linear_pmap R E F} (H : ∀ (x : ↥(domain f)) (y : ↥(domain g)), ↑x = ↑y → coe_fn f x = coe_fn g y) (fh : f ≤ h) (gh : g ≤ h) : linear_pmap.sup f g H ≤ h := sorry

/-- Hypothesis for `linear_pmap.sup` holds, if `f.domain` is disjoint with `g.domain`. -/
theorem sup_h_of_disjoint {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] (f : linear_pmap R E F) (g : linear_pmap R E F) (h : disjoint (domain f) (domain g)) (x : ↥(domain f)) (y : ↥(domain g)) (hxy : ↑x = ↑y) : coe_fn f x = coe_fn g y := sorry

/-- Glue a collection of partially defined linear maps to a linear map defined on `Sup`
of these submodules. -/
protected def Sup {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] (c : set (linear_pmap R E F)) (hc : directed_on LessEq c) : linear_pmap R E F :=
  mk (Sup (domain '' c)) (classical.some (Sup_aux c hc))

protected theorem le_Sup {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] {c : set (linear_pmap R E F)} (hc : directed_on LessEq c) {f : linear_pmap R E F} (hf : f ∈ c) : f ≤ linear_pmap.Sup c hc :=
  classical.some_spec (Sup_aux c hc) f hf

protected theorem Sup_le {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] {c : set (linear_pmap R E F)} (hc : directed_on LessEq c) {g : linear_pmap R E F} (hg : ∀ (f : linear_pmap R E F), f ∈ c → f ≤ g) : linear_pmap.Sup c hc ≤ g := sorry

end linear_pmap


namespace linear_map


/-- Restrict a linear map to a submodule, reinterpreting the result as a `linear_pmap`. -/
def to_pmap {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] (f : linear_map R E F) (p : submodule R E) : linear_pmap R E F :=
  linear_pmap.mk p (comp f (submodule.subtype p))

@[simp] theorem to_pmap_apply {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] (f : linear_map R E F) (p : submodule R E) (x : ↥p) : coe_fn (to_pmap f p) x = coe_fn f ↑x :=
  rfl

/-- Compose a linear map with a `linear_pmap` -/
def comp_pmap {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] {G : Type u_4} [add_comm_group G] [module R G] (g : linear_map R F G) (f : linear_pmap R E F) : linear_pmap R E G :=
  linear_pmap.mk (linear_pmap.domain f) (comp g (linear_pmap.to_fun f))

@[simp] theorem comp_pmap_apply {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] {G : Type u_4} [add_comm_group G] [module R G] (g : linear_map R F G) (f : linear_pmap R E F) (x : ↥(linear_pmap.domain (comp_pmap g f))) : coe_fn (comp_pmap g f) x = coe_fn g (coe_fn f x) :=
  rfl

end linear_map


namespace linear_pmap


/-- Restrict codomain of a `linear_pmap` -/
def cod_restrict {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] (f : linear_pmap R E F) (p : submodule R F) (H : ∀ (x : ↥(domain f)), coe_fn f x ∈ p) : linear_pmap R E ↥p :=
  mk (domain f) (linear_map.cod_restrict p (to_fun f) H)

/-- Compose two `linear_pmap`s -/
def comp {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] {G : Type u_4} [add_comm_group G] [module R G] (g : linear_pmap R F G) (f : linear_pmap R E F) (H : ∀ (x : ↥(domain f)), coe_fn f x ∈ domain g) : linear_pmap R E G :=
  linear_map.comp_pmap (to_fun g) (cod_restrict f (domain g) H)

/-- `f.coprod g` is the partially defined linear map defined on `f.domain × g.domain`,
and sending `p` to `f p.1 + g p.2`. -/
def coprod {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] {G : Type u_4} [add_comm_group G] [module R G] (f : linear_pmap R E G) (g : linear_pmap R F G) : linear_pmap R (E × F) G :=
  mk (submodule.prod (domain f) (domain g))
    (to_fun (comp f (linear_pmap.fst (domain f) (domain g)) sorry) +
      to_fun (comp g (linear_pmap.snd (domain f) (domain g)) sorry))

@[simp] theorem coprod_apply {R : Type u_1} [ring R] {E : Type u_2} [add_comm_group E] [module R E] {F : Type u_3} [add_comm_group F] [module R F] {G : Type u_4} [add_comm_group G] [module R G] (f : linear_pmap R E G) (g : linear_pmap R F G) (x : ↥(domain (coprod f g))) : coe_fn (coprod f g) x =
  coe_fn f { val := prod.fst ↑x, property := and.left (subtype.property x) } +
    coe_fn g { val := prod.snd ↑x, property := and.right (subtype.property x) } :=
  rfl

