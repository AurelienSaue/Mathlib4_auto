/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Chris Hughes, Mario Carneiro, Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.group.prod
import Mathlib.algebra.ring.basic
import Mathlib.data.equiv.ring
import Mathlib.PostPort

universes u_1 u_3 u_5 u_2 u_4 

namespace Mathlib

/-!
# Semiring, ring etc structures on `R × S`

In this file we define two-binop (`semiring`, `ring` etc) structures on `R × S`. We also prove
trivial `simp` lemmas, and define the following operations on `ring_hom`s:

* `fst R S : R × S →+* R`, `snd R S : R × S →+* R`: projections `prod.fst` and `prod.snd`
  as `ring_hom`s;
* `f.prod g : `R →+* S × T`: sends `x` to `(f x, g x)`;
* `f.prod_map g : `R × S → R' × S'`: `prod.map f g` as a `ring_hom`,
  sends `(x, y)` to `(f x, g y)`.
-/

namespace prod


/-- Product of two semirings is a semiring. -/
protected instance semiring {R : Type u_1} {S : Type u_3} [semiring R] [semiring S] :
    semiring (R × S) :=
  semiring.mk add_comm_monoid.add sorry add_comm_monoid.zero sorry sorry sorry monoid.mul sorry
    monoid.one sorry sorry sorry sorry sorry sorry

/-- Product of two commutative semirings is a commutative semiring. -/
protected instance comm_semiring {R : Type u_1} {S : Type u_3} [comm_semiring R] [comm_semiring S] :
    comm_semiring (R × S) :=
  comm_semiring.mk semiring.add sorry semiring.zero sorry sorry sorry semiring.mul sorry
    semiring.one sorry sorry sorry sorry sorry sorry sorry

/-- Product of two rings is a ring. -/
protected instance ring {R : Type u_1} {S : Type u_3} [ring R] [ring S] : ring (R × S) :=
  ring.mk add_comm_group.add sorry add_comm_group.zero sorry sorry add_comm_group.neg
    add_comm_group.sub sorry sorry semiring.mul sorry semiring.one sorry sorry sorry sorry

/-- Product of two commutative rings is a commutative ring. -/
protected instance comm_ring {R : Type u_1} {S : Type u_3} [comm_ring R] [comm_ring S] :
    comm_ring (R × S) :=
  comm_ring.mk ring.add sorry ring.zero sorry sorry ring.neg ring.sub sorry sorry ring.mul sorry
    ring.one sorry sorry sorry sorry sorry

end prod


namespace ring_hom


/-- Given semirings `R`, `S`, the natural projection homomorphism from `R × S` to `R`.-/
def fst (R : Type u_1) (S : Type u_3) [semiring R] [semiring S] : R × S →+* R :=
  mk prod.fst sorry sorry sorry sorry

/-- Given semirings `R`, `S`, the natural projection homomorphism from `R × S` to `S`.-/
def snd (R : Type u_1) (S : Type u_3) [semiring R] [semiring S] : R × S →+* S :=
  mk prod.snd sorry sorry sorry sorry

@[simp] theorem coe_fst {R : Type u_1} {S : Type u_3} [semiring R] [semiring S] :
    ⇑(fst R S) = prod.fst :=
  rfl

@[simp] theorem coe_snd {R : Type u_1} {S : Type u_3} [semiring R] [semiring S] :
    ⇑(snd R S) = prod.snd :=
  rfl

/-- Combine two ring homomorphisms `f : R →+* S`, `g : R →+* T` into `f.prod g : R →+* S × T`
given by `(f.prod g) x = (f x, g x)` -/
protected def prod {R : Type u_1} {S : Type u_3} {T : Type u_5} [semiring R] [semiring S]
    [semiring T] (f : R →+* S) (g : R →+* T) : R →+* S × T :=
  mk (fun (x : R) => (coe_fn f x, coe_fn g x)) sorry sorry sorry sorry

@[simp] theorem prod_apply {R : Type u_1} {S : Type u_3} {T : Type u_5} [semiring R] [semiring S]
    [semiring T] (f : R →+* S) (g : R →+* T) (x : R) :
    coe_fn (ring_hom.prod f g) x = (coe_fn f x, coe_fn g x) :=
  rfl

@[simp] theorem fst_comp_prod {R : Type u_1} {S : Type u_3} {T : Type u_5} [semiring R] [semiring S]
    [semiring T] (f : R →+* S) (g : R →+* T) : comp (fst S T) (ring_hom.prod f g) = f :=
  ext fun (x : R) => rfl

@[simp] theorem snd_comp_prod {R : Type u_1} {S : Type u_3} {T : Type u_5} [semiring R] [semiring S]
    [semiring T] (f : R →+* S) (g : R →+* T) : comp (snd S T) (ring_hom.prod f g) = g :=
  ext fun (x : R) => rfl

theorem prod_unique {R : Type u_1} {S : Type u_3} {T : Type u_5} [semiring R] [semiring S]
    [semiring T] (f : R →+* S × T) : ring_hom.prod (comp (fst S T) f) (comp (snd S T) f) = f :=
  sorry

/-- `prod.map` as a `ring_hom`. -/
def prod_map {R : Type u_1} {R' : Type u_2} {S : Type u_3} {S' : Type u_4} [semiring R] [semiring S]
    [semiring R'] [semiring S'] (f : R →+* R') (g : S →+* S') : R × S →* R' × S' :=
  ↑(ring_hom.prod (comp f (fst R S)) (comp g (snd R S)))

theorem prod_map_def {R : Type u_1} {R' : Type u_2} {S : Type u_3} {S' : Type u_4} [semiring R]
    [semiring S] [semiring R'] [semiring S'] (f : R →+* R') (g : S →+* S') :
    prod_map f g = ↑(ring_hom.prod (comp f (fst R S)) (comp g (snd R S))) :=
  rfl

@[simp] theorem coe_prod_map {R : Type u_1} {R' : Type u_2} {S : Type u_3} {S' : Type u_4}
    [semiring R] [semiring S] [semiring R'] [semiring S'] (f : R →+* R') (g : S →+* S') :
    ⇑(prod_map f g) = prod.map ⇑f ⇑g :=
  rfl

theorem prod_comp_prod_map {R : Type u_1} {R' : Type u_2} {S : Type u_3} {S' : Type u_4}
    {T : Type u_5} [semiring R] [semiring S] [semiring R'] [semiring S'] [semiring T] (f : T →* R)
    (g : T →* S) (f' : R →* R') (g' : S →* S') :
    monoid_hom.comp (monoid_hom.prod_map f' g') (monoid_hom.prod f g) =
        monoid_hom.prod (monoid_hom.comp f' f) (monoid_hom.comp g' g) :=
  rfl

end ring_hom


namespace ring_equiv


/-- Swapping components as an equivalence of (semi)rings. -/
def prod_comm {R : Type u_1} {S : Type u_3} [semiring R] [semiring S] : R × S ≃+* S × R :=
  mk (add_equiv.to_fun add_equiv.prod_comm) (add_equiv.inv_fun add_equiv.prod_comm) sorry sorry
    sorry sorry

@[simp] theorem coe_prod_comm {R : Type u_1} {S : Type u_3} [semiring R] [semiring S] :
    ⇑prod_comm = prod.swap :=
  rfl

@[simp] theorem coe_prod_comm_symm {R : Type u_1} {S : Type u_3} [semiring R] [semiring S] :
    ⇑(ring_equiv.symm prod_comm) = prod.swap :=
  rfl

@[simp] theorem fst_comp_coe_prod_comm {R : Type u_1} {S : Type u_3} [semiring R] [semiring S] :
    ring_hom.comp (ring_hom.fst S R) ↑prod_comm = ring_hom.snd R S :=
  ring_hom.ext fun (_x : R × S) => rfl

@[simp] theorem snd_comp_coe_prod_comm {R : Type u_1} {S : Type u_3} [semiring R] [semiring S] :
    ring_hom.comp (ring_hom.snd S R) ↑prod_comm = ring_hom.fst R S :=
  ring_hom.ext fun (_x : R × S) => rfl

end Mathlib