/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad, Simon Hudon
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.pfunctor.multivariate.basic
import Mathlib.PostPort

universes u u_1 l 

namespace Mathlib

/-!
# Multivariate quotients of polynomial functors.

Basic definition of multivariate QPF. QPFs form a compositional framework
for defining inductive and coinductive types, their quotients and nesting.

The idea is based on building ever larger functors. For instance, we can define
a list using a shape functor:

```lean
inductive list_shape (a b : Type)
| nil : list_shape
| cons : a -> b -> list_shape
```

This shape can itself be decomposed as a sum of product which are themselves
QPFs. It follows that the shape is a QPF and we can take its fixed point
and create the list itself:

```lean
def list (a : Type) := fix list_shape a -- not the actual notation
```

We can continue and define the quotient on permutation of lists and create
the multiset type:

```lean
def multiset (a : Type) := qpf.quot list.perm list a -- not the actual notion
```

And `multiset` is also a QPF. We can then create a novel data type (for Lean):

```lean
inductive tree (a : Type)
| node : a -> multiset tree -> tree
```

An unordered tree. This is currently not supported by Lean because it nests
an inductive type inside of a quotient. We can go further and define
unordered, possibly infinite trees:

```lean
coinductive tree' (a : Type)
| node : a -> multiset tree' -> tree'
```

by using the `cofix` construct. Those options can all be mixed and
matched because they preserve the properties of QPF. The latter example,
`tree'`, combines fixed point, co-fixed point and quotients.

## Related modules

 * constructions
   * fix
   * cofix
   * quot
   * comp
   * sigma / pi
   * prj
   * const

each proves that some operations on functors preserves the QPF structure

##reference

 * [Jeremy Avigad, Mario M. Carneiro and Simon Hudon, *Data Types as Quotients of Polynomial Functors*][avigad-carneiro-hudon2019]
-/

/--
Multivariate quotients of polynomial functors.
-/
class mvqpf {n : ???} (F : typevec n ??? Type u_1) [mvfunctor F] 
where
  P : mvpfunctor n
  abs : {?? : typevec n} ??? mvpfunctor.obj P ?? ??? F ??
  repr : {?? : typevec n} ??? F ?? ??? mvpfunctor.obj P ??
  abs_repr : ??? {?? : typevec n} (x : F ??), abs (repr x) = x
  abs_map : ??? {?? ?? : typevec n} (f : typevec.arrow ?? ??) (p : mvpfunctor.obj P ??), abs (mvfunctor.map f p) = mvfunctor.map f (abs p)

namespace mvqpf


/-!
### Show that every mvqpf is a lawful mvfunctor.
-/

protected theorem id_map {n : ???} {F : typevec n ??? Type u_1} [mvfunctor F] [q : mvqpf F] {?? : typevec n} (x : F ??) : mvfunctor.map typevec.id x = x := sorry

@[simp] theorem comp_map {n : ???} {F : typevec n ??? Type u_1} [mvfunctor F] [q : mvqpf F] {?? : typevec n} {?? : typevec n} {?? : typevec n} (f : typevec.arrow ?? ??) (g : typevec.arrow ?? ??) (x : F ??) : mvfunctor.map (typevec.comp g f) x = mvfunctor.map g (mvfunctor.map f x) := sorry

protected instance is_lawful_mvfunctor {n : ???} {F : typevec n ??? Type u_1} [mvfunctor F] [q : mvqpf F] : is_lawful_mvfunctor F :=
  is_lawful_mvfunctor.mk mvqpf.id_map comp_map

/- Lifting predicates and relations -/

theorem liftp_iff {n : ???} {F : typevec n ??? Type u_1} [mvfunctor F] [q : mvqpf F] {?? : typevec n} (p : {i : fin2 n} ??? ?? i ??? Prop) (x : F ??) : mvfunctor.liftp p x ???
  ??? (a : mvpfunctor.A (P F)),
    ??? (f : typevec.arrow (mvpfunctor.B (P F) a) ??),
      x = abs (sigma.mk a f) ??? ??? (i : fin2 n) (j : mvpfunctor.B (P F) a i), p (f i j) := sorry

theorem liftr_iff {n : ???} {F : typevec n ??? Type u_1} [mvfunctor F] [q : mvqpf F] {?? : typevec n} (r : {i : fin2 n} ??? ?? i ??? ?? i ??? Prop) (x : F ??) (y : F ??) : mvfunctor.liftr r x y ???
  ??? (a : mvpfunctor.A (P F)),
    ??? (f??? : typevec.arrow (mvpfunctor.B (P F) a) ??),
      ??? (f??? : typevec.arrow (mvpfunctor.B (P F) a) ??),
        x = abs (sigma.mk a f???) ???
          y = abs (sigma.mk a f???) ??? ??? (i : fin2 n) (j : mvpfunctor.B (P F) a i), r (f??? i j) (f??? i j) := sorry

theorem mem_supp {n : ???} {F : typevec n ??? Type u_1} [mvfunctor F] [q : mvqpf F] {?? : typevec n} (x : F ??) (i : fin2 n) (u : ?? i) : u ??? mvfunctor.supp x i ???
  ??? (a : mvpfunctor.A (P F)) (f : typevec.arrow (mvpfunctor.B (P F) a) ??), abs (sigma.mk a f) = x ??? u ??? f i '' set.univ := sorry

theorem supp_eq {n : ???} {F : typevec n ??? Type u_1} [mvfunctor F] [q : mvqpf F] {?? : typevec n} {i : fin2 n} (x : F ??) : mvfunctor.supp x i =
  set_of
    fun (u : ?? i) =>
      ??? (a : mvpfunctor.A (P F)) (f : typevec.arrow (mvpfunctor.B (P F) a) ??),
        abs (sigma.mk a f) = x ??? u ??? f i '' set.univ :=
  set.ext fun (x_1 : ?? i) => mem_supp x i x_1

theorem has_good_supp_iff {n : ???} {F : typevec n ??? Type u_1} [mvfunctor F] [q : mvqpf F] {?? : typevec n} (x : F ??) : (??? (p : (i : fin2 n) ??? ?? i ??? Prop), mvfunctor.liftp p x ??? ??? (i : fin2 n) (u : ?? i), u ??? mvfunctor.supp x i ??? p i u) ???
  ??? (a : mvpfunctor.A (P F)),
    ??? (f : typevec.arrow (mvpfunctor.B (P F) a) ??),
      abs (sigma.mk a f) = x ???
        ??? (i : fin2 n) (a' : mvpfunctor.A (P F)) (f' : typevec.arrow (mvpfunctor.B (P F) a') ??),
          abs (sigma.mk a' f') = x ??? f i '' set.univ ??? f' i '' set.univ := sorry

/-- A qpf is said to be uniform if every polynomial functor
representing a single value all have the same range. -/
def is_uniform {n : ???} {F : typevec n ??? Type u_1} [mvfunctor F] (q : mvqpf F) :=
  ??? {?? : typevec n} (a a' : mvpfunctor.A (P F)) (f : typevec.arrow (mvpfunctor.B (P F) a) ??)
    (f' : typevec.arrow (mvpfunctor.B (P F) a') ??),
    abs (sigma.mk a f) = abs (sigma.mk a' f') ??? ??? (i : fin2 n), f i '' set.univ = f' i '' set.univ

/-- does `abs` preserve `liftp`? -/
def liftp_preservation {n : ???} {F : typevec n ??? Type u_1} [mvfunctor F] (q : mvqpf F) :=
  ??? {?? : typevec n} (p : {i : fin2 n} ??? ?? i ??? Prop) (x : mvpfunctor.obj (P F) ??),
    mvfunctor.liftp p (abs x) ??? mvfunctor.liftp p x

/-- does `abs` preserve `supp`? -/
def supp_preservation {n : ???} {F : typevec n ??? Type u_1} [mvfunctor F] (q : mvqpf F) :=
  ??? {?? : typevec n} (x : mvpfunctor.obj (P F) ??), mvfunctor.supp (abs x) = mvfunctor.supp x

theorem supp_eq_of_is_uniform {n : ???} {F : typevec n ??? Type u_1} [mvfunctor F] [q : mvqpf F] (h : is_uniform q) {?? : typevec n} (a : mvpfunctor.A (P F)) (f : typevec.arrow (mvpfunctor.B (P F) a) ??) (i : fin2 n) : mvfunctor.supp (abs (sigma.mk a f)) i = f i '' set.univ := sorry

theorem liftp_iff_of_is_uniform {n : ???} {F : typevec n ??? Type u_1} [mvfunctor F] [q : mvqpf F] (h : is_uniform q) {?? : typevec n} (x : F ??) (p : (i : fin2 n) ??? ?? i ??? Prop) : mvfunctor.liftp p x ??? ??? (i : fin2 n) (u : ?? i), u ??? mvfunctor.supp x i ??? p i u := sorry

theorem supp_map {n : ???} {F : typevec n ??? Type u_1} [mvfunctor F] [q : mvqpf F] (h : is_uniform q) {?? : typevec n} {?? : typevec n} (g : typevec.arrow ?? ??) (x : F ??) (i : fin2 n) : mvfunctor.supp (mvfunctor.map g x) i = g i '' mvfunctor.supp x i := sorry

theorem supp_preservation_iff_uniform {n : ???} {F : typevec n ??? Type u_1} [mvfunctor F] [q : mvqpf F] : supp_preservation q ??? is_uniform q := sorry

theorem supp_preservation_iff_liftp_preservation {n : ???} {F : typevec n ??? Type u_1} [mvfunctor F] [q : mvqpf F] : supp_preservation q ??? liftp_preservation q := sorry

theorem liftp_preservation_iff_uniform {n : ???} {F : typevec n ??? Type u_1} [mvfunctor F] [q : mvqpf F] : liftp_preservation q ??? is_uniform q := sorry

