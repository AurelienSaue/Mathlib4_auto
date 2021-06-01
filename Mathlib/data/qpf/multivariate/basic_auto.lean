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
class mvqpf {n : ℕ} (F : typevec n → Type u_1) [mvfunctor F] where
  P : mvpfunctor n
  abs : {α : typevec n} → mvpfunctor.obj P α → F α
  repr : {α : typevec n} → F α → mvpfunctor.obj P α
  abs_repr : ∀ {α : typevec n} (x : F α), abs (repr x) = x
  abs_map :
    ∀ {α β : typevec n} (f : typevec.arrow α β) (p : mvpfunctor.obj P α),
      abs (mvfunctor.map f p) = mvfunctor.map f (abs p)

namespace mvqpf


/-!
### Show that every mvqpf is a lawful mvfunctor.
-/

protected theorem id_map {n : ℕ} {F : typevec n → Type u_1} [mvfunctor F] [q : mvqpf F]
    {α : typevec n} (x : F α) : mvfunctor.map typevec.id x = x :=
  sorry

@[simp] theorem comp_map {n : ℕ} {F : typevec n → Type u_1} [mvfunctor F] [q : mvqpf F]
    {α : typevec n} {β : typevec n} {γ : typevec n} (f : typevec.arrow α β) (g : typevec.arrow β γ)
    (x : F α) : mvfunctor.map (typevec.comp g f) x = mvfunctor.map g (mvfunctor.map f x) :=
  sorry

protected instance is_lawful_mvfunctor {n : ℕ} {F : typevec n → Type u_1} [mvfunctor F]
    [q : mvqpf F] : is_lawful_mvfunctor F :=
  is_lawful_mvfunctor.mk mvqpf.id_map comp_map

/- Lifting predicates and relations -/

theorem liftp_iff {n : ℕ} {F : typevec n → Type u_1} [mvfunctor F] [q : mvqpf F] {α : typevec n}
    (p : {i : fin2 n} → α i → Prop) (x : F α) :
    mvfunctor.liftp p x ↔
        ∃ (a : mvpfunctor.A (P F)),
          ∃ (f : typevec.arrow (mvpfunctor.B (P F) a) α),
            x = abs (sigma.mk a f) ∧ ∀ (i : fin2 n) (j : mvpfunctor.B (P F) a i), p (f i j) :=
  sorry

theorem liftr_iff {n : ℕ} {F : typevec n → Type u_1} [mvfunctor F] [q : mvqpf F] {α : typevec n}
    (r : {i : fin2 n} → α i → α i → Prop) (x : F α) (y : F α) :
    mvfunctor.liftr r x y ↔
        ∃ (a : mvpfunctor.A (P F)),
          ∃ (f₀ : typevec.arrow (mvpfunctor.B (P F) a) α),
            ∃ (f₁ : typevec.arrow (mvpfunctor.B (P F) a) α),
              x = abs (sigma.mk a f₀) ∧
                y = abs (sigma.mk a f₁) ∧
                  ∀ (i : fin2 n) (j : mvpfunctor.B (P F) a i), r (f₀ i j) (f₁ i j) :=
  sorry

theorem mem_supp {n : ℕ} {F : typevec n → Type u_1} [mvfunctor F] [q : mvqpf F] {α : typevec n}
    (x : F α) (i : fin2 n) (u : α i) :
    u ∈ mvfunctor.supp x i ↔
        ∀ (a : mvpfunctor.A (P F)) (f : typevec.arrow (mvpfunctor.B (P F) a) α),
          abs (sigma.mk a f) = x → u ∈ f i '' set.univ :=
  sorry

theorem supp_eq {n : ℕ} {F : typevec n → Type u_1} [mvfunctor F] [q : mvqpf F] {α : typevec n}
    {i : fin2 n} (x : F α) :
    mvfunctor.supp x i =
        set_of
          fun (u : α i) =>
            ∀ (a : mvpfunctor.A (P F)) (f : typevec.arrow (mvpfunctor.B (P F) a) α),
              abs (sigma.mk a f) = x → u ∈ f i '' set.univ :=
  set.ext fun (x_1 : α i) => mem_supp x i x_1

theorem has_good_supp_iff {n : ℕ} {F : typevec n → Type u_1} [mvfunctor F] [q : mvqpf F]
    {α : typevec n} (x : F α) :
    (∀ (p : (i : fin2 n) → α i → Prop),
          mvfunctor.liftp p x ↔ ∀ (i : fin2 n) (u : α i), u ∈ mvfunctor.supp x i → p i u) ↔
        ∃ (a : mvpfunctor.A (P F)),
          ∃ (f : typevec.arrow (mvpfunctor.B (P F) a) α),
            abs (sigma.mk a f) = x ∧
              ∀ (i : fin2 n) (a' : mvpfunctor.A (P F))
                (f' : typevec.arrow (mvpfunctor.B (P F) a') α),
                abs (sigma.mk a' f') = x → f i '' set.univ ⊆ f' i '' set.univ :=
  sorry

/-- A qpf is said to be uniform if every polynomial functor
representing a single value all have the same range. -/
def is_uniform {n : ℕ} {F : typevec n → Type u_1} [mvfunctor F] (q : mvqpf F) :=
  ∀ {α : typevec n} (a a' : mvpfunctor.A (P F)) (f : typevec.arrow (mvpfunctor.B (P F) a) α)
    (f' : typevec.arrow (mvpfunctor.B (P F) a') α),
    abs (sigma.mk a f) = abs (sigma.mk a' f') → ∀ (i : fin2 n), f i '' set.univ = f' i '' set.univ

/-- does `abs` preserve `liftp`? -/
def liftp_preservation {n : ℕ} {F : typevec n → Type u_1} [mvfunctor F] (q : mvqpf F) :=
  ∀ {α : typevec n} (p : {i : fin2 n} → α i → Prop) (x : mvpfunctor.obj (P F) α),
    mvfunctor.liftp p (abs x) ↔ mvfunctor.liftp p x

/-- does `abs` preserve `supp`? -/
def supp_preservation {n : ℕ} {F : typevec n → Type u_1} [mvfunctor F] (q : mvqpf F) :=
  ∀ {α : typevec n} (x : mvpfunctor.obj (P F) α), mvfunctor.supp (abs x) = mvfunctor.supp x

theorem supp_eq_of_is_uniform {n : ℕ} {F : typevec n → Type u_1} [mvfunctor F] [q : mvqpf F]
    (h : is_uniform q) {α : typevec n} (a : mvpfunctor.A (P F))
    (f : typevec.arrow (mvpfunctor.B (P F) a) α) (i : fin2 n) :
    mvfunctor.supp (abs (sigma.mk a f)) i = f i '' set.univ :=
  sorry

theorem liftp_iff_of_is_uniform {n : ℕ} {F : typevec n → Type u_1} [mvfunctor F] [q : mvqpf F]
    (h : is_uniform q) {α : typevec n} (x : F α) (p : (i : fin2 n) → α i → Prop) :
    mvfunctor.liftp p x ↔ ∀ (i : fin2 n) (u : α i), u ∈ mvfunctor.supp x i → p i u :=
  sorry

theorem supp_map {n : ℕ} {F : typevec n → Type u_1} [mvfunctor F] [q : mvqpf F] (h : is_uniform q)
    {α : typevec n} {β : typevec n} (g : typevec.arrow α β) (x : F α) (i : fin2 n) :
    mvfunctor.supp (mvfunctor.map g x) i = g i '' mvfunctor.supp x i :=
  sorry

theorem supp_preservation_iff_uniform {n : ℕ} {F : typevec n → Type u_1} [mvfunctor F]
    [q : mvqpf F] : supp_preservation q ↔ is_uniform q :=
  sorry

theorem supp_preservation_iff_liftp_preservation {n : ℕ} {F : typevec n → Type u_1} [mvfunctor F]
    [q : mvqpf F] : supp_preservation q ↔ liftp_preservation q :=
  sorry

theorem liftp_preservation_iff_uniform {n : ℕ} {F : typevec n → Type u_1} [mvfunctor F]
    [q : mvqpf F] : liftp_preservation q ↔ is_uniform q :=
  sorry

end Mathlib