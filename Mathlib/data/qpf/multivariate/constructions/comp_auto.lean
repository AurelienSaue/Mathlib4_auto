/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad, Simon Hudon
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.pfunctor.multivariate.basic
import Mathlib.data.qpf.multivariate.basic
import Mathlib.PostPort

universes u u_1 

namespace Mathlib

/-!
# The composition of QPFs is itself a QPF

We define composition between one `n`-ary functor and `n` `m`-ary functors
and show that it preserves the QPF structure
-/

namespace mvqpf


/-- Composition of an `n`-ary functor with `n` `m`-ary
functors gives us one `m`-ary functor -/
def comp {n : ℕ} {m : ℕ} (F : typevec n → Type u_1) (G : fin2 n → typevec m → Type u)
    (v : typevec m) :=
  F fun (i : fin2 n) => G i v

namespace comp


protected instance inhabited {n : ℕ} {m : ℕ} {F : typevec n → Type u_1}
    {G : fin2 n → typevec m → Type u} {α : typevec m}
    [I : Inhabited (F fun (i : fin2 n) => G i α)] : Inhabited (comp F G α) :=
  I

/-- Constructor for functor composition -/
protected def mk {n : ℕ} {m : ℕ} {F : typevec n → Type u_1} {G : fin2 n → typevec m → Type u}
    {α : typevec m} (x : F fun (i : fin2 n) => G i α) : comp F G α :=
  x

/-- Destructor for functor composition -/
protected def get {n : ℕ} {m : ℕ} {F : typevec n → Type u_1} {G : fin2 n → typevec m → Type u}
    {α : typevec m} (x : comp F G α) : F fun (i : fin2 n) => G i α :=
  x

@[simp] protected theorem mk_get {n : ℕ} {m : ℕ} {F : typevec n → Type u_1}
    {G : fin2 n → typevec m → Type u} {α : typevec m} (x : comp F G α) : comp.mk (comp.get x) = x :=
  rfl

@[simp] protected theorem get_mk {n : ℕ} {m : ℕ} {F : typevec n → Type u_1}
    {G : fin2 n → typevec m → Type u} {α : typevec m} (x : F fun (i : fin2 n) => G i α) :
    comp.get (comp.mk x) = x :=
  rfl

/-- map operation defined on a vector of functors -/
protected def map' {n : ℕ} {m : ℕ} {G : fin2 n → typevec m → Type u}
    [fG : (i : fin2 n) → mvfunctor (G i)] {α : typevec m} {β : typevec m} (f : typevec.arrow α β) :
    typevec.arrow (fun (i : fin2 n) => G i α) fun (i : fin2 n) => G i β :=
  fun (i : fin2 n) => mvfunctor.map f

/-- The composition of functors is itself functorial -/
protected def map {n : ℕ} {m : ℕ} {F : typevec n → Type u_1} [fF : mvfunctor F]
    {G : fin2 n → typevec m → Type u} [fG : (i : fin2 n) → mvfunctor (G i)] {α : typevec m}
    {β : typevec m} (f : typevec.arrow α β) : comp F G α → comp F G β :=
  mvfunctor.map fun (i : fin2 n) => mvfunctor.map f

protected instance mvfunctor {n : ℕ} {m : ℕ} {F : typevec n → Type u_1} [fF : mvfunctor F]
    {G : fin2 n → typevec m → Type u} [fG : (i : fin2 n) → mvfunctor (G i)] :
    mvfunctor (comp F G) :=
  mvfunctor.mk fun (α β : typevec m) => comp.map

theorem map_mk {n : ℕ} {m : ℕ} {F : typevec n → Type u_1} [fF : mvfunctor F]
    {G : fin2 n → typevec m → Type u} [fG : (i : fin2 n) → mvfunctor (G i)] {α : typevec m}
    {β : typevec m} (f : typevec.arrow α β) (x : F fun (i : fin2 n) => G i α) :
    mvfunctor.map f (comp.mk x) =
        comp.mk (mvfunctor.map (fun (i : fin2 n) (x : G i α) => mvfunctor.map f x) x) :=
  rfl

theorem get_map {n : ℕ} {m : ℕ} {F : typevec n → Type u_1} [fF : mvfunctor F]
    {G : fin2 n → typevec m → Type u} [fG : (i : fin2 n) → mvfunctor (G i)] {α : typevec m}
    {β : typevec m} (f : typevec.arrow α β) (x : comp F G α) :
    comp.get (mvfunctor.map f x) =
        mvfunctor.map (fun (i : fin2 n) (x : G i α) => mvfunctor.map f x) (comp.get x) :=
  rfl

protected instance mvqpf {n : ℕ} {m : ℕ} {F : typevec n → Type u_1} [fF : mvfunctor F] [q : mvqpf F]
    {G : fin2 n → typevec m → Type u} [fG : (i : fin2 n) → mvfunctor (G i)]
    [q' : (i : fin2 n) → mvqpf (G i)] : mvqpf (comp F G) :=
  mk (mvpfunctor.comp (P F) fun (i : fin2 n) => P (G i))
    (fun (α : typevec m) =>
      comp.mk ∘ (mvfunctor.map fun (i : fin2 n) => abs) ∘ abs ∘ mvpfunctor.comp.get)
    (fun (α : typevec m) =>
      mvpfunctor.comp.mk ∘ repr ∘ (mvfunctor.map fun (i : fin2 n) => repr) ∘ comp.get)
    sorry sorry

end Mathlib