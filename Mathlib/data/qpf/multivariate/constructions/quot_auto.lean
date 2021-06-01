/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad, Simon Hudon
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.qpf.multivariate.basic
import Mathlib.PostPort

universes u 

namespace Mathlib

/-!
# The quotient of QPF is itself a QPF

The quotients are here defined using a surjective function and
its right inverse. They are very similar to the `abs` and `repr`
functions found in the definition of `mvqpf`
-/

namespace mvqpf


/-- If `F` is a QPF then `G` is a QPF as well. Can be used to
construct `mvqpf` instances by transporting them across
surjective functions -/
def quotient_qpf {n : ℕ} {F : typevec n → Type u} [mvfunctor F] [q : mvqpf F]
    {G : typevec n → Type u} [mvfunctor G] {FG_abs : {α : typevec n} → F α → G α}
    {FG_repr : {α : typevec n} → G α → F α}
    (FG_abs_repr : ∀ {α : typevec n} (x : G α), FG_abs (FG_repr x) = x)
    (FG_abs_map :
      ∀ {α β : typevec n} (f : typevec.arrow α β) (x : F α),
        FG_abs (mvfunctor.map f x) = mvfunctor.map f (FG_abs x)) :
    mvqpf G :=
  mk (P F) (fun (α : typevec n) (p : mvpfunctor.obj (P F) α) => FG_abs (abs p))
    (fun (α : typevec n) (x : G α) => repr (FG_repr x)) sorry sorry

/-- Functorial quotient type -/
def quot1 {n : ℕ} {F : typevec n → Type u} (R : {α : typevec n} → F α → F α → Prop)
    (α : typevec n) :=
  Quot R

protected instance quot1.inhabited {n : ℕ} {F : typevec n → Type u}
    (R : {α : typevec n} → F α → F α → Prop) {α : typevec n} [Inhabited (F α)] :
    Inhabited (quot1 R α) :=
  { default := Quot.mk R Inhabited.default }

/-- `map` of the `quot1` functor -/
def quot1.map {n : ℕ} {F : typevec n → Type u} (R : {α : typevec n} → F α → F α → Prop)
    [mvfunctor F]
    (Hfunc :
      ∀ {α β : typevec n} (a b : F α) (f : typevec.arrow α β),
        R a b → R (mvfunctor.map f a) (mvfunctor.map f b))
    {α : typevec n} {β : typevec n} (f : typevec.arrow α β) : quot1 R α → quot1 R β :=
  Quot.lift (fun (x : F α) => Quot.mk R (mvfunctor.map f x)) sorry

/-- `mvfunctor` instance for `quot1` with well-behaved `R` -/
def quot1.mvfunctor {n : ℕ} {F : typevec n → Type u} (R : {α : typevec n} → F α → F α → Prop)
    [mvfunctor F]
    (Hfunc :
      ∀ {α β : typevec n} (a b : F α) (f : typevec.arrow α β),
        R a b → R (mvfunctor.map f a) (mvfunctor.map f b)) :
    mvfunctor (quot1 R) :=
  mvfunctor.mk (quot1.map R Hfunc)

/-- `quot1` is a qpf -/
def rel_quot {n : ℕ} {F : typevec n → Type u} (R : {α : typevec n} → F α → F α → Prop) [mvfunctor F]
    [q : mvqpf F]
    (Hfunc :
      ∀ {α β : typevec n} (a b : F α) (f : typevec.arrow α β),
        R a b → R (mvfunctor.map f a) (mvfunctor.map f b)) :
    mvqpf (quot1 R) :=
  quotient_qpf sorry sorry

end Mathlib