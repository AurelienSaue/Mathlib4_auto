/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.pfunctor.multivariate.basic
import Mathlib.data.qpf.multivariate.basic
import Mathlib.PostPort

universes u 

namespace Mathlib

/-!
# Dependent product and sum of QPFs are QPFs
-/

namespace mvqpf


/-- Dependent sum of of an `n`-ary functor. The sum can range over
data types like `ℕ` or over `Type.{u-1}` -/
def sigma {n : ℕ} {A : Type u} (F : A → typevec n → Type u) (v : typevec n) :=
  sigma fun (α : A) => F α v

/-- Dependent product of of an `n`-ary functor. The sum can range over
data types like `ℕ` or over `Type.{u-1}` -/
def pi {n : ℕ} {A : Type u} (F : A → typevec n → Type u) (v : typevec n) := (α : A) → F α v

protected instance sigma.inhabited {n : ℕ} {A : Type u} (F : A → typevec n → Type u) {α : typevec n}
    [Inhabited A] [Inhabited (F Inhabited.default α)] : Inhabited (sigma F α) :=
  { default := sigma.mk Inhabited.default Inhabited.default }

protected instance pi.inhabited {n : ℕ} {A : Type u} (F : A → typevec n → Type u) {α : typevec n}
    [(a : A) → Inhabited (F a α)] : Inhabited (pi F α) :=
  { default := fun (a : A) => Inhabited.default }

namespace sigma


protected instance mvfunctor {n : ℕ} {A : Type u} (F : A → typevec n → Type u)
    [(α : A) → mvfunctor (F α)] : mvfunctor (sigma F) :=
  mvfunctor.mk fun (α β : typevec n) (f : typevec.arrow α β) (_x : sigma F α) => sorry

/-- polynomial functor representation of a dependent sum -/
protected def P {n : ℕ} {A : Type u} (F : A → typevec n → Type u) [(α : A) → mvfunctor (F α)]
    [(α : A) → mvqpf (F α)] : mvpfunctor n :=
  mvpfunctor.mk (sigma fun (a : A) => mvpfunctor.A (P (F a)))
    fun (x : sigma fun (a : A) => mvpfunctor.A (P (F a))) =>
      mvpfunctor.B (P (F (sigma.fst x))) (sigma.snd x)

/-- abstraction function for dependent sums -/
protected def abs {n : ℕ} {A : Type u} (F : A → typevec n → Type u) [(α : A) → mvfunctor (F α)]
    [(α : A) → mvqpf (F α)] {α : typevec n} : mvpfunctor.obj (sigma.P F) α → sigma F α :=
  sorry

/-- representation function for dependent sums -/
protected def repr {n : ℕ} {A : Type u} (F : A → typevec n → Type u) [(α : A) → mvfunctor (F α)]
    [(α : A) → mvqpf (F α)] {α : typevec n} : sigma F α → mvpfunctor.obj (sigma.P F) α :=
  sorry

protected instance mvqpf {n : ℕ} {A : Type u} (F : A → typevec n → Type u)
    [(α : A) → mvfunctor (F α)] [(α : A) → mvqpf (F α)] : mvqpf (sigma F) :=
  mk (sigma.P F) (sigma.abs F) (sigma.repr F) sorry sorry

end sigma


namespace pi


protected instance mvfunctor {n : ℕ} {A : Type u} (F : A → typevec n → Type u)
    [(α : A) → mvfunctor (F α)] : mvfunctor (pi F) :=
  mvfunctor.mk
    fun (α β : typevec n) (f : typevec.arrow α β) (x : pi F α) (a : A) => mvfunctor.map f (x a)

/-- polynomial functor representation of a dependent product -/
protected def P {n : ℕ} {A : Type u} (F : A → typevec n → Type u) [(α : A) → mvfunctor (F α)]
    [(α : A) → mvqpf (F α)] : mvpfunctor n :=
  mvpfunctor.mk ((a : A) → mvpfunctor.A (P (F a)))
    fun (x : (a : A) → mvpfunctor.A (P (F a))) (i : fin2 n) =>
      sigma fun (a : A) => mvpfunctor.B (P (F a)) (x a) i

/-- abstraction function for dependent products -/
protected def abs {n : ℕ} {A : Type u} (F : A → typevec n → Type u) [(α : A) → mvfunctor (F α)]
    [(α : A) → mvqpf (F α)] {α : typevec n} : mvpfunctor.obj (pi.P F) α → pi F α :=
  sorry

/-- representation function for dependent products -/
protected def repr {n : ℕ} {A : Type u} (F : A → typevec n → Type u) [(α : A) → mvfunctor (F α)]
    [(α : A) → mvqpf (F α)] {α : typevec n} : pi F α → mvpfunctor.obj (pi.P F) α :=
  sorry

protected instance mvqpf {n : ℕ} {A : Type u} (F : A → typevec n → Type u)
    [(α : A) → mvfunctor (F α)] [(α : A) → mvqpf (F α)] : mvqpf (pi F) :=
  mk (pi.P F) (pi.abs F) (pi.repr F) sorry sorry

end Mathlib