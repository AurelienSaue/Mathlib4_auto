/-
Copyright (c) 2020 Simon Hudon All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.control.functor.multivariate
import Mathlib.data.qpf.multivariate.basic
import Mathlib.PostPort

universes u u_1 u_2 

namespace Mathlib

/-!
Projection functors are QPFs. The `n`-ary projection functors on `i` is an `n`-ary
functor `F` such that `F (α₀..αᵢ₋₁, αᵢ, αᵢ₊₁..αₙ₋₁) = αᵢ`
-/

namespace mvqpf


/-- The projection `i` functor -/
def prj {n : ℕ} (i : fin2 n) (v : typevec n) :=
  v i

protected instance prj.inhabited {n : ℕ} (i : fin2 n) {v : typevec n} [Inhabited (v i)] : Inhabited (prj i v) :=
  { default := Inhabited.default }

/-- `map` on functor `prj i` -/
def prj.map {n : ℕ} (i : fin2 n) {α : typevec n} {β : typevec n} (f : typevec.arrow α β) : prj i α → prj i β :=
  f i

protected instance prj.mvfunctor {n : ℕ} (i : fin2 n) : mvfunctor (prj i) :=
  mvfunctor.mk (prj.map i)

/-- Polynomial representation of the projection functor -/
def prj.P {n : ℕ} (i : fin2 n) : mvpfunctor n :=
  mvpfunctor.mk PUnit fun (_x : PUnit) (j : fin2 n) => ulift (plift (i = j))

/-- Abstraction function of the `qpf` instance -/
def prj.abs {n : ℕ} (i : fin2 n) {α : typevec n} : mvpfunctor.obj (prj.P i) α → prj i α :=
  sorry

/-- Representation function of the `qpf` instance -/
def prj.repr {n : ℕ} (i : fin2 n) {α : typevec n} : prj i α → mvpfunctor.obj (prj.P i) α :=
  fun (x : α i) => sigma.mk PUnit.unit fun (j : fin2 n) (_x : mvpfunctor.B (prj.P i) PUnit.unit j) => sorry

protected instance prj.mvqpf {n : ℕ} (i : fin2 n) : mvqpf (prj i) :=
  mk (prj.P i) (prj.abs i) (prj.repr i) sorry sorry

