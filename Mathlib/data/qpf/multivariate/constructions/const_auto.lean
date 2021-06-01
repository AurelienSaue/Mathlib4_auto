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
# Constant functors are QPFs

Constant functors map every type vectors to the same target type. This
is a useful device for constructing data types from more basic types
that are not actually functorial. For instance `const n nat` makes
`nat` into a functor that can be used in a functor-based data type
specification.
-/

namespace mvqpf


/-- Constant multivariate functor -/
def const (n : ℕ) (A : Type u_1) (v : typevec n) := A

protected instance const.inhabited (n : ℕ) {A : Type u_1} {α : typevec n} [Inhabited A] :
    Inhabited (const n A α) :=
  { default := Inhabited.default }

namespace const


/-- Constructor for constant functor -/
protected def mk {n : ℕ} {A : Type u} {α : typevec n} (x : A) : const n A α := x

/-- Destructor for constant functor -/
protected def get {n : ℕ} {A : Type u} {α : typevec n} (x : const n A α) : A := x

@[simp] protected theorem mk_get {n : ℕ} {A : Type u} {α : typevec n} (x : const n A α) :
    const.mk (const.get x) = x :=
  rfl

@[simp] protected theorem get_mk {n : ℕ} {A : Type u} {α : typevec n} (x : A) :
    const.get (const.mk x) = x :=
  rfl

/-- `map` for constant functor -/
protected def map {n : ℕ} {A : Type u} {α : typevec n} {β : typevec n} :
    const n A α → const n A β :=
  fun (x : const n A α) => x

protected instance mvfunctor {n : ℕ} {A : Type u} : mvfunctor (const n A) :=
  mvfunctor.mk fun (α β : typevec n) (f : typevec.arrow α β) => const.map

theorem map_mk {n : ℕ} {A : Type u} {α : typevec n} {β : typevec n} (f : typevec.arrow α β)
    (x : A) : mvfunctor.map f (const.mk x) = const.mk x :=
  rfl

theorem get_map {n : ℕ} {A : Type u} {α : typevec n} {β : typevec n} (f : typevec.arrow α β)
    (x : const n A α) : const.get (mvfunctor.map f x) = const.get x :=
  rfl

protected instance mvqpf {n : ℕ} {A : Type u} : mvqpf (const n A) :=
  mk (mvpfunctor.const n A)
    (fun (α : typevec n) (x : mvpfunctor.obj (mvpfunctor.const n A) α) => mvpfunctor.const.get x)
    (fun (α : typevec n) (x : const n A α) => mvpfunctor.const.mk n x) sorry sorry

end Mathlib