/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad, Simon Hudon
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.control.functor.multivariate
import Mathlib.data.pfunctor.univariate.default
import Mathlib.data.sigma.default
import PostPort

universes u l u_1 

namespace Mathlib

/-!
# Multivariate polynomial functors.

Multivariate polynomial functors are used for defining M-types and W-types.
They map a type vector `α` to the type `Σ a : A, B a ⟹ α`, with `A : Type` and
`B : A → typevec n`. They interact well with Lean's inductive definitions because
they guarantee that occurrences of `α` are positive.
-/

/--
multivariate polynomial functors
-/
structure mvpfunctor (n : ℕ) 
where
  A : Type u
  B : A → typevec n

namespace mvpfunctor


/-- Applying `P` to an object of `Type` -/
def obj {n : ℕ} (P : mvpfunctor n) (α : typevec n)  :=
  sigma fun (a : A P) => typevec.arrow (B P a) α

/-- Applying `P` to a morphism of `Type` -/
def map {n : ℕ} (P : mvpfunctor n) {α : typevec n} {β : typevec n} (f : typevec.arrow α β) : obj P α → obj P β :=
  fun (_x : obj P α) => sorry

protected instance inhabited {n : ℕ} : Inhabited (mvpfunctor n) :=
  { default := mk Inhabited.default fun (_x : Inhabited.default) => Inhabited.default }

protected instance obj.inhabited {n : ℕ} (P : mvpfunctor n) {α : typevec n} [Inhabited (A P)] [(i : fin2 n) → Inhabited (α i)] : Inhabited (obj P α) :=
  { default := sigma.mk Inhabited.default fun (_x : fin2 n) (_x_1 : B P Inhabited.default _x) => Inhabited.default }

protected instance obj.mvfunctor {n : ℕ} (P : mvpfunctor n) : mvfunctor (obj P) :=
  mvfunctor.mk (map P)

theorem map_eq {n : ℕ} (P : mvpfunctor n) {α : typevec n} {β : typevec n} (g : typevec.arrow α β) (a : A P) (f : typevec.arrow (B P a) α) : mvfunctor.map g (sigma.mk a f) = sigma.mk a (typevec.comp g f) :=
  rfl

theorem id_map {n : ℕ} (P : mvpfunctor n) {α : typevec n} (x : obj P α) : mvfunctor.map typevec.id x = x :=
  sigma.cases_on x
    fun (x_fst : A P) (x_snd : typevec.arrow (B P x_fst) α) =>
      idRhs (mvfunctor.map typevec.id (sigma.mk x_fst x_snd) = mvfunctor.map typevec.id (sigma.mk x_fst x_snd)) rfl

theorem comp_map {n : ℕ} (P : mvpfunctor n) {α : typevec n} {β : typevec n} {γ : typevec n} (f : typevec.arrow α β) (g : typevec.arrow β γ) (x : obj P α) : mvfunctor.map (typevec.comp g f) x = mvfunctor.map g (mvfunctor.map f x) := sorry

protected instance obj.is_lawful_mvfunctor {n : ℕ} (P : mvpfunctor n) : is_lawful_mvfunctor (obj P) :=
  is_lawful_mvfunctor.mk (id_map P) (comp_map P)

/-- Constant functor where the input object does not affect the output -/
def const (n : ℕ) (A : Type u) : mvpfunctor n :=
  mk A fun (a : A) (i : fin2 n) => pempty

/-- Constructor for the constant functor -/
def const.mk (n : ℕ) {A : Type u} (x : A) {α : typevec n} : obj (const n A) α :=
  sigma.mk x fun (i : fin2 n) (a : B (const n A) x i) => pempty.elim a

/-- Destructor for the constant functor -/
def const.get {n : ℕ} {A : Type u} {α : typevec n} (x : obj (const n A) α) : A :=
  sigma.fst x

@[simp] theorem const.get_map {n : ℕ} {A : Type u} {α : typevec n} {β : typevec n} (f : typevec.arrow α β) (x : obj (const n A) α) : const.get (mvfunctor.map f x) = const.get x :=
  sigma.cases_on x
    fun (x_fst : A (const n A)) (x_snd : typevec.arrow (B (const n A) x_fst) α) =>
      Eq.refl (const.get (mvfunctor.map f (sigma.mk x_fst x_snd)))

@[simp] theorem const.get_mk {n : ℕ} {A : Type u} {α : typevec n} (x : A) : const.get (const.mk n x) = x :=
  Eq.refl (const.get (const.mk n x))

@[simp] theorem const.mk_get {n : ℕ} {A : Type u} {α : typevec n} (x : obj (const n A) α) : const.mk n (const.get x) = x := sorry

/-- Functor composition on polynomial functors -/
def comp {n : ℕ} {m : ℕ} (P : mvpfunctor n) (Q : fin2 n → mvpfunctor m) : mvpfunctor m :=
  mk (sigma fun (a₂ : A P) => (i : fin2 n) → B P a₂ i → A (Q i))
    fun (a : sigma fun (a₂ : A P) => (i : fin2 n) → B P a₂ i → A (Q i)) (i : fin2 m) =>
      sigma fun (j : fin2 n) => sigma fun (b : B P (sigma.fst a) j) => B (Q j) (sigma.snd a j b) i

/-- Constructor for functor composition -/
def comp.mk {n : ℕ} {m : ℕ} {P : mvpfunctor n} {Q : fin2 n → mvpfunctor m} {α : typevec m} (x : obj P fun (i : fin2 n) => obj (Q i) α) : obj (comp P Q) α :=
  sigma.mk (sigma.mk (sigma.fst x) fun (i : fin2 n) (a : B P (sigma.fst x) i) => sigma.fst (sigma.snd x i a))
    fun (i : fin2 m)
      (a :
      B (comp P Q) (sigma.mk (sigma.fst x) fun (i : fin2 n) (a : B P (sigma.fst x) i) => sigma.fst (sigma.snd x i a))
        i) =>
      sigma.snd (sigma.snd x (sigma.fst a) (sigma.fst (sigma.snd a))) i (sigma.snd (sigma.snd a))

/-- Destructor for functor composition -/
def comp.get {n : ℕ} {m : ℕ} {P : mvpfunctor n} {Q : fin2 n → mvpfunctor m} {α : typevec m} (x : obj (comp P Q) α) : obj P fun (i : fin2 n) => obj (Q i) α :=
  sigma.mk (sigma.fst (sigma.fst x))
    fun (i : fin2 n) (a : B P (sigma.fst (sigma.fst x)) i) =>
      sigma.mk (sigma.snd (sigma.fst x) i a)
        fun (j : fin2 m) (b : B (Q i) (sigma.snd (sigma.fst x) i a) j) => sigma.snd x j (sigma.mk i (sigma.mk a b))

theorem comp.get_map {n : ℕ} {m : ℕ} {P : mvpfunctor n} {Q : fin2 n → mvpfunctor m} {α : typevec m} {β : typevec m} (f : typevec.arrow α β) (x : obj (comp P Q) α) : comp.get (mvfunctor.map f x) = mvfunctor.map (fun (i : fin2 n) (x : obj (Q i) α) => mvfunctor.map f x) (comp.get x) :=
  sigma.cases_on x
    fun (x_fst : A (comp P Q)) (x_snd : typevec.arrow (B (comp P Q) x_fst) α) =>
      Eq.refl (comp.get (mvfunctor.map f (sigma.mk x_fst x_snd)))

@[simp] theorem comp.get_mk {n : ℕ} {m : ℕ} {P : mvpfunctor n} {Q : fin2 n → mvpfunctor m} {α : typevec m} (x : obj P fun (i : fin2 n) => obj (Q i) α) : comp.get (comp.mk x) = x := sorry

@[simp] theorem comp.mk_get {n : ℕ} {m : ℕ} {P : mvpfunctor n} {Q : fin2 n → mvpfunctor m} {α : typevec m} (x : obj (comp P Q) α) : comp.mk (comp.get x) = x := sorry

/-
lifting predicates and relations
-/

theorem liftp_iff {n : ℕ} {P : mvpfunctor n} {α : typevec n} (p : {i : fin2 n} → α i → Prop) (x : obj P α) : mvfunctor.liftp p x ↔
  ∃ (a : A P), ∃ (f : typevec.arrow (B P a) α), x = sigma.mk a f ∧ ∀ (i : fin2 n) (j : B P a i), p (f i j) := sorry

theorem liftp_iff' {n : ℕ} {P : mvpfunctor n} {α : typevec n} (p : {i : fin2 n} → α i → Prop) (a : A P) (f : typevec.arrow (B P a) α) : mvfunctor.liftp p (sigma.mk a f) ↔ ∀ (i : fin2 n) (x : B P a i), p (f i x) := sorry

theorem liftr_iff {n : ℕ} {P : mvpfunctor n} {α : typevec n} (r : {i : fin2 n} → α i → α i → Prop) (x : obj P α) (y : obj P α) : mvfunctor.liftr r x y ↔
  ∃ (a : A P),
    ∃ (f₀ : typevec.arrow (B P a) α),
      ∃ (f₁ : typevec.arrow (B P a) α),
        x = sigma.mk a f₀ ∧ y = sigma.mk a f₁ ∧ ∀ (i : fin2 n) (j : B P a i), r (f₀ i j) (f₁ i j) := sorry

theorem supp_eq {n : ℕ} {P : mvpfunctor n} {α : typevec n} (a : A P) (f : typevec.arrow (B P a) α) (i : fin2 n) : mvfunctor.supp (sigma.mk a f) i = f i '' set.univ := sorry

end mvpfunctor


/-
Decomposing an n+1-ary pfunctor.
-/

namespace mvpfunctor


/-- Split polynomial functor, get a n-ary functor
from a `n+1`-ary functor -/
def drop {n : ℕ} (P : mvpfunctor (n + 1)) : mvpfunctor n :=
  mk (A P) fun (a : A P) => typevec.drop (B P a)

/-- Split polynomial functor, get a univariate functor
from a `n+1`-ary functor -/
def last {n : ℕ} (P : mvpfunctor (n + 1)) : pfunctor :=
  pfunctor.mk (A P) fun (a : A P) => typevec.last (B P a)

/-- append arrows of a polynomial functor application -/
def append_contents {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} {β : Type u_1} {a : A P} (f' : typevec.arrow (B (drop P) a) α) (f : pfunctor.B (last P) a → β) : typevec.arrow (B P a) (α ::: β) :=
  typevec.split_fun f' f

