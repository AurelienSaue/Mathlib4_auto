/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad, Mario Carneiro, Simon Hudon
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.pfunctor.univariate.default
import Mathlib.data.pfunctor.multivariate.basic
import Mathlib.PostPort

universes u l u_1 

namespace Mathlib

/-!
# The M construction as a multivariate polynomial functor.

M types are potentially infinite tree-like structures. They are defined
as the greatest fixpoint of a polynomial functor.

## Main definitions

 * `M.mk`     - constructor
 * `M.dest`   - destructor
 * `M.corec`  - corecursor: useful for formulating infinite, productive computations
 * `M.bisim`  - bisimulation: proof technique to show the equality of infinite objects

## Implementation notes

Dual view of M-types:

 * `Mp`: polynomial functor
 * `M`: greatest fixed point of a polynomial functor

Specifically, we define the polynomial functor `Mp` as:

 * A := a possibly infinite tree-like structure without information in the nodes
 * B := given the tree-like structure `t`, `B t` is a valid path
   from the root of `t` to any given node.

As a result `Mp.obj α` is made of a dataless tree and a function from
its valid paths to values of `α`

The difference with the polynomial functor of an initial algebra is
that `A` is a possibly infinite tree.

## Reference

 * [Jeremy Avigad, Mario M. Carneiro and Simon Hudon, *Data Types as Quotients of Polynomial Functors*][avigad-carneiro-hudon2019]
-/

namespace mvpfunctor


/-- A path from the root of a tree to one of its node -/
inductive M.path {n : ℕ} (P : mvpfunctor (n + 1)) : pfunctor.M (last P) → fin2 n → Type u
where
| root : (x : pfunctor.M (last P)) →
  (a : A P) →
    (f : pfunctor.B (last P) a → pfunctor.M (last P)) →
      pfunctor.M.dest x = sigma.mk a f → (i : fin2 n) → B (drop P) a i → M.path P x i
| child : (x : pfunctor.M (last P)) →
  (a : A P) →
    (f : pfunctor.B (last P) a → pfunctor.M (last P)) →
      pfunctor.M.dest x = sigma.mk a f → (j : pfunctor.B (last P) a) → (i : fin2 n) → M.path P (f j) i → M.path P x i

protected instance M.path.inhabited {n : ℕ} (P : mvpfunctor (n + 1)) (x : pfunctor.M (last P)) {i : fin2 n} [Inhabited (B (drop P) (pfunctor.M.head x) i)] : Inhabited (M.path P x i) :=
  { default := M.path.root x (pfunctor.M.head x) (pfunctor.M.children x) sorry i Inhabited.default }

/-- Polynomial functor of the M-type of `P`. `A` is a data-less
possibly infinite tree whereas, for a given `a : A`, `B a` is a valid
path in tree `a` so that `Wp.obj α` is made of a tree and a function
from its valid paths to the values it contains -/
def Mp {n : ℕ} (P : mvpfunctor (n + 1)) : mvpfunctor n :=
  mk (pfunctor.M (last P)) (M.path P)

/-- `n`-ary M-type for `P` -/
def M {n : ℕ} (P : mvpfunctor (n + 1)) (α : typevec n) :=
  obj (Mp P) α

protected instance mvfunctor_M {n : ℕ} (P : mvpfunctor (n + 1)) : mvfunctor (M P) :=
  id (obj.mvfunctor (Mp P))

protected instance inhabited_M {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} [I : Inhabited (A P)] [(i : fin2 n) → Inhabited (α i)] : Inhabited (M P α) :=
  obj.inhabited (Mp P)

/-- construct through corecursion the shape of an M-type
without its contents -/
def M.corec_shape {n : ℕ} (P : mvpfunctor (n + 1)) {β : Type u} (g₀ : β → A P) (g₂ : (b : β) → pfunctor.B (last P) (g₀ b) → β) : β → pfunctor.M (last P) :=
  pfunctor.M.corec fun (b : β) => sigma.mk (g₀ b) (g₂ b)

/-- Proof of type equality as an arrow -/
def cast_dropB {n : ℕ} (P : mvpfunctor (n + 1)) {a : A P} {a' : A P} (h : a = a') : typevec.arrow (B (drop P) a) (B (drop P) a') :=
  fun (i : fin2 n) (b : B (drop P) a i) => eq.rec_on h b

/-- Proof of type equality as a function -/
def cast_lastB {n : ℕ} (P : mvpfunctor (n + 1)) {a : A P} {a' : A P} (h : a = a') : pfunctor.B (last P) a → pfunctor.B (last P) a' :=
  fun (b : pfunctor.B (last P) a) => eq.rec_on h b

/-- Using corecursion, construct the contents of an M-type -/
def M.corec_contents {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} {β : Type u} (g₀ : β → A P) (g₁ : (b : β) → typevec.arrow (B (drop P) (g₀ b)) α) (g₂ : (b : β) → pfunctor.B (last P) (g₀ b) → β) (x : pfunctor.M (last P)) (b : β) : x = M.corec_shape P g₀ g₂ b → typevec.arrow (M.path P x) α :=
  sorry

/-- Corecursor for M-type of `P` -/
def M.corec' {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} {β : Type u} (g₀ : β → A P) (g₁ : (b : β) → typevec.arrow (B (drop P) (g₀ b)) α) (g₂ : (b : β) → pfunctor.B (last P) (g₀ b) → β) : β → M P α :=
  fun (b : β) => sigma.mk (M.corec_shape P g₀ g₂ b) (M.corec_contents P g₀ g₁ g₂ (M.corec_shape P g₀ g₂ b) b sorry)

/-- Corecursor for M-type of `P` -/
def M.corec {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} {β : Type u} (g : β → obj P (α ::: β)) : β → M P α :=
  M.corec' P (fun (b : β) => sigma.fst (g b)) (fun (b : β) => typevec.drop_fun (sigma.snd (g b)))
    fun (b : β) => typevec.last_fun (sigma.snd (g b))

/-- Implementation of destructor for M-type of `P` -/
def M.path_dest_left {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} {x : pfunctor.M (last P)} {a : A P} {f : pfunctor.B (last P) a → pfunctor.M (last P)} (h : pfunctor.M.dest x = sigma.mk a f) (f' : typevec.arrow (M.path P x) α) : typevec.arrow (B (drop P) a) α :=
  fun (i : fin2 n) (c : B (drop P) a i) => f' i (M.path.root x a f h i c)

/-- Implementation of destructor for M-type of `P` -/
def M.path_dest_right {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} {x : pfunctor.M (last P)} {a : A P} {f : pfunctor.B (last P) a → pfunctor.M (last P)} (h : pfunctor.M.dest x = sigma.mk a f) (f' : typevec.arrow (M.path P x) α) (j : pfunctor.B (last P) a) : typevec.arrow (M.path P (f j)) α :=
  fun (i : fin2 n) (c : M.path P (f j) i) => f' i (M.path.child x a f h j i c)

/-- Destructor for M-type of `P` -/
def M.dest' {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} {x : pfunctor.M (last P)} {a : A P} {f : pfunctor.B (last P) a → pfunctor.M (last P)} (h : pfunctor.M.dest x = sigma.mk a f) (f' : typevec.arrow (M.path P x) α) : obj P (α ::: M P α) :=
  sigma.mk a
    (typevec.split_fun (M.path_dest_left P h f')
      fun (x_1 : typevec.last (B P a)) => sigma.mk (f x_1) (M.path_dest_right P h f' x_1))

/-- Destructor for M-types -/
def M.dest {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} (x : M P α) : obj P (α ::: M P α) :=
  M.dest' P sorry (sigma.snd x)

/-- Constructor for M-types -/
def M.mk {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} : obj P (α ::: M P α) → M P α :=
  M.corec P fun (i : obj P (α ::: M P α)) => mvfunctor.map (typevec.id ::: M.dest P) i

theorem M.dest'_eq_dest' {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} {x : pfunctor.M (last P)} {a₁ : A P} {f₁ : pfunctor.B (last P) a₁ → pfunctor.M (last P)} (h₁ : pfunctor.M.dest x = sigma.mk a₁ f₁) {a₂ : A P} {f₂ : pfunctor.B (last P) a₂ → pfunctor.M (last P)} (h₂ : pfunctor.M.dest x = sigma.mk a₂ f₂) (f' : typevec.arrow (M.path P x) α) : M.dest' P h₁ f' = M.dest' P h₂ f' := sorry

theorem M.dest_eq_dest' {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} {x : pfunctor.M (last P)} {a : A P} {f : pfunctor.B (last P) a → pfunctor.M (last P)} (h : pfunctor.M.dest x = sigma.mk a f) (f' : typevec.arrow (M.path P x) α) : M.dest P (sigma.mk x f') = M.dest' P h f' :=
  M.dest'_eq_dest' P (M.dest._proof_1 P (sigma.mk x f')) h (sigma.snd (sigma.mk x f'))

theorem M.dest_corec' {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} {β : Type u} (g₀ : β → A P) (g₁ : (b : β) → typevec.arrow (B (drop P) (g₀ b)) α) (g₂ : (b : β) → pfunctor.B (last P) (g₀ b) → β) (x : β) : M.dest P (M.corec' P g₀ g₁ g₂ x) = sigma.mk (g₀ x) (typevec.split_fun (g₁ x) (M.corec' P g₀ g₁ g₂ ∘ g₂ x)) :=
  rfl

theorem M.dest_corec {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} {β : Type u} (g : β → obj P (α ::: β)) (x : β) : M.dest P (M.corec P g x) = mvfunctor.map (typevec.id ::: M.corec P g) (g x) := sorry

theorem M.bisim_lemma {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} {a₁ : A (Mp P)} {f₁ : typevec.arrow (B (Mp P) a₁) α} {a' : A P} {f' : typevec.arrow (typevec.drop (B P a')) α} {f₁' : typevec.last (B P a') → M P α} (e₁ : M.dest P (sigma.mk a₁ f₁) = sigma.mk a' (typevec.split_fun f' f₁')) : ∃ (g₁' : pfunctor.B (last P) a' → pfunctor.M (last P)),
  ∃ (e₁' : pfunctor.M.dest a₁ = sigma.mk a' g₁'),
    f' = M.path_dest_left P e₁' f₁ ∧
      f₁' = fun (x : pfunctor.B (last P) a') => sigma.mk (g₁' x) (M.path_dest_right P e₁' f₁ x) := sorry

theorem M.bisim {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} (R : M P α → M P α → Prop) (h : ∀ (x y : M P α),
  R x y →
    ∃ (a : A P),
      ∃ (f : typevec.arrow (typevec.drop (B P a)) (typevec.drop (α ::: M P α))),
        ∃ (f₁ : typevec.last (B P a) → typevec.last (α ::: M P α)),
          ∃ (f₂ : typevec.last (B P a) → typevec.last (α ::: M P α)),
            M.dest P x = sigma.mk a (typevec.split_fun f f₁) ∧
              M.dest P y = sigma.mk a (typevec.split_fun f f₂) ∧ ∀ (i : typevec.last (B P a)), R (f₁ i) (f₂ i)) (x : M P α) (y : M P α) (r : R x y) : x = y := sorry

theorem M.bisim₀ {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} (R : M P α → M P α → Prop) (h₀ : equivalence R) (h : ∀ (x y : M P α),
  R x y → mvfunctor.map (typevec.id ::: Quot.mk R) (M.dest P x) = mvfunctor.map (typevec.id ::: Quot.mk R) (M.dest P y)) (x : M P α) (y : M P α) (r : R x y) : x = y := sorry

theorem M.bisim' {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} (R : M P α → M P α → Prop) (h : ∀ (x y : M P α),
  R x y → mvfunctor.map (typevec.id ::: Quot.mk R) (M.dest P x) = mvfunctor.map (typevec.id ::: Quot.mk R) (M.dest P y)) (x : M P α) (y : M P α) (r : R x y) : x = y := sorry

theorem M.dest_map {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} {β : typevec n} (g : typevec.arrow α β) (x : M P α) : M.dest P (mvfunctor.map g x) = mvfunctor.map (g ::: fun (x : M P α) => mvfunctor.map g x) (M.dest P x) := sorry

theorem M.map_dest {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} {β : typevec n} (g : typevec.arrow (α ::: M P α) (β ::: M P β)) (x : M P α) (h : ∀ (x : M P α), typevec.last_fun g x = mvfunctor.map (typevec.drop_fun g) x) : mvfunctor.map g (M.dest P x) = M.dest P (mvfunctor.map (typevec.drop_fun g) x) := sorry

