/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad, Simon Hudon
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.pfunctor.multivariate.basic
import PostPort

universes u l u_1 u_2 

namespace Mathlib

/-!
# The W construction as a multivariate polynomial functor.

W types are well-founded tree-like structures. They are defined
as the least fixpoint of a polynomial functor.

## Main definitions

 * `W_mk`     - constructor
 * `W_dest    - destructor
 * `W_rec`    - recursor: basis for defining functions by structural recursion on `P.W α`
 * `W_rec_eq` - defining equation for `W_rec`
 * `W_ind`    - induction principle for `P.W α`

## Implementation notes

Three views of M-types:

 * `Wp`: polynomial functor
 * `W`: data type inductively defined by a triple: shape of the root, data in the root and children of the root
 * `W`: least fixed point of a polynomial functor

Specifically, we define the polynomial functor `Wp` as:

 * A := a tree-like structure without information in the nodes
 * B := given the tree-like structure `t`, `B t` is a valid path
   (specified inductively by `W_path`) from the root of `t` to any given node.

As a result `Wp.obj α` is made of a dataless tree and a function from
its valid paths to values of `α`

## Reference

 * [Jeremy Avigad, Mario M. Carneiro and Simon Hudon, *Data Types as Quotients of Polynomial Functors*][avigad-carneiro-hudon2019]
-/

namespace mvpfunctor


/-- A path from the root of a tree to one of its node -/
inductive W_path {n : ℕ} (P : mvpfunctor (n + 1)) : pfunctor.W (last P) → fin2 n → Type u
where
| root : (a : A P) →
  (f : pfunctor.B (last P) a → pfunctor.W (last P)) → (i : fin2 n) → B (drop P) a i → W_path P (W_type.mk a f) i
| child : (a : A P) →
  (f : pfunctor.B (last P) a → pfunctor.W (last P)) →
    (i : fin2 n) → (j : pfunctor.B (last P) a) → W_path P (f j) i → W_path P (W_type.mk a f) i

protected instance W_path.inhabited {n : ℕ} (P : mvpfunctor (n + 1)) (x : pfunctor.W (last P)) {i : fin2 n} [I : Inhabited (B (drop P) (pfunctor.W.head x) i)] : Inhabited (W_path P x i) :=
  { default := sorry }

/-- Specialized destructor on `W_path` -/
def W_path_cases_on {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} {a : A P} {f : pfunctor.B (last P) a → pfunctor.W (last P)} (g' : typevec.arrow (B (drop P) a) α) (g : (j : pfunctor.B (last P) a) → typevec.arrow (W_path P (f j)) α) : typevec.arrow (W_path P (W_type.mk a f)) α := sorry

/-- Specialized destructor on `W_path` -/
def W_path_dest_left {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} {a : A P} {f : pfunctor.B (last P) a → pfunctor.W (last P)} (h : typevec.arrow (W_path P (W_type.mk a f)) α) : typevec.arrow (B (drop P) a) α :=
  fun (i : fin2 n) (c : B (drop P) a i) => h i (W_path.root a f i c)

/-- Specialized destructor on `W_path` -/
def W_path_dest_right {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} {a : A P} {f : pfunctor.B (last P) a → pfunctor.W (last P)} (h : typevec.arrow (W_path P (W_type.mk a f)) α) (j : pfunctor.B (last P) a) : typevec.arrow (W_path P (f j)) α :=
  fun (i : fin2 n) (c : W_path P (f j) i) => h i (W_path.child a f i j c)

theorem W_path_dest_left_W_path_cases_on {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} {a : A P} {f : pfunctor.B (last P) a → pfunctor.W (last P)} (g' : typevec.arrow (B (drop P) a) α) (g : (j : pfunctor.B (last P) a) → typevec.arrow (W_path P (f j)) α) : W_path_dest_left P (W_path_cases_on P g' g) = g' :=
  rfl

theorem W_path_dest_right_W_path_cases_on {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} {a : A P} {f : pfunctor.B (last P) a → pfunctor.W (last P)} (g' : typevec.arrow (B (drop P) a) α) (g : (j : pfunctor.B (last P) a) → typevec.arrow (W_path P (f j)) α) : W_path_dest_right P (W_path_cases_on P g' g) = g :=
  rfl

theorem W_path_cases_on_eta {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} {a : A P} {f : pfunctor.B (last P) a → pfunctor.W (last P)} (h : typevec.arrow (W_path P (W_type.mk a f)) α) : W_path_cases_on P (W_path_dest_left P h) (W_path_dest_right P h) = h := sorry

theorem comp_W_path_cases_on {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} {β : typevec n} (h : typevec.arrow α β) {a : A P} {f : pfunctor.B (last P) a → pfunctor.W (last P)} (g' : typevec.arrow (B (drop P) a) α) (g : (j : pfunctor.B (last P) a) → typevec.arrow (W_path P (f j)) α) : typevec.comp h (W_path_cases_on P g' g) =
  W_path_cases_on P (typevec.comp h g') fun (i : pfunctor.B (last P) a) => typevec.comp h (g i) := sorry

/-- Polynomial functor for the W-type of `P`. `A` is a data-less well-founded
tree whereas, for a given `a : A`, `B a` is a valid path in tree `a` so
that `Wp.obj α` is made of a tree and a function from its valid paths to
the values it contains  -/
def Wp {n : ℕ} (P : mvpfunctor (n + 1)) : mvpfunctor n :=
  mk (pfunctor.W (last P)) (W_path P)

/-- W-type of `P` -/
def W {n : ℕ} (P : mvpfunctor (n + 1)) (α : typevec n)  :=
  obj (Wp P) α

protected instance mvfunctor_W {n : ℕ} (P : mvpfunctor (n + 1)) : mvfunctor (W P) :=
  id (obj.mvfunctor (Wp P))

/-!
First, describe operations on `W` as a polynomial functor.
-/

/-- Constructor for `Wp` -/
def Wp_mk {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} (a : A P) (f : pfunctor.B (last P) a → pfunctor.W (last P)) (f' : typevec.arrow (W_path P (W_type.mk a f)) α) : W P α :=
  sigma.mk (W_type.mk a f) f'

/-- Recursor for `Wp` -/
def Wp_rec {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} {C : Type u_2} (g : (a : A P) →
  (f : pfunctor.B (last P) a → pfunctor.W (last P)) →
    typevec.arrow (W_path P (W_type.mk a f)) α → (pfunctor.B (last P) a → C) → C) (x : pfunctor.W (last P)) (f' : typevec.arrow (W_path P x) α) : C :=
  sorry

theorem Wp_rec_eq {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} {C : Type u_2} (g : (a : A P) →
  (f : pfunctor.B (last P) a → pfunctor.W (last P)) →
    typevec.arrow (W_path P (W_type.mk a f)) α → (pfunctor.B (last P) a → C) → C) (a : A P) (f : pfunctor.B (last P) a → pfunctor.W (last P)) (f' : typevec.arrow (W_path P (W_type.mk a f)) α) : Wp_rec P g (W_type.mk a f) f' = g a f f' fun (i : pfunctor.B (last P) a) => Wp_rec P g (f i) (W_path_dest_right P f' i) :=
  rfl

-- Note: we could replace Prop by Type* and obtain a dependent recursor

theorem Wp_ind {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} {C : (x : pfunctor.W (last P)) → typevec.arrow (W_path P x) α → Prop} (ih : ∀ (a : A P) (f : pfunctor.B (last P) a → pfunctor.W (last P)) (f' : typevec.arrow (W_path P (W_type.mk a f)) α),
  (∀ (i : pfunctor.B (last P) a), C (f i) (W_path_dest_right P f' i)) → C (W_type.mk a f) f') (x : pfunctor.W (last P)) (f' : typevec.arrow (W_path P x) α) : C x f' := sorry

/-!
Now think of W as defined inductively by the data ⟨a, f', f⟩ where
- `a  : P.A` is the shape of the top node
- `f' : P.drop.B a ⟹ α` is the contents of the top node
- `f  : P.last.B a → P.last.W` are the subtrees
 -/

/-- Constructor for `W` -/
def W_mk {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} (a : A P) (f' : typevec.arrow (B (drop P) a) α) (f : pfunctor.B (last P) a → W P α) : W P α :=
  let g : pfunctor.B (last P) a → pfunctor.W (last P) := fun (i : pfunctor.B (last P) a) => sigma.fst (f i);
  let g' : typevec.arrow (W_path P (W_type.mk a g)) α :=
    W_path_cases_on P f' fun (i : pfunctor.B (last P) a) => sigma.snd (f i);
  sigma.mk (W_type.mk a g) g'

/-- Recursor for `W` -/
def W_rec {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} {C : Type u_1} (g : (a : A P) → typevec.arrow (B (drop P) a) α → (pfunctor.B (last P) a → W P α) → (pfunctor.B (last P) a → C) → C) : W P α → C :=
  sorry

/-- Defining equation for the recursor of `W` -/
theorem W_rec_eq {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} {C : Type u_1} (g : (a : A P) → typevec.arrow (B (drop P) a) α → (pfunctor.B (last P) a → W P α) → (pfunctor.B (last P) a → C) → C) (a : A P) (f' : typevec.arrow (B (drop P) a) α) (f : pfunctor.B (last P) a → W P α) : W_rec P g (W_mk P a f' f) = g a f' f fun (i : pfunctor.B (last P) a) => W_rec P g (f i) := sorry

/-- Induction principle for `W` -/
theorem W_ind {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} {C : W P α → Prop} (ih : ∀ (a : A P) (f' : typevec.arrow (B (drop P) a) α) (f : pfunctor.B (last P) a → W P α),
  (∀ (i : pfunctor.B (last P) a), C (f i)) → C (W_mk P a f' f)) (x : W P α) : C x := sorry

theorem W_cases {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} {C : W P α → Prop} (ih : ∀ (a : A P) (f' : typevec.arrow (B (drop P) a) α) (f : pfunctor.B (last P) a → W P α), C (W_mk P a f' f)) (x : W P α) : C x :=
  W_ind P
    fun (a : A P) (f' : typevec.arrow (B (drop P) a) α) (f : pfunctor.B (last P) a → W P α)
      (ih' : ∀ (i : pfunctor.B (last P) a), C (f i)) => ih a f' f

/-- W-types are functorial -/
def W_map {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} {β : typevec n} (g : typevec.arrow α β) : W P α → W P β :=
  fun (x : W P α) => mvfunctor.map g x

theorem W_mk_eq {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} (a : A P) (f : pfunctor.B (last P) a → pfunctor.W (last P)) (g' : typevec.arrow (B (drop P) a) α) (g : (j : pfunctor.B (last P) a) → typevec.arrow (W_path P (f j)) α) : (W_mk P a g' fun (i : pfunctor.B (last P) a) => sigma.mk (f i) (g i)) =
  sigma.mk (W_type.mk a f) (W_path_cases_on P g' g) :=
  rfl

theorem W_map_W_mk {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} {β : typevec n} (g : typevec.arrow α β) (a : A P) (f' : typevec.arrow (B (drop P) a) α) (f : pfunctor.B (last P) a → W P α) : mvfunctor.map g (W_mk P a f' f) = W_mk P a (typevec.comp g f') fun (i : pfunctor.B (last P) a) => mvfunctor.map g (f i) := sorry

-- TODO: this technical theorem is used in one place in constructing the initial algebra.

-- Can it be avoided?

/-- Constructor of a value of `P.obj (α ::: β)` from components.
Useful to avoid complicated type annotation -/
def obj_append1 {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} {β : Type u} (a : A P) (f' : typevec.arrow (B (drop P) a) α) (f : pfunctor.B (last P) a → β) : obj P (α ::: β) :=
  sigma.mk a (typevec.split_fun f' f)

theorem map_obj_append1 {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} {γ : typevec n} (g : typevec.arrow α γ) (a : A P) (f' : typevec.arrow (B (drop P) a) α) (f : pfunctor.B (last P) a → W P α) : mvfunctor.map (g ::: W_map P g) (obj_append1 P a f' f) =
  obj_append1 P a (typevec.comp g f') fun (x : pfunctor.B (last P) a) => W_map P g (f x) := sorry

/-!
Yet another view of the W type: as a fixed point for a multivariate polynomial functor.
These are needed to use the W-construction to construct a fixed point of a qpf, since
the qpf axioms are expressed in terms of `map` on `P`.
-/

/-- Constructor for the W-type of `P` -/
def W_mk' {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} : obj P (α ::: W P α) → W P α :=
  sorry

/-- Destructor for the W-type of `P` -/
def W_dest' {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} : W P α → obj P (α ::: W P α) :=
  W_rec P
    fun (a : A P) (f' : typevec.arrow (B (drop P) a) α) (f : pfunctor.B (last P) a → W P α)
      (_x : pfunctor.B (last P) a → obj P (α ::: W P α)) => sigma.mk a (typevec.split_fun f' f)

theorem W_dest'_W_mk {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} (a : A P) (f' : typevec.arrow (B (drop P) a) α) (f : pfunctor.B (last P) a → W P α) : W_dest' P (W_mk P a f' f) = sigma.mk a (typevec.split_fun f' f) := sorry

theorem W_dest'_W_mk' {n : ℕ} (P : mvpfunctor (n + 1)) {α : typevec n} (x : obj P (α ::: W P α)) : W_dest' P (W_mk' P x) = x := sorry

