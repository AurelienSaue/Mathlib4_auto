/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.ring
import Mathlib.data.num.lemmas
import Mathlib.data.tree
import Mathlib.PostPort

universes u_1 l 

namespace Mathlib

/-!
# ring2

An experimental variant on the `ring` tactic that uses computational
reflection instead of proof generation. Useful for kernel benchmarking.
-/

namespace tree


/-- `(reflect' t u α)` quasiquotes a tree `(t: tree expr)` of quoted
values of type `α` at level `u` into an `expr` which reifies to a `tree α`
containing the reifications of the `expr`s from the original `t`. -/
/-- Returns an element indexed by `n`, or zero if `n` isn't a valid index.
See `tree.get`. -/
protected def get_or_zero {α : Type u_1} [HasZero α] (t : tree α) (n : pos_num) : α :=
  get_or_else n t 0

end tree


namespace tactic.ring2


/-- A reflected/meta representation of an expression in a commutative
semiring. This representation is a direct translation of such
expressions - see `horner_expr` for a normal form. -/
/- (atom n) is an opaque element of the csring. For example,
inductive csring_expr 
where
| atom : pos_num → csring_expr
| const : num → csring_expr
| add : csring_expr → csring_expr → csring_expr
| mul : csring_expr → csring_expr → csring_expr
| pow : csring_expr → num → csring_expr

a local variable in the context. n indexes into a storage
of such atoms - a `tree α`. -/

/- (const n) is technically the csring's one, added n times.
Or the zero if n is 0. -/

namespace csring_expr


protected instance inhabited : Inhabited csring_expr :=
  { default := const 0 }

/-- Evaluates a reflected `csring_expr` into an element of the
original `comm_semiring` type `α`, retrieving opaque elements
(atoms) from the tree `t`. -/
def eval {α : Type u_1} [comm_semiring α] (t : tree α) : csring_expr → α :=
  sorry

end csring_expr


/-- An efficient representation of expressions in a commutative
semiring using the sparse Horner normal form. This type admits
non-optimal instantiations (e.g. `P` can be represented as `P+0+0`),
so to get good performance out of it, care must be taken to maintain
an optimal, *canonical* form. -/
/- (const n) is a constant n in the csring, similarly to the same
inductive horner_expr 
where
| const : znum → horner_expr
| horner : horner_expr → pos_num → num → horner_expr → horner_expr

constructor in `csring_expr`. This one, however, can be negative. -/

/- (horner a x n b) is a*xⁿ + b, where x is the x-th atom
in the atom tree. -/

namespace horner_expr


/-- True iff the `horner_expr` argument is a valid `csring_expr`.
For that to be the case, all its constants must be non-negative. -/
def is_cs : horner_expr → Prop :=
  sorry

protected instance has_zero : HasZero horner_expr :=
  { zero := const 0 }

protected instance has_one : HasOne horner_expr :=
  { one := const 1 }

protected instance inhabited : Inhabited horner_expr :=
  { default := 0 }

/-- Represent a `csring_expr.atom` in Horner form. -/
def atom (n : pos_num) : horner_expr :=
  horner 1 n 1 0

def to_string : horner_expr → string :=
  sorry

protected instance has_to_string : has_to_string horner_expr :=
  has_to_string.mk to_string

/-- Alternative constructor for (horner a x n b) which maintains canonical
form by simplifying special cases of `a`. -/
def horner' (a : horner_expr) (x : pos_num) (n : num) (b : horner_expr) : horner_expr :=
  sorry

def add_const (k : znum) (e : horner_expr) : horner_expr :=
  ite (k = 0) e
    (horner_expr.rec (fun (n : znum) => const (k + n))
      (fun (a : horner_expr) (x : pos_num) (n : num) (b A B : horner_expr) => horner a x n B) e)

def add_aux (a₁ : horner_expr) (A₁ : horner_expr → horner_expr) (x₁ : pos_num) : horner_expr → num → horner_expr → (horner_expr → horner_expr) → horner_expr :=
  sorry

def add : horner_expr → horner_expr → horner_expr :=
  sorry

/-begin
  induction e₁ with n₁ a₁ x₁ n₁ b₁ A₁ B₁ generalizing e₂,
  { exact add_const n₁ e₂ },
  exact match e₂ with e₂ := begin
    induction e₂ with n₂ a₂ x₂ n₂ b₂ A₂ B₂ generalizing n₁ b₁;
    let e₁ := horner a₁ x₁ n₁ b₁,
    { exact add_const n₂ e₁ },
    let e₂ := horner a₂ x₂ n₂ b₂,
    exact match pos_num.cmp x₁ x₂ with
    | ordering.lt := horner a₁ x₁ n₁ (B₁ e₂)
    | ordering.gt := horner a₂ x₂ n₂ (B₂ n₁ b₁)
    | ordering.eq :=
      match num.sub' n₁ n₂ with
      | znum.zero := horner' (A₁ a₂) x₁ n₁ (B₁ b₂)
      | (znum.pos k) := horner (A₂ k 0) x₁ n₂ (B₁ b₂)
      | (znum.neg k) := horner (A₁ (horner a₂ x₁ k 0)) x₁ n₁ (B₁ b₂)
      end
    end
  end end
end-/

def neg (e : horner_expr) : horner_expr :=
  horner_expr.rec (fun (n : znum) => const (-n))
    (fun (a : horner_expr) (x : pos_num) (n : num) (b A B : horner_expr) => horner A x n B) e

def mul_const (k : znum) (e : horner_expr) : horner_expr :=
  ite (k = 0) 0
    (ite (k = 1) e
      (horner_expr.rec (fun (n : znum) => const (n * k))
        (fun (a : horner_expr) (x : pos_num) (n : num) (b A B : horner_expr) => horner A x n B) e))

def mul_aux (a₁ : horner_expr) (x₁ : pos_num) (n₁ : num) (b₁ : horner_expr) (A₁ : horner_expr → horner_expr) (B₁ : horner_expr → horner_expr) : horner_expr → horner_expr :=
  sorry

def mul : horner_expr → horner_expr → horner_expr :=
  sorry

/-begin
  induction e₁ with n₁ a₁ x₁ n₁ b₁ A₁ B₁ generalizing e₂,
  { exact mul_const n₁ e₂ },
  induction e₂ with n₂ a₂ x₂ n₂ b₂ A₂ B₂;
  let e₁ := horner a₁ x₁ n₁ b₁,
  { exact mul_const n₂ e₁ },
  let e₂ := horner a₂ x₂ n₂ b₂,
  cases pos_num.cmp x₁ x₂,
  { exact horner (A₁ e₂) x₁ n₁ (B₁ e₂) },
  { let haa := horner' A₂ x₁ n₂ 0,
    exact if b₂ = 0 then haa else
      haa.add (horner (A₁ b₂) x₁ n₁ (B₁ b₂)) },
  { exact horner A₂ x₂ n₂ B₂ }
end-/

protected instance has_add : Add horner_expr :=
  { add := add }

protected instance has_neg : Neg horner_expr :=
  { neg := neg }

protected instance has_mul : Mul horner_expr :=
  { mul := mul }

def pow (e : horner_expr) : num → horner_expr :=
  sorry

def inv (e : horner_expr) : horner_expr :=
  0

/-- Brings expressions into Horner normal form. -/
def of_csexpr : csring_expr → horner_expr :=
  sorry

/-- Evaluates a reflected `horner_expr` - see `csring_expr.eval`. -/
def cseval {α : Type u_1} [comm_semiring α] (t : tree α) : horner_expr → α :=
  sorry

theorem cseval_atom {α : Type u_1} [comm_semiring α] (t : tree α) (n : pos_num) : is_cs (atom n) ∧ cseval t (atom n) = tree.get_or_zero t n :=
  { left := { left := Exists.intro 1 rfl, right := Exists.intro 0 rfl },
    right := Eq.symm (ring.horner_atom (tree.get_or_zero t n)) }

theorem cseval_add_const {α : Type u_1} [comm_semiring α] (t : tree α) (k : num) {e : horner_expr} (cs : is_cs e) : is_cs (add_const (num.to_znum k) e) ∧ cseval t (add_const (num.to_znum k) e) = ↑k + cseval t e := sorry

theorem cseval_horner' {α : Type u_1} [comm_semiring α] (t : tree α) (a : horner_expr) (x : pos_num) (n : num) (b : horner_expr) (h₁ : is_cs a) (h₂ : is_cs b) : is_cs (horner' a x n b) ∧ cseval t (horner' a x n b) = ring.horner (cseval t a) (tree.get_or_zero t x) (↑n) (cseval t b) := sorry

theorem cseval_add {α : Type u_1} [comm_semiring α] (t : tree α) {e₁ : horner_expr} {e₂ : horner_expr} (cs₁ : is_cs e₁) (cs₂ : is_cs e₂) : is_cs (add e₁ e₂) ∧ cseval t (add e₁ e₂) = cseval t e₁ + cseval t e₂ := sorry

theorem cseval_mul_const {α : Type u_1} [comm_semiring α] (t : tree α) (k : num) {e : horner_expr} (cs : is_cs e) : is_cs (mul_const (num.to_znum k) e) ∧ cseval t (mul_const (num.to_znum k) e) = cseval t e * ↑k := sorry

theorem cseval_mul {α : Type u_1} [comm_semiring α] (t : tree α) {e₁ : horner_expr} {e₂ : horner_expr} (cs₁ : is_cs e₁) (cs₂ : is_cs e₂) : is_cs (mul e₁ e₂) ∧ cseval t (mul e₁ e₂) = cseval t e₁ * cseval t e₂ := sorry

theorem cseval_pow {α : Type u_1} [comm_semiring α] (t : tree α) {x : horner_expr} (cs : is_cs x) (n : num) : is_cs (pow x n) ∧ cseval t (pow x n) = cseval t x ^ ↑n := sorry

/-- For any given tree `t` of atoms and any reflected expression `r`,
the Horner form of `r` is a valid csring expression, and under `t`,
the Horner form evaluates to the same thing as `r`. -/
theorem cseval_of_csexpr {α : Type u_1} [comm_semiring α] (t : tree α) (r : csring_expr) : is_cs (of_csexpr r) ∧ cseval t (of_csexpr r) = csring_expr.eval t r := sorry

end horner_expr


/-- The main proof-by-reflection theorem. Given reflected csring expressions
`r₁` and `r₂` plus a storage `t` of atoms, if both expressions go to the
same Horner normal form, then the original non-reflected expressions are
equal. `H` follows from kernel reduction and is therefore `rfl`. -/
theorem correctness {α : Type u_1} [comm_semiring α] (t : tree α) (r₁ : csring_expr) (r₂ : csring_expr) (H : horner_expr.of_csexpr r₁ = horner_expr.of_csexpr r₂) : csring_expr.eval t r₁ = csring_expr.eval t r₂ := sorry

/-- Reflects a csring expression into a `csring_expr`, together
with a dlist of atoms, i.e. opaque variables over which the
expression is a polynomial. -/
/-| `(%%e₁ - %%e₂) :=
  let (r₁, l₁) := reflect_expr e₁, (r₂, l₂) := reflect_expr e₂ in
  (r₁.add r₂.neg, l₁ ++ l₂)
| `(- %%e) := let (r, l) := reflect_expr e in (r.neg, l)-/

/-| `(has_inv.inv %%e) := let (r, l) := reflect_expr e in (r.neg, l)
| `(%%e₁ / %%e₂) :=
  let (r₁, l₁) := reflect_expr e₁, (r₂, l₂) := reflect_expr e₂ in
  (r₁.mul r₂.inv, l₁ ++ l₂)-/

/-- In the output of `reflect_expr`, `atom`s are initialized with incorrect indices.
The indices cannot be computed until the whole tree is built, so another pass over
the expressions is needed - this is what `replace` does. The computation (expressed
in the state monad) fixes up `atom`s to match their positions in the atom tree.
The initial state is a list of all atom occurrences in the goal, left-to-right. -/
--| (csring_expr.neg x)  := csring_expr.neg <$> x.replace

--| (csring_expr.inv x)  := csring_expr.inv <$> x.replace

end tactic.ring2


namespace tactic


namespace interactive


/-- `ring2` solves equations in the language of rings.

It supports only the commutative semiring operations, i.e. it does not normalize subtraction or division.

  This variant on the `ring` tactic uses kernel computation instead
  of proof generation. In general, you should use `ring` instead of `ring2`. -/
