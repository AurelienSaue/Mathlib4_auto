/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.number_theory.pell
import Mathlib.data.pfun
import Mathlib.data.fin2
import Mathlib.PostPort

universes u u_1 u_2 u_3 

namespace Mathlib

namespace int


theorem eq_nat_abs_iff_mul (x : ℤ) (n : ℕ) : nat_abs x = n ↔ (x - ↑n) * (x + ↑n) = 0 := sorry

end int


/-- Alternate definition of `vector` based on `fin2`. -/
def vector3 (α : Type u) (n : ℕ) :=
  fin2 n → α

namespace vector3


/-- The empty vector -/
def nil {α : Type u_1} : vector3 α 0 :=
  sorry

/-- The vector cons operation -/
def cons {α : Type u_1} {n : ℕ} (a : α) (v : vector3 α n) : vector3 α (Nat.succ n) :=
  fun (i : fin2 (Nat.succ n)) => fin2.cases' a v i

infixr:67 " :: " => Mathlib.vector3.cons

/- We do not want to make the following notation global, because then these expressions will be
overloaded, and only the expected type will be able to disambiguate the meaning. Worse: Lean will
try to insert a coercion from `vector3 α _` to `list α`, if a list is expected. -/

@[simp] theorem cons_fz {α : Type u_1} {n : ℕ} (a : α) (v : vector3 α n) : cons a v fin2.fz = a :=
  rfl

@[simp] theorem cons_fs {α : Type u_1} {n : ℕ} (a : α) (v : vector3 α n) (i : fin2 n) : cons a v (fin2.fs i) = v i :=
  rfl

/-- Get the `i`th element of a vector -/
def nth {α : Type u_1} {n : ℕ} (i : fin2 n) (v : vector3 α n) : α :=
  v i

/-- Construct a vector from a function on `fin2`. -/
def of_fn {α : Type u_1} {n : ℕ} (f : fin2 n → α) : vector3 α n :=
  f

/-- Get the head of a nonempty vector. -/
def head {α : Type u_1} {n : ℕ} (v : vector3 α (Nat.succ n)) : α :=
  v fin2.fz

/-- Get the tail of a nonempty vector. -/
def tail {α : Type u_1} {n : ℕ} (v : vector3 α (Nat.succ n)) : vector3 α n :=
  fun (i : fin2 n) => v (fin2.fs i)

theorem eq_nil {α : Type u_1} (v : vector3 α 0) : v = nil := sorry

theorem cons_head_tail {α : Type u_1} {n : ℕ} (v : vector3 α (Nat.succ n)) : head v :: tail v = v :=
  funext fun (i : fin2 (Nat.succ n)) => fin2.cases' rfl (fun (_x : fin2 n) => rfl) i

def nil_elim {α : Type u_1} {C : vector3 α 0 → Sort u} (H : C nil) (v : vector3 α 0) : C v :=
  eq.mpr sorry H

def cons_elim {α : Type u_1} {n : ℕ} {C : vector3 α (Nat.succ n) → Sort u} (H : (a : α) → (t : vector3 α n) → C (a :: t)) (v : vector3 α (Nat.succ n)) : C v :=
  eq.mpr sorry (H (head v) (tail v))

@[simp] theorem cons_elim_cons {α : Type u_1} {n : ℕ} {C : vector3 α (Nat.succ n) → Sort u_2} {H : (a : α) → (t : vector3 α n) → C (a :: t)} {a : α} {t : vector3 α n} : cons_elim H (a :: t) = H a t :=
  rfl

protected def rec_on {α : Type u_1} {C : {n : ℕ} → vector3 α n → Sort u} {n : ℕ} (v : vector3 α n) (H0 : C nil) (Hs : {n : ℕ} → (a : α) → (w : vector3 α n) → C w → C (a :: w)) : C v :=
  nat.rec_on n (fun (v : vector3 α 0) => nil_elim H0 v)
    (fun (n : ℕ) (IH : (_a : vector3 α n) → C _a) (v : vector3 α (Nat.succ n)) =>
      cons_elim (fun (a : α) (t : vector3 α n) => Hs a t (IH t)) v)
    v

@[simp] theorem rec_on_nil {α : Type u_1} {C : {n : ℕ} → vector3 α n → Sort u_2} {H0 : C nil} {Hs : {n : ℕ} → (a : α) → (w : vector3 α n) → C w → C (a :: w)} : vector3.rec_on nil H0 Hs = H0 :=
  rfl

@[simp] theorem rec_on_cons {α : Type u_1} {C : {n : ℕ} → vector3 α n → Sort u_2} {H0 : C nil} {Hs : {n : ℕ} → (a : α) → (w : vector3 α n) → C w → C (a :: w)} {n : ℕ} {a : α} {v : vector3 α n} : vector3.rec_on (a :: v) H0 Hs = Hs a v (vector3.rec_on v H0 Hs) :=
  rfl

/-- Append two vectors -/
def append {α : Type u_1} {m : ℕ} (v : vector3 α m) {n : ℕ} (w : vector3 α n) : vector3 α (n + m) :=
  nat.rec_on m (fun (_x : vector3 α 0) => w)
    (fun (m : ℕ) (IH : vector3 α m → vector3 α (n + m)) (v : vector3 α (Nat.succ m)) =>
      cons_elim (fun (a : α) (t : vector3 α m) => fin2.cases' a (IH t)) v)
    v

@[simp] theorem append_nil {α : Type u_1} {n : ℕ} (w : vector3 α n) : append nil w = w :=
  rfl

@[simp] theorem append_cons {α : Type u_1} (a : α) {m : ℕ} (v : vector3 α m) {n : ℕ} (w : vector3 α n) : append (a :: v) w = a :: append v w :=
  rfl

@[simp] theorem append_left {α : Type u_1} {m : ℕ} (i : fin2 m) (v : vector3 α m) {n : ℕ} (w : vector3 α n) : append v w (fin2.left n i) = v i := sorry

@[simp] theorem append_add {α : Type u_1} {m : ℕ} (v : vector3 α m) {n : ℕ} (w : vector3 α n) (i : fin2 n) : append v w (fin2.add i m) = w i := sorry

/-- Insert `a` into `v` at index `i`. -/
def insert {α : Type u_1} (a : α) {n : ℕ} (v : vector3 α n) (i : fin2 (Nat.succ n)) : vector3 α (Nat.succ n) :=
  fun (j : fin2 (Nat.succ n)) => cons a v (fin2.insert_perm i j)

@[simp] theorem insert_fz {α : Type u_1} (a : α) {n : ℕ} (v : vector3 α n) : insert a v fin2.fz = a :: v := sorry

@[simp] theorem insert_fs {α : Type u_1} (a : α) {n : ℕ} (b : α) (v : vector3 α n) (i : fin2 (Nat.succ n)) : insert a (b :: v) (fin2.fs i) = b :: insert a v i := sorry

theorem append_insert {α : Type u_1} (a : α) {k : ℕ} (t : vector3 α k) {n : ℕ} (v : vector3 α n) (i : fin2 (Nat.succ n)) (e : Nat.succ n + k = Nat.succ (n + k)) : insert a (append t v) (eq.rec_on e (fin2.add i k)) = eq.rec_on e (append t (insert a v i)) := sorry

end vector3


/-- "Curried" exists, i.e. ∃ x1 ... xn, f [x1, ..., xn] -/
def vector_ex {α : Type u_1} (k : ℕ) : (vector3 α k → Prop) → Prop :=
  sorry

/-- "Curried" forall, i.e. ∀ x1 ... xn, f [x1, ..., xn] -/
def vector_all {α : Type u_1} (k : ℕ) : (vector3 α k → Prop) → Prop :=
  sorry

theorem exists_vector_zero {α : Type u_1} (f : vector3 α 0 → Prop) : Exists f ↔ f vector3.nil := sorry

theorem exists_vector_succ {α : Type u_1} {n : ℕ} (f : vector3 α (Nat.succ n) → Prop) : Exists f ↔ ∃ (x : α), ∃ (v : vector3 α n), f (x :: v) := sorry

theorem vector_ex_iff_exists {α : Type u_1} {n : ℕ} (f : vector3 α n → Prop) : vector_ex n f ↔ Exists f := sorry

theorem vector_all_iff_forall {α : Type u_1} {n : ℕ} (f : vector3 α n → Prop) : vector_all n f ↔ ∀ (v : vector3 α n), f v := sorry

/-- `vector_allp p v` is equivalent to `∀ i, p (v i)`, but unfolds directly to a conjunction,
  i.e. `vector_allp p [0, 1, 2] = p 0 ∧ p 1 ∧ p 2`. -/
def vector_allp {α : Type u_1} (p : α → Prop) {n : ℕ} (v : vector3 α n) :=
  vector3.rec_on v True
    fun (n : ℕ) (a : α) (v : vector3 α n) (IH : Prop) =>
      vector3.rec_on v (p a) fun (n : ℕ) (b : α) (v' : vector3 α n) (_x : Prop) => p a ∧ IH

@[simp] theorem vector_allp_nil {α : Type u_1} (p : α → Prop) : vector_allp p vector3.nil = True :=
  rfl

@[simp] theorem vector_allp_singleton {α : Type u_1} (p : α → Prop) (x : α) : vector_allp p (x :: vector3.nil) = p x :=
  rfl

@[simp] theorem vector_allp_cons {α : Type u_1} (p : α → Prop) {n : ℕ} (x : α) (v : vector3 α n) : vector_allp p (x :: v) ↔ p x ∧ vector_allp p v :=
  vector3.rec_on v (iff.symm (and_true (vector_allp p (x :: vector3.nil))))
    fun (n : ℕ) (a : α) (v : vector3 α n) (IH : vector_allp p (x :: v) ↔ p x ∧ vector_allp p v) => iff.rfl

theorem vector_allp_iff_forall {α : Type u_1} (p : α → Prop) {n : ℕ} (v : vector3 α n) : vector_allp p v ↔ ∀ (i : fin2 n), p (v i) := sorry

theorem vector_allp.imp {α : Type u_1} {p : α → Prop} {q : α → Prop} (h : ∀ (x : α), p x → q x) {n : ℕ} {v : vector3 α n} (al : vector_allp p v) : vector_allp q v :=
  iff.mpr (vector_allp_iff_forall q v) fun (i : fin2 n) => h (v i) (iff.mp (vector_allp_iff_forall p v) al i)

/-- `list_all p l` is equivalent to `∀ a ∈ l, p a`, but unfolds directly to a conjunction,
  i.e. `list_all p [0, 1, 2] = p 0 ∧ p 1 ∧ p 2`. -/
@[simp] def list_all {α : Type u_1} (p : α → Prop) : List α → Prop :=
  sorry

@[simp] theorem list_all_cons {α : Type u_1} (p : α → Prop) (x : α) (l : List α) : list_all p (x :: l) ↔ p x ∧ list_all p l :=
  list.cases_on l (idRhs (list_all p [x] ↔ list_all p [x] ∧ True) (iff.symm (and_true (list_all p [x]))))
    fun (l_hd : α) (l_tl : List α) => idRhs (list_all p (x :: l_hd :: l_tl) ↔ list_all p (x :: l_hd :: l_tl)) iff.rfl

theorem list_all_iff_forall {α : Type u_1} (p : α → Prop) (l : List α) : list_all p l ↔ ∀ (x : α), x ∈ l → p x := sorry

theorem list_all.imp {α : Type u_1} {p : α → Prop} {q : α → Prop} (h : ∀ (x : α), p x → q x) {l : List α} : list_all p l → list_all q l := sorry

@[simp] theorem list_all_map {α : Type u_1} {β : Type u_2} {p : β → Prop} (f : α → β) {l : List α} : list_all p (list.map f l) ↔ list_all (p ∘ f) l := sorry

theorem list_all_congr {α : Type u_1} {p : α → Prop} {q : α → Prop} (h : ∀ (x : α), p x ↔ q x) {l : List α} : list_all p l ↔ list_all q l :=
  { mp := list_all.imp fun (x : α) => iff.mp (h x), mpr := list_all.imp fun (x : α) => iff.mpr (h x) }

protected instance decidable_list_all {α : Type u_1} (p : α → Prop) [decidable_pred p] (l : List α) : Decidable (list_all p l) :=
  decidable_of_decidable_of_iff (list.decidable_ball (fun (x : α) => p x) l) sorry

/- poly -/

/-- A predicate asserting that a function is a multivariate integer polynomial.
  (We are being a bit lazy here by allowing many representations for multiplication,
  rather than only allowing monomials and addition, but the definition is equivalent
  and this is easier to use.) -/
inductive is_poly {α : Sort u_1} : ((α → ℕ) → ℤ) → Prop
where
| proj : ∀ (i : α), is_poly fun (x : α → ℕ) => ↑(x i)
| const : ∀ (n : ℤ), is_poly fun (x : α → ℕ) => n
| sub : ∀ {f g : (α → ℕ) → ℤ}, is_poly f → is_poly g → is_poly fun (x : α → ℕ) => f x - g x
| mul : ∀ {f g : (α → ℕ) → ℤ}, is_poly f → is_poly g → is_poly fun (x : α → ℕ) => f x * g x

/-- The type of multivariate integer polynomials -/
def poly (α : Type u) :=
  Subtype fun (f : (α → ℕ) → ℤ) => is_poly f

namespace poly


protected instance has_coe_to_fun {α : Type u} : has_coe_to_fun (poly α) :=
  has_coe_to_fun.mk (fun (f : poly α) => (α → ℕ) → ℤ) fun (f : poly α) => subtype.val f

/-- The underlying function of a `poly` is a polynomial -/
theorem isp {α : Type u} (f : poly α) : is_poly ⇑f :=
  subtype.property f

/-- Extensionality for `poly α` -/
theorem ext {α : Type u} {f : poly α} {g : poly α} (e : ∀ (x : α → ℕ), coe_fn f x = coe_fn g x) : f = g :=
  subtype.eq (funext e)

/-- Construct a `poly` given an extensionally equivalent `poly`. -/
def subst {α : Type u} (f : poly α) (g : (α → ℕ) → ℤ) (e : ∀ (x : α → ℕ), coe_fn f x = g x) : poly α :=
  { val := g, property := sorry }

@[simp] theorem subst_eval {α : Type u} (f : poly α) (g : (α → ℕ) → ℤ) (e : ∀ (x : α → ℕ), coe_fn f x = g x) (x : α → ℕ) : coe_fn (subst f g e) x = g x :=
  rfl

/-- The `i`th projection function, `x_i`. -/
def proj {α : Type u} (i : α) : poly α :=
  { val := fun (x : α → ℕ) => ↑(x i), property := is_poly.proj i }

@[simp] theorem proj_eval {α : Type u} (i : α) (x : α → ℕ) : coe_fn (proj i) x = ↑(x i) :=
  rfl

/-- The constant function with value `n : ℤ`. -/
def const {α : Type u} (n : ℤ) : poly α :=
  { val := fun (x : α → ℕ) => n, property := is_poly.const n }

@[simp] theorem const_eval {α : Type u} (n : ℤ) (x : α → ℕ) : coe_fn (const n) x = n :=
  rfl

/-- The zero polynomial -/
def zero {α : Type u} : poly α :=
  const 0

protected instance has_zero {α : Type u} : HasZero (poly α) :=
  { zero := zero }

@[simp] theorem zero_eval {α : Type u} (x : α → ℕ) : coe_fn 0 x = 0 :=
  rfl

/-- The zero polynomial -/
def one {α : Type u} : poly α :=
  const 1

protected instance has_one {α : Type u} : HasOne (poly α) :=
  { one := one }

@[simp] theorem one_eval {α : Type u} (x : α → ℕ) : coe_fn 1 x = 1 :=
  rfl

/-- Subtraction of polynomials -/
def sub {α : Type u} : poly α → poly α → poly α :=
  sorry

protected instance has_sub {α : Type u} : Sub (poly α) :=
  { sub := sub }

@[simp] theorem sub_eval {α : Type u} (f : poly α) (g : poly α) (x : α → ℕ) : coe_fn (f - g) x = coe_fn f x - coe_fn g x := sorry

/-- Negation of a polynomial -/
def neg {α : Type u} (f : poly α) : poly α :=
  0 - f

protected instance has_neg {α : Type u} : Neg (poly α) :=
  { neg := neg }

@[simp] theorem neg_eval {α : Type u} (f : poly α) (x : α → ℕ) : coe_fn (-f) x = -coe_fn f x := sorry

/-- Addition of polynomials -/
def add {α : Type u} : poly α → poly α → poly α :=
  sorry

protected instance has_add {α : Type u} : Add (poly α) :=
  { add := add }

@[simp] theorem add_eval {α : Type u} (f : poly α) (g : poly α) (x : α → ℕ) : coe_fn (f + g) x = coe_fn f x + coe_fn g x := sorry

/-- Multiplication of polynomials -/
def mul {α : Type u} : poly α → poly α → poly α :=
  sorry

protected instance has_mul {α : Type u} : Mul (poly α) :=
  { mul := mul }

@[simp] theorem mul_eval {α : Type u} (f : poly α) (g : poly α) (x : α → ℕ) : coe_fn (f * g) x = coe_fn f x * coe_fn g x := sorry

protected instance comm_ring {α : Type u} : comm_ring (poly α) :=
  comm_ring.mk Add.add sorry 0 sorry sorry Neg.neg Sub.sub sorry sorry Mul.mul sorry 1 sorry sorry sorry sorry sorry

theorem induction {α : Type u} {C : poly α → Prop} (H1 : ∀ (i : α), C (proj i)) (H2 : ∀ (n : ℤ), C (const n)) (H3 : ∀ (f g : poly α), C f → C g → C (f - g)) (H4 : ∀ (f g : poly α), C f → C g → C (f * g)) (f : poly α) : C f := sorry

/-- The sum of squares of a list of polynomials. This is relevant for
  Diophantine equations, because it means that a list of equations
  can be encoded as a single equation: `x = 0 ∧ y = 0 ∧ z = 0` is
  equivalent to `x^2 + y^2 + z^2 = 0`. -/
def sumsq {α : Type u} : List (poly α) → poly α :=
  sorry

theorem sumsq_nonneg {α : Type u} (x : α → ℕ) (l : List (poly α)) : 0 ≤ coe_fn (sumsq l) x := sorry

theorem sumsq_eq_zero {α : Type u} (x : α → ℕ) (l : List (poly α)) : coe_fn (sumsq l) x = 0 ↔ list_all (fun (a : poly α) => coe_fn a x = 0) l := sorry

/-- Map the index set of variables, replacing `x_i` with `x_(f i)`. -/
def remap {α : Type u_1} {β : Type u_2} (f : α → β) (g : poly α) : poly β :=
  { val := fun (v : β → ℕ) => coe_fn g (v ∘ f), property := sorry }

@[simp] theorem remap_eval {α : Type u_1} {β : Type u_2} (f : α → β) (g : poly α) (v : β → ℕ) : coe_fn (remap f g) v = coe_fn g (v ∘ f) :=
  rfl

end poly


namespace sum


/-- combine two functions into a function on the disjoint union -/
def join {α : Type u_1} {β : Type u_2} {γ : Sort u_3} (f : α → γ) (g : β → γ) : α ⊕ β → γ :=
  sum.rec f g

end sum


namespace option


/-- Functions from `option` can be combined similarly to `vector.cons` -/
def cons {α : Type u_1} {β : Sort u_2} (a : β) (v : α → β) : Option α → β :=
  Option.rec a v

infixr:67 " :: " => Mathlib.option.cons

@[simp] theorem cons_head_tail {α : Type u_1} {β : Sort u_2} (v : Option α → β) : v none :: v ∘ some = v := sorry

end option


/- dioph -/

/-- A set `S ⊆ ℕ^α` is diophantine if there exists a polynomial on
  `α ⊕ β` such that `v ∈ S` iff there exists `t : ℕ^β` with `p (v, t) = 0`. -/
def dioph {α : Type u} (S : set (α → ℕ)) :=
  Exists fun {β : Type u} => ∃ (p : poly (α ⊕ β)), ∀ (v : α → ℕ), S v ↔ ∃ (t : β → ℕ), coe_fn p (sum.join v t) = 0

namespace dioph


theorem ext {α : Type u} {S : set (α → ℕ)} {S' : set (α → ℕ)} (d : dioph S) (H : ∀ (v : α → ℕ), S v ↔ S' v) : dioph S' :=
  Eq._oldrec d ((fun (this : S = S') => this) (set.ext H))

theorem of_no_dummies {α : Type u} (S : set (α → ℕ)) (p : poly α) (h : ∀ (v : α → ℕ), S v ↔ coe_fn p v = 0) : dioph S := sorry

theorem inject_dummies_lem {α : Type u} {β : Type u} {γ : Type u} (f : β → γ) (g : γ → Option β) (inv : ∀ (x : β), g (f x) = some x) (p : poly (α ⊕ β)) (v : α → ℕ) : (∃ (t : β → ℕ), coe_fn p (sum.join v t) = 0) ↔
  ∃ (t : γ → ℕ), coe_fn (poly.remap (sum.join sum.inl (sum.inr ∘ f)) p) (sum.join v t) = 0 := sorry

theorem inject_dummies {α : Type u} {β : Type u} {γ : Type u} {S : set (α → ℕ)} (f : β → γ) (g : γ → Option β) (inv : ∀ (x : β), g (f x) = some x) (p : poly (α ⊕ β)) (h : ∀ (v : α → ℕ), S v ↔ ∃ (t : β → ℕ), coe_fn p (sum.join v t) = 0) : ∃ (q : poly (α ⊕ γ)), ∀ (v : α → ℕ), S v ↔ ∃ (t : γ → ℕ), coe_fn q (sum.join v t) = 0 :=
  Exists.intro (poly.remap (sum.join sum.inl (sum.inr ∘ f)) p)
    fun (v : α → ℕ) => iff.trans (h v) (inject_dummies_lem f g inv p v)

theorem reindex_dioph {α : Type u} {β : Type u} {S : set (α → ℕ)} (d : dioph S) (f : α → β) : dioph fun (v : β → ℕ) => S (v ∘ f) := sorry

theorem dioph_list_all {α : Type u} (l : List (set (α → ℕ))) (d : list_all dioph l) : dioph fun (v : α → ℕ) => list_all (fun (S : set (α → ℕ)) => S v) l := sorry

theorem and_dioph {α : Type u} {S : set (α → ℕ)} {S' : set (α → ℕ)} (d : dioph S) (d' : dioph S') : dioph fun (v : α → ℕ) => S v ∧ S' v :=
  dioph_list_all [S, S'] { left := d, right := d' }

theorem or_dioph {α : Type u} {S : set (α → ℕ)} {S' : set (α → ℕ)} (d : dioph S) (d' : dioph S') : dioph fun (v : α → ℕ) => S v ∨ S' v := sorry

/-- A partial function is Diophantine if its graph is Diophantine. -/
def dioph_pfun {α : Type u} (f : (α → ℕ) →. ℕ) :=
  dioph fun (v : Option α → ℕ) => pfun.graph f (v ∘ some, v none)

/-- A function is Diophantine if its graph is Diophantine. -/
def dioph_fn {α : Type u} (f : (α → ℕ) → ℕ) :=
  dioph fun (v : Option α → ℕ) => f (v ∘ some) = v none

theorem reindex_dioph_fn {α : Type u} {β : Type u} {f : (α → ℕ) → ℕ} (d : dioph_fn f) (g : α → β) : dioph_fn fun (v : β → ℕ) => f (v ∘ g) :=
  reindex_dioph d (Functor.map g)

theorem ex_dioph {α : Type u} {β : Type u} {S : set (α ⊕ β → ℕ)} : dioph S → dioph fun (v : α → ℕ) => ∃ (x : β → ℕ), S (sum.join v x) := sorry

theorem ex1_dioph {α : Type u} {S : set (Option α → ℕ)} : dioph S → dioph fun (v : α → ℕ) => ∃ (x : ℕ), S (x :: v) := sorry

theorem dom_dioph {α : Type u} {f : (α → ℕ) →. ℕ} (d : dioph_pfun f) : dioph (pfun.dom f) :=
  cast (congr_arg dioph (set.ext fun (v : α → ℕ) => iff.symm (pfun.dom_iff_graph f v))) (ex1_dioph d)

theorem dioph_fn_iff_pfun {α : Type u} (f : (α → ℕ) → ℕ) : dioph_fn f = dioph_pfun ↑f :=
  congr_arg dioph (set.ext fun (v : Option α → ℕ) => iff.symm pfun.lift_graph)

theorem abs_poly_dioph {α : Type u} (p : poly α) : dioph_fn fun (v : α → ℕ) => int.nat_abs (coe_fn p v) :=
  of_no_dummies (fun (v : Option α → ℕ) => (fun (v : α → ℕ) => int.nat_abs (coe_fn p v)) (v ∘ some) = v none)
    ((poly.remap some p - poly.proj none) * (poly.remap some p + poly.proj none))
    fun (v : Option α → ℕ) => int.eq_nat_abs_iff_mul (coe_fn p (v ∘ some)) (v none)

theorem proj_dioph {α : Type u} (i : α) : dioph_fn fun (v : α → ℕ) => v i :=
  abs_poly_dioph (poly.proj i)

theorem dioph_pfun_comp1 {α : Type u} {S : set (Option α → ℕ)} (d : dioph S) {f : (α → ℕ) →. ℕ} (df : dioph_pfun f) : dioph fun (v : α → ℕ) => ∃ (h : pfun.dom f v), S (pfun.fn f v h :: v) := sorry

theorem dioph_fn_comp1 {α : Type u} {S : set (Option α → ℕ)} (d : dioph S) {f : (α → ℕ) → ℕ} (df : dioph_fn f) : dioph fun (v : α → ℕ) => S (f v :: v) := sorry

theorem dioph_fn_vec_comp1 {n : ℕ} {S : set (vector3 ℕ (Nat.succ n))} (d : dioph S) {f : vector3 ℕ n → ℕ} (df : dioph_fn f) : dioph fun (v : vector3 ℕ n) => S (f v :: v) := sorry

theorem vec_ex1_dioph (n : ℕ) {S : set (vector3 ℕ (Nat.succ n))} (d : dioph S) : dioph fun (v : vector3 ℕ n) => ∃ (x : ℕ), S (x :: v) := sorry

theorem dioph_fn_vec {n : ℕ} (f : vector3 ℕ n → ℕ) : dioph_fn f ↔ dioph fun (v : vector3 ℕ (Nat.succ n)) => f (v ∘ fin2.fs) = v fin2.fz :=
  { mp := fun (h : dioph_fn f) => reindex_dioph h (fin2.fz :: fin2.fs),
    mpr :=
      fun (h : dioph fun (v : vector3 ℕ (Nat.succ n)) => f (v ∘ fin2.fs) = v fin2.fz) => reindex_dioph h (none :: some) }

theorem dioph_pfun_vec {n : ℕ} (f : vector3 ℕ n →. ℕ) : dioph_pfun f ↔ dioph fun (v : vector3 ℕ (Nat.succ n)) => pfun.graph f (v ∘ fin2.fs, v fin2.fz) := sorry

theorem dioph_fn_compn {α : Type} {n : ℕ} {S : set (α ⊕ fin2 n → ℕ)} (d : dioph S) {f : vector3 ((α → ℕ) → ℕ) n} (df : vector_allp dioph_fn f) : dioph fun (v : α → ℕ) => S (sum.join v fun (i : fin2 n) => f i v) := sorry

theorem dioph_comp {α : Type} {n : ℕ} {S : set (vector3 ℕ n)} (d : dioph S) (f : vector3 ((α → ℕ) → ℕ) n) (df : vector_allp dioph_fn f) : dioph fun (v : α → ℕ) => S fun (i : fin2 n) => f i v :=
  dioph_fn_compn (reindex_dioph d sum.inr) df

theorem dioph_fn_comp {α : Type} {n : ℕ} {f : vector3 ℕ n → ℕ} (df : dioph_fn f) (g : vector3 ((α → ℕ) → ℕ) n) (dg : vector_allp dioph_fn g) : dioph_fn fun (v : α → ℕ) => f fun (i : fin2 n) => g i v := sorry

theorem proj_dioph_of_nat {n : ℕ} (m : ℕ) [fin2.is_lt m n] : dioph_fn fun (v : vector3 ℕ n) => v (fin2.of_nat' m) :=
  proj_dioph (fin2.of_nat' m)

theorem const_dioph {α : Type} (n : ℕ) : dioph_fn (function.const (α → ℕ) n) :=
  abs_poly_dioph (poly.const ↑n)

theorem dioph_comp2 {α : Type} {f : (α → ℕ) → ℕ} {g : (α → ℕ) → ℕ} (df : dioph_fn f) (dg : dioph_fn g) {S : ℕ → ℕ → Prop} (d : dioph fun (v : vector3 ℕ (bit0 1)) => S (v (fin2.of_nat' 0)) (v (fin2.of_nat' 1))) : dioph fun (v : α → ℕ) => S (f v) (g v) :=
  dioph_comp d (f :: g :: vector3.nil) { left := df, right := dg }

theorem dioph_fn_comp2 {α : Type} {f : (α → ℕ) → ℕ} {g : (α → ℕ) → ℕ} (df : dioph_fn f) (dg : dioph_fn g) {h : ℕ → ℕ → ℕ} (d : dioph_fn fun (v : vector3 ℕ (bit0 1)) => h (v (fin2.of_nat' 0)) (v (fin2.of_nat' 1))) : dioph_fn fun (v : α → ℕ) => h (f v) (g v) :=
  dioph_fn_comp d (f :: g :: vector3.nil) { left := df, right := dg }

theorem eq_dioph {α : Type} {f : (α → ℕ) → ℕ} {g : (α → ℕ) → ℕ} (df : dioph_fn f) (dg : dioph_fn g) : dioph fun (v : α → ℕ) => f v = g v := sorry

theorem add_dioph {α : Type} {f : (α → ℕ) → ℕ} {g : (α → ℕ) → ℕ} (df : dioph_fn f) (dg : dioph_fn g) : dioph_fn fun (v : α → ℕ) => f v + g v :=
  dioph_fn_comp2 df dg (abs_poly_dioph (poly.proj (fin2.of_nat' 0) + poly.proj (fin2.of_nat' 1)))

theorem mul_dioph {α : Type} {f : (α → ℕ) → ℕ} {g : (α → ℕ) → ℕ} (df : dioph_fn f) (dg : dioph_fn g) : dioph_fn fun (v : α → ℕ) => f v * g v :=
  dioph_fn_comp2 df dg (abs_poly_dioph (poly.proj (fin2.of_nat' 0) * poly.proj (fin2.of_nat' 1)))

theorem le_dioph {α : Type} {f : (α → ℕ) → ℕ} {g : (α → ℕ) → ℕ} (df : dioph_fn f) (dg : dioph_fn g) : dioph fun (v : α → ℕ) => f v ≤ g v := sorry

theorem lt_dioph {α : Type} {f : (α → ℕ) → ℕ} {g : (α → ℕ) → ℕ} (df : dioph_fn f) (dg : dioph_fn g) : dioph fun (v : α → ℕ) => f v < g v :=
  le_dioph (add_dioph df (const_dioph 1)) dg

theorem ne_dioph {α : Type} {f : (α → ℕ) → ℕ} {g : (α → ℕ) → ℕ} (df : dioph_fn f) (dg : dioph_fn g) : dioph fun (v : α → ℕ) => f v ≠ g v :=
  ext (or_dioph (lt_dioph df dg) (lt_dioph dg df)) fun (v : α → ℕ) => iff.symm ne_iff_lt_or_gt

theorem sub_dioph {α : Type} {f : (α → ℕ) → ℕ} {g : (α → ℕ) → ℕ} (df : dioph_fn f) (dg : dioph_fn g) : dioph_fn fun (v : α → ℕ) => f v - g v := sorry

theorem dvd_dioph {α : Type} {f : (α → ℕ) → ℕ} {g : (α → ℕ) → ℕ} (df : dioph_fn f) (dg : dioph_fn g) : dioph fun (v : α → ℕ) => f v ∣ g v := sorry

theorem mod_dioph {α : Type} {f : (α → ℕ) → ℕ} {g : (α → ℕ) → ℕ} (df : dioph_fn f) (dg : dioph_fn g) : dioph_fn fun (v : α → ℕ) => f v % g v := sorry

theorem modeq_dioph {α : Type} {f : (α → ℕ) → ℕ} {g : (α → ℕ) → ℕ} (df : dioph_fn f) (dg : dioph_fn g) {h : (α → ℕ) → ℕ} (dh : dioph_fn h) : dioph fun (v : α → ℕ) => nat.modeq (h v) (f v) (g v) :=
  eq_dioph (mod_dioph df dh) (mod_dioph dg dh)

theorem div_dioph {α : Type} {f : (α → ℕ) → ℕ} {g : (α → ℕ) → ℕ} (df : dioph_fn f) (dg : dioph_fn g) : dioph_fn fun (v : α → ℕ) => f v / g v := sorry

theorem pell_dioph : dioph
  fun (v : vector3 ℕ (bit0 (bit0 1))) =>
    ∃ (h : 1 < v (fin2.of_nat' 0)),
      pell.xn h (v (fin2.of_nat' 1)) = v (fin2.of_nat' (bit0 1)) ∧
        pell.yn h (v (fin2.of_nat' 1)) = v (fin2.of_nat' (bit1 1)) := sorry

theorem xn_dioph : dioph_pfun
  fun (v : vector3 ℕ (bit0 1)) =>
    roption.mk (1 < v (fin2.of_nat' 0)) fun (h : 1 < v (fin2.of_nat' 0)) => pell.xn h (v (fin2.of_nat' 1)) := sorry

theorem pow_dioph {α : Type} {f : (α → ℕ) → ℕ} {g : (α → ℕ) → ℕ} (df : dioph_fn f) (dg : dioph_fn g) : dioph_fn fun (v : α → ℕ) => f v ^ g v := sorry

