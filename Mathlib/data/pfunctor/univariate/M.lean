/-
Copyright (c) 2017 Simon Hudon All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.pfunctor.univariate.basic
import Mathlib.PostPort

universes u l w u_1 

namespace Mathlib

/-!
# M-types

M types are potentially infinite tree-like structures. They are defined
as the greatest fixpoint of a polynomial functor.
-/

namespace pfunctor


namespace approx


/-- `cofix_a F n` is an `n` level approximation of a M-type -/
inductive cofix_a (F : pfunctor) : ℕ → Type u
where
| continue : cofix_a F 0
| intro : {n : ℕ} → (a : A F) → (B F a → cofix_a F n) → cofix_a F (Nat.succ n)

/-- default inhabitant of `cofix_a` -/
protected def cofix_a.default (F : pfunctor) [Inhabited (A F)] (n : ℕ) : cofix_a F n :=
  sorry

protected instance cofix_a.inhabited (F : pfunctor) [Inhabited (A F)] {n : ℕ} : Inhabited (cofix_a F n) :=
  { default := cofix_a.default F n }

theorem cofix_a_eq_zero (F : pfunctor) (x : cofix_a F 0) (y : cofix_a F 0) : x = y := sorry

/--
The label of the root of the tree for a non-trivial
approximation of the cofix of a pfunctor.
-/
def head' {F : pfunctor} {n : ℕ} : cofix_a F (Nat.succ n) → A F :=
  sorry

/-- for a non-trivial approximation, return all the subtrees of the root -/
def children' {F : pfunctor} {n : ℕ} (x : cofix_a F (Nat.succ n)) : B F (head' x) → cofix_a F n :=
  sorry

theorem approx_eta {F : pfunctor} {n : ℕ} (x : cofix_a F (n + 1)) : x = cofix_a.intro (head' x) (children' x) := sorry

/-- Relation between two approximations of the cofix of a pfunctor that state they both contain the same
data until one of them is truncated -/
inductive agree {F : pfunctor} : {n : ℕ} → cofix_a F n → cofix_a F (n + 1) → Prop
where
| continue : ∀ (x : cofix_a F 0) (y : cofix_a F 1), agree x y
| intro : ∀ {n : ℕ} {a : A F} (x : B F a → cofix_a F n) (x' : B F a → cofix_a F (n + 1)),
  (∀ (i : B F a), agree (x i) (x' i)) → agree (cofix_a.intro a x) (cofix_a.intro a x')

/--
Given an infinite series of approximations `approx`,
`all_agree approx` states that they are all consistent with each other.
-/
def all_agree {F : pfunctor} (x : (n : ℕ) → cofix_a F n)  :=
  ∀ (n : ℕ), agree (x n) (x (Nat.succ n))

@[simp] theorem agree_trival {F : pfunctor} {x : cofix_a F 0} {y : cofix_a F 1} : agree x y :=
  agree.continue x y

theorem agree_children {F : pfunctor} {n : ℕ} (x : cofix_a F (Nat.succ n)) (y : cofix_a F (Nat.succ n + 1)) {i : B F (head' x)} {j : B F (head' y)} (h₀ : i == j) (h₁ : agree x y) : agree (children' x i) (children' y j) := sorry

/-- `truncate a` turns `a` into a more limited approximation -/
def truncate {F : pfunctor} {n : ℕ} : cofix_a F (n + 1) → cofix_a F n :=
  sorry

theorem truncate_eq_of_agree {F : pfunctor} {n : ℕ} (x : cofix_a F n) (y : cofix_a F (Nat.succ n)) (h : agree x y) : truncate y = x := sorry

/-- `s_corec f i n` creates an approximation of height `n`
of the final coalgebra of `f` -/
def s_corec {F : pfunctor} {X : Type w} (f : X → obj F X) (i : X) (n : ℕ) : cofix_a F n :=
  sorry

theorem P_corec {F : pfunctor} {X : Type w} (f : X → obj F X) (i : X) (n : ℕ) : agree (s_corec f i n) (s_corec f i (Nat.succ n)) := sorry

/-- `path F` provides indices to access internal nodes in `corec F` -/
def path (F : pfunctor)  :=
  List (Idx F)

protected instance path.inhabited {F : pfunctor} : Inhabited (path F) :=
  { default := [] }

protected instance cofix_a.subsingleton {F : pfunctor} : subsingleton (cofix_a F 0) :=
  subsingleton.intro
    fun (a b : cofix_a F 0) =>
      cofix_a.cases_on a
        (fun (a_1 : 0 = 0) (H_2 : a == cofix_a.continue) =>
          Eq._oldrec
            (cofix_a.cases_on b
              (fun (a : 0 = 0) (H_2 : b == cofix_a.continue) =>
                Eq._oldrec (Eq.refl cofix_a.continue) (Eq.symm (eq_of_heq H_2)))
              (fun {b_n : ℕ} (b_a : A F) (b_ᾰ : B F b_a → cofix_a F b_n) (a : 0 = Nat.succ b_n) => nat.no_confusion a)
              (Eq.refl 0) (HEq.refl b))
            (Eq.symm (eq_of_heq H_2)))
        (fun {a_n : ℕ} (a_a : A F) (a_ᾰ : B F a_a → cofix_a F a_n) (a_1 : 0 = Nat.succ a_n) => nat.no_confusion a_1)
        (Eq.refl 0) (HEq.refl a)

theorem head_succ' {F : pfunctor} (n : ℕ) (m : ℕ) (x : (n : ℕ) → cofix_a F n) (Hconsistent : all_agree x) : head' (x (Nat.succ n)) = head' (x (Nat.succ m)) := sorry

end approx


/-- Internal definition for `M`. It is needed to avoid name clashes
between `M.mk` and `M.cases_on` and the declarations generated for
the structure -/
structure M_intl (F : pfunctor) 
where
  approx : (n : ℕ) → approx.cofix_a F n
  consistent : approx.all_agree approx

/-- For polynomial functor `F`, `M F` is its final coalgebra -/
def M (F : pfunctor)  :=
  M_intl F

theorem M.default_consistent (F : pfunctor) [Inhabited (A F)] (n : ℕ) : approx.agree Inhabited.default Inhabited.default := sorry

protected instance M.inhabited (F : pfunctor) [Inhabited (A F)] : Inhabited (M F) :=
  { default := M_intl.mk (fun (n : ℕ) => Inhabited.default) (M.default_consistent F) }

protected instance M_intl.inhabited (F : pfunctor) [Inhabited (A F)] : Inhabited (M_intl F) :=
  (fun (this : Inhabited (M F)) => this) (M.inhabited F)

namespace M


theorem ext' (F : pfunctor) (x : M F) (y : M F) (H : ∀ (i : ℕ), M_intl.approx x i = M_intl.approx y i) : x = y := sorry

/-- Corecursor for the M-type defined by `F`. -/
protected def corec {F : pfunctor} {X : Type u_1} (f : X → obj F X) (i : X) : M F :=
  M_intl.mk (approx.s_corec f i) (approx.P_corec f i)

/-- given a tree generated by `F`, `head` gives us the first piece of data
it contains -/
def head {F : pfunctor} (x : M F) : A F :=
  approx.head' (M_intl.approx x 1)

/-- return all the subtrees of the root of a tree `x : M F` -/
def children {F : pfunctor} (x : M F) (i : B F (head x)) : M F :=
  M_intl.mk (fun (n : ℕ) => approx.children' (M_intl.approx x (Nat.succ n)) (cast sorry i)) sorry

/-- select a subtree using a `i : F.Idx` or return an arbitrary tree if
`i` designates no subtree of `x` -/
def ichildren {F : pfunctor} [Inhabited (M F)] [DecidableEq (A F)] (i : Idx F) (x : M F) : M F :=
  dite (sigma.fst i = head x) (fun (H' : sigma.fst i = head x) => children x (cast sorry (sigma.snd i)))
    fun (H' : ¬sigma.fst i = head x) => Inhabited.default

theorem head_succ {F : pfunctor} (n : ℕ) (m : ℕ) (x : M F) : approx.head' (M_intl.approx x (Nat.succ n)) = approx.head' (M_intl.approx x (Nat.succ m)) :=
  approx.head_succ' n m (M_intl.approx x) (M_intl.consistent x)

theorem head_eq_head' {F : pfunctor} (x : M F) (n : ℕ) : head x = approx.head' (M_intl.approx x (n + 1)) := sorry

theorem head'_eq_head {F : pfunctor} (x : M F) (n : ℕ) : approx.head' (M_intl.approx x (n + 1)) = head x := sorry

theorem truncate_approx {F : pfunctor} (x : M F) (n : ℕ) : approx.truncate (M_intl.approx x (n + 1)) = M_intl.approx x n :=
  approx.truncate_eq_of_agree (M_intl.approx x n) (M_intl.approx x (n + 1)) (M_intl.consistent x n)

/-- unfold an M-type -/
def dest {F : pfunctor} : M F → obj F (M F) :=
  sorry

namespace approx


/-- generates the approximations needed for `M.mk` -/
protected def s_mk {F : pfunctor} (x : obj F (M F)) (n : ℕ) : approx.cofix_a F n :=
  sorry

protected theorem P_mk {F : pfunctor} (x : obj F (M F)) : approx.all_agree (approx.s_mk x) := sorry

end approx


/-- constructor for M-types -/
protected def mk {F : pfunctor} (x : obj F (M F)) : M F :=
  M_intl.mk (approx.s_mk x) (approx.P_mk x)

/-- `agree' n` relates two trees of type `M F` that
are the same up to dept `n` -/
inductive agree' {F : pfunctor} : ℕ → M F → M F → Prop
where
| trivial : ∀ (x y : M F), agree' 0 x y
| step : ∀ {n : ℕ} {a : A F} (x y : B F a → M F) {x' y' : M F},
  x' = M.mk (sigma.mk a x) →
    y' = M.mk (sigma.mk a y) → (∀ (i : B F a), agree' n (x i) (y i)) → agree' (Nat.succ n) x' y'

@[simp] theorem dest_mk {F : pfunctor} (x : obj F (M F)) : dest (M.mk x) = x := sorry

@[simp] theorem mk_dest {F : pfunctor} (x : M F) : M.mk (dest x) = x := sorry

theorem mk_inj {F : pfunctor} {x : obj F (M F)} {y : obj F (M F)} (h : M.mk x = M.mk y) : x = y :=
  eq.mpr (id (Eq._oldrec (Eq.refl (x = y)) (Eq.symm (dest_mk x))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (dest (M.mk x) = y)) h))
      (eq.mpr (id (Eq._oldrec (Eq.refl (dest (M.mk y) = y)) (dest_mk y))) (Eq.refl y)))

/-- destructor for M-types -/
protected def cases {F : pfunctor} {r : M F → Sort w} (f : (x : obj F (M F)) → r (M.mk x)) (x : M F) : r x :=
  (fun (this : r (M.mk (dest x))) => eq.mpr sorry this) (f (dest x))

/-- destructor for M-types -/
protected def cases_on {F : pfunctor} {r : M F → Sort w} (x : M F) (f : (x : obj F (M F)) → r (M.mk x)) : r x :=
  M.cases f x

/-- destructor for M-types, similar to `cases_on` but also
gives access directly to the root and subtrees on an M-type -/
protected def cases_on' {F : pfunctor} {r : M F → Sort w} (x : M F) (f : (a : A F) → (f : B F a → M F) → r (M.mk (sigma.mk a f))) : r x :=
  M.cases_on x fun (_x : obj F (M F)) => sorry

theorem approx_mk {F : pfunctor} (a : A F) (f : B F a → M F) (i : ℕ) : M_intl.approx (M.mk (sigma.mk a f)) (Nat.succ i) = approx.cofix_a.intro a fun (j : B F a) => M_intl.approx (f j) i :=
  rfl

@[simp] theorem agree'_refl {F : pfunctor} {n : ℕ} (x : M F) : agree' n x x := sorry

theorem agree_iff_agree' {F : pfunctor} {n : ℕ} (x : M F) (y : M F) : approx.agree (M_intl.approx x n) (M_intl.approx y (n + 1)) ↔ agree' n x y := sorry

@[simp] theorem cases_mk {F : pfunctor} {r : M F → Sort u_1} (x : obj F (M F)) (f : (x : obj F (M F)) → r (M.mk x)) : M.cases f (M.mk x) = f x := sorry

@[simp] theorem cases_on_mk {F : pfunctor} {r : M F → Sort u_1} (x : obj F (M F)) (f : (x : obj F (M F)) → r (M.mk x)) : M.cases_on (M.mk x) f = f x :=
  cases_mk x f

@[simp] theorem cases_on_mk' {F : pfunctor} {r : M F → Sort u_1} {a : A F} (x : B F a → M F) (f : (a : A F) → (f : B F a → M F) → r (M.mk (sigma.mk a f))) : M.cases_on' (M.mk (sigma.mk a x)) f = f a x :=
  cases_mk (sigma.mk a x) fun (_x : obj F (M F)) => cases_on'._match_1 f _x

/-- `is_path p x` tells us if `p` is a valid path through `x` -/
inductive is_path {F : pfunctor} : approx.path F → M F → Prop
where
| nil : ∀ (x : M F), is_path [] x
| cons : ∀ (xs : approx.path F) {a : A F} (x : M F) (f : B F a → M F) (i : B F a),
  x = M.mk (sigma.mk a f) → is_path xs (f i) → is_path (sigma.mk a i :: xs) x

theorem is_path_cons {F : pfunctor} {xs : approx.path F} {a : A F} {a' : A F} {f : B F a → M F} {i : B F a'} (h : is_path (sigma.mk a' i :: xs) (M.mk (sigma.mk a f))) : a = a' := sorry

theorem is_path_cons' {F : pfunctor} {xs : approx.path F} {a : A F} {f : B F a → M F} {i : B F a} (h : is_path (sigma.mk a i :: xs) (M.mk (sigma.mk a f))) : is_path xs (f i) := sorry

/-- follow a path through a value of `M F` and return the subtree
found at the end of the path if it is a valid path for that value and
return a default tree -/
def isubtree {F : pfunctor} [DecidableEq (A F)] [Inhabited (M F)] : approx.path F → M F → M F :=
  sorry

/-- similar to `isubtree` but returns the data at the end of the path instead
of the whole subtree -/
def iselect {F : pfunctor} [DecidableEq (A F)] [Inhabited (M F)] (ps : approx.path F) : M F → A F :=
  fun (x : M F) => head (isubtree ps x)

theorem iselect_eq_default {F : pfunctor} [DecidableEq (A F)] [Inhabited (M F)] (ps : approx.path F) (x : M F) (h : ¬is_path ps x) : iselect ps x = head Inhabited.default := sorry

@[simp] theorem head_mk {F : pfunctor} (x : obj F (M F)) : head (M.mk x) = sigma.fst x := sorry

theorem children_mk {F : pfunctor} {a : A F} (x : B F a → M F) (i : B F (head (M.mk (sigma.mk a x)))) : children (M.mk (sigma.mk a x)) i =
  x
    (cast
      (eq.mpr (id (Eq._oldrec (Eq.refl (B F (head (M.mk (sigma.mk a x))) = B F a)) (head_mk (sigma.mk a x))))
        (Eq.refl (B F (sigma.fst (sigma.mk a x)))))
      i) := sorry

@[simp] theorem ichildren_mk {F : pfunctor} [DecidableEq (A F)] [Inhabited (M F)] (x : obj F (M F)) (i : Idx F) : ichildren i (M.mk x) = obj.iget x i := sorry

@[simp] theorem isubtree_cons {F : pfunctor} [DecidableEq (A F)] [Inhabited (M F)] (ps : approx.path F) {a : A F} (f : B F a → M F) {i : B F a} : isubtree (sigma.mk a i :: ps) (M.mk (sigma.mk a f)) = isubtree ps (f i) := sorry

@[simp] theorem iselect_nil {F : pfunctor} [DecidableEq (A F)] [Inhabited (M F)] {a : A F} (f : B F a → M F) : iselect [] (M.mk (sigma.mk a f)) = a :=
  Eq.refl (iselect [] (M.mk (sigma.mk a f)))

@[simp] theorem iselect_cons {F : pfunctor} [DecidableEq (A F)] [Inhabited (M F)] (ps : approx.path F) {a : A F} (f : B F a → M F) {i : B F a} : iselect (sigma.mk a i :: ps) (M.mk (sigma.mk a f)) = iselect ps (f i) := sorry

theorem corec_def {F : pfunctor} {X : Type u} (f : X → obj F X) (x₀ : X) : M.corec f x₀ = M.mk (M.corec f <$> f x₀) := sorry

theorem ext_aux {F : pfunctor} [Inhabited (M F)] [DecidableEq (A F)] {n : ℕ} (x : M F) (y : M F) (z : M F) (hx : agree' n z x) (hy : agree' n z y) (hrec : ∀ (ps : approx.path F), n = list.length ps → iselect ps x = iselect ps y) : M_intl.approx x (n + 1) = M_intl.approx y (n + 1) := sorry

theorem ext {F : pfunctor} [Inhabited (M F)] (x : M F) (y : M F) (H : ∀ (ps : approx.path F), iselect ps x = iselect ps y) : x = y := sorry

/-- Bisimulation is the standard proof technique for equality between
infinite tree-like structures -/
structure is_bisimulation {F : pfunctor} (R : M F → M F → Prop) 
where
  head : ∀ {a a' : A F} {f : B F a → M F} {f' : B F a' → M F}, R (M.mk (sigma.mk a f)) (M.mk (sigma.mk a' f')) → a = a'
  tail : ∀ {a : A F} {f f' : B F a → M F}, R (M.mk (sigma.mk a f)) (M.mk (sigma.mk a f')) → ∀ (i : B F a), R (f i) (f' i)

theorem nth_of_bisim {F : pfunctor} (R : M F → M F → Prop) [Inhabited (M F)] (bisim : is_bisimulation R) (s₁ : M F) (s₂ : M F) (ps : approx.path F) : R s₁ s₂ →
  is_path ps s₁ ∨ is_path ps s₂ →
    iselect ps s₁ = iselect ps s₂ ∧
      ∃ (a : A F),
        ∃ (f : B F a → M F),
          ∃ (f' : B F a → M F),
            isubtree ps s₁ = M.mk (sigma.mk a f) ∧ isubtree ps s₂ = M.mk (sigma.mk a f') ∧ ∀ (i : B F a), R (f i) (f' i) := sorry

theorem eq_of_bisim {F : pfunctor} (R : M F → M F → Prop) [Nonempty (M F)] (bisim : is_bisimulation R) (s₁ : M F) (s₂ : M F) : R s₁ s₂ → s₁ = s₂ := sorry

/-- corecursor for `M F` with swapped arguments -/
def corec_on {F : pfunctor} {X : Type u_1} (x₀ : X) (f : X → obj F X) : M F :=
  M.corec f x₀

theorem dest_corec {P : pfunctor} {α : Type u} (g : α → obj P α) (x : α) : dest (M.corec g x) = M.corec g <$> g x := sorry

theorem bisim {P : pfunctor} (R : M P → M P → Prop) (h : ∀ (x y : M P),
  R x y →
    ∃ (a : A P),
      ∃ (f : B P a → M P),
        ∃ (f' : B P a → M P), dest x = sigma.mk a f ∧ dest y = sigma.mk a f' ∧ ∀ (i : B P a), R (f i) (f' i)) (x : M P) (y : M P) : R x y → x = y := sorry

theorem bisim' {P : pfunctor} {α : Type u_1} (Q : α → Prop) (u : α → M P) (v : α → M P) (h : ∀ (x : α),
  Q x →
    ∃ (a : A P),
      ∃ (f : B P a → M P),
        ∃ (f' : B P a → M P),
          dest (u x) = sigma.mk a f ∧
            dest (v x) = sigma.mk a f' ∧ ∀ (i : B P a), ∃ (x' : α), Q x' ∧ f i = u x' ∧ f' i = v x') (x : α) : Q x → u x = v x := sorry

-- for the record, show M_bisim follows from _bisim'

theorem bisim_equiv {P : pfunctor} (R : M P → M P → Prop) (h : ∀ (x y : M P),
  R x y →
    ∃ (a : A P),
      ∃ (f : B P a → M P),
        ∃ (f' : B P a → M P), dest x = sigma.mk a f ∧ dest y = sigma.mk a f' ∧ ∀ (i : B P a), R (f i) (f' i)) (x : M P) (y : M P) : R x y → x = y := sorry

theorem corec_unique {P : pfunctor} {α : Type u} (g : α → obj P α) (f : α → M P) (hyp : ∀ (x : α), dest (f x) = f <$> g x) : f = M.corec g := sorry

/-- corecursor where the state of the computation can be sent downstream
in the form of a recursive call -/
def corec₁ {P : pfunctor} {α : Type u} (F : (X : Type u) → (α → X) → α → obj P X) : α → M P :=
  M.corec (F α id)

/-- corecursor where it is possible to return a fully formed value at any point
of the computation -/
def corec' {P : pfunctor} {α : Type u} (F : {X : Type u} → (α → X) → α → M P ⊕ obj P X) (x : α) : M P :=
  corec₁
    (fun (X : Type u) (rec : M P ⊕ α → X) (a : M P ⊕ α) =>
      let y : M P ⊕ obj P X := a >>= F (rec ∘ sum.inr);
      sorry)
    (sum.inr x)

