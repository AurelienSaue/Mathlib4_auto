/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

A model of ZFC in Lean.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.set.basic
import Mathlib.PostPort

universes u u_1 l u_2 u_3 v 

namespace Mathlib

/-- The type of `n`-ary functions `α → α → ... → α`. -/
def arity (α : Type u) : ℕ → Type u := sorry

namespace arity


/-- Constant `n`-ary function with value `a`. -/
def const {α : Type u} (a : α) (n : ℕ) : arity α n := sorry

protected instance arity.inhabited {α : Type u_1} {n : ℕ} [Inhabited α] : Inhabited (arity α n) :=
  { default := const Inhabited.default n }

end arity


/-- The type of pre-sets in universe `u`. A pre-set
  is a family of pre-sets indexed by a type in `Type u`.
  The ZFC universe is defined as a quotient of this
  to ensure extensionality. -/
inductive pSet where
| mk : (α : Type u) → (α → pSet) → pSet

namespace pSet


/-- The underlying type of a pre-set -/
def type : pSet → Type u := sorry

/-- The underlying pre-set family of a pre-set -/
def func (x : pSet) : type x → pSet := sorry

theorem mk_type_func (x : pSet) : mk (type x) (func x) = x :=
  pSet.cases_on x
    fun (x_α : Type u_1) (x_A : x_α → pSet) =>
      idRhs
        (mk (type (mk x_α x_A)) (func (mk x_α x_A)) = mk (type (mk x_α x_A)) (func (mk x_α x_A)))
        rfl

/-- Two pre-sets are extensionally equivalent if every
  element of the first family is extensionally equivalent to
  some element of the second family and vice-versa. -/
def equiv (x : pSet) (y : pSet) :=
  pSet.rec (fun (α : Type u_1) (z : α → pSet) (m : α → pSet → Prop) (_x : pSet) => sorry) x y

theorem equiv.refl (x : pSet) : equiv x x :=
  pSet.rec_on x
    fun (α : Type u_1) (A : α → pSet) (IH : ∀ (ᾰ : α), equiv (A ᾰ) (A ᾰ)) =>
      { left := fun (a : α) => Exists.intro a (IH a),
        right := fun (a : α) => Exists.intro a (IH a) }

theorem equiv.euc {x : pSet} {y : pSet} {z : pSet} : equiv x y → equiv z y → equiv x z := sorry

theorem equiv.symm {x : pSet} {y : pSet} : equiv x y → equiv y x := equiv.euc (equiv.refl y)

theorem equiv.trans {x : pSet} {y : pSet} {z : pSet} (h1 : equiv x y) (h2 : equiv y z) :
    equiv x z :=
  equiv.euc h1 (equiv.symm h2)

protected instance setoid : setoid pSet := setoid.mk equiv sorry

protected def subset : pSet → pSet → Prop := sorry

protected instance has_subset : has_subset pSet := has_subset.mk pSet.subset

theorem equiv.ext (x : pSet) (y : pSet) : equiv x y ↔ x ⊆ y ∧ y ⊆ x := sorry

theorem subset.congr_left {x : pSet} {y : pSet} {z : pSet} : equiv x y → (x ⊆ z ↔ y ⊆ z) := sorry

theorem subset.congr_right {x : pSet} {y : pSet} {z : pSet} : equiv x y → (z ⊆ x ↔ z ⊆ y) := sorry

/-- `x ∈ y` as pre-sets if `x` is extensionally equivalent to a member
  of the family `y`. -/
def mem : pSet → pSet → Prop := sorry

protected instance has_mem : has_mem pSet pSet := has_mem.mk mem

theorem mem.mk {α : Type u} (A : α → pSet) (a : α) : A a ∈ mk α A :=
  (fun (this : mem (A a) (mk α A)) => this) (Exists.intro a (equiv.refl (A a)))

theorem mem.ext {x : pSet} {y : pSet} : (∀ (w : pSet), w ∈ x ↔ w ∈ y) → equiv x y := sorry

theorem mem.congr_right {x : pSet} {y : pSet} : equiv x y → ∀ {w : pSet}, w ∈ x ↔ w ∈ y := sorry

theorem equiv_iff_mem {x : pSet} {y : pSet} : equiv x y ↔ ∀ {w : pSet}, w ∈ x ↔ w ∈ y := sorry

theorem mem.congr_left {x : pSet} {y : pSet} : equiv x y → ∀ {w : pSet}, x ∈ w ↔ y ∈ w := sorry

/-- Convert a pre-set to a `set` of pre-sets. -/
def to_set (u : pSet) : set pSet := set_of fun (x : pSet) => x ∈ u

/-- Two pre-sets are equivalent iff they have the same members. -/
theorem equiv.eq {x : pSet} {y : pSet} : equiv x y ↔ to_set x = to_set y :=
  iff.trans equiv_iff_mem (iff.symm set.ext_iff)

protected instance set.has_coe : has_coe pSet (set pSet) := has_coe.mk to_set

/-- The empty pre-set -/
protected def empty : pSet := mk (ulift empty) fun (e : ulift empty) => sorry

protected instance has_emptyc : has_emptyc pSet := has_emptyc.mk pSet.empty

protected instance inhabited : Inhabited pSet := { default := ∅ }

theorem mem_empty (x : pSet) : ¬x ∈ ∅ := sorry

/-- Insert an element into a pre-set -/
protected def insert : pSet → pSet → pSet := sorry

protected instance has_insert : has_insert pSet pSet := has_insert.mk pSet.insert

protected instance has_singleton : has_singleton pSet pSet :=
  has_singleton.mk fun (s : pSet) => insert s ∅

protected instance is_lawful_singleton : is_lawful_singleton pSet pSet :=
  is_lawful_singleton.mk fun (_x : pSet) => rfl

/-- The n-th von Neumann ordinal -/
def of_nat : ℕ → pSet := sorry

/-- The von Neumann ordinal ω -/
def omega : pSet := mk (ulift ℕ) fun (n : ulift ℕ) => of_nat (ulift.down n)

/-- The separation operation `{x ∈ a | p x}` -/
protected def sep (p : set pSet) : pSet → pSet := sorry

protected instance has_sep : has_sep pSet pSet := has_sep.mk pSet.sep

/-- The powerset operator -/
def powerset : pSet → pSet := sorry

theorem mem_powerset {x : pSet} {y : pSet} : y ∈ powerset x ↔ y ⊆ x := sorry

/-- The set union operator -/
def Union : pSet → pSet := sorry

theorem mem_Union {x : pSet} {y : pSet} : y ∈ Union x ↔ ∃ (z : pSet), ∃ (_x : z ∈ x), y ∈ z := sorry

/-- The image of a function -/
def image (f : pSet → pSet) : pSet → pSet := sorry

theorem mem_image {f : pSet → pSet} (H : ∀ {x y : pSet}, equiv x y → equiv (f x) (f y)) {x : pSet}
    {y : pSet} : y ∈ image f x ↔ ∃ (z : pSet), ∃ (H : z ∈ x), equiv y (f z) :=
  sorry

/-- Universe lift operation -/
protected def lift : pSet → pSet := sorry

/-- Embedding of one universe in another -/
def embed : pSet := mk (ulift pSet) fun (_x : ulift pSet) => sorry

theorem lift_mem_embed (x : pSet) : pSet.lift x ∈ embed :=
  Exists.intro (ulift.up x) (equiv.refl (pSet.lift x))

/-- Function equivalence is defined so that `f ~ g` iff
  `∀ x y, x ~ y → f x ~ g y`. This extends to equivalence of n-ary
  functions. -/
def arity.equiv {n : ℕ} : arity pSet n → arity pSet n → Prop := sorry

theorem arity.equiv_const {a : pSet} (n : ℕ) : arity.equiv (arity.const a n) (arity.const a n) :=
  sorry

/-- `resp n` is the collection of n-ary functions on `pSet` that respect
  equivalence, i.e. when the inputs are equivalent the output is as well. -/
def resp (n : ℕ) := Subtype fun (x : arity pSet n) => arity.equiv x x

protected instance resp.inhabited {n : ℕ} : Inhabited (resp n) :=
  { default := { val := arity.const Inhabited.default n, property := sorry } }

def resp.f {n : ℕ} (f : resp (n + 1)) (x : pSet) : resp n :=
  { val := subtype.val f x, property := sorry }

def resp.equiv {n : ℕ} (a : resp n) (b : resp n) := arity.equiv (subtype.val a) (subtype.val b)

theorem resp.refl {n : ℕ} (a : resp n) : resp.equiv a a := subtype.property a

theorem resp.euc {n : ℕ} {a : resp n} {b : resp n} {c : resp n} :
    resp.equiv a b → resp.equiv c b → resp.equiv a c :=
  sorry

protected instance resp.setoid {n : ℕ} : setoid (resp n) := setoid.mk resp.equiv sorry

end pSet


/-- The ZFC universe of sets consists of the type of pre-sets,
  quotiented by extensional equivalence. -/
def Set := quotient pSet.setoid

namespace pSet


namespace resp


def eval_aux {n : ℕ} :
    Subtype fun (f : resp n → arity Set n) => ∀ (a b : resp n), equiv a b → f a = f b :=
  sorry

/-- An equivalence-respecting function yields an n-ary Set function. -/
def eval (n : ℕ) : resp n → arity Set n := subtype.val eval_aux

theorem eval_val {n : ℕ} {f : resp (n + 1)} {x : pSet} :
    eval (n + 1) f (quotient.mk x) = eval n (f f x) :=
  rfl

end resp


/-- A set function is "definable" if it is the image of some n-ary pre-set
  function. This isn't exactly definability, but is useful as a sufficient
  condition for functions that have a computable image. -/
class inductive definable (n : ℕ) : arity Set n → Type (u + 1) where
| mk : (f : resp n) → definable n (resp.eval n f)

def definable.eq_mk {n : ℕ} (f : resp n) {s : arity Set n} (H : resp.eval n f = s) :
    definable n s :=
  sorry

def definable.resp {n : ℕ} (s : arity Set n) [definable n s] : resp n := sorry

theorem definable.eq {n : ℕ} (s : arity Set n) [H : definable n s] :
    resp.eval n (definable.resp s) = s :=
  sorry

end pSet


namespace classical


def all_definable {n : ℕ} (F : arity Set n) : pSet.definable n F := sorry

end classical


namespace Set


def mk : pSet → Set := quotient.mk

@[simp] theorem mk_eq (x : pSet) : quotient.mk x = mk x := rfl

@[simp] theorem eval_mk {n : ℕ} {f : pSet.resp (n + 1)} {x : pSet} :
    pSet.resp.eval (n + 1) f (mk x) = pSet.resp.eval n (pSet.resp.f f x) :=
  rfl

def mem : Set → Set → Prop := quotient.lift₂ pSet.mem sorry

protected instance has_mem : has_mem Set Set := has_mem.mk mem

/-- Convert a ZFC set into a `set` of sets -/
def to_set (u : Set) : set Set := set_of fun (x : Set) => x ∈ u

protected def subset (x : Set) (y : Set) := ∀ {z : Set}, z ∈ x → z ∈ y

protected instance has_subset : has_subset Set := has_subset.mk Set.subset

theorem subset_def {x : Set} {y : Set} : x ⊆ y ↔ ∀ {z : Set}, z ∈ x → z ∈ y := iff.rfl

theorem subset_iff (x : pSet) (y : pSet) : mk x ⊆ mk y ↔ x ⊆ y := sorry

theorem ext {x : Set} {y : Set} : (∀ (z : Set), z ∈ x ↔ z ∈ y) → x = y :=
  quotient.induction_on₂ x y
    fun (u v : pSet) (h : ∀ (z : Set), z ∈ quotient.mk u ↔ z ∈ quotient.mk v) =>
      quotient.sound (pSet.mem.ext fun (w : pSet) => h (quotient.mk w))

theorem ext_iff {x : Set} {y : Set} : (∀ (z : Set), z ∈ x ↔ z ∈ y) ↔ x = y := sorry

/-- The empty set -/
def empty : Set := mk ∅

protected instance has_emptyc : has_emptyc Set := has_emptyc.mk empty

protected instance inhabited : Inhabited Set := { default := ∅ }

@[simp] theorem mem_empty (x : Set) : ¬x ∈ ∅ := quotient.induction_on x pSet.mem_empty

theorem eq_empty (x : Set) : x = ∅ ↔ ∀ (y : Set), ¬y ∈ x := sorry

/-- `insert x y` is the set `{x} ∪ y` -/
protected def insert : Set → Set → Set :=
  pSet.resp.eval (bit0 1) { val := pSet.insert, property := sorry }

protected instance has_insert : has_insert Set Set := has_insert.mk Set.insert

protected instance has_singleton : has_singleton Set Set :=
  has_singleton.mk fun (x : Set) => insert x ∅

protected instance is_lawful_singleton : is_lawful_singleton Set Set :=
  is_lawful_singleton.mk fun (x : Set) => rfl

@[simp] theorem mem_insert {x : Set} {y : Set} {z : Set} : x ∈ insert y z ↔ x = y ∨ x ∈ z := sorry

@[simp] theorem mem_singleton {x : Set} {y : Set} : x ∈ singleton y ↔ x = y :=
  iff.trans mem_insert
    { mp :=
        fun (o : x = y ∨ x ∈ ∅) =>
          Or._oldrec (fun (h : x = y) => h) (fun (n : x ∈ ∅) => absurd n (mem_empty x)) o,
      mpr := Or.inl }

@[simp] theorem mem_pair {x : Set} {y : Set} {z : Set} :
    x ∈ insert y (singleton z) ↔ x = y ∨ x = z :=
  iff.trans mem_insert (or_congr iff.rfl mem_singleton)

/-- `omega` is the first infinite von Neumann ordinal -/
def omega : Set := mk pSet.omega

@[simp] theorem omega_zero : ∅ ∈ omega :=
  (fun (this : pSet.mem ∅ pSet.omega) => this) (Exists.intro (ulift.up 0) (pSet.equiv.refl ∅))

@[simp] theorem omega_succ {n : Set} : n ∈ omega → insert n n ∈ omega := sorry

/-- `{x ∈ a | p x}` is the set of elements in `a` satisfying `p` -/
protected def sep (p : Set → Prop) : Set → Set :=
  pSet.resp.eval 1 { val := pSet.sep fun (y : pSet) => p (quotient.mk y), property := sorry }

protected instance has_sep : has_sep Set Set := has_sep.mk Set.sep

@[simp] theorem mem_sep {p : Set → Prop} {x : Set} {y : Set} :
    y ∈ has_sep.sep (fun (y : Set) => p y) x ↔ y ∈ x ∧ p y :=
  sorry

/-- The powerset operation, the collection of subsets of a set -/
def powerset : Set → Set := pSet.resp.eval 1 { val := pSet.powerset, property := sorry }

@[simp] theorem mem_powerset {x : Set} {y : Set} : y ∈ powerset x ↔ y ⊆ x := sorry

theorem Union_lem {α : Type u} {β : Type u} (A : α → pSet) (B : β → pSet)
    (αβ : ∀ (a : α), ∃ (b : β), pSet.equiv (A a) (B b)) (a : pSet.type (pSet.Union (pSet.mk α A))) :
    ∃ (b : pSet.type (pSet.Union (pSet.mk β B))),
        pSet.equiv (pSet.func (pSet.Union (pSet.mk α A)) a)
          (pSet.func (pSet.Union (pSet.mk β B)) b) :=
  sorry

/-- The union operator, the collection of elements of elements of a set -/
def Union : Set → Set := pSet.resp.eval 1 { val := pSet.Union, property := sorry }

notation:1024 "⋃" => Mathlib.Set.Union

@[simp] theorem mem_Union {x : Set} {y : Set} : y ∈ ⋃ ↔ ∃ (z : Set), ∃ (H : z ∈ x), y ∈ z := sorry

@[simp] theorem Union_singleton {x : Set} : ⋃ = x := sorry

theorem singleton_inj {x : Set} {y : Set} (H : singleton x = singleton y) : x = y :=
  let this : ⋃ = ⋃ := congr_arg ⋃ H;
  eq.mp (Eq._oldrec (Eq.refl (x = ⋃)) Union_singleton)
    (eq.mp (Eq._oldrec (Eq.refl (⋃ = ⋃)) Union_singleton) this)

/-- The binary union operation -/
protected def union (x : Set) (y : Set) : Set := ⋃

/-- The binary intersection operation -/
protected def inter (x : Set) (y : Set) : Set := has_sep.sep (fun (z : Set) => z ∈ y) x

/-- The set difference operation -/
protected def diff (x : Set) (y : Set) : Set := has_sep.sep (fun (z : Set) => ¬z ∈ y) x

protected instance has_union : has_union Set := has_union.mk Set.union

protected instance has_inter : has_inter Set := has_inter.mk Set.inter

protected instance has_sdiff : has_sdiff Set := has_sdiff.mk Set.diff

@[simp] theorem mem_union {x : Set} {y : Set} {z : Set} : z ∈ x ∪ y ↔ z ∈ x ∨ z ∈ y := sorry

@[simp] theorem mem_inter {x : Set} {y : Set} {z : Set} : z ∈ x ∩ y ↔ z ∈ x ∧ z ∈ y := mem_sep

@[simp] theorem mem_diff {x : Set} {y : Set} {z : Set} : z ∈ x \ y ↔ z ∈ x ∧ ¬z ∈ y := mem_sep

theorem induction_on {p : Set → Prop} (x : Set)
    (h : ∀ (x : Set), (∀ (y : Set), y ∈ x → p y) → p x) : p x :=
  sorry

theorem regularity (x : Set) (h : x ≠ ∅) : ∃ (y : Set), ∃ (H : y ∈ x), x ∩ y = ∅ := sorry

/-- The image of a (definable) set function -/
def image (f : Set → Set) [H : pSet.definable 1 f] : Set → Set :=
  let r : pSet.resp 1 := pSet.definable.resp f;
  pSet.resp.eval 1 { val := pSet.image (subtype.val r), property := sorry }

theorem image.mk (f : Set → Set) [H : pSet.definable 1 f] (x : Set) {y : Set} (h : y ∈ x) :
    f y ∈ image f x :=
  sorry

@[simp] theorem mem_image {f : Set → Set} [H : pSet.definable 1 f] {x : Set} {y : Set} :
    y ∈ image f x ↔ ∃ (z : Set), ∃ (H : z ∈ x), f z = y :=
  sorry

/-- Kuratowski ordered pair -/
def pair (x : Set) (y : Set) : Set := insert (singleton x) (singleton (insert x (singleton y)))

/-- A subset of pairs `{(a, b) ∈ x × y | p a b}` -/
def pair_sep (p : Set → Set → Prop) (x : Set) (y : Set) : Set :=
  has_sep.sep
    (fun (z : Set) => ∃ (a : Set), ∃ (H : a ∈ x), ∃ (b : Set), ∃ (H : b ∈ y), z = pair a b ∧ p a b)
    (powerset (powerset (x ∪ y)))

@[simp] theorem mem_pair_sep {p : Set → Set → Prop} {x : Set} {y : Set} {z : Set} :
    z ∈ pair_sep p x y ↔
        ∃ (a : Set), ∃ (H : a ∈ x), ∃ (b : Set), ∃ (H : b ∈ y), z = pair a b ∧ p a b :=
  sorry

theorem pair_inj {x : Set} {y : Set} {x' : Set} {y' : Set} (H : pair x y = pair x' y') :
    x = x' ∧ y = y' :=
  sorry

/-- The cartesian product, `{(a, b) | a ∈ x, b ∈ y}` -/
def prod : Set → Set → Set := pair_sep fun (a b : Set) => True

@[simp] theorem mem_prod {x : Set} {y : Set} {z : Set} :
    z ∈ prod x y ↔ ∃ (a : Set), ∃ (H : a ∈ x), ∃ (b : Set), ∃ (H : b ∈ y), z = pair a b :=
  sorry

@[simp] theorem pair_mem_prod {x : Set} {y : Set} {a : Set} {b : Set} :
    pair a b ∈ prod x y ↔ a ∈ x ∧ b ∈ y :=
  sorry

/-- `is_func x y f` is the assertion `f : x → y` where `f` is a ZFC function
  (a set of ordered pairs) -/
def is_func (x : Set) (y : Set) (f : Set) :=
  f ⊆ prod x y ∧ ∀ (z : Set), z ∈ x → exists_unique fun (w : Set) => pair z w ∈ f

/-- `funs x y` is `y ^ x`, the set of all set functions `x → y` -/
def funs (x : Set) (y : Set) : Set :=
  has_sep.sep (fun (f : Set) => is_func x y f) (powerset (prod x y))

@[simp] theorem mem_funs {x : Set} {y : Set} {f : Set} : f ∈ funs x y ↔ is_func x y f := sorry

-- TODO(Mario): Prove this computably

protected instance map_definable_aux (f : Set → Set) [H : pSet.definable 1 f] :
    pSet.definable 1 fun (y : Set) => pair y (f y) :=
  classical.all_definable fun (y : Set) => pair y (f y)

/-- Graph of a function: `map f x` is the ZFC function which maps `a ∈ x` to `f a` -/
def map (f : Set → Set) [H : pSet.definable 1 f] : Set → Set := image fun (y : Set) => pair y (f y)

@[simp] theorem mem_map {f : Set → Set} [H : pSet.definable 1 f] {x : Set} {y : Set} :
    y ∈ map f x ↔ ∃ (z : Set), ∃ (H : z ∈ x), pair z (f z) = y :=
  mem_image

theorem map_unique {f : Set → Set} [H : pSet.definable 1 f] {x : Set} {z : Set} (zx : z ∈ x) :
    exists_unique fun (w : Set) => pair z w ∈ map f x :=
  sorry

@[simp] theorem map_is_func {f : Set → Set} [H : pSet.definable 1 f] {x : Set} {y : Set} :
    is_func x y (map f x) ↔ ∀ (z : Set), z ∈ x → f z ∈ y :=
  sorry

end Set


def Class := set Set

namespace Class


protected instance has_subset : has_subset Class := has_subset.mk set.subset

protected instance has_sep : has_sep Set Class := has_sep.mk set.sep

protected instance has_emptyc : has_emptyc Class := has_emptyc.mk fun (a : Set) => False

protected instance inhabited : Inhabited Class := { default := ∅ }

protected instance has_insert : has_insert Set Class := has_insert.mk set.insert

protected instance has_union : has_union Class := has_union.mk set.union

protected instance has_inter : has_inter Class := has_inter.mk set.inter

protected instance has_neg : Neg Class := { neg := set.compl }

protected instance has_sdiff : has_sdiff Class := has_sdiff.mk set.diff

/-- Coerce a set into a class -/
def of_Set (x : Set) : Class := set_of fun (y : Set) => y ∈ x

protected instance has_coe : has_coe Set Class := has_coe.mk of_Set

/-- The universal class -/
def univ : Class := set.univ

/-- Assert that `A` is a set satisfying `p` -/
def to_Set (p : Set → Prop) (A : Class) := ∃ (x : Set), ↑x = A ∧ p x

/-- `A ∈ B` if `A` is a set which is a member of `B` -/
protected def mem (A : Class) (B : Class) := to_Set B A

protected instance has_mem : has_mem Class Class := has_mem.mk Class.mem

theorem mem_univ {A : Class} : A ∈ univ ↔ ∃ (x : Set), ↑x = A :=
  exists_congr fun (x : Set) => and_true (↑x = A)

/-- Convert a conglomerate (a collection of classes) into a class -/
def Cong_to_Class (x : set Class) : Class := set_of fun (y : Set) => ↑y ∈ x

/-- Convert a class into a conglomerate (a collection of classes) -/
def Class_to_Cong (x : Class) : set Class := set_of fun (y : Class) => y ∈ x

/-- The power class of a class is the class of all subclasses that are sets -/
def powerset (x : Class) : Class := Cong_to_Class (𝒫 x)

/-- The union of a class is the class of all members of sets in the class -/
def Union (x : Class) : Class := ⋃₀Class_to_Cong x

notation:1024 "⋃" => Mathlib.Class.Union

theorem of_Set.inj {x : Set} {y : Set} (h : ↑x = ↑y) : x = y := sorry

@[simp] theorem to_Set_of_Set (p : Set → Prop) (x : Set) : to_Set p ↑x ↔ p x := sorry

@[simp] theorem mem_hom_left (x : Set) (A : Class) : ↑x ∈ A ↔ A x :=
  to_Set_of_Set (fun (x : Set) => A x) x

@[simp] theorem mem_hom_right (x : Set) (y : Set) : coe y x ↔ x ∈ y := iff.rfl

@[simp] theorem subset_hom (x : Set) (y : Set) : ↑x ⊆ ↑y ↔ x ⊆ y := iff.rfl

@[simp] theorem sep_hom (p : Set → Prop) (x : Set) :
    ↑(has_sep.sep (fun (y : Set) => p y) x) = has_sep.sep (fun (y : Set) => p y) ↑x :=
  set.ext fun (y : Set) => Set.mem_sep

@[simp] theorem empty_hom : ↑∅ = ∅ :=
  set.ext
    fun (y : Set) =>
      (fun (this : y ∈ ↑∅ ↔ False) => this)
        (eq.mpr (id (propext (iff_false (y ∈ ↑∅)))) (Set.mem_empty y))

@[simp] theorem insert_hom (x : Set) (y : Set) : insert x ↑y = ↑(insert x y) :=
  set.ext fun (z : Set) => iff.symm Set.mem_insert

@[simp] theorem union_hom (x : Set) (y : Set) : ↑x ∪ ↑y = ↑(x ∪ y) :=
  set.ext fun (z : Set) => iff.symm Set.mem_union

@[simp] theorem inter_hom (x : Set) (y : Set) : ↑x ∩ ↑y = ↑(x ∩ y) :=
  set.ext fun (z : Set) => iff.symm Set.mem_inter

@[simp] theorem diff_hom (x : Set) (y : Set) : ↑x \ ↑y = ↑(x \ y) :=
  set.ext fun (z : Set) => iff.symm Set.mem_diff

@[simp] theorem powerset_hom (x : Set) : powerset ↑x = ↑(Set.powerset x) :=
  set.ext fun (z : Set) => iff.symm Set.mem_powerset

@[simp] theorem Union_hom (x : Set) : ⋃ = ↑⋃ := sorry

/-- The definite description operator, which is {x} if `{a | p a} = {x}`
  and ∅ otherwise -/
def iota (p : Set → Prop) : Class := ⋃

theorem iota_val (p : Set → Prop) (x : Set) (H : ∀ (y : Set), p y ↔ y = x) : iota p = ↑x := sorry

/-- Unlike the other set constructors, the `iota` definite descriptor
  is a set for any set input, but not constructively so, so there is no
  associated `(Set → Prop) → Set` function. -/
theorem iota_ex (p : Set → Prop) : iota p ∈ univ := sorry

/-- Function value -/
def fval (F : Class) (A : Class) : Class :=
  iota fun (y : Set) => to_Set (fun (x : Set) => F (Set.pair x y)) A

infixl:100 "′" => Mathlib.Class.fval

theorem fval_ex (F : Class) (A : Class) : F′A ∈ univ :=
  iota_ex fun (y : Set) => to_Set (fun (x : Set) => F (Set.pair x y)) A

end Class


namespace Set


@[simp] theorem map_fval {f : Set → Set} [H : pSet.definable 1 f] {x : Set} {y : Set} (h : y ∈ x) :
    ↑(map f x)′↑y = ↑(f y) :=
  sorry

/-- A choice function on the set of nonempty sets `x` -/
def choice (x : Set) : Set := map (fun (y : Set) => classical.epsilon fun (z : Set) => z ∈ y) x

theorem choice_mem_aux (x : Set) (h : ¬∅ ∈ x) (y : Set) (yx : y ∈ x) :
    (classical.epsilon fun (z : Set) => z ∈ y) ∈ y :=
  sorry

theorem choice_is_func (x : Set) (h : ¬∅ ∈ x) : is_func x ⋃ (choice x) := sorry

theorem choice_mem (x : Set) (h : ¬∅ ∈ x) (y : Set) (yx : y ∈ x) : ↑(choice x)′↑y ∈ ↑y := sorry

end Mathlib