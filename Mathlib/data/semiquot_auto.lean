/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

A data type for semiquotients, which are classically equivalent to
nonempty sets, but are useful for programming; the idea is that
a semiquotient set `S` represents some (particular but unknown)
element of `S`. This can be used to model nondeterministic functions,
which return something in a range of values (represented by the
predicate `S`) but are not completely determined.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.set.lattice
import Mathlib.PostPort

universes u u_1 l u_2 u_3 u_4 u_5 

namespace Mathlib

/-- A member of `semiquot α` is classically a nonempty `set α`,
  and in the VM is represented by an element of `α`; the relation
  between these is that the VM element is required to be a member
  of the set `s`. The specific element of `s` that the VM computes
  is hidden by a quotient construction, allowing for the representation
  of nondeterministic functions. -/
structure semiquot (α : Type u_1) where
  mk' :: (s : set α) (val : trunc ↥s)

namespace semiquot


protected instance has_mem {α : Type u_1} : has_mem α (semiquot α) :=
  has_mem.mk fun (a : α) (q : semiquot α) => a ∈ s q

/-- Construct a `semiquot α` from `h : a ∈ s` where `s : set α`. -/
def mk {α : Type u_1} {a : α} {s : set α} (h : a ∈ s) : semiquot α :=
  mk' s (trunc.mk { val := a, property := h })

theorem ext_s {α : Type u_1} {q₁ : semiquot α} {q₂ : semiquot α} : q₁ = q₂ ↔ s q₁ = s q₂ := sorry

theorem ext {α : Type u_1} {q₁ : semiquot α} {q₂ : semiquot α} :
    q₁ = q₂ ↔ ∀ (a : α), a ∈ q₁ ↔ a ∈ q₂ :=
  iff.trans ext_s set.ext_iff

theorem exists_mem {α : Type u_1} (q : semiquot α) : ∃ (a : α), a ∈ q := sorry

theorem eq_mk_of_mem {α : Type u_1} {q : semiquot α} {a : α} (h : a ∈ q) : q = mk h :=
  iff.mpr ext_s rfl

theorem nonempty {α : Type u_1} (q : semiquot α) : set.nonempty (s q) := exists_mem q

/-- `pure a` is `a` reinterpreted as an unspecified element of `{a}`. -/
protected def pure {α : Type u_1} (a : α) : semiquot α := mk (set.mem_singleton a)

@[simp] theorem mem_pure' {α : Type u_1} {a : α} {b : α} : a ∈ semiquot.pure b ↔ a = b :=
  set.mem_singleton_iff

/-- Replace `s` in a `semiquot` with a superset. -/
def blur' {α : Type u_1} (q : semiquot α) {s : set α} (h : s q ⊆ s) : semiquot α :=
  mk' s
    (trunc.lift (fun (a : ↥(s q)) => trunc.mk { val := subtype.val a, property := sorry }) sorry
      (val q))

/-- Replace `s` in a `q : semiquot α` with a union `s ∪ q.s` -/
def blur {α : Type u_1} (s : set α) (q : semiquot α) : semiquot α := blur' q sorry

theorem blur_eq_blur' {α : Type u_1} (q : semiquot α) (s : set α) (h : s q ⊆ s) :
    blur s q = blur' q h :=
  sorry

@[simp] theorem mem_blur' {α : Type u_1} (q : semiquot α) {s : set α} (h : s q ⊆ s) {a : α} :
    a ∈ blur' q h ↔ a ∈ s :=
  iff.rfl

/-- Convert a `trunc α` to a `semiquot α`. -/
def of_trunc {α : Type u_1} (q : trunc α) : semiquot α :=
  mk' set.univ (trunc.map (fun (a : α) => { val := a, property := trivial }) q)

/-- Convert a `semiquot α` to a `trunc α`. -/
def to_trunc {α : Type u_1} (q : semiquot α) : trunc α := trunc.map subtype.val (val q)

/-- If `f` is a constant on `q.s`, then `q.lift_on f` is the value of `f`
at any point of `q`. -/
def lift_on {α : Type u_1} {β : Type u_2} (q : semiquot α) (f : α → β)
    (h : ∀ (a b : α), a ∈ q → b ∈ q → f a = f b) : β :=
  trunc.lift_on (val q) (fun (x : ↥(s q)) => f (subtype.val x)) sorry

theorem lift_on_of_mem {α : Type u_1} {β : Type u_2} (q : semiquot α) (f : α → β)
    (h : ∀ (a b : α), a ∈ q → b ∈ q → f a = f b) (a : α) (aq : a ∈ q) : lift_on q f h = f a :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (∀ (h : ∀ (a b : α), a ∈ q → b ∈ q → f a = f b), lift_on q f h = f a))
        (eq_mk_of_mem aq)))
    (fun (h : ∀ (a_1 b : α), a_1 ∈ mk aq → b ∈ mk aq → f a_1 = f b) =>
      Eq.refl (lift_on (mk aq) f h))
    h

def map {α : Type u_1} {β : Type u_2} (f : α → β) (q : semiquot α) : semiquot β :=
  mk' (f '' s q)
    (trunc.map (fun (x : ↥(s q)) => { val := f (subtype.val x), property := sorry }) (val q))

@[simp] theorem mem_map {α : Type u_1} {β : Type u_2} (f : α → β) (q : semiquot α) (b : β) :
    b ∈ map f q ↔ ∃ (a : α), a ∈ q ∧ f a = b :=
  set.mem_image (fun (a : α) => f a) (s q) b

def bind {α : Type u_1} {β : Type u_2} (q : semiquot α) (f : α → semiquot β) : semiquot β :=
  mk' (set.Union fun (a : α) => set.Union fun (H : a ∈ s q) => s (f a))
    (trunc.bind (val q)
      fun (a : ↥(s q)) =>
        trunc.map
          (fun (b : ↥(s (f (subtype.val a)))) => { val := subtype.val b, property := sorry })
          (val (f (subtype.val a))))

@[simp] theorem mem_bind {α : Type u_1} {β : Type u_2} (q : semiquot α) (f : α → semiquot β)
    (b : β) : b ∈ bind q f ↔ ∃ (a : α), ∃ (H : a ∈ q), b ∈ f a :=
  set.mem_bUnion_iff

protected instance monad : Monad semiquot :=
  { toApplicative :=
      { toFunctor := { map := map, mapConst := fun (α β : Type u_1) => map ∘ function.const β },
        toPure := { pure := semiquot.pure },
        toSeq :=
          { seq :=
              fun (α β : Type u_1) (f : semiquot (α → β)) (x : semiquot α) =>
                bind f fun (_x : α → β) => map _x x },
        toSeqLeft :=
          { seqLeft :=
              fun (α β : Type u_1) (a : semiquot α) (b : semiquot β) =>
                (fun (α β : Type u_1) (f : semiquot (α → β)) (x : semiquot α) =>
                    bind f fun (_x : α → β) => map _x x)
                  β α (map (function.const β) a) b },
        toSeqRight :=
          { seqRight :=
              fun (α β : Type u_1) (a : semiquot α) (b : semiquot β) =>
                (fun (α β : Type u_1) (f : semiquot (α → β)) (x : semiquot α) =>
                    bind f fun (_x : α → β) => map _x x)
                  β β (map (function.const α id) a) b } },
    toBind := { bind := bind } }

@[simp] theorem map_def {α : Type u_1} {β : Type u_1} : Functor.map = map := rfl

@[simp] theorem bind_def {α : Type u_1} {β : Type u_1} : bind = bind := rfl

@[simp] theorem mem_pure {α : Type u_1} {a : α} {b : α} : a ∈ pure b ↔ a = b :=
  set.mem_singleton_iff

theorem mem_pure_self {α : Type u_1} (a : α) : a ∈ pure a := set.mem_singleton a

@[simp] theorem pure_inj {α : Type u_1} {a : α} {b : α} : pure a = pure b ↔ a = b :=
  iff.trans ext_s set.singleton_eq_singleton_iff

protected instance is_lawful_monad : is_lawful_monad semiquot := sorry

protected instance has_le {α : Type u_1} : HasLessEq (semiquot α) :=
  { LessEq := fun (s t : semiquot α) => s s ⊆ s t }

protected instance partial_order {α : Type u_1} : partial_order (semiquot α) :=
  partial_order.mk (fun (s t : semiquot α) => ∀ {x : α}, x ∈ s → x ∈ t)
    (preorder.lt._default fun (s t : semiquot α) => ∀ {x : α}, x ∈ s → x ∈ t) sorry sorry sorry

protected instance semilattice_sup {α : Type u_1} : semilattice_sup (semiquot α) :=
  semilattice_sup.mk (fun (s : semiquot α) => blur (s s)) partial_order.le partial_order.lt sorry
    sorry sorry sorry sorry sorry

@[simp] theorem pure_le {α : Type u_1} {a : α} {s : semiquot α} : pure a ≤ s ↔ a ∈ s :=
  set.singleton_subset_iff

def is_pure {α : Type u_1} (q : semiquot α) := ∀ (a b : α), a ∈ q → b ∈ q → a = b

def get {α : Type u_1} (q : semiquot α) (h : is_pure q) : α := lift_on q id h

theorem get_mem {α : Type u_1} {q : semiquot α} (p : is_pure q) : get q p ∈ q := sorry

theorem eq_pure {α : Type u_1} {q : semiquot α} (p : is_pure q) : q = pure (get q p) := sorry

@[simp] theorem pure_is_pure {α : Type u_1} (a : α) : is_pure (pure a) :=
  fun (a_1 b : α) (H : a_1 ∈ pure a) (H_1 : b ∈ pure a) =>
    idRhs (a_1 = b)
      (of_eq_true
        (eq_true_intro
          (Eq.trans (eq.mp (propext mem_pure) H) (Eq.symm (eq.mp (propext mem_pure) H_1)))))

theorem is_pure_iff {α : Type u_1} {s : semiquot α} : is_pure s ↔ ∃ (a : α), s = pure a := sorry

theorem is_pure.mono {α : Type u_1} {s : semiquot α} {t : semiquot α} (st : s ≤ t) (h : is_pure t) :
    is_pure s :=
  fun (a b : α) (H : a ∈ s) (H_1 : b ∈ s) => idRhs (a = b) (h a b (st H) (st H_1))

theorem is_pure.min {α : Type u_1} {s : semiquot α} {t : semiquot α} (h : is_pure t) :
    s ≤ t ↔ s = t :=
  sorry

theorem is_pure_of_subsingleton {α : Type u_1} [subsingleton α] (q : semiquot α) : is_pure q :=
  fun (a b : α) (H : a ∈ q) (H : b ∈ q) => idRhs (a = b) (subsingleton.elim a b)

/-- `univ : semiquot α` represents an unspecified element of `univ : set α`. -/
def univ {α : Type u_1} [Inhabited α] : semiquot α := mk sorry

protected instance inhabited {α : Type u_1} [Inhabited α] : Inhabited (semiquot α) :=
  { default := univ }

@[simp] theorem mem_univ {α : Type u_1} [Inhabited α] (a : α) : a ∈ univ := set.mem_univ

theorem univ_unique {α : Type u_1} (I : Inhabited α) (J : Inhabited α) : univ = univ := sorry

@[simp] theorem is_pure_univ {α : Type u_1} [Inhabited α] : is_pure univ ↔ subsingleton α := sorry

protected instance order_top {α : Type u_1} [Inhabited α] : order_top (semiquot α) :=
  order_top.mk univ partial_order.le partial_order.lt sorry sorry sorry sorry

protected instance semilattice_sup_top {α : Type u_1} [Inhabited α] :
    semilattice_sup_top (semiquot α) :=
  semilattice_sup_top.mk order_top.top order_top.le order_top.lt sorry sorry sorry sorry
    semilattice_sup.sup sorry sorry sorry

end Mathlib