/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.Lean3Lib.data.vector
import Mathlib.data.list.nodup
import Mathlib.data.list.of_fn
import Mathlib.control.applicative
import Mathlib.PostPort

universes u_1 u_2 u u_3 

namespace Mathlib

/-!
# Additional theorems about the `vector` type

This file introduces the infix notation `::ᵥ` for `vector.cons`.
-/

namespace vector


infixr:67 "::ᵥ" => Mathlib.vector.cons

protected instance inhabited {n : ℕ} {α : Type u_1} [Inhabited α] : Inhabited (vector α n) :=
  { default := of_fn fun (_x : fin n) => Inhabited.default }

theorem to_list_injective {n : ℕ} {α : Type u_1} : function.injective to_list :=
  subtype.val_injective

/-- Two `v w : vector α n` are equal iff they are equal at every single index. -/
theorem ext {n : ℕ} {α : Type u_1} {v : vector α n} {w : vector α n}
    (h : ∀ (m : fin n), nth v m = nth w m) : v = w :=
  sorry

/-- The empty `vector` is a `subsingleton`. -/
protected instance zero_subsingleton {α : Type u_1} : subsingleton (vector α 0) :=
  subsingleton.intro fun (_x _x_1 : vector α 0) => ext fun (m : fin 0) => fin.elim0 m

@[simp] theorem cons_val {n : ℕ} {α : Type u_1} (a : α) (v : vector α n) :
    subtype.val (a::ᵥv) = a :: subtype.val v :=
  sorry

@[simp] theorem cons_head {n : ℕ} {α : Type u_1} (a : α) (v : vector α n) : head (a::ᵥv) = a :=
  sorry

@[simp] theorem cons_tail {n : ℕ} {α : Type u_1} (a : α) (v : vector α n) : tail (a::ᵥv) = v :=
  sorry

@[simp] theorem to_list_of_fn {α : Type u_1} {n : ℕ} (f : fin n → α) :
    to_list (of_fn f) = list.of_fn f :=
  sorry

@[simp] theorem mk_to_list {n : ℕ} {α : Type u_1} (v : vector α n)
    (h : list.length (to_list v) = n) : { val := to_list v, property := h } = v :=
  sorry

@[simp] theorem to_list_map {n : ℕ} {α : Type u_1} {β : Type u_2} (v : vector α n) (f : α → β) :
    to_list (map f v) = list.map f (to_list v) :=
  subtype.cases_on v
    fun (v_val : List α) (v_property : list.length v_val = n) =>
      Eq.refl (to_list (map f { val := v_val, property := v_property }))

theorem nth_eq_nth_le {n : ℕ} {α : Type u_1} (v : vector α n) (i : fin n) :
    nth v i =
        list.nth_le (to_list v) (subtype.val i)
          (eq.mpr
            (id (Eq._oldrec (Eq.refl (subtype.val i < list.length (to_list v))) (to_list_length v)))
            (subtype.property i)) :=
  subtype.cases_on v
    fun (v_val : List α) (v_property : list.length v_val = n) =>
      idRhs
        (nth { val := v_val, property := v_property } i =
          nth { val := v_val, property := v_property } i)
        rfl

@[simp] theorem nth_map {n : ℕ} {α : Type u_1} {β : Type u_2} (v : vector α n) (f : α → β)
    (i : fin n) : nth (map f v) i = f (nth v i) :=
  sorry

@[simp] theorem nth_of_fn {α : Type u_1} {n : ℕ} (f : fin n → α) (i : fin n) :
    nth (of_fn f) i = f i :=
  sorry

@[simp] theorem of_fn_nth {n : ℕ} {α : Type u_1} (v : vector α n) : of_fn (nth v) = v := sorry

@[simp] theorem nth_tail {n : ℕ} {α : Type u_1} (v : vector α (Nat.succ n)) (i : fin n) :
    nth (tail v) i = nth v (fin.succ i) :=
  sorry

@[simp] theorem tail_val {n : ℕ} {α : Type u_1} (v : vector α (Nat.succ n)) :
    subtype.val (tail v) = list.tail (subtype.val v) :=
  sorry

/-- The `tail` of a `nil` vector is `nil`. -/
@[simp] theorem tail_nil {α : Type u_1} : tail nil = nil := rfl

/-- The `tail` of a vector made up of one element is `nil`. -/
@[simp] theorem singleton_tail {α : Type u_1} (v : vector α 1) : tail v = nil :=
  eq.mpr (id (propext (eq_iff_true_of_subsingleton (tail v) nil))) trivial

@[simp] theorem tail_of_fn {α : Type u_1} {n : ℕ} (f : fin (Nat.succ n) → α) :
    tail (of_fn f) = of_fn fun (i : fin (Nat.succ n - 1)) => f (fin.succ i) :=
  sorry

/-- The list that makes up a `vector` made up of a single element,
retrieved via `to_list`, is equal to the list of that single element. -/
@[simp] theorem to_list_singleton {α : Type u_1} (v : vector α 1) : to_list v = [head v] := sorry

/-- Mapping under `id` does not change a vector. -/
@[simp] theorem map_id {α : Type u_1} {n : ℕ} (v : vector α n) : map id v = v := sorry

theorem mem_iff_nth {n : ℕ} {α : Type u_1} {a : α} {v : vector α n} :
    a ∈ to_list v ↔ ∃ (i : fin n), nth v i = a :=
  sorry

theorem nodup_iff_nth_inj {n : ℕ} {α : Type u_1} {v : vector α n} :
    list.nodup (to_list v) ↔ function.injective (nth v) :=
  sorry

@[simp] theorem nth_mem {n : ℕ} {α : Type u_1} (i : fin n) (v : vector α n) : nth v i ∈ to_list v :=
  sorry

theorem head'_to_list {n : ℕ} {α : Type u_1} (v : vector α (Nat.succ n)) :
    list.head' (to_list v) = some (head v) :=
  sorry

def reverse {n : ℕ} {α : Type u_1} (v : vector α n) : vector α n :=
  { val := list.reverse (to_list v), property := sorry }

/-- The `list` of a vector after a `reverse`, retrieved by `to_list` is equal
to the `list.reverse` after retrieving a vector's `to_list`. -/
theorem to_list_reverse {n : ℕ} {α : Type u_1} {v : vector α n} :
    to_list (reverse v) = list.reverse (to_list v) :=
  rfl

@[simp] theorem nth_zero {n : ℕ} {α : Type u_1} (v : vector α (Nat.succ n)) : nth v 0 = head v :=
  sorry

@[simp] theorem head_of_fn {α : Type u_1} {n : ℕ} (f : fin (Nat.succ n) → α) :
    head (of_fn f) = f 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (head (of_fn f) = f 0)) (Eq.symm (nth_zero (of_fn f)))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (nth (of_fn f) 0 = f 0)) (nth_of_fn f 0))) (Eq.refl (f 0)))

@[simp] theorem nth_cons_zero {n : ℕ} {α : Type u_1} (a : α) (v : vector α n) : nth (a::ᵥv) 0 = a :=
  sorry

/-- Accessing the `nth` element of a vector made up
of one element `x : α` is `x` itself. -/
@[simp] theorem nth_cons_nil {α : Type u_1} {ix : fin 1} (x : α) : nth (x::ᵥnil) ix = x := sorry

@[simp] theorem nth_cons_succ {n : ℕ} {α : Type u_1} (a : α) (v : vector α n) (i : fin n) :
    nth (a::ᵥv) (fin.succ i) = nth v i :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (nth (a::ᵥv) (fin.succ i) = nth v i)) (Eq.symm (nth_tail (a::ᵥv) i))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (nth (tail (a::ᵥv)) i = nth v i)) (tail_cons a v)))
      (Eq.refl (nth v i)))

/-- The last element of a `vector`, given that the vector is at least one element. -/
def last {n : ℕ} {α : Type u_1} (v : vector α (n + 1)) : α := nth v (fin.last n)

/-- The last element of a `vector`, given that the vector is at least one element. -/
theorem last_def {n : ℕ} {α : Type u_1} {v : vector α (n + 1)} : last v = nth v (fin.last n) := rfl

/-- The `last` element of a vector is the `head` of the `reverse` vector. -/
theorem reverse_nth_zero {n : ℕ} {α : Type u_1} {v : vector α (n + 1)} :
    head (reverse v) = last v :=
  sorry

/--
Construct a `vector β (n + 1)` from a `vector α n` by scanning `f : β → α → β`
from the "left", that is, from 0 to `fin.last n`, using `b : β` as the starting value.
-/
def scanl {n : ℕ} {α : Type u_1} {β : Type u_2} (f : β → α → β) (b : β) (v : vector α n) :
    vector β (n + 1) :=
  { val := list.scanl f b (to_list v), property := sorry }

/-- Providing an empty vector to `scanl` gives the starting value `b : β`. -/
@[simp] theorem scanl_nil {α : Type u_1} {β : Type u_2} (f : β → α → β) (b : β) :
    scanl f b nil = b::ᵥnil :=
  rfl

/--
The recursive step of `scanl` splits a vector `x ::ᵥ v : vector α (n + 1)`
into the provided starting value `b : β` and the recursed `scanl`
`f b x : β` as the starting value.

This lemma is the `cons` version of `scanl_nth`.
-/
@[simp] theorem scanl_cons {n : ℕ} {α : Type u_1} {β : Type u_2} (f : β → α → β) (b : β)
    (v : vector α n) (x : α) : scanl f b (x::ᵥv) = b::ᵥscanl f (f b x) v :=
  sorry

/--
The underlying `list` of a `vector` after a `scanl` is the `list.scanl`
of the underlying `list` of the original `vector`.
-/
@[simp] theorem scanl_val {n : ℕ} {α : Type u_1} {β : Type u_2} (f : β → α → β) (b : β)
    {v : vector α n} : subtype.val (scanl f b v) = list.scanl f b (subtype.val v) :=
  sorry

/--
The `to_list` of a `vector` after a `scanl` is the `list.scanl`
of the `to_list` of the original `vector`.
-/
@[simp] theorem to_list_scanl {n : ℕ} {α : Type u_1} {β : Type u_2} (f : β → α → β) (b : β)
    (v : vector α n) : to_list (scanl f b v) = list.scanl f b (to_list v) :=
  rfl

/--
The recursive step of `scanl` splits a vector made up of a single element
`x ::ᵥ nil : vector α 1` into a `vector` of the provided starting value `b : β`
and the mapped `f b x : β` as the last value.
-/
@[simp] theorem scanl_singleton {α : Type u_1} {β : Type u_2} (f : β → α → β) (b : β)
    (v : vector α 1) : scanl f b v = b::ᵥf b (head v)::ᵥnil :=
  sorry

/--
The first element of `scanl` of a vector `v : vector α n`,
retrieved via `head`, is the starting value `b : β`.
-/
@[simp] theorem scanl_head {n : ℕ} {α : Type u_1} {β : Type u_2} (f : β → α → β) (b : β)
    (v : vector α n) : head (scanl f b v) = b :=
  sorry

/--
For an index `i : fin n`, the `nth` element of `scanl` of a
vector `v : vector α n` at `i.succ`, is equal to the application
function `f : β → α → β` of the `i.cast_succ` element of
`scanl f b v` and `nth v i`.

This lemma is the `nth` version of `scanl_cons`.
-/
@[simp] theorem scanl_nth {n : ℕ} {α : Type u_1} {β : Type u_2} (f : β → α → β) (b : β)
    (v : vector α n) (i : fin n) :
    nth (scanl f b v) (fin.succ i) = f (nth (scanl f b v) (coe_fn fin.cast_succ i)) (nth v i) :=
  sorry

def m_of_fn {m : Type u → Type u_1} [Monad m] {α : Type u} {n : ℕ} :
    (fin n → m α) → m (vector α n) :=
  sorry

theorem m_of_fn_pure {m : Type u_1 → Type u_2} [Monad m] [is_lawful_monad m] {α : Type u_1} {n : ℕ}
    (f : fin n → α) : (m_of_fn fun (i : fin n) => pure (f i)) = pure (of_fn f) :=
  sorry

def mmap {m : Type u → Type u_1} [Monad m] {α : Type u_2} {β : Type u} (f : α → m β) {n : ℕ} :
    vector α n → m (vector β n) :=
  sorry

@[simp] theorem mmap_nil {m : Type u_1 → Type u_2} [Monad m] {α : Type u_3} {β : Type u_1}
    (f : α → m β) : mmap f nil = pure nil :=
  rfl

@[simp] theorem mmap_cons {m : Type u_1 → Type u_2} [Monad m] {α : Type u_3} {β : Type u_1}
    (f : α → m β) (a : α) {n : ℕ} (v : vector α n) :
    mmap f (a::ᵥv) =
        do 
          let h' ← f a 
          let t' ← mmap f v 
          pure (h'::ᵥt') :=
  sorry

/-- Define `C v` by induction on `v : vector α (n + 1)`, a vector of
at least one element.
This function has two arguments: `h0` handles the base case on `C nil`,
and `hs` defines the inductive step using `∀ x : α, C v → C (x ::ᵥ v)`. -/
def induction_on {α : Type u_1} {n : ℕ} {C : {n : ℕ} → vector α n → Sort u_2} (v : vector α (n + 1))
    (h0 : C nil) (hs : {n : ℕ} → {x : α} → {w : vector α n} → C w → C (x::ᵥw)) : C v :=
  Nat.rec (fun (v : vector α (0 + 1)) => eq.mpr sorry (eq.mpr sorry (hs h0)))
    (fun (n : ℕ) (hn : (v : vector α (n + 1)) → C v) (v : vector α (Nat.succ n + 1)) =>
      eq.mpr sorry (hs (hn (tail v))))
    n v

def to_array {n : ℕ} {α : Type u_1} : vector α n → array n α := sorry

def insert_nth {n : ℕ} {α : Type u_1} (a : α) (i : fin (n + 1)) (v : vector α n) :
    vector α (n + 1) :=
  { val := list.insert_nth (↑i) a (subtype.val v), property := sorry }

theorem insert_nth_val {n : ℕ} {α : Type u_1} {a : α} {i : fin (n + 1)} {v : vector α n} :
    subtype.val (insert_nth a i v) = list.insert_nth (subtype.val i) a (subtype.val v) :=
  rfl

@[simp] theorem remove_nth_val {n : ℕ} {α : Type u_1} {i : fin n} {v : vector α n} :
    subtype.val (remove_nth i v) = list.remove_nth (subtype.val v) ↑i :=
  sorry

theorem remove_nth_insert_nth {n : ℕ} {α : Type u_1} {a : α} {v : vector α n} {i : fin (n + 1)} :
    remove_nth i (insert_nth a i v) = v :=
  subtype.eq (list.remove_nth_insert_nth (subtype.val i) (subtype.val v))

theorem remove_nth_insert_nth_ne {n : ℕ} {α : Type u_1} {a : α} {v : vector α (n + 1)}
    {i : fin (n + bit0 1)} {j : fin (n + bit0 1)} (h : i ≠ j) :
    remove_nth i (insert_nth a j v) =
        insert_nth a (fin.pred_above i j (ne.symm h)) (remove_nth (fin.pred_above j i h) v) :=
  sorry

theorem insert_nth_comm {n : ℕ} {α : Type u_1} (a : α) (b : α) (i : fin (n + 1)) (j : fin (n + 1))
    (h : i ≤ j) (v : vector α n) :
    insert_nth b (fin.succ j) (insert_nth a i v) =
        insert_nth a (coe_fn fin.cast_succ i) (insert_nth b j v) :=
  sorry

/-- `update_nth v n a` replaces the `n`th element of `v` with `a` -/
def update_nth {n : ℕ} {α : Type u_1} (v : vector α n) (i : fin n) (a : α) : vector α n :=
  { val := list.update_nth (subtype.val v) (subtype.val i) a, property := sorry }

@[simp] theorem nth_update_nth_same {n : ℕ} {α : Type u_1} (v : vector α n) (i : fin n) (a : α) :
    nth (update_nth v i a) i = a :=
  sorry

theorem nth_update_nth_of_ne {n : ℕ} {α : Type u_1} {v : vector α n} {i : fin n} {j : fin n}
    (h : i ≠ j) (a : α) : nth (update_nth v i a) j = nth v j :=
  sorry

theorem nth_update_nth_eq_if {n : ℕ} {α : Type u_1} {v : vector α n} {i : fin n} {j : fin n}
    (a : α) : nth (update_nth v i a) j = ite (i = j) a (nth v j) :=
  sorry

end vector


namespace vector


protected def traverse {n : ℕ} {F : Type u → Type u} [Applicative F] {α : Type u} {β : Type u}
    (f : α → F β) : vector α n → F (vector β n) :=
  sorry

@[simp] protected theorem traverse_def {n : ℕ} {F : Type u → Type u} [Applicative F]
    [is_lawful_applicative F] {α : Type u} {β : Type u} (f : α → F β) (x : α) (xs : vector α n) :
    vector.traverse f (x::ᵥxs) = cons <$> f x <*> vector.traverse f xs :=
  subtype.cases_on xs
    fun (xs : List α) (xs_property : list.length xs = n) =>
      eq.drec
        (Eq.refl (vector.traverse f (x::ᵥ{ val := xs, property := Eq.refl (list.length xs) })))
        xs_property

protected theorem id_traverse {n : ℕ} {α : Type u} (x : vector α n) : vector.traverse id.mk x = x :=
  sorry

protected theorem comp_traverse {n : ℕ} {F : Type u → Type u} {G : Type u → Type u} [Applicative F]
    [Applicative G] [is_lawful_applicative F] [is_lawful_applicative G] {α : Type u} {β : Type u}
    {γ : Type u} (f : β → F γ) (g : α → G β) (x : vector α n) :
    vector.traverse (functor.comp.mk ∘ Functor.map f ∘ g) x =
        functor.comp.mk (vector.traverse f <$> vector.traverse g x) :=
  sorry

protected theorem traverse_eq_map_id {n : ℕ} {α : Type u_1} {β : Type u_1} (f : α → β)
    (x : vector α n) : vector.traverse (id.mk ∘ f) x = id.mk (map f x) :=
  sorry

protected theorem naturality {n : ℕ} {F : Type u → Type u} {G : Type u → Type u} [Applicative F]
    [Applicative G] [is_lawful_applicative F] [is_lawful_applicative G]
    (η : applicative_transformation F G) {α : Type u} {β : Type u} (f : α → F β) (x : vector α n) :
    coe_fn η (vector β n) (vector.traverse f x) = vector.traverse (coe_fn η β ∘ f) x :=
  sorry

protected instance flip.traversable {n : ℕ} : traversable (flip vector n) :=
  traversable.mk vector.traverse

protected instance flip.is_lawful_traversable {n : ℕ} : is_lawful_traversable (flip vector n) :=
  is_lawful_traversable.mk vector.id_traverse vector.comp_traverse vector.traverse_eq_map_id
    vector.naturality

end Mathlib