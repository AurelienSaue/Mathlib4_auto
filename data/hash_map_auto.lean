/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.pnat.basic
import Mathlib.data.list.range
import Mathlib.data.array.lemmas
import Mathlib.algebra.group.default
import Mathlib.data.sigma.basic
import PostPort

universes u v w l u_1 

namespace Mathlib

/-!
# Hash maps

Defines a hash map data structure, representing a finite key-value map
with a value type that may depend on the key type.  The structure
requires a `nat`-valued hash function to associate keys to buckets.

## Main definitions

* `hash_map`: constructed with `mk_hash_map`.

## Implementation details

A hash map with key type `α` and (dependent) value type `β : α → Type*`
consists of an array of *buckets*, which are lists containing
key/value pairs for that bucket.  The hash function is taken modulo `n`
to assign keys to their respective bucket.  Because of this, some care
should be put into the hash function to ensure it evenly distributes
keys.

The bucket array is an `array`.  These have special VM support for
in-place modification if there is only ever one reference to them.  If
one takes special care to never keep references to old versions of a
hash map alive after updating it, then the hash map will be modified
in-place.  In this documentation, when we say a hash map is modified
in-place, we are assuming the API is being used in this manner.

When inserting (`hash_map.insert`), if the number of stored pairs (the
*size*) is going to exceed the number of buckets, then a new hash map
is first created with double the number of buckets and everything in
the old hash map is reinserted along with the new key/value pair.
Otherwise, the bucket array is modified in-place.  The amortized
running time of inserting $$n$$ elements into a hash map is $$O(n)$$.

When removing (`hash_map.erase`), the hash map is modified in-place.
The implementation does not reduce the number of buckets in the hash
map if the size gets too low.

## Tags

hash map

-/

/-- `bucket_array α β` is the underlying data type for `hash_map α β`,
  an array of linked lists of key-value pairs. -/
def bucket_array (α : Type u) (β : α → Type v) (n : ℕ+)  :=
  array (↑n) (List (sigma fun (a : α) => β a))

/-- Make a hash_map index from a `nat` hash value and a (positive) buffer size -/
def hash_map.mk_idx (n : ℕ+) (i : ℕ) : fin ↑n :=
  { val := i % ↑n, property := sorry }

namespace bucket_array


protected instance inhabited {α : Type u} {β : α → Type v} {n : ℕ+} : Inhabited (bucket_array α β n) :=
  { default := mk_array ↑n [] }

/-- Read the bucket corresponding to an element -/
def read {α : Type u} {β : α → Type v} (hash_fn : α → ℕ) {n : ℕ+} (data : bucket_array α β n) (a : α) : List (sigma fun (a : α) => β a) :=
  let bidx : fin ↑n := hash_map.mk_idx n (hash_fn a);
  array.read data bidx

/-- Write the bucket corresponding to an element -/
def write {α : Type u} {β : α → Type v} (hash_fn : α → ℕ) {n : ℕ+} (data : bucket_array α β n) (a : α) (l : List (sigma fun (a : α) => β a)) : bucket_array α β n :=
  let bidx : fin ↑n := hash_map.mk_idx n (hash_fn a);
  array.write data bidx l

/-- Modify (read, apply `f`, and write) the bucket corresponding to an element -/
def modify {α : Type u} {β : α → Type v} (hash_fn : α → ℕ) {n : ℕ+} (data : bucket_array α β n) (a : α) (f : List (sigma fun (a : α) => β a) → List (sigma fun (a : α) => β a)) : bucket_array α β n :=
  let bidx : fin ↑n := hash_map.mk_idx n (hash_fn a);
  array.write data bidx (f (array.read data bidx))

/-- The list of all key-value pairs in the bucket list -/
def as_list {α : Type u} {β : α → Type v} {n : ℕ+} (data : bucket_array α β n) : List (sigma fun (a : α) => β a) :=
  list.join (array.to_list data)

theorem mem_as_list {α : Type u} {β : α → Type v} {n : ℕ+} (data : bucket_array α β n) {a : sigma fun (a : α) => β a} : a ∈ as_list data ↔ ∃ (i : fin ↑n), a ∈ array.read data i := sorry

/-- Fold a function `f` over the key-value pairs in the bucket list -/
def foldl {α : Type u} {β : α → Type v} {n : ℕ+} (data : bucket_array α β n) {δ : Type w} (d : δ) (f : δ → (a : α) → β a → δ) : δ :=
  array.foldl data d
    fun (b : List (sigma fun (a : α) => β a)) (d : δ) =>
      list.foldl (fun (r : δ) (a : sigma fun (a : α) => β a) => f r (sigma.fst a) (sigma.snd a)) d b

theorem foldl_eq {α : Type u} {β : α → Type v} {n : ℕ+} (data : bucket_array α β n) {δ : Type w} (d : δ) (f : δ → (a : α) → β a → δ) : foldl data d f =
  list.foldl (fun (r : δ) (a : sigma fun (a : α) => β a) => f r (sigma.fst a) (sigma.snd a)) d (as_list data) := sorry

end bucket_array


namespace hash_map


/-- Insert the pair `⟨a, b⟩` into the correct location in the bucket array
  (without checking for duplication) -/
def reinsert_aux {α : Type u} {β : α → Type v} (hash_fn : α → ℕ) {n : ℕ+} (data : bucket_array α β n) (a : α) (b : β a) : bucket_array α β n :=
  bucket_array.modify hash_fn data a fun (l : List (sigma fun (a : α) => β a)) => sigma.mk a b :: l

theorem mk_as_list {α : Type u} {β : α → Type v} (n : ℕ+) : bucket_array.as_list (mk_array ↑n []) = [] := sorry

/-- Search a bucket for a key `a` and return the value -/
def find_aux {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) : List (sigma fun (a : α) => β a) → Option (β a) :=
  sorry

theorem find_aux_iff {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {b : β a} {l : List (sigma fun (a : α) => β a)} : list.nodup (list.map sigma.fst l) → (find_aux a l = some b ↔ sigma.mk a b ∈ l) := sorry

/-- Returns `tt` if the bucket `l` contains the key `a` -/
def contains_aux {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) (l : List (sigma fun (a : α) => β a)) : Bool :=
  option.is_some (find_aux a l)

theorem contains_aux_iff {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {l : List (sigma fun (a : α) => β a)} (nd : list.nodup (list.map sigma.fst l)) : ↥(contains_aux a l) ↔ a ∈ list.map sigma.fst l := sorry

/-- Modify a bucket to replace a value in the list. Leaves the list
 unchanged if the key is not found. -/
def replace_aux {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) (b : β a) : List (sigma fun (a : α) => β a) → List (sigma fun (a : α) => β a) :=
  sorry

/-- Modify a bucket to remove a key, if it exists. -/
def erase_aux {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) : List (sigma fun (a : α) => β a) → List (sigma fun (a : α) => β a) :=
  sorry

/-- The predicate `valid bkts sz` means that `bkts` satisfies the `hash_map`
  invariants: There are exactly `sz` elements in it, every pair is in the
  bucket determined by its key and the hash function, and no key appears
  multiple times in the list. -/
structure valid {α : Type u} {β : α → Type v} (hash_fn : α → ℕ) [DecidableEq α] {n : ℕ+} (bkts : bucket_array α β n) (sz : ℕ) 
where
  len : list.length (bucket_array.as_list bkts) = sz
  idx : ∀ {i : fin ↑n} {a : sigma fun (a : α) => β a}, a ∈ array.read bkts i → mk_idx n (hash_fn (sigma.fst a)) = i
  nodup : ∀ (i : fin ↑n), list.nodup (list.map sigma.fst (array.read bkts i))

theorem valid.idx_enum {α : Type u} {β : α → Type v} (hash_fn : α → ℕ) [DecidableEq α] {n : ℕ+} {bkts : bucket_array α β n} {sz : ℕ} (v : valid hash_fn bkts sz) {i : ℕ} {l : List (sigma fun (a : α) => β a)} (he : (i, l) ∈ list.enum (array.to_list bkts)) {a : α} {b : β a} (hl : sigma.mk a b ∈ l) : ∃ (h : i < ↑n), mk_idx n (hash_fn a) = { val := i, property := h } := sorry

theorem valid.idx_enum_1 {α : Type u} {β : α → Type v} (hash_fn : α → ℕ) [DecidableEq α] {n : ℕ+} {bkts : bucket_array α β n} {sz : ℕ} (v : valid hash_fn bkts sz) {i : ℕ} {l : List (sigma fun (a : α) => β a)} (he : (i, l) ∈ list.enum (array.to_list bkts)) {a : α} {b : β a} (hl : sigma.mk a b ∈ l) : subtype.val (mk_idx n (hash_fn a)) = i := sorry

theorem valid.as_list_nodup {α : Type u} {β : α → Type v} (hash_fn : α → ℕ) [DecidableEq α] {n : ℕ+} {bkts : bucket_array α β n} {sz : ℕ} (v : valid hash_fn bkts sz) : list.nodup (list.map sigma.fst (bucket_array.as_list bkts)) := sorry

theorem mk_valid {α : Type u} {β : α → Type v} (hash_fn : α → ℕ) [DecidableEq α] (n : ℕ+) : valid hash_fn (mk_array ↑n []) 0 := sorry

theorem valid.find_aux_iff {α : Type u} {β : α → Type v} (hash_fn : α → ℕ) [DecidableEq α] {n : ℕ+} {bkts : bucket_array α β n} {sz : ℕ} (v : valid hash_fn bkts sz) {a : α} {b : β a} : find_aux a (bucket_array.read hash_fn bkts a) = some b ↔ sigma.mk a b ∈ bucket_array.as_list bkts := sorry

theorem valid.contains_aux_iff {α : Type u} {β : α → Type v} (hash_fn : α → ℕ) [DecidableEq α] {n : ℕ+} {bkts : bucket_array α β n} {sz : ℕ} (v : valid hash_fn bkts sz) (a : α) : ↥(contains_aux a (bucket_array.read hash_fn bkts a)) ↔ a ∈ list.map sigma.fst (bucket_array.as_list bkts) := sorry

theorem append_of_modify {α : Type u} {β : α → Type v} [DecidableEq α] {n : ℕ+} {bkts : bucket_array α β n} {bidx : fin ↑n} {f : List (sigma fun (a : α) => β a) → List (sigma fun (a : α) => β a)} (u : List (sigma fun (a : α) => β a)) (v1 : List (sigma fun (a : α) => β a)) (v2 : List (sigma fun (a : α) => β a)) (w : List (sigma fun (a : α) => β a)) (hl : array.read bkts bidx = u ++ v1 ++ w) (hfl : f (array.read bkts bidx) = u ++ v2 ++ w) : ∃ (u' : List (sigma fun (a : α) => β a)),
  ∃ (w' : List (sigma fun (a : α) => β a)),
    bucket_array.as_list bkts = u' ++ v1 ++ w' ∧ bucket_array.as_list bkts' = u' ++ v2 ++ w' := sorry

theorem valid.modify {α : Type u} {β : α → Type v} (hash_fn : α → ℕ) [DecidableEq α] {n : ℕ+} {bkts : bucket_array α β n} {bidx : fin ↑n} {f : List (sigma fun (a : α) => β a) → List (sigma fun (a : α) => β a)} (u : List (sigma fun (a : α) => β a)) (v1 : List (sigma fun (a : α) => β a)) (v2 : List (sigma fun (a : α) => β a)) (w : List (sigma fun (a : α) => β a)) (hl : array.read bkts bidx = u ++ v1 ++ w) (hfl : f (array.read bkts bidx) = u ++ v2 ++ w) (hvnd : list.nodup (list.map sigma.fst v2)) (hal : ∀ (a : sigma fun (a : α) => β a), a ∈ v2 → mk_idx n (hash_fn (sigma.fst a)) = bidx) (djuv : list.disjoint (list.map sigma.fst u) (list.map sigma.fst v2)) (djwv : list.disjoint (list.map sigma.fst w) (list.map sigma.fst v2)) {sz : ℕ} (v : valid hash_fn bkts sz) : list.length v1 ≤ sz + list.length v2 ∧ valid hash_fn bkts' (sz + list.length v2 - list.length v1) := sorry

theorem valid.replace_aux {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) (b : β a) (l : List (sigma fun (a : α) => β a)) : a ∈ list.map sigma.fst l →
  ∃ (u : List (sigma fun (a : α) => β a)),
    ∃ (w : List (sigma fun (a : α) => β a)),
      ∃ (b' : β a), l = u ++ [sigma.mk a b'] ++ w ∧ replace_aux a b l = u ++ [sigma.mk a b] ++ w := sorry

theorem valid.replace {α : Type u} {β : α → Type v} (hash_fn : α → ℕ) [DecidableEq α] {n : ℕ+} {bkts : bucket_array α β n} {sz : ℕ} (a : α) (b : β a) (Hc : ↥(contains_aux a (bucket_array.read hash_fn bkts a))) (v : valid hash_fn bkts sz) : valid hash_fn (bucket_array.modify hash_fn bkts a (replace_aux a b)) sz := sorry

theorem valid.insert {α : Type u} {β : α → Type v} (hash_fn : α → ℕ) [DecidableEq α] {n : ℕ+} {bkts : bucket_array α β n} {sz : ℕ} (a : α) (b : β a) (Hnc : ¬↥(contains_aux a (bucket_array.read hash_fn bkts a))) (v : valid hash_fn bkts sz) : valid hash_fn (reinsert_aux hash_fn bkts a b) (sz + 1) := sorry

theorem valid.erase_aux {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) (l : List (sigma fun (a : α) => β a)) : a ∈ list.map sigma.fst l →
  ∃ (u : List (sigma fun (a : α) => β a)),
    ∃ (w : List (sigma fun (a : α) => β a)), ∃ (b : β a), l = u ++ [sigma.mk a b] ++ w ∧ erase_aux a l = u ++ [] ++ w := sorry

theorem valid.erase {α : Type u} {β : α → Type v} (hash_fn : α → ℕ) [DecidableEq α] {n : ℕ+} {bkts : bucket_array α β n} {sz : ℕ} (a : α) (Hc : ↥(contains_aux a (bucket_array.read hash_fn bkts a))) (v : valid hash_fn bkts sz) : valid hash_fn (bucket_array.modify hash_fn bkts a (erase_aux a)) (sz - 1) := sorry

end hash_map


/-- A hash map data structure, representing a finite key-value map
  with key type `α` and value type `β` (which may depend on `α`). -/
structure hash_map (α : Type u) [DecidableEq α] (β : α → Type v) 
where
  hash_fn : α → ℕ
  size : ℕ
  nbuckets : ℕ+
  buckets : bucket_array α β nbuckets
  is_valid : hash_map.valid hash_fn buckets size

/-- Construct an empty hash map with buffer size `nbuckets` (default 8). -/
def mk_hash_map {α : Type u} [DecidableEq α] {β : α → Type v} (hash_fn : α → ℕ) (nbuckets : optParam ℕ (bit0 (bit0 (bit0 1)))) : hash_map α β :=
  let n : optParam ℕ (bit0 (bit0 (bit0 1))) := ite (nbuckets = 0) (bit0 (bit0 (bit0 1))) nbuckets;
  let nz : n > 0 := sorry;
  hash_map.mk hash_fn 0 { val := n, property := nz } (mk_array n []) sorry

namespace hash_map


/-- Return the value corresponding to a key, or `none` if not found -/
def find {α : Type u} {β : α → Type v} [DecidableEq α] (m : hash_map α β) (a : α) : Option (β a) :=
  find_aux a (bucket_array.read (hash_fn m) (buckets m) a)

/-- Return `tt` if the key exists in the map -/
def contains {α : Type u} {β : α → Type v} [DecidableEq α] (m : hash_map α β) (a : α) : Bool :=
  option.is_some (find m a)

protected instance has_mem {α : Type u} {β : α → Type v} [DecidableEq α] : has_mem α (hash_map α β) :=
  has_mem.mk fun (a : α) (m : hash_map α β) => ↥(contains m a)

/-- Fold a function over the key-value pairs in the map -/
def fold {α : Type u} {β : α → Type v} [DecidableEq α] {δ : Type w} (m : hash_map α β) (d : δ) (f : δ → (a : α) → β a → δ) : δ :=
  bucket_array.foldl (buckets m) d f

/-- The list of key-value pairs in the map -/
def entries {α : Type u} {β : α → Type v} [DecidableEq α] (m : hash_map α β) : List (sigma fun (a : α) => β a) :=
  bucket_array.as_list (buckets m)

/-- The list of keys in the map -/
def keys {α : Type u} {β : α → Type v} [DecidableEq α] (m : hash_map α β) : List α :=
  list.map sigma.fst (entries m)

theorem find_iff {α : Type u} {β : α → Type v} [DecidableEq α] (m : hash_map α β) (a : α) (b : β a) : find m a = some b ↔ sigma.mk a b ∈ entries m :=
  valid.find_aux_iff (hash_fn m) (is_valid m)

theorem contains_iff {α : Type u} {β : α → Type v} [DecidableEq α] (m : hash_map α β) (a : α) : ↥(contains m a) ↔ a ∈ keys m :=
  valid.contains_aux_iff (hash_fn m) (is_valid m) a

theorem entries_empty {α : Type u} {β : α → Type v} [DecidableEq α] (hash_fn : α → ℕ) (n : optParam ℕ (bit0 (bit0 (bit0 1)))) : entries (mk_hash_map hash_fn n) = [] :=
  mk_as_list (nbuckets (mk_hash_map hash_fn n))

theorem keys_empty {α : Type u} {β : α → Type v} [DecidableEq α] (hash_fn : α → ℕ) (n : optParam ℕ (bit0 (bit0 (bit0 1)))) : keys (mk_hash_map hash_fn n) = [] := sorry

theorem find_empty {α : Type u} {β : α → Type v} [DecidableEq α] (hash_fn : α → ℕ) (n : optParam ℕ (bit0 (bit0 (bit0 1)))) (a : α) : find (mk_hash_map hash_fn n) a = none := sorry

theorem not_contains_empty {α : Type u} {β : α → Type v} [DecidableEq α] (hash_fn : α → ℕ) (n : optParam ℕ (bit0 (bit0 (bit0 1)))) (a : α) : ¬↥(contains (mk_hash_map hash_fn n) a) := sorry

theorem insert_lemma {α : Type u} {β : α → Type v} [DecidableEq α] (hash_fn : α → ℕ) {n : ℕ+} {n' : ℕ+} {bkts : bucket_array α β n} {sz : ℕ} (v : valid hash_fn bkts sz) : valid hash_fn (bucket_array.foldl bkts (mk_array ↑n' []) (reinsert_aux hash_fn)) sz := sorry

/-- Insert a key-value pair into the map. (Modifies `m` in-place when applicable) -/
def insert {α : Type u} {β : α → Type v} [DecidableEq α] (m : hash_map α β) (a : α) (b : β a) : hash_map α β :=
  sorry

theorem mem_insert {α : Type u} {β : α → Type v} [DecidableEq α] (m : hash_map α β) (a : α) (b : β a) (a' : α) (b' : β a') : sigma.mk a' b' ∈ entries (insert m a b) ↔ ite (a = a') (b == b') (sigma.mk a' b' ∈ entries m) := sorry

theorem find_insert_eq {α : Type u} {β : α → Type v} [DecidableEq α] (m : hash_map α β) (a : α) (b : β a) : find (insert m a b) a = some b :=
  iff.mpr (find_iff (insert m a b) a b)
    (iff.mpr (mem_insert m a b a b)
      (eq.mpr (id (Eq._oldrec (Eq.refl (ite (a = a) (b == b) (sigma.mk a b ∈ entries m))) (if_pos rfl))) (HEq.refl b)))

theorem find_insert_ne {α : Type u} {β : α → Type v} [DecidableEq α] (m : hash_map α β) (a : α) (a' : α) (b : β a) (h : a ≠ a') : find (insert m a b) a' = find m a' := sorry

theorem find_insert {α : Type u} {β : α → Type v} [DecidableEq α] (m : hash_map α β) (a' : α) (a : α) (b : β a) : find (insert m a b) a' = dite (a = a') (fun (h : a = a') => some (eq.rec_on h b)) fun (h : ¬a = a') => find m a' := sorry

/-- Insert a list of key-value pairs into the map. (Modifies `m` in-place when applicable) -/
def insert_all {α : Type u} {β : α → Type v} [DecidableEq α] (l : List (sigma fun (a : α) => β a)) (m : hash_map α β) : hash_map α β :=
  list.foldl (fun (m : hash_map α β) (_x : sigma fun (a : α) => β a) => sorry) m l

/-- Construct a hash map from a list of key-value pairs. -/
def of_list {α : Type u} {β : α → Type v} [DecidableEq α] (l : List (sigma fun (a : α) => β a)) (hash_fn : α → ℕ) : hash_map α β :=
  insert_all l (mk_hash_map hash_fn (bit0 1 * list.length l))

/-- Remove a key from the map. (Modifies `m` in-place when applicable) -/
def erase {α : Type u} {β : α → Type v} [DecidableEq α] (m : hash_map α β) (a : α) : hash_map α β :=
  sorry

theorem mem_erase {α : Type u} {β : α → Type v} [DecidableEq α] (m : hash_map α β) (a : α) (a' : α) (b' : β a') : sigma.mk a' b' ∈ entries (erase m a) ↔ a ≠ a' ∧ sigma.mk a' b' ∈ entries m := sorry

theorem find_erase_eq {α : Type u} {β : α → Type v} [DecidableEq α] (m : hash_map α β) (a : α) : find (erase m a) a = none := sorry

theorem find_erase_ne {α : Type u} {β : α → Type v} [DecidableEq α] (m : hash_map α β) (a : α) (a' : α) (h : a ≠ a') : find (erase m a) a' = find m a' := sorry

theorem find_erase {α : Type u} {β : α → Type v} [DecidableEq α] (m : hash_map α β) (a' : α) (a : α) : find (erase m a) a' = ite (a = a') none (find m a') := sorry

protected instance has_to_string {α : Type u} {β : α → Type v} [DecidableEq α] [has_to_string α] [(a : α) → has_to_string (β a)] : has_to_string (hash_map α β) :=
  has_to_string.mk to_string

/-- `hash_map` with key type `nat` and value type that may vary. -/
protected instance inhabited {β : ℕ → Type u_1} : Inhabited (hash_map ℕ β) :=
  { default := mk_hash_map id }

