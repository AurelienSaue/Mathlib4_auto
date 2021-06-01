/-
Copyright (c) 2020 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.string.basic
import Mathlib.PostPort

namespace Mathlib

/-!
# Parsers

`parser α` is the type that describes a computation that can ingest a `char_buffer`
and output, if successful, a term of type `α`.
This file expands on the definitions in the core library, proving that all the core library
parsers are `valid`. There are also lemmas on the composability of parsers.

## Main definitions

* `parse_result.pos` : The position of a `char_buffer` at which a `parser α` has finished.
* `parser.valid` : The property that a parser only moves forward within a buffer,
  in both cases of success or failure.

## Implementation details

Lemmas about how parsers are valid are in the `valid` namespace. That allows using projection
notation for shorter term proofs that are parallel to the definitions of the parsers in structure.

-/

/--
For some `parse_result α`, give the position at which the result was provided, in either the
`done` or the `fail` case.
-/
@[simp] def parse_result.pos {α : Type} : parse_result α → ℕ := sorry

namespace parser


/--
A `parser α` is defined to be `valid` if the result `p cb n` it gives,
for some `cb : char_buffer` and `n : ℕ`, (whether `done` or `fail`),
is always at a `parse_result.pos` that is at least `n`. Additionally, if the position of the result
of the parser was within the size of the `cb`, then the input to the parser must have been within
`cb.size` too.
-/
def valid {α : Type} (p : parser α) :=
  ∀ (cb : char_buffer) (n : ℕ),
    n ≤ parse_result.pos (p cb n) ∧
      (parse_result.pos (p cb n) ≤ buffer.size cb → n ≤ buffer.size cb)

theorem fail_iff {α : Type} (p : parser α) (cb : char_buffer) (n : ℕ) :
    (∀ (pos' : ℕ) (result : α), p cb n ≠ parse_result.done pos' result) ↔
        ∃ (pos' : ℕ), ∃ (err : dlist string), p cb n = parse_result.fail pos' err :=
  sorry

theorem success_iff {α : Type} (p : parser α) (cb : char_buffer) (n : ℕ) :
    (∀ (pos' : ℕ) (err : dlist string), p cb n ≠ parse_result.fail pos' err) ↔
        ∃ (pos' : ℕ), ∃ (result : α), p cb n = parse_result.done pos' result :=
  sorry

theorem decorate_errors_fail {α : Type} {msgs : thunk (List string)} {p : parser α}
    {cb : char_buffer} {n : ℕ} {n' : ℕ} {err : dlist string}
    (h : p cb n = parse_result.fail n' err) :
    decorate_errors msgs p cb n =
        parse_result.fail n (dlist.lazy_of_list fun (_ : Unit) => msgs Unit.unit) :=
  sorry

theorem decorate_errors_success {α : Type} {msgs : thunk (List string)} {p : parser α}
    {cb : char_buffer} {n : ℕ} {n' : ℕ} {a : α} (h : p cb n = parse_result.done n' a) :
    decorate_errors msgs p cb n = parse_result.done n' a :=
  sorry

theorem decorate_error_fail {α : Type} {msg : thunk string} {p : parser α} {cb : char_buffer}
    {n : ℕ} {n' : ℕ} {err : dlist string} (h : p cb n = parse_result.fail n' err) :
    decorate_error msg p cb n =
        parse_result.fail n (dlist.lazy_of_list fun (_ : Unit) => [msg Unit.unit]) :=
  decorate_errors_fail h

theorem decorate_error_success {α : Type} {msg : thunk string} {p : parser α} {cb : char_buffer}
    {n : ℕ} {n' : ℕ} {a : α} (h : p cb n = parse_result.done n' a) :
    decorate_error msg p cb n = parse_result.done n' a :=
  decorate_errors_success h

@[simp] theorem decorate_errors_eq_done {α : Type} {msgs : thunk (List string)} {p : parser α}
    {cb : char_buffer} {n : ℕ} {n' : ℕ} {a : α} :
    decorate_errors msgs p cb n = parse_result.done n' a ↔ p cb n = parse_result.done n' a :=
  sorry

@[simp] theorem decorate_error_eq_done {α : Type} {msg : thunk string} {p : parser α}
    {cb : char_buffer} {n : ℕ} {n' : ℕ} {a : α} :
    decorate_error msg p cb n = parse_result.done n' a ↔ p cb n = parse_result.done n' a :=
  decorate_errors_eq_done

@[simp] theorem decorate_errors_eq_fail {α : Type} {msgs : thunk (List string)} {p : parser α}
    {cb : char_buffer} {n : ℕ} {err : dlist string} :
    decorate_errors msgs p cb n = parse_result.fail n err ↔
        (err = dlist.lazy_of_list fun (_ : Unit) => msgs Unit.unit) ∧
          ∃ (np : ℕ), ∃ (err' : dlist string), p cb n = parse_result.fail np err' :=
  sorry

@[simp] theorem decorate_error_eq_fail {α : Type} {msg : thunk string} {p : parser α}
    {cb : char_buffer} {n : ℕ} {err : dlist string} :
    decorate_error msg p cb n = parse_result.fail n err ↔
        (err = dlist.lazy_of_list fun (_ : Unit) => [msg Unit.unit]) ∧
          ∃ (np : ℕ), ∃ (err' : dlist string), p cb n = parse_result.fail np err' :=
  decorate_errors_eq_fail

@[simp] theorem return_eq_pure {α : Type} {a : α} : return a = pure a := rfl

theorem pure_eq_done {α : Type} {a : α} :
    pure a = fun (_x : char_buffer) (n : ℕ) => parse_result.done n a :=
  rfl

@[simp] theorem pure_ne_fail {α : Type} {cb : char_buffer} {n : ℕ} {n' : ℕ} {err : dlist string}
    {a : α} : pure a cb n ≠ parse_result.fail n' err :=
  sorry

@[simp] theorem bind_eq_bind {α : Type} {β : Type} {p : parser α} (f : α → parser β) :
    parser.bind p f = p >>= f :=
  rfl

@[simp] theorem bind_eq_done {α : Type} {β : Type} {p : parser α} {cb : char_buffer} {n : ℕ}
    {n' : ℕ} {b : β} {f : α → parser β} :
    bind p f cb n = parse_result.done n' b ↔
        ∃ (np : ℕ),
          ∃ (a : α), p cb n = parse_result.done np a ∧ f a cb np = parse_result.done n' b :=
  sorry

@[simp] theorem bind_eq_fail {α : Type} {β : Type} {p : parser α} {cb : char_buffer} {n : ℕ}
    {n' : ℕ} {err : dlist string} {f : α → parser β} :
    bind p f cb n = parse_result.fail n' err ↔
        p cb n = parse_result.fail n' err ∨
          ∃ (np : ℕ),
            ∃ (a : α), p cb n = parse_result.done np a ∧ f a cb np = parse_result.fail n' err :=
  sorry

@[simp] theorem and_then_eq_bind {α : Type} {β : Type} {m : Type → Type} [Monad m] (a : m α)
    (b : m β) :
    a >> b =
        do 
          a 
          b :=
  rfl

theorem and_then_fail {α : Type} {p : parser α} {cb : char_buffer} {n : ℕ} {n' : ℕ}
    {err : dlist string} :
    has_bind.and_then p (return Unit.unit) cb n = parse_result.fail n' err ↔
        p cb n = parse_result.fail n' err :=
  sorry

theorem and_then_success {α : Type} {p : parser α} {cb : char_buffer} {n : ℕ} {n' : ℕ} :
    has_bind.and_then p (return Unit.unit) cb n = parse_result.done n' Unit.unit ↔
        ∃ (a : α), p cb n = parse_result.done n' a :=
  sorry

@[simp] theorem map_eq_done {α : Type} {β : Type} {p : parser α} {cb : char_buffer} {n : ℕ} {n' : ℕ}
    {b : β} {f : α → β} :
    Functor.map f p cb n = parse_result.done n' b ↔
        ∃ (a : α), p cb n = parse_result.done n' a ∧ f a = b :=
  sorry

@[simp] theorem map_eq_fail {α : Type} {β : Type} {p : parser α} {cb : char_buffer} {n : ℕ} {n' : ℕ}
    {err : dlist string} {f : α → β} :
    Functor.map f p cb n = parse_result.fail n' err ↔ p cb n = parse_result.fail n' err :=
  sorry

@[simp] theorem map_const_eq_done {α : Type} {β : Type} {p : parser α} {cb : char_buffer} {n : ℕ}
    {n' : ℕ} {b : β} {b' : β} :
    Functor.mapConst b p cb n = parse_result.done n' b' ↔
        ∃ (a : α), p cb n = parse_result.done n' a ∧ b = b' :=
  sorry

@[simp] theorem map_const_eq_fail {α : Type} {β : Type} {p : parser α} {cb : char_buffer} {n : ℕ}
    {n' : ℕ} {err : dlist string} {b : β} :
    Functor.mapConst b p cb n = parse_result.fail n' err ↔ p cb n = parse_result.fail n' err :=
  sorry

theorem map_const_rev_eq_done {α : Type} {β : Type} {p : parser α} {cb : char_buffer} {n : ℕ}
    {n' : ℕ} {b : β} {b' : β} :
    functor.map_const_rev p b cb n = parse_result.done n' b' ↔
        ∃ (a : α), p cb n = parse_result.done n' a ∧ b = b' :=
  map_const_eq_done

theorem map_rev_const_eq_fail {α : Type} {β : Type} {p : parser α} {cb : char_buffer} {n : ℕ}
    {n' : ℕ} {err : dlist string} {b : β} :
    functor.map_const_rev p b cb n = parse_result.fail n' err ↔ p cb n = parse_result.fail n' err :=
  map_const_eq_fail

@[simp] theorem orelse_eq_orelse {α : Type} {p : parser α} {q : parser α} :
    parser.orelse p q = (p <|> q) :=
  rfl

@[simp] theorem orelse_eq_done {α : Type} {p : parser α} {q : parser α} {cb : char_buffer} {n : ℕ}
    {n' : ℕ} {a : α} :
    has_orelse.orelse p q cb n = parse_result.done n' a ↔
        p cb n = parse_result.done n' a ∨
          q cb n = parse_result.done n' a ∧
            ∃ (err : dlist string), p cb n = parse_result.fail n err :=
  sorry

@[simp] theorem orelse_eq_fail_eq {α : Type} {p : parser α} {q : parser α} {cb : char_buffer}
    {n : ℕ} {err : dlist string} :
    has_orelse.orelse p q cb n = parse_result.fail n err ↔
        (p cb n = parse_result.fail n err ∧
            ∃ (nq : ℕ), ∃ (errq : dlist string), n < nq ∧ q cb n = parse_result.fail nq errq) ∨
          ∃ (errp : dlist string),
            ∃ (errq : dlist string),
              p cb n = parse_result.fail n errp ∧
                q cb n = parse_result.fail n errq ∧ errp ++ errq = err :=
  sorry

theorem orelse_eq_fail_invalid_lt {α : Type} {p : parser α} {q : parser α} {cb : char_buffer}
    {n : ℕ} {n' : ℕ} {err : dlist string} (hn : n' < n) :
    has_orelse.orelse p q cb n = parse_result.fail n' err ↔
        p cb n = parse_result.fail n' err ∨
          q cb n = parse_result.fail n' err ∧
            ∃ (errp : dlist string), p cb n = parse_result.fail n errp :=
  sorry

theorem orelse_eq_fail_of_valid_ne {α : Type} {p : parser α} {q : parser α} {cb : char_buffer}
    {n : ℕ} {n' : ℕ} {err : dlist string} (hv : valid q) (hn : n ≠ n') :
    has_orelse.orelse p q cb n = parse_result.fail n' err ↔ p cb n = parse_result.fail n' err :=
  sorry

@[simp] theorem failure_eq_failure {α : Type} : parser.failure = failure := rfl

@[simp] theorem failure_def {α : Type} {cb : char_buffer} {n : ℕ} :
    failure cb n = parse_result.fail n dlist.empty :=
  rfl

theorem not_failure_eq_done {α : Type} {cb : char_buffer} {n : ℕ} {n' : ℕ} {a : α} :
    ¬failure cb n = parse_result.done n' a :=
  sorry

theorem failure_eq_fail {α : Type} {cb : char_buffer} {n : ℕ} {n' : ℕ} {err : dlist string} :
    failure cb n = parse_result.fail n' err ↔ n = n' ∧ err = dlist.empty :=
  sorry

theorem seq_eq_done {α : Type} {β : Type} {cb : char_buffer} {n : ℕ} {n' : ℕ} {b : β}
    {f : parser (α → β)} {p : parser α} :
    Seq.seq f p cb n = parse_result.done n' b ↔
        ∃ (nf : ℕ),
          ∃ (f' : α → β),
            ∃ (a : α),
              f cb n = parse_result.done nf f' ∧ p cb nf = parse_result.done n' a ∧ f' a = b :=
  sorry

theorem seq_eq_fail {α : Type} {β : Type} {cb : char_buffer} {n : ℕ} {n' : ℕ} {err : dlist string}
    {f : parser (α → β)} {p : parser α} :
    Seq.seq f p cb n = parse_result.fail n' err ↔
        f cb n = parse_result.fail n' err ∨
          ∃ (nf : ℕ),
            ∃ (f' : α → β), f cb n = parse_result.done nf f' ∧ p cb nf = parse_result.fail n' err :=
  sorry

theorem seq_left_eq_done {α : Type} {β : Type} {cb : char_buffer} {n : ℕ} {n' : ℕ} {a : α}
    {p : parser α} {q : parser β} :
    SeqLeft.seqLeft p q cb n = parse_result.done n' a ↔
        ∃ (np : ℕ), ∃ (b : β), p cb n = parse_result.done np a ∧ q cb np = parse_result.done n' b :=
  sorry

theorem seq_left_eq_fail {α : Type} {β : Type} {cb : char_buffer} {n : ℕ} {n' : ℕ}
    {err : dlist string} {p : parser α} {q : parser β} :
    SeqLeft.seqLeft p q cb n = parse_result.fail n' err ↔
        p cb n = parse_result.fail n' err ∨
          ∃ (np : ℕ),
            ∃ (a : α), p cb n = parse_result.done np a ∧ q cb np = parse_result.fail n' err :=
  sorry

theorem seq_right_eq_done {α : Type} {β : Type} {cb : char_buffer} {n : ℕ} {n' : ℕ} {b : β}
    {p : parser α} {q : parser β} :
    SeqRight.seqRight p q cb n = parse_result.done n' b ↔
        ∃ (np : ℕ), ∃ (a : α), p cb n = parse_result.done np a ∧ q cb np = parse_result.done n' b :=
  sorry

theorem seq_right_eq_fail {α : Type} {β : Type} {cb : char_buffer} {n : ℕ} {n' : ℕ}
    {err : dlist string} {p : parser α} {q : parser β} :
    SeqRight.seqRight p q cb n = parse_result.fail n' err ↔
        p cb n = parse_result.fail n' err ∨
          ∃ (np : ℕ),
            ∃ (a : α), p cb n = parse_result.done np a ∧ q cb np = parse_result.fail n' err :=
  sorry

theorem mmap_eq_done {α : Type} {β : Type} {cb : char_buffer} {n : ℕ} {n' : ℕ} {f : α → parser β}
    {a : α} {l : List α} {b : β} {l' : List β} :
    mmap f (a :: l) cb n = parse_result.done n' (b :: l') ↔
        ∃ (np : ℕ), f a cb n = parse_result.done np b ∧ mmap f l cb np = parse_result.done n' l' :=
  sorry

theorem mmap'_eq_done {α : Type} {β : Type} {cb : char_buffer} {n : ℕ} {n' : ℕ} {f : α → parser β}
    {a : α} {l : List α} :
    mmap' f (a :: l) cb n = parse_result.done n' Unit.unit ↔
        ∃ (np : ℕ),
          ∃ (b : β),
            f a cb n = parse_result.done np b ∧ mmap' f l cb np = parse_result.done n' Unit.unit :=
  sorry

theorem guard_eq_done {cb : char_buffer} {n : ℕ} {n' : ℕ} {p : Prop} [Decidable p] :
    guard p cb n = parse_result.done n' Unit.unit ↔ p ∧ n = n' :=
  sorry

theorem guard_eq_fail {cb : char_buffer} {n : ℕ} {n' : ℕ} {err : dlist string} {p : Prop}
    [Decidable p] : guard p cb n = parse_result.fail n' err ↔ ¬p ∧ n = n' ∧ err = dlist.empty :=
  sorry

namespace valid


theorem mono_done {α : Type} {p : parser α} {cb : char_buffer} {n : ℕ} {n' : ℕ} {a : α}
    (hp : valid p) (h : p cb n = parse_result.done n' a) : n ≤ n' :=
  sorry

theorem mono_fail {α : Type} {p : parser α} {cb : char_buffer} {n : ℕ} {n' : ℕ} {err : dlist string}
    (hp : valid p) (h : p cb n = parse_result.fail n' err) : n ≤ n' :=
  sorry

theorem pure {α : Type} {a : α} : valid (pure a) := sorry

@[simp] theorem bind {α : Type} {β : Type} {p : parser α} {f : α → parser β} (hp : valid p)
    (hf : ∀ (a : α), valid (f a)) : valid (p >>= f) :=
  sorry

theorem and_then {α : Type} {β : Type} {p : parser α} {q : parser β} (hp : valid p) (hq : valid q) :
    valid (p >> q) :=
  bind hp fun (_x : α) => hq

@[simp] theorem map {α : Type} {β : Type} {p : parser α} (hp : valid p) {f : α → β} :
    valid (f <$> p) :=
  bind hp fun (_x : α) => pure

@[simp] theorem seq {α : Type} {β : Type} {p : parser α} {f : parser (α → β)} (hf : valid f)
    (hp : valid p) : valid (f <*> p) :=
  bind hf fun (_x : α → β) => map hp

@[simp] theorem mmap {α : Type} {β : Type} {l : List α} {f : α → parser β}
    (h : ∀ (a : α), a ∈ l → valid (f a)) : valid (mmap f l) :=
  sorry

@[simp] theorem mmap' {α : Type} {β : Type} {l : List α} {f : α → parser β}
    (h : ∀ (a : α), a ∈ l → valid (f a)) : valid (mmap' f l) :=
  sorry

@[simp] theorem failure {α : Type} : valid failure := sorry

@[simp] theorem guard {p : Prop} [Decidable p] : valid (guard p) := sorry

@[simp] theorem orelse {α : Type} {p : parser α} {q : parser α} (hp : valid p) (hq : valid q) :
    valid (p <|> q) :=
  sorry

@[simp] theorem decorate_errors {α : Type} {msgs : thunk (List string)} {p : parser α}
    (hp : valid p) : valid (decorate_errors msgs p) :=
  sorry

@[simp] theorem decorate_error {α : Type} {msg : thunk string} {p : parser α} (hp : valid p) :
    valid (decorate_error msg p) :=
  decorate_errors hp

@[simp] theorem any_char : valid any_char := sorry

@[simp] theorem sat {p : char → Prop} [decidable_pred p] : valid (sat p) := sorry

@[simp] theorem eps : valid eps := pure

theorem ch {c : char} : valid (ch c) := decorate_error (and_then sat eps)

theorem char_buf {s : char_buffer} : valid (char_buf s) :=
  decorate_error (mmap' fun (_x : char) (_x_1 : _x ∈ buffer.to_list s) => ch)

theorem one_of {cs : List char} : valid (one_of cs) := decorate_errors sat

theorem one_of' {cs : List char} : valid (one_of' cs) := and_then one_of eps

theorem str {s : string} : valid (str s) :=
  decorate_error (mmap' fun (_x : char) (_x_1 : _x ∈ string.to_list s) => ch)

theorem remaining : valid remaining :=
  fun (_x : char_buffer) (_x_1 : ℕ) =>
    { left := le_refl _x_1,
      right := fun (h : parse_result.pos (remaining _x _x_1) ≤ buffer.size _x) => h }

theorem eof : valid eof := decorate_error (bind remaining fun (_x : ℕ) => guard)

theorem foldr_core_zero {α : Type} {β : Type} {p : parser α} {f : α → β → β} {b : β} :
    valid (foldr_core f p b 0) :=
  failure

theorem foldr_core {α : Type} {β : Type} {p : parser α} {f : α → β → β} {b : β} (hp : valid p)
    {reps : ℕ} : valid (foldr_core f p b reps) :=
  sorry

theorem foldr {α : Type} {β : Type} {p : parser α} {b : β} {f : α → β → β} (hp : valid p) :
    valid (foldr f p b) :=
  fun (_x : char_buffer) (_x_1 : ℕ) => foldr_core hp _x _x_1

theorem foldl_core_zero {α : Type} {β : Type} {p : parser α} {f : β → α → β} {b : β} :
    valid (foldl_core f b p 0) :=
  failure

theorem foldl_core {α : Type} {β : Type} {f : α → β → α} {p : parser β} (hp : valid p) {a : α}
    {reps : ℕ} : valid (foldl_core f a p reps) :=
  sorry

theorem foldl {α : Type} {β : Type} {a : α} {f : α → β → α} {p : parser β} (hp : valid p) :
    valid (foldl f a p) :=
  fun (_x : char_buffer) (_x_1 : ℕ) => foldl_core hp _x _x_1

theorem many {α : Type} {p : parser α} (hp : valid p) : valid (many p) := foldr hp

theorem many_char {p : parser char} (hp : valid p) : valid (many_char p) := map (many hp)

theorem many' {α : Type} {p : parser α} (hp : valid p) : valid (many' p) := and_then (many hp) eps

theorem many1 {α : Type} {p : parser α} (hp : valid p) : valid (many1 p) := seq (map hp) (many hp)

theorem many_char1 {p : parser char} (hp : valid p) : valid (many_char1 p) := map (many1 hp)

theorem sep_by1 {α : Type} {p : parser α} {sep : parser Unit} (hp : valid p) (hs : valid sep) :
    valid (sep_by1 sep p) :=
  seq (map hp) (many (and_then hs hp))

theorem sep_by {α : Type} {p : parser α} {sep : parser Unit} (hp : valid p) (hs : valid sep) :
    valid (sep_by sep p) :=
  orelse (sep_by1 hp hs) pure

theorem fix_core {α : Type} {F : parser α → parser α} (hF : ∀ (p : parser α), valid p → valid (F p))
    (max_depth : ℕ) : valid (fix_core F max_depth) :=
  sorry

theorem digit : valid digit := decorate_error (bind sat fun (_x : char) => pure)

theorem nat : valid nat := decorate_error (bind (many1 digit) fun (_x : List ℕ) => pure)

theorem fix {α : Type} {F : parser α → parser α} (hF : ∀ (p : parser α), valid p → valid (F p)) :
    valid (fix F) :=
  fun (_x : char_buffer) (_x_1 : ℕ) => fix_core hF (buffer.size _x - _x_1 + 1) _x _x_1

end valid


@[simp] theorem orelse_pure_eq_fail {α : Type} {p : parser α} {cb : char_buffer} {n : ℕ} {n' : ℕ}
    {err : dlist string} {a : α} :
    has_orelse.orelse p (pure a) cb n = parse_result.fail n' err ↔
        p cb n = parse_result.fail n' err ∧ n ≠ n' :=
  sorry

theorem any_char_eq_done {cb : char_buffer} {n : ℕ} {n' : ℕ} (hn : n < buffer.size cb) {c : char} :
    any_char cb n = parse_result.done n' c ↔
        n' = n + 1 ∧ buffer.read cb { val := n, property := hn } = c :=
  sorry

theorem sat_eq_done {cb : char_buffer} {n : ℕ} {n' : ℕ} (hn : n < buffer.size cb) {c : char}
    {p : char → Prop} [decidable_pred p] :
    sat p cb n = parse_result.done n' c ↔
        p c ∧ n' = n + 1 ∧ buffer.read cb { val := n, property := hn } = c :=
  sorry

theorem eps_eq_done {cb : char_buffer} {n : ℕ} {n' : ℕ} :
    eps cb n = parse_result.done n' Unit.unit ↔ n = n' :=
  sorry

theorem ch_eq_done {cb : char_buffer} {n : ℕ} {n' : ℕ} (hn : n < buffer.size cb) {c : char} :
    ch c cb n = parse_result.done n' Unit.unit ↔
        n' = n + 1 ∧ buffer.read cb { val := n, property := hn } = c :=
  sorry

-- TODO: add char_buf_eq_done, needs lemmas about matching buffers

theorem one_of_eq_done {cb : char_buffer} {n : ℕ} {n' : ℕ} (hn : n < buffer.size cb) {c : char}
    {cs : List char} :
    one_of cs cb n = parse_result.done n' c ↔
        c ∈ cs ∧ n' = n + 1 ∧ buffer.read cb { val := n, property := hn } = c :=
  sorry

theorem one_of'_eq_done {cb : char_buffer} {n : ℕ} {n' : ℕ} (hn : n < buffer.size cb)
    {cs : List char} :
    one_of' cs cb n = parse_result.done n' Unit.unit ↔
        buffer.read cb { val := n, property := hn } ∈ cs ∧ n' = n + 1 :=
  sorry

theorem remaining_eq_done {cb : char_buffer} {n : ℕ} {n' : ℕ} {r : ℕ} :
    remaining cb n = parse_result.done n' r ↔ n = n' ∧ buffer.size cb - n = r :=
  sorry

theorem eof_eq_done {cb : char_buffer} {n : ℕ} {n' : ℕ} :
    eof cb n = parse_result.done n' Unit.unit ↔ n = n' ∧ buffer.size cb ≤ n :=
  sorry

@[simp] theorem foldr_core_zero_eq_done {α : Type} {β : Type} {cb : char_buffer} {n : ℕ} {n' : ℕ}
    {b : β} {f : α → β → β} {p : parser α} {b' : β} :
    foldr_core f p b 0 cb n ≠ parse_result.done n' b' :=
  sorry

theorem foldr_core_eq_done {α : Type} {β : Type} {cb : char_buffer} {n : ℕ} {n' : ℕ} {b : β}
    {f : α → β → β} {p : parser α} {reps : ℕ} {b' : β} :
    foldr_core f p b (reps + 1) cb n = parse_result.done n' b' ↔
        (∃ (np : ℕ),
            ∃ (a : α),
              ∃ (xs : β),
                p cb n = parse_result.done np a ∧
                  foldr_core f p b reps cb np = parse_result.done n' xs ∧ f a xs = b') ∨
          n = n' ∧
            b = b' ∧
              ∃ (err : dlist string),
                p cb n = parse_result.fail n err ∨
                  ∃ (np : ℕ),
                    ∃ (a : α),
                      p cb n = parse_result.done np a ∧
                        foldr_core f p b reps cb np = parse_result.fail n err :=
  sorry

@[simp] theorem foldr_core_zero_eq_fail {α : Type} {β : Type} {cb : char_buffer} {n : ℕ} {n' : ℕ}
    {b : β} {f : α → β → β} {p : parser α} {err : dlist string} :
    foldr_core f p b 0 cb n = parse_result.fail n' err ↔ n = n' ∧ err = dlist.empty :=
  sorry

theorem foldr_core_succ_eq_fail {α : Type} {β : Type} {cb : char_buffer} {n : ℕ} {n' : ℕ} {b : β}
    {f : α → β → β} {p : parser α} {reps : ℕ} {err : dlist string} :
    foldr_core f p b (reps + 1) cb n = parse_result.fail n' err ↔
        n ≠ n' ∧
          (p cb n = parse_result.fail n' err ∨
            ∃ (np : ℕ),
              ∃ (a : α),
                p cb n = parse_result.done np a ∧
                  foldr_core f p b reps cb np = parse_result.fail n' err) :=
  sorry

theorem foldr_eq_done {α : Type} {β : Type} {cb : char_buffer} {n : ℕ} {n' : ℕ} {b : β}
    {f : α → β → β} {p : parser α} {b' : β} :
    foldr f p b cb n = parse_result.done n' b' ↔
        (∃ (np : ℕ),
            ∃ (a : α),
              ∃ (x : β),
                p cb n = parse_result.done np a ∧
                  foldr_core f p b (buffer.size cb - n) cb np = parse_result.done n' x ∧
                    f a x = b') ∨
          n = n' ∧
            b = b' ∧
              ∃ (err : dlist string),
                p cb n = parse_result.fail n err ∨
                  ∃ (np : ℕ),
                    ∃ (x : α),
                      p cb n = parse_result.done np x ∧
                        foldr_core f p b (buffer.size cb - n) cb np = parse_result.fail n err :=
  sorry

theorem foldr_eq_fail_of_valid_at_end {α : Type} {β : Type} {cb : char_buffer} {n : ℕ} {n' : ℕ}
    {b : β} {f : α → β → β} {p : parser α} {err : dlist string} (hp : valid p)
    (hc : buffer.size cb ≤ n) :
    foldr f p b cb n = parse_result.fail n' err ↔
        n < n' ∧
          (p cb n = parse_result.fail n' err ∨
            ∃ (a : α), p cb n = parse_result.done n' a ∧ err = dlist.empty) :=
  sorry

theorem foldr_eq_fail {α : Type} {β : Type} {cb : char_buffer} {n : ℕ} {n' : ℕ} {b : β}
    {f : α → β → β} {p : parser α} {err : dlist string} :
    foldr f p b cb n = parse_result.fail n' err ↔
        n ≠ n' ∧
          (p cb n = parse_result.fail n' err ∨
            ∃ (np : ℕ),
              ∃ (a : α),
                p cb n = parse_result.done np a ∧
                  foldr_core f p b (buffer.size cb - n) cb np = parse_result.fail n' err) :=
  sorry

@[simp] theorem foldl_core_zero_eq_done {α : Type} {β : Type} {cb : char_buffer} {n : ℕ} {n' : ℕ}
    {b : β} {f : β → α → β} {p : parser α} {b' : β} :
    foldl_core f b p 0 cb n = parse_result.done n' b' ↔ False :=
  sorry

theorem foldl_core_eq_done {α : Type} {β : Type} {cb : char_buffer} {n : ℕ} {n' : ℕ} {b : β}
    {f : β → α → β} {p : parser α} {reps : ℕ} {b' : β} :
    foldl_core f b p (reps + 1) cb n = parse_result.done n' b' ↔
        (∃ (np : ℕ),
            ∃ (a : α),
              p cb n = parse_result.done np a ∧
                foldl_core f (f b a) p reps cb np = parse_result.done n' b') ∨
          n = n' ∧
            b = b' ∧
              ∃ (err : dlist string),
                p cb n = parse_result.fail n err ∨
                  ∃ (np : ℕ),
                    ∃ (a : α),
                      p cb n = parse_result.done np a ∧
                        foldl_core f (f b a) p reps cb np = parse_result.fail n err :=
  sorry

@[simp] theorem foldl_core_zero_eq_fail {α : Type} {β : Type} {cb : char_buffer} {n : ℕ} {n' : ℕ}
    {b : β} {f : β → α → β} {p : parser α} {err : dlist string} :
    foldl_core f b p 0 cb n = parse_result.fail n' err ↔ n = n' ∧ err = dlist.empty :=
  sorry

theorem foldl_core_succ_eq_fail {α : Type} {β : Type} {cb : char_buffer} {n : ℕ} {n' : ℕ} {b : β}
    {f : β → α → β} {p : parser α} {reps : ℕ} {err : dlist string} :
    foldl_core f b p (reps + 1) cb n = parse_result.fail n' err ↔
        n ≠ n' ∧
          (p cb n = parse_result.fail n' err ∨
            ∃ (np : ℕ),
              ∃ (a : α),
                p cb n = parse_result.done np a ∧
                  foldl_core f (f b a) p reps cb np = parse_result.fail n' err) :=
  sorry

theorem foldl_eq_done {α : Type} {β : Type} {cb : char_buffer} {n : ℕ} {n' : ℕ} {b : β}
    {f : β → α → β} {p : parser α} {b' : β} :
    foldl f b p cb n = parse_result.done n' b' ↔
        (∃ (np : ℕ),
            ∃ (a : α),
              p cb n = parse_result.done np a ∧
                foldl_core f (f b a) p (buffer.size cb - n) cb np = parse_result.done n' b') ∨
          n = n' ∧
            b = b' ∧
              ∃ (err : dlist string),
                p cb n = parse_result.fail n err ∨
                  ∃ (np : ℕ),
                    ∃ (a : α),
                      p cb n = parse_result.done np a ∧
                        foldl_core f (f b a) p (buffer.size cb - n) cb np =
                          parse_result.fail n err :=
  sorry

theorem foldl_eq_fail {α : Type} {β : Type} {cb : char_buffer} {n : ℕ} {n' : ℕ} {b : β}
    {f : β → α → β} {p : parser α} {err : dlist string} :
    foldl f b p cb n = parse_result.fail n' err ↔
        n ≠ n' ∧
          (p cb n = parse_result.fail n' err ∨
            ∃ (np : ℕ),
              ∃ (a : α),
                p cb n = parse_result.done np a ∧
                  foldl_core f (f b a) p (buffer.size cb - n) cb np = parse_result.fail n' err) :=
  sorry

theorem many_eq_done_nil {α : Type} {cb : char_buffer} {n : ℕ} {n' : ℕ} {p : parser α} :
    many p cb n = parse_result.done n' [] ↔
        n = n' ∧
          ∃ (err : dlist string),
            p cb n = parse_result.fail n err ∨
              ∃ (np : ℕ),
                ∃ (a : α),
                  p cb n = parse_result.done np a ∧
                    foldr_core List.cons p [] (buffer.size cb - n) cb np =
                      parse_result.fail n err :=
  sorry

theorem many_eq_done {α : Type} {cb : char_buffer} {n : ℕ} {n' : ℕ} {p : parser α} {x : α}
    {xs : List α} :
    many p cb n = parse_result.done n' (x :: xs) ↔
        ∃ (np : ℕ),
          p cb n = parse_result.done np x ∧
            foldr_core List.cons p [] (buffer.size cb - n) cb np = parse_result.done n' xs :=
  sorry

theorem many_eq_fail {α : Type} {cb : char_buffer} {n : ℕ} {n' : ℕ} {p : parser α}
    {err : dlist string} :
    many p cb n = parse_result.fail n' err ↔
        n ≠ n' ∧
          (p cb n = parse_result.fail n' err ∨
            ∃ (np : ℕ),
              ∃ (a : α),
                p cb n = parse_result.done np a ∧
                  foldr_core List.cons p [] (buffer.size cb - n) cb np =
                    parse_result.fail n' err) :=
  sorry

theorem many_char_eq_done_empty {cb : char_buffer} {n : ℕ} {n' : ℕ} {p : parser char} :
    many_char p cb n = parse_result.done n' string.empty ↔
        n = n' ∧
          ∃ (err : dlist string),
            p cb n = parse_result.fail n err ∨
              ∃ (np : ℕ),
                ∃ (c : char),
                  p cb n = parse_result.done np c ∧
                    foldr_core List.cons p [] (buffer.size cb - n) cb np =
                      parse_result.fail n err :=
  sorry

theorem many_char_eq_done_not_empty {cb : char_buffer} {n : ℕ} {n' : ℕ} {p : parser char}
    {s : string} (h : s ≠ string.empty) :
    many_char p cb n = parse_result.done n' s ↔
        ∃ (np : ℕ),
          p cb n = parse_result.done np (string.head s) ∧
            foldr_core List.cons p [] (buffer.size cb - n) cb np =
              parse_result.done n' (string.to_list (string.popn s 1)) :=
  sorry

theorem many_char_eq_many_of_to_list {cb : char_buffer} {n : ℕ} {n' : ℕ} {p : parser char}
    {s : string} :
    many_char p cb n = parse_result.done n' s ↔
        many p cb n = parse_result.done n' (string.to_list s) :=
  sorry

theorem many'_eq_done {α : Type} {cb : char_buffer} {n : ℕ} {n' : ℕ} {p : parser α} :
    many' p cb n = parse_result.done n' Unit.unit ↔
        many p cb n = parse_result.done n' [] ∨
          ∃ (np : ℕ),
            ∃ (a : α),
              ∃ (l : List α),
                many p cb n = parse_result.done n' (a :: l) ∧
                  p cb n = parse_result.done np a ∧
                    foldr_core List.cons p [] (buffer.size cb - n) cb np = parse_result.done n' l :=
  sorry

@[simp] theorem many1_ne_done_nil {α : Type} {cb : char_buffer} {n : ℕ} {n' : ℕ} {p : parser α} :
    many1 p cb n ≠ parse_result.done n' [] :=
  sorry

theorem many1_eq_done {α : Type} {cb : char_buffer} {n : ℕ} {n' : ℕ} {a : α} {p : parser α}
    {l : List α} :
    many1 p cb n = parse_result.done n' (a :: l) ↔
        ∃ (np : ℕ), p cb n = parse_result.done np a ∧ many p cb np = parse_result.done n' l :=
  sorry

theorem many1_eq_fail {α : Type} {cb : char_buffer} {n : ℕ} {n' : ℕ} {p : parser α}
    {err : dlist string} :
    many1 p cb n = parse_result.fail n' err ↔
        p cb n = parse_result.fail n' err ∨
          ∃ (np : ℕ),
            ∃ (a : α), p cb n = parse_result.done np a ∧ many p cb np = parse_result.fail n' err :=
  sorry

@[simp] theorem many_char1_ne_empty {cb : char_buffer} {n : ℕ} {n' : ℕ} {p : parser char} :
    many_char1 p cb n ≠ parse_result.done n' string.empty :=
  sorry

theorem many_char1_eq_done {cb : char_buffer} {n : ℕ} {n' : ℕ} {p : parser char} {s : string}
    (h : s ≠ string.empty) :
    many_char1 p cb n = parse_result.done n' s ↔
        ∃ (np : ℕ),
          p cb n = parse_result.done np (string.head s) ∧
            many_char p cb np = parse_result.done n' (string.popn s 1) :=
  sorry

@[simp] theorem sep_by1_ne_done_nil {α : Type} {cb : char_buffer} {n : ℕ} {n' : ℕ}
    {sep : parser Unit} {p : parser α} : sep_by1 sep p cb n ≠ parse_result.done n' [] :=
  sorry

theorem sep_by1_eq_done {α : Type} {cb : char_buffer} {n : ℕ} {n' : ℕ} {a : α} {sep : parser Unit}
    {p : parser α} {l : List α} :
    sep_by1 sep p cb n = parse_result.done n' (a :: l) ↔
        ∃ (np : ℕ),
          p cb n = parse_result.done np a ∧ many (sep >> p) cb np = parse_result.done n' l :=
  sorry

theorem sep_by_eq_done_nil {α : Type} {cb : char_buffer} {n : ℕ} {n' : ℕ} {sep : parser Unit}
    {p : parser α} :
    sep_by sep p cb n = parse_result.done n' [] ↔
        n = n' ∧ ∃ (err : dlist string), sep_by1 sep p cb n = parse_result.fail n err :=
  sorry

@[simp] theorem fix_core_ne_done_zero {α : Type} {cb : char_buffer} {n : ℕ} {n' : ℕ} {a : α}
    {F : parser α → parser α} : fix_core F 0 cb n ≠ parse_result.done n' a :=
  sorry

theorem fix_core_eq_done {α : Type} {cb : char_buffer} {n : ℕ} {n' : ℕ} {a : α}
    {F : parser α → parser α} {max_depth : ℕ} :
    fix_core F (max_depth + 1) cb n = parse_result.done n' a ↔
        F (fix_core F max_depth) cb n = parse_result.done n' a :=
  sorry

theorem digit_eq_done {cb : char_buffer} {n : ℕ} {n' : ℕ} (hn : n < buffer.size cb) {k : ℕ} :
    digit cb n = parse_result.done n' k ↔
        n' = n + 1 ∧
          k ≤ bit1 (bit0 (bit0 1)) ∧
            char.to_nat (buffer.read cb { val := n, property := hn }) -
                  char.to_nat (char.of_nat (bit0 (bit0 (bit0 (bit0 (bit1 1)))))) =
                k ∧
              char.of_nat (bit0 (bit0 (bit0 (bit0 (bit1 1))))) ≤
                  buffer.read cb { val := n, property := hn } ∧
                buffer.read cb { val := n, property := hn } ≤
                  char.of_nat (bit1 (bit0 (bit0 (bit1 (bit1 1))))) :=
  sorry

end Mathlib