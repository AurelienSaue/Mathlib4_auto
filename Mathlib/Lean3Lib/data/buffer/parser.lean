/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.Lean3Lib.data.buffer
import Mathlib.Lean3Lib.data.dlist
 

universes l 

namespace Mathlib

inductive parse_result (α : Type) 
where
| done : ℕ → α → parse_result α
| fail : ℕ → dlist string → parse_result α

/-- The parser monad. If you are familiar with the Parsec library in Haskell, you will understand this.  -/
def parser (α : Type)  :=
  char_buffer → ℕ → parse_result α

namespace parser


protected def bind {α : Type} {β : Type} (p : parser α) (f : α → parser β) : parser β :=
  fun (input : char_buffer) (pos : ℕ) => sorry

protected def pure {α : Type} (a : α) : parser α :=
  fun (input : char_buffer) (pos : ℕ) => parse_result.done pos a

protected def fail {α : Type} (msg : string) : parser α :=
  fun (_x : char_buffer) (pos : ℕ) => parse_result.fail pos (dlist.singleton msg)

protected instance monad : Monad parser := sorry

protected instance is_lawful_monad : is_lawful_monad parser :=
  is_lawful_monad.mk (fun (_x _x_1 : Type) (_x_2 : _x) (_x_3 : _x → parser _x_1) => rfl) parser.bind_assoc

protected instance monad_fail : monad_fail parser :=
  monad_fail.mk parser.fail

protected def failure {α : Type} : parser α :=
  fun (_x : char_buffer) (pos : ℕ) => parse_result.fail pos dlist.empty

protected def orelse {α : Type} (p : parser α) (q : parser α) : parser α :=
  fun (input : char_buffer) (pos : ℕ) => sorry

protected instance alternative : alternative parser :=
  alternative.mk parser.failure

protected instance inhabited {α : Type} : Inhabited (parser α) :=
  { default := parser.failure }

/-- Overrides the expected token name, and does not consume input on failure. -/
def decorate_errors {α : Type} (msgs : thunk (List string)) (p : parser α) : parser α :=
  fun (input : char_buffer) (pos : ℕ) => sorry

/-- Overrides the expected token name, and does not consume input on failure. -/
def decorate_error {α : Type} (msg : thunk string) (p : parser α) : parser α :=
  decorate_errors (fun (_ : Unit) => [msg Unit.unit]) p

/-- Matches a single character. Fails only if there is no more input. -/
def any_char : parser char :=
  fun (input : char_buffer) (pos : ℕ) =>
    dite (pos < buffer.size input)
      (fun (h : pos < buffer.size input) =>
        let c : char := buffer.read input { val := pos, property := h };
        parse_result.done (pos + 1) c)
      fun (h : ¬pos < buffer.size input) => parse_result.fail pos dlist.empty

/-- Matches a single character satisfying the given predicate. -/
def sat (p : char → Prop) [decidable_pred p] : parser char :=
  fun (input : char_buffer) (pos : ℕ) =>
    dite (pos < buffer.size input)
      (fun (h : pos < buffer.size input) =>
        let c : char := buffer.read input { val := pos, property := h };
        ite (p c) (parse_result.done (pos + 1) c) (parse_result.fail pos dlist.empty))
      fun (h : ¬pos < buffer.size input) => parse_result.fail pos dlist.empty

/-- Matches the empty word. -/
def eps : parser Unit :=
  return Unit.unit

/-- Matches the given character. -/
def ch (c : char) : parser Unit :=
  decorate_error (fun (_ : Unit) => char.to_string c) ((sat fun (_x : char) => _x = c) >> eps)

/-- Matches a whole char_buffer.  Does not consume input in case of failure. -/
def char_buf (s : char_buffer) : parser Unit :=
  decorate_error (fun (_ : Unit) => buffer.to_string s) (mmap' ch (buffer.to_list s))

/-- Matches one out of a list of characters. -/
def one_of (cs : List char) : parser char :=
  decorate_errors
    (fun (_ : Unit) =>
      do 
        let c ← cs 
        return (char.to_string c))
    (sat fun (_x : char) => _x ∈ cs)

def one_of' (cs : List char) : parser Unit :=
  one_of cs >> eps

/-- Matches a string.  Does not consume input in case of failure. -/
def str (s : string) : parser Unit :=
  decorate_error (fun (_ : Unit) => s) (mmap' ch (string.to_list s))

/-- Number of remaining input characters. -/
def remaining : parser ℕ :=
  fun (input : char_buffer) (pos : ℕ) => parse_result.done pos (buffer.size input - pos)

/-- Matches the end of the input. -/
def eof : parser Unit := sorry

def foldr_core {α : Type} {β : Type} (f : α → β → β) (p : parser α) (b : β) (reps : ℕ) : parser β :=
  sorry

/-- Matches zero or more occurrences of `p`, and folds the result. -/
def foldr {α : Type} {β : Type} (f : α → β → β) (p : parser α) (b : β) : parser β :=
  fun (input : char_buffer) (pos : ℕ) => foldr_core f p b (buffer.size input - pos + 1) input pos

def foldl_core {α : Type} {β : Type} (f : α → β → α) (a : α) (p : parser β) (reps : ℕ) : parser α :=
  sorry

/-- Matches zero or more occurrences of `p`, and folds the result. -/
def foldl {α : Type} {β : Type} (f : α → β → α) (a : α) (p : parser β) : parser α :=
  fun (input : char_buffer) (pos : ℕ) => foldl_core f a p (buffer.size input - pos + 1) input pos

/-- Matches zero or more occurrences of `p`. -/
def many {α : Type} (p : parser α) : parser (List α) :=
  foldr List.cons p []

def many_char (p : parser char) : parser string :=
  list.as_string <$> many p

/-- Matches zero or more occurrences of `p`. -/
def many' {α : Type} (p : parser α) : parser Unit :=
  many p >> eps

/-- Matches one or more occurrences of `p`. -/
def many1 {α : Type} (p : parser α) : parser (List α) :=
  List.cons <$> p <*> many p

/-- Matches one or more occurences of the char parser `p` and implodes them into a string. -/
def many_char1 (p : parser char) : parser string :=
  list.as_string <$> many1 p

/-- Matches one or more occurrences of `p`, separated by `sep`. -/
def sep_by1 {α : Type} (sep : parser Unit) (p : parser α) : parser (List α) :=
  List.cons <$> p <*> many (sep >> p)

/-- Matches zero or more occurrences of `p`, separated by `sep`. -/
def sep_by {α : Type} (sep : parser Unit) (p : parser α) : parser (List α) :=
  sep_by1 sep p <|> return []

def fix_core {α : Type} (F : parser α → parser α) (max_depth : ℕ) : parser α :=
  sorry

/-- Matches a digit (0-9). -/
def digit : parser ℕ :=
  decorate_error
    (fun (_ : Unit) =>
      string.str
        (string.str
          (string.str
            (string.str
              (string.str
                (string.str (string.str string.empty (char.of_nat (bit0 (bit0 (bit1 (bit1 (bit1 1)))))))
                  (char.of_nat (bit0 (bit0 (bit1 (bit0 (bit0 (bit1 1))))))))
                (char.of_nat (bit1 (bit0 (bit0 (bit1 (bit0 (bit1 1))))))))
              (char.of_nat (bit1 (bit1 (bit1 (bit0 (bit0 (bit1 1))))))))
            (char.of_nat (bit1 (bit0 (bit0 (bit1 (bit0 (bit1 1))))))))
          (char.of_nat (bit0 (bit0 (bit1 (bit0 (bit1 (bit1 1))))))))
        (char.of_nat (bit0 (bit1 (bit1 (bit1 (bit1 1)))))))
    (do 
      let c ←
        sat
          fun (c : char) =>
            char.of_nat (bit0 (bit0 (bit0 (bit0 (bit1 1))))) ≤ c ∧ c ≤ char.of_nat (bit1 (bit0 (bit0 (bit1 (bit1 1)))))
      pure (char.to_nat c - char.to_nat (char.of_nat (bit0 (bit0 (bit0 (bit0 (bit1 1))))))))

/-- Matches a natural number. Large numbers may cause performance issues, so
don't run this parser on untrusted input. -/
def nat : parser ℕ :=
  decorate_error
    (fun (_ : Unit) =>
      string.str
        (string.str
          (string.str
            (string.str
              (string.str
                (string.str
                  (string.str
                    (string.str (string.str string.empty (char.of_nat (bit0 (bit0 (bit1 (bit1 (bit1 1)))))))
                      (char.of_nat (bit0 (bit1 (bit1 (bit1 (bit0 (bit1 1))))))))
                    (char.of_nat (bit1 (bit0 (bit0 (bit0 (bit0 (bit1 1))))))))
                  (char.of_nat (bit0 (bit0 (bit1 (bit0 (bit1 (bit1 1))))))))
                (char.of_nat (bit1 (bit0 (bit1 (bit0 (bit1 (bit1 1))))))))
              (char.of_nat (bit0 (bit1 (bit0 (bit0 (bit1 (bit1 1))))))))
            (char.of_nat (bit1 (bit0 (bit0 (bit0 (bit0 (bit1 1))))))))
          (char.of_nat (bit0 (bit0 (bit1 (bit1 (bit0 (bit1 1))))))))
        (char.of_nat (bit0 (bit1 (bit1 (bit1 (bit1 1)))))))
    (do 
      let digits ← many1 digit 
      pure (prod.fst (list.foldr (fun (digit : ℕ) (_x : ℕ × ℕ) => sorry) (0, 1) digits)))

/-- Fixpoint combinator satisfying `fix F = F (fix F)`. -/
def fix {α : Type} (F : parser α → parser α) : parser α :=
  fun (input : char_buffer) (pos : ℕ) => fix_core F (buffer.size input - pos + 1) input pos

def mk_error_msg (input : char_buffer) (pos : ℕ) (expected : dlist string) : char_buffer := sorry

/-- Runs a parser on the given input.  The parser needs to match the complete input. -/
def run {α : Type} (p : parser α) (input : char_buffer) : string ⊕ α :=
  sorry

/-- Runs a parser on the given input.  The parser needs to match the complete input. -/
def run_string {α : Type} (p : parser α) (input : string) : string ⊕ α :=
  run p (string.to_char_buffer input)

