/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Simon Hudon
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.testing.slim_check.sampleable
import Mathlib.PostPort

universes l v u_1 u u_2 

namespace Mathlib

/-!
# `testable` Class

Testable propositions have a procedure that can generate counter-examples
together with a proof that they invalidate the proposition.

This is a port of the Haskell QuickCheck library.

## Creating Customized Instances

The type classes `testable` and `sampleable` are the means by which
`slim_check` creates samples and tests them. For instance, the proposition
`∀ i j : ℕ, i ≤ j` has a `testable` instance because `ℕ` is sampleable
and `i ≤ j` is decidable. Once `slim_check` finds the `testable`
instance, it can start using the instance to repeatedly creating samples
and checking whether they satisfy the property. This allows the
user to create new instances and apply `slim_check` to new situations.

### Polymorphism

The property `testable.check (∀ (α : Type) (xs ys : list α), xs ++ ys
= ys ++ xs)` shows us that type-polymorphic properties can be
tested. `α` is instantiated with `ℤ` first and then tested as normal
monomorphic properties.

The monomorphisation limits the applicability of `slim_check` to
polymorphic properties that can be stated about integers. The
limitation may be lifted in the future but, for now, if
one wishes to use a different type than `ℤ`, one has to refer to
the desired type.

### What do I do if I'm testing a property about my newly defined type?

Let us consider a type made for a new formalization:

```lean
structure my_type :=
(x y : ℕ)
(h : x ≤ y)
```

How do we test a property about `my_type`? For instance, let us consider
`testable.check $ ∀ a b : my_type, a.y ≤ b.x → a.x ≤ b.y`. Writing this
property as is will give us an error because we do not have an instance
of `sampleable my_type`. We can define one as follows:

```lean
instance : sampleable my_type :=
{ sample := do
  x ← sample ℕ,
  xy_diff ← sample ℕ,
  return { x := x, y := x + xy_diff, h := /- some proof -/ } }
```

We can see that the instance is very simple because our type is built
up from other type that have `sampleable` instances. `sampleable` also
has a `shrink` method but it is optional. We may want to implement one
for ease of testing as:

```lean
/- ... -/

/- no specialized sampling -/

-- discard

--  x := 1

-- discard

--  x := 41

-- discard

--  x := 3

-- discard

--  x := 5

-- discard

--  x := 5

-- discard

--  x := 197

-- discard

--  x := 469

-- discard

--  x := 9

-- discard

-- ===================

-- Found problems!

-- x := 552

-- -------------------

/- let us define a specialized sampling instance -/

-- ===================

-- Found problems!

-- x := 358

-- -------------------

namespace slim_check


/-- Result of trying to disprove `p`

The constructors are:
  *  `success : (psum unit p) → test_result`
     succeed when we find another example satisfying `p`
     In `success h`, `h` is an optional proof of the proposition.
     Without the proof, all we know is that we found one example
     where `p` holds. With a proof, the one test was sufficient to
     prove that `p` holds and we do not need to keep finding examples.
   * `gave_up {} : ℕ → test_result`
     give up when a well-formed example cannot be generated.
     `gave_up n` tells us that `n` invalid examples were tried.
     Above 100, we give up on the proposition and report that we
     did not find a way to properly test it.
   * `failure : ¬ p → (list string) → ℕ → test_result`
     a counter-example to `p`; the strings specify values for the relevant variables.
     `failure h vs n` also carries a proof that `p` does not hold. This way, we can
     guarantee that there will be no false positive. The last component, `n`,
     is the number of times that the counter-example was shrunk.
-/
inductive test_result (p : Prop) 
where
| success : psum Unit p → test_result p
| gave_up : ℕ → test_result p
| failure : ¬p → List string → ℕ → test_result p

/-- format a `test_result` as a string. -/
protected def test_result.to_string {p : Prop} : test_result p → string :=
  sorry

/-- configuration for testing a property -/
structure slim_check_cfg 
where
  num_inst : ℕ
  max_size : ℕ
  trace_discarded : Bool
  trace_success : Bool
  trace_shrink : Bool
  trace_shrink_candidates : Bool
  random_seed : Option ℕ
  quiet : Bool

protected instance test_result.has_to_string {p : Prop} : has_to_string (test_result p) :=
  has_to_string.mk test_result.to_string

/--
`printable_prop p` allows one to print a proposition so that
`slim_check` can indicate how values relate to each other.
-/
class printable_prop (p : Prop) 
where
  print_prop : Option string

protected instance default_printable_prop {p : Prop} : printable_prop p :=
  printable_prop.mk none

/-- `testable p` uses random examples to try to disprove `p`. -/
class testable (p : Prop) 
where
  run : slim_check_cfg → Bool → gen (test_result p)

/-- applicative combinator proof carrying test results -/
def combine {p : Prop} {q : Prop} : psum Unit (p → q) → psum Unit p → psum Unit q :=
  sorry

/-- Combine the test result for properties `p` and `q` to create a test for their conjunction. -/
def and_counter_example {p : Prop} {q : Prop} : test_result p → test_result q → test_result (p ∧ q) :=
  sorry

/-- Combine the test result for properties `p` and `q` to create a test for their disjunction -/
def or_counter_example {p : Prop} {q : Prop} : test_result p → test_result q → test_result (p ∨ q) :=
  sorry

/-- If `q → p`, then `¬ p → ¬ q` which means that testing `p` can allow us
to find counter-examples to `q`. -/
def convert_counter_example {p : Prop} {q : Prop} (h : q → p) : test_result p → optParam (psum Unit (p → q)) (psum.inl Unit.unit) → test_result q :=
  sorry

/-- Test `q` by testing `p` and proving the equivalence between the two. -/
def convert_counter_example' {p : Prop} {q : Prop} (h : p ↔ q) (r : test_result p) : test_result q :=
  convert_counter_example (iff.mpr h) r (psum.inr (iff.mp h))

/-- When we assign a value to a universally quantified variable,
we record that value using this function so that our counter-examples
can be informative. -/
def add_to_counter_example (x : string) {p : Prop} {q : Prop} (h : q → p) : test_result p → optParam (psum Unit (p → q)) (psum.inl Unit.unit) → test_result q :=
  sorry

/-- Add some formatting to the information recorded by `add_to_counter_example`. -/
def add_var_to_counter_example {γ : Type v} [has_repr γ] (var : string) (x : γ) {p : Prop} {q : Prop} (h : q → p) : test_result p → optParam (psum Unit (p → q)) (psum.inl Unit.unit) → test_result q :=
  add_to_counter_example
    (var ++
        string.str
          (string.str
            (string.str (string.str string.empty (char.of_nat (bit0 (bit0 (bit0 (bit0 (bit0 1)))))))
              (char.of_nat (bit0 (bit1 (bit0 (bit1 (bit1 1)))))))
            (char.of_nat (bit1 (bit0 (bit1 (bit1 (bit1 1)))))))
          (char.of_nat (bit0 (bit0 (bit0 (bit0 (bit0 1)))))) ++
      repr x)
    h

/-- Gadget used to introspect the name of bound variables.

It is used with the `testable` typeclass so that
`testable (named_binder "x" (∀ x, p x))` can use the variable name
of `x` in error messages displayed to the user. If we find that instantiating
the above quantifier with 3 falsifies it, we can print:

```
==============
Problem found!
==============
x := 3
```
 -/
@[simp] def named_binder (n : string) (p : Prop) :=
  p

/-- Is the given test result a failure? -/
def is_failure {p : Prop} : test_result p → Bool :=
  sorry

protected instance and_testable (p : Prop) (q : Prop) [testable p] [testable q] : testable (p ∧ q) :=
  testable.mk
    fun (cfg : slim_check_cfg) (min : Bool) =>
      do 
        let xp ← testable.run p cfg min 
        let xq ← testable.run q cfg min 
        pure (and_counter_example xp xq)

protected instance or_testable (p : Prop) (q : Prop) [testable p] [testable q] : testable (p ∨ q) :=
  testable.mk
    fun (cfg : slim_check_cfg) (min : Bool) =>
      do 
        testable.run p cfg min 
        sorry

protected instance iff_testable (p : Prop) (q : Prop) [testable (p ∧ q ∨ ¬p ∧ ¬q)] : testable (p ↔ q) :=
  testable.mk
    fun (cfg : slim_check_cfg) (min : Bool) =>
      do 
        let xp ← testable.run (p ∧ q ∨ ¬p ∧ ¬q) cfg min 
        return (convert_counter_example' sorry xp)

protected instance dec_guard_testable (var : string) (p : Prop) [printable_prop p] [Decidable p] (β : p → Prop) [(h : p) → testable (β h)] : testable (named_binder var (∀ (h : p), β h)) :=
  testable.mk
    fun (cfg : slim_check_cfg) (min : Bool) =>
      dite p (fun (h : p) => sorry)
        fun (h : ¬p) =>
          ite (↥(slim_check_cfg.trace_discarded cfg) ∨ ↥(slim_check_cfg.trace_success cfg)) sorry
            (return (test_result.gave_up 1))

/-- Type tag that replaces a type's `has_repr` instance with its `has_to_string` instance. -/
def use_has_to_string (α : Type u_1) :=
  α

protected instance use_has_to_string.inhabited (α : Type u) [I : Inhabited α] : Inhabited (use_has_to_string α) :=
  I

/-- Add the type tag `use_has_to_string` to an expression's type. -/
def use_has_to_string.mk {α : Type u_1} (x : α) : use_has_to_string α :=
  x

protected instance use_has_to_string.has_repr (α : Type u) [has_to_string α] : has_repr (use_has_to_string α) :=
  has_repr.mk to_string

protected instance all_types_testable (var : string) (f : Type → Prop) [testable (f ℤ)] : testable (named_binder var (∀ (x : Type), f x)) :=
  testable.mk
    fun (cfg : slim_check_cfg) (min : Bool) =>
      do 
        let r ← testable.run (f ℤ) cfg min 
        return
            (add_var_to_counter_example var
              (use_has_to_string.mk
                (string.str string.empty
                  (char.of_nat
                    (bit0 (bit0 (bit1 (bit0 (bit0 (bit1 (bit0 (bit0 (bit1 (bit0 (bit0 (bit0 (bit0 1))))))))))))))))
              sorry r (psum.inl Unit.unit))

/-- Trace the value of sampled variables if the sample is discarded. -/
def trace_if_giveup {p : Prop} {α : Type u_1} {β : Type u_2} [has_repr α] (tracing_enabled : Bool) (var : string) (val : α) : test_result p → thunk β → β :=
  sorry

/-- testable instance for a property iterating over the element of a list -/
protected instance test_forall_in_list (var : string) (var' : string) (α : Type u) (β : α → Prop) [(x : α) → testable (β x)] [has_repr α] (xs : List α) : testable (named_binder var (∀ (x : α), named_binder var' (x ∈ xs → β x))) :=
  sorry

/-- Test proposition `p` by randomly selecting one of the provided
testable instances. -/
def combine_testable (p : Prop) (t : List (testable p)) (h : 0 < list.length t) : testable p :=
  testable.mk
    fun (cfg : slim_check_cfg) (min : Bool) =>
      (fun (this : 0 < list.length (list.map (fun (t : testable p) => testable.run p cfg min) t)) =>
          gen.one_of (list.map (fun (t : testable p) => testable.run p cfg min) t) this)
        sorry

/--
Format the counter-examples found in a test failure.
-/
def format_failure (s : string) (xs : List string) (n : ℕ) : string := sorry

-------------------

/--
Format the counter-examples found in a test failure.
-/
def format_failure' (s : string) {p : Prop} : test_result p → string :=
  sorry

/--
Increase the number of shrinking steps in a test result.
-/
def add_shrinks {p : Prop} (n : ℕ) : test_result p → test_result p :=
  sorry

/-- Shrink a counter-example `x` by using `shrink x`, picking the first
candidate that falsifies a property and recursively shrinking that one.

The process is guaranteed to terminate because `shrink x` produces
a proof that all the values it produces are smaller (according to `sizeof`)
than `x`. -/
def minimize_aux (α : Type u) (β : α → Prop) [sampleable_ext α] [(x : α) → testable (β x)] (cfg : slim_check_cfg) (var : string) : sampleable_ext.proxy_repr α →
  ℕ → option_t gen (sigma fun (x : sampleable_ext.proxy_repr α) => test_result (β (sampleable_ext.interp α x))) := sorry

/-- Once a property fails to hold on an example, look for smaller counter-examples
to show the user. -/
def minimize (α : Type u) (β : α → Prop) [sampleable_ext α] [(x : α) → testable (β x)] (cfg : slim_check_cfg) (var : string) (x : sampleable_ext.proxy_repr α) (r : test_result (β (sampleable_ext.interp α x))) : gen (sigma fun (x : sampleable_ext.proxy_repr α) => test_result (β (sampleable_ext.interp α x))) := sorry

protected instance exists_testable (var : string) (var' : string) (α : Type u) (β : α → Prop) (p : Prop) [testable (named_binder var (∀ (x : α), named_binder var' (β x → p)))] : testable (named_binder var' (named_binder var (∃ (x : α), β x) → p)) :=
  testable.mk
    fun (cfg : slim_check_cfg) (min : Bool) =>
      do 
        let x ← testable.run (named_binder var (∀ (x : α), named_binder var' (β x → p))) cfg min 
        pure (convert_counter_example' sorry x)

/-- Test a universal property by creating a sample of the right type and instantiating the
bound variable with it -/
protected instance var_testable (var : string) (α : Type u) (β : α → Prop) [sampleable_ext α] [(x : α) → testable (β x)] : testable (named_binder var (∀ (x : α), β x)) := sorry

/-- Test a universal property about propositions -/
protected instance prop_var_testable (var : string) (β : Prop → Prop) [I : (b : Bool) → testable (β ↥b)] : testable (named_binder var (∀ (p : Prop), β p)) :=
  testable.mk
    fun (cfg : slim_check_cfg) (min : Bool) =>
      (fun (ᾰ : test_result (∀ (b : Bool), β ↥b)) => convert_counter_example sorry ᾰ (psum.inl Unit.unit)) <$>
        testable.run (named_binder var (∀ (b : Bool), β ↥b)) cfg min

protected instance unused_var_testable (var : string) (α : Type u) (β : Prop) [Inhabited α] [testable β] : testable (named_binder var (α → β)) :=
  testable.mk
    fun (cfg : slim_check_cfg) (min : Bool) =>
      do 
        let r ← testable.run β cfg min 
        pure (convert_counter_example sorry r (psum.inr sorry))

protected instance subtype_var_testable (var : string) (var' : string) (α : Type u) (β : α → Prop) {p : α → Prop} [(x : α) → printable_prop (p x)] [(x : α) → testable (β x)] [I : sampleable_ext (Subtype p)] : testable (named_binder var (∀ (x : α), named_binder var' (p x → β x))) :=
  testable.mk
    fun (cfg : slim_check_cfg) (min : Bool) =>
      let test : (x : Subtype p) → testable (β ↑x) :=
        fun (x : Subtype p) =>
          testable.mk
            fun (cfg : slim_check_cfg) (min : Bool) =>
              do 
                testable.run (β (subtype.val x)) cfg min 
                sorry;
      do 
        let r ← testable.run (∀ (x : Subtype p), β (subtype.val x)) cfg min 
        pure (convert_counter_example' sorry r)

protected instance decidable_testable (p : Prop) [printable_prop p] [Decidable p] : testable p :=
  testable.mk
    fun (cfg : slim_check_cfg) (min : Bool) =>
      return (dite p (fun (h : p) => test_result.success (psum.inr h)) fun (h : ¬p) => sorry)

protected instance eq.printable_prop {α : Type u_1} [has_repr α] (x : α) (y : α) : printable_prop (x = y) :=
  printable_prop.mk
    (some
      (string.empty ++ to_string (repr x) ++
        (string.str
              (string.str (string.str string.empty (char.of_nat (bit0 (bit0 (bit0 (bit0 (bit0 1)))))))
                (char.of_nat (bit1 (bit0 (bit1 (bit1 (bit1 1)))))))
              (char.of_nat (bit0 (bit0 (bit0 (bit0 (bit0 1)))))) ++
            to_string (repr y) ++
          string.empty)))

protected instance ne.printable_prop {α : Type u_1} [has_repr α] (x : α) (y : α) : printable_prop (x ≠ y) :=
  printable_prop.mk
    (some
      (string.empty ++ to_string (repr x) ++
        (string.str
              (string.str (string.str string.empty (char.of_nat (bit0 (bit0 (bit0 (bit0 (bit0 1)))))))
                (char.of_nat
                  (bit0 (bit0 (bit0 (bit0 (bit0 (bit1 (bit1 (bit0 (bit0 (bit1 (bit0 (bit0 (bit0 1)))))))))))))))
              (char.of_nat (bit0 (bit0 (bit0 (bit0 (bit0 1)))))) ++
            to_string (repr y) ++
          string.empty)))

protected instance le.printable_prop {α : Type u_1} [HasLessEq α] [has_repr α] (x : α) (y : α) : printable_prop (x ≤ y) :=
  printable_prop.mk
    (some
      (string.empty ++ to_string (repr x) ++
        (string.str
              (string.str (string.str string.empty (char.of_nat (bit0 (bit0 (bit0 (bit0 (bit0 1)))))))
                (char.of_nat
                  (bit0 (bit0 (bit1 (bit0 (bit0 (bit1 (bit1 (bit0 (bit0 (bit1 (bit0 (bit0 (bit0 1)))))))))))))))
              (char.of_nat (bit0 (bit0 (bit0 (bit0 (bit0 1)))))) ++
            to_string (repr y) ++
          string.empty)))

protected instance lt.printable_prop {α : Type u_1} [HasLess α] [has_repr α] (x : α) (y : α) : printable_prop (x < y) :=
  printable_prop.mk
    (some
      (string.empty ++ to_string (repr x) ++
        (string.str
              (string.str (string.str string.empty (char.of_nat (bit0 (bit0 (bit0 (bit0 (bit0 1)))))))
                (char.of_nat (bit0 (bit0 (bit1 (bit1 (bit1 1)))))))
              (char.of_nat (bit0 (bit0 (bit0 (bit0 (bit0 1)))))) ++
            to_string (repr y) ++
          string.empty)))

protected instance perm.printable_prop {α : Type u_1} [has_repr α] (xs : List α) (ys : List α) : printable_prop (xs ~ ys) :=
  printable_prop.mk
    (some
      (string.empty ++ to_string (repr xs) ++
        (string.str
              (string.str (string.str string.empty (char.of_nat (bit0 (bit0 (bit0 (bit0 (bit0 1)))))))
                (char.of_nat (bit0 (bit1 (bit1 (bit1 (bit1 (bit1 1))))))))
              (char.of_nat (bit0 (bit0 (bit0 (bit0 (bit0 1)))))) ++
            to_string (repr ys) ++
          string.empty)))

protected instance and.printable_prop (x : Prop) (y : Prop) [printable_prop x] [printable_prop y] : printable_prop (x ∧ y) :=
  printable_prop.mk
    (do 
      let x' ← printable_prop.print_prop x 
      let y' ← printable_prop.print_prop y 
      some
          (string.str string.empty (char.of_nat (bit0 (bit0 (bit0 (bit1 (bit0 1)))))) ++ to_string x' ++
            (string.str
                  (string.str (string.str string.empty (char.of_nat (bit0 (bit0 (bit0 (bit0 (bit0 1)))))))
                    (char.of_nat
                      (bit1 (bit1 (bit1 (bit0 (bit0 (bit1 (bit0 (bit0 (bit0 (bit1 (bit0 (bit0 (bit0 1)))))))))))))))
                  (char.of_nat (bit0 (bit0 (bit0 (bit0 (bit0 1)))))) ++
                to_string y' ++
              string.str string.empty (char.of_nat (bit1 (bit0 (bit0 (bit1 (bit0 1)))))))))

protected instance or.printable_prop (x : Prop) (y : Prop) [printable_prop x] [printable_prop y] : printable_prop (x ∨ y) :=
  printable_prop.mk
    (do 
      let x' ← printable_prop.print_prop x 
      let y' ← printable_prop.print_prop y 
      some
          (string.str string.empty (char.of_nat (bit0 (bit0 (bit0 (bit1 (bit0 1)))))) ++ to_string x' ++
            (string.str
                  (string.str (string.str string.empty (char.of_nat (bit0 (bit0 (bit0 (bit0 (bit0 1)))))))
                    (char.of_nat
                      (bit0 (bit0 (bit0 (bit1 (bit0 (bit1 (bit0 (bit0 (bit0 (bit1 (bit0 (bit0 (bit0 1)))))))))))))))
                  (char.of_nat (bit0 (bit0 (bit0 (bit0 (bit0 1)))))) ++
                to_string y' ++
              string.str string.empty (char.of_nat (bit1 (bit0 (bit0 (bit1 (bit0 1)))))))))

protected instance iff.printable_prop (x : Prop) (y : Prop) [printable_prop x] [printable_prop y] : printable_prop (x ↔ y) :=
  printable_prop.mk
    (do 
      let x' ← printable_prop.print_prop x 
      let y' ← printable_prop.print_prop y 
      some
          (string.str string.empty (char.of_nat (bit0 (bit0 (bit0 (bit1 (bit0 1)))))) ++ to_string x' ++
            (string.str
                  (string.str (string.str string.empty (char.of_nat (bit0 (bit0 (bit0 (bit0 (bit0 1)))))))
                    (char.of_nat
                      (bit0 (bit0 (bit1 (bit0 (bit1 (bit0 (bit0 (bit1 (bit1 (bit0 (bit0 (bit0 (bit0 1)))))))))))))))
                  (char.of_nat (bit0 (bit0 (bit0 (bit0 (bit0 1)))))) ++
                to_string y' ++
              string.str string.empty (char.of_nat (bit1 (bit0 (bit0 (bit1 (bit0 1)))))))))

protected instance imp.printable_prop (x : Prop) (y : Prop) [printable_prop x] [printable_prop y] : printable_prop (x → y) :=
  printable_prop.mk
    (do 
      let x' ← printable_prop.print_prop x 
      let y' ← printable_prop.print_prop y 
      some
          (string.str string.empty (char.of_nat (bit0 (bit0 (bit0 (bit1 (bit0 1)))))) ++ to_string x' ++
            (string.str
                  (string.str (string.str string.empty (char.of_nat (bit0 (bit0 (bit0 (bit0 (bit0 1)))))))
                    (char.of_nat
                      (bit0 (bit1 (bit0 (bit0 (bit1 (bit0 (bit0 (bit1 (bit1 (bit0 (bit0 (bit0 (bit0 1)))))))))))))))
                  (char.of_nat (bit0 (bit0 (bit0 (bit0 (bit0 1)))))) ++
                to_string y' ++
              string.str string.empty (char.of_nat (bit1 (bit0 (bit0 (bit1 (bit0 1)))))))))

protected instance not.printable_prop (x : Prop) [printable_prop x] : printable_prop (¬x) :=
  printable_prop.mk
    (do 
      let x' ← printable_prop.print_prop x 
      some
          (string.str (string.str string.empty (char.of_nat (bit0 (bit0 (bit1 (bit1 (bit0 (bit1 (bit0 1)))))))))
                (char.of_nat (bit0 (bit0 (bit0 (bit0 (bit0 1)))))) ++
              to_string x' ++
            string.empty))

protected instance true.printable_prop : printable_prop True :=
  printable_prop.mk
    (some
      (string.str
        (string.str
          (string.str (string.str string.empty (char.of_nat (bit0 (bit0 (bit1 (bit0 (bit1 (bit1 1))))))))
            (char.of_nat (bit0 (bit1 (bit0 (bit0 (bit1 (bit1 1))))))))
          (char.of_nat (bit1 (bit0 (bit1 (bit0 (bit1 (bit1 1))))))))
        (char.of_nat (bit1 (bit0 (bit1 (bit0 (bit0 (bit1 1)))))))))

protected instance false.printable_prop : printable_prop False :=
  printable_prop.mk
    (some
      (string.str
        (string.str
          (string.str
            (string.str (string.str string.empty (char.of_nat (bit0 (bit1 (bit1 (bit0 (bit0 (bit1 1))))))))
              (char.of_nat (bit1 (bit0 (bit0 (bit0 (bit0 (bit1 1))))))))
            (char.of_nat (bit0 (bit0 (bit1 (bit1 (bit0 (bit1 1))))))))
          (char.of_nat (bit1 (bit1 (bit0 (bit0 (bit1 (bit1 1))))))))
        (char.of_nat (bit1 (bit0 (bit1 (bit0 (bit0 (bit1 1)))))))))

protected instance bool.printable_prop (b : Bool) : printable_prop ↥b :=
  printable_prop.mk
    (some
      (ite (↥b)
        (string.str
          (string.str
            (string.str (string.str string.empty (char.of_nat (bit0 (bit0 (bit1 (bit0 (bit1 (bit1 1))))))))
              (char.of_nat (bit0 (bit1 (bit0 (bit0 (bit1 (bit1 1))))))))
            (char.of_nat (bit1 (bit0 (bit1 (bit0 (bit1 (bit1 1))))))))
          (char.of_nat (bit1 (bit0 (bit1 (bit0 (bit0 (bit1 1))))))))
        (string.str
          (string.str
            (string.str
              (string.str (string.str string.empty (char.of_nat (bit0 (bit1 (bit1 (bit0 (bit0 (bit1 1))))))))
                (char.of_nat (bit1 (bit0 (bit0 (bit0 (bit0 (bit1 1))))))))
              (char.of_nat (bit0 (bit0 (bit1 (bit1 (bit0 (bit1 1))))))))
            (char.of_nat (bit1 (bit1 (bit0 (bit0 (bit1 (bit1 1))))))))
          (char.of_nat (bit1 (bit0 (bit1 (bit0 (bit0 (bit1 1))))))))))

/-- Execute `cmd` and repeat every time the result is `gave_up` (at most
`n` times). -/
def retry {p : Prop} (cmd : rand (test_result p)) : ℕ → rand (test_result p) :=
  sorry

/-- Count the number of times the test procedure gave up. -/
def give_up {p : Prop} (x : ℕ) : test_result p → test_result p :=
  sorry

/-- Try `n` times to find a counter-example for `p`. -/
def testable.run_suite_aux (p : Prop) [testable p] (cfg : slim_check_cfg) : test_result p → ℕ → rand (test_result p) :=
  sorry

/-- Try to find a counter-example of `p`. -/
def testable.run_suite (p : Prop) [testable p] (cfg : optParam slim_check_cfg
  (slim_check_cfg.mk (bit0 (bit0 (bit1 (bit0 (bit0 (bit1 1)))))) (bit0 (bit0 (bit1 (bit0 (bit0 (bit1 1)))))) false false
    false false none false)) : rand (test_result p) :=
  testable.run_suite_aux p cfg (test_result.success (psum.inl Unit.unit)) (slim_check_cfg.num_inst cfg)

/-- Run a test suite for `p` in `io`. -/
def testable.check' (p : Prop) [testable p] (cfg : optParam slim_check_cfg
  (slim_check_cfg.mk (bit0 (bit0 (bit1 (bit0 (bit0 (bit1 1)))))) (bit0 (bit0 (bit1 (bit0 (bit0 (bit1 1)))))) false false
    false false none false)) : io (test_result p) :=
  sorry

namespace tactic


/-!
## Decorations

Instances of `testable` use `named_binder` as a decoration on
propositions in order to access the name of bound variables, as in
`named_binder "x" (forall x, x < y)`.  This helps the
`testable` instances create useful error messages where variables
are matched with values that falsify a given proposition.

The following functions help support the gadget so that the user does
not have to put them in themselves.
-/

/-- `add_existential_decorations p` adds `a `named_binder` annotation at the
root of `p` if `p` is an existential quantification. -/
/-- Traverse the syntax of a proposition to find universal quantifiers
and existential quantifiers and add `named_binder` annotations next to
them. -/
/-- `decorations_of p` is used as a hint to `mk_decorations` to specify
that the goal should be satisfied with a proposition equivalent to `p`
with added annotations. -/
def decorations_of (p : Prop) :=
  Prop

/-- In a goal of the shape `⊢ tactic.decorations_of p`, `mk_decoration` examines
the syntax of `p` and add `named_binder` around universal quantifications and
existential quantifications to improve error messages.

This tool can be used in the declaration of a function as follows:

```lean
def foo (p : Prop) (p' : tactic.decorations_of p . mk_decorations) [testable p'] : ...
```

`p` is the parameter given by the user, `p'` is an equivalent proposition where
the quantifiers are annotated with `named_binder`.
-/
end tactic


/-- Run a test suite for `p` and return true or false: should we believe that `p` holds? -/
def testable.check (p : Prop) (cfg : optParam slim_check_cfg
  (slim_check_cfg.mk (bit0 (bit0 (bit1 (bit0 (bit0 (bit1 1)))))) (bit0 (bit0 (bit1 (bit0 (bit0 (bit1 1)))))) false false
    false false none false)) (p' : autoParam (tactic.decorations_of p)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.slim_check.tactic.mk_decorations")
    (Lean.Name.mkStr
      (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "slim_check") "tactic")
      "mk_decorations")
    [])) [testable p'] : io PUnit :=
  do 
    sorry 
    sorry

