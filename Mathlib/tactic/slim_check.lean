/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.testing.slim_check.testable
import Mathlib.testing.slim_check.functions
import Mathlib.data.list.sort
import Mathlib.PostPort

namespace Mathlib

/-!
## Finding counterexamples automatically using `slim_check`

A proposition can be tested by writing it out as:

```lean
example (xs : list ℕ) (w : ∃ x ∈ xs, x < 3) : ∀ y ∈ xs, y < 5 := by slim_check
-- ===================

-- ===================
-- Found problems!

-- Found problems!

-- xs := [0, 5]

-- xs := [0, 5]
-- x := 0

-- x := 0
-- y := 5

-- y := 5
-- -------------------

-- -------------------

example (x : ℕ) (h : 2 ∣ x) : x < 100 := by slim_check
-- ===================

-- ===================
-- Found problems!

-- Found problems!

-- x := 258

-- x := 258
-- -------------------

-- -------------------

example (α : Type) (xs ys : list α) : xs ++ ys = ys ++ xs := by slim_check
-- ===================

-- ===================
-- Found problems!

-- Found problems!

-- α := ℤ

-- α := ℤ
-- xs := [-4]

-- xs := [-4]
-- ys := [1]

-- ys := [1]
-- -------------------

-- -------------------

example : ∀ x ∈ [1,2,3], x < 4 := by slim_check
-- Success

-- Success
```

In the first example, `slim_check` is called on the following goal:

```lean
xs : list ℕ,
h : ∃ (x : ℕ) (H : x ∈ xs), x < 3
⊢ ∀ (y : ℕ), y ∈ xs → y < 5
```

The local constants are reverted and an instance is found for
`testable (∀ (xs : list ℕ), (∃ x ∈ xs, x < 3) → (∀ y ∈ xs, y < 5))`.
The `testable` instance is supported by instances of `sampleable (list ℕ)`,
`decidable (x < 3)` and `decidable (y < 5)`. `slim_check` builds a
`testable` instance step by step with:

```
- testable (∀ (xs : list ℕ), (∃ x ∈ xs, x < 3) → (∀ y ∈ xs, y < 5))
                                     -: sampleable (list xs)
- testable ((∃ x ∈ xs, x < 3) → (∀ y ∈ xs, y < 5))
- testable (∀ x ∈ xs, x < 3 → (∀ y ∈ xs, y < 5))
- testable (x < 3 → (∀ y ∈ xs, y < 5))
                                     -: decidable (x < 3)
- testable (∀ y ∈ xs, y < 5)
                                     -: decidable (y < 5)
```

`sampleable (list ℕ)` lets us create random data of type `list ℕ` in a way that
helps find small counter-examples.  Next, the test of the proposition
hinges on `x < 3` and `y < 5` to both be decidable. The
implication between the two could be tested as a whole but it would be
less informative. Indeed, if we generate lists that only contain numbers
greater than `3`, the implication will always trivially hold but we should
conclude that we haven't found meaningful examples. Instead, when `x < 3`
does not hold, we reject the example (i.e.  we do not count it toward
the 100 required positive examples) and we start over. Therefore, when
`slim_check` prints `Success`, it means that a hundred suitable lists
were found and successfully tested.

If no counter-examples are found, `slim_check` behaves like `admit`.

`slim_check` can also be invoked using `#eval`:

```lean
#eval slim_check.testable.check (∀ (α : Type) (xs ys : list α), xs ++ ys = ys ++ xs)
-- ===================

-- ===================
-- Found problems!

-- Found problems!

-- α := ℤ

-- α := ℤ
-- xs := [-4]

-- xs := [-4]
-- ys := [1]

-- ys := [1]
-- -------------------

-- -------------------
```

For more information on writing your own `sampleable` and `testable`
instances, see `testing.slim_check.testable`.
-/

namespace tactic.interactive


/-- Tree structure representing a `testable` instance. -/
