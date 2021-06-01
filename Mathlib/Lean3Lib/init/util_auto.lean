/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.meta.format

universes u 

namespace Mathlib

/-- This function has a native implementation that tracks time. -/
def timeit {α : Type u} (s : string) (f : thunk α) : α := f Unit.unit

/-- This function has a native implementation that displays the given string in the regular output stream. -/
def trace {α : Type u} (s : string) (f : thunk α) : α := f Unit.unit

/-- This function has a native implementation that shows the VM call stack. -/
def trace_call_stack {α : Type u} (f : thunk α) : α := f Unit.unit

/-- This function has a native implementation that displays in the given position all trace messages used in f.
   The arguments line and col are filled by the elaborator. -/
def scope_trace {α : Type u} {line : ℕ} {col : ℕ} (f : thunk α) : α := f Unit.unit

end Mathlib