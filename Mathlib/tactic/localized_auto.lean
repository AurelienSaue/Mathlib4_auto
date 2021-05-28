/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.tactic.core
import PostPort

namespace Mathlib

/-!
# Localized notation

This consists of two user-commands which allow you to declare notation and commands localized to a
locale.

See the tactic doc entry below for more information.

The code is inspired by code from Gabriel Ebner from the
[hott3 repository](https://github.com/gebner/hott3).
-/

/-- Get all commands in the given locale and return them as a list of strings -/
/-- Execute all commands in the given locale -/
/-- Add a new command to a locale and execute it right now.
  The new command is added as a declaration to the environment with name `_localized_decl.<number>`.
  This declaration has attribute `_localized` and as value a name-string pair. -/
/--
This consists of two user-commands which allow you to declare notation and commands localized to a
