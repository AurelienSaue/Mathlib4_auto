/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import PrePort
import Lean3Lib.init.meta.name
import Lean3Lib.init.meta.format
import PostPort

namespace Mathlib

/-- A type universe term. eg `max u v`. Reflect a C++ level object. The VM replaces it with the C++ implementation. -/
