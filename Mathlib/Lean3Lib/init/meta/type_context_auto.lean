import Mathlib.PrePort
import Mathlib.Lean3Lib.init.control.monad
import Mathlib.Lean3Lib.init.meta.local_context
import Mathlib.Lean3Lib.init.meta.tactic
import Mathlib.Lean3Lib.init.meta.fun_info

namespace Mathlib

namespace tactic.unsafe


/-- A monad that exposes the functionality of the C++ class `type_context_old`.
The idea is that the methods to `type_context` are more powerful but _unsafe_ in the
sense that you can create terms that do not typecheck or that are infinitely descending.
Under the hood, `type_context` is implemented as a reader monad, with a mutable `type_context` object.
-/
namespace type_context


end Mathlib