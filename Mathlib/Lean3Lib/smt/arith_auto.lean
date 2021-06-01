import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default

namespace Mathlib

axiom real

instance real.has_zero : HasZero real

instance real.has_one : HasOne real

instance real.has_add : Add real

instance real.has_mul : Mul real

instance real.has_sub : Sub real

instance real.has_neg : Neg real

instance real.has_div : Div real

instance real.has_lt : HasLess real

instance real.has_le : HasLessEq real

axiom real.of_int : ℤ → real

end Mathlib