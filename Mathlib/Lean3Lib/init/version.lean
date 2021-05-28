import Mathlib.PrePort
import Mathlib.Lean3Lib.init.data.nat.basic
import Mathlib.Lean3Lib.init.data.string.basic
import Mathlib.PostPort

namespace Mathlib

def lean.version : ℕ × ℕ × ℕ :=
  (bit1 1, bit0 (bit1 (bit0 (bit1 1))), 0)

def lean.githash : string := sorry

def lean.is_release : Bool :=
  to_bool (1 ≠ 0)

/-- Additional version description like "nightly-2018-03-11" -/
def lean.special_version_desc : string :=
  string.empty

