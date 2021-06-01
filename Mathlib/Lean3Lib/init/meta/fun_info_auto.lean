/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.meta.tactic
import Mathlib.Lean3Lib.init.meta.format
import Mathlib.Lean3Lib.init.function

universes l 

namespace Mathlib

structure param_info where
  is_implicit : Bool
  is_inst_implicit : Bool
  is_prop : Bool
  has_fwd_deps : Bool
  back_deps : List ℕ

structure fun_info where
  params : List param_info
  result_deps : List ℕ

/--
  specialized is true if the result of fun_info has been specifialized
  using this argument.
  For example, consider the function

             f : Pi (α : Type), α -> α

  Now, suppse we request get_specialize fun_info for the application

         f unit a

  fun_info_manager returns two param_info objects:
  1) specialized = true
  2) is_subsingleton = true

  Note that, in general, the second argument of f is not a subsingleton,
  but it is in this particular case/specialization.

  \remark This bit is only set if it is a dependent parameter.

   Moreover, we only set is_specialized IF another parameter
   becomes a subsingleton -/
structure subsingleton_info where
  specialized : Bool
  is_subsingleton : Bool

end Mathlib