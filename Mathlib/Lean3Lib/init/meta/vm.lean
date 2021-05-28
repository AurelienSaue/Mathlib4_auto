/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.meta.tactic
import Mathlib.Lean3Lib.init.control.option
import Mathlib.Lean3Lib.init.meta.mk_dec_eq_instance
import Mathlib.PostPort

universes l 

namespace Mathlib

inductive vm_obj_kind 
where
| simple : vm_obj_kind
| constructor : vm_obj_kind
| closure : vm_obj_kind
| native_closure : vm_obj_kind
| mpz : vm_obj_kind
| name : vm_obj_kind
| level : vm_obj_kind
| expr : vm_obj_kind
| declaration : vm_obj_kind
| environment : vm_obj_kind
| tactic_state : vm_obj_kind
| format : vm_obj_kind
| options : vm_obj_kind
| other : vm_obj_kind

namespace vm_obj


/-- For simple and constructor vm_obj's, it returns the constructor tag/index.
   Return 0 otherwise. -/
/-- For closure vm_obj's, it returns the internal function index. -/
/-- For constructor vm_obj's, it returns the data stored in the object.
   For closure vm_obj's, it returns the local arguments captured by the closure. -/
/-- For simple and mpz vm_obj's -/
/-- For name vm_obj's, it returns the name wrapped by the vm_obj. -/
/-- For level vm_obj's, it returns the universe level wrapped by the vm_obj. -/
/-- For expr vm_obj's, it returns the expression wrapped by the vm_obj. -/
/-- For declaration vm_obj's, it returns the declaration wrapped by the vm_obj. -/
/-- For environment vm_obj's, it returns the environment wrapped by the vm_obj. -/
/-- For tactic_state vm_obj's, it returns the tactic_state object wrapped by the vm_obj. -/
/-- For format vm_obj's, it returns the format object wrapped by the vm_obj. -/
end vm_obj


inductive vm_decl_kind 
where
| bytecode : vm_decl_kind
| builtin : vm_decl_kind
| cfun : vm_decl_kind

