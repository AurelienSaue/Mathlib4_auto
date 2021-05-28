/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.data.fin.basic
import Mathlib.PostPort

namespace Mathlib

def unsigned_sz : ℕ :=
  Nat.succ
    (bit1
      (bit1
        (bit1
          (bit1
            (bit1
              (bit1
                (bit1
                  (bit1
                    (bit1
                      (bit1
                        (bit1
                          (bit1
                            (bit1
                              (bit1
                                (bit1
                                  (bit1
                                    (bit1
                                      (bit1
                                        (bit1
                                          (bit1
                                            (bit1
                                              (bit1
                                                (bit1
                                                  (bit1
                                                    (bit1
                                                      (bit1 (bit1 (bit1 (bit1 (bit1 (bit1 1)))))))))))))))))))))))))))))))

def unsigned  :=
  fin unsigned_sz

namespace unsigned


/- We cannot use tactic dec_trivial here because the tactic framework has not been defined yet. -/

/- Later, we define of_nat using mod, the following version is used to define the metaprogramming system. -/

protected def of_nat' (n : ℕ) : unsigned :=
  dite (n < unsigned_sz) (fun (h : n < unsigned_sz) => { val := n, property := h })
    fun (h : ¬n < unsigned_sz) => { val := 0, property := zero_lt_unsigned_sz }

def to_nat (c : unsigned) : ℕ :=
  subtype.val c

end unsigned


protected instance unsigned.decidable_eq : DecidableEq unsigned :=
  (fun (this : DecidableEq (fin unsigned_sz)) => this) (fin.decidable_eq unsigned_sz)

