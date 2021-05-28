/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

Additional facts about equiv and encodable using the
pairing function on nat.
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.nat.pairing
import Mathlib.data.pnat.basic
import PostPort

universes u_1 u_2 

namespace Mathlib

namespace equiv


/--
An equivalence between `ℕ × ℕ` and `ℕ`, using the `mkpair` and `unpair` functions in
`data.nat.pairing`.
-/
@[simp] def nat_prod_nat_equiv_nat : ℕ × ℕ ≃ ℕ :=
  mk (fun (p : ℕ × ℕ) => nat.mkpair (prod.fst p) (prod.snd p)) nat.unpair sorry nat.mkpair_unpair

/--
An equivalence between `bool × ℕ` and `ℕ`, by mapping `(tt, x)` to `2 * x + 1` and `(ff, x)` to
`2 * x`.
-/
@[simp] def bool_prod_nat_equiv_nat : Bool × ℕ ≃ ℕ :=
  mk (fun (_x : Bool × ℕ) => sorry) nat.bodd_div2 sorry sorry

/--
An equivalence between `ℕ ⊕ ℕ` and `ℕ`, by mapping `(sum.inl x)` to `2 * x` and `(sum.inr x)` to
`2 * x + 1`.
-/
@[simp] def nat_sum_nat_equiv_nat : ℕ ⊕ ℕ ≃ ℕ :=
  equiv.trans (equiv.symm (bool_prod_equiv_sum ℕ)) bool_prod_nat_equiv_nat

/--
An equivalence between `ℤ` and `ℕ`, through `ℤ ≃ ℕ ⊕ ℕ` and `ℕ ⊕ ℕ ≃ ℕ`.
-/
def int_equiv_nat : ℤ ≃ ℕ :=
  equiv.trans int_equiv_nat_sum_nat nat_sum_nat_equiv_nat

/--
An equivalence between `α × α` and `α`, given that there is an equivalence between `α` and `ℕ`.
-/
def prod_equiv_of_equiv_nat {α : Type (max u_1 u_2)} (e : α ≃ ℕ) : α × α ≃ α :=
  equiv.trans (equiv.trans (prod_congr e e) nat_prod_nat_equiv_nat) (equiv.symm e)

/--
An equivalence between `ℕ+` and `ℕ`, by mapping `x` in `ℕ+` to `x - 1` in `ℕ`.
-/
def pnat_equiv_nat : ℕ+ ≃ ℕ :=
  mk (fun (n : ℕ+) => Nat.pred (subtype.val n)) nat.succ_pnat sorry sorry

