/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.fintype.basic
import Mathlib.control.equiv_functor
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# `equiv_functor` instances

We derive some `equiv_functor` instances, to enable `equiv_rw` to rewrite under these functions.
-/

protected instance equiv_functor_unique : equiv_functor unique :=
  equiv_functor.mk fun (α β : Type u_1) (e : α ≃ β) => ⇑(equiv.unique_congr e)

protected instance equiv_functor_perm : equiv_functor equiv.perm :=
  equiv_functor.mk
    fun (α β : Type u_1) (e : α ≃ β) (p : equiv.perm α) =>
      equiv.trans (equiv.trans (equiv.symm e) p) e

-- There is a classical instance of `is_lawful_functor finset` available,

-- but we provide this computable alternative separately.

protected instance equiv_functor_finset : equiv_functor finset :=
  equiv_functor.mk
    fun (α β : Type u_1) (e : α ≃ β) (s : finset α) => finset.map (equiv.to_embedding e) s

protected instance equiv_functor_fintype : equiv_functor fintype :=
  equiv_functor.mk
    fun (α β : Type u_1) (e : α ≃ β) (s : fintype α) =>
      fintype.of_bijective (⇑e) (equiv.bijective e)

end Mathlib