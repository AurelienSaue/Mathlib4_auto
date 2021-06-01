/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Extensional equality for functions, and a proof of function extensionality from quotients.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.data.quot
import Mathlib.Lean3Lib.init.logic

universes u v 

namespace Mathlib

namespace function


protected def equiv {α : Sort u} {β : α → Sort v} (f₁ : (x : α) → β x) (f₂ : (x : α) → β x) :=
  ∀ (x : α), f₁ x = f₂ x

protected theorem equiv.refl {α : Sort u} {β : α → Sort v} (f : (x : α) → β x) :
    function.equiv f f :=
  fun (x : α) => rfl

protected theorem equiv.symm {α : Sort u} {β : α → Sort v} {f₁ : (x : α) → β x}
    {f₂ : (x : α) → β x} : function.equiv f₁ f₂ → function.equiv f₂ f₁ :=
  fun (h : function.equiv f₁ f₂) (x : α) => Eq.symm (h x)

protected theorem equiv.trans {α : Sort u} {β : α → Sort v} {f₁ : (x : α) → β x}
    {f₂ : (x : α) → β x} {f₃ : (x : α) → β x} :
    function.equiv f₁ f₂ → function.equiv f₂ f₃ → function.equiv f₁ f₃ :=
  fun (h₁ : function.equiv f₁ f₂) (h₂ : function.equiv f₂ f₃) (x : α) => Eq.trans (h₁ x) (h₂ x)

protected theorem equiv.is_equivalence (α : Sort u) (β : α → Sort v) : equivalence function.equiv :=
  mk_equivalence function.equiv equiv.refl equiv.symm equiv.trans

end function


theorem funext {α : Sort u} {β : α → Sort v} {f₁ : (x : α) → β x} {f₂ : (x : α) → β x}
    (h : ∀ (x : α), f₁ x = f₂ x) : f₁ = f₂ :=
  (fun (this : extfun_app (quotient.mk f₁) = extfun_app (quotient.mk f₂)) => this)
    (congr_arg extfun_app (quotient.sound h))

protected instance pi.subsingleton {α : Sort u} {β : α → Sort v} [∀ (a : α), subsingleton (β a)] :
    subsingleton ((a : α) → β a) :=
  subsingleton.intro
    fun (f₁ f₂ : (a : α) → β a) => funext fun (a : α) => subsingleton.elim (f₁ a) (f₂ a)

end Mathlib