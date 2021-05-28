/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import PrePort
import Lean3Lib.init.logic
import PostPort

universes u 

namespace Mathlib

axiom propext {a : Prop} {b : Prop} : (a ↔ b) → a = b/- Additional congruence lemmas. -/

theorem forall_congr_eq {a : Sort u} {p : a → Prop} {q : a → Prop} (h : ∀ (x : a), p x = q x) : (∀ (x : a), p x) = ∀ (x : a), q x :=
  propext (forall_congr fun (a : a) => eq.to_iff (h a))

theorem imp_congr_eq {a : Prop} {b : Prop} {c : Prop} {d : Prop} (h₁ : a = c) (h₂ : b = d) : (a → b) = (c → d) :=
  propext (imp_congr (eq.to_iff h₁) (eq.to_iff h₂))

theorem imp_congr_ctx_eq {a : Prop} {b : Prop} {c : Prop} {d : Prop} (h₁ : a = c) (h₂ : c → b = d) : (a → b) = (c → d) :=
  propext (imp_congr_ctx (eq.to_iff h₁) fun (hc : c) => eq.to_iff (h₂ hc))

theorem eq_true_intro {a : Prop} (h : a) : a = True :=
  propext (iff_true_intro h)

theorem eq_false_intro {a : Prop} (h : ¬a) : a = False :=
  propext (iff_false_intro h)

theorem iff.to_eq {a : Prop} {b : Prop} (h : a ↔ b) : a = b :=
  propext h

theorem iff_eq_eq {a : Prop} {b : Prop} : (a ↔ b) = (a = b) :=
  propext { mp := fun (h : a ↔ b) => iff.to_eq h, mpr := fun (h : a = b) => eq.to_iff h }

theorem eq_false {a : Prop} : a = False = (¬a) :=
  (fun (this : (a ↔ False) = (¬a)) => iff_eq_eq ▸ this) (propext (iff_false a))

theorem eq_true {a : Prop} : a = True = a :=
  (fun (this : (a ↔ True) = a) => iff_eq_eq ▸ this) (propext (iff_true a))

