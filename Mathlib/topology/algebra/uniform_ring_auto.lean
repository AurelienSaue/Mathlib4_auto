/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl

Theory of topological rings with uniform structure.
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.topology.algebra.group_completion
import Mathlib.topology.algebra.ring
import PostPort

universes u_1 u_2 u 

namespace Mathlib

namespace uniform_space.completion


protected instance has_one (α : Type u_1) [ring α] [uniform_space α] : HasOne (completion α) :=
  { one := ↑1 }

protected instance has_mul (α : Type u_1) [ring α] [uniform_space α] : Mul (completion α) :=
  { mul := function.curry (dense_inducing.extend sorry (coe ∘ function.uncurry Mul.mul)) }

theorem coe_one (α : Type u_1) [ring α] [uniform_space α] : ↑1 = 1 :=
  rfl

theorem coe_mul {α : Type u_1} [ring α] [uniform_space α] [topological_ring α] (a : α) (b : α) : ↑(a * b) = ↑a * ↑b :=
  Eq.symm
    (dense_inducing.extend_eq (dense_inducing.prod dense_inducing_coe dense_inducing_coe)
      (continuous.comp (continuous_coe α) continuous_mul) (a, b))

theorem continuous_mul {α : Type u_1} [ring α] [uniform_space α] [topological_ring α] [uniform_add_group α] : continuous fun (p : completion α × completion α) => prod.fst p * prod.snd p := sorry

theorem continuous.mul {α : Type u_1} [ring α] [uniform_space α] [topological_ring α] [uniform_add_group α] {β : Type u_2} [topological_space β] {f : β → completion α} {g : β → completion α} (hf : continuous f) (hg : continuous g) : continuous fun (b : β) => f b * g b :=
  continuous.comp continuous_mul (continuous.prod_mk hf hg)

protected instance ring {α : Type u_1} [ring α] [uniform_space α] [topological_ring α] [uniform_add_group α] : ring (completion α) :=
  ring.mk add_comm_group.add sorry add_comm_group.zero sorry sorry add_comm_group.neg add_comm_group.sub sorry sorry
    Mul.mul sorry 1 sorry sorry sorry sorry

/-- The map from a uniform ring to its completion, as a ring homomorphism. -/
def coe_ring_hom {α : Type u_1} [ring α] [uniform_space α] [topological_ring α] [uniform_add_group α] : α →+* completion α :=
  ring_hom.mk coe (coe_one α) sorry sorry sorry

/-- The completion extension as a ring morphism. -/
def extension_hom {α : Type u_1} [ring α] [uniform_space α] [topological_ring α] [uniform_add_group α] {β : Type u} [uniform_space β] [ring β] [uniform_add_group β] [topological_ring β] (f : α →+* β) (hf : continuous ⇑f) [complete_space β] [separated_space β] : completion α →+* β :=
  (fun (hf : uniform_continuous ⇑f) => ring_hom.mk (completion.extension ⇑f) sorry sorry sorry sorry) sorry

protected instance top_ring_compl {α : Type u_1} [ring α] [uniform_space α] [topological_ring α] [uniform_add_group α] : topological_ring (completion α) :=
  topological_ring.mk continuous_neg

/-- The completion map as a ring morphism. -/
def map_ring_hom {α : Type u_1} [ring α] [uniform_space α] [topological_ring α] [uniform_add_group α] {β : Type u} [uniform_space β] [ring β] [uniform_add_group β] [topological_ring β] (f : α →+* β) (hf : continuous ⇑f) : completion α →+* completion β :=
  extension_hom (ring_hom.comp coe_ring_hom f) sorry

protected instance comm_ring (R : Type u_2) [comm_ring R] [uniform_space R] [uniform_add_group R] [topological_ring R] : comm_ring (completion R) :=
  comm_ring.mk ring.add sorry ring.zero sorry sorry ring.neg ring.sub sorry sorry ring.mul sorry ring.one sorry sorry
    sorry sorry sorry

end uniform_space.completion


namespace uniform_space


theorem ring_sep_rel (α : Type u_1) [comm_ring α] [uniform_space α] [uniform_add_group α] [topological_ring α] : separation_setoid α = submodule.quotient_rel (ideal.closure ⊥) :=
  setoid.ext fun (x y : α) => group_separation_rel x y

theorem ring_sep_quot (α : Type u_1) [r : comm_ring α] [uniform_space α] [uniform_add_group α] [topological_ring α] : quotient (separation_setoid α) = ideal.quotient (ideal.closure ⊥) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (quotient (separation_setoid α) = ideal.quotient (ideal.closure ⊥))) (ring_sep_rel α)))
    (Eq.refl (quotient (submodule.quotient_rel (ideal.closure ⊥))))

/-- Given a topological ring `α` equipped with a uniform structure that makes subtraction uniformly
continuous, get an equivalence between the separated quotient of `α` and the quotient ring
corresponding to the closure of zero. -/
def sep_quot_equiv_ring_quot (α : Type u_1) [r : comm_ring α] [uniform_space α] [uniform_add_group α] [topological_ring α] : quotient (separation_setoid α) ≃ ideal.quotient (ideal.closure ⊥) :=
  quotient.congr_right sorry

/- TODO: use a form of transport a.k.a. lift definition a.k.a. transfer -/

protected instance comm_ring {α : Type u_1} [comm_ring α] [uniform_space α] [uniform_add_group α] [topological_ring α] : comm_ring (quotient (separation_setoid α)) :=
  eq.mpr sorry (ideal.quotient.comm_ring (ideal.closure ⊥))

protected instance topological_ring {α : Type u_1} [comm_ring α] [uniform_space α] [uniform_add_group α] [topological_ring α] : topological_ring (quotient (separation_setoid α)) := sorry

