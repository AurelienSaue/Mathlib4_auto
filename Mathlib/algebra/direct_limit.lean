/-
Copyright (c) 2019 Kenny Lau, Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.finset.order
import Mathlib.linear_algebra.direct_sum_module
import Mathlib.ring_theory.free_comm_ring
import Mathlib.ring_theory.ideal.operations
import Mathlib.PostPort

universes v w l u u₁ 

namespace Mathlib

/-!
# Direct limit of modules, abelian groups, rings, and fields.

See Atiyah-Macdonald PP.32-33, Matsumura PP.269-270

Generalizes the notion of "union", or "gluing", of incomparable modules over the same ring,
or incomparable abelian groups, or rings, or fields.

It is constructed as a quotient of the free module (for the module case) or quotient of
the free commutative ring (for the ring case) instead of a quotient of the disjoint union
so as to make the operations (addition etc.) "computable".

-/

/-- A directed system is a functor from the category (directed poset) to another category.
This is used for abelian groups and rings and fields because their maps are not bundled.
See module.directed_system -/
class directed_system {ι : Type v} [directed_order ι] (G : ι → Type w) (f : (i j : ι) → i ≤ j → G i → G j) 
where
  map_self : ∀ (i : ι) (x : G i) (h : i ≤ i), f i i h x = x
  map_map : ∀ (i j k : ι) (hij : i ≤ j) (hjk : j ≤ k) (x : G i), f j k hjk (f i j hij x) = f i k (le_trans hij hjk) x

namespace module


/-- A directed system is a functor from the category (directed poset) to the category of
`R`-modules. -/
class directed_system {R : Type u} [ring R] {ι : Type v} [directed_order ι] (G : ι → Type w) [(i : ι) → add_comm_group (G i)] [(i : ι) → module R (G i)] (f : (i j : ι) → i ≤ j → linear_map R (G i) (G j)) 
where
  map_self : ∀ (i : ι) (x : G i) (h : i ≤ i), coe_fn (f i i h) x = x
  map_map : ∀ (i j k : ι) (hij : i ≤ j) (hjk : j ≤ k) (x : G i),
  coe_fn (f j k hjk) (coe_fn (f i j hij) x) = coe_fn (f i k (le_trans hij hjk)) x

/-- The direct limit of a directed system is the modules glued together along the maps. -/
def direct_limit {R : Type u} [ring R] {ι : Type v} [dec_ι : DecidableEq ι] [directed_order ι] (G : ι → Type w) [(i : ι) → add_comm_group (G i)] [(i : ι) → module R (G i)] (f : (i j : ι) → i ≤ j → linear_map R (G i) (G j))  :=
  submodule.quotient
    (submodule.span R
      (set_of
        fun (a : direct_sum ι fun (i : ι) => G i) =>
          ∃ (i : ι),
            ∃ (j : ι),
              ∃ (H : i ≤ j),
                ∃ (x : G i),
                  coe_fn (direct_sum.lof R ι G i) x - coe_fn (direct_sum.lof R ι G j) (coe_fn (f i j H) x) = a))

namespace direct_limit


protected instance add_comm_group {R : Type u} [ring R] {ι : Type v} [dec_ι : DecidableEq ι] [directed_order ι] (G : ι → Type w) [(i : ι) → add_comm_group (G i)] [(i : ι) → module R (G i)] (f : (i j : ι) → i ≤ j → linear_map R (G i) (G j)) : add_comm_group (direct_limit G f) :=
  submodule.quotient.add_comm_group
    (submodule.span R
      (set_of
        fun (a : direct_sum ι fun (i : ι) => G i) =>
          ∃ (i : ι),
            ∃ (j : ι),
              ∃ (H : i ≤ j),
                ∃ (x : G i),
                  coe_fn (direct_sum.lof R ι G i) x - coe_fn (direct_sum.lof R ι G j) (coe_fn (f i j H) x) = a))

protected instance semimodule {R : Type u} [ring R] {ι : Type v} [dec_ι : DecidableEq ι] [directed_order ι] (G : ι → Type w) [(i : ι) → add_comm_group (G i)] [(i : ι) → module R (G i)] (f : (i j : ι) → i ≤ j → linear_map R (G i) (G j)) : semimodule R (direct_limit G f) :=
  submodule.quotient.semimodule
    (submodule.span R
      (set_of
        fun (a : direct_sum ι fun (i : ι) => G i) =>
          ∃ (i : ι),
            ∃ (j : ι),
              ∃ (H : i ≤ j),
                ∃ (x : G i),
                  coe_fn (direct_sum.lof R ι G i) x - coe_fn (direct_sum.lof R ι G j) (coe_fn (f i j H) x) = a))

protected instance inhabited {R : Type u} [ring R] {ι : Type v} [dec_ι : DecidableEq ι] [directed_order ι] (G : ι → Type w) [(i : ι) → add_comm_group (G i)] [(i : ι) → module R (G i)] (f : (i j : ι) → i ≤ j → linear_map R (G i) (G j)) : Inhabited (direct_limit G f) :=
  { default := 0 }

/-- The canonical map from a component to the direct limit. -/
def of (R : Type u) [ring R] (ι : Type v) [dec_ι : DecidableEq ι] [directed_order ι] (G : ι → Type w) [(i : ι) → add_comm_group (G i)] [(i : ι) → module R (G i)] (f : (i j : ι) → i ≤ j → linear_map R (G i) (G j)) (i : ι) : linear_map R (G i) (direct_limit G f) :=
  linear_map.comp
    (submodule.mkq
      (submodule.span R
        (set_of
          fun (a : direct_sum ι fun (i : ι) => G i) =>
            ∃ (i : ι),
              ∃ (j : ι),
                ∃ (H : i ≤ j),
                  ∃ (x : G i),
                    coe_fn (direct_sum.lof R ι G i) x - coe_fn (direct_sum.lof R ι G j) (coe_fn (f i j H) x) = a)))
    (direct_sum.lof R ι G i)

@[simp] theorem of_f {R : Type u} [ring R] {ι : Type v} [dec_ι : DecidableEq ι] [directed_order ι] {G : ι → Type w} [(i : ι) → add_comm_group (G i)] [(i : ι) → module R (G i)] {f : (i j : ι) → i ≤ j → linear_map R (G i) (G j)} {i : ι} {j : ι} {hij : i ≤ j} {x : G i} : coe_fn (of R ι G f j) (coe_fn (f i j hij) x) = coe_fn (of R ι G f i) x := sorry

/-- Every element of the direct limit corresponds to some element in
some component of the directed system. -/
theorem exists_of {R : Type u} [ring R] {ι : Type v} [dec_ι : DecidableEq ι] [directed_order ι] {G : ι → Type w} [(i : ι) → add_comm_group (G i)] [(i : ι) → module R (G i)] {f : (i j : ι) → i ≤ j → linear_map R (G i) (G j)} [Nonempty ι] (z : direct_limit G f) : ∃ (i : ι), ∃ (x : G i), coe_fn (of R ι G f i) x = z := sorry

protected theorem induction_on {R : Type u} [ring R] {ι : Type v} [dec_ι : DecidableEq ι] [directed_order ι] {G : ι → Type w} [(i : ι) → add_comm_group (G i)] [(i : ι) → module R (G i)] {f : (i j : ι) → i ≤ j → linear_map R (G i) (G j)} [Nonempty ι] {C : direct_limit G f → Prop} (z : direct_limit G f) (ih : ∀ (i : ι) (x : G i), C (coe_fn (of R ι G f i) x)) : C z := sorry

/-- The universal property of the direct limit: maps from the components to another module
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit. -/
def lift (R : Type u) [ring R] (ι : Type v) [dec_ι : DecidableEq ι] [directed_order ι] (G : ι → Type w) [(i : ι) → add_comm_group (G i)] [(i : ι) → module R (G i)] (f : (i j : ι) → i ≤ j → linear_map R (G i) (G j)) {P : Type u₁} [add_comm_group P] [module R P] (g : (i : ι) → linear_map R (G i) P) (Hg : ∀ (i j : ι) (hij : i ≤ j) (x : G i), coe_fn (g j) (coe_fn (f i j hij) x) = coe_fn (g i) x) : linear_map R (direct_limit G f) P :=
  submodule.liftq
    (submodule.span R
      (set_of
        fun (a : direct_sum ι fun (i : ι) => G i) =>
          ∃ (i : ι),
            ∃ (j : ι),
              ∃ (H : i ≤ j),
                ∃ (x : G i),
                  coe_fn (direct_sum.lof R ι G i) x - coe_fn (direct_sum.lof R ι G j) (coe_fn (f i j H) x) = a))
    (direct_sum.to_module R ι P g) sorry

theorem lift_of {R : Type u} [ring R] {ι : Type v} [dec_ι : DecidableEq ι] [directed_order ι] {G : ι → Type w} [(i : ι) → add_comm_group (G i)] [(i : ι) → module R (G i)] {f : (i j : ι) → i ≤ j → linear_map R (G i) (G j)} {P : Type u₁} [add_comm_group P] [module R P] (g : (i : ι) → linear_map R (G i) P) (Hg : ∀ (i j : ι) (hij : i ≤ j) (x : G i), coe_fn (g j) (coe_fn (f i j hij) x) = coe_fn (g i) x) {i : ι} (x : G i) : coe_fn (lift R ι G f g Hg) (coe_fn (of R ι G f i) x) = coe_fn (g i) x :=
  direct_sum.to_module_lof R i x

theorem lift_unique {R : Type u} [ring R] {ι : Type v} [dec_ι : DecidableEq ι] [directed_order ι] {G : ι → Type w} [(i : ι) → add_comm_group (G i)] [(i : ι) → module R (G i)] {f : (i j : ι) → i ≤ j → linear_map R (G i) (G j)} {P : Type u₁} [add_comm_group P] [module R P] [Nonempty ι] (F : linear_map R (direct_limit G f) P) (x : direct_limit G f) : coe_fn F x =
  coe_fn
    (lift R ι G f (fun (i : ι) => linear_map.comp F (of R ι G f i))
      fun (i j : ι) (hij : i ≤ j) (x : G i) =>
        eq.mpr
          (id
            (Eq._oldrec
              (Eq.refl
                (coe_fn ((fun (i : ι) => linear_map.comp F (of R ι G f i)) j) (coe_fn (f i j hij) x) =
                  coe_fn ((fun (i : ι) => linear_map.comp F (of R ι G f i)) i) x))
              (linear_map.comp_apply F (of R ι G f j) (coe_fn (f i j hij) x))))
          (eq.mpr
            (id
              (Eq._oldrec
                (Eq.refl
                  (coe_fn F (coe_fn (of R ι G f j) (coe_fn (f i j hij) x)) =
                    coe_fn ((fun (i : ι) => linear_map.comp F (of R ι G f i)) i) x))
                of_f))
            (Eq.refl (coe_fn F (coe_fn (of R ι G f i) x)))))
    x := sorry

/-- `totalize G f i j` is a linear map from `G i` to `G j`, for *every* `i` and `j`.
If `i ≤ j`, then it is the map `f i j` that comes with the directed system `G`,
and otherwise it is the zero map. -/
def totalize {R : Type u} [ring R] {ι : Type v} [directed_order ι] (G : ι → Type w) [(i : ι) → add_comm_group (G i)] [(i : ι) → module R (G i)] (f : (i j : ι) → i ≤ j → linear_map R (G i) (G j)) (i : ι) (j : ι) : linear_map R (G i) (G j) :=
  dite (i ≤ j) (fun (h : i ≤ j) => f i j h) fun (h : ¬i ≤ j) => 0

theorem totalize_apply {R : Type u} [ring R] {ι : Type v} [directed_order ι] {G : ι → Type w} [(i : ι) → add_comm_group (G i)] [(i : ι) → module R (G i)] {f : (i j : ι) → i ≤ j → linear_map R (G i) (G j)} (i : ι) (j : ι) (x : G i) : coe_fn (totalize G f i j) x = dite (i ≤ j) (fun (h : i ≤ j) => coe_fn (f i j h) x) fun (h : ¬i ≤ j) => 0 := sorry

theorem to_module_totalize_of_le {R : Type u} [ring R] {ι : Type v} [dec_ι : DecidableEq ι] [directed_order ι] {G : ι → Type w} [(i : ι) → add_comm_group (G i)] [(i : ι) → module R (G i)] {f : (i j : ι) → i ≤ j → linear_map R (G i) (G j)} [directed_system G f] {x : direct_sum ι G} {i : ι} {j : ι} (hij : i ≤ j) (hx : ∀ (k : ι), k ∈ dfinsupp.support x → k ≤ i) : coe_fn (direct_sum.to_module R ι (G j) fun (k : ι) => totalize G f k j) x =
  coe_fn (f i j hij) (coe_fn (direct_sum.to_module R ι (G i) fun (k : ι) => totalize G f k i) x) := sorry

theorem of.zero_exact_aux {R : Type u} [ring R] {ι : Type v} [dec_ι : DecidableEq ι] [directed_order ι] {G : ι → Type w} [(i : ι) → add_comm_group (G i)] [(i : ι) → module R (G i)] {f : (i j : ι) → i ≤ j → linear_map R (G i) (G j)} [directed_system G f] [Nonempty ι] {x : direct_sum ι G} (H : submodule.quotient.mk x = 0) : ∃ (j : ι),
  (∀ (k : ι), k ∈ dfinsupp.support x → k ≤ j) ∧
    coe_fn (direct_sum.to_module R ι (G j) fun (i : ι) => totalize G f i j) x = 0 := sorry

/-- A component that corresponds to zero in the direct limit is already zero in some
bigger module in the directed system. -/
theorem of.zero_exact {R : Type u} [ring R] {ι : Type v} [dec_ι : DecidableEq ι] [directed_order ι] {G : ι → Type w} [(i : ι) → add_comm_group (G i)] [(i : ι) → module R (G i)] {f : (i j : ι) → i ≤ j → linear_map R (G i) (G j)} [directed_system G f] {i : ι} {x : G i} (H : coe_fn (of R ι G f i) x = 0) : ∃ (j : ι), ∃ (hij : i ≤ j), coe_fn (f i j hij) x = 0 := sorry

end direct_limit


end module


namespace add_comm_group


/-- The direct limit of a directed system is the abelian groups glued together along the maps. -/
def direct_limit {ι : Type v} [dec_ι : DecidableEq ι] [directed_order ι] (G : ι → Type w) [(i : ι) → add_comm_group (G i)] (f : (i j : ι) → i ≤ j → G i →+ G j)  :=
  module.direct_limit G fun (i j : ι) (hij : i ≤ j) => add_monoid_hom.to_int_linear_map (f i j hij)

namespace direct_limit


protected theorem directed_system {ι : Type v} [directed_order ι] (G : ι → Type w) [(i : ι) → add_comm_group (G i)] (f : (i j : ι) → i ≤ j → G i →+ G j) [directed_system G fun (i j : ι) (h : i ≤ j) => ⇑(f i j h)] : module.directed_system G fun (i j : ι) (hij : i ≤ j) => add_monoid_hom.to_int_linear_map (f i j hij) :=
  module.directed_system.mk (directed_system.map_self fun (i j : ι) (h : i ≤ j) => ⇑(f i j h))
    (directed_system.map_map fun (i j : ι) (h : i ≤ j) => ⇑(f i j h))

protected instance add_comm_group {ι : Type v} [dec_ι : DecidableEq ι] [directed_order ι] (G : ι → Type w) [(i : ι) → add_comm_group (G i)] (f : (i j : ι) → i ≤ j → G i →+ G j) : add_comm_group (direct_limit G f) :=
  module.direct_limit.add_comm_group G fun (i j : ι) (hij : i ≤ j) => add_monoid_hom.to_int_linear_map (f i j hij)

protected instance inhabited {ι : Type v} [dec_ι : DecidableEq ι] [directed_order ι] (G : ι → Type w) [(i : ι) → add_comm_group (G i)] (f : (i j : ι) → i ≤ j → G i →+ G j) : Inhabited (direct_limit G f) :=
  { default := 0 }

/-- The canonical map from a component to the direct limit. -/
def of {ι : Type v} [dec_ι : DecidableEq ι] [directed_order ι] (G : ι → Type w) [(i : ι) → add_comm_group (G i)] (f : (i j : ι) → i ≤ j → G i →+ G j) (i : ι) : linear_map ℤ (G i) (direct_limit G f) :=
  module.direct_limit.of ℤ ι G (fun (i j : ι) (hij : i ≤ j) => add_monoid_hom.to_int_linear_map (f i j hij)) i

@[simp] theorem of_f {ι : Type v} [dec_ι : DecidableEq ι] [directed_order ι] {G : ι → Type w} [(i : ι) → add_comm_group (G i)] {f : (i j : ι) → i ≤ j → G i →+ G j} {i : ι} {j : ι} (hij : i ≤ j) (x : G i) : coe_fn (of G f j) (coe_fn (f i j hij) x) = coe_fn (of G f i) x :=
  module.direct_limit.of_f

protected theorem induction_on {ι : Type v} [dec_ι : DecidableEq ι] [directed_order ι] {G : ι → Type w} [(i : ι) → add_comm_group (G i)] {f : (i j : ι) → i ≤ j → G i →+ G j} [Nonempty ι] {C : direct_limit G f → Prop} (z : direct_limit G f) (ih : ∀ (i : ι) (x : G i), C (coe_fn (of G f i) x)) : C z :=
  module.direct_limit.induction_on z ih

/-- A component that corresponds to zero in the direct limit is already zero in some
bigger module in the directed system. -/
theorem of.zero_exact {ι : Type v} [dec_ι : DecidableEq ι] [directed_order ι] {G : ι → Type w} [(i : ι) → add_comm_group (G i)] {f : (i j : ι) → i ≤ j → G i →+ G j} [directed_system G fun (i j : ι) (h : i ≤ j) => ⇑(f i j h)] (i : ι) (x : G i) (h : coe_fn (of G f i) x = 0) : ∃ (j : ι), ∃ (hij : i ≤ j), coe_fn (f i j hij) x = 0 :=
  module.direct_limit.of.zero_exact h

/-- The universal property of the direct limit: maps from the components to another abelian group
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit. -/
def lift {ι : Type v} [dec_ι : DecidableEq ι] [directed_order ι] (G : ι → Type w) [(i : ι) → add_comm_group (G i)] (f : (i j : ι) → i ≤ j → G i →+ G j) (P : Type u₁) [add_comm_group P] (g : (i : ι) → G i →+ P) (Hg : ∀ (i j : ι) (hij : i ≤ j) (x : G i), coe_fn (g j) (coe_fn (f i j hij) x) = coe_fn (g i) x) : linear_map ℤ (direct_limit G f) P :=
  module.direct_limit.lift ℤ ι G (fun (i j : ι) (hij : i ≤ j) => add_monoid_hom.to_int_linear_map (f i j hij))
    (fun (i : ι) => add_monoid_hom.to_int_linear_map (g i)) Hg

@[simp] theorem lift_of {ι : Type v} [dec_ι : DecidableEq ι] [directed_order ι] {G : ι → Type w} [(i : ι) → add_comm_group (G i)] {f : (i j : ι) → i ≤ j → G i →+ G j} (P : Type u₁) [add_comm_group P] (g : (i : ι) → G i →+ P) (Hg : ∀ (i j : ι) (hij : i ≤ j) (x : G i), coe_fn (g j) (coe_fn (f i j hij) x) = coe_fn (g i) x) (i : ι) (x : G i) : coe_fn (lift G f P g Hg) (coe_fn (of G f i) x) = coe_fn (g i) x :=
  module.direct_limit.lift_of (fun (i : ι) => add_monoid_hom.to_int_linear_map (g i)) Hg x

theorem lift_unique {ι : Type v} [dec_ι : DecidableEq ι] [directed_order ι] {G : ι → Type w} [(i : ι) → add_comm_group (G i)] {f : (i j : ι) → i ≤ j → G i →+ G j} (P : Type u₁) [add_comm_group P] [Nonempty ι] (F : direct_limit G f →+ P) (x : direct_limit G f) : coe_fn F x =
  coe_fn
    (lift G f P (fun (i : ι) => add_monoid_hom.comp F (linear_map.to_add_monoid_hom (of G f i)))
      fun (i j : ι) (hij : i ≤ j) (x : G i) =>
        eq.mpr
          (id
            (Eq.trans
              ((fun (a a_1 : P) (e_1 : a = a_1) (ᾰ ᾰ_1 : P) (e_2 : ᾰ = ᾰ_1) => congr (congr_arg Eq e_1) e_2)
                (coe_fn ((fun (i : ι) => add_monoid_hom.comp F (linear_map.to_add_monoid_hom (of G f i))) j)
                  (coe_fn (f i j hij) x))
                (coe_fn F (coe_fn (of G f i) x))
                (Eq.trans
                  (Eq.trans
                    (Eq.trans
                      (congr_fun (add_monoid_hom.coe_comp F (linear_map.to_add_monoid_hom (of G f j)))
                        (coe_fn (f i j hij) x))
                      ((fun (f_1 f_2 : direct_limit G f → P) (e_1 : f_1 = f_2) (g g_1 : G j → direct_limit G f)
                          (e_2 : g = g_1) (ᾰ ᾰ_1 : G j) (e_3 : ᾰ = ᾰ_1) =>
                          congr (congr (congr_arg function.comp e_1) e_2) e_3)
                        (⇑F) (⇑F) (Eq.refl ⇑F) (⇑(linear_map.to_add_monoid_hom (of G f j))) (⇑(of G f j))
                        (linear_map.to_add_monoid_hom_coe (of G f j)) (coe_fn (f i j hij) x) (coe_fn (f i j hij) x)
                        (Eq.refl (coe_fn (f i j hij) x))))
                    (function.comp_app (⇑F) (⇑(of G f j)) (coe_fn (f i j hij) x)))
                  ((fun (x x_1 : direct_limit G f →+ P) (e_1 : x = x_1) (ᾰ ᾰ_1 : direct_limit G f) (e_2 : ᾰ = ᾰ_1) =>
                      congr (congr_arg coe_fn e_1) e_2)
                    F F (Eq.refl F) (coe_fn (of G f j) (coe_fn (f i j hij) x)) (coe_fn (of G f i) x) (of_f hij x)))
                (coe_fn ((fun (i : ι) => add_monoid_hom.comp F (linear_map.to_add_monoid_hom (of G f i))) i) x)
                (coe_fn F (coe_fn (of G f i) x))
                (Eq.trans
                  (Eq.trans (congr_fun (add_monoid_hom.coe_comp F (linear_map.to_add_monoid_hom (of G f i))) x)
                    ((fun (f_1 f_2 : direct_limit G f → P) (e_1 : f_1 = f_2) (g g_1 : G i → direct_limit G f)
                        (e_2 : g = g_1) (ᾰ ᾰ_1 : G i) (e_3 : ᾰ = ᾰ_1) =>
                        congr (congr (congr_arg function.comp e_1) e_2) e_3)
                      (⇑F) (⇑F) (Eq.refl ⇑F) (⇑(linear_map.to_add_monoid_hom (of G f i))) (⇑(of G f i))
                      (linear_map.to_add_monoid_hom_coe (of G f i)) x x (Eq.refl x)))
                  (function.comp_app (⇑F) (⇑(of G f i)) x)))
              (propext (eq_self_iff_true (coe_fn F (coe_fn (of G f i) x))))))
          trivial)
    x := sorry

end direct_limit


end add_comm_group


namespace ring


/-- The direct limit of a directed system is the rings glued together along the maps. -/
def direct_limit {ι : Type v} [directed_order ι] (G : ι → Type w) [(i : ι) → comm_ring (G i)] (f : (i j : ι) → i ≤ j → G i → G j)  :=
  ideal.quotient
    (ideal.span
      (set_of
        fun (a : free_comm_ring (sigma fun (i : ι) => G i)) =>
          (∃ (i : ι),
              ∃ (j : ι),
                ∃ (H : i ≤ j),
                  ∃ (x : G i), free_comm_ring.of (sigma.mk j (f i j H x)) - free_comm_ring.of (sigma.mk i x) = a) ∨
            (∃ (i : ι), free_comm_ring.of (sigma.mk i 1) - 1 = a) ∨
              (∃ (i : ι),
                  ∃ (x : G i),
                    ∃ (y : G i),
                      free_comm_ring.of (sigma.mk i (x + y)) -
                          (free_comm_ring.of (sigma.mk i x) + free_comm_ring.of (sigma.mk i y)) =
                        a) ∨
                ∃ (i : ι),
                  ∃ (x : G i),
                    ∃ (y : G i),
                      free_comm_ring.of (sigma.mk i (x * y)) -
                          free_comm_ring.of (sigma.mk i x) * free_comm_ring.of (sigma.mk i y) =
                        a))

namespace direct_limit


protected instance comm_ring {ι : Type v} [directed_order ι] (G : ι → Type w) [(i : ι) → comm_ring (G i)] (f : (i j : ι) → i ≤ j → G i → G j) : comm_ring (direct_limit G f) :=
  ideal.quotient.comm_ring
    (ideal.span
      (set_of
        fun (a : free_comm_ring (sigma fun (i : ι) => G i)) =>
          (∃ (i : ι),
              ∃ (j : ι),
                ∃ (H : i ≤ j),
                  ∃ (x : G i), free_comm_ring.of (sigma.mk j (f i j H x)) - free_comm_ring.of (sigma.mk i x) = a) ∨
            (∃ (i : ι), free_comm_ring.of (sigma.mk i 1) - 1 = a) ∨
              (∃ (i : ι),
                  ∃ (x : G i),
                    ∃ (y : G i),
                      free_comm_ring.of (sigma.mk i (x + y)) -
                          (free_comm_ring.of (sigma.mk i x) + free_comm_ring.of (sigma.mk i y)) =
                        a) ∨
                ∃ (i : ι),
                  ∃ (x : G i),
                    ∃ (y : G i),
                      free_comm_ring.of (sigma.mk i (x * y)) -
                          free_comm_ring.of (sigma.mk i x) * free_comm_ring.of (sigma.mk i y) =
                        a))

protected instance ring {ι : Type v} [directed_order ι] (G : ι → Type w) [(i : ι) → comm_ring (G i)] (f : (i j : ι) → i ≤ j → G i → G j) : ring (direct_limit G f) :=
  comm_ring.to_ring (direct_limit G f)

protected instance inhabited {ι : Type v} [directed_order ι] (G : ι → Type w) [(i : ι) → comm_ring (G i)] (f : (i j : ι) → i ≤ j → G i → G j) : Inhabited (direct_limit G f) :=
  { default := 0 }

/-- The canonical map from a component to the direct limit. -/
def of {ι : Type v} [directed_order ι] (G : ι → Type w) [(i : ι) → comm_ring (G i)] (f : (i j : ι) → i ≤ j → G i → G j) (i : ι) : G i →+* direct_limit G f := sorry

@[simp] theorem of_f {ι : Type v} [directed_order ι] {G : ι → Type w} [(i : ι) → comm_ring (G i)] {f : (i j : ι) → i ≤ j → G i → G j} {i : ι} {j : ι} (hij : i ≤ j) (x : G i) : coe_fn (of G f j) (f i j hij x) = coe_fn (of G f i) x :=
  iff.mpr ideal.quotient.eq
    (submodule.subset_span (Or.inl (Exists.intro i (Exists.intro j (Exists.intro hij (Exists.intro x rfl))))))

/-- Every element of the direct limit corresponds to some element in
some component of the directed system. -/
theorem exists_of {ι : Type v} [directed_order ι] {G : ι → Type w} [(i : ι) → comm_ring (G i)] {f : (i j : ι) → i ≤ j → G i → G j} [Nonempty ι] (z : direct_limit G f) : ∃ (i : ι), ∃ (x : G i), coe_fn (of G f i) x = z := sorry

theorem polynomial.exists_of {ι : Type v} [directed_order ι] {G : ι → Type w} [(i : ι) → comm_ring (G i)] {f' : (i j : ι) → i ≤ j → G i →+* G j} [Nonempty ι] (q : polynomial (direct_limit G fun (i j : ι) (h : i ≤ j) => ⇑(f' i j h))) : ∃ (i : ι), ∃ (p : polynomial (G i)), polynomial.map (of G (fun (i j : ι) (h : i ≤ j) => ⇑(f' i j h)) i) p = q := sorry

theorem induction_on {ι : Type v} [directed_order ι] {G : ι → Type w} [(i : ι) → comm_ring (G i)] {f : (i j : ι) → i ≤ j → G i → G j} [Nonempty ι] {C : direct_limit G f → Prop} (z : direct_limit G f) (ih : ∀ (i : ι) (x : G i), C (coe_fn (of G f i) x)) : C z := sorry

theorem of.zero_exact_aux2 {ι : Type v} [directed_order ι] (G : ι → Type w) [(i : ι) → comm_ring (G i)] (f' : (i j : ι) → i ≤ j → G i →+* G j) [directed_system G fun (i j : ι) (h : i ≤ j) => ⇑(f' i j h)] {x : free_comm_ring (sigma fun (i : ι) => G i)} {s : set (sigma fun (i : ι) => G i)} {t : set (sigma fun (i : ι) => G i)} (hxs : free_comm_ring.is_supported x s) {j : ι} {k : ι} (hj : ∀ (z : sigma fun (i : ι) => G i), z ∈ s → sigma.fst z ≤ j) (hk : ∀ (z : sigma fun (i : ι) => G i), z ∈ t → sigma.fst z ≤ k) (hjk : j ≤ k) (hst : s ⊆ t) : coe_fn (f' j k hjk)
    (coe_fn
      (free_comm_ring.lift
        fun (ix : ↥s) =>
          coe_fn (f' (sigma.fst (subtype.val ix)) j (hj (↑ix) (subtype.pro