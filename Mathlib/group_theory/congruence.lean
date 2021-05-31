/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.setoid.basic
import Mathlib.algebra.group.pi
import Mathlib.algebra.group.prod
import Mathlib.data.equiv.mul_add
import Mathlib.group_theory.submonoid.operations
import Mathlib.PostPort

universes u_1 l u_3 u_2 

namespace Mathlib

/-!
# Congruence relations

This file defines congruence relations: equivalence relations that preserve a binary operation,
which in this case is multiplication or addition. The principal definition is a `structure`
extending a `setoid` (an equivalence relation), and the inductive definition of the smallest
congruence relation containing a binary relation is also given (see `con_gen`).

The file also proves basic properties of the quotient of a type by a congruence relation, and the
complete lattice of congruence relations on a type. We then establish an order-preserving bijection
between the set of congruence relations containing a congruence relation `c` and the set of
congruence relations on the quotient by `c`.

The second half of the file concerns congruence relations on monoids, in which case the
quotient by the congruence relation is also a monoid. There are results about the universal
property of quotients of monoids, and the isomorphism theorems for monoids.

## Implementation notes

The inductive definition of a congruence relation could be a nested inductive type, defined using
the equivalence closure of a binary relation `eqv_gen`, but the recursor generated does not work.
A nested inductive definition could conceivably shorten proofs, because they would allow invocation
of the corresponding lemmas about `eqv_gen`.

The lemmas `refl`, `symm` and `trans` are not tagged with `@[refl]`, `@[symm]`, and `@[trans]`
respectively as these tags do not work on a structure coerced to a binary relation.

There is a coercion from elements of a type to the element's equivalence class under a
congruence relation.

A congruence relation on a monoid `M` can be thought of as a submonoid of `M × M` for which
membership is an equivalence relation, but whilst this fact is established in the file, it is not
used, since this perspective adds more layers of definitional unfolding.

## Tags

congruence, congruence relation, quotient, quotient by congruence relation, monoid,
quotient monoid, isomorphism theorems
-/

/-- A congruence relation on a type with an addition is an equivalence relation which
    preserves addition. -/
structure add_con (M : Type u_1) [Add M] 
extends setoid M
where
  add' : ∀ {w x y z : M}, r w x → r y z → r (w + y) (x + z)

/-- A congruence relation on a type with a multiplication is an equivalence relation which
    preserves multiplication. -/
structure con (M : Type u_1) [Mul M] 
extends setoid M
where
  mul' : ∀ {w x y z : M}, r w x → r y z → r (w * y) (x * z)

/-- The equivalence relation underlying an additive congruence relation. -/
/-- The equivalence relation underlying a multiplicative congruence relation. -/
/-- The inductively defined smallest additive congruence relation containing a given binary
    relation. -/
inductive add_con_gen.rel {M : Type u_1} [Add M] (r : M → M → Prop) : M → M → Prop
where
| of : ∀ (x y : M), r x y → add_con_gen.rel r x y
| refl : ∀ (x : M), add_con_gen.rel r x x
| symm : ∀ (x y : M), add_con_gen.rel r x y → add_con_gen.rel r y x
| trans : ∀ (x y z : M), add_con_gen.rel r x y → add_con_gen.rel r y z → add_con_gen.rel r x z
| add : ∀ (w x y z : M), add_con_gen.rel r w x → add_con_gen.rel r y z → add_con_gen.rel r (w + y) (x + z)

/-- The inductively defined smallest multiplicative congruence relation containing a given binary
    relation. -/
inductive con_gen.rel {M : Type u_1} [Mul M] (r : M → M → Prop) : M → M → Prop
where
| of : ∀ (x y : M), r x y → con_gen.rel r x y
| refl : ∀ (x : M), con_gen.rel r x x
| symm : ∀ (x y : M), con_gen.rel r x y → con_gen.rel r y x
| trans : ∀ (x y z : M), con_gen.rel r x y → con_gen.rel r y z → con_gen.rel r x z
| mul : ∀ (w x y z : M), con_gen.rel r w x → con_gen.rel r y z → con_gen.rel r (w * y) (x * z)

/-- The inductively defined smallest multiplicative congruence relation containing a given binary
    relation. -/
def con_gen {M : Type u_1} [Mul M] (r : M → M → Prop) : con M :=
  con.mk sorry sorry sorry

namespace con


protected instance Mathlib.add_con.inhabited {M : Type u_1} [Add M] : Inhabited (add_con M) :=
  { default := add_con_gen empty_relation }

/-- A coercion from a congruence relation to its underlying binary relation. -/
protected instance Mathlib.add_con.has_coe_to_fun {M : Type u_1} [Add M] : has_coe_to_fun (add_con M) :=
  has_coe_to_fun.mk (fun (c : add_con M) => M → M → Prop) fun (c : add_con M) (x y : M) => add_con.r c x y

@[simp] theorem Mathlib.add_con.rel_eq_coe {M : Type u_1} [Add M] (c : add_con M) : add_con.r c = ⇑c :=
  rfl

/-- Congruence relations are reflexive. -/
protected theorem Mathlib.add_con.refl {M : Type u_1} [Add M] (c : add_con M) (x : M) : coe_fn c x x :=
  and.left (add_con.iseqv c) x

/-- Congruence relations are symmetric. -/
protected theorem Mathlib.add_con.symm {M : Type u_1} [Add M] (c : add_con M) {x : M} {y : M} : coe_fn c x y → coe_fn c y x :=
  fun (h : coe_fn c _x✝ _x) => and.left (and.right (add_con.iseqv c)) _x✝ _x h

/-- Congruence relations are transitive. -/
protected theorem Mathlib.add_con.trans {M : Type u_1} [Add M] (c : add_con M) {x : M} {y : M} {z : M} : coe_fn c x y → coe_fn c y z → coe_fn c x z :=
  fun (h : coe_fn c _x✝¹ _x✝) => and.right (and.right (add_con.iseqv c)) _x✝¹ _x✝ _x h

/-- Multiplicative congruence relations preserve multiplication. -/
protected theorem Mathlib.add_con.add {M : Type u_1} [Add M] (c : add_con M) {w : M} {x : M} {y : M} {z : M} : coe_fn c w x → coe_fn c y z → coe_fn c (w + y) (x + z) :=
  fun (h1 : coe_fn c _x✝² _x✝¹) (h2 : coe_fn c _x✝ _x) => add_con.add' c h1 h2

/-- Given a type `M` with a multiplication, a congruence relation `c` on `M`, and elements of `M`
    `x, y`, `(x, y) ∈ M × M` iff `x` is related to `y` by `c`. -/
protected instance Mathlib.add_con.has_mem {M : Type u_1} [Add M] : has_mem (M × M) (add_con M) :=
  has_mem.mk fun (x : M × M) (c : add_con M) => coe_fn c (prod.fst x) (prod.snd x)

/-- The map sending a congruence relation to its underlying binary relation is injective. -/
theorem Mathlib.add_con.ext' {M : Type u_1} [Add M] {c : add_con M} {d : add_con M} (H : add_con.r c = add_con.r d) : c = d := sorry

/-- Extensionality rule for congruence relations. -/
theorem Mathlib.add_con.ext {M : Type u_1} [Add M] {c : add_con M} {d : add_con M} (H : ∀ (x y : M), coe_fn c x y ↔ coe_fn d x y) : c = d :=
  add_con.ext' (funext fun (x : M) => funext fun (x_1 : M) => propext (H x x_1))

/-- The map sending a congruence relation to its underlying equivalence relation is injective. -/
theorem to_setoid_inj {M : Type u_1} [Mul M] {c : con M} {d : con M} (H : to_setoid c = to_setoid d) : c = d :=
  ext (iff.mp setoid.ext_iff H)

/-- Iff version of extensionality rule for congruence relations. -/
theorem Mathlib.add_con.ext_iff {M : Type u_1} [Add M] {c : add_con M} {d : add_con M} : (∀ (x y : M), coe_fn c x y ↔ coe_fn d x y) ↔ c = d :=
  { mp := add_con.ext, mpr := fun (h : c = d) (_x _x_1 : M) => h ▸ iff.rfl }

/-- Two congruence relations are equal iff their underlying binary relations are equal. -/
theorem ext'_iff {M : Type u_1} [Mul M] {c : con M} {d : con M} : r c = r d ↔ c = d :=
  { mp := ext', mpr := fun (h : c = d) => h ▸ rfl }

/-- The kernel of a multiplication-preserving function as a congruence relation. -/
def mul_ker {M : Type u_1} {P : Type u_3} [Mul M] [Mul P] (f : M → P) (h : ∀ (x y : M), f (x * y) = f x * f y) : con M :=
  mk (fun (x y : M) => f x = f y) sorry sorry

/-- Given types with multiplications `M, N`, the product of two congruence relations `c` on `M` and
    `d` on `N`: `(x₁, x₂), (y₁, y₂) ∈ M × N` are related by `c.prod d` iff `x₁` is related to `y₁`
    by `c` and `x₂` is related to `y₂` by `d`. -/
protected def Mathlib.add_con.prod {M : Type u_1} {N : Type u_2} [Add M] [Add N] (c : add_con M) (d : add_con N) : add_con (M × N) :=
  add_con.mk setoid.r sorry sorry

/-- The product of an indexed collection of congruence relations. -/
def Mathlib.add_con.pi {ι : Type u_1} {f : ι → Type u_2} [(i : ι) → Add (f i)] (C : (i : ι) → add_con (f i)) : add_con ((i : ι) → f i) :=
  add_con.mk setoid.r sorry sorry

@[simp] theorem Mathlib.add_con.coe_eq {M : Type u_1} [Add M] (c : add_con M) : setoid.r = ⇑c :=
  rfl

-- Quotients

/-- Defining the quotient by a congruence relation of a type with a multiplication. -/
protected def Mathlib.add_con.quotient {M : Type u_1} [Add M] (c : add_con M) :=
  quotient (add_con.to_setoid c)

/-- Coercion from a type with a multiplication to its quotient by a congruence relation.

See Note [use has_coe_t]. -/
protected instance quotient.has_coe_t {M : Type u_1} [Mul M] (c : con M) : has_coe_t M (con.quotient c) :=
  has_coe_t.mk quotient.mk

/-- The quotient of a type with decidable equality by a congruence relation also has
    decidable equality. -/
protected instance quotient.decidable_eq {M : Type u_1} [Mul M] (c : con M) [d : (a b : M) → Decidable (coe_fn c a b)] : DecidableEq (con.quotient c) :=
  quotient.decidable_eq

/-- The function on the quotient by a congruence relation `c` induced by a function that is
    constant on `c`'s equivalence classes. -/
protected def Mathlib.add_con.lift_on {M : Type u_1} [Add M] {β : Sort u_2} {c : add_con M} (q : add_con.quotient c) (f : M → β) (h : ∀ (a b : M), coe_fn c a b → f a = f b) : β :=
  quotient.lift_on' q f h

/-- The binary function on the quotient by a congruence relation `c` induced by a binary function
    that is constant on `c`'s equivalence classes. -/
protected def Mathlib.add_con.lift_on₂ {M : Type u_1} [Add M] {β : Sort u_2} {c : add_con M} (q : add_con.quotient c) (r : add_con.quotient c) (f : M → M → β) (h : ∀ (a₁ a₂ b₁ b₂ : M), coe_fn c a₁ b₁ → coe_fn c a₂ b₂ → f a₁ a₂ = f b₁ b₂) : β :=
  quotient.lift_on₂' q r f h

/-- The inductive principle used to prove propositions about the elements of a quotient by a
    congruence relation. -/
protected theorem Mathlib.add_con.induction_on {M : Type u_1} [Add M] {c : add_con M} {C : add_con.quotient c → Prop} (q : add_con.quotient c) (H : ∀ (x : M), C ↑x) : C q :=
  quotient.induction_on' q H

/-- A version of `con.induction_on` for predicates which take two arguments. -/
protected theorem Mathlib.add_con.induction_on₂ {M : Type u_1} {N : Type u_2} [Add M] [Add N] {c : add_con M} {d : add_con N} {C : add_con.quotient c → add_con.quotient d → Prop} (p : add_con.quotient c) (q : add_con.quotient d) (H : ∀ (x : M) (y : N), C ↑x ↑y) : C p q :=
  quotient.induction_on₂' p q H

/-- Two elements are related by a congruence relation `c` iff they are represented by the same
    element of the quotient by `c`. -/
@[simp] protected theorem Mathlib.add_con.eq {M : Type u_1} [Add M] (c : add_con M) {a : M} {b : M} : ↑a = ↑b ↔ coe_fn c a b :=
  quotient.eq'

/-- The multiplication induced on the quotient by a congruence relation on a type with a
    multiplication. -/
protected instance has_mul {M : Type u_1} [Mul M] (c : con M) : Mul (con.quotient c) :=
  { mul := fun (x y : con.quotient c) => quotient.lift_on₂' x y (fun (w z : M) => ↑(w * z)) sorry }

/-- The kernel of the quotient map induced by a congruence relation `c` equals `c`. -/
@[simp] theorem mul_ker_mk_eq {M : Type u_1} [Mul M] (c : con M) : (mul_ker coe fun (x y : M) => rfl) = c :=
  ext fun (x y : M) => quotient.eq'

/-- The coercion to the quotient of a congruence relation commutes with multiplication (by
    definition). -/
@[simp] theorem Mathlib.add_con.coe_add {M : Type u_1} [Add M] {c : add_con M} (x : M) (y : M) : ↑(x + y) = ↑x + ↑y :=
  rfl

/-- Definition of the function on the quotient by a congruence relation `c` induced by a function
    that is constant on `c`'s equivalence classes. -/
@[simp] protected theorem lift_on_beta {M : Type u_1} [Mul M] {β : Sort u_2} (c : con M) (f : M → β) (h : ∀ (a b : M), coe_fn c a b → f a = f b) (x : M) : con.lift_on (↑x) f h = f x :=
  rfl

/-- Makes an isomorphism of quotients by two congruence relations, given that the relations are
    equal. -/
protected def Mathlib.add_con.congr {M : Type u_1} [Add M] {c : add_con M} {d : add_con M} (h : c = d) : add_con.quotient c ≃+ add_con.quotient d :=
  add_equiv.mk (equiv.to_fun (quotient.congr (equiv.refl M) sorry)) (equiv.inv_fun (quotient.congr (equiv.refl M) sorry))
    sorry sorry sorry

-- The complete lattice of congruence relations on a type

/-- For congruence relations `c, d` on a type `M` with a multiplication, `c ≤ d` iff `∀ x y ∈ M`,
    `x` is related to `y` by `d` if `x` is related to `y` by `c`. -/
protected instance Mathlib.add_con.has_le {M : Type u_1} [Add M] : HasLessEq (add_con M) :=
  { LessEq := fun (c d : add_con M) => ∀ {x y : M}, coe_fn c x y → coe_fn d x y }

/-- Definition of `≤` for congruence relations. -/
theorem Mathlib.add_con.le_def {M : Type u_1} [Add M] {c : add_con M} {d : add_con M} : c ≤ d ↔ ∀ {x y : M}, coe_fn c x y → coe_fn d x y :=
  iff.rfl

/-- The infimum of a set of congruence relations on a given type with a multiplication. -/
protected instance Mathlib.add_con.has_Inf {M : Type u_1} [Add M] : has_Inf (add_con M) :=
  has_Inf.mk
    fun (S : set (add_con M)) => add_con.mk (fun (x y : M) => ∀ (c : add_con M), c ∈ S → coe_fn c x y) sorry sorry

/-- The infimum of a set of congruence relations is the same as the infimum of the set's image
    under the map to the underlying equivalence relation. -/
theorem Mathlib.add_con.Inf_to_setoid {M : Type u_1} [Add M] (S : set (add_con M)) : add_con.to_setoid (Inf S) = Inf (add_con.to_setoid '' S) := sorry

/-- The infimum of a set of congruence relations is the same as the infimum of the set's image
    under the map to the underlying binary relation. -/
theorem Inf_def {M : Type u_1} [Mul M] (S : set (con M)) : r (Inf S) = Inf (r '' S) := sorry

protected instance Mathlib.add_con.partial_order {M : Type u_1} [Add M] : partial_order (add_con M) :=
  partial_order.mk LessEq (fun (c d : add_con M) => c ≤ d ∧ ¬d ≤ c) sorry sorry sorry

/-- The complete lattice of congruence relations on a given type with a multiplication. -/
protected instance complete_lattice {M : Type u_1} [Mul M] : complete_lattice (con M) :=
  complete_lattice.mk complete_lattice.sup complete_lattice.le complete_lattice.lt sorry sorry sorry sorry sorry sorry
    (fun (c d : con M) => mk setoid.r sorry sorry) sorry sorry sorry (mk setoid.r sorry sorry) sorry
    (mk setoid.r sorry sorry) sorry complete_lattice.Sup complete_lattice.Inf sorry sorry sorry sorry

/-- The infimum of two congruence relations equals the infimum of the underlying binary
    operations. -/
theorem Mathlib.add_con.inf_def {M : Type u_1} [Add M] {c : add_con M} {d : add_con M} : add_con.r (c ⊓ d) = add_con.r c ⊓ add_con.r d :=
  rfl

/-- Definition of the infimum of two congruence relations. -/
theorem Mathlib.add_con.inf_iff_and {M : Type u_1} [Add M] {c : add_con M} {d : add_con M} {x : M} {y : M} : coe_fn (c ⊓ d) x y ↔ coe_fn c x y ∧ coe_fn d x y :=
  iff.rfl

/-- The inductively defined smallest congruence relation containing a binary relation `r` equals
    the infimum of the set of congruence relations containing `r`. -/
theorem Mathlib.add_con.add_con_gen_eq {M : Type u_1} [Add M] (r : M → M → Prop) : add_con_gen r = Inf (set_of fun (s : add_con M) => ∀ (x y : M), r x y → coe_fn s x y) := sorry

/-- The smallest congruence relation containing a binary relation `r` is contained in any
    congruence relation containing `r`. -/
theorem con_gen_le {M : Type u_1} [Mul M] {r : M → M → Prop} {c : con M} (h : ∀ (x y : M), r x y → r c x y) : con_gen r ≤ c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (con_gen r ≤ c)) (con_gen_eq r))) (Inf_le h)

/-- Given binary relations `r, s` with `r` contained in `s`, the smallest congruence relation
    containing `s` contains the smallest congruence relation containing `r`. -/
theorem Mathlib.add_con.add_con_gen_mono {M : Type u_1} [Add M] {r : M → M → Prop} {s : M → M → Prop} (h : ∀ (x y : M), r x y → s x y) : add_con_gen r ≤ add_con_gen s :=
  add_con.add_con_gen_le fun (x y : M) (hr : r x y) => add_con_gen.rel.of x y (h x y hr)

/-- Congruence relations equal the smallest congruence relation in which they are contained. -/
@[simp] theorem con_gen_of_con {M : Type u_1} [Mul M] (c : con M) : con_gen ⇑c = c :=
  le_antisymm (eq.mpr (id (Eq._oldrec (Eq.refl (con_gen ⇑c ≤ c)) (con_gen_eq ⇑c))) (Inf_le fun (_x _x_1 : M) => id))
    con_gen.rel.of

/-- The map sending a binary relation to the smallest congruence relation in which it is
    contained is idempotent. -/
@[simp] theorem Mathlib.add_con.add_con_gen_idem {M : Type u_1} [Add M] (r : M → M → Prop) : add_con_gen ⇑(add_con_gen r) = add_con_gen r :=
  add_con.add_con_gen_of_add_con (add_con_gen r)

/-- The supremum of congruence relations `c, d` equals the smallest congruence relation containing
    the binary relation '`x` is related to `y` by `c` or `d`'. -/
theorem sup_eq_con_gen {M : Type u_1} [Mul M] (c : con M) (d : con M) : c ⊔ d = con_gen fun (x y : M) => coe_fn c x y ∨ coe_fn d x y := sorry

/-- The supremum of two congruence relations equals the smallest congruence relation containing
    the supremum of the underlying binary operations. -/
theorem Mathlib.add_con.sup_def {M : Type u_1} [Add M] {c : add_con M} {d : add_con M} : c ⊔ d = add_con_gen (add_con.r c ⊔ add_con.r d) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (c ⊔ d = add_con_gen (add_con.r c ⊔ add_con.r d))) (add_con.sup_eq_add_con_gen c d)))
    (Eq.refl (add_con_gen fun (x y : M) => coe_fn c x y ∨ coe_fn d x y))

/-- The supremum of a set of congruence relations `S` equals the smallest congruence relation
    containing the binary relation 'there exists `c ∈ S` such that `x` is related to `y` by
    `c`'. -/
theorem Mathlib.add_con.Sup_eq_add_con_gen {M : Type u_1} [Add M] (S : set (add_con M)) : Sup S = add_con_gen fun (x y : M) => ∃ (c : add_con M), c ∈ S ∧ coe_fn c x y := sorry

/-- The supremum of a set of congruence relations is the same as the smallest congruence relation
    containing the supremum of the set's image under the map to the underlying binary relation. -/
theorem Mathlib.add_con.Sup_def {M : Type u_1} [Add M] {S : set (add_con M)} : Sup S = add_con_gen (Sup (add_con.r '' S)) := sorry

/-- There is a Galois insertion of congruence relations on a type with a multiplication `M` into
    binary relations on `M`. -/
protected def gi (M : Type u_1) [Mul M] : galois_insertion con_gen r :=
  galois_insertion.mk (fun (r : M → M → Prop) (h : r (con_gen r) ≤ r) => con_gen r) sorry sorry sorry

/-- Given a function `f`, the smallest congruence relation containing the binary relation on `f`'s
    image defined by '`x ≈ y` iff the elements of `f⁻¹(x)` are related to the elements of `f⁻¹(y)`
    by a congruence relation `c`.' -/
def Mathlib.add_con.map_gen {M : Type u_1} {N : Type u_2} [Add M] [Add N] (c : add_con M) (f : M → N) : add_con N :=
  add_con_gen fun (x y : N) => ∃ (a : M), ∃ (b : M), f a = x ∧ f b = y ∧ coe_fn c a b

/-- Given a surjective multiplicative-preserving function `f` whose kernel is contained in a
    congruence relation `c`, the congruence relation on `f`'s codomain defined by '`x ≈ y` iff the
    elements of `f⁻¹(x)` are related to the elements of `f⁻¹(y)` by `c`.' -/
def Mathlib.add_con.map_of_surjective {M : Type u_1} {N : Type u_2} [Add M] [Add N] (c : add_con M) (f : M → N) (H : ∀ (x y : M), f (x + y) = f x + f y) (h : add_con.add_ker f H ≤ c) (hf : function.surjective f) : add_con N :=
  add_con.mk setoid.r sorry sorry

/-- A specialization of 'the smallest congruence relation containing a congruence relation `c`
    equals `c`'. -/
theorem Mathlib.add_con.map_of_surjective_eq_map_gen {M : Type u_1} {N : Type u_2} [Add M] [Add N] {c : add_con M} {f : M → N} (H : ∀ (x y : M), f (x + y) = f x + f y) (h : add_con.add_ker f H ≤ c) (hf : function.surjective f) : add_con.map_gen c f = add_con.map_of_surjective c f H h hf := sorry

/-- Given types with multiplications `M, N` and a congruence relation `c` on `N`, a
    multiplication-preserving map `f : M → N` induces a congruence relation on `f`'s domain
    defined by '`x ≈ y` iff `f(x)` is related to `f(y)` by `c`.' -/
def Mathlib.add_con.comap {M : Type u_1} {N : Type u_2} [Add M] [Add N] (f : M → N) (H : ∀ (x y : M), f (x + y) = f x + f y) (c : add_con N) : add_con M :=
  add_con.mk setoid.r sorry sorry

/-- Given a congruence relation `c` on a type `M` with a multiplication, the order-preserving
    bijection between the set of congruence relations containing `c` and the congruence relations
    on the quotient of `M` by `c`. -/
def Mathlib.add_con.correspondence {M : Type u_1} [Add M] (c : add_con M) : (Subtype fun (d : add_con M) => c ≤ d) ≃o add_con (add_con.quotient c) :=
  rel_iso.mk
    (equiv.mk
      (fun (d : Subtype fun (d : add_con M) => c ≤ d) => add_con.map_of_surjective (subtype.val d) coe sorry sorry sorry)
      (fun (d : add_con (add_con.quotient c)) => { val := add_con.comap coe sorry d, property := sorry }) sorry sorry)
    sorry

-- Monoids

/-- The quotient of a monoid by a congruence relation is a monoid. -/
protected instance monoid {M : Type u_1} [monoid M] (c : con M) : monoid (con.quotient c) :=
  monoid.mk Mul.mul sorry ↑1 sorry sorry

/-- The quotient of a `comm_monoid` by a congruence relation is a `comm_monoid`. -/
protected instance Mathlib.add_con.add_comm_monoid {α : Type u_1} [add_comm_monoid α] (c : add_con α) : add_comm_monoid (add_con.quotient c) :=
  add_comm_monoid.mk add_monoid.add sorry add_monoid.zero sorry sorry sorry

/-- The 1 of the quotient of a monoid by a congruence relation is the equivalence class of the
    monoid's 1. -/
@[simp] theorem coe_one {M : Type u_1} [monoid M] {c : con M} : ↑1 = 1 :=
  rfl

/-- The submonoid of `M × M` defined by a congruence relation on a monoid `M`. -/
protected def Mathlib.add_con.add_submonoid (M : Type u_1) [add_monoid M] (c : add_con M) : add_submonoid (M × M) :=
  add_submonoid.mk (set_of fun (x : M × M) => coe_fn c (prod.fst x) (prod.snd x)) sorry sorry

/-- The congruence relation on a monoid `M` from a submonoid of `M × M` for which membership
    is an equivalence relation. -/
def Mathlib.add_con.of_add_submonoid {M : Type u_1} [add_monoid M] (N : add_submonoid (M × M)) (H : equivalence fun (x y : M) => (x, y) ∈ N) : add_con M :=
  add_con.mk (fun (x y : M) => (x, y) ∈ N) H sorry

/-- Coercion from a congruence relation `c` on a monoid `M` to the submonoid of `M × M` whose
    elements are `(x, y)` such that `x` is related to `y` by `c`. -/
protected instance to_submonoid {M : Type u_1} [monoid M] : has_coe (con M) (submonoid (M × M)) :=
  has_coe.mk fun (c : con M) => con.submonoid M c

theorem Mathlib.add_con.mem_coe {M : Type u_1} [add_monoid M] {c : add_con M} {x : M} {y : M} : (x, y) ∈ ↑c ↔ (x, y) ∈ c :=
  iff.rfl

theorem to_submonoid_inj {M : Type u_1} [monoid M] (c : con M) (d : con M) (H : ↑c = ↑d) : c = d := sorry

theorem Mathlib.add_con.le_iff {M : Type u_1} [add_monoid M] {c : add_con M} {d : add_con M} : c ≤ d ↔ ↑c ≤ ↑d :=
  { mp := fun (h : c ≤ d) (x : M × M) (H : x ∈ ↑c) => h H,
    mpr := fun (h : ↑c ≤ ↑d) (x y : M) (hc : coe_fn c x y) => h ((fun (this : (x, y) ∈ c) => this) hc) }

/-- The kernel of a monoid homomorphism as a congruence relation. -/
def Mathlib.add_con.ker {M : Type u_1} {P : Type u_3} [add_monoid M] [add_monoid P] (f : M →+ P) : add_con M :=
  add_con.add_ker (⇑f) (add_monoid_hom.map_add' f)

/-- The definition of the congruence relation defined by a monoid homomorphism's kernel. -/
theorem ker_rel {M : Type u_1} {P : Type u_3} [monoid M] [monoid P] (f : M →* P) {x : M} {y : M} : coe_fn (ker f) x y ↔ coe_fn f x = coe_fn f y :=
  iff.rfl

/-- There exists an element of the quotient of a monoid by a congruence relation (namely 1). -/
protected instance quotient.inhabited {M : Type u_1} [monoid M] {c : con M} : Inhabited (con.quotient c) :=
  { default := ↑1 }

/-- The natural homomorphism from a monoid to its quotient by a congruence relation. -/
def Mathlib.add_con.mk' {M : Type u_1} [add_monoid M] (c : add_con M) : M →+ add_con.quotient c :=
  add_monoid_hom.mk coe sorry sorry

/-- The kernel of the natural homomorphism from a monoid to its quotient by a congruence
    relation `c` equals `c`. -/
@[simp] theorem Mathlib.add_con.mk'_ker {M : Type u_1} [add_monoid M] (c : add_con M) : add_con.ker (add_con.mk' c) = c :=
  add_con.ext fun (_x _x_1 : M) => add_con.eq c

/-- The natural homomorphism from a monoid to its quotient by a congruence relation is
    surjective. -/
theorem Mathlib.add_con.mk'_surjective {M : Type u_1} [add_monoid M] {c : add_con M} : function.surjective ⇑(add_con.mk' c) :=
  fun (x : add_con.quotient c) => quot.induction_on x fun (x : M) => Exists.intro x rfl

@[simp] theorem Mathlib.add_con.comp_mk'_apply {M : Type u_1} {P : Type u_3} [add_monoid M] [add_monoid P] {c : add_con M} (g : add_con.quotient c →+ P) {x : M} : coe_fn (add_monoid_hom.comp g (add_con.mk' c)) x = coe_fn g ↑x :=
  rfl

/-- The elements related to `x ∈ M`, `M` a monoid, by the kernel of a monoid homomorphism are
    those in the preimage of `f(x)` under `f`. -/
theorem Mathlib.add_con.ker_apply_eq_preimage {M : Type u_1} {P : Type u_3} [add_monoid M] [add_monoid P] {f : M →+ P} (x : M) : coe_fn (add_con.ker f) x = ⇑f ⁻¹' singleton (coe_fn f x) := sorry

/-- Given a monoid homomorphism `f : N → M` and a congruence relation `c` on `M`, the congruence
    relation induced on `N` by `f` equals the kernel of `c`'s quotient homomorphism composed with
    `f`. -/
theorem Mathlib.add_con.comap_eq {M : Type u_1} {N : Type u_2} [add_monoid M] [add_monoid N] {c : add_con M} {f : N →+ M} : add_con.comap (⇑f) (add_monoid_hom.map_add f) c = add_con.ker (add_monoid_hom.comp (add_con.mk' c) f) := sorry

/-- The homomorphism on the quotient of a monoid by a congruence relation `c` induced by a
    homomorphism constant on `c`'s equivalence classes. -/
def Mathlib.add_con.lift {M : Type u_1} {P : Type u_3} [add_monoid M] [add_monoid P] (c : add_con M) (f : M →+ P) (H : c ≤ add_con.ker f) : add_con.quotient c →+ P :=
  add_monoid_hom.mk (fun (x : add_con.quotient c) => add_con.lift_on x ⇑f sorry) sorry sorry

/-- The diagram describing the universal property for quotients of monoids commutes. -/
@[simp] theorem Mathlib.add_con.lift_mk' {M : Type u_1} {P : Type u_3} [add_monoid M] [add_monoid P] {c : add_con M} {f : M →+ P} (H : c ≤ add_con.ker f) (x : M) : coe_fn (add_con.lift c f H) (coe_fn (add_con.mk' c) x) = coe_fn f x :=
  rfl

/-- The diagram describing the universal property for quotients of monoids commutes. -/
@[simp] theorem Mathlib.add_con.lift_coe {M : Type u_1} {P : Type u_3} [add_monoid M] [add_monoid P] {c : add_con M} {f : M →+ P} (H : c ≤ add_con.ker f) (x : M) : coe_fn (add_con.lift c f H) ↑x = coe_fn f x :=
  rfl

/-- The diagram describing the universal property for quotients of monoids commutes. -/
@[simp] theorem Mathlib.add_con.lift_comp_mk' {M : Type u_1} {P : Type u_3} [add_monoid M] [add_monoid P] {c : add_con M} {f : M →+ P} (H : c ≤ add_con.ker f) : add_monoid_hom.comp (add_con.lift c f H) (add_con.mk' c) = f :=
  add_monoid_hom.ext fun (x : M) => Eq.refl (coe_fn (add_monoid_hom.comp (add_con.lift c f H) (add_con.mk' c)) x)

/-- Given a homomorphism `f` from the quotient of a monoid by a congruence relation, `f` equals the
    homomorphism on the quotient induced by `f` composed with the natural map from the monoid to
    the quotient. -/
@[simp] theorem Mathlib.add_con.lift_apply_mk' {M : Type u_1} {P : Type u_3} [add_monoid M] [add_monoid P] {c : add_con M} (f : add_con.quotient c →+ P) : (add_con.lift c (add_monoid_hom.comp f (add_con.mk' c))
    fun (x y : M) (h : coe_fn c x y) =>
      (fun (this : coe_fn f ↑x = coe_fn f ↑y) => this)
        (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn f ↑x = coe_fn f ↑y)) (iff.mpr (add_con.eq c) h)))
          (Eq.refl (coe_fn f ↑y)))) =
  f := sorry

/-- Homomorphisms on the quotient of a monoid by a congruence relation are equal if they
    are equal on elements that are coercions from the monoid. -/
theorem Mathlib.add_con.lift_funext {M : Type u_1} {P : Type u_3} [add_monoid M] [add_monoid P] {c : add_con M} (f : add_con.quotient c →+ P) (g : add_con.quotient c →+ P) (h : ∀ (a : M), coe_fn f ↑a = coe_fn g ↑a) : f = g := sorry

/-- The uniqueness part of the universal property for quotients of monoids. -/
theorem Mathlib.add_con.lift_unique {M : Type u_1} {P : Type u_3} [add_monoid M] [add_monoid P] {c : add_con M} {f : M →+ P} (H : c ≤ add_con.ker f) (g : add_con.quotient c →+ P) (Hg : add_monoid_hom.comp g (add_con.mk' c) = f) : g = add_con.lift c f H := sorry

/-- Given a congruence relation `c` on a monoid and a homomorphism `f` constant on `c`'s
    equivalence classes, `f` has the same image as the homomorphism that `f` induces on the
    quotient. -/
theorem Mathlib.add_con.lift_range {M : Type u_1} {P : Type u_3} [add_monoid M] [add_monoid P] {c : add_con M} {f : M →+ P} (H : c ≤ add_con.ker f) : add_monoid_hom.mrange (add_con.lift c f H) = add_monoid_hom.mrange f := sorry

/-- Surjective monoid homomorphisms constant on a congruence relation `c`'s equivalence classes
    induce a surjective homomorphism on `c`'s quotient. -/
theorem Mathlib.add_con.lift_surjective_of_surjective {M : Type u_1} {P : Type u_3} [add_monoid M] [add_monoid P] {c : add_con M} {f : M →+ P} (h : c ≤ add_con.ker f) (hf : function.surjective ⇑f) : function.surjective ⇑(add_con.lift c f h) :=
  fun (y : P) =>
    exists.elim (hf y) fun (w : M) (hw : coe_fn f w = y) => Exists.intro (↑w) (Eq.symm (add_con.lift_mk' h w) ▸ hw)

/-- Given a monoid homomorphism `f` from `M` to `P`, the kernel of `f` is the unique congruence
    relation on `M` whose induced map from the quotient of `M` to `P` is injective. -/
theorem Mathlib.add_con.ker_eq_lift_of_injective {M : Type u_1} {P : Type u_3} [add_monoid M] [add_monoid P] (c : add_con M) (f : M →+ P) (H : c ≤ add_con.ker f) (h : function.injective ⇑(add_con.lift c f H)) : add_con.ker f = c :=
  add_con.to_setoid_inj (setoid.ker_eq_lift_of_injective (⇑f) H h)

/-- The homomorphism induced on the quotient of a monoid by the kernel of a monoid homomorphism. -/
def Mathlib.add_con.ker_lift {M : Type u_1} {P : Type u_3} [add_monoid M] [add_monoid P] (f : M →+ P) : add_con.quotient (add_con.ker f) →+ P :=
  add_con.lift (add_con.ker f) f sorry

/-- The diagram described by the universal property for quotients of monoids, when the congruence
    relation is the kernel of the homomorphism, commutes. -/
@[simp] theorem ker_lift_mk {M : Type u_1} {P : Type u_3} [monoid M] [monoid P] {f : M →* P} (x : M) : coe_fn (ker_lift f) ↑x = coe_fn f x :=
  rfl

/-- Given a monoid homomorphism `f`, the induced homomorphism on the quotient by `f`'s kernel has
    the same image as `f`. -/
@[simp] theorem Mathlib.add_con.ker_lift_range_eq {M : Type u_1} {P : Type u_3} [add_monoid M] [add_monoid P] {f : M →+ P} : add_monoid_hom.mrange (add_con.ker_lift f) = add_monoid_hom.mrange f :=
  add_con.lift_range fun (_x _x_1 : M) => id

/-- A monoid homomorphism `f` induces an injective homomorphism on the quotient by `f`'s kernel. -/
theorem Mathlib.add_con.ker_lift_injective {M : Type u_1} {P : Type u_3} [add_monoid M] [add_monoid P] (f : M →+ P) : function.injective ⇑(add_con.ker_lift f) :=
  fun (x y : add_con.quotient (add_con.ker f)) =>
    quotient.induction_on₂' x y fun (_x _x_1 : M) => iff.mpr (add_con.eq (add_con.ker f))

/-- Given congruence relations `c, d` on a monoid such that `d` contains `c`, `d`'s quotient
    map induces a homomorphism from the quotient by `c` to the quotient by `d`. -/
def Mathlib.add_con.map {M : Type u_1} [add_monoid M] (c : add_con M) (d : add_con M) (h : c ≤ d) : add_con.quotient c →+ add_con.quotient d :=
  add_con.lift c (add_con.mk' d) sorry

/-- Given congruence relations `c, d` on a monoid such that `d` contains `c`, the definition of
    the homomorphism from the quotient by `c` to the quotient by `d` induced by `d`'s quotient
    map. -/
theorem Mathlib.add_con.map_apply {M : Type u_1} [add_monoid M] {c : add_con M} {d : add_con M} (h : c ≤ d) (x : add_con.quotient c) : coe_fn (add_con.map c d h) x =
  coe_fn (add_con.lift c (add_con.mk' d) fun (x y : M) (hc : coe_fn c x y) => iff.mpr (add_con.eq d) (h hc)) x :=
  rfl

/-- The first isomorphism theorem for monoids. -/
def Mathlib.add_con.quotient_ker_equiv_range {M : Type u_1} {P : Type u_3} [add_monoid M] [add_monoid P] (f : M →+ P) : add_con.quotient (add_con.ker f) ≃+ ↥(add_monoid_hom.mrange f) :=
  add_equiv.mk
    (equiv.to_fun
      (equiv.of_bijective
        ⇑(add_monoid_hom.comp (add_equiv.to_add_monoid_hom (add_equiv.add_submonoid_congr add_con.ker_lift_range_eq))
            (add_monoid_hom.mrange_restrict (add_con.ker_lift f)))
        sorry))
    (equiv.inv_fun
      (equiv.of_bijective
        ⇑(add_monoid_hom.comp (add_equiv.to_add_monoid_hom (add_equiv.add_submonoid_congr add_con.ker_lift_range_eq))
            (add_monoid_hom.mrange_restrict (add_con.ker_lift f)))
        sorry))
    sorry sorry sorry

/-- The first isomorphism theorem for monoids in the case of a surjective homomorphism. -/
def Mathlib.add_con.quotient_ker_equiv_of_surjective {M : Type u_1} {P : Type u_3} [add_monoid M] [add_monoid P] (f : M →+ P) (hf : function.surjective ⇑f) : add_con.quotient (add_con.ker f) ≃+ P :=
  add_equiv.mk (equiv.to_fun (equiv.of_bijective ⇑(add_con.ker_lift f) sorry))
    (equiv.inv_fun (equiv.of_bijective ⇑(add_con.ker_lift f) sorry)) sorry sorry sorry

/-- The second isomorphism theorem for monoids. -/
def Mathlib.add_con.comap_quotient_equiv {M : Type u_1} {N : Type u_2} [add_monoid M] [add_monoid N] (c : add_con M) (f : N →+ M) : add_con.quotient (add_con.comap (⇑f) (add_monoid_hom.map_add f) c) ≃+
  ↥(add_monoid_hom.mrange (add_monoid_hom.comp (add_con.mk' c) f)) :=
  add_equiv.trans (add_con.congr add_con.comap_eq)
    (add_con.quotient_ker_equiv_range (add_monoid_hom.comp (add_con.mk' c) f))

/-- The third isomorphism theorem for monoids. -/
def quotient_quotient_equiv_quotient {M : Type u_1} [monoid M] (c : con M) (d : con M) (h : c ≤ d) : con.quotient (ker (map c d h)) ≃* con.quotient d :=
  mul_equiv.mk (equiv.to_fun (setoid.quotient_quotient_equiv_quotient (to_setoid c) (to_setoid d) h))
    (equiv.inv_fun (setoid.quotient_quotient_equiv_quotient (to_setoid c) (to_setoid d) h)) sorry sorry sorry

/-- Multiplicative congruence relations preserve inversion. -/
protected theorem Mathlib.add_con.neg {M : Type u_1} [add_group M] (c : add_con M) {w : M} {x : M} : coe_fn c w x → coe_fn c (-w) (-x) := sorry

/-- The inversion induced on the quotient by a congruence relation on a type with a
    inversion. -/
protected instance has_inv {M : Type u_1} [group M] (c : con M) : has_inv (con.quotient c) :=
  has_inv.mk fun (x : con.quotient c) => quotient.lift_on' x (fun (w : M) => ↑(w⁻¹)) sorry

/-- The quotient of a group by a congruence relation is a group. -/
protected instance Mathlib.add_con.add_group {M : Type u_1} [add_group M] (c : add_con M) : add_group (add_con.quotient c) :=
  add_group.mk add_monoid.add sorry add_monoid.zero sorry sorry (fun (x : add_con.quotient c) => -x)
    (sub_neg_monoid.sub._default add_monoid.add sorry add_monoid.zero sorry sorry fun (x : add_con.quotient c) => -x)
    sorry

