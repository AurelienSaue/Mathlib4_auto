/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.pfunctor.univariate.default
import Mathlib.PostPort

universes u l u_1 

namespace Mathlib

/-!

# Quotients of Polynomial Functors

We assume the following:

`P`   : a polynomial functor
`W`   : its W-type
`M`   : its M-type
`F`   : a functor

We define:

`q`   : `qpf` data, representing `F` as a quotient of `P`

The main goal is to construct:

`fix`   : the initial algebra with structure map `F fix → fix`.
`cofix` : the final coalgebra with structure map `cofix → F cofix`

We also show that the composition of qpfs is a qpf, and that the quotient of a qpf
is a qpf.

The present theory focuses on the univariate case for qpfs

## References

* [Jeremy Avigad, Mario M. Carneiro and Simon Hudon, *Data Types as Quotients of Polynomial Functors*][avigad-carneiro-hudon2019]

-/

/--
Quotients of polynomial functors.

Roughly speaking, saying that `F` is a quotient of a polynomial functor means that for each `α`,
elements of `F α` are represented by pairs `⟨a, f⟩`, where `a` is the shape of the object and
`f` indexes the relevant elements of `α`, in a suitably natural manner.
-/
class qpf (F : Type u → Type u) [Functor F] 
where
  P : pfunctor
  abs : {α : Type u} → pfunctor.obj P α → F α
  repr : {α : Type u} → F α → pfunctor.obj P α
  abs_repr : ∀ {α : Type u} (x : F α), abs (repr x) = x
  abs_map : ∀ {α β : Type u} (f : α → β) (p : pfunctor.obj P α), abs (f <$> p) = f <$> abs p

namespace qpf


/-
Show that every qpf is a lawful functor.

Note: every functor has a field, `map_const`, and is_lawful_functor has the defining
characterization. We can only propagate the assumption.
-/

theorem id_map {F : Type u → Type u} [Functor F] [q : qpf F] {α : Type u} (x : F α) : id <$> x = x := sorry

theorem comp_map {F : Type u → Type u} [Functor F] [q : qpf F] {α : Type u} {β : Type u} {γ : Type u} (f : α → β) (g : β → γ) (x : F α) : (g ∘ f) <$> x = g <$> f <$> x := sorry

theorem is_lawful_functor {F : Type u → Type u} [Functor F] [q : qpf F] (h : ∀ (α β : Type u), Functor.mapConst = Functor.map ∘ function.const β) : is_lawful_functor F :=
  is_lawful_functor.mk id_map comp_map

/-
Lifting predicates and relations
-/

theorem liftp_iff {F : Type u → Type u} [Functor F] [q : qpf F] {α : Type u} (p : α → Prop) (x : F α) : functor.liftp p x ↔
  ∃ (a : pfunctor.A (P F)), ∃ (f : pfunctor.B (P F) a → α), x = abs (sigma.mk a f) ∧ ∀ (i : pfunctor.B (P F) a), p (f i) := sorry

theorem liftp_iff' {F : Type u → Type u} [Functor F] [q : qpf F] {α : Type u} (p : α → Prop) (x : F α) : functor.liftp p x ↔ ∃ (u : pfunctor.obj (P F) α), abs u = x ∧ ∀ (i : pfunctor.B (P F) (sigma.fst u)), p (sigma.snd u i) := sorry

theorem liftr_iff {F : Type u → Type u} [Functor F] [q : qpf F] {α : Type u} (r : α → α → Prop) (x : F α) (y : F α) : functor.liftr r x y ↔
  ∃ (a : pfunctor.A (P F)),
    ∃ (f₀ : pfunctor.B (P F) a → α),
      ∃ (f₁ : pfunctor.B (P F) a → α),
        x = abs (sigma.mk a f₀) ∧ y = abs (sigma.mk a f₁) ∧ ∀ (i : pfunctor.B (P F) a), r (f₀ i) (f₁ i) := sorry

/-
Think of trees in the `W` type corresponding to `P` as representatives of elements of the
least fixed point of `F`, and assign a canonical representative to each equivalence class
of trees.
-/

/-- does recursion on `q.P.W` using `g : F α → α` rather than `g : P α → α` -/
def recF {F : Type u → Type u} [Functor F] [q : qpf F] {α : Type u} (g : F α → α) : pfunctor.W (P F) → α :=
  sorry

theorem recF_eq {F : Type u → Type u} [Functor F] [q : qpf F] {α : Type u} (g : F α → α) (x : pfunctor.W (P F)) : recF g x = g (abs (recF g <$> pfunctor.W.dest x)) :=
  W_type.cases_on x
    fun (x_a : pfunctor.A (P F)) (x_f : pfunctor.B (P F) x_a → W_type (pfunctor.B (P F))) =>
      Eq.refl (recF g (W_type.mk x_a x_f))

theorem recF_eq' {F : Type u → Type u} [Functor F] [q : qpf F] {α : Type u} (g : F α → α) (a : pfunctor.A (P F)) (f : pfunctor.B (P F) a → pfunctor.W (P F)) : recF g (W_type.mk a f) = g (abs (recF g <$> sigma.mk a f)) :=
  rfl

/-- two trees are equivalent if their F-abstractions are -/
inductive Wequiv {F : Type u → Type u} [Functor F] [q : qpf F] : pfunctor.W (P F) → pfunctor.W (P F) → Prop
where
| ind : ∀ (a : pfunctor.A (P F)) (f f' : pfunctor.B (P F) a → pfunctor.W (P F)),
  (∀ (x : pfunctor.B (P F) a), Wequiv (f x) (f' x)) → Wequiv (W_type.mk a f) (W_type.mk a f')
| abs : ∀ (a : pfunctor.A (P F)) (f : pfunctor.B (P F) a → pfunctor.W (P F)) (a' : pfunctor.A (P F))
  (f' : pfunctor.B (P F) a' → pfunctor.W (P F)),
  abs (sigma.mk a f) = abs (sigma.mk a' f') → Wequiv (W_type.mk a f) (W_type.mk a' f')
| trans : ∀ (u v w : pfunctor.W (P F)), Wequiv u v → Wequiv v w → Wequiv u w

/-- recF is insensitive to the representation -/
theorem recF_eq_of_Wequiv {F : Type u → Type u} [Functor F] [q : qpf F] {α : Type u} (u : F α → α) (x : pfunctor.W (P F)) (y : pfunctor.W (P F)) : Wequiv x y → recF u x = recF u y := sorry

theorem Wequiv.abs' {F : Type u → Type u} [Functor F] [q : qpf F] (x : pfunctor.W (P F)) (y : pfunctor.W (P F)) (h : abs (pfunctor.W.dest x) = abs (pfunctor.W.dest y)) : Wequiv x y := sorry

theorem Wequiv.refl {F : Type u → Type u} [Functor F] [q : qpf F] (x : pfunctor.W (P F)) : Wequiv x x :=
  W_type.cases_on x
    fun (a : pfunctor.A (P F)) (f : pfunctor.B (P F) a → W_type (pfunctor.B (P F))) => Wequiv.abs a f a f rfl

theorem Wequiv.symm {F : Type u → Type u} [Functor F] [q : qpf F] (x : pfunctor.W (P F)) (y : pfunctor.W (P F)) : Wequiv x y → Wequiv y x := sorry

/-- maps every element of the W type to a canonical representative -/
def Wrepr {F : Type u → Type u} [Functor F] [q : qpf F] : pfunctor.W (P F) → pfunctor.W (P F) :=
  recF (pfunctor.W.mk ∘ repr)

theorem Wrepr_equiv {F : Type u → Type u} [Functor F] [q : qpf F] (x : pfunctor.W (P F)) : Wequiv (Wrepr x) x := sorry

/--
Define the fixed point as the quotient of trees under the equivalence relation `Wequiv`.
-/
def W_setoid {F : Type u → Type u} [Functor F] [q : qpf F] : setoid (pfunctor.W (P F)) :=
  setoid.mk Wequiv sorry

/-- inductive type defined as initial algebra of a Quotient of Polynomial Functor -/
def fix (F : Type u → Type u) [Functor F] [q : qpf F]  :=
  quotient W_setoid

/-- recursor of a type defined by a qpf -/
def fix.rec {F : Type u → Type u} [Functor F] [q : qpf F] {α : Type u} (g : F α → α) : fix F → α :=
  Quot.lift (recF g) (recF_eq_of_Wequiv g)

/-- access the underlying W-type of a fixpoint data type -/
def fix_to_W {F : Type u → Type u} [Functor F] [q : qpf F] : fix F → pfunctor.W (P F) :=
  quotient.lift Wrepr sorry

/-- constructor of a type defined by a qpf -/
def fix.mk {F : Type u → Type u} [Functor F] [q : qpf F] (x : F (fix F)) : fix F :=
  Quot.mk setoid.r (pfunctor.W.mk (fix_to_W <$> repr x))

/-- destructor of a type defined by a qpf -/
def fix.dest {F : Type u → Type u} [Functor F] [q : qpf F] : fix F → F (fix F) :=
  fix.rec (Functor.map fix.mk)

theorem fix.rec_eq {F : Type u → Type u} [Functor F] [q : qpf F] {α : Type u} (g : F α → α) (x : F (fix F)) : fix.rec g (fix.mk x) = g (fix.rec g <$> x) := sorry

theorem fix.ind_aux {F : Type u → Type u} [Functor F] [q : qpf F] (a : pfunctor.A (P F)) (f : pfunctor.B (P F) a → pfunctor.W (P F)) : fix.mk (abs (sigma.mk a fun (x : pfunctor.B (P F) a) => quotient.mk (f x))) = quotient.mk (W_type.mk a f) := sorry

theorem fix.ind_rec {F : Type u → Type u} [Functor F] [q : qpf F] {α : Type u} (g₁ : fix F → α) (g₂ : fix F → α) (h : ∀ (x : F (fix F)), g₁ <$> x = g₂ <$> x → g₁ (fix.mk x) = g₂ (fix.mk x)) (x : fix F) : g₁ x = g₂ x := sorry

theorem fix.rec_unique {F : Type u → Type u} [Functor F] [q : qpf F] {α : Type u} (g : F α → α) (h : fix F → α) (hyp : ∀ (x : F (fix F)), h (fix.mk x) = g (h <$> x)) : fix.rec g = h := sorry

theorem fix.mk_dest {F : Type u → Type u} [Functor F] [q : qpf F] (x : fix F) : fix.mk (fix.dest x) = x := sorry

theorem fix.dest_mk {F : Type u → Type u} [Functor F] [q : qpf F] (x : F (fix F)) : fix.dest (fix.mk x) = x := sorry

theorem fix.ind {F : Type u → Type u} [Functor F] [q : qpf F] (p : fix F → Prop) (h : ∀ (x : F (fix F)), functor.liftp p x → p (fix.mk x)) (x : fix F) : p x := sorry

end qpf


/-
Construct the final coalgebra to a qpf.
-/

namespace qpf


/-- does recursion on `q.P.M` using `g : α → F α` rather than `g : α → P α` -/
def corecF {F : Type u → Type u} [Functor F] [q : qpf F] {α : Type u} (g : α → F α) : α → pfunctor.M (P F) :=
  pfunctor.M.corec fun (x : α) => repr (g x)

theorem corecF_eq {F : Type u → Type u} [Functor F] [q : qpf F] {α : Type u} (g : α → F α) (x : α) : pfunctor.M.dest (corecF g x) = corecF g <$> repr (g x) := sorry

/- Equivalence -/

/-- A pre-congruence on q.P.M *viewed as an F-coalgebra*. Not necessarily symmetric. -/
def is_precongr {F : Type u → Type u} [Functor F] [q : qpf F] (r : pfunctor.M (P F) → pfunctor.M (P F) → Prop)  :=
  ∀ {x y : pfunctor.M (P F)}, r x y → abs (Quot.mk r <$> pfunctor.M.dest x) = abs (Quot.mk r <$> pfunctor.M.dest y)

/-- The maximal congruence on q.P.M -/
def Mcongr {F : Type u → Type u} [Functor F] [q : qpf F] : pfunctor.M (P F) → pfunctor.M (P F) → Prop :=
  fun (x y : pfunctor.M (P F)) => ∃ (r : pfunctor.M (P F) → pfunctor.M (P F) → Prop), is_precongr r ∧ r x y

/-- coinductive type defined as the final coalgebra of a qpf -/
def cofix (F : Type u → Type u) [Functor F] [q : qpf F]  :=
  Quot Mcongr

protected instance cofix.inhabited {F : Type u → Type u} [Functor F] [q : qpf F] [Inhabited (pfunctor.A (P F))] : Inhabited (cofix F) :=
  { default := Quot.mk Mcongr Inhabited.default }

/-- corecursor for type defined by `cofix` -/
def cofix.corec {F : Type u → Type u} [Functor F] [q : qpf F] {α : Type u} (g : α → F α) (x : α) : cofix F :=
  Quot.mk Mcongr (corecF g x)

/-- destructor for type defined by `cofix` -/
def cofix.dest {F : Type u → Type u} [Functor F] [q : qpf F] : cofix F → F (cofix F) :=
  Quot.lift (fun (x : pfunctor.M (P F)) => Quot.mk Mcongr <$> abs (pfunctor.M.dest x)) sorry

theorem cofix.dest_corec {F : Type u → Type u} [Functor F] [q : qpf F] {α : Type u} (g : α → F α) (x : α) : cofix.dest (cofix.corec g x) = cofix.corec g <$> g x := sorry

theorem cofix.bisim_rel {F : Type u → Type u} [Functor F] [q : qpf F] (r : cofix F → cofix F → Prop) (h : ∀ (x y : cofix F), r x y → Quot.mk r <$> cofix.dest x = Quot.mk r <$> cofix.dest y) (x : cofix F) (y : cofix F) : r x y → x = y := sorry

theorem cofix.bisim {F : Type u → Type u} [Functor F] [q : qpf F] (r : cofix F → cofix F → Prop) (h : ∀ (x y : cofix F), r x y → functor.liftr r (cofix.dest x) (cofix.dest y)) (x : cofix F) (y : cofix F) : r x y → x = y := sorry

theorem cofix.bisim' {F : Type u → Type u} [Functor F] [q : qpf F] {α : Type u_1} (Q : α → Prop) (u : α → cofix F) (v : α → cofix F) (h : ∀ (x : α),
  Q x →
    ∃ (a : pfunctor.A (P F)),
      ∃ (f : pfunctor.B (P F) a → cofix F),
        ∃ (f' : pfunctor.B (P F) a → cofix F),
          cofix.dest (u x) = abs (sigma.mk a f) ∧
            cofix.dest (v x) = abs (sigma.mk a f') ∧
              ∀ (i : pfunctor.B (P F) a), ∃ (x' : α), Q x' ∧ f i = u x' ∧ f' i = v x') (x : α) : Q x → u x = v x := sorry

end qpf


/-
Composition of qpfs.
-/

namespace qpf


/-- composition of qpfs gives another qpf  -/
def comp {F₂ : Type u → Type u} [Functor F₂] [q₂ : qpf F₂] {F₁ : Type u → Type u} [Functor F₁] [q₁ : qpf F₁] : qpf (functor.comp F₂ F₁) :=
  mk (pfunctor.comp (P F₂) (P F₁))
    (fun (α : Type u) =>
      id
        fun (p : pfunctor.obj (pfunctor.comp (P F₂) (P F₁)) α) =>
          abs
            (sigma.mk (sigma.fst (sigma.fst p))
              fun (x : pfunctor.B (P F₂) (sigma.fst (sigma.fst p))) =>
                abs
                  (sigma.mk (sigma.snd (sigma.fst p) x)
                    fun (y : pfunctor.B (P F₁) (sigma.snd (sigma.fst p) x)) => sigma.snd p (sigma.mk x y))))
    (fun (α : Type u) =>
      id
        fun (y : F₂ (F₁ α)) =>
          sigma.mk
            (sigma.mk (sigma.fst (repr y))
              fun (u : pfunctor.B (P F₂) (sigma.fst (repr y))) => sigma.fst (repr (sigma.snd (repr y) u)))
            (id
              fun
                (x :
                sigma
                  fun (u : pfunctor.B (P F₂) (sigma.fst (repr y))) =>
                    pfunctor.B (P F₁) (sigma.fst (repr (sigma.snd (repr y) u)))) =>
                sigma.snd (repr (sigma.snd (repr y) (sigma.fst x))) (sigma.snd x)))
    sorry sorry

end qpf


/-
Quotients.

We show that if `F` is a qpf and `G` is a suitable quotient of `F`, then `G` is a qpf.
-/

namespace qpf


/-- Given a qpf `F` and a well-behaved surjection `FG_abs` from F α to
functor G α, `G` is a qpf. We can consider `G` a quotient on `F` where
elements `x y : F α` are in the same equivalence class if
`FG_abs x = FG_abs y`  -/
def quotient_qpf {F : Type u → Type u} [Functor F] [q : qpf F] {G : Type u → Type u} [Functor G] {FG_abs : {α : Type u} → F α → G α} {FG_repr : {α : Type u} → G α → F α} (FG_abs_repr : ∀ {α : Type u} (x : G α), FG_abs (FG_repr x) = x) (FG_abs_map : ∀ {α β : Type u} (f : α → β) (x : F α), FG_abs (f <$> x) = f <$> FG_abs x) : qpf G :=
  mk (P F) (fun {α : Type u} (p : pfunctor.obj (P F) α) => FG_abs (abs p))
    (fun {α : Type u} (x : G α) => repr (FG_repr x)) sorry sorry

end qpf


/-
Support.
-/

namespace qpf


theorem mem_supp {F : Type u → Type u} [Functor F] [q : qpf F] {α : Type u} (x : F α) (u : α) : u ∈ functor.supp x ↔ ∀ (a : pfunctor.A (P F)) (f : pfunctor.B (P F) a → α), abs (sigma.mk a f) = x → u ∈ f '' set.univ := sorry

theorem supp_eq {F : Type u → Type u} [Functor F] [q : qpf F] {α : Type u} (x : F α) : functor.supp x =
  set_of
    fun (u : α) => ∀ (a : pfunctor.A (P F)) (f : pfunctor.B (P F) a → α), abs (sigma.mk a f) = x → u ∈ f '' set.univ :=
  set.ext fun (x_1 : α) => mem_supp x x_1

theorem has_good_supp_iff {F : Type u → Type u} [Functor F] [q : qpf F] {α : Type u} (x : F α) : (∀ (p : α → Prop), functor.liftp p x ↔ ∀ (u : α), u ∈ functor.supp x → p u) ↔
  ∃ (a : pfunctor.A (P F)),
    ∃ (f : pfunctor.B (P F) a → α),
      abs (sigma.mk a f) = x ∧
        ∀ (a' : pfunctor.A (P F)) (f' : pfunctor.B (P F) a' → α),
          abs (sigma.mk a' f') = x → f '' set.univ ⊆ f' '' set.univ := sorry

/-- A qpf is said to be uniform if every polynomial functor
representing a single value all have the same range. -/
def is_uniform {F : Type u → Type u} [Functor F] (q : qpf F)  :=
  ∀ {α : Type u} (a a' : pfunctor.A (P F)) (f : pfunctor.B (P F) a → α) (f' : pfunctor.B (P F) a' → α),
    abs (sigma.mk a f) = abs (sigma.mk a' f') → f '' set.univ = f' '' set.univ

/-- does `abs` preserve `liftp`? -/
def liftp_preservation {F : Type u → Type u} [Functor F] (q : qpf F)  :=
  ∀ {α : Type u} (p : α → Prop) (x : pfunctor.obj (P F) α), functor.liftp p (abs x) ↔ functor.liftp p x

/-- does `abs` preserve `supp`? -/
def supp_preservation {F : Type u → Type u} [Functor F] (q : qpf F)  :=
  ∀ {α : Type u} (x : pfunctor.obj (P F) α), functor.supp (abs x) = functor.supp x

theorem supp_eq_of_is_uniform {F : Type u → Type u} [Functor F] [q : qpf F] (h : is_uniform q) {α : Type u} (a : pfunctor.A (P F)) (f : pfunctor.B (P F) a → α) : functor.supp (abs (sigma.mk a f)) = f '' set.univ := sorry

theorem liftp_iff_of_is_uniform {F : Type u → Type u} [Functor F] [q : qpf F] (h : is_uniform q) {α : Type u} (x : F α) (p : α → Prop) : functor.liftp p x ↔ ∀ (u : α), u ∈ functor.supp x → p u := sorry

theorem supp_map {F : Type u → Type u} [Functor F] [q : qpf F] (h : is_uniform q) {α : Type u} {β : Type u} (g : α → β) (x : F α) : functor.supp (g <$> x) = g '' functor.supp x := sorry

theorem supp_preservation_iff_uniform {F : Type u → Type u} [Functor F] [q : qpf F] : supp_preservation q ↔ is_uniform q := sorry

theorem supp_preservation_iff_liftp_preservation {F : Type u → Type u} [Functor F] [q : qpf F] : supp_preservation q ↔ liftp_preservation q := sorry

theorem liftp_preservation_iff_uniform {F : Type u → Type u} [Functor F] [q : qpf F] : liftp_preservation q ↔ is_uniform q := sorry

