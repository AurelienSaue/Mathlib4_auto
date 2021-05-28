/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.tactic.omega.clause
import PostPort

universes l 

namespace Mathlib

/-
Correctness lemmas for equality elimination.
See 5.5 of <http://www.decision-procedures.org/> for details.
-/

namespace omega


def symdiv (i : ℤ) (j : ℤ) : ℤ :=
  ite (bit0 1 * (i % j) < j) (i / j) (i / j + 1)

def symmod (i : ℤ) (j : ℤ) : ℤ :=
  ite (bit0 1 * (i % j) < j) (i % j) (i % j - j)

theorem symmod_add_one_self {i : ℤ} : 0 < i → symmod i (i + 1) = -1 := sorry

theorem mul_symdiv_eq {i : ℤ} {j : ℤ} : j * symdiv i j = i - symmod i j := sorry

theorem symmod_eq {i : ℤ} {j : ℤ} : symmod i j = i - j * symdiv i j :=
  eq.mpr (id (Eq._oldrec (Eq.refl (symmod i j = i - j * symdiv i j)) mul_symdiv_eq))
    (eq.mpr (id (Eq._oldrec (Eq.refl (symmod i j = i - (i - symmod i j))) (sub_sub_cancel i (symmod i j))))
      (Eq.refl (symmod i j)))

/-- (sgm v b as n) is the new value assigned to the nth variable
after a single step of equality elimination using valuation v,
term ⟨b, as⟩, and variable index n. If v satisfies the initial
constraint set, then (v ⟨n ↦ sgm v b as n⟩) satisfies the new
constraint set after equality elimination. -/
def sgm (v : ℕ → ℤ) (b : ℤ) (as : List ℤ) (n : ℕ) : ℤ :=
  let a_n : ℤ := list.func.get n as;
  let m : ℤ := a_n + 1;
  (symmod b m + coeffs.val v (list.map (fun (x : ℤ) => symmod x m) as)) / m

def rhs : ℕ → ℤ → List ℤ → term :=
  sorry

theorem rhs_correct_aux {v : ℕ → ℤ} {m : ℤ} {as : List ℤ} {k : ℕ} : ∃ (d : ℤ), m * d + coeffs.val_between v (list.map (fun (x : ℤ) => symmod x m) as) 0 k = coeffs.val_between v as 0 k := sorry

theorem rhs_correct {v : ℕ → ℤ} {b : ℤ} {as : List ℤ} (n : ℕ) : 0 < list.func.get n as → 0 = term.val v (b, as) → v n = term.val (update n (sgm v b as n) v) (rhs n b as) := sorry

def sym_sym (m : ℤ) (b : ℤ) : ℤ :=
  symdiv b m + symmod b m

def coeffs_reduce : ℕ → ℤ → List ℤ → term :=
  sorry

theorem coeffs_reduce_correct {v : ℕ → ℤ} {b : ℤ} {as : List ℤ} {n : ℕ} : 0 < list.func.get n as → 0 = term.val v (b, as) → 0 = term.val (update n (sgm v b as n) v) (coeffs_reduce n b as) := sorry

-- Requires : t1.coeffs[m] = 1

def cancel (m : ℕ) (t1 : term) (t2 : term) : term :=
  term.add (term.mul (-list.func.get m (prod.snd t2)) t1) t2

def subst (n : ℕ) (t1 : term) (t2 : term) : term :=
  term.add (term.mul (list.func.get n (prod.snd t2)) t1) (prod.fst t2, list.func.set 0 (prod.snd t2) n)

theorem subst_correct {v : ℕ → ℤ} {b : ℤ} {as : List ℤ} {t : term} {n : ℕ} : 0 < list.func.get n as →
  0 = term.val v (b, as) → term.val v t = term.val (update n (sgm v b as n) v) (subst n (rhs n b as) t) := sorry

/-- The type of equality elimination rules. -/
inductive ee 
where
| drop : ee
| nondiv : ℤ → ee
| factor : ℤ → ee
| neg : ee
| reduce : ℕ → ee
| cancel : ℕ → ee

namespace ee


def repr : ee → string :=
  sorry

protected instance has_repr : has_repr ee :=
  has_repr.mk repr

end ee


/-- Apply a given sequence of equality elimination steps to a clause. -/
def eq_elim : List ee → clause → clause :=
  sorry

theorem sat_empty : clause.sat ([], []) :=
  Exists.intro (fun (_x : ℕ) => 0) { left := of_as_true trivial, right := of_as_true trivial }

theorem sat_eq_elim {es : List ee} {c : clause} : clause.sat c → clause.sat (eq_elim es c) := sorry

/-- If the result of equality elimination is unsatisfiable, the original clause is unsatisfiable. -/
theorem unsat_of_unsat_eq_elim (ee : List ee) (c : clause) : clause.unsat (eq_elim ee c) → clause.unsat c :=
  fun (h1 : clause.unsat (eq_elim ee c)) => id fun (h2 : clause.sat c) => h1 (sat_eq_elim h2)

