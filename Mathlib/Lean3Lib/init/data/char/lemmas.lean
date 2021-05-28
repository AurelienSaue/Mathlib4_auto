import Mathlib.PrePort
import Mathlib.Lean3Lib.init.meta.default
import Mathlib.Lean3Lib.init.logic
import Mathlib.Lean3Lib.init.data.nat.lemmas
import Mathlib.Lean3Lib.init.data.char.basic
 

namespace Mathlib

namespace char


theorem val_of_nat_eq_of_is_valid {n : ℕ} : is_valid_char n → val (of_nat n) = n := sorry

theorem val_of_nat_eq_of_not_is_valid {n : ℕ} : ¬is_valid_char n → val (of_nat n) = 0 := sorry

theorem of_nat_eq_of_not_is_valid {n : ℕ} : ¬is_valid_char n → of_nat n = of_nat 0 :=
  fun (h : ¬is_valid_char n) =>
    eq_of_veq
      (eq.mpr (id (Eq._oldrec (Eq.refl (val (of_nat n) = val (of_nat 0))) (val_of_nat_eq_of_not_is_valid h))) (Eq.refl 0))

theorem of_nat_ne_of_ne {n₁ : ℕ} {n₂ : ℕ} (h₁ : n₁ ≠ n₂) (h₂ : is_valid_char n₁) (h₃ : is_valid_char n₂) : of_nat n₁ ≠ of_nat n₂ :=
  ne_of_vne
    (eq.mpr (id (Eq._oldrec (Eq.refl (val (of_nat n₁) ≠ val (of_nat n₂))) (val_of_nat_eq_of_is_valid h₂)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (n₁ ≠ val (of_nat n₂))) (val_of_nat_eq_of_is_valid h₃))) h₁))

