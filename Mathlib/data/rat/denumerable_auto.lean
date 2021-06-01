/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Chris Hughes
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.rat.default
import Mathlib.set_theory.cardinal
import Mathlib.PostPort

namespace Mathlib

namespace rat


protected instance infinite : infinite ℚ := infinite.of_injective coe nat.cast_injective

protected instance denumerable : denumerable ℚ :=
  let T : Type :=
    Subtype fun (x : ℤ × ℕ) => 0 < prod.snd x ∧ nat.coprime (int.nat_abs (prod.fst x)) (prod.snd x);
  let _inst : infinite T := sorry;
  let _inst_1 : encodable T := encodable.subtype;
  let _inst_2 : denumerable T := denumerable.of_encodable_of_infinite T;
  denumerable.of_equiv T denumerable_aux

end rat


namespace cardinal


theorem mk_rat : mk ℚ = omega := iff.mp denumerable_iff (Nonempty.intro rat.denumerable)

end Mathlib