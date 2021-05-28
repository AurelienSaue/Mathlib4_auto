/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

Godel numbering for partial recursive functions.
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.computability.partrec
import PostPort

universes l u_1 u_2 

namespace Mathlib

namespace nat.partrec


theorem rfind' {f : ℕ →. ℕ} (hf : partrec f) : partrec
  (unpaired
    fun (a m : ℕ) =>
      roption.map (fun (_x : ℕ) => _x + m)
        (rfind fun (n : ℕ) => (fun (m : ℕ) => to_bool (m = 0)) <$> f (mkpair a (n + m)))) := sorry

inductive code 
where
| zero : code
| succ : code
| left : code
| right : code
| pair : code → code → code
| comp : code → code → code
| prec : code → code → code
| rfind' : code → code

end nat.partrec


namespace nat.partrec.code


protected instance inhabited : Inhabited code :=
  { default := zero }

protected def const : ℕ → code :=
  sorry

theorem const_inj {n₁ : ℕ} {n₂ : ℕ} : code.const n₁ = code.const n₂ → n₁ = n₂ := sorry

protected def id : code :=
  pair left right

def curry (c : code) (n : ℕ) : code :=
  comp c (pair (code.const n) code.id)

def encode_code : code → ℕ :=
  sorry

def of_nat_code : ℕ → code :=
  sorry

protected instance denumerable : denumerable code :=
  denumerable.mk' (equiv.mk encode_code of_nat_code sorry encode_of_nat_code)

theorem encode_code_eq : encodable.encode = encode_code :=
  rfl

theorem of_nat_code_eq : denumerable.of_nat code = of_nat_code :=
  rfl

theorem encode_lt_pair (cf : code) (cg : code) : encodable.encode cf < encodable.encode (pair cf cg) ∧ encodable.encode cg < encodable.encode (pair cf cg) := sorry

theorem encode_lt_comp (cf : code) (cg : code) : encodable.encode cf < encodable.encode (comp cf cg) ∧ encodable.encode cg < encodable.encode (comp cf cg) := sorry

theorem encode_lt_prec (cf : code) (cg : code) : encodable.encode cf < encodable.encode (prec cf cg) ∧ encodable.encode cg < encodable.encode (prec cf cg) := sorry

theorem encode_lt_rfind' (cf : code) : encodable.encode cf < encodable.encode (rfind' cf) := sorry

theorem pair_prim : primrec₂ pair := sorry

theorem comp_prim : primrec₂ comp := sorry

theorem prec_prim : primrec₂ prec := sorry

theorem rfind_prim : primrec rfind' := sorry

theorem rec_prim' {α : Type u_1} {σ : Type u_2} [primcodable α] [primcodable σ] {c : α → code} (hc : primrec c) {z : α → σ} (hz : primrec z) {s : α → σ} (hs : primrec s) {l : α → σ} (hl : primrec l) {r : α → σ} (hr : primrec r) {pr : α → code × code × σ × σ → σ} (hpr : primrec₂ pr) {co : α → code × code × σ × σ → σ} (hco : primrec₂ co) {pc : α → code × code × σ × σ → σ} (hpc : primrec₂ pc) {rf : α → code × σ → σ} (hrf : primrec₂ rf) : let PR : α → code → code → σ → σ → σ := fun (a : α) (cf cg : code) (hf hg : σ) => pr a (cf, cg, hf, hg);
let CO : α → code → code → σ → σ → σ := fun (a : α) (cf cg : code) (hf hg : σ) => co a (cf, cg, hf, hg);
let PC : α → code → code → σ → σ → σ := fun (a : α) (cf cg : code) (hf hg : σ) => pc a (cf, cg, hf, hg);
let RF : α → code → σ → σ := fun (a : α) (cf : code) (hf : σ) => rf a (cf, hf);
let F : α → code → σ := fun (a : α) (c : code) => code.rec_on c (z a) (s a) (l a) (r a) (PR a) (CO a) (PC a) (RF a);
primrec fun (a : α) => F a (c a) := sorry

theorem rec_prim {α : Type u_1} {σ : Type u_2} [primcodable α] [primcodable σ] {c : α → code} (hc : primrec c) {z : α → σ} (hz : primrec z) {s : α → σ} (hs : primrec s) {l : α → σ} (hl : primrec l) {r : α → σ} (hr : primrec r) {pr : α → code → code → σ → σ → σ} (hpr : primrec
  fun (a : α × code × code × σ × σ) =>
    pr (prod.fst a) (prod.fst (prod.snd a)) (prod.fst (prod.snd (prod.snd a)))
      (prod.fst (prod.snd (prod.snd (prod.snd a)))) (prod.snd (prod.snd (prod.snd (prod.snd a))))) {co : α → code → code → σ → σ → σ} (hco : primrec
  fun (a : α × code × code × σ × σ) =>
    co (prod.fst a) (prod.fst (prod.snd a)) (prod.fst (prod.snd (prod.snd a)))
      (prod.fst (prod.snd (prod.snd (prod.snd a)))) (prod.snd (prod.snd (prod.snd (prod.snd a))))) {pc : α → code → code → σ → σ → σ} (hpc : primrec
  fun (a : α × code × code × σ × σ) =>
    pc (prod.fst a) (prod.fst (prod.snd a)) (prod.fst (prod.snd (prod.snd a)))
      (prod.fst (prod.snd (prod.snd (prod.snd a)))) (prod.snd (prod.snd (prod.snd (prod.snd a))))) {rf : α → code → σ → σ} (hrf : primrec fun (a : α × code × σ) => rf (prod.fst a) (prod.fst (prod.snd a)) (prod.snd (prod.snd a))) : let F : α → code → σ := fun (a : α) (c : code) => code.rec_on c (z a) (s a) (l a) (r a) (pr a) (co a) (pc a) (rf a);
primrec fun (a : α) => F a (c a) := sorry

/- TODO(Mario): less copy-paste from previous proof -/

theorem rec_computable {α : Type u_1} {σ : Type u_2} [primcodable α] [primcodable σ] {c : α → code} (hc : computable c) {z : α → σ} (hz : computable z) {s : α → σ} (hs : computable s) {l : α → σ} (hl : computable l) {r : α → σ} (hr : computable r) {pr : α → code × code × σ × σ → σ} (hpr : computable₂ pr) {co : α → code × code × σ × σ → σ} (hco : computable₂ co) {pc : α → code × code × σ × σ → σ} (hpc : computable₂ pc) {rf : α → code × σ → σ} (hrf : computable₂ rf) : let PR : α → code → code → σ → σ → σ := fun (a : α) (cf cg : code) (hf hg : σ) => pr a (cf, cg, hf, hg);
let CO : α → code → code → σ → σ → σ := fun (a : α) (cf cg : code) (hf hg : σ) => co a (cf, cg, hf, hg);
let PC : α → code → code → σ → σ → σ := fun (a : α) (cf cg : code) (hf hg : σ) => pc a (cf, cg, hf, hg);
let RF : α → code → σ → σ := fun (a : α) (cf : code) (hf : σ) => rf a (cf, hf);
let F : α → code → σ := fun (a : α) (c : code) => code.rec_on c (z a) (s a) (l a) (r a) (PR a) (CO a) (PC a) (RF a);
computable fun (a : α) => F a (c a) := sorry

def eval : code → ℕ →. ℕ :=
  sorry

protected instance has_mem : has_mem (ℕ →. ℕ) code :=
  has_mem.mk fun (f : ℕ →. ℕ) (c : code) => eval c = f

@[simp] theorem eval_const (n : ℕ) (m : ℕ) : eval (code.const n) m = roption.some n := sorry

@[simp] theorem eval_id (n : ℕ) : eval code.id n = roption.some n := sorry

@[simp] theorem eval_curry (c : code) (n : ℕ) (x : ℕ) : eval (curry c n) x = eval c (mkpair n x) := sorry

theorem const_prim : primrec code.const := sorry

theorem curry_prim : primrec₂ curry :=
  primrec₂.comp comp_prim primrec.fst
    (primrec₂.comp pair_prim (primrec.comp const_prim primrec.snd) (primrec.const code.id))

theorem curry_inj {c₁ : code} {c₂ : code} {n₁ : ℕ} {n₂ : ℕ} (h : curry c₁ n₁ = curry c₂ n₂) : c₁ = c₂ ∧ n₁ = n₂ := sorry

theorem smn : ∃ (f : code → ℕ → code), computable₂ f ∧ ∀ (c : code) (n x : ℕ), eval (f c n) x = eval c (mkpair n x) :=
  Exists.intro curry { left := primrec₂.to_comp curry_prim, right := eval_curry }

theorem exists_code {f : ℕ →. ℕ} : partrec f ↔ ∃ (c : code), eval c = f := sorry

def evaln (k : ℕ) : code → ℕ → Option ℕ :=
  sorry

theorem evaln_bound {k : ℕ} {c : code} {n : ℕ} {x : ℕ} : x ∈ evaln k c n → n < k := sorry

theorem evaln_mono {k₁ : ℕ} {k₂ : ℕ} {c : code} {n : ℕ} {x : ℕ} : k₁ ≤ k₂ → x ∈ evaln k₁ c n → x ∈ evaln k₂ c n := sorry

theorem evaln_sound {k : ℕ} {c : code} {n : ℕ} {x : ℕ} : x ∈ evaln k c n → x ∈ eval c n := sorry

theorem evaln_complete {c : code} {n : ℕ} {x : ℕ} : x ∈ eval c n ↔ ∃ (k : ℕ), x ∈ evaln k c n := sorry

theorem evaln_prim : primrec fun (a : (ℕ × code) × ℕ) => evaln (prod.fst (prod.fst a)) (prod.snd (prod.fst a)) (prod.snd a) := sorry

theorem eval_eq_rfind_opt (c : code) (n : ℕ) : eval c n = rfind_opt fun (k : ℕ) => evaln k c n :=
  roption.ext
    fun (x : ℕ) => iff.trans evaln_complete (iff.symm (rfind_opt_mono fun (a m n_1 : ℕ) (hl : m ≤ n_1) => evaln_mono hl))

theorem eval_part : partrec₂ eval := sorry

theorem fixed_point {f : code → code} (hf : computable f) : ∃ (c : code), eval (f c) = eval c := sorry

theorem fixed_point₂ {f : code → ℕ →. ℕ} (hf : partrec₂ f) : ∃ (c : code), eval c = f c := sorry

