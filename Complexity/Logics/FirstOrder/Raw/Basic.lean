/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Logic.Equiv.List
public import Mathlib.Basic.Finite.Defs

/-!
# Raw first-order formulas with a primitive recursive coding

`Cslib.Logic.FO.RawFormula` is a flat syntax of relational first-order formulas: variables are
natural numbers, relation symbols are natural numbers, and an atom `rel r args` applies symbol `r`
to the variable list `args` (its arity is the length of `args`). The primitives are `falsum`,
equality of variables `equal x y`, atoms `rel r args`, `imp` and `all`; the other connectives are
derived (`neg`, `verum`, `disj`, `conj`, `ex`, `iff`, `bigConj`).

**Why a separate syntax.** Mathlib's `FirstOrder.Language.BoundedFormula` is a dependent family
over a language whose symbol types are arbitrary, and Mathlib has no `Primcodable` instance for it
(listed as a TODO in `Mathlib/ModelTheory/Encoding.lean`). Decidability statements in Mathlib's
plain computability vocabulary (`ComputablePred`, `REPred`) need such an instance. `RawFormula`
is `Denumerable` through `Nat.pair`, so its `Primcodable` instance is immediate and its
constructors and structural recursion are primitive recursive
(`Complexity/Logics/FirstOrder/Raw/Primrec.lean`). A computable translation to Mathlib's
`L.Sentence` for a relational language with symbols indexed by `ℕ` is left as future work.

A formula is interpreted in any type `M` by a relation interpretation `I : ℕ → List M → Prop`
(the meaning of `rel r args` under an assignment `v` is `I r (args.map v)`) and an assignment
`v : ℕ → M`.

The name `RawFormula` is also used by the FO(LFP) syntax `Cslib.Logic.FO.LFP.RawFormula`
(`Complexity/Logics/FirstOrder/Operator/LeastFixedPoint.lean`); under
`open Cslib.Logic.FO Cslib.Logic.FO.LFP` qualify the name.

## Main definitions

* `Cslib.Logic.FO.RawFormula`: raw relational first-order formulas.
* `Cslib.Logic.FO.RawFormula.toNat`, `Cslib.Logic.FO.RawFormula.ofNat`: the coding, giving the
  `Denumerable` instance.
* `Cslib.Logic.FO.RawFormula.Realize`: satisfaction.
* `Cslib.Logic.FO.RawFormula.rename`: renaming of relation symbols.
* `Cslib.Logic.FO.RawFormula.FinSat`, `Cslib.Logic.FO.RawFormula.FinValid`: finite
  satisfiability and finite validity (truth in every finite nonempty structure).

## Main results

* `Cslib.Logic.FO.RawFormula.realize_congr_var`, `Cslib.Logic.FO.RawFormula.realize_congr_rel`:
  satisfaction depends only on the variables below `varBound` and the symbols in `atoms`.
* `Cslib.Logic.FO.RawFormula.realize_equiv`: satisfaction is invariant under bijections.
* `Cslib.Logic.FO.RawFormula.finValid_neg_iff`: `¬φ` is finitely valid iff `φ` is not finitely
  satisfiable.
-/

-- The section is exposed because other modules unfold these definitions definitionally: for
-- example `primrec_neg` (`Raw/Primrec.lean`) uses `neg φ = imp φ falsum`, the primitive
-- recursiveness proofs unfold the coding, and clients destructure `FinSat` directly.
@[expose] public section

namespace Cslib.Logic.FO

/-- Relational first-order formulas with variables and relation symbols named by natural numbers.
The arity of `rel r args` is the length of `args`. -/
inductive RawFormula : Type
  /-- Falsity. -/
  | falsum : RawFormula
  /-- Equality of two variables. -/
  | equal (x y : ℕ) : RawFormula
  /-- Relation symbol `r` applied to a list of variables. -/
  | rel (r : ℕ) (args : List ℕ) : RawFormula
  /-- Implication. -/
  | imp (φ ψ : RawFormula) : RawFormula
  /-- Universal quantification of variable `x`. -/
  | all (x : ℕ) (φ : RawFormula) : RawFormula
  deriving DecidableEq

namespace RawFormula

/-! ### Coding -/

/-- The code of a formula: `falsum` is `0`, and a formula built by `equal`, `rel`, `imp` or `all`
(index `i = 1, 2, 3, 4`) from arguments paired into `p` has code `4 * p + i`. -/
def toNat : RawFormula → ℕ
  | falsum => 0
  | equal x y => 4 * Nat.pair x y + 1
  | rel r args => 4 * Nat.pair r (Encodable.encode args) + 2
  | imp φ ψ => 4 * Nat.pair φ.toNat ψ.toNat + 3
  | all x φ => 4 * Nat.pair x φ.toNat + 4

/-- Decoding recurses on the first component of the payload, which is smaller. -/
theorem unpair_fst_div_four_lt (m : ℕ) : (m / 4).unpair.1 < m + 1 :=
  Nat.lt_succ_of_le ((Nat.unpair_left_le _).trans (Nat.div_le_self _ _))

/-- Decoding recurses on the second component of the payload, which is smaller. -/
theorem unpair_snd_div_four_lt (m : ℕ) : (m / 4).unpair.2 < m + 1 :=
  Nat.lt_succ_of_le ((Nat.unpair_right_le _).trans (Nat.div_le_self _ _))

/-- The formula with a given code. -/
def ofNat : ℕ → RawFormula
  | 0 => falsum
  | m + 1 =>
    have := unpair_fst_div_four_lt m
    have := unpair_snd_div_four_lt m
    if m % 4 = 0 then equal (m / 4).unpair.1 (m / 4).unpair.2
    else if m % 4 = 1 then rel (m / 4).unpair.1 (Denumerable.ofNat (List ℕ) (m / 4).unpair.2)
    else if m % 4 = 2 then imp (ofNat (m / 4).unpair.1) (ofNat (m / 4).unpair.2)
    else all (m / 4).unpair.1 (ofNat (m / 4).unpair.2)

theorem ofNat_zero : ofNat 0 = falsum := by rw [ofNat]

theorem ofNat_succ (m : ℕ) : ofNat (m + 1) =
    if m % 4 = 0 then equal (m / 4).unpair.1 (m / 4).unpair.2
    else if m % 4 = 1 then rel (m / 4).unpair.1 (Denumerable.ofNat (List ℕ) (m / 4).unpair.2)
    else if m % 4 = 2 then imp (ofNat (m / 4).unpair.1) (ofNat (m / 4).unpair.2)
    else all (m / 4).unpair.1 (ofNat (m / 4).unpair.2) := by
  rw [ofNat]

private theorem ofNat_four_mul_add (p j : ℕ) (hj : j < 4) :
    ofNat (4 * p + j + 1) =
    if j = 0 then equal p.unpair.1 p.unpair.2
    else if j = 1 then rel p.unpair.1 (Denumerable.ofNat (List ℕ) p.unpair.2)
    else if j = 2 then imp (ofNat p.unpair.1) (ofNat p.unpair.2)
    else all p.unpair.1 (ofNat p.unpair.2) := by
  rw [ofNat_succ]
  have h1 : (4 * p + j) % 4 = j := by omega
  have h2 : (4 * p + j) / 4 = p := by omega
  rw [h1, h2]

theorem ofNat_toNat : ∀ φ : RawFormula, ofNat φ.toNat = φ
  | falsum => ofNat_zero
  | equal x y => by
    rw [toNat, ofNat_four_mul_add _ 0 (by omega)]
    simp
  | rel r args => by
    rw [toNat, show 4 * Nat.pair r (Encodable.encode args) + 2 =
      4 * Nat.pair r (Encodable.encode args) + 1 + 1 from rfl, ofNat_four_mul_add _ 1 (by omega)]
    simp
  | imp φ ψ => by
    rw [toNat,
      show 4 * Nat.pair φ.toNat ψ.toNat + 3 = 4 * Nat.pair φ.toNat ψ.toNat + 2 + 1 from rfl,
      ofNat_four_mul_add _ 2 (by omega)]
    simp [ofNat_toNat φ, ofNat_toNat ψ]
  | all x φ => by
    rw [toNat, show 4 * Nat.pair x φ.toNat + 4 = 4 * Nat.pair x φ.toNat + 3 + 1 from rfl,
      ofNat_four_mul_add _ 3 (by omega)]
    simp [ofNat_toNat φ]

theorem toNat_ofNat : ∀ n : ℕ, (ofNat n).toNat = n
  | 0 => by rw [ofNat_zero, toNat]
  | m + 1 => by
    have h1 := unpair_fst_div_four_lt m
    have h2 := unpair_snd_div_four_lt m
    have ih1 := toNat_ofNat (m / 4).unpair.1
    have ih2 := toNat_ofNat (m / 4).unpair.2
    have hm : 4 * (m / 4) + m % 4 = m := Nat.div_add_mod m 4
    have hp := Nat.pair_unpair (m / 4)
    rw [ofNat_succ]
    split_ifs with c0 c1 c2
    · rw [toNat, hp]; omega
    · rw [toNat, Denumerable.encode_ofNat, hp]; omega
    · rw [toNat, ih1, ih2, hp]; omega
    · rw [toNat, ih2, hp]; omega

instance : Denumerable RawFormula :=
  Denumerable.mk' ⟨toNat, ofNat, ofNat_toNat, toNat_ofNat⟩

theorem encode_eq_toNat (φ : RawFormula) : Encodable.encode φ = φ.toNat := rfl

theorem ofNat_eq (n : ℕ) : Denumerable.ofNat RawFormula n = ofNat n := rfl

/-! ### Derived connectives -/

/-- Negation. -/
def neg (φ : RawFormula) : RawFormula := imp φ falsum

/-- Truth. -/
def verum : RawFormula := neg falsum

/-- Disjunction. -/
def disj (φ ψ : RawFormula) : RawFormula := imp (neg φ) ψ

/-- Conjunction. -/
def conj (φ ψ : RawFormula) : RawFormula := neg (imp φ (neg ψ))

/-- Existential quantification. -/
def ex (x : ℕ) (φ : RawFormula) : RawFormula := neg (all x (neg φ))

/-- Biconditional. -/
def iff (φ ψ : RawFormula) : RawFormula := conj (imp φ ψ) (imp ψ φ)

/-- Conjunction of a list of formulas. -/
def bigConj : List RawFormula → RawFormula
  | [] => verum
  | φ :: l => conj φ (bigConj l)

theorem bigConj_eq_foldr (l : List RawFormula) : bigConj l = l.foldr conj verum := by
  induction l with
  | nil => rfl
  | cons φ l ih => simp only [bigConj, ih, List.foldr_cons]

/-- Rename relation symbol `r` to `σ.getD r r`. -/
def rename (σ : List ℕ) : RawFormula → RawFormula
  | falsum => falsum
  | equal x y => equal x y
  | rel r args => rel (σ.getD r r) args
  | imp φ ψ => imp (rename σ φ) (rename σ ψ)
  | all x φ => all x (rename σ φ)

/-- A strict upper bound on the variables occurring in a formula. -/
def varBound : RawFormula → ℕ
  | falsum => 0
  | equal x y => max x y + 1
  | rel _ args => (args.map (· + 1)).foldr max 0
  | imp φ ψ => max φ.varBound ψ.varBound
  | all x φ => max (x + 1) φ.varBound

/-- The relation symbols occurring in a formula, with the arities at which they occur. -/
def atoms : RawFormula → List (ℕ × ℕ)
  | falsum => []
  | equal _ _ => []
  | rel r args => [(r, args.length)]
  | imp φ ψ => φ.atoms ++ ψ.atoms
  | all _ φ => φ.atoms

theorem lt_varBound_of_mem {x : ℕ} {args : List ℕ} (h : x ∈ args) :
    x < ((args.map (· + 1)).foldr max 0) := by
  induction args with
  | nil => simp at h
  | cons a as ih =>
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h; omega

/-! ### Semantics -/

variable {M : Type*}

/-- Satisfaction of a formula in `M` under the relation interpretation `I` and assignment `v`. -/
def Realize (I : ℕ → List M → Prop) : RawFormula → (ℕ → M) → Prop
  | falsum, _ => False
  | equal x y, v => v x = v y
  | rel r args, v => I r (args.map v)
  | imp φ ψ, v => Realize I φ v → Realize I ψ v
  | all x φ, v => ∀ m : M, Realize I φ (Function.update v x m)

section Realize

variable {I : ℕ → List M → Prop} {v : ℕ → M}

@[simp] theorem realize_falsum : falsum.Realize I v ↔ False := Iff.rfl

@[simp] theorem realize_equal {x y : ℕ} : (equal x y).Realize I v ↔ v x = v y := Iff.rfl

@[simp] theorem realize_rel {r : ℕ} {args : List ℕ} :
    (rel r args).Realize I v ↔ I r (args.map v) := Iff.rfl

@[simp] theorem realize_imp {φ ψ : RawFormula} :
    (imp φ ψ).Realize I v ↔ (φ.Realize I v → ψ.Realize I v) := Iff.rfl

@[simp] theorem realize_all {x : ℕ} {φ : RawFormula} :
    (all x φ).Realize I v ↔ ∀ m, φ.Realize I (Function.update v x m) := Iff.rfl

@[simp] theorem realize_neg {φ : RawFormula} : (neg φ).Realize I v ↔ ¬φ.Realize I v := Iff.rfl

@[simp] theorem realize_verum : verum.Realize I v ↔ True := by simp [verum]

@[simp] theorem realize_disj {φ ψ : RawFormula} :
    (disj φ ψ).Realize I v ↔ φ.Realize I v ∨ ψ.Realize I v := by
  simp only [disj, realize_imp, realize_neg]
  tauto

@[simp] theorem realize_conj {φ ψ : RawFormula} :
    (conj φ ψ).Realize I v ↔ φ.Realize I v ∧ ψ.Realize I v := by
  simp only [conj, realize_imp, realize_neg]
  tauto

@[simp] theorem realize_ex {x : ℕ} {φ : RawFormula} :
    (ex x φ).Realize I v ↔ ∃ m, φ.Realize I (Function.update v x m) := by
  simp [ex]

@[simp] theorem realize_iff {φ ψ : RawFormula} :
    (iff φ ψ).Realize I v ↔ (φ.Realize I v ↔ ψ.Realize I v) := by
  simp only [iff, realize_conj, realize_imp]
  tauto

@[simp] theorem realize_bigConj {l : List RawFormula} :
    (bigConj l).Realize I v ↔ ∀ φ ∈ l, φ.Realize I v := by
  induction l with
  | nil => simp [bigConj]
  | cons φ l ih => simp [bigConj, ih]

end Realize

theorem realize_rename (σ : List ℕ) (I : ℕ → List M → Prop) :
    ∀ (φ : RawFormula) (v : ℕ → M),
      (rename σ φ).Realize I v ↔ φ.Realize (fun r => I (σ.getD r r)) v
  | falsum, _ => Iff.rfl
  | equal _ _, _ => Iff.rfl
  | rel _ _, _ => Iff.rfl
  | imp φ ψ, v => by
    simp only [rename, realize_imp, realize_rename σ I φ, realize_rename σ I ψ]
  | all x φ, v => by
    simp only [rename, realize_all, realize_rename σ I φ]

theorem realize_congr_var {I : ℕ → List M → Prop} :
    ∀ (φ : RawFormula) {v w : ℕ → M}, (∀ x < φ.varBound, v x = w x) →
      (φ.Realize I v ↔ φ.Realize I w)
  | falsum, _, _, _ => Iff.rfl
  | equal x y, v, w, h => by
    simp only [Realize, varBound] at h ⊢
    rw [h x (by omega), h y (by omega)]
  | rel r args, v, w, h => by
    simp only [Realize, varBound] at h ⊢
    rw [List.map_congr_left fun x hx => h x (lt_varBound_of_mem hx)]
  | imp φ ψ, v, w, h => by
    simp only [Realize, varBound] at h ⊢
    rw [realize_congr_var φ fun x hx => h x (lt_max_of_lt_left hx),
      realize_congr_var ψ fun x hx => h x (lt_max_of_lt_right hx)]
  | all x φ, v, w, h => by
    simp only [Realize, varBound] at h ⊢
    refine forall_congr' fun m => realize_congr_var φ fun y hy => ?_
    by_cases hyx : y = x
    · subst hyx; simp
    · simp [Function.update_of_ne hyx, h y (lt_max_of_lt_right hy)]

theorem realize_congr_rel {I J : ℕ → List M → Prop} :
    ∀ (φ : RawFormula) (v : ℕ → M),
      (∀ r (as : List M), (r, as.length) ∈ φ.atoms → (I r as ↔ J r as)) →
      (φ.Realize I v ↔ φ.Realize J v)
  | falsum, _, _ => Iff.rfl
  | equal _ _, _, _ => Iff.rfl
  | rel r args, v, h => h r _ (by simp [atoms])
  | imp φ ψ, v, h => by
    simp only [Realize, atoms, List.mem_append] at h ⊢
    rw [realize_congr_rel φ v fun r as hr => h r as (Or.inl hr),
      realize_congr_rel ψ v fun r as hr => h r as (Or.inr hr)]
  | all x φ, v, h => by
    simp only [Realize, atoms] at h ⊢
    exact forall_congr' fun m => realize_congr_rel φ _ h

theorem realize_equiv {N : Type*} (e : M ≃ N) (I : ℕ → List M → Prop) :
    ∀ (φ : RawFormula) (v : ℕ → M),
      φ.Realize (fun r as => I r (as.map e.symm)) (e ∘ v) ↔ φ.Realize I v
  | falsum, _ => Iff.rfl
  | equal x y, v => by simp [Realize]
  | rel r args, v => by simp [Realize, Function.comp_def]
  | imp φ ψ, v => by
    simp only [Realize]
    rw [realize_equiv e I φ v, realize_equiv e I ψ v]
  | all x φ, v => by
    simp only [Realize]
    refine (e.forall_congr_right).symm.trans (forall_congr' fun m => ?_)
    rw [← realize_equiv e I φ (Function.update v x m)]
    congr! 1
    funext y
    by_cases hyx : y = x
    · subst hyx; simp
    · simp [Function.update_of_ne hyx]

/-! ### Finite satisfiability and finite validity -/

/-- `φ` is **finitely satisfiable**: it holds in some finite nonempty structure under some
assignment. -/
def FinSat (φ : RawFormula) : Prop :=
  ∃ (M : Type) (_ : Finite M) (_ : Nonempty M) (I : ℕ → List M → Prop) (v : ℕ → M),
    φ.Realize I v

/-- `φ` is **finitely valid**: it holds in every finite nonempty structure under every
assignment. -/
def FinValid (φ : RawFormula) : Prop :=
  ∀ (M : Type) [Finite M] [Nonempty M] (I : ℕ → List M → Prop) (v : ℕ → M), φ.Realize I v

theorem finValid_neg_iff (φ : RawFormula) : FinValid (neg φ) ↔ ¬FinSat φ := by
  simp only [FinValid, FinSat, realize_neg, not_exists]

theorem finValid_iff_not_finSat_neg (φ : RawFormula) : FinValid φ ↔ ¬FinSat (neg φ) := by
  simp only [FinValid, FinSat, realize_neg, not_exists, not_not]

end RawFormula

end Cslib.Logic.FO
