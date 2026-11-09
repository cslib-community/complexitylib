/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Trakhtenbrot.Arithmetic
public import CslibFrontier.Logics.FirstOrder.Raw.Primrec
public import Mathlib.Computability.PartrecCode

/-!
# First-order axioms for the graphs of `Nat.Partrec.Code.evaln`

The reduction in Trakhtenbrot's theorem describes a halting computation inside a finite
structure. Here the computation model is Mathlib's step-bounded evaluator
`Nat.Partrec.Code.evaln k c n : Option ℕ` for partial recursive codes. Over the arithmetic
symbols `0`–`3` of `CslibFrontier/Logics/FirstOrder/Trakhtenbrot/Arithmetic.lean`, the ternary
relation symbol `encode c + 4` is intended as the graph `{(k, n, x) | evaln k c n = some x}`.
The axiom `evAx c` says that every tuple in that graph satisfies `n < k` and one unfolding of
the defining equations of `evaln` for `c`, phrased with the arithmetic symbols and the graph
symbols of the immediate subcodes of `c` (and of `c` itself, at step `k - 1`, for `prec` and
`rfind'`).

Only this one direction is axiomatized. It suffices: in a model whose arithmetic is standard
(which every finite model of `arithAxioms` is, by `arithModel_faithful`), every tuple in the
graph is a true `evaln` fact (`evaln_of_model`, by induction on the step count and the code).
Conversely, the true graphs on a large enough initial segment `Fin N` satisfy the axioms
(`stdInterp_caseSem`).

## Main definitions

* `Cslib.Logic.FO.Trakhtenbrot.evAx`: the axiom for the graph of `evaln · c`.
* `Cslib.Logic.FO.Trakhtenbrot.CaseSem`: its semantic content.
* `Cslib.Logic.FO.Trakhtenbrot.stdInterp`: the standard interpretation on `Fin N`, with the
  graphs of `evaln k c` for `k ≤ K`.

## Main results

* `Cslib.Logic.FO.Trakhtenbrot.realize_evAx`: the sentence `evAx c` expresses `CaseSem`.
* `Cslib.Logic.FO.Trakhtenbrot.evaln_of_model`: soundness of the axioms in standard models.
* `Cslib.Logic.FO.Trakhtenbrot.stdInterp_caseSem`: the standard interpretation satisfies the
  axioms once `N` exceeds the step bound and all relevant outputs.
* `Cslib.Logic.FO.Trakhtenbrot.primrec_evAx`: `evAx` is primitive recursive.
-/

public section

namespace Cslib.Logic.FO.Trakhtenbrot

open RawFormula
open Nat.Partrec (Code)
open Encodable (encode)

variable {M : Type*}

/-! ### Unfolding `Code.evaln` -/

section Evaln

variable {k n x : ℕ} {cf cg : Code}

private theorem evaln_succ_zero_iff (h : n ≤ k) :
    Code.evaln (k + 1) Code.zero n = some x ↔ x = 0 := by
  simp [Code.evaln, h, eq_comm]

private theorem evaln_succ_succ_iff (h : n ≤ k) :
    Code.evaln (k + 1) Code.succ n = some x ↔ x = n + 1 := by
  simp [Code.evaln, h, eq_comm]

private theorem evaln_succ_left_iff (h : n ≤ k) :
    Code.evaln (k + 1) Code.left n = some x ↔ x = n.unpair.1 := by
  simp [Code.evaln, h, eq_comm]

private theorem evaln_succ_right_iff (h : n ≤ k) :
    Code.evaln (k + 1) Code.right n = some x ↔ x = n.unpair.2 := by
  simp [Code.evaln, h, eq_comm]

private theorem evaln_succ_pair_iff (h : n ≤ k) :
    Code.evaln (k + 1) (Code.pair cf cg) n = some x ↔
      ∃ a b, Code.evaln (k + 1) cf n = some a ∧ Code.evaln (k + 1) cg n = some b ∧
        Nat.pair a b = x := by
  simp [Code.evaln, h, Option.bind_eq_some_iff, Seq.seq]

private theorem evaln_succ_comp_iff (h : n ≤ k) :
    Code.evaln (k + 1) (Code.comp cf cg) n = some x ↔
      ∃ y, Code.evaln (k + 1) cg n = some y ∧ Code.evaln (k + 1) cf y = some x := by
  simp [Code.evaln, h, Option.bind_eq_some_iff]

private theorem evaln_succ_prec_iff (h : n ≤ k) :
    Code.evaln (k + 1) (Code.prec cf cg) n = some x ↔
      (n.unpair.2 = 0 ∧ Code.evaln (k + 1) cf n.unpair.1 = some x) ∨
      ∃ y', n.unpair.2 = y' + 1 ∧
        ∃ i, Code.evaln k (Code.prec cf cg) (Nat.pair n.unpair.1 y') = some i ∧
          Code.evaln (k + 1) cg (Nat.pair n.unpair.1 (Nat.pair y' i)) = some x := by
  simp only [Code.evaln, h, Nat.unpaired]
  rcases n.unpair.2 with _ | y'
  · simp
  · simp [Option.bind_eq_some_iff]

private theorem evaln_succ_rfind_iff (h : n ≤ k) :
    Code.evaln (k + 1) (Code.rfind' cf) n = some x ↔
      ∃ w, Code.evaln (k + 1) cf n = some w ∧
        ((w = 0 ∧ x = n.unpair.2) ∨
          (w ≠ 0 ∧
            Code.evaln k (Code.rfind' cf) (Nat.pair n.unpair.1 (n.unpair.2 + 1)) = some x)) := by
  simp only [Code.evaln, h, Nat.unpaired]
  simp only [guard, ite_true, Nat.pair_unpair, Option.pure_def, Option.bind_eq_bind,
    Option.bind_some, Option.bind_eq_some_iff]
  refine exists_congr fun w => and_congr_right fun _ => ?_
  split_ifs with hw <;> simp [hw, eq_comm]

end Evaln

/-! ### The axioms

The axiom for `c` is written over seven symbol slots `0`–`6` (`<`, zero, successor, pairing,
`c` itself, and the immediate subcodes of `c`) and then renamed by `symList c`. In the bodies,
variable `0` is the step bound `k`, variable `1` the input `n` and variable `2` the output `x`. -/

/-- Body for `Code.zero`. -/
def bodyZero : RawFormula := rel 1 [2]

/-- Body for `Code.succ`. -/
def bodySucc : RawFormula := rel 2 [1, 2]

/-- Body for `Code.left`. -/
def bodyLeft : RawFormula := ex 3 (rel 3 [2, 3, 1])

/-- Body for `Code.right`. -/
def bodyRight : RawFormula := ex 3 (rel 3 [3, 2, 1])

/-- Body for `Code.pair`. -/
def bodyPair : RawFormula :=
  ex 3 (ex 4 (conj (rel 5 [0, 1, 3]) (conj (rel 6 [0, 1, 4]) (rel 3 [3, 4, 2]))))

/-- Body for `Code.comp`. -/
def bodyComp : RawFormula := ex 3 (conj (rel 6 [0, 1, 3]) (rel 5 [0, 3, 2]))

/-- Body for `Code.prec` (`3 = a`, `4 = y`, `5 = y'`, `6 = k'`, `7 = t`, `8 = i`, `9 = s`,
`10 = u`). -/
def bodyPrec : RawFormula :=
  ex 3 (ex 4 (conj (rel 3 [3, 4, 1]) (disj (conj (rel 1 [4]) (rel 5 [0, 3, 2]))
    (ex 5 (ex 6 (ex 7 (ex 8 (ex 9 (ex 10 (conj (rel 2 [5, 4]) (conj (rel 2 [6, 0])
      (conj (rel 3 [3, 5, 7]) (conj (rel 4 [6, 7, 8]) (conj (rel 3 [5, 8, 9])
        (conj (rel 3 [3, 9, 10]) (rel 6 [0, 10, 2]))))))))))))))))

/-- Body for `Code.rfind'` (`3 = a`, `4 = j`, `5 = w`, `6 = k'`, `7 = j'`, `8 = t`). -/
def bodyRfind : RawFormula :=
  ex 3 (ex 4 (ex 5 (conj (rel 3 [3, 4, 1]) (conj (rel 5 [0, 1, 5])
    (disj (conj (rel 1 [5]) (equal 2 4))
      (conj (neg (rel 1 [5])) (ex 6 (ex 7 (ex 8 (conj (rel 2 [6, 0])
        (conj (rel 2 [4, 7]) (conj (rel 3 [3, 7, 8]) (rel 4 [6, 8, 2])))))))))))))

/-- The axiom skeleton: every tuple in the graph satisfies `n < k` and the body. -/
def evSkel (body : RawFormula) : RawFormula :=
  all 0 (all 1 (all 2 (imp (rel 4 [0, 1, 2]) (conj (rel 0 [1, 0]) body))))

/-- The body for a code. -/
def bodyOf : Code → RawFormula
  | .zero => bodyZero
  | .succ => bodySucc
  | .left => bodyLeft
  | .right => bodyRight
  | .pair _ _ => bodyPair
  | .comp _ _ => bodyComp
  | .prec _ _ => bodyPrec
  | .rfind' _ => bodyRfind

/-- Encodings of the immediate subcodes (`0` when absent). -/
def subCodes : Code → ℕ × ℕ
  | .pair cf cg => (encode cf, encode cg)
  | .comp cf cg => (encode cf, encode cg)
  | .prec cf cg => (encode cf, encode cg)
  | .rfind' cf => (encode cf, 0)
  | _ => (0, 0)

/-- The symbol renaming for the axiom of `c`: slots `4`, `5`, `6` become the graph symbols of `c`
and of its immediate subcodes. -/
def symList (c : Code) : List ℕ :=
  [0, 1, 2, 3] ++ [encode c + 4, (subCodes c).1 + 4, (subCodes c).2 + 4]

/-- The axiom for the graph of `evaln · c`. -/
def evAx (c : Code) : RawFormula := rename (symList c) (evSkel (bodyOf c))

/-- Semantic content of the axiom for `c`, at a tuple `(k, n, x)`. -/
def CaseSem (I : ℕ → List M → Prop) : Code → M → M → M → Prop
  | .zero, _, _, x => I 1 [x]
  | .succ, _, n, x => I 2 [n, x]
  | .left, _, n, x => ∃ b, I 3 [x, b, n]
  | .right, _, n, x => ∃ a, I 3 [a, x, n]
  | .pair cf cg, k, n, x => ∃ a b, I (encode cf + 4) [k, n, a] ∧ I (encode cg + 4) [k, n, b] ∧
      I 3 [a, b, x]
  | .comp cf cg, k, n, x => ∃ y, I (encode cg + 4) [k, n, y] ∧ I (encode cf + 4) [k, y, x]
  | .prec cf cg, k, n, x => ∃ a y, I 3 [a, y, n] ∧ ((I 1 [y] ∧ I (encode cf + 4) [k, a, x]) ∨
      ∃ y' k' t i s u, I 2 [y', y] ∧ I 2 [k', k] ∧ I 3 [a, y', t] ∧
        I (encode (Code.prec cf cg) + 4) [k', t, i] ∧ I 3 [y', i, s] ∧ I 3 [a, s, u] ∧
          I (encode cg + 4) [k, u, x])
  | .rfind' cf, k, n, x => ∃ a j w, I 3 [a, j, n] ∧ I (encode cf + 4) [k, n, w] ∧
      ((I 1 [w] ∧ x = j) ∨ (¬I 1 [w] ∧ ∃ k' j' t, I 2 [k', k] ∧ I 2 [j, j'] ∧ I 3 [a, j', t] ∧
        I (encode (Code.rfind' cf) + 4) [k', t, x]))

theorem realize_evAx {I : ℕ → List M → Prop} {v : ℕ → M} (c : Code) :
    (evAx c).Realize I v ↔
      ∀ k n x, I (encode c + 4) [k, n, x] → I 0 [n, k] ∧ CaseSem I c k n x := by
  rw [evAx, realize_rename]
  cases c <;>
    simp [evSkel, bodyOf, symList, subCodes, CaseSem, bodyZero, bodySucc, bodyLeft, bodyRight,
      bodyPair, bodyComp, bodyPrec, bodyRfind]

/-! ### Soundness: a model with standard arithmetic only contains true `evaln` facts -/

/-- In any model of the `evaln` axioms whose order, zero, successor and pairing are standard
along `val` (as provided for finite models by `arithModel_faithful`), every tuple in the graph of
a code `c` is a true `evaln` fact. -/
theorem evaln_of_model {I : ℕ → List M → Prop} (val : M → ℕ)
    (hlt : ∀ a b, I 0 [a, b] ↔ val a < val b) (hz : ∀ a, I 1 [a] ↔ val a = 0)
    (hs : ∀ a b, I 2 [a, b] ↔ val b = val a + 1)
    (hp : ∀ a b p, I 3 [a, b, p] ↔ Nat.pair (val a) (val b) = val p) {C : ℕ}
    (hax : ∀ d : Code, encode d ≤ C → ∀ k n x, I (encode d + 4) [k, n, x] →
      I 0 [n, k] ∧ CaseSem I d k n x) :
    ∀ (c : Code), encode c ≤ C → ∀ k n x, I (encode c + 4) [k, n, x] →
      Code.evaln (val k) c (val n) = some (val x) := by
  suffices H : ∀ K, ∀ (c : Code), encode c ≤ C → ∀ k n x, val k = K →
      I (encode c + 4) [k, n, x] → Code.evaln K c (val n) = some (val x) from
    fun c hc k n x hI => H _ c hc k n x rfl hI
  intro K
  induction K using Nat.strong_induction_on with
  | _ K ihK =>
  intro c
  induction c with
  | zero =>
    intro hc k n x hk hI
    obtain ⟨hnk, hcase⟩ := hax _ hc k n x hI
    rw [hlt, hk] at hnk
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    rw [evaln_succ_zero_iff (by omega)]
    exact (hz x).1 hcase
  | succ =>
    intro hc k n x hk hI
    obtain ⟨hnk, hcase⟩ := hax _ hc k n x hI
    rw [hlt, hk] at hnk
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    rw [evaln_succ_succ_iff (by omega)]
    exact (hs n x).1 hcase
  | left =>
    intro hc k n x hk hI
    obtain ⟨hnk, b, hb⟩ := hax _ hc k n x hI
    rw [hlt, hk] at hnk
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    rw [evaln_succ_left_iff (by omega), ← (hp _ _ _).1 hb, Nat.unpair_pair]
  | right =>
    intro hc k n x hk hI
    obtain ⟨hnk, a, ha⟩ := hax _ hc k n x hI
    rw [hlt, hk] at hnk
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    rw [evaln_succ_right_iff (by omega), ← (hp _ _ _).1 ha, Nat.unpair_pair]
  | pair cf cg ihf ihg =>
    intro hc k n x hk hI
    obtain ⟨hnk, a, b, ha, hb, hab⟩ := hax _ hc k n x hI
    rw [hlt, hk] at hnk
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    have h1 := Code.encode_lt_pair cf cg
    rw [evaln_succ_pair_iff (by omega)]
    exact ⟨_, _, ihf (by omega) k n a hk ha, ihg (by omega) k n b hk hb, (hp _ _ _).1 hab⟩
  | comp cf cg ihf ihg =>
    intro hc k n x hk hI
    obtain ⟨hnk, y, hy, hx⟩ := hax _ hc k n x hI
    rw [hlt, hk] at hnk
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    have h1 := Code.encode_lt_comp cf cg
    rw [evaln_succ_comp_iff (by omega)]
    exact ⟨_, ihg (by omega) k n y hk hy, ihf (by omega) k y x hk hx⟩
  | prec cf cg ihf ihg =>
    intro hc k n x hk hI
    obtain ⟨hnk, a, y, hay, hcase⟩ := hax _ hc k n x hI
    rw [hlt, hk] at hnk
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    have h1 := Code.encode_lt_prec cf cg
    have hun : (val n).unpair = (val a, val y) := by rw [← (hp _ _ _).1 hay, Nat.unpair_pair]
    rw [evaln_succ_prec_iff (by omega), hun]
    rcases hcase with ⟨hy0, hx⟩ | ⟨y', k', t, i, s, u, hyy, hkk, ht, hi, hs', hu, hx⟩
    · exact Or.inl ⟨(hz y).1 hy0, ihf (by omega) k a x hk hx⟩
    · rw [hs, hk] at hkk
      rw [hs] at hyy
      refine Or.inr ⟨val y', hyy, val i, ?_, ?_⟩
      · have := ihK K' (by omega) (Code.prec cf cg) hc k' t i (by omega) hi
        rwa [← (hp _ _ _).1 ht] at this
      · have := ihg (by omega) k u x hk hx
        rwa [← (hp _ _ _).1 hu, ← (hp _ _ _).1 hs'] at this
  | rfind' cf ihf =>
    intro hc k n x hk hI
    obtain ⟨hnk, a, j, w, haj, hw, hcase⟩ := hax _ hc k n x hI
    rw [hlt, hk] at hnk
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    have h1 := Code.encode_lt_rfind' cf
    have hun : (val n).unpair = (val a, val j) := by rw [← (hp _ _ _).1 haj, Nat.unpair_pair]
    rw [evaln_succ_rfind_iff (by omega), hun]
    refine ⟨val w, ihf (by omega) k n w hk hw, ?_⟩
    rcases hcase with ⟨hw0, rfl⟩ | ⟨hw0, k', j', t, hkk, hjj, ht, hx⟩
    · exact Or.inl ⟨(hz w).1 hw0, rfl⟩
    · rw [hs, hk] at hkk
      rw [hs] at hjj
      refine Or.inr ⟨fun h => hw0 ((hz w).2 h), ?_⟩
      have := ihK K' (by omega) (Code.rfind' cf) hc k' t x (by omega) hx
      rwa [← (hp _ _ _).1 ht, hjj] at this

/-! ### Completeness: the true graphs satisfy the axioms on a large initial segment -/

/-- A bound on all outputs of `evaln k c n` with `k ≤ K` and `encode c ≤ C`. -/
noncomputable def outBound (K C : ℕ) : ℕ :=
  (Finset.range (K + 1)).sup fun k => (Finset.range K).sup fun n =>
    (Finset.range (C + 1)).sup fun m => (Code.evaln k (Denumerable.ofNat Code m) n).getD 0

theorem le_outBound {K C k n x : ℕ} {c : Code} (hk : k ≤ K) (hc : encode c ≤ C)
    (h : Code.evaln k c n = some x) : x ≤ outBound K C := by
  have hn : n < k := Code.evaln_bound h
  refine Finset.le_sup_of_le (Finset.mem_range.2 (by omega : k < K + 1)) ?_
  refine Finset.le_sup_of_le (Finset.mem_range.2 (by omega : n < K)) ?_
  refine Finset.le_sup_of_le (Finset.mem_range.2 (by omega : encode c < C + 1)) ?_
  simp [h]

/-- The standard interpretation on `Fin N`: the standard arithmetic relations, together with the
graphs of `evaln k c` for `k ≤ K`. -/
def stdInterp (N K : ℕ) : ℕ → List (Fin N) → Prop
  | m + 4, [k, n, x] => (k : ℕ) ≤ K ∧ Code.evaln k (Denumerable.ofNat Code m) n = some (x : ℕ)
  | r, l => StdArith N r l

section StdInterp

variable {N K : ℕ}

@[simp] theorem stdInterp_lt (a b : Fin N) : stdInterp N K 0 [a, b] ↔ (a : ℕ) < b := Iff.rfl

@[simp] theorem stdInterp_zero (a : Fin N) : stdInterp N K 1 [a] ↔ (a : ℕ) = 0 := Iff.rfl

@[simp] theorem stdInterp_succ (a b : Fin N) : stdInterp N K 2 [a, b] ↔ (b : ℕ) = a + 1 :=
  Iff.rfl

@[simp] theorem stdInterp_pair (a b p : Fin N) :
    stdInterp N K 3 [a, b, p] ↔ Nat.pair a b = p := Iff.rfl

@[simp] theorem stdInterp_ev (c : Code) (k n x : Fin N) :
    stdInterp N K (encode c + 4) [k, n, x] ↔
      (k : ℕ) ≤ K ∧ Code.evaln k c n = some (x : ℕ) := by
  simp only [stdInterp, Denumerable.ofNat_encode]

theorem arithModel_stdInterp : ArithModel (stdInterp N K) :=
  arithModel_of_std (fun _ _ => Iff.rfl) (fun _ => Iff.rfl) (fun _ _ => Iff.rfl)
    (fun _ _ _ => Iff.rfl)

/-- The standard interpretation satisfies the `evaln` axioms for all codes `c` with
`encode c ≤ C`, provided `N` exceeds `K` and all outputs bounded by `outBound K C`. -/
theorem stdInterp_caseSem {C : ℕ} (hN : K + outBound K C < N) (c : Code) (hc : encode c ≤ C)
    (k n x : Fin N) (hI : stdInterp N K (encode c + 4) [k, n, x]) :
    stdInterp N K 0 [n, k] ∧ CaseSem (stdInterp N K) c k n x := by
  rw [stdInterp_ev] at hI
  obtain ⟨hkK, h⟩ := hI
  have hnk : (n : ℕ) < k := Code.evaln_bound h
  refine ⟨hnk, ?_⟩
  obtain ⟨k', hk'⟩ : ∃ k', (k : ℕ) = k' + 1 := ⟨(k : ℕ) - 1, by omega⟩
  rw [hk'] at h
  have hout : ∀ {d : Code} {k₀ n₀ x₀ : ℕ}, k₀ ≤ K → encode d ≤ C →
      Code.evaln k₀ d n₀ = some x₀ → x₀ < N := fun hk hd h =>
    by have := le_outBound hk hd h; omega
  have hin : ∀ {d : Code} {k₀ n₀ x₀ : ℕ}, k₀ ≤ K → Code.evaln k₀ d n₀ = some x₀ → n₀ < N :=
    fun hk h => by have := Code.evaln_bound h; omega
  cases c with
  | zero =>
    rw [evaln_succ_zero_iff (by omega)] at h
    exact h
  | succ =>
    rw [evaln_succ_succ_iff (by omega)] at h
    change (x : ℕ) = n + 1
    exact h
  | left =>
    rw [evaln_succ_left_iff (by omega)] at h
    refine ⟨⟨(n : ℕ).unpair.2, lt_of_le_of_lt (Nat.unpair_right_le _) n.2⟩, ?_⟩
    change Nat.pair x _ = n
    rw [h, Nat.pair_unpair]
  | right =>
    rw [evaln_succ_right_iff (by omega)] at h
    refine ⟨⟨(n : ℕ).unpair.1, lt_of_le_of_lt (Nat.unpair_left_le _) n.2⟩, ?_⟩
    change Nat.pair _ x = n
    rw [h, Nat.pair_unpair]
  | pair cf cg =>
    have h1 := Code.encode_lt_pair cf cg
    rw [evaln_succ_pair_iff (by omega)] at h
    obtain ⟨a, b, ha, hb, hab⟩ := h
    rw [← hk'] at ha hb
    refine ⟨⟨a, hout hkK (by omega) ha⟩, ⟨b, hout hkK (by omega) hb⟩, ?_, ?_, ?_⟩
    · simpa [hkK] using ha
    · simpa [hkK] using hb
    · exact hab
  | comp cf cg =>
    have h1 := Code.encode_lt_comp cf cg
    rw [evaln_succ_comp_iff (by omega)] at h
    obtain ⟨y, hy, hx⟩ := h
    rw [← hk'] at hy hx
    refine ⟨⟨y, hout hkK (by omega) hy⟩, ?_, ?_⟩
    · simpa [hkK] using hy
    · simpa [hkK] using hx
  | prec cf cg =>
    have h1 := Code.encode_lt_prec cf cg
    rw [evaln_succ_prec_iff (by omega)] at h
    refine ⟨⟨(n : ℕ).unpair.1, lt_of_le_of_lt (Nat.unpair_left_le _) n.2⟩,
      ⟨(n : ℕ).unpair.2, lt_of_le_of_lt (Nat.unpair_right_le _) n.2⟩,
      (Nat.pair_unpair (n : ℕ) :), ?_⟩
    rcases h with ⟨hy0, hx⟩ | ⟨y', hy', i, hi, hx⟩
    · rw [← hk'] at hx
      exact Or.inl ⟨hy0, by simpa [hkK] using hx⟩
    · rw [← hk'] at hx
      have hiN : i < N := hout (by omega) hc hi
      have htN := hin (by omega : k' ≤ K) hi
      have huN := hin hkK hx
      have hsN : Nat.pair y' i < N :=
        lt_of_le_of_lt (Nat.right_le_pair _ _) huN
      have := Nat.unpair_right_le (n : ℕ)
      have := n.2
      refine Or.inr ⟨⟨y', by omega⟩, ⟨k', by omega⟩, ⟨_, htN⟩, ⟨i, hiN⟩, ⟨_, hsN⟩, ⟨_, huN⟩,
        ?_, ?_, rfl, ?_, rfl, rfl, ?_⟩
      · change (n : ℕ).unpair.2 = y' + 1
        exact hy'
      · change (k : ℕ) = k' + 1
        exact hk'
      · simpa [show k' ≤ K by omega] using hi
      · simpa [hkK] using hx
  | rfind' cf =>
    have h1 := Code.encode_lt_rfind' cf
    rw [evaln_succ_rfind_iff (by omega)] at h
    obtain ⟨w, hw, hcase⟩ := h
    rw [← hk'] at hw
    refine ⟨⟨(n : ℕ).unpair.1, lt_of_le_of_lt (Nat.unpair_left_le _) n.2⟩,
      ⟨(n : ℕ).unpair.2, lt_of_le_of_lt (Nat.unpair_right_le _) n.2⟩,
      ⟨w, hout hkK (by omega) hw⟩, (Nat.pair_unpair (n : ℕ) :), by simpa [hkK] using hw, ?_⟩
    rcases hcase with ⟨hw0, hx⟩ | ⟨hw0, hx⟩
    · exact Or.inl ⟨hw0, Fin.ext hx⟩
    · have htN := hin (by omega : k' ≤ K) hx
      have hjN : (n : ℕ).unpair.2 + 1 < N := lt_of_le_of_lt (Nat.right_le_pair _ _) htN
      refine Or.inr ⟨hw0, ⟨k', by omega⟩, ⟨_, hjN⟩, ⟨_, htN⟩, ?_, rfl, rfl, ?_⟩
      · change (k : ℕ) = k' + 1
        exact hk'
      · simpa [show k' ≤ K by omega] using hx

end StdInterp

/-! ### Primitive recursiveness of the axioms -/

section Primrec

open Primrec

theorem primrec_bodyOf : Primrec bodyOf := by
  refine Primrec.of_eq (Code.primrec_recOn' (α := Code) (σ := RawFormula) Primrec.id
    (const bodyZero) (const bodySucc) (const bodyLeft) (const bodyRight)
    (Primrec₂.const bodyPair) (Primrec₂.const bodyComp) (Primrec₂.const bodyPrec)
    (Primrec₂.const bodyRfind)) fun c => ?_
  cases c <;> rfl

theorem primrec_subCodes : Primrec subCodes := by
  have hpair : Primrec₂ fun (_ : Code) (p : Code × Code × (ℕ × ℕ) × (ℕ × ℕ)) =>
      (encode p.1, encode p.2.1) :=
    (Primrec.pair (Primrec.encode.comp (fst.comp snd))
      (Primrec.encode.comp (fst.comp (snd.comp snd)))).to₂
  have hrf : Primrec₂ fun (_ : Code) (p : Code × (ℕ × ℕ)) => (encode p.1, 0) :=
    (Primrec.pair (Primrec.encode.comp (fst.comp snd)) (const 0)).to₂
  refine Primrec.of_eq (Code.primrec_recOn' (α := Code) (σ := ℕ × ℕ) Primrec.id
    (const (0, 0)) (const (0, 0)) (const (0, 0)) (const (0, 0)) hpair hpair hpair hrf)
    fun c => ?_
  cases c <;> rfl

theorem primrec_symList : Primrec symList :=
  list_append.comp (const [0, 1, 2, 3]) (list_cons.comp (nat_add.comp Primrec.encode (const 4))
    (list_cons.comp (nat_add.comp (fst.comp primrec_subCodes) (const 4))
      (list_cons.comp (nat_add.comp (snd.comp primrec_subCodes) (const 4)) (const []))))

theorem primrec_evSkel : Primrec evSkel :=
  primrec_all (const 0) (primrec_all (const 1) (primrec_all (const 2)
    (primrec_imp (const (rel 4 [0, 1, 2])) (primrec_conj (const (rel 0 [1, 0])) Primrec.id))))

/-- The axiom map `c ↦ evAx c` is primitive recursive. -/
theorem primrec_evAx : Primrec evAx :=
  primrec₂_rename.comp primrec_symList (primrec_evSkel.comp primrec_bodyOf)

end Primrec

end Cslib.Logic.FO.Trakhtenbrot
