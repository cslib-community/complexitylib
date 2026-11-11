/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Accumulate
public import CslibFrontier.Computability.Circuit.Boolean.Comparison
public import CslibFrontier.Computability.Circuit.Boolean.Oracle
public import CslibFrontier.Computability.Circuit.Boolean.Substitution
public import CslibFrontier.Computability.Circuit.Pi

/-!
# Selecting an accepted candidate with oracle gates

A *selection round* asks the oracle about `N` candidates side by side and keeps the word of the
first accepted candidate, or a default word when none is accepted. Each query word and each
candidate word is read from *sources* (`Boolean.Source`): input wires or constants. A word of
sources is a substitution, so it reads the word `Boolean.substitute ρ x` from the input `x`. So a
candidate can mix fixed bits, such as its own index, with input bits, such as a truth-table entry
or the output of an earlier round. The default word is read from sources too, so it can be made
correct for the inputs it reads.

`Boolean.selectionRound src word dflt` is this round as an oracle circuit that keeps its inputs
and appends the selected word. Its queries have length `q`. It has `N` oracle gates, all at oracle
depth one, and its other gates are a chain of multiplexers (`Boolean.selectFirst`). Rounds compose
with `Circuit.accumulate`, where each round reads the inputs and the words of all earlier rounds;
`Boolean.eval_selectionRound` has the shape that `Circuit.eval_accumulate_block` consumes.

The selected word is the first accepted candidate's, or the default when none is accepted
(`Boolean.selectedWord_spec`). In particular, a property of words that every accepted candidate
and the default satisfy holds for the selected word (`Boolean.selectedWord_prop`).

## Main definitions

* `Cslib.Circuits.Boolean.firstSel`: the word of the first accepted candidate, or the default.
* `Cslib.Circuits.Boolean.selectFirst`: a De Morgan circuit computing `firstSel` by multiplexers.
* `Cslib.Circuits.Boolean.Source`, `Cslib.Circuits.Boolean.constLayer`,
  `Cslib.Circuits.Boolean.queryLayer`: sources of words, the two constant gates, and oracle gates
  side by side.
* `Cslib.Circuits.Boolean.selectionRound`, `Cslib.Circuits.Boolean.selectedWord`: one selection
  round and the word it selects.

## Main results

* `Cslib.Circuits.Boolean.firstSel_spec`, `Cslib.Circuits.Boolean.firstSel_prop`: the first
  accepted candidate, or the default.
* `Cslib.Circuits.Boolean.eval_selectionRound`, `Cslib.Circuits.Boolean.selectedWord_spec`,
  `Cslib.Circuits.Boolean.selectedWord_prop`: the semantics of a round.
* `Cslib.Circuits.Boolean.size_selectionRound`,
  `Cslib.Circuits.Boolean.cost_program_selectionRound`,
  `Cslib.Circuits.Boolean.depthWith_selectionRound_le`,
  `Cslib.Circuits.Boolean.fanInAtMost_selectionRound`: a round has `N` oracle gates, oracle depth
  at most one and fan-in at most `max q 2`.
-/

public section

namespace Cslib.Circuits.Boolean

variable {K N q w : ℕ}

/-! ### The first accepted candidate -/

/-- The word of the first candidate `i` with `acc i`, or the default `d` when there is none. -/
def firstSel (d : BitString w) : {N : ℕ} → (Fin N → Bool) → (Fin N → BitString w) → BitString w
  | 0, _, _ => d
  | _ + 1, acc, word => if acc 0 then word 0 else firstSel d (acc ∘ Fin.succ) (word ∘ Fin.succ)

/-- **The first accepted candidate, or the default.** Either some candidate is accepted and the
selected word is that of the first accepted candidate, or none is and it is the default. -/
theorem firstSel_spec (d : BitString w) (acc : Fin N → Bool) (word : Fin N → BitString w) :
    (∃ i, acc i = true ∧ (∀ j < i, acc j = false) ∧ firstSel d acc word = word i) ∨
      ((∀ i, acc i = false) ∧ firstSel d acc word = d) := by
  induction N with
  | zero => exact .inr ⟨fun i => i.elim0, rfl⟩
  | succ N ih =>
    by_cases h0 : acc 0 = true
    · refine .inl ⟨0, h0, fun j hj => absurd hj (Fin.not_lt_zero j), ?_⟩
      simp [firstSel, h0]
    · have hsel : firstSel d acc word = firstSel d (acc ∘ Fin.succ) (word ∘ Fin.succ) := by
        simp [firstSel, h0]
      rw [hsel]
      rcases ih (acc ∘ Fin.succ) (word ∘ Fin.succ) with ⟨i, hi, hfirst, h⟩ | ⟨hnone, h⟩
      · refine .inl ⟨i.succ, hi, fun j hj => ?_, h⟩
        cases j using Fin.cases with
        | zero => simpa using h0
        | succ j => exact hfirst j (Fin.succ_lt_succ_iff.mp hj)
      · refine .inr ⟨fun i => ?_, h⟩
        cases i using Fin.cases with
        | zero => simpa using h0
        | succ i => exact hnone i

/-- A property of words that the default and every accepted candidate's word have holds for the
selected word. -/
theorem firstSel_prop {P : BitString w → Prop} {d : BitString w} {acc : Fin N → Bool}
    {word : Fin N → BitString w} (hd : P d) (hacc : ∀ i, acc i = true → P (word i)) :
    P (firstSel d acc word) := by
  rcases firstSel_spec d acc word with ⟨i, hi, -, h⟩ | ⟨-, h⟩
  · rw [h]; exact hacc i hi
  · rw [h]; exact hd

/-- The De Morgan circuit selecting the first accepted candidate: candidate `i` is accepted when
the input `acc i` is true, and its word is read from the inputs `word i`; the default word is read
from the inputs `dflt`. A chain of `N` multiplexers. -/
def selectFirst (dflt : Fin w → Fin K) :
    {N : ℕ} → (Fin N → Fin K) → (Fin N → Fin w → Fin K) → Circuit signature K w
  | 0, _, _ => Circuit.wiring signature dflt
  | _ + 1, acc, word =>
    (muxCircuit w).comp
      ((Circuit.wiring signature fun _ : Fin 1 => acc 0).append
        ((Circuit.wiring signature (word 0)).append
          (selectFirst dflt (acc ∘ Fin.succ) (word ∘ Fin.succ))))

@[simp] theorem eval_selectFirst (dflt : Fin w → Fin K) (acc : Fin N → Fin K)
    (word : Fin N → Fin w → Fin K) (x : BitString K) :
    (selectFirst dflt acc word).eval interpretation x =
      firstSel (x ∘ dflt) (x ∘ acc) (fun i => x ∘ word i) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [selectFirst, Circuit.eval_comp, Circuit.eval_append, Circuit.eval_append,
      Circuit.eval_wiring, Circuit.eval_wiring, ih]
    exact eval_muxCircuit (x (acc 0)) _ _

@[simp] theorem size_selectFirst (dflt : Fin w → Fin K) (acc : Fin N → Fin K)
    (word : Fin N → Fin w → Fin K) : (selectFirst dflt acc word).size = N * (3 * w + 1) := by
  induction N with
  | zero => rw [Nat.zero_mul]; rfl
  | succ N ih =>
    rw [selectFirst, Circuit.size_comp, Circuit.size_append, Circuit.size_append,
      Circuit.size_wiring, Circuit.size_wiring, ih, size_muxCircuit]
    ring

/-! ### Sources, constants and oracle gates -/

/-- A source of one bit of a word: one of `K` input wires, or a constant. A word of sources
`ρ : Fin w → Source K` is a substitution, and reads the word `substitute ρ x` from the input `x`. -/
abbrev Source (K : ℕ) := Fin K ⊕ Bool

/-- The wire carrying a source after `constLayer`. -/
def Source.idx : Source K → Fin (K + 2)
  | .inl i => Fin.castAdd 2 i
  | .inr false => Fin.natAdd K (Fin.castAdd 1 (0 : Fin 1) : Fin (1 + 1))
  | .inr true => Fin.natAdd K (Fin.natAdd 1 (0 : Fin 1) : Fin (1 + 1))

/-- The inputs followed by the constants `false` and `true`. Two gates. -/
def constLayer (K : ℕ) : Circuit oracleSignature K (K + 2) :=
  (Circuit.id oracleSignature K).append
    ((Circuit.oneGate (σ := oracleSignature) (OracleOp.base (.const false)) Fin.elim0).append
      (Circuit.oneGate (σ := oracleSignature) (OracleOp.base (.const true)) Fin.elim0))

/-- After `constLayer`, the wire of a source carries the bit that the source reads. -/
@[simp] theorem eval_constLayer_idx (O : Language Bool) (x : BitString K) (s : Source K) :
    (constLayer K).eval (oracleInterpretation O) x s.idx = s.elim x id := by
  rcases s with i | _ | _
  · simp [constLayer, Source.idx, Circuit.eval_append, Fin.append_left]
  all_goals
    simp only [constLayer, Source.idx, Circuit.eval_append, Fin.append_right]
    rfl

@[simp] theorem size_constLayer (K : ℕ) : (constLayer K).size = 2 := by
  simp [constLayer]

@[simp] theorem cost_program_constLayer (K : ℕ) :
    (constLayer K).program.cost OracleOp.queryWeight = 0 := by
  rw [constLayer, Circuit.cost_program_append, Circuit.cost_program_append,
    Circuit.cost_program_oneGate, Circuit.cost_program_oneGate]
  rfl

@[simp] theorem depthWith_constLayer (K : ℕ) :
    (constLayer K).depthWith OracleOp.queryWeight = 0 :=
  Nat.eq_zero_of_le_zero <| (Circuit.depthWith_append_le _ _ _).trans <| max_le (by simp) <|
    (Circuit.depthWith_append_le _ _ _).trans <| max_le (by simp) (by simp)

theorem fanInAtMost_constLayer (K r : ℕ) : (constLayer K).FanInAtMost r :=
  (Circuit.fanInAtMost_wiring _ _).append <|
    ((Circuit.fanInAtMost_oneGate _ _ _).2 (Nat.zero_le _)).append
      ((Circuit.fanInAtMost_oneGate _ _ _).2 (Nat.zero_le _))

/-- `N` oracle gates side by side, on the output of `constLayer`: gate `i` asks about the word read
from the `q` sources `src i`. -/
def queryLayer (src : Fin N → Fin q → Source K) : Circuit oracleSignature (K + 2) N :=
  Circuit.pi fun i => Circuit.oneGate (σ := oracleSignature) (OracleOp.query q)
    fun a => (src i a).idx

@[simp] theorem eval_queryLayer (src : Fin N → Fin q → Source K) (O : Language Bool)
    (x : BitString K) (i : Fin N) :
    (queryLayer src).eval (oracleInterpretation O) ((constLayer K).eval (oracleInterpretation O) x)
        i = O.slice q (substitute (src i) x) := by
  simp only [queryLayer, Circuit.eval_pi, Circuit.eval_oneGate, eval_constLayer_idx,
    oracleInterpretation_query]
  rfl

@[simp] theorem size_queryLayer (src : Fin N → Fin q → Source K) : (queryLayer src).size = N := by
  simp [queryLayer]

@[simp] theorem cost_program_queryLayer (src : Fin N → Fin q → Source K) :
    (queryLayer src).program.cost OracleOp.queryWeight = N := by
  simp only [queryLayer, Circuit.cost_program_pi, Circuit.cost_program_oneGate,
    OracleOp.queryWeight_query, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    mul_one]

theorem depthWith_queryLayer_le (src : Fin N → Fin q → Source K) :
    (queryLayer src).depthWith OracleOp.queryWeight ≤ 1 :=
  Circuit.depthWith_pi_le _ _ fun _ => by simp

theorem fanInAtMost_queryLayer (src : Fin N → Fin q → Source K) : (queryLayer src).FanInAtMost q :=
  Circuit.fanInAtMost_pi fun _ => (Circuit.fanInAtMost_oneGate _ _ _).2 le_rfl

/-! ### One round -/

/-- **One selection round.** Candidate `i` is accepted when the oracle accepts the word read from
the sources `src i`. The round keeps its inputs and appends the word read from `word i` for the
first accepted candidate `i`, or the word read from `dflt` when none is accepted. -/
def selectionRound (src : Fin N → Fin q → Source K) (word : Fin N → Fin w → Source K)
    (dflt : Fin w → Source K) : Circuit oracleSignature K (K + w) :=
  (Circuit.id oracleSignature K).append
    (((selectFirst (K := K + 2 + N) (fun b => Fin.castAdd N (dflt b).idx)
        (fun i => Fin.natAdd (K + 2) i) (fun i b => Fin.castAdd N (word i b).idx)).mapOp
      toOracle).comp
      (((Circuit.id oracleSignature (K + 2)).append (queryLayer src)).comp (constLayer K)))

/-- The word that `selectionRound src word dflt` selects on the input `x` under the oracle `O`. -/
noncomputable def selectedWord (O : Language Bool) (src : Fin N → Fin q → Source K)
    (word : Fin N → Fin w → Source K) (dflt : Fin w → Source K) (x : BitString K) : BitString w :=
  firstSel (substitute dflt x) (fun i => O.slice q (substitute (src i) x))
    (fun i => substitute (word i) x)

/-- A round keeps its inputs and appends the selected word. -/
@[simp] theorem eval_selectionRound (src : Fin N → Fin q → Source K)
    (word : Fin N → Fin w → Source K) (dflt : Fin w → Source K) (O : Language Bool)
    (x : BitString K) :
    (selectionRound src word dflt).eval (oracleInterpretation O) x =
      Fin.append x (selectedWord O src word dflt x) := by
  rw [selectionRound, Circuit.eval_append, Circuit.eval_wiring, Circuit.eval_comp,
    Circuit.eval_comp, Circuit.eval_append, Circuit.eval_wiring,
    Circuit.eval_mapOp (I := interpretation), eval_selectFirst]
  simp only [selectedWord, Function.comp_def, Fin.append_left, Fin.append_right, id,
    eval_constLayer_idx, eval_queryLayer]
  rfl

/-- **The word a round selects.** Either the oracle accepts some candidate's query and the selected
word is that of the first such candidate, or it accepts none and the selected word is the
default. -/
theorem selectedWord_spec (O : Language Bool) (src : Fin N → Fin q → Source K)
    (word : Fin N → Fin w → Source K) (dflt : Fin w → Source K) (x : BitString K) :
    (∃ i, O.slice q (substitute (src i) x) = true ∧
        (∀ j < i, O.slice q (substitute (src j) x) = false) ∧
        selectedWord O src word dflt x = substitute (word i) x) ∨
      ((∀ i, O.slice q (substitute (src i) x) = false) ∧
        selectedWord O src word dflt x = substitute dflt x) :=
  firstSel_spec _ _ _

/-- A property of words that the default and every accepted candidate's word have holds for the
word a round selects. -/
theorem selectedWord_prop {P : BitString w → Prop} (O : Language Bool)
    (src : Fin N → Fin q → Source K) (word : Fin N → Fin w → Source K) (dflt : Fin w → Source K)
    (x : BitString K) (hd : P (substitute dflt x))
    (hacc : ∀ i, O.slice q (substitute (src i) x) = true → P (substitute (word i) x)) :
    P (selectedWord O src word dflt x) :=
  firstSel_prop hd hacc

/-- A round has `2` constant gates, `N` oracle gates and `N` multiplexers of width `w`. -/
@[simp] theorem size_selectionRound (src : Fin N → Fin q → Source K)
    (word : Fin N → Fin w → Source K) (dflt : Fin w → Source K) :
    (selectionRound src word dflt).size = 2 + N + N * (3 * w + 1) := by
  simp [selectionRound]

/-- A round has `N` oracle gates. -/
@[simp] theorem cost_program_selectionRound (src : Fin N → Fin q → Source K)
    (word : Fin N → Fin w → Source K) (dflt : Fin w → Source K) :
    (selectionRound src word dflt).program.cost OracleOp.queryWeight = N := by
  rw [selectionRound, Circuit.cost_program_append, Circuit.cost_program_comp,
    Circuit.cost_program_comp, Circuit.cost_program_append, cost_program_queryLayer,
    cost_program_constLayer, Circuit.cost_program_wiring, Circuit.cost_program_wiring]
  simp

/-- A round has at most one oracle gate on any path. -/
theorem depthWith_selectionRound_le (src : Fin N → Fin q → Source K)
    (word : Fin N → Fin w → Source K) (dflt : Fin w → Source K) :
    (selectionRound src word dflt).depthWith OracleOp.queryWeight ≤ 1 := by
  refine (Circuit.depthWith_append_le _ _ _).trans (max_le (by simp) ?_)
  refine (Circuit.depthWith_comp_le _ _ _).trans ?_
  rw [depthWith_mapOp_toOracle, Nat.zero_add]
  refine (Circuit.depthWith_comp_le _ _ _).trans ?_
  rw [depthWith_constLayer, Nat.add_zero]
  exact (Circuit.depthWith_append_le _ _ _).trans (max_le (by simp) (depthWith_queryLayer_le src))

/-- A round has fan-in at most `max q 2`. -/
theorem fanInAtMost_selectionRound (src : Fin N → Fin q → Source K)
    (word : Fin N → Fin w → Source K) (dflt : Fin w → Source K) :
    (selectionRound src word dflt).FanInAtMost (max q 2) :=
  (Circuit.fanInAtMost_wiring _ _).append <|
    ((Circuit.fanInAtMost_mapOp _ _).2
        ((Circuit.fanInAtMost_two _).mono (le_max_right _ _))).comp <|
      ((Circuit.fanInAtMost_wiring _ _).append
        ((fanInAtMost_queryLayer src).mono (le_max_left _ _))).comp (fanInAtMost_constLayer _ _)

end Cslib.Circuits.Boolean
