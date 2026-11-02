/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Machine
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Bound
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Windowed
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO
import Complexity.Computability.Machines.Turing.MultiTape.Universal.WindowedParts
import Complexity.Computability.Machines.Turing.MultiTape.Universal.WindowedInit
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.DivConq
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The universal function in time `O(t log t)`

The universal function (`Turing.MultiTapeTM.Universal.universal`), on a description `d`, an input
`x` and a number `t` of steps in binary, is computed by the windowed simulation
(`Turing.MultiTapeTM.Universal.Windowed.sim`, see
`Turing.MultiTapeTM.Universal.Windowed.universal_eq_sim`) run as a divide-and-conquer recursion
(`Turing.MultiTapeTM.ComputableInO.divConq`). A problem is the description, a number of steps in
unary and the windows. A problem of at most one step is solved by a windowed step; a larger one by
its first half on the cut windows, pasted back, and then its second half likewise.

Let `D` be the length of the encoded description and `M` the largest input symbol. The windows of a
problem of `n` steps, and those it computes, hold `O(n)` cells, each at most `D + M + 1`, and there
are at most `D + 1` of them (`Turing.MultiTapeTM.Universal.Windowed.WInv`). Cutting and pasting are
linear in the encoded windows for each window, so a problem of `n ≥ 2` steps costs
`O((D + M + 2) ^ 3 * (n + 1))` besides its halves, and a problem of at most one step
`O((D + M + 2) ^ 6)`. The recursion on `t` steps then costs
`O((D + M + 2) ^ 6 * (t + 1) * (log₂ (t + 1) + 1))`. The first problem is computed in time linear in
the encoded input plus `O((D + 1) ^ 3 + (t + 1) * (log₂ (t + 1) + 1))`.

The bound covers time and space alike; the space is not bounded separately here. It depends on the
largest input symbol `M` because the input cells hold the symbols in unary.

For a fixed machine on inputs over a fixed alphabet this is the `O(t log t)` simulation overhead of
[Arora and Barak, Theorem 1.9][AroraBarak09], attributed there to Hennie and Stearns, with an
additive term for reading the encoded input. It differs from that statement in several ways: the
number of steps is an input (a clocked simulation, not a run until the simulated machine halts);
the factor is an explicit polynomial in `D` and `M` rather than a constant depending on the
machine's alphabet, tapes and states; the space is not bounded by the simulated machine's space;
and the simulated model is the description format of `Turing.MultiTapeTM.Universal.Desc`, with a
read-only input and an emitted output. The construction is an original divide-and-conquer windowed
simulation, not the buffered tapes of Hennie and Stearns.

## Main results

* `Turing.MultiTapeTM.Universal.computableInO_universal_nlogn`: the universal function in time and
  space `O(N + (D + M + 2) ^ 6 * (t + 1) * (log₂ (t + 1) + 1))`, for the length `N` of the encoded
  input.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

namespace Turing.MultiTapeTM.Universal.Windowed

open ComputableTidilyInO

/-! ### The divide-and-conquer form of the windowed simulation -/

/-- The solution of a base problem: no step or one step. -/
def baseSol (a : Prob) : Sol :=
  if a.2.1 = 0 then (a.2.2, []) else ((wstep a.1 a.2.2).1, (wstep a.1 a.2.2).2.toList)

/-- The windowed simulation as a divide-and-conquer recursion. -/
def simDC : DivConq Prob Sol Saved where
  isBase a := decide (a.2.1 ≤ 1)
  base := baseSol
  left a := (a.1, firstHalf a.2.1, extract (firstHalf a.2.1) a.2.2)
  mid p := ((p.1.1, p.1.2.1 / 2, extract (p.1.2.1 / 2) (restore (firstHalf p.1.2.1) p.1.2.2 p.2.1)),
    (p.1.2.1 / 2, restore (firstHalf p.1.2.1) p.1.2.2 p.2.1, p.2.2))
  join q := (restore q.1.1 q.1.2.1 q.2.1, q.1.2.2 ++ q.2.2)

/-! ### The parts -/

section Parts

lemma prob_d : ComputableTidilyInO (fun a : Prob => a.1) eProb eDesc (fun a => (eProb a).length)
    (fun a => (eProb a).length) :=
  fst _ _

lemma prob_n : ComputableTidilyInO (fun a : Prob => a.2.1) eProb encUnary
    (fun a => (eProb a).length) (fun a => (eProb a).length) :=
  (snd eDesc (encPair encUnary eWin)).fst'

lemma prob_w : ComputableTidilyInO (fun a : Prob => a.2.2) eProb eWin
    (fun a => (eProb a).length) (fun a => (eProb a).length) :=
  (snd eDesc (encPair encUnary eWin)).snd'

lemma length_eProb (a : Prob) : (eProb a).length =
    2 * descLen a.1 + 1 + (2 * a.2.1 + 1 + (eWin a.2.2).length) := by
  change _ = 2 * (eDesc a.1).length + 1 + _
  simp only [length_encPair, encUnary_apply, List.length_replicate]

/-- The test for base problems, in linear time. -/
lemma isBase_inO : ComputableTidilyInO simDC.isBase eProb encBool (fun a => (eProb a).length)
    (fun a => (eProb a).length) :=
  (((ComputableTidilyInDegree.unary_isZero.comp ComputableTidilyInDegree.unary_pred).mono
    (d' := 1) (e' := 1)).inO_one.comp_linear prob_n).of_enc_eq fun a =>
    congrArg encBool (decide_eq_decide.mpr (by dsimp only; omega))

/-- `Option.toList` on symbols, in linear time. -/
lemma toList_inO : ComputableTidilyInO Option.toList eSym (encList encUnary)
    (fun o => (eSym o).length) (fun o => (eSym o).length) :=
  ((((ComputableTidilyInDegree.isSome encUnary).inO_one).ite
    ((ComputableTidilyInDegree.snoc encUnary).inO_one.comp_linear
      ((const []).prod (ComputableTidilyInDegree.getD (enc₁ := encUnary) 0).inO_one))
    (const [])).mono 4 (fun o => by dsimp only [eSym]; split_ifs <;> omega)
      (fun o => by dsimp only [eSym]; split_ifs <;> omega)).of_enc_eq
    fun o => by cases o <;> rfl

lemma length_dw_le (a : Prob) : (encPair eDesc eWin (a.1, a.2.2)).length ≤ (eProb a).length := by
  simp only [length_encPair]; omega

/-- The time and space of a base problem. -/
def Tb (a : Prob) : ℕ := ((eProb a).length + 1) ^ 3

/-- Base problems: no step, or one windowed step. -/
lemma base_inO : ComputableTidilyInO simDC.base eProb eSol Tb Tb := by
  have hstep := wstep_inO.tidy.comp (prob_d.prod prob_w)
  have hlive := hstep.fst'.prod (toList_inO.comp_linear hstep.snd')
  have hidle := prob_w.prod (const (encMid := encList encUnary) [])
  refine ((((ComputableTidilyInDegree.unary_isZero.inO_one.comp_linear prob_n).ite hidle
    hlive).mono 8 (fun a => ?_) (fun a => ?_)).of_enc_eq fun a => ?_)
  all_goals
    have h₁ := length_dw_le a
    have h₂ : (eProb a).length + 1 ≤ ((eProb a).length + 1) ^ 3 := Nat.le_self_pow (by omega) _
    have h₃ : ((encPair eDesc eWin (a.1, a.2.2)).length + 1) ^ 3 ≤ ((eProb a).length + 1) ^ 3 :=
      Nat.pow_le_pow_left (by omega) 3
    simp only [Function.comp_apply, Tb]
  · split_ifs <;> omega
  · split_ifs <;> omega
  · simp only [simDC, baseSol]
    split_ifs <;> simp_all

/-- The time and space of the first subproblem. -/
def Tl (a : Prob) : ℕ := (a.2.2.2.length + 1) * ((eProb a).length + 1)

/-- The first subproblem: the first half of the steps on the cut windows. -/
lemma left_inO : ComputableTidilyInO simDC.left eProb eProb Tl Tl := by
  have hfh := firstHalf_inO.tidy.comp_linear prob_n
  have hex := extract_inO.tidy.comp (hfh.prod prob_w)
  refine ((prob_d.prod (hfh.prod hex)).mono 8 (fun a => ?_) (fun a => ?_)).of_enc_eq
    fun a => rfl
  all_goals
    have h₁ : (encPair encUnary eWin (firstHalf a.2.1, a.2.2)).length ≤ (eProb a).length := by
      rw [length_eProb]; simp only [length_encPair, encUnary_apply, List.length_replicate,
        firstHalf]; omega
    have h₂ := Nat.mul_le_mul_left (a.2.2.2.length + 1) (Nat.add_le_add_right h₁ 1)
    have h₃ : (eProb a).length + 1 ≤ (a.2.2.2.length + 1) * ((eProb a).length + 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    simp only [Function.comp_apply, Tl] at *
    omega

lemma length_restore_tapes_le (r : ℕ) (o i : Win) : (restore r o i).2.length ≤ o.2.length := by
  simp only [restore, List.length_zipWith]; omega

/-- The time and space of the middle part: the windows after the first half are pasted back. -/
def Tm (p : Prob × Sol) : ℕ :=
  (p.1.2.2.2.length + 1) *
    ((encPair eProb eSol p).length + (eWin (restore (firstHalf p.1.2.1) p.1.2.2 p.2.1)).length + 1)

/-- The second subproblem and the saved data: the windows after the first half are pasted
back and cut again for the second half. -/
lemma mid_inO :
    ComputableTidilyInO simDC.mid (encPair eProb eSol) (encPair eProb eSaved) Tm Tm := by
  have hd := prob_d.comp_linear (fst eProb eSol)
  have hn := prob_n.comp_linear (fst eProb eSol)
  have hw := prob_w.comp_linear (fst eProb eSol)
  have hw1 := (fst eWin (encList encUnary)).comp_linear (snd eProb eSol)
  have ho1 := (snd eWin (encList encUnary)).comp_linear (snd eProb eSol)
  have hfh := firstHalf_inO.tidy.comp_linear hn
  have hres := restore_inO.tidy.comp (hfh.prod (hw.prod hw1))
  have hh := half_inO.tidy.comp_linear hn
  have hex := extract_inO.tidy.comp (hh.prod hres)
  refine (((hd.prod (hh.prod hex)).prod (hh.prod (hres.prod ho1))).mono 16 (fun p => ?_)
    (fun p => ?_)).of_enc_eq fun p => rfl
  all_goals
    obtain ⟨⟨d, n, w⟩, w₁', o₁⟩ := p
    have h₁ : (encPair encUnary (encPair eWin eWin) (firstHalf n, w, w₁')).length ≤
        (encPair eProb eSol ((d, n, w), w₁', o₁)).length := by
      simp only [length_encPair, encUnary_apply, List.length_replicate, firstHalf]; omega
    have h₂ : (encPair encUnary eWin (n / 2, restore (firstHalf n) w w₁')).length ≤
        (encPair eProb eSol ((d, n, w), w₁', o₁)).length +
          (eWin (restore (firstHalf n) w w₁')).length := by
      simp only [length_encPair, encUnary_apply, List.length_replicate]; omega
    have h₃ := length_restore_tapes_le (firstHalf n) w w₁'
    have h₄ := Nat.mul_le_mul (Nat.add_le_add_right h₃ 1) (Nat.add_le_add_right h₂ 1)
    have h₅ := Nat.mul_le_mul_left (w.2.length + 1) (Nat.add_le_add_right h₁ 1)
    have h₆ : (encPair eProb eSol ((d, n, w), w₁', o₁)).length +
        (eWin (restore (firstHalf n) w w₁')).length + 1 ≤ Tm ((d, n, w), w₁', o₁) :=
      Nat.le_mul_of_pos_left _ (by omega)
    have h₇ : (w.2.length + 1) * ((encPair eProb eSol ((d, n, w), w₁', o₁)).length + 1) ≤
        Tm ((d, n, w), w₁', o₁) := Nat.mul_le_mul_left _ (by omega)
    have h₈ : ((restore (firstHalf n) w w₁').2.length + 1) *
        ((encPair encUnary eWin (n / 2, restore (firstHalf n) w w₁')).length + 1) ≤
        Tm ((d, n, w), w₁', o₁) := by
      unfold Tm; exact h₄
    simp only [Function.comp_apply] at *
    omega

/-- The time and space of the combination. -/
def Tj (q : Saved × Sol) : ℕ := (q.1.2.1.2.length + 1) * ((encPair eSaved eSol q).length + 1)

/-- The combination: the windows after the second half are pasted back and the emitted symbols
concatenated. -/
lemma join_inO : ComputableTidilyInO simDC.join (encPair eSaved eSol) eSol Tj Tj := by
  have hr := (fst encUnary (encPair eWin (encList encUnary))).comp_linear (fst eSaved eSol)
  have hs := (snd encUnary (encPair eWin (encList encUnary))).comp_linear (fst eSaved eSol)
  have hw2 := (fst eWin (encList encUnary)).comp_linear (snd eSaved eSol)
  have ho2 := (snd eWin (encList encUnary)).comp_linear (snd eSaved eSol)
  have hres := restore_inO.tidy.comp (hr.prod (hs.fst'.prod hw2))
  have happ := (ComputableTidilyInDegree.listAppend encUnary).inO_one.comp_linear
    (hs.snd'.prod ho2)
  refine ((hres.prod happ).mono 8 (fun q => ?_) (fun q => ?_)).of_enc_eq fun q => rfl
  all_goals
    obtain ⟨⟨r, w₁, o₁⟩, w₂', o₂⟩ := q
    have h₁ : (encPair encUnary (encPair eWin eWin) (r, w₁, w₂')).length ≤
        (encPair eSaved eSol ((r, w₁, o₁), w₂', o₂)).length := by
      simp only [length_encPair, encUnary_apply, List.length_replicate]; omega
    have h₂ := Nat.mul_le_mul_left (w₁.2.length + 1) (Nat.add_le_add_right h₁ 1)
    have h₃ : (encPair eSaved eSol ((r, w₁, o₁), w₂', o₂)).length + 1 ≤
        Tj ((r, w₁, o₁), w₂', o₂) := Nat.le_mul_of_pos_left _ (by omega)
    simp only [Function.comp_apply, Tj] at *
    omega

end Parts

/-! ### The cost recurrence -/

section Cost

/-- The cost of a base problem charged by `Turing.MultiTapeTM.ComputableInO.divConq`. -/
def baseCost (a : Prob) : ℕ :=
  (eProb a).length + (eProb a).length + Tb a + Tb a + (eProb a).length +
    (eSol (simDC.base a)).length + 1

/-- The cost of a node charged by `Turing.MultiTapeTM.ComputableInO.divConq`. -/
def nodeCost (a : Prob) (b₁ b₂ : Sol) : ℕ :=
  (eProb a).length + (eProb a).length + Tl a + Tl a + Tm (a, b₁) + Tm (a, b₁) +
    Tj ((simDC.mid (a, b₁)).2, b₂) + Tj ((simDC.mid (a, b₁)).2, b₂) +
    (eProb a).length + (eProb (simDC.left a)).length + (eSol b₁).length +
    (eProb (simDC.mid (a, b₁)).1).length + (eSaved (simDC.mid (a, b₁)).2).length +
    (eSol b₂).length + (eSol (simDC.join ((simDC.mid (a, b₁)).2, b₂))).length + 1

/-- The factor of the cost of the simulation, for a description of length `D` and cells at most
`B`. -/
def costA (D B : ℕ) : ℕ := 10000000 * (D + B + 2) ^ 6

lemma winBound_node (D B n : ℕ) :
    winBound D B 1 (4 * n + 1) + 1 ≤ 65 * ((D + 1) * (B + 1) * (n + 1)) ∧
      D + n + n * (2 * D + 1) ≤ winBound D B 1 (4 * n + 1) := by
  unfold winBound
  constructor
  · nlinarith [Nat.zero_le (D * B * n), Nat.zero_le (D * B), Nat.zero_le (D * n),
      Nat.zero_le (B * n)]
  · nlinarith [Nat.zero_le (D * B * n), Nat.zero_le (D * B), Nat.zero_le (D * n),
      Nat.zero_le (B * n)]

lemma winBound_base (D B : ℕ) : winBound D B 1 5 ≤ 76 * ((D + 1) * (B + 1)) := by
  unfold winBound
  nlinarith [Nat.zero_le (D * B)]

lemma le_sq_X (D B : ℕ) : (D + 1) * (B + 1) ≤ (D + B + 2) ^ 2 := by
  nlinarith

lemma simDC_base_eq {d : Desc} {n : ℕ} (hn : n ≤ 1) (w : Win) :
    simDC.base (d, n, w) = sim d n w := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl
  · simp [simDC, baseSol, sim]
  · simp [simDC, baseSol, sim]

/-- The cost of a base problem, within `costA`. -/
lemma baseCost_le {d : Desc} {B n : ℕ} {w : Win} (hDB : descLen d ≤ B) (hn : n ≤ 1)
    (hw : WInv (descLen d) B 0 (2 * n + 1) w) : baseCost (d, n, w) ≤ costA (descLen d) B := by
  have hZ := winBound_base (descLen d) B
  have hX := le_sq_X (descLen d) B
  have hw' := length_eWin_le (hw.mono (h' := 1) (L' := 5) (by omega) (by omega))
  have hs := length_eWin_le ((hw.sim hDB n).mono (h' := 1) (L' := 5) (by omega) (by omega))
  have ho := length_encList_sim_out_le d n w
  have hn' : n * (2 * descLen d + 1) ≤ 2 * descLen d + 1 :=
    (Nat.mul_le_mul_right _ hn).trans (by rw [Nat.one_mul])
  have hX2 : (descLen d + B + 2) ^ 2 ≤ (descLen d + B + 2) ^ 6 :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hE := length_eProb (d, n, w)
  have hS : (eSol (sim d n w)).length =
      2 * (eWin (sim d n w).1).length + 1 + (encList encUnary (sim d n w).2).length :=
    length_encPair ..
  unfold baseCost costA Tb
  rw [simDC_base_eq hn]
  have h83 : (83 * (descLen d + B + 2) ^ 2) ^ 3 = 571787 * (descLen d + B + 2) ^ 6 := by ring
  simp only [descLen] at *
  generalize (eProb (d, n, w)).length = E at *
  have hY : E + 1 ≤ 83 * ((eDesc d).length + B + 2) ^ 2 := by
    nlinarith
  have hY3 := Nat.pow_le_pow_left hY 3
  have hY1 : E + 1 ≤ (E + 1) ^ 3 := Nat.le_self_pow (by omega) _
  omega

/-- The cost of a node of `n` steps, within `costA * (n + 1)`. -/
lemma nodeCost_le {d : Desc} {B n : ℕ} {w : Win} (hDB : descLen d ≤ B)
    (hw : WInv (descLen d) B 0 (2 * n + 1) w) :
    nodeCost (d, n, w) (sim d (firstHalf n) (extract (firstHalf n) w))
      (sim d (n / 2) (extract (n / 2)
        (restore (firstHalf n) w (sim d (firstHalf n) (extract (firstHalf n) w)).1))) ≤
      costA (descLen d) B * (n + 1) := by
  have hfh : firstHalf n + n / 2 = n := by unfold firstHalf; omega
  set b₁ := sim d (firstHalf n) (extract (firstHalf n) w) with hb₁
  set w₁ := restore (firstHalf n) w b₁.1 with hw₁
  set b₂ := sim d (n / 2) (extract (n / 2) w₁) with hb₂
  -- the bounds on the windows
  have iL := (hw.extract (firstHalf n)).mono (h' := 0) (L' := 2 * firstHalf n + 1) le_rfl
    (min_le_right _ _)
  have ib₁ : WInv (descLen d) B 1 (2 * firstHalf n + 1 + 2 * firstHalf n) b₁.1 :=
    iL.sim hDB (firstHalf n)
  have iw₁ : WInv (descLen d) B 0 (2 * n + 1 + 2 * firstHalf n) w₁ :=
    hw.restore_sim hDB (firstHalf n) (firstHalf n)
  have iM := (iw₁.extract (n / 2)).mono (h' := 0) (L' := 2 * (n / 2) + 1) le_rfl
    (min_le_right _ _)
  have ib₂ : WInv (descLen d) B 1 (2 * (n / 2) + 1 + 2 * (n / 2)) b₂.1 := iM.sim hDB (n / 2)
  have iJ : WInv (descLen d) B 0 (2 * n + 1 + 2 * firstHalf n + 2 * (n / 2))
      (restore (n / 2) w₁ b₂.1) := iw₁.restore_sim hDB (n / 2) (n / 2)
  -- their sizes
  obtain ⟨hZ, hZ'⟩ := winBound_node (descLen d) B n
  have sw := length_eWin_le (hw.mono (h' := 1) (L' := 4 * n + 1) (by omega) (by omega))
  have sL := length_eWin_le (iL.mono (h' := 1) (L' := 4 * n + 1) (by omega) (by omega))
  have sb₁ := length_eWin_le (ib₁.mono (h' := 1) (L' := 4 * n + 1) (by omega) (by omega))
  have sw₁ := length_eWin_le (iw₁.mono (h' := 1) (L' := 4 * n + 1) (by omega) (by omega))
  have sM := length_eWin_le (iM.mono (h' := 1) (L' := 4 * n + 1) (by omega) (by omega))
  have sb₂ := length_eWin_le (ib₂.mono (h' := 1) (L' := 4 * n + 1) (by omega) (by omega))
  have sJ := length_eWin_le (iJ.mono (h' := 1) (L' := 4 * n + 1) (by omega) (by omega))
  have o₁ : (encList encUnary b₁.2).length ≤ firstHalf n * (2 * descLen d + 1) :=
    length_encList_sim_out_le d (firstHalf n) (extract (firstHalf n) w)
  have o₂ : (encList encUnary b₂.2).length ≤ n / 2 * (2 * descLen d + 1) :=
    length_encList_sim_out_le d (n / 2) (extract (n / 2) w₁)
  have o₁' := Nat.mul_le_mul_right (2 * descLen d + 1) (show firstHalf n ≤ n by omega)
  have o₂' := Nat.mul_le_mul_right (2 * descLen d + 1) (show n / 2 ≤ n by omega)
  have o₁₂ : firstHalf n * (2 * descLen d + 1) + n / 2 * (2 * descLen d + 1) =
      n * (2 * descLen d + 1) := by rw [← Nat.add_mul, hfh]
  generalize winBound (descLen d) B 1 (4 * n + 1) = Z at *
  -- the sizes of the values
  have hA : (eProb (d, n, w)).length ≤ 5 * Z + 2 := by rw [length_eProb]; dsimp only; omega
  have hLp : (eProb (simDC.left (d, n, w))).length ≤ 5 * Z + 2 := by
    change (eProb (d, firstHalf n, extract (firstHalf n) w)).length ≤ _
    rw [length_eProb]; dsimp only; unfold firstHalf at sL ⊢; omega
  have hB₁ : (eSol b₁).length ≤ 3 * Z + 1 := by
    rw [length_encPair (enc₁ := eWin) (enc₂ := encList encUnary)]; omega
  have hMp : (eProb (simDC.mid ((d, n, w), b₁)).1).length ≤ 5 * Z + 2 := by
    change (eProb (d, n / 2, extract (n / 2) w₁)).length ≤ _
    rw [length_eProb]; dsimp only; omega
  have hS : (eSaved (simDC.mid ((d, n, w), b₁)).2).length ≤ 4 * Z + 2 := by
    change (eSaved (n / 2, w₁, b₁.2)).length ≤ _
    rw [length_encPair (enc₁ := encUnary) (enc₂ := encPair eWin (encList encUnary)),
      length_encPair (enc₁ := eWin) (enc₂ := encList encUnary)]
    simp only [encUnary_apply, List.length_replicate]
    omega
  have hB₂ : (eSol b₂).length ≤ 3 * Z + 1 := by
    rw [length_encPair (enc₁ := eWin) (enc₂ := encList encUnary)]; omega
  have hJs : (eSol (simDC.join ((simDC.mid ((d, n, w), b₁)).2, b₂))).length ≤ 3 * Z + 1 := by
    change (eSol (restore (n / 2) w₁ b₂.1, b₁.2 ++ b₂.2)).length ≤ _
    rw [length_encPair (enc₁ := eWin) (enc₂ := encList encUnary)]
    simp only [encList_append, List.length_append]
    omega
  -- the products
  have hk := hw.tapes
  have hk₁ := iw₁.tapes
  have hP : ∀ {k m c : ℕ}, k ≤ descLen d + 1 → m ≤ c * (Z + 1) →
      (k + 1) * m ≤ c * ((descLen d + 2) * (Z + 1)) := fun hk hm =>
    (Nat.mul_le_mul (Nat.add_le_add_right hk 1) hm).trans (le_of_eq (by ring))
  have hTl : Tl (d, n, w) ≤ 5 * ((descLen d + 2) * (Z + 1)) := hP hk (by omega)
  have hTm : Tm ((d, n, w), b₁) ≤ 14 * ((descLen d + 2) * (Z + 1)) := by
    refine hP (m := (encPair eProb eSol ((d, n, w), b₁)).length + (eWin w₁).length + 1) hk ?_
    rw [length_encPair (enc₁ := eProb) (enc₂ := eSol)]; dsimp only; omega
  have hTj : Tj ((simDC.mid ((d, n, w), b₁)).2, b₂) ≤ 11 * ((descLen d + 2) * (Z + 1)) := by
    refine hP (k := w₁.2.length)
      (m := (encPair eSaved eSol ((simDC.mid ((d, n, w), b₁)).2, b₂)).length + 1) hk₁ ?_
    rw [length_encPair (enc₁ := eSaved) (enc₂ := eSol)]; dsimp only; omega
  have hZP : Z + 1 ≤ (descLen d + 2) * (Z + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have hX3 : (descLen d + 2) * ((descLen d + 1) * (B + 1)) ≤ (descLen d + B + 2) ^ 6 :=
    calc _ ≤ (descLen d + B + 2) * ((descLen d + B + 2) * (descLen d + B + 2)) :=
          Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) (by omega))
      _ = (descLen d + B + 2) ^ 3 := by ring
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  have hfin : 100 * ((descLen d + 2) * (Z + 1)) ≤ costA (descLen d) B * (n + 1) :=
    calc 100 * ((descLen d + 2) * (Z + 1))
        ≤ 100 * ((descLen d + 2) * (65 * ((descLen d + 1) * (B + 1) * (n + 1)))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hZ)
      _ = 6500 * ((descLen d + 2) * ((descLen d + 1) * (B + 1)) * (n + 1)) := by ring
      _ ≤ 6500 * ((descLen d + B + 2) ^ 6 * (n + 1)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hX3)
      _ ≤ costA (descLen d) B * (n + 1) := by
          unfold costA
          rw [Nat.mul_assoc]
          exact Nat.mul_le_mul_right _ (by norm_num)
  unfold nodeCost
  omega

lemma eval_base {d : Desc} {B n : ℕ} {w : Win} (hDB : descLen d ≤ B) (hn : n ≤ 1)
    (hw : WInv (descLen d) B 0 (2 * n + 1) w) :
    ∃ c, simDC.Eval baseCost nodeCost (d, n, w) (sim d n w) c ∧ c ≤ costA (descLen d) B := by
  refine ⟨baseCost (d, n, w), ?_, baseCost_le hDB hn hw⟩
  rw [← simDC_base_eq hn]
  exact .base (by simp only [simDC, decide_eq_true_eq]; exact hn)

/-- **The cost recurrence**: on `n ≤ 2 ^ k` steps, the windowed simulation costs at most
`2 ^ (k + 1) * (k + 1) * costA D B`. -/
lemma eval_le (d : Desc) {B : ℕ} (hDB : descLen d ≤ B) (k : ℕ) :
    ∀ n w, n ≤ 2 ^ k → WInv (descLen d) B 0 (2 * n + 1) w →
      ∃ c, simDC.Eval baseCost nodeCost (d, n, w) (sim d n w) c ∧
        c ≤ 2 ^ (k + 1) * (k + 1) * costA (descLen d) B := by
  induction k with
  | zero =>
    intro n w hn hw
    obtain ⟨c, hc, hle⟩ := eval_base hDB (by simpa using hn) hw
    exact ⟨c, hc, by simp only [zero_add, pow_one, Nat.mul_one]; omega⟩
  | succ k ih =>
    intro n w hn hw
    have hA : costA (descLen d) B ≤ 2 ^ (k + 1 + 1) * (k + 1 + 1) * costA (descLen d) B :=
      Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.pow_pos (by omega)) (by omega))
    by_cases hn1 : n ≤ 1
    · obtain ⟨c, hc, hle⟩ := eval_base hDB hn1 hw
      exact ⟨c, hc, hle.trans hA⟩
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    have iL := (hw.extract (firstHalf n)).mono (h' := 0) (L' := 2 * firstHalf n + 1) le_rfl
      (min_le_right _ _)
    obtain ⟨c₁, h₁, hc₁⟩ := ih (firstHalf n) _ (by unfold firstHalf; omega) iL
    have iw₁ := hw.restore_sim hDB (firstHalf n) (firstHalf n)
    have iM := (iw₁.extract (n / 2)).mono (h' := 0) (L' := 2 * (n / 2) + 1) le_rfl
      (min_le_right _ _)
    obtain ⟨c₂, h₂, hc₂⟩ := ih (n / 2) _ (by omega) iM
    have hnode := DivConq.Eval.node (D := simDC) (a := (d, n, w))
      (by simp only [simDC, decide_eq_false_iff_not]; omega) h₁ h₂
    have hcost := nodeCost_le hDB hw
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [show simDC.join ((simDC.mid ((d, m + 2, w), sim d (firstHalf (m + 2))
        (extract (firstHalf (m + 2)) w))).2, sim d ((m + 2) / 2) (extract ((m + 2) / 2)
          (restore (firstHalf (m + 2)) w (sim d (firstHalf (m + 2))
            (extract (firstHalf (m + 2)) w)).1))) = sim d (m + 2) w by
      rw [sim_add_two]; rfl] at hnode
    refine ⟨_, hnode, ?_⟩
    · have h2 : m + 2 + 1 ≤ 2 * 2 ^ (k + 1) := by omega
      calc c₁ + c₂ + nodeCost (d, m + 2, w) _ _
          ≤ 2 ^ (k + 1) * (k + 1) * costA (descLen d) B +
              2 ^ (k + 1) * (k + 1) * costA (descLen d) B +
              costA (descLen d) B * (m + 2 + 1) := by omega
        _ ≤ 2 ^ (k + 1) * (k + 1) * costA (descLen d) B +
              2 ^ (k + 1) * (k + 1) * costA (descLen d) B +
              costA (descLen d) B * (2 * 2 ^ (k + 1)) := by gcongr
        _ = 2 ^ (k + 1 + 1) * (k + 1 + 1) * costA (descLen d) B := by ring

end Cost

end Turing.MultiTapeTM.Universal.Windowed

namespace Turing.MultiTapeTM.Universal

open Windowed ComputableTidilyInO

/-- The output of the universal function from the result of the windowed simulation. -/
lemma post_inO : ComputableTidilyInO (fun s : Sol => (s.2, s.1.1.isNone)) eSol eOut
    (fun s => (eSol s).length) (fun s => (eSol s).length) := by
  have hst := (fst eSym (encList eTape)).comp_linear (fst eWin (encList encUnary))
  have hnone := (ComputableTidilyInDegree.of_finite (encIn := encBool) (encMid := encBool)
    (fun b : Bool => !b)).inO_one.comp_linear
      ((ComputableTidilyInDegree.isSome encUnary).inO_one.comp_linear hst)
  exact (((snd eWin (encList encUnary)).prod hnone).mono 2 (fun s => by dsimp only [eSol]; omega)
    (fun s => by dsimp only [eSol]; omega)).of_enc_eq fun ⟨⟨st, ts⟩, o⟩ => by cases st <;> rfl

lemma length_encNat_le_log (t : ℕ) : (encNat t).length ≤ Nat.log 2 (t + 1) + 1 := by
  have h := Nat.le_log_of_pow_le (b := 2) (by norm_num)
    (show 2 ^ (encNat t).length ≤ (t + 1) * 2 by
      have := two_pow_length_encNat_le t; omega)
  rwa [Nat.log_mul_base (by norm_num) (by omega)] at h

lemma two_pow_log_le (t : ℕ) : 2 ^ Nat.log 2 t ≤ t + 1 := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp
  · exact (Nat.pow_log_le_self 2 (by omega)).trans (by omega)

/-- **The universal function in time `O(t log t)`.** For a description `d` of encoded length `D`,
an input `x` with largest symbol `M` and `t` steps given in binary, the universal function is
computable in time and space `O(N + (D + M + 2) ^ 6 * (t + 1) * (log₂ (t + 1) + 1))`, where `N` is
the length of the encoded input `(d, x, t)`. -/
public theorem computableInO_universal_nlogn :
    ComputableInO universal eIn eOut
      (fun i => (eIn i).length +
        (descLen i.1 + listMax id i.2.1 + 2) ^ 6 * ((i.2.2 + 1) * (Nat.log 2 (i.2.2 + 1) + 1)))
      (fun i => (eIn i).length +
        (descLen i.1 + listMax id i.2.1 + 2) ^ 6 *
          ((i.2.2 + 1) * (Nat.log 2 (i.2.2 + 1) + 1))) := by
  have hev : ∀ i : Desc × List ℕ × ℕ, ∃ c, simDC.Eval baseCost nodeCost
      (i.1, i.2.2, extract i.2.2 (initWin i.1 i.2.1))
      (sim i.1 i.2.2 (extract i.2.2 (initWin i.1 i.2.1))) c ∧
      c ≤ 2 ^ (Nat.log 2 i.2.2 + 1 + 1) * (Nat.log 2 i.2.2 + 1 + 1) *
        costA (descLen i.1) (descLen i.1 + listMax id i.2.1 + 1) := fun i =>
    eval_le i.1 (by omega) (Nat.log 2 i.2.2 + 1) i.2.2 _
      (Nat.lt_pow_succ_log_self (by norm_num) _).le
      (((winv_initWin i.1 i.2.1).extract i.2.2).mono le_rfl (min_le_right _ _))
  choose C hC using hev
  have hdc := ComputableInO.divConq simDC initProb_inO isBase_inO.computableInO
    base_inO.computableInO left_inO.computableInO mid_inO.computableInO join_inO.computableInO
    (cb := baseCost) (cn := nodeCost) (fun _ _ => le_rfl) (fun _ _ _ _ => le_rfl)
    (fun i => (hC i).1)
  refine (((post_inO.comp_linear hdc.tidy).of_enc_eq (g := universal) fun ⟨d, x, t⟩ => by
    rw [universal_eq_sim]; rfl).computableInO.mono 6000000000 (fun i => ?_) (fun i => ?_))
  all_goals
    obtain ⟨d, x, t⟩ := i
    have hY : descLen d + 1 ≤ descLen d + listMax id x + 2 := by omega
    have hY6 : 1 ≤ (descLen d + listMax id x + 2) ^ 6 := Nat.one_le_pow _ _ (by omega)
    have hD3 : (descLen d + 1) ^ 3 ≤ (descLen d + listMax id x + 2) ^ 6 :=
      (Nat.pow_le_pow_left hY 3).trans (Nat.pow_le_pow_right (by omega) (by omega))
    have hQ1 : 1 ≤ (t + 1) * (Nat.log 2 (t + 1) + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hQ : (t + 1) * ((encNat t).length + 1) ≤ 2 * ((t + 1) * (Nat.log 2 (t + 1) + 1)) := by
      have := length_encNat_le_log t
      calc (t + 1) * ((encNat t).length + 1) ≤ (t + 1) * (2 * (Nat.log 2 (t + 1) + 1)) :=
            Nat.mul_le_mul_left _ (by omega)
        _ = _ := by ring
    have hlog : Nat.log 2 t ≤ Nat.log 2 (t + 1) := Nat.log_mono_right (by omega)
    have hC1 : 2 ^ (Nat.log 2 t + 1 + 1) * (Nat.log 2 t + 1 + 1) ≤
        8 * ((t + 1) * (Nat.log 2 (t + 1) + 1)) :=
      calc 2 ^ (Nat.log 2 t + 1 + 1) * (Nat.log 2 t + 1 + 1)
          ≤ (4 * (t + 1)) * (2 * (Nat.log 2 (t + 1) + 1)) := by
            refine Nat.mul_le_mul ?_ (by omega)
            have := two_pow_log_le t
            rw [pow_succ, pow_succ]; omega
        _ = _ := by ring
    have hC2 : costA (descLen d) (descLen d + listMax id x + 1) ≤
        640000000 * (descLen d + listMax id x + 2) ^ 6 := by
      unfold costA
      calc 10000000 * (descLen d + (descLen d + listMax id x + 1) + 2) ^ 6
          ≤ 10000000 * (2 * (descLen d + listMax id x + 2)) ^ 6 :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 6)
        _ = _ := by ring
    have hC3 := (hC (d, x, t)).2
    have hC4 : C (d, x, t) ≤ 5120000000 * ((descLen d + listMax id x + 2) ^ 6 *
        ((t + 1) * (Nat.log 2 (t + 1) + 1))) :=
      calc C (d, x, t) ≤ 8 * ((t + 1) * (Nat.log 2 (t + 1) + 1)) *
            (640000000 * (descLen d + listMax id x + 2) ^ 6) :=
            hC3.trans (Nat.mul_le_mul hC1 hC2)
        _ = _ := by ring
    have hP1 := Nat.le_mul_of_pos_right ((descLen d + listMax id x + 2) ^ 6) hQ1
    have hP2 := Nat.le_mul_of_pos_left ((t + 1) * (Nat.log 2 (t + 1) + 1)) hY6
    dsimp only at *
    omega

end Turing.MultiTapeTM.Universal
