/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Universal.WindowedParts
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.WindowedInit
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.DivConq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The universal function in time `O(t log t)`

TODO docstring
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
  show _ = 2 * (eDesc a.1).length + 1 + _
  simp only [length_encPair, encUnary_apply, List.length_replicate]

lemma isBase_inO : ComputableTidilyInO simDC.isBase eProb encBool (fun a => (eProb a).length)
    (fun a => (eProb a).length) :=
  (((ComputableTidilyInDegree.unary_isZero.comp ComputableTidilyInDegree.unary_pred).mono
    (d' := 1) (e' := 1)).inO_one.comp_linear prob_n).of_enc_eq fun a =>
    congrArg encBool (decide_eq_decide.mpr (by dsimp only; omega))

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

lemma mid_inO : ComputableTidilyInO simDC.mid (encPair eProb eSol) (encPair eProb eSaved) Tm Tm := by
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
    show (eProb (d, firstHalf n, extract (firstHalf n) w)).length ≤ _
    rw [length_eProb]; dsimp only; unfold firstHalf at sL ⊢; omega
  have hB₁ : (eSol b₁).length ≤ 3 * Z + 1 := by
    rw [length_encPair (enc₁ := eWin) (enc₂ := encList encUnary)]; omega
  have hMp : (eProb (simDC.mid ((d, n, w), b₁)).1).length ≤ 5 * Z + 2 := by
    show (eProb (d, n / 2, extract (n / 2) w₁)).length ≤ _
    rw [length_eProb]; dsimp only; omega
  have hS : (eSaved (simDC.mid ((d, n, w), b₁)).2).length ≤ 4 * Z + 2 := by
    show (eSaved (n / 2, w₁, b₁.2)).length ≤ _
    rw [length_encPair (enc₁ := encUnary) (enc₂ := encPair eWin (encList encUnary)),
      length_encPair (enc₁ := eWin) (enc₂ := encList encUnary)]
    simp only [encUnary_apply, List.length_replicate]
    omega
  have hB₂ : (eSol b₂).length ≤ 3 * Z + 1 := by
    rw [length_encPair (enc₁ := eWin) (enc₂ := encList encUnary)]; omega
  have hJs : (eSol (simDC.join ((simDC.mid ((d, n, w), b₁)).2, b₂))).length ≤ 3 * Z + 1 := by
    show (eSol (restore (n / 2) w₁ b₂.1, b₁.2 ++ b₂.2)).length ≤ _
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

end Cost

end Turing.MultiTapeTM.Universal.Windowed
