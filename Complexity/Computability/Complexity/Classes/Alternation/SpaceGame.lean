/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Alternation.Space
public import Complexity.Computability.Machines.Turing.MultiTape.Alternating.WordGame
import Complexity.Computability.Circuit.Boolean.Tableau.ValueGame
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.StreamFold
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NatPow
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelOnWords
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimePrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Run
import Mathlib.Data.Set.Finite.List
import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation

/-!
# Word games in `APSPACE`, and `APSPACE = EXP`

A word game (`Turing.MultiTapeATM.WordGame`) whose initial position `I a` and update `U` are
polynomial-space computable, whose reachable positions have polynomial length, and whose plays all
end, is decided in alternating polynomial space: the alternating machine
`Turing.MultiTapeATM.wordGame` keeps only the current position on a work tape, and each round
recomputes the next position within polynomial space
[Chandra, Kozen and Stockmeyer, Section 3][ChandraKozenStockmeyer1981]
[Sipser, Section 10.3][Sipser2013]. The update need only be computed on the reachable positions,
through an encoding of typed positions (`Cslib.Complexity.mem_APSPACE_of_wins_polySpace`); with a
polynomial-time update on all words this is `Cslib.Complexity.mem_APSPACE_of_wins`.

The plays may be exponentially long: only their finiteness is assumed, since deciding asks every
branch to halt. This is the step from deterministic exponential time to `APSPACE`. A problem in
`EXP` is decided by a machine within `T = 2 ^ p n` steps, so by the output wire of its tableau
circuit (`Cslib.Circuits.Boolean.Tableau.evalOutput_gates`). The circuit-value game on that
tableau (`Cslib.Circuits.Boolean.Tableau.ValueGame`) has claims of polynomial length and an update
within linear space in the claim, so `EXP ⊆ APSPACE` (`Cslib.Complexity.EXP_subset_APSPACE`).
Together with `Cslib.Complexity.APSPACE_subset_EXP` this gives `APSPACE = EXP`
(`Cslib.Complexity.APSPACE_eq_EXP`).

## Main results

* `Cslib.Complexity.mem_APSPACE_of_wins_polySpace`: a word game on polynomially long positions
  with a polynomial-space initial position and update is in `APSPACE`.
* `Cslib.Complexity.mem_APSPACE_of_wins`: the same with a polynomial-time initial position and
  update.
* `Cslib.Complexity.EXP_subset_APSPACE`: `EXP ⊆ APSPACE`.
* `Cslib.Complexity.APSPACE_eq_EXP`: `APSPACE = EXP`.

## References

* [A. K. Chandra, D. C. Kozen, L. J. Stockmeyer, *Alternation*][ChandraKozenStockmeyer1981]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeATM

/-- A polynomial-space certificate gives one tidy machine within a monotone polynomial space bound
and some time. -/
private theorem tidy_of_polySpace {α β : Type} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    {f : α → β} (h : ComputableInPolySpace f encIn encOut) :
    ∃ (c d : ℕ) (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State)
      (t : α → ℕ), ∀ a, tm.ComputesTidilyInTimeAndSpace (encIn a) (encOut (f a)) (t a)
        (c * ((encIn a).length + 1) ^ d) := by
  obtain ⟨t, s, hs, hc, -⟩ := h
  obtain ⟨c₀, k, State, hfin, tm, htm⟩ := hc.exists_computableTidilyInTimeAndSpace
  have hp : PolynomiallyBounded fun n => c₀ * (s n + 1) := by fun_prop
  obtain ⟨c, d, hcd⟩ := polynomiallyBounded_iff_le.mp hp
  exact ⟨c, d, k, State, hfin, tm, _, fun a => (htm a).mono le_rfl (hcd _)⟩

variable {α : Type} {enc : α ↪ List Bool}

/-- **Word games with a polynomial-space update are in `APSPACE`.** Let the initial position `I a`
be polynomial-space computable, and let the update `U` be computed by a polynomial-space computable
`F`, through some encoding `encPos` of typed positions, on every word `u :: b :: r` such that
`u :: x :: r` is reachable from `I a` for some `x` (and `b` is any move). Let every position
reachable from `I a` have length at most `ℓ a`, polynomial in the instance, and let every play from
`I a` end. Then the problem of whether the existential player wins from `I a` is in `APSPACE`. -/
theorem mem_APSPACE_of_wins_polySpace {π : Type} {encPos : π ↪ List Bool} {A : Set α}
    {I : α → List Bool} {U : List Bool → List Bool} {F : π → List Bool} {ℓ : α → ℕ}
    (hI : ComputableInPolySpace I enc encBits)
    (hF : ComputableInPolySpace F encPos encBits)
    (hℓ : PolyBounded (fun a => (enc a).length) ℓ)
    (hpos : ∀ a u x r b, WordGame.Reach U (I a) (u :: x :: r) →
      ∃ p, encPos p = u :: b :: r ∧ F p = U (u :: b :: r))
    (hlen : ∀ a w, WordGame.Reach U (I a) w → w.length ≤ ℓ a)
    (hends : ∀ a, ∃ n, WordGame.Ends U n (I a))
    (hA : ∀ a, a ∈ A ↔ WordGame.Wins U (I a)) : A ∈ APSPACE enc := by
  classical
  obtain ⟨cI, dI, kI, SI, _, TI, tI, hTI⟩ := tidy_of_polySpace hI
  obtain ⟨cU, dU, kU, SU, _, TU, tU, hTU⟩ := tidy_of_polySpace hF
  -- the tapes: the position on `N`, the next position on `O`, a flag on `M`
  set K := kI + kU + 3 with hK
  let N : Fin K := ⟨0, by omega⟩
  let O : Fin K := ⟨1, by omega⟩
  let M : Fin K := ⟨2, by omega⟩
  have hNO : N ≠ O := by simp [N, O]
  have hNM : N ≠ M := by simp [N, M]
  have hOM : O ≠ M := by simp [O, M]
  obtain ⟨eI, heI⟩ := exists_embedding_eq (show kI + 1 ≤ K by omega) (Fin.last kI) N
  obtain ⟨eU, heUi, heUo⟩ := exists_embedding_eq₂ (show kU + 1 + 2 ≤ K by omega)
    (i := Fin.natAdd (kU + 1) 0) (o := (Fin.last kU).castAdd 2) (by simp [Fin.ext_iff]) hNO
  -- the machines
  let Pm := TI.outputToWord.extendTapes eI
  let R := frozenRound (nop K Bool) ((TU.onWords true).extendTapes eU) N O M hNO hNM hOM
  -- the round from a position, within some time
  let sR : α → ℕ := fun a => cU * (ℓ a + 1) ^ dU + 10 * ℓ a + 5 * K + 3 * kU + 40
  have hround (p : π) : ∃ t, TransformsTapes R
      (fun _ ws => ws = Function.update (fun _ => []) N (encPos p))
      (fun _ _ ws' em => ws' = Function.update (fun _ => []) N (F p) ∧ em = []) t
      (cU * ((encPos p).length + 1) ^ dU + 3 * (encPos p).length + 7 * (F p).length + 5 * K +
        3 * kU + 40) := by
    have hE := (transformsTapes_nop K Bool).imp
      (P' := fun _ ws => ws = Function.update (fun _ => []) N (encPos p))
      (Q' := fun _ ws ws' em => ws' = ws ∧ em = []) (fun _ _ _ => trivial)
      (fun _ _ _ _ _ h => h) le_rfl le_rfl
    have hNm := (hTU p).onWords_extendTapes true heUi heUo
    simp only [encBits_apply] at hNm
    exact ⟨_, (transformsTapes_frozenRound hNO hNM hOM hE hNm).mono le_rfl (by omega)⟩
  choose tp htp using hround
  -- a common time bound for the rounds of an instance, over the finitely many short words
  let tRw : List Bool → ℕ := fun w => if h : ∃ p, encPos p = w then tp h.choose else 0
  let tR : α → ℕ := fun a => (List.finite_length_le Bool (ℓ a)).toFinset.sup tRw
  have htR (a : α) (p : π) (hp : (encPos p).length ≤ ℓ a) : tp p ≤ tR a := by
    have hmem : encPos p ∈ (List.finite_length_le Bool (ℓ a)).toFinset := by simpa using hp
    have h1 : tRw (encPos p) = tp p := by
      have hex : ∃ q, encPos q = encPos p := ⟨p, rfl⟩
      simp only [tRw, hex, ↓reduceDIte]
      exact congrArg tp (encPos.injective hex.choose_spec)
    exact h1 ▸ Finset.le_sup (f := tRw) hmem
  -- the specifications
  let tP : α → ℕ := fun a => tI a + (I a).length + 2
  let sP : α → ℕ := fun a =>
    cI * ((enc a).length + 1) ^ dI + 2 * (I a).length + kI + 4 + (K - (kI + 1))
  have hP (a : α) : WordGame.PrepSpec Pm N (enc a) (I a) (tP a) (sP a) := by
    obtain ⟨ws, em, hrun, ⟨rfl, rfl⟩, hsp⟩ := transformsTapes_iff_runFrom.mp
      ((hTI a).outputToWord_onTape heI) (enc a) (fun _ => []) [] ⟨rfl, rfl⟩
    unfold WordGame.PrepSpec
    rw [Cfg.init_eq_wordsCfg]
    exact ⟨hrun, hsp⟩
  have hR (a : α) : WordGame.RoundSpec R N (enc a) U (I a) (tR a) (sR a) := by
    intro u x r hreach b
    obtain ⟨p, hp, hFp⟩ := hpos a u x r b hreach
    have hw : (u :: b :: r).length ≤ ℓ a := by simpa using hlen a _ hreach
    have hUw : (U (u :: b :: r)).length ≤ ℓ a := hlen a _ (WordGame.Reach.move b hreach)
    rw [← hFp] at hUw ⊢
    rw [← hp] at hw ⊢
    have hpow : cU * ((encPos p).length + 1) ^ dU ≤ cU * (ℓ a + 1) ^ dU := by gcongr
    have h := (htp p).mono (t' := tR a) (s' := sR a) (htR a p hw) (by simp only [sR]; omega)
    obtain ⟨ws, em, hrun, ⟨rfl, rfl⟩, hsp⟩ := transformsTapes_iff_runFrom.mp h (enc a) _ [] rfl
    exact ⟨hrun, hsp⟩
  have hspec (a : α) := wordGame_spec (hP a) (hR a)
  refine ⟨K, _, inferInstance, wordGame Pm R N,
    fun a => K * (2 * max (max (sP a) (sR a)) 1 + 1), ?_, ⟨fun a => ⟨(hspec a).1, ?_⟩, fun a => ?_⟩⟩
  · have hlenI : PolyBounded (fun a => (enc a).length) fun a => (I a).length := by
      simpa using hI.polyBounded_length
    have hpowI : PolyBounded (fun a => (enc a).length) fun a => cI * ((enc a).length + 1) ^ dI :=
      PolyBounded.of_forall_le cI dI fun _ => le_rfl
    have hpowU : PolyBounded (fun a => (enc a).length) fun a => cU * (ℓ a + 1) ^ dU :=
      (PolyBounded.of_forall_le (size := id) cU dU fun _ => le_rfl).comp hℓ
    have hsP : PolyBounded (fun a => (enc a).length) sP := by growth_poly
    have hsR : PolyBounded (fun a => (enc a).length) sR := by growth_poly
    refine ((PolyBounded.const K).mul (((PolyBounded.const 2).mul
      ((hsP.add hsR).add (.const 1))).add (.const 1))).mono fun a => ?_
    exact Nat.mul_le_mul_left _ (by omega)
  · rw [hA a, (hspec a).2.1]
  · obtain ⟨n, hn⟩ := hends a
    exact ⟨_, (hspec a).2.2 n hn⟩

/-- **Word games on polynomially long positions are in `APSPACE`.** Let the initial position `I a`
and the update `U` be polynomial-time computable, every position reachable from `I a` have length
at most `ℓ a`, polynomial in the instance, and every play from `I a` end. Then the problem of
whether the existential player wins from `I a` is in `APSPACE`. -/
theorem mem_APSPACE_of_wins {A : Set α} {I : α → List Bool} {U : List Bool → List Bool}
    {ℓ : α → ℕ} (hI : ComputableInPolyTime I enc encBits)
    (hU : ComputableInPolyTime U encBits encBits)
    (hℓ : PolyBounded (fun a => (enc a).length) ℓ)
    (hlen : ∀ a w, WordGame.Reach U (I a) w → w.length ≤ ℓ a)
    (hends : ∀ a, ∃ n, WordGame.Ends U n (I a))
    (hA : ∀ a, a ∈ A ↔ WordGame.Wins U (I a)) : A ∈ APSPACE enc :=
  mem_APSPACE_of_wins_polySpace (encPos := encBits) (.of_polyTime hI) (.of_polyTime hU) hℓ
    (fun _ u _ r b _ => ⟨u :: b :: r, rfl, rfl⟩) hlen hends hA

/-! ### `EXP ⊆ APSPACE` -/

section EXP

open Circuits Circuits.Boolean Circuits.Boolean.Tableau Circuits.Boolean.Tableau.ValueGame
open ComputableInSpace

/-- The time bound `c₁ * 2 ^ m + c₂` is at most `2 ^ (m + c₁ + c₂ + n)`. -/
private theorem two_pow_bound (c₁ c₂ m n : ℕ) :
    c₁ * 2 ^ m + c₂ ≤ 2 ^ (m + c₁ + c₂ + n) := by
  have h₁ : c₁ < 2 ^ c₁ := Nat.lt_two_pow_self
  have h₂ : c₂ < 2 ^ c₂ := Nat.lt_two_pow_self
  have hX : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hR : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  rw [pow_add, pow_add, pow_add]
  have hPQ : 2 ^ c₁ + 2 ^ c₂ ≤ 2 ^ c₁ * 2 ^ c₂ + 1 := by nlinarith
  nlinarith [Nat.mul_le_mul_left (2 ^ m * 2 ^ c₁ * 2 ^ c₂) hR]

/-- **`EXP ⊆ APSPACE`**: the circuit-value game on the tableau of an exponential-time decider is
played in alternating polynomial space. -/
theorem EXP_subset_APSPACE : EXP enc ⊆ APSPACE enc := by
  intro A hA
  obtain ⟨d, c₁, c₂, s, k, State, hfin, tm, htm⟩ := mem_EXP_iff.mp hA
  have := Fintype.ofFinite State
  classical
  set n : α → ℕ := fun a => (enc a).length
  set E : α → ℕ := fun a => n a ^ d + c₁ + c₂ + n a
  set T : α → ℕ := fun a => 2 ^ E a
  set N : α → ℕ := fun a => outWire k State (n a) (T a)
  set M : α → ℕ := fun a => n a + numGates k State (T a)
  set Bs : α → ℕ := fun a => n a + E a
  have hin : (fun a => (enc a).length) ≼ Bs := .of_le fun a => by simp [Bs, n]
  have hx : ComputableInSpace (fun a => enc a) enc (encList encBool) Bs :=
    ((budget_comp_linear (of_inO ComputableInDegree.bitsToList.inO_one)
      ((of_inO ComputableInDegree.id'.inO_one).of_enc_eq
        (encB := encBits) (g := fun a => enc a) fun _ => rfl)).weaken hin)
  have hn : ComputableInSpace n enc encNat Bs := budget_length hx
  have hE : ComputableInSpace E enc encNat Bs :=
    budget_natAdd (budget_natAdd (budget_natAdd (budget_natPow hn hin d) (budget_const c₁ hin))
      (budget_const c₂ hin)) hn
  have hT : ComputableInSpace T enc encNat Bs := by
    refine budget_natPow_variable (budget_const 2 hin) hE (.of_le_linear 3 3 fun a => ?_)
    have h2 : (encNat 2).length = 2 := rfl
    have hEl : (encNat (E a)).length ≤ E a :=
      length_encNat_le_of_lt_two_pow Nat.lt_two_pow_self
    simp only [h2, Bs]
    nlinarith
  have hN : ComputableInSpace N enc encNat Bs :=
    budget_natAdd (budget_natAdd (budget_natAdd hn (budget_const 2 hin))
      (budget_natMul hT (blockSize_inSpace (k := k) (State := State) hT hin)))
      (budget_natAdd (gfStart_inSpace (k := k) (State := State) hT hin) (budget_const _ hin))
  have hM : ComputableInSpace M enc encNat Bs :=
    budget_natAdd hn (budget_natAdd (budget_const 2 hin)
      (budget_natMul (budget_natAdd hT (budget_const 1 hin))
        (blockSize_inSpace (k := k) (State := State) hT hin)))
  have hBs : PolyBounded (fun a => (enc a).length) Bs := by growth_poly
  have hJ := budget_prod hx (budget_prod hT
    (budget_prod hN (budget_const (encB := encBool) true hin)))
  have hJM := budget_prod hx (budget_prod hT
    (budget_prod hM (budget_const (encB := encBool) true hin)))
  have hI := ComputableInPolySpace.of_inSpace hBs
    (budget_comp_linear (position_inSpace tm) hJ)
  have hℓ := (ComputableInPolySpace.of_inSpace hBs hJM).polyBounded_length.add
    (PolyBounded.const 2)
  have hNM (a : α) : N a < M a := outWire_lt (k := k) (State := State) _ _
  refine mem_APSPACE_of_wins_polySpace (π := Pos) (encPos := encPos) (F := step tm)
    (U := update tm encClaim) hI ((ComputableInPolySpace.of_inSpace
      (PolyBounded.self) (step_inSpace tm))) hℓ ?_ ?_ ?_ ?_
  · intro a u x r b hr
    obtain ⟨w', v, -, he⟩ := reach_position (tm := tm) encClaim (hNM a) hr
    obtain ⟨-, rfl⟩ := position_eq_cons he.symm
    exact ⟨pos u b (enc a, T a, w', v), encPos_pos _ _ _, by rw [step_pos, update_position_cons]⟩
  · intro a w hr
    obtain ⟨w', v, hw', rfl⟩ := reach_position (tm := tm) encClaim (hNM a) hr
    refine (length_position_le _).trans ?_
    simp only [encPair_apply, Nat.add_le_add_iff_right]
    exact length_encClaim_mono hw'.le
  · exact fun a => ⟨N a, ends_position (tm := tm) encClaim (enc a) (T a) (N a) (hNM a) true⟩
  · intro a
    rw [wins_position_iff (enc a) (T a) (N a) (hNM a) true]
    have hnT : (enc a).length < 2 * T a := by
      have : n a < 2 ^ n a := Nat.lt_two_pow_self
      have : 2 ^ n a ≤ T a := Nat.pow_le_pow_right (by norm_num) (by simp only [E]; omega)
      simp only [n] at *
      omega
    have hval : val tm (T a) (enc a) (N a) =
        decide (OutView.ofList (tm.runFrom (tm.initCfg (enc a)) (T a)).output = .one true) :=
      evalOutput_gates tm hnT
    have hle : c₁ * 2 ^ (enc a).length ^ d + c₂ ≤ T a := two_pow_bound _ _ _ _
    obtain ⟨-, hout⟩ := (htm a).runFrom_of_le hle
    rw [hval, hout]
    by_cases h : a ∈ A <;> simp [h, indicator, OutView.ofList]

end EXP

/-- **`APSPACE = EXP`** [Chandra, Kozen and Stockmeyer, Section 3][ChandraKozenStockmeyer1981]
[Sipser, Section 10.3][Sipser2013]: alternating polynomial space is deterministic exponential
time. -/
theorem APSPACE_eq_EXP : APSPACE enc = EXP enc :=
  le_antisymm APSPACE_subset_EXP EXP_subset_APSPACE

end Cslib.Complexity
