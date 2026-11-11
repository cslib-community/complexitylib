import CslibFrontier.Crypto.Computational.LWE.SearchToDecision

/-! Tests for `CslibFrontier.Crypto.Computational.LWE.SearchToDecision`. -/

namespace CslibFrontierTests.Crypto.LWESearchToDecision

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.PrimeLWE

/-- Two estimators per coordinate plus the uniform one, two trials each, one row per block. -/
example : searchSamples 1 2 2 1 = 6 := rfl

example : trueCount ![true, false, true] = 2 := by decide

/-- Re-randomizing `[b | a] = [1 | 2]` over `ZMod 3` by `s' = 1` gives `[1 + 2 | 2] = [0 | 2]`. -/
example :
    rerandomizeSecret (n := 1) (m := 1) (q := 3) (fun _ => ![1, 2]) (fun _ => 1) =
      fun _ => ![0, 2] := by
  funext i c
  fin_cases i
  fin_cases c <;> decide

/-- Trials where the correct guess `0` always accepts and every other estimator never does. -/
def perfectTrials (o : Option (Fin 1 × ZMod 2)) (_ : Fin 4) : Bool :=
  if o = some (0, 0) then true else false

/-- With real acceptance `1` and uniform acceptance `0`, exact counts recover the secret. -/
example : guessSecret perfectTrials = fun _ => 0 := by
  have hcount (o : Option (Fin 1 × ZMod 2)) :
      trueCount (perfectTrials o) = if o = some (0, 0) then 4 else 0 := by
    by_cases h : o = some (0, 0) <;> simp [perfectTrials, trueCount, h]
  refine guessSecret_eq_of_close perfectTrials _ (pR := 1) (pU := 0) ?_ ?_
  · rw [hcount]
    norm_num
  · intro j g
    rw [hcount]
    obtain rfl : j = 0 := Subsingleton.elim _ _
    by_cases hg : g = 0
    · subst hg
      norm_num
    · have hg' : (0, g) ≠ ((0 : Fin 1), (0 : ZMod 2)) := fun h => hg (Prod.ext_iff.mp h).2
      simp only [Option.some.injEq, hg', hg, ite_false]
      norm_num

/-- The concrete reduction specializes to any adversary and repetition count. -/
example (adversary : List Bool → ProbComp Bool) (N : ℕ) :
    1 - (1 * 2 + 1) * (2 * Real.exp (-(N * (Game.advantage
        (distinguishingGame (realEnsemble (fun _ => 1) (fun _ => 3) (fun _ => 2)
          (fun _ => PMF.uniformOfFintype (ZMod 2)) 0) adversary)
        (distinguishingGame (uniformEnsemble (fun _ => 1) (fun _ => 3) (fun _ => 2) 0)
          adversary) : ℝ) ^ 2) / 8)) ≤
      Game.succProbability (searchGame 1 (searchSamples 1 2 N 3) 2
        (PMF.uniformOfFintype (ZMod 2))
        (reduceSearchToDecision (n := 1) (m := 3) (q := 2) N adversary)) := by
  exact_mod_cast searchToDecision adversary N

/--
info: 'Cslib.Crypto.PrimeLWE.searchToDecision' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms searchToDecision

/--
info: 'Cslib.Crypto.PrimeLWE.pi_estimatorLaw_guessSecret_ne_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms pi_estimatorLaw_guessSecret_ne_le

end CslibFrontierTests.Crypto.LWESearchToDecision
