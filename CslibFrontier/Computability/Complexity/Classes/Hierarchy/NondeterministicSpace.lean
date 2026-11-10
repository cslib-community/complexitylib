/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Constructible
public import CslibFrontier.Computability.Complexity.Classes.Hierarchy.TinyDesc
public import CslibFrontier.Computability.Complexity.Classes.LogSpace
public import CslibFrontier.Computability.Complexity.Classes.Space
public import CslibFrontier.Computability.Complexity.Classes.Space.Nondeterministic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.NondeterministicBudget
import CslibFrontier.Computability.Complexity.Classes.Constructible.Space
import CslibFrontier.Computability.Complexity.Classes.Hierarchy.Space
import CslibFrontier.Computability.Complexity.Classes.LogSpace.Complement
import CslibFrontier.Computability.Complexity.Classes.LogSpace.Savitch
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OPrimitives
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The nondeterministic space hierarchy theorem

`Cslib.Complexity.nspaceDiagonal G` is the set of words `x` of length `n` on which the description
cut from the start of `x` (`Cslib.Complexity.Diagonal.tinyCut`) does not accept `x`, under the
coding `Turing.MultiTapeTM.Universal.eBit` of bits, within the budget of `G n` bits for its encoded
configurations (`Turing.MultiTapeTM.Universal.BAccepts`). Acceptance within a budget is
reachability between configurations of bounded size, so the diagonal needs no clock.

A machine within `S` work-tape cells accepts exactly when its description accepts within the
size bound `Turing.MultiTapeTM.Universal.cfgSpaceBound` of its configurations
(`Turing.MultiTapeTM.Universal.accepts_iff_bAccepts_descN`). Let a nondeterministic machine
recognize the diagonal within space `c₁ * f n + c₂`, where every `c * f n + c` is eventually below
`G n`, and let `4 * log₂ n ≤ G n`. That size bound is `O(f n + log n)`, with a factor linear in the
description, so it is eventually below `G n`. On its own description, padded to a doubly
exponential length where it is tiny (`Cslib.Complexity.Diagonal.tinyDesc`), the machine accepts
exactly when the diagonal rejects (`Cslib.Complexity.nspaceDiagonal_notMem_NSPACE`). This is the
diagonal argument of [Sipser, Theorem 9.3][Sipser2013] for nondeterministic machines.

Conversely, the universal recognizer within a budget
(`Turing.MultiTapeTM.Universal.exists_recognizesInSpace_bAccepts`) guesses a run of the decoded
description, reading the input in place, and so recognizes the complement of the diagonal within
space `O(G n + log n)` for a space-constructible `G`. By the Immerman–Szelepcsényi theorem
[Immerman1988] [Szelepcsenyi1987] the diagonal itself is then in `NSPACE G` when `log₂ n ≤ G n`
(`Cslib.Complexity.nspaceDiagonal_mem_NSPACE`). Hence the nondeterministic space hierarchy:

* `NSPACE f ⊂ NSPACE g` for a space-constructible `g` with `log₂ n ≤ g n`, when every
  `c * f n + c` is eventually below `g n` (`Cslib.Complexity.NSPACE_ssubset_NSPACE`);
* `NL ⊂ NSPACE (log₂ n ^ 2)` (`Cslib.Complexity.NL_ssubset_NSPACE_log2_sq`), and more generally
  `NSPACE (log₂ n ^ (k + 1)) ⊂ NSPACE (log₂ n ^ (k + 2))`
  (`Cslib.Complexity.NSPACE_log2_pow_ssubset_NSPACE_log2_pow_succ`);
* `NSPACE (n ^ k) ⊂ NSPACE (n ^ (k + 1))` (`Cslib.Complexity.NSPACE_pow_ssubset_NSPACE_pow_succ`).
* `NL ⊂ PSPACE` (`Cslib.Complexity.NL_ssubset_PSPACE`), from Savitch's `NL ⊆ DSPACE (log₂ n ^ 2)`
  and the deterministic hierarchy.

The gap `f = o(g)` and the lower bound `log n ≤ g n` are those of the deterministic theorem
(`Cslib.Complexity.DSPACE_ssubset_DSPACE`).

## Main definitions

* `Cslib.Complexity.nspaceDiagonal`: the nondeterministic diagonal within a space budget.

## Main results

* `Turing.MultiTapeTM.Universal.accepts_iff_bAccepts_descN`: a machine within `S` cells accepts
  exactly when its description accepts within any budget above the size of its configurations.
* `Cslib.Complexity.not_recognizesInSpace_nspaceDiagonal`: no nondeterministic machine recognizes
  the diagonal within space `O(f)`.
* `Cslib.Complexity.nspaceDiagonal_notMem_NSPACE`, `Cslib.Complexity.nspaceDiagonal_mem_NSPACE`:
  the diagonal within space `G` is not in `NSPACE f` for `f = o(G)`, and is in `NSPACE G`.
* `Cslib.Complexity.NSPACE_ssubset_NSPACE`: the nondeterministic space hierarchy theorem.
* `Cslib.Complexity.NL_ssubset_NSPACE_log2_sq`,
  `Cslib.Complexity.NSPACE_log2_pow_ssubset_NSPACE_log2_pow_succ`,
  `Cslib.Complexity.NSPACE_pow_ssubset_NSPACE_pow_succ`, `Cslib.Complexity.NL_ssubset_PSPACE`: its
  corollaries.

## References

* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
* [N. Immerman, *Nondeterministic Space Is Closed under Complementation*][Immerman1988]
* [R. Szelepcsényi, *The Method of Forcing for Nondeterministic Automata*][Szelepcsenyi1987]
-/

public section

namespace Turing.MultiTapeTM.Universal

/-- **A machine within `S` cells accepts exactly when its description accepts within a budget**
`b` above the size bound `Turing.MultiTapeTM.Universal.cfgSpaceBound` of its configurations. -/
theorem accepts_iff_bAccepts_descN {k : ℕ} {State : Type} [Finite State] (eS : State ↪ ℕ)
    (ntm : MultiTapeNTM k Bool State) {input : List Bool} {S b : ℕ}
    (hS : ntm.RunsInSpace input S)
    (hb : cfgSpaceBound (descLen (descN eS eBit ntm)) input.length k S ≤ b) :
    ntm.Accepts input ↔ BAccepts (descN eS eBit ntm) (input.map eBit) b := by
  refine ⟨fun h => BAccepts.mono ((accepts_iff_reflTransGen_nStep_fits eS ntm input hS).mp h) hb,
    fun h => ?_⟩
  obtain ⟨s, hs, hr⟩ := h.exists_reflTransGen_nStep
  exact (accepts_iff_reflTransGen_nStep eS ntm input).mpr ⟨s, hs, hr⟩

end Turing.MultiTapeTM.Universal

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.Universal Filter

/-- **The nondeterministic diagonal within space `G`.** The words `x` of length `n` on which the
description cut from the start of `x` (`Cslib.Complexity.Diagonal.tinyCut`) does not accept `x`,
under the coding `Turing.MultiTapeTM.Universal.eBit` of bits, within the budget of `G n` bits for
its encoded configurations (`Turing.MultiTapeTM.Universal.BAccepts`). -/
@[expose] def nspaceDiagonal (G : ℕ → ℕ) : Set (List Bool) :=
  {x | ¬ BAccepts (decodeDesc (Diagonal.tinyCut x)) (x.map eBit) (G x.length)}

open Diagonal in
/-- **The nondeterministic diagonal argument for space.** If every `c * f n + c` is eventually below
`G n` and `4 * log₂ n ≤ G n`, no nondeterministic machine recognizes the diagonal within space
`c₁ * f n + c₂`. The configurations of its description take `O(f n + log n)` bits, eventually within
the budget `G n`; so on its own description, padded to a tiny one beyond that point, it accepts
exactly when the diagonal rejects. -/
theorem not_recognizesInSpace_nspaceDiagonal {f G : ℕ → ℕ} (hlog : ∀ n, 4 * Nat.log2 n ≤ G n)
    (hfG : ∀ c, ∀ᶠ n in atTop, c * f n + c ≤ G n) {k : ℕ} {State : Type} [Finite State]
    (ntm : MultiTapeNTM k Bool State) (c₁ c₂ : ℕ) :
    ¬ ntm.RecognizesInSpace encBits (nspaceDiagonal G) fun x => c₁ * f x.length + c₂ := by
  intro hA
  have := Fintype.ofFinite State
  let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
  set D := descLen (descN eS eBit ntm)
  set P := 6 * (2 * D + 5) * (c₁ + c₂) + 3 * D + 8 with hP
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hfG (2 * P))
  -- the description, padded beyond `N` and to a length where it is tiny
  suffices ∀ pad : List Bool,
      N + 2 ^ 2 ^ (eDesc (descN eS eBit ntm)).length ≤ pad.length → False
    from this (List.replicate _ false) (List.length_replicate ..).ge
  intro pad hpad
  have hpow := Nat.one_le_two_pow (n := 2 ^ (eDesc (descN eS eBit ntm)).length)
  have hlen : (frame (eDesc (descN eS eBit ntm)) ++ pad).length =
      2 * (eDesc (descN eS eBit ntm)).length + 1 + pad.length := by
    rw [List.length_append, length_frame]
  have hdec : decodeDesc (tinyCut (frame (eDesc (descN eS eBit ntm)) ++ pad)) =
      descN eS eBit ntm := by
    rw [tinyCut_of_tinyDesc (tinyDesc_frame_append (by omega)), decodeDesc_unframe_frame_append]
  generalize frame (eDesc (descN eS eBit ntm)) ++ pad = x at hlen hdec
  have h₁ := hN x.length (by omega)
  have hl := hlog x.length
  obtain ⟨hrun, hmem⟩ := hA x
  simp only [encBits_apply] at hrun hmem
  set s := c₁ * f x.length + c₂ with hs
  have hsf : s ≤ (c₁ + c₂) * (f x.length + 1) := by rw [hs]; nlinarith
  -- the configurations of the description fit within the budget
  have hbudget : cfgSpaceBound D x.length k s ≤ G x.length := by
    have hk : k ≤ D := by simpa using tapes_le (descN eS eBit ntm)
    have hn : (encNat (x.length + 1)).length ≤ Nat.log2 x.length + 2 :=
      length_encNat_le_log2_add_two le_rfl
    have hP' : 6 * (2 * D + 5) * s + 3 * D + 8 ≤ P * (f x.length + 1) := by
      have := Nat.mul_le_mul_left (6 * (2 * D + 5)) hsf
      have e₁ : P * (f x.length + 1) = 6 * (2 * D + 5) * ((c₁ + c₂) * (f x.length + 1)) +
          (3 * D + 8) * (f x.length + 1) := by rw [hP]; ring
      have : 3 * D + 8 ≤ (3 * D + 8) * (f x.length + 1) := Nat.le_mul_of_pos_right _ (by omega)
      omega
    have e₂ : 2 * P * f x.length + 2 * P = 2 * (P * (f x.length + 1)) := by ring
    have e₃ : 3 * (2 * D + 5) * 2 * s = 6 * (2 * D + 5) * s := by ring
    simp only [cfgSpaceBound]
    omega
  -- so the machine accepts its padded description exactly when the diagonal rejects it
  rw [nspaceDiagonal, Set.mem_ofPred_eq, hdec,
    accepts_iff_bAccepts_descN eS ntm hrun hbudget] at hmem
  exact iff_not_self hmem.symm

/-- **The nondeterministic diagonal within space `G` is not in `NSPACE f`** when every
`c * f n + c` is eventually below `G n` and `4 * log₂ n ≤ G n`: a decider within space `O(f)`
recognizes the diagonal within that space (`Cslib.Complexity.not_recognizesInSpace_nspaceDiagonal`).
-/
theorem nspaceDiagonal_notMem_NSPACE {f G : ℕ → ℕ} (hlog : ∀ n, 4 * Nat.log2 n ≤ G n)
    (hfG : ∀ c, ∀ᶠ n in atTop, c * f n + c ≤ G n) : nspaceDiagonal G ∉ NSPACE encBits f := by
  rintro ⟨k, State, _, ntm, c₁, c₂, hA⟩
  exact not_recognizesInSpace_nspaceDiagonal hlog hfG ntm c₁ c₂ hA.recognizesInSpace

open Diagonal in
/-- **The nondeterministic diagonal within space `G` is in `NSPACE G`**, for a space-constructible
`G` with `log₂ n ≤ G n`. The universal recognizer within a budget
(`Turing.MultiTapeTM.Universal.exists_recognizesInSpace_bAccepts`) recognizes its complement within
space `O(G n + log n)`: the tiny description is decoded in logarithmic space and the budget `G n`
written in unary within space `O(G n)`. By the Immerman–Szelepcsényi theorem the complement of a
problem so recognized is decided within the same space
(`Cslib.Complexity.compl_mem_NSPACE_of_recognizesInSpace`). -/
theorem nspaceDiagonal_mem_NSPACE {G : ℕ → ℕ} (hG : SpaceConstructible G)
    (hlog : ∀ n, Nat.log2 n ≤ G n) : nspaceDiagonal G ∈ NSPACE encBits G := by
  -- the description, in logarithmic space, with an encoding of logarithmic length
  obtain ⟨tD, cD, hD⟩ := computableInLogSpace_decodeDesc_tinyCut
  obtain ⟨cL, hL⟩ := exists_length_eDesc_decodeDesc_tinyCut_le
  have hD' : ComputableInSpace (fun x => decodeDesc (tinyCut x)) encBits eDesc
      fun x => G x.length + Nat.log2 x.length + 1 :=
    ⟨tD, cD + cL, hD.mono (fun _ => le_rfl) fun x => by
      simp only [encBits_apply]; nlinarith, fun x => (hL x).trans (by nlinarith)⟩
  -- the budget `G n` in unary, within space `O(G n)`
  obtain ⟨TG, hGb⟩ := hG.computableInO
  have hB : ComputableInSpace (fun x : List Bool => G x.length) encBits encUnary
      fun x => G x.length + Nat.log2 x.length + 1 :=
    (ComputableInSpace.of_inO (ComputableInO.natToUnary.comp hGb)).weaken
      (.of_le_linear 2 0 fun x => by omega)
  obtain ⟨k, State, _, ntm, c, hrec⟩ := exists_recognizesInSpace_bAccepts encBits
    (fun x => decodeDesc (tinyCut x)) (fun x => G x.length) _ hD' hB fun x => by
      simp only [encBits_apply]; omega
  exact compl_mem_NSPACE_of_recognizesInSpace hlog (c₁ := 2 * c) (c₂ := c)
    (hrec.mono fun x => by
      simp only [encBits_apply]
      have := Nat.mul_le_mul_left c (hlog x.length)
      nlinarith)

/-! ### The nondeterministic space hierarchy theorem -/

/-- **The nondeterministic space hierarchy theorem.** If `g` is space-constructible,
`log₂ n ≤ g n`, and every `c * f n + c` is eventually below `g n`, then `NSPACE f` is strictly
contained in `NSPACE g`. The nondeterministic diagonal within space `4 * g` separates the classes:
it is in `NSPACE g` by the Immerman–Szelepcsényi theorem
(`Cslib.Complexity.nspaceDiagonal_mem_NSPACE`), and not in `NSPACE f` by the diagonal argument
(`Cslib.Complexity.nspaceDiagonal_notMem_NSPACE`). -/
theorem NSPACE_ssubset_NSPACE {f g : ℕ → ℕ} (hg : SpaceConstructible g)
    (hlog : ∀ n, Nat.log2 n ≤ g n) (hfg : ∀ c, ∀ᶠ n in atTop, c * f n + c ≤ g n) :
    NSPACE encBits f ⊂ NSPACE encBits g := by
  have hsub : NSPACE encBits f ⊆ NSPACE encBits g := NSPACE_mono_of_eventually_le <| by
    filter_upwards [hfg 1] with n h
    omega
  refine (Set.ssubset_iff_of_subset hsub).mpr ⟨_, NSPACE_subset_of_le_mul_add 4 0
    (fun n => (Nat.add_zero _).ge) (nspaceDiagonal_mem_NSPACE (hg.const_mul 4)
      fun n => (hlog n).trans (Nat.le_mul_of_pos_left _ (by norm_num))),
    nspaceDiagonal_notMem_NSPACE (fun n => Nat.mul_le_mul_left 4 (hlog n)) fun c => ?_⟩
  filter_upwards [hfg c] with n h
  omega

/-- **Nondeterministic polylogarithmic space has a strict hierarchy**:
`NSPACE (log₂ n ^ (k + 1)) ⊂ NSPACE (log₂ n ^ (k + 2))`. -/
theorem NSPACE_log2_pow_ssubset_NSPACE_log2_pow_succ (k : ℕ) :
    NSPACE encBits (Nat.log2 · ^ (k + 1)) ⊂ NSPACE encBits (Nat.log2 · ^ (k + 2)) :=
  NSPACE_ssubset_NSPACE (spaceConstructible_log2_pow (k + 1))
    (fun n => Nat.le_self_pow (by omega) _) fun c => eventually_mul_log2_pow_add_le (k + 1) c

/-- **Nondeterministic logarithmic space is strictly within nondeterministic space `log² n`**:
`NL = NSPACE (log₂ n)` (`Cslib.Complexity.NL_eq_NSPACE`), and the nondeterministic diagonal within
space `4 * log₂ n ^ 2` separates them. -/
theorem NL_ssubset_NSPACE_log2_sq : NL encBits ⊂ NSPACE encBits (Nat.log2 · ^ 2) := by
  rw [NL_eq_NSPACE]
  refine NSPACE_ssubset_NSPACE (spaceConstructible_log2_pow 1)
    (fun n => Nat.le_self_pow (by omega) _) fun c => ?_
  simpa using eventually_mul_log2_pow_add_le 1 c

/-- **Nondeterministic polynomial space has a strict hierarchy**:
`NSPACE (n ^ k) ⊂ NSPACE (n ^ (k + 1))`. The nondeterministic diagonal within space
`4 * (n + 1) ^ (k + 1)` separates them. -/
theorem NSPACE_pow_ssubset_NSPACE_pow_succ (k : ℕ) :
    NSPACE encBits (· ^ k) ⊂ NSPACE encBits (· ^ (k + 1)) :=
  (NSPACE_ssubset_NSPACE (g := fun n => (n + 1) ^ (k + 1))
    (spaceConstructible_succ_pow (k + 1))
    (fun n => (Nat.log2_le_self n).trans ((Nat.le_succ n).trans (Nat.le_self_pow (by omega) _)))
    (eventually_mul_pow_add_le_succ_pow k)).trans_subset (NSPACE_subset_of_le_mul_add (2 ^ (k + 1))
      1 fun n => by simpa using Nat.mul_add_one_pow_le_two_pow 1 (k + 1) n)

/-- **Nondeterministic logarithmic space is strictly within polynomial space**
[Sipser, Corollary 9.6][Sipser2013]: `NL ⊆ DSPACE (log₂ n ^ 2)` by Savitch's theorem
(`Cslib.Complexity.NL_subset_DSPACE_log2_sq`), which is strictly within
`DSPACE (log₂ n ^ 3) ⊆ PSPACE` by the deterministic space hierarchy. -/
theorem NL_ssubset_PSPACE : NL encBits ⊂ PSPACE encBits :=
  (NL_subset_DSPACE_log2_sq.trans_ssubset
    (DSPACE_log2_pow_ssubset_DSPACE_log2_pow_succ 1)).trans_subset
    <| (DSPACE_mono (s₂ := fun n => (n + 1) ^ 3) fun n =>
      Nat.pow_le_pow_left ((Nat.log2_le_self n).trans (Nat.le_succ n)) 3).trans
    (DSPACE_subset_PSPACE (by fun_prop))

end Cslib.Complexity
