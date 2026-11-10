/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Hierarchy.TinyDesc
public import CslibFrontier.Computability.Complexity.Classes.Space.Nondeterministic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.NondeterministicBudget
import CslibFrontier.Computability.Complexity.Classes.Hierarchy.SpaceDiagonalBounds

/-!
# The nondeterministic space diagonal

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
description, so it is eventually below `G n`
(`Cslib.Complexity.Diagonal.eventually_cfgSpaceBound_le`). On its own description, padded to a
doubly exponential length where it is tiny (`Cslib.Complexity.Diagonal.tinyDesc`), the machine
accepts exactly when the diagonal rejects (`Cslib.Complexity.nspaceDiagonal_notMem_NSPACE`). This
is the diagonal argument of [Sipser, Theorem 9.3][Sipser2013] for nondeterministic machines.

## Main definitions

* `Cslib.Complexity.nspaceDiagonal`: the nondeterministic diagonal within a space budget.

## Main results

* `Turing.MultiTapeTM.Universal.accepts_iff_bAccepts_descN`: a machine within `S` cells accepts
  exactly when its description accepts within any budget at least the size of its configurations.
* `Cslib.Complexity.not_recognizesInSpace_nspaceDiagonal`: no nondeterministic machine recognizes
  the diagonal within space `O(f)`.
* `Cslib.Complexity.nspaceDiagonal_notMem_NSPACE`: the diagonal is not in `NSPACE f`.

## References

* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

public section

namespace Turing.MultiTapeTM.Universal

/-- **A machine within `S` cells accepts exactly when its description accepts within a budget**
`b` at least the size bound `Turing.MultiTapeTM.Universal.cfgSpaceBound` of its configurations. -/
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

@[simp]
theorem mem_nspaceDiagonal {G : ℕ → ℕ} {x : List Bool} :
    x ∈ nspaceDiagonal G ↔ ¬ BAccepts (decodeDesc (Diagonal.tinyCut x)) (x.map eBit) (G x.length) :=
  Iff.rfl

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
  -- the configurations of the description eventually fit within the budget
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_cfgSpaceBound_le hlog hfG (descLen (descN eS eBit ntm)) c₁ c₂)
  -- so on its description, padded beyond `N`, it accepts exactly when the diagonal rejects
  obtain ⟨x, hx, -, hdec⟩ := exists_decodeDesc_tinyCut_eq (descN eS eBit ntm) N
  obtain ⟨hrun, hmem⟩ := hA x
  simp only [encBits_apply] at hrun hmem
  have hk : k ≤ descLen (descN eS eBit ntm) := by simpa using tapes_le (descN eS eBit ntm)
  rw [mem_nspaceDiagonal, hdec,
    accepts_iff_bAccepts_descN eS ntm hrun (hN x.length hx k hk)] at hmem
  exact iff_not_self hmem.symm

/-- **The nondeterministic diagonal within space `G` is not in `NSPACE f`** when every
`c * f n + c` is eventually below `G n` and `4 * log₂ n ≤ G n`: a decider within space `O(f)`
recognizes the diagonal within that space (`Cslib.Complexity.not_recognizesInSpace_nspaceDiagonal`).
-/
theorem nspaceDiagonal_notMem_NSPACE {f G : ℕ → ℕ} (hlog : ∀ n, 4 * Nat.log2 n ≤ G n)
    (hfG : ∀ c, ∀ᶠ n in atTop, c * f n + c ≤ G n) : nspaceDiagonal G ∉ NSPACE encBits f := by
  rintro ⟨k, State, _, ntm, c₁, c₂, hA⟩
  exact not_recognizesInSpace_nspaceDiagonal hlog hfG ntm c₁ c₂ hA.recognizesInSpace

end Cslib.Complexity
