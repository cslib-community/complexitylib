/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.DeterministicTransitiveClosure.Compile
public import CslibFrontier.Logics.FirstOrder.Ordered.DeterministicTransitiveClosure
public import CslibFrontier.Computability.Complexity.Classes.LogSpace
public import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.Ordered.Decider

/-!
# FO(DTC) model checking in logarithmic space

For each fixed sentence of FO(DTC) over a finite relational vocabulary expanded by the canonical
numeric symbols, the encoded query language belongs to the native class `L`. The input uses
`encStructure`, as for ordered first-order model checking in `L`; malformed table shapes and
cardinalities below two are rejected.

FO(DTC) sentences are FO(TC) syntax trees read with `DTC.interpretation`. The decider is one
deterministic counter program, `blockDecider` around the compiled sentence: it validates the
input tables, rejects cardinalities below two, runs the compiled code of the sentence, and
accepts or rejects at the exit the code takes. It
halts with every register at most `(N + 1) ^ (d + w)` for input length `N`, maximal input arity
`d` and closure width `w`, so it runs in logarithmic space.

Each closure is evaluated by following unique successors for at most `n ^ k` steps, where the
successor is found by enumerating all candidate tuples and running the compiled body on each.
Every compiled block exits on both truth values, so closures under negation need nothing more
([Immerman1987], Theorem 4.2). The converse inclusion L ⊆ FO(DTC) is
`DTCDefinable.of_encodedLanguage_mem_L`, and the two together give
`dtcDefinable_iff_encodedLanguage_mem_L`, both in `DeterministicTransitiveClosure/Converse`.

## Main results

* `Cslib.Logic.FO.Ordered.DTCModelChecker.encodedLanguage_mem_L`: a query defined by an FO(DTC)
  sentence is in native `L`.
* `Cslib.Logic.FO.Ordered.DTCDefinable.encodedLanguage_mem_L`: FO(DTC) ⊆ L on canonically ordered
  structures.

## References

* [N. Immerman, *Languages That Capture Complexity Classes*, Theorem 4.2][Immerman1987]
-/

public section

universe u v

open FirstOrder Language

namespace Cslib.Logic.FO.Ordered.DTCModelChecker

open Turing Turing.CounterProgram Turing.CounterProgram.Block Expr Vocabulary.ModelChecker
open Operator (Formula RelEnv)

variable {L : Language.{u, v}} [L.IsRelational] (v : Vocabulary L)

/-- **A query defined by an FO(DTC) sentence is in native `L`**: its source-only encoded language
is decided by one deterministic machine, `blockDecider` around the compiled sentence, in
logarithmic space. -/
theorem encodedLanguage_mem_L {φ : Formula (language L) TC.shape [] Empty} {K : Query L}
    (hφ : ∀ M : Ordered.Structure L,
      M ∈ K ↔ φ.Realize (M := M) DTC.interpretation RelEnv.empty Empty.elim) :
    K.encodedLanguage v ∈ Complexity.L encStructure :=
  mem_L_of_decidingBlock v (k := TC.width φ) (s := scratch φ)
    (length_compile v (fun e : Empty => e.elim) 3 φ) (fun _ h => ⟨h.1, h.2.1⟩)
    fun a hwf hn _ b T F regs hP hlen h0 hB => by
      let _ : Fact (2 ≤ a.1) := ⟨hn⟩
      let _ := v.decode a
      obtain ⟨hB1, hnB, hwidth, -, -⟩ := decider_bounds v a (TC.width φ)
      have hE : Env v a (((encStructure a).length + 1) ^ (v.maxArity + TC.width φ)) :=
        ⟨fun fv base val => ModelChecker.atomicCompiler_correct hwf fv base val, hB1, hnB⟩
      obtain ⟨res, regs', hres, hreach, hk⟩ := correct hE φ rfl hwidth (fun e : Empty => e.elim)
        3 Empty.elim RelEnv.empty b T F regs hP (by decide) (fun e => e.elim) (by omega) h0
        (fun e => e.elim) hB
      refine ⟨res, regs', ?_, hreach, hk.bounded⟩
      rw [hres]
      exact ⟨fun h => ⟨hwf, hn, (hφ (decoded v a hn)).mpr h⟩,
        fun ⟨_, _, h⟩ => (hφ (decoded v a hn)).mp h⟩

end Cslib.Logic.FO.Ordered.DTCModelChecker

namespace Cslib.Logic.FO.Ordered

/-- **FO(DTC) ⊆ L** on canonically ordered structures: a query defined by one FO(DTC) sentence is
in native deterministic logarithmic space, at the source-only structure encoding
([Immerman1987], Theorem 4.2). -/
theorem DTCDefinable.encodedLanguage_mem_L {L : Language} [L.IsRelational] {K : Query L}
    (hK : DTCDefinable K) (v : Vocabulary L) :
    K.encodedLanguage v ∈ Complexity.L encStructure :=
  let ⟨_, hφ⟩ := hK
  DTCModelChecker.encodedLanguage_mem_L v hφ

end Cslib.Logic.FO.Ordered
