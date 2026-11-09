/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Reduction.LocalSelfReducibility.RuntimeAccess
public import CslibFrontier.Computability.Machines.ReadMachine.VirtualWord.Generate
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Words
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Unary

/-!
# Runtime headers computed from live local-query generators

`localQueryData_logSpace` runs a query generator, drops its prefix through the existing counter
program, converts the cut to binary, and emits compact metadata. No query or frame is placed in
workspace. `consume_localQuery` composes this frame generator with an arbitrary ordinary logspace
word consumer. Its bound uses the original word, with no padded input or free header oracle.
The unary cut is a streamed intermediate output, not a unary workspace counter.

These are original implementation lemmas supporting the reconstruction of Definitions 3.1–3.2
and the storage argument of Lemma 3.3, expanded ECCC TR13-047 (18 March 2013), printed pages 6–7
[GlasserNguyenReitwiessnerSelmanWitek2013]. The cut computation is an explicit ordinary logspace
premise; this module does not construct the ceiling-logarithmic cut program. Nor does it prove
answer regeneration, the decreasing suffix loop, adaptive-to-tt conversion or Lemma 3.3.
-/

public section

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM

/-- Extract the small suffix from the live query stream and encode both counters in binary.
The cut generator's unary output is consumed by recomputation in `bitsDrop'`. -/
theorem localQueryData_logSpace {α : Type} {enc : α ↪ List Bool}
    {q : α → List Bool} {cut address : α → ℕ}
    (hq : ComputableInLogSpace q enc encBits)
    (hcut : ComputableInLogSpace cut enc encUnary)
    (hi : ComputableInLogSpace address enc encNat) :
    ComputableInLogSpace (fun a => (cut a, (q a).drop (cut a), address a))
      enc VirtualWord.encData :=
  hcut.unaryToBinary.pair ((hq.bitsDrop' hcut).pair hi)

/-- A local-query consumer with workspace logarithmic in the actual original input. The
source locality theorem proves the entire header bound and exact virtual length; they are
not assumed transfer certificates. `hcut` is still a real cut-program obligation. -/
theorem consume_localQuery {α β : Type} {enc : α ↪ List Bool}
    {x q : α → List Bool} {cut : α → ℕ} {f : List Bool → β}
    {encOut : β ↪ List Bool}
    (hx : ComputableInLogSpace x enc encBits)
    (hq : ComputableInLogSpace q enc encBits)
    (hcut : ComputableInLogSpace cut enc encUnary)
    (hcut_eq : ∀ a, cut a = (x a).length - Nat.clog 2 (x a).length)
    (hlocal : ∀ a, LocalSelfReductionQuery (x a) (q a))
    (hlen : ∀ a, (x a).length ≤ (enc a).length)
    (hf : ComputableInLogSpace f encBits encOut) :
    ComputableInLogSpace (fun a => f (q a)) enc encOut := by
  have hd := localQueryData_logSpace hq hcut
    (ComputableInLogSpace.const (encMid := encNat) 0)
  have hc (a : α) : cut a ≤ (x a).length := by rw [hcut_eq]; omega
  have h := VirtualWord.Generate.consume hx hd hc hf 17 1 1
    (fun a => ?_) (fun a => ?_)
  · apply h.congr_fun
    intro a
    congr 1
    rw [hcut_eq]
    exact (hlocal a).reconstruct
  · rw [hcut_eq]
    have hb := VirtualWord.Runtime.budget_le_original_log _
      ((hlocal a).runtime_admissible (i := 0) (by omega))
    have hm : Nat.log2 (x a).length ≤ Nat.log2 (enc a).length := by
      simp only [Nat.log2_eq_log_two]
      exact Nat.log_mono_right (hlen a)
    dsimp only [localQueryAccessData] at hb
    nlinarith
  · rw [hcut_eq, (hlocal a).access_length]
    simpa using (hlen a).trans (Nat.le_succ _)

end Cslib.Complexity
