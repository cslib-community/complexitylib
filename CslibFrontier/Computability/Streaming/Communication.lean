/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Randomized
public import CslibFrontier.Computability.Streaming.Basic
import CslibFrontier.Probability.PMF.Event

/-!
# Streaming algorithms give one-way protocols

A streaming algorithm with `b` bits of memory turns into a one-way protocol: Alice runs it on her
part `u x` of the stream and sends the `b`-bit encoding of the memory state, and Bob decodes the
state, runs the algorithm on his part `v y` and announces the answer
(`Cslib.Streaming.Algorithm.toProtocol`). So if the answer on `u x ++ v y` determines `f x y`,
then `f` has communication complexity at most `b + 1`, deterministically
(`Cslib.Streaming.Algorithm.ecomplexityFun_le_of_spaceLE`) and, for randomized streaming
algorithms, with public coins and the same error
(`Cslib.Streaming.Randomized.ecomplexityFun_le_of_spaceLE`). This is the reduction behind the
streaming lower bounds of Alon, Matias and Szegedy [AlonMatiasSzegedy1999, Section 3]. Only the
memory reachable on Alice's streams needs an encoding; Bob's decoder inverts it on these states.

## Main definitions

* `Cslib.Streaming.Algorithm.toProtocol`: the one-way protocol simulating a streaming algorithm.

## Main results

* `Cslib.Streaming.Algorithm.depth_toProtocol_le`, `Cslib.Streaming.Algorithm.run_toProtocol`: it
  sends `b + 1` bits and answers as the streaming algorithm.
* `Cslib.Streaming.Algorithm.ecomplexityFun_le_of_spaceLE`,
  `Cslib.Streaming.Randomized.ecomplexityFun_le_of_spaceLE`: streaming memory bounds deterministic
  and public-coin communication.

## References

* [N. Alon, Y. Matias, M. Szegedy, *The space complexity of approximating the frequency
  moments*, Section 3][AlonMatiasSzegedy1999]
-/

public section

namespace Cslib.Streaming

open Communication

namespace Algorithm

variable {σ α β X Y : Type*}

/-- The one-way protocol in which Alice runs `A` on the stream `u x`, sends the `b`-bit encoding
of its memory state, and Bob decodes it, continues the run on `v y` and announces `d` of the
answer. Bob decodes by inverting `enc` on the states reachable on streams of at most `m` items. -/
noncomputable def toProtocol (A : Algorithm σ α β) (m b : ℕ) (enc : σ → BitString b)
    (u : X → List α) (v : Y → List α) (d : β → Bool) : Protocol X Y Bool :=
  haveI : Nonempty σ := ⟨A.init⟩
  Protocol.aliceSend b (fun x => enc (A.state (u x))) fun msg =>
    Protocol.bob (fun y => d (A.output (A.stateFrom (Function.invFunOn enc (A.reachable m) msg)
      (v y)))) (Protocol.output false) (Protocol.output true)

/-- The simulating protocol sends `b + 1` bits. -/
theorem depth_toProtocol_le (A : Algorithm σ α β) (m b : ℕ) (enc : σ → BitString b)
    (u : X → List α) (v : Y → List α) (d : β → Bool) :
    (A.toProtocol m b enc u v d).depth ≤ b + 1 :=
  Protocol.depth_aliceSend_le fun _ => by simp [Protocol.depth]

/-- When `enc` is injective on the states reachable on streams of at most `m` items and Alice's
stream has at most `m` items, the simulating protocol answers as the streaming algorithm on the
concatenated stream. -/
theorem run_toProtocol (A : Algorithm σ α β) {m b : ℕ} {enc : σ → BitString b}
    (henc : Set.InjOn enc (A.reachable m)) (u : X → List α) (v : Y → List α) (d : β → Bool)
    {x : X} (hx : (u x).length ≤ m) (y : Y) :
    (A.toProtocol m b enc u v d).run x y = d (A.run (u x ++ v y)) := by
  have : Nonempty σ := ⟨A.init⟩
  have hdec : Function.invFunOn enc (A.reachable m) (enc (A.state (u x))) = A.state (u x) :=
    henc.leftInvOn_invFunOn (A.state_mem_reachable hx)
  simp only [toProtocol, Protocol.run_aliceSend, Protocol.run_bob, Protocol.run_output, hdec,
    run, state_append]
  cases d (A.output (A.stateFrom (A.state (u x)) (v y))) <;> rfl

/-- **Streaming space bounds communication** (deterministic): if a streaming algorithm with `b`
bits of memory on streams of length at most `m` decides `f x y` from its answer on the stream
`u x ++ v y`, whenever `u x` has length at most `m`, then `f` has a deterministic protocol with
`b + 1` bits. -/
theorem ecomplexityFun_le_of_spaceLE (A : Algorithm σ α β) {m b : ℕ} (hA : A.SpaceLE m b)
    (u : X → List α) (v : Y → List α) (hu : ∀ x, (u x).length ≤ m) (d : β → Bool)
    (f : X → Y → Bool) (hf : ∀ x y, d (A.run (u x ++ v y)) = f x y) :
    Protocol.ecomplexityFun f ≤ b + 1 := by
  obtain ⟨enc, henc⟩ := hA
  have := Protocol.ecomplexityFun_le_depth (p := A.toProtocol m b enc u v d)
    (funext₂ fun x y => (A.run_toProtocol henc u v d (hu x) y).trans (hf x y))
  exact this.trans (by exact_mod_cast A.depth_toProtocol_le m b enc u v d)

end Algorithm

namespace Randomized

variable {σ α β X Y : Type*}

/-- **Streaming space bounds communication** (public coins): if a randomized streaming algorithm
`μ` whose algorithms use at most `b` bits of memory on streams of length at most `m` decides
`f x y` with error `ε` from its answer on `u x ++ v y`, whenever `u x` has length at most `m`, then
`f` has a public-coin protocol with error `ε` and `b + 1` bits. -/
theorem ecomplexityFun_le_of_spaceLE (μ : Randomized σ α β) {m b : ℕ} (hμ : μ.SpaceLE m b)
    (u : X → List α) (v : Y → List α) (hu : ∀ x, (u x).length ≤ m) (d : β → Bool)
    (f : X → Y → Bool) {ε : ℝ}
    (hf : ∀ x y, (μ.toOuterMeasure {A | d (A.run (u x ++ v y)) ≠ f x y}).toReal ≤ ε) :
    PublicCoin.ecomplexityFun ε f ≤ b + 1 := by
  classical
  let P : Algorithm σ α β → Protocol X Y Bool := fun A =>
    if h : A.SpaceLE m b then A.toProtocol m b h.choose u v d else Protocol.output false
  refine (PublicCoin.ecomplexity_le_depth (μ := μ.map P) fun x _ y _ => ?_).trans ?_
  · refine le_trans ?_ (hf x y)
    unfold PublicCoin.errorProb
    rw [PMF.toOuterMeasure_map_apply]
    refine ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top _ _)
      (PMF.toOuterMeasure_mono _ ?_)
    rintro A ⟨hA, hsupp⟩
    have hs := hμ A hsupp
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, P, dite_eq_left hs] at hA ⊢
    rwa [A.run_toProtocol hs.choose_spec u v d (hu x) y, eq_comm] at hA
  · refine PublicCoin.depth_le_iff.2 fun p hp => ?_
    rw [PMF.support_map] at hp
    obtain ⟨A, hA, rfl⟩ := hp
    simp only [P, dite_eq_left (hμ A hA)]
    exact_mod_cast A.depth_toProtocol_le m b _ u v d

end Randomized

end Cslib.Streaming
