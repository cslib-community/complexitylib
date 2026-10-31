/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.CountingSimulation.FastAnalysis
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.FastContractionLeaf

/-!
# The leaf bounds of the native recursion

The leaf clause of the resource analysis of the native recursion of Theorem D.1 of
[OpenAI2026ETH] (`Cslib.Complexity.CountingSimulation.FastLeaves`), from the cost of a leaf with
the packet shape (`Cslib.Circuits.Frontier.FastContraction.exists_leafCertificate_le`), the sizes
of the reached calls (`Cslib.Complexity.CountingSimulation.FastSizes`) and three facts about the
reached calls: at most twice the scale in edges and, from some size on, at most the leaf size in
edges at a leaf and precision at most the fourth power of the scale. Those facts and the sizes are
proved (`FastContraction.Reach.edges_le_two_mul_scale`, `CountingSimulation.reach_facts`,
`CountingSimulation.fastSizes`), so the resource analysis of the native recursion holds
(`CountingSimulation.fastAnalysis_nativeMk_holds`).

Every reached call is well-formed and has the packet shape (`FastContraction.Reach.wf_packetShape`),
by `FastContraction.wfChildren_nativeMk` and `FastContraction.packetShape_child`.

## Main results

* `Cslib.Circuits.Frontier.FastContraction.Reach.wf_packetShape`: the reached calls are
  well-formed and have the packet shape.
* `Cslib.Complexity.CountingSimulation.fastLeaves_of`: the leaf bounds from the reached-call facts.
* `Cslib.Circuits.Frontier.FastContraction.Reach.edges_le_two_mul_scale`: at most twice the scale
  in edges.
* `Cslib.Complexity.CountingSimulation.fastLeaves`: the leaf bounds.
* `Cslib.Complexity.CountingSimulation.fastAnalysis_nativeMk_holds`: the resource analysis of the
  native recursion.
* `Cslib.Complexity.CountingSimulation.fastContractionAlgorithm`: the contraction algorithm of
  Theorem D.1 for admissible explicit networks.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §D.4.6–§D.4.7,
  pp. 63–64.
-/

public section

namespace Cslib.Circuits.Frontier.FastContraction

/-- **The reached calls are well-formed and have the packet shape**, from a well-formed root with
the packet shape. -/
theorem Reach.wf_packetShape {x₀ x : Call} (h : Reach nativeMk x₀ x) (hw : WF x₀)
    (hs : PacketShape x₀) : WF x ∧ PacketShape x := by
  induction h with
  | root => exact ⟨hw, hs⟩
  | step c _ ha hc ih =>
    exact ⟨wfChildren_nativeMk _ ih.1 ha c hc, packetShape_child ih.1 ha ih.2 hc⟩

/-- **Reached calls have at most twice the scale in edges**, from a root at scale its number of
edges with bound plus depth one more, for every input: a child has at most twice its parent's
edges (`NativeChild.numEdges_nativeChild_le`), and an active parent has at most the root's. -/
theorem Reach.edges_le_two_mul_scale {x₀ x : Call} (h₀s : x₀.scale = x₀.edges)
    (h₀b : x₀.bound + x₀.depth = x₀.edges + 1) (h : Reach nativeMk x₀ x) :
    x.edges ≤ 2 * x.scale := by
  have key : x.edges ≤ 2 * x₀.edges := by
    induction h with
    | root => omega
    | @step y c hy ha _ _ =>
      have h1 : (nativeMk y c).2.numEdges ≤ 2 * y.edges := by
        unfold nativeMk
        exact NativeChild.numEdges_nativeChild_le _ _ _ _ _ _ _ _ _ _ _
      have h2 := hy.bound_add_depth_le
      have h3 := edges_lt_bound_of_active ha
      change (nativeMk y c).2.numEdges ≤ 2 * x₀.edges
      omega
  rw [h.scale_eq, h₀s]
  exact key

end Cslib.Circuits.Frontier.FastContraction

namespace Cslib.Complexity.CountingSimulation

open Cslib.Circuits.Frontier Cslib.Circuits.Frontier.ContractionSchedule
  Cslib.Circuits.Frontier.FastContraction

/-- **The leaf bounds of the native recursion**, from the sizes of the reached calls and three
facts about them on admissible guarded inputs: every reached call has at most twice its scale in
edges, and for each `C` and `D`, from some size on, every reached leaf has at most the leaf size in
edges and precision at most the fourth power of its scale. -/
theorem fastLeaves_of (hS : FastSizes)
    (hE : ∀ (P : ℕ) (G : ℕ × ExplicitTensorNetwork ℕ) (x : Call),
      Reach nativeMk (root (ExplicitTensorNetwork.capPrecision (P, G))) x →
        x.edges ≤ 2 * x.scale)
    (hbig : ∀ C D : ℕ, ∃ s₀ : ℕ, ∀ (s P : ℕ) (G : ℕ × ExplicitTensorNetwork ℕ), 2 ≤ s → 1 ≤ P →
      P ≤ D * s → ExplicitAdmissible C s G → fastGuard G = true → s₀ ≤ s →
      ∀ x, Reach nativeMk (root (ExplicitTensorNetwork.capPrecision (P, G))) x →
        active x = false → x.edges ≤ leafSize x.scale ∧ x.prec ≤ x.scale ^ 4) :
    FastLeaves := by
  intro C D
  obtain ⟨cS, dS, hKS⟩ := hS C D
  set KS := cS + dS
  obtain ⟨s₀, hs₀⟩ := hbig C D
  obtain ⟨KB, hKB⟩ := exists_leafCertificate_le C 4 s₀
  refine ⟨KB * (KS + 1) ^ KB + KS * KB + KB, fun s P G hs hP hPD hA hg x hx hl => ?_⟩
  set n := (FastContraction.encInput (P, G)).length with hn
  have hscale : x.scale = G.2.numEdges := hx.scale_eq
  have hsm : s ≤ x.scale := hscale ▸ hA.2.2.2.2.2
  have hmC : x.scale ≤ C * s := hscale ▸ hA.2.1
  obtain ⟨-, hshape⟩ := hx.wf_packetShape (wf_root P hg) (packetShape_root _)
  obtain ⟨hT, hSp⟩ := hKB nativeMk s x hs hsm hmC hshape (hE P G x hx)
    fun h => hs₀ s P G hs hP hPD hA hg h x hx hl
  have hlen' := (hKS s P G hs hP hPD hA hg x hx).1
  rw [← hn] at hlen'
  have hlen : (encCall x).length ≤ KS * (n + 1) ^ KS :=
    hlen'.trans (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega)))
  -- `n_x + 1 ≤ (KS + 1) (n + 1) ^ KS`.
  have hB1 : 1 ≤ (n + 1) ^ KS := Nat.one_le_pow _ _ (by omega)
  have hx1 : (encCall x).length + 1 ≤ (KS + 1) * (n + 1) ^ KS := by
    rw [add_mul, one_mul]; omega
  set K := KB * (KS + 1) ^ KB + KS * KB + KB
  have hpoly : KB * ((encCall x).length + 1) ^ KB ≤ K * (n + 1) ^ K :=
    calc KB * ((encCall x).length + 1) ^ KB ≤ KB * ((KS + 1) * (n + 1) ^ KS) ^ KB :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hx1 _)
      _ = KB * (KS + 1) ^ KB * (n + 1) ^ (KS * KB) := by rw [mul_pow, ← pow_mul]; ring
      _ ≤ K * (n + 1) ^ K :=
          Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
  have hexp : KB * s / Nat.sqrt (Nat.log 2 s) ≤ K * s / Nat.sqrt (Nat.log 2 s) :=
    Nat.div_le_div_right (Nat.mul_le_mul_right _ (by omega))
  exact ⟨hT.trans (Nat.mul_le_mul hpoly (Nat.pow_le_pow_right (by norm_num) hexp)),
    hSp.trans hpoly⟩

/-- **The leaf bounds of the native recursion.** -/
theorem fastLeaves : FastLeaves :=
  fastLeaves_of fastSizes (fun _ _ _ hx => hx.edges_le_two_mul_scale rfl rfl) fun C D => by
    obtain ⟨s₀, hs₀⟩ := reach_facts C D
    refine ⟨s₀, fun s P G hs hP hPD hA hg h x hx hl => ?_⟩
    obtain ⟨hp, hlf⟩ := (hs₀ s P G hs hP hPD hA hg x hx).2.2.2 h
    exact ⟨hlf hl, hp⟩

/-- **The resource analysis of the native recursion holds**: the derivation of the root over the
reached calls has polynomial height, sizes and leaf space, leaf time `poly(n) 2 ^ O(s / √⌊log₂ s⌋)`,
and, from some size on, its nodes fit in the clock. -/
theorem fastAnalysis_nativeMk_holds : FastAnalysis nativeMk :=
  fastAnalysis_nativeMk fastLeaves

/-- **The contraction algorithm of Theorem D.1** for admissible explicit networks: the native
recursion behind a guard, with direct summation for the networks the guard rejects, in time
`poly(n) 2 ^ O(s / √⌊log₂ s⌋)` and polynomial space. -/
noncomputable def fastContractionAlgorithm :
    ContractionAlgorithm (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encNat
      ExplicitTensorNetwork.encExplicitNetwork)
      (fun G => G.2.contraction) ExplicitAdmissible :=
  contractionAlgorithmOfNative fastAnalysis_nativeMk_holds

end Cslib.Complexity.CountingSimulation
