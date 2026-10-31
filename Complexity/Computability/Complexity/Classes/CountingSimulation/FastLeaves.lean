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
edges at a leaf and precision at most the square of the scale.

Every reached call is well-formed and has the packet shape (`FastContraction.Reach.wf_packetShape`),
by `FastContraction.wfChildren_nativeMk` and `FastContraction.packetShape_child`.

## Main results

* `Cslib.Circuits.Frontier.FastContraction.Reach.wf_packetShape`: the reached calls are
  well-formed and have the packet shape.
* `Cslib.Complexity.CountingSimulation.fastLeaves_of`: the leaf bounds.

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

end Cslib.Circuits.Frontier.FastContraction

namespace Cslib.Complexity.CountingSimulation

open Cslib.Circuits.Frontier Cslib.Circuits.Frontier.ContractionSchedule
  Cslib.Circuits.Frontier.FastContraction

/-- **The leaf bounds of the native recursion**, from the sizes of the reached calls and three
facts about them on admissible guarded inputs: every reached call has at most twice its scale in
edges, and for each `C` and `D`, from some size on, every reached leaf has at most the leaf size in
edges and precision at most the square of its scale. -/
theorem fastLeaves_of (hS : FastSizes)
    (hE : ∀ (P : ℕ) (G : ℕ × ExplicitTensorNetwork ℕ) (x : Call),
      Reach nativeMk (root (ExplicitTensorNetwork.capPrecision (P, G))) x →
        x.edges ≤ 2 * x.scale)
    (hbig : ∀ C D : ℕ, ∃ s₀ : ℕ, ∀ (s P : ℕ) (G : ℕ × ExplicitTensorNetwork ℕ), 2 ≤ s → 1 ≤ P →
      P ≤ D * s → ExplicitAdmissible C s G → fastGuard G = true → s₀ ≤ s →
      ∀ x, Reach nativeMk (root (ExplicitTensorNetwork.capPrecision (P, G))) x →
        active x = false → x.edges ≤ leafSize x.scale ∧ x.prec ≤ x.scale ^ 2) :
    FastLeaves := by
  intro C D
  obtain ⟨KS, hKS⟩ := hS C D
  obtain ⟨s₀, hs₀⟩ := hbig C D
  obtain ⟨KB, hKB⟩ := exists_leafCertificate_le C 2 s₀
  refine ⟨KB * (KS + 1) ^ KB + KS * KB + KB, fun s P G hs hP hPD hA hg x hx hl => ?_⟩
  set n := (FastContraction.encInput (P, G)).length with hn
  have hscale : x.scale = G.2.numEdges := hx.scale_eq
  have hsm : s ≤ x.scale := hscale ▸ hA.2.2.2.2.2
  have hmC : x.scale ≤ C * s := hscale ▸ hA.2.1
  obtain ⟨-, hshape⟩ := hx.wf_packetShape (wf_root P hg) (packetShape_root _)
  obtain ⟨hT, hSp⟩ := hKB nativeMk s x hs hsm hmC hshape (hE P G x hx)
    fun h => hs₀ s P G hs hP hPD hA hg h x hx hl
  have hlen := (hKS s P G hs hP hPD hA hg x hx).1
  rw [← hn] at hlen
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

end Cslib.Complexity.CountingSimulation
