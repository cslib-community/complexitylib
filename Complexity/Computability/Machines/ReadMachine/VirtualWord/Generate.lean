/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.ReadMachine.VirtualWord.Native
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Composition.SmallSpace

/-!
# Generating and consuming runtime frames

`prepare` streams a computed binary cut/suffix/address header followed by a computed original
word. `prepare_logSpace` constructs its native certificate from ordinary logspace component
programs. `consume` composes that generator with `Native.of_logSpace` using `comp_space`:
the generated frame is recomputed at every requested input position, never stored in workspace.
Both the header and virtual-length estimates are relative to the caller's actual encoding.

This is original implementation infrastructure for the small stored suffix in Definitions
3.1–3.2 and the proof of Lemma 3.3 of [GlasserNguyenReitwiessnerSelmanWitek2013], expanded
ECCC TR13-047 (18 March 2013), printed pages 6–7. It supplies no suffix iteration, language oracle,
answer-word generator or adaptive-to-tt conversion, and does not establish that lemma.
-/

public section

namespace Turing.VirtualWord.Generate

open MultiTapeTM

variable {α β : Type} {enc : α ↪ List Bool}

/-- A generated runtime input; the proof changes neither the encoding nor the input length. -/
@[expose] def prepare (w : α → List Bool) (d : α → Data)
    (hc : ∀ a, (d a).1 ≤ (w a).length) (a : α) : Simulation.Input :=
  ⟨(d a, w a), hc a⟩

/-- Exact streamed bytes: a framed binary metadata header and the unchanged generated tail. -/
theorem enc_prepare (w : α → List Bool) (d : α → Data)
    (hc : ∀ a, (d a).1 ≤ (w a).length) (a : α) :
    Simulation.encInput (prepare w d hc a) = frame (encData (d a)) ++ w a := rfl

/-- Generate the frame from actual component programs. Pairing runs the header generator and
then the tail generator, emitting their outputs without allocating a polynomial-sized word. -/
theorem prepare_logSpace {w : α → List Bool} {d : α → Data}
    (hw : ComputableInLogSpace w enc encBits) (hd : ComputableInLogSpace d enc encData)
    (hc : ∀ a, (d a).1 ≤ (w a).length) :
    ComputableInLogSpace (prepare w d hc) enc Simulation.encInput :=
  (hd.pair hw).congr fun _ => rfl

private theorem log_le_binary (n : ℕ) : Nat.log2 n ≤ (encNat n).length := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [encNat_apply, Nat.size_eq_bits_len]
  exact ((Nat.log2_lt hn.ne').mpr (Nat.lt_size_self n)).le

/-- Consume a generated virtual word in caller-logarithmic workspace. Only actual generator
certificates and size estimates are premises; no virtual-input or transfer certificate is
assumed. Polynomial output length of the frame generator follows from its logspace certificate.
The consumer may itself emit a polynomial word: composition does not retain its output history. -/
theorem consume {w : α → List Bool} {d : α → Data} {f : List Bool → β}
    {encOut : β ↪ List Bool}
    (hw : ComputableInLogSpace w enc encBits) (hd : ComputableInLogSpace d enc encData)
    (hc : ∀ a, (d a).1 ≤ (w a).length)
    (hf : ComputableInLogSpace f encBits encOut)
    (H V D : ℕ)
    (hheader : ∀ a, (encData (d a)).length ≤ H * (Nat.log2 (enc a).length + 1))
    (hvirtual : ∀ a, (word (w a) (d a).1 (d a).2.1).length ≤
      V * ((enc a).length + 1) ^ D) :
    ComputableInLogSpace (fun a => f (word (w a) (d a).1 (d a).2.1)) enc encOut := by
  have hg := prepare_logSpace hw hd hc
  obtain ⟨A, B, hlen⟩ := hg.polyBounded_length.exists_le
  obtain ⟨tg, cg, hg⟩ := hg
  obtain ⟨tf, c, a, C, hf⟩ := Native.of_logSpace hf
  obtain ⟨k, hk⟩ := hg.comp_space hf
  let K := Nat.size A + 2 * B + 1
  let L := Nat.size V + 2 * D + 1
  refine ⟨_, k * (cg + c * (C * (a + 1) * (L + 1) + H + K + 1) + 2 + (K + 2) + 1),
    hk.mono (fun _ => le_rfl) fun x => ?_⟩
  have hphys := length_encNat_le_of_le_mul_pow (hlen x)
  have hv := length_encNat_le_of_le_mul_pow (hvirtual x)
  have hp := (log_le_binary (Simulation.encInput (prepare w d hc x)).length).trans hphys
  have hv' := (log_le_binary (word (w x) (d x).1 (d x).2.1).length).trans hv
  have hpos := length_encNat_le_log2_add_two
    (j := (enc x).length + 1) (N := (enc x).length) le_rfl
  have hmid := length_encNat_le_log2_add_two
    (j := (Simulation.encInput (prepare w d hc x)).length + 1)
    (N := (Simulation.encInput (prepare w d hc x)).length) le_rfl
  have hh := hheader x
  rw [Nat.mul_assoc]
  apply Nat.mul_le_mul_left
  dsimp only [Function.comp_apply, prepare] at *
  have hv1 : (word (w x) (d x).1 (d x).2.1).length.log2 + 1 ≤
      (L + 1) * (Nat.log2 (enc x).length + 1) := by dsimp only [L]; nlinarith only [hv']
  have hconsumer : c * (C *
      (a * ((word (w x) (d x).1 (d x).2.1).length.log2 + 1) +
        (word (w x) (d x).1 (d x).2.1).length.log2 + 1) +
        (encData (d x)).length +
        (Simulation.encInput (prepare w d hc x)).length.log2 + 1) ≤
      c * (C * (a + 1) * (L + 1) + H + K + 1) *
        (Nat.log2 (enc x).length + 1) := by
    calc
      _ = c * (C * ((a + 1) *
          ((word (w x) (d x).1 (d x).2.1).length.log2 + 1)) +
          (encData (d x)).length +
          (Simulation.encInput (prepare w d hc x)).length.log2 + 1) := by ring
      _ ≤ c * (C * ((a + 1) * ((L + 1) * (Nat.log2 (enc x).length + 1))) +
          H * (Nat.log2 (enc x).length + 1) +
          K * (Nat.log2 (enc x).length + 1) + (Nat.log2 (enc x).length + 1)) := by
        gcongr <;> first | exact hp | omega
      _ = _ := by ring
  dsimp only [prepare] at hconsumer
  dsimp only [K] at *
  nlinarith only [hconsumer, hpos, hmid, hp]

end Turing.VirtualWord.Generate
