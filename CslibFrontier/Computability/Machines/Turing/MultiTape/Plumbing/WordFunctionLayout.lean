/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WordFunction
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.FromLeftBlank
import Mathlib.Data.Fin.Tuple.Embedding

/-!
# Writing one word in a protected block

The ambient tapes contain a prefix of reusable scratch, a protected block, and a source and
boundary marker. A native word computation may choose any blank destination in the protected
block. It restores its scratch, preserves the source and every other protected word, and returns
all heads to their origins. The host input starts and ends at its left blank; both head movements
are charged. The underlying finite machine and polynomial clock are chosen before the ambient
block sizes, selected destination, or runtime words.
-/

public section

namespace Turing.MultiTapeTM.WordFunctionLayout

private def scratchTapes {k S E : ℕ} (hk : k ≤ S) : Fin k ↪ Fin (S + E + 2) :=
  (Fin.castLEEmb hk).trans ((Fin.castAddEmb E).trans (Fin.castAddEmb 2))

private def outputBlock {k S E : ℕ} (hk : k ≤ S) (dest : Fin E) :
    Fin (k + 1) ↪ Fin (S + E + 2) :=
  Fin.Embedding.snoc (scratchTapes hk) (a := (Fin.natAdd S dest).castAdd 2) (by
    rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    change i.val = S + dest.val at hv
    have := i.isLt
    omega)

/-- Embed the private scratch, selected output, and final source/marker into the ambient layout. -/
def outputTapes {k S E : ℕ} (hk : k ≤ S) (dest : Fin E) :
    Fin (k + 1 + 2) ↪ Fin (S + E + 2) :=
  Fin.Embedding.append (x := outputBlock hk dest) (y := Fin.natAddEmb (S + E)) (by
    rw [Set.disjoint_left]
    rintro _ ⟨i, rfl⟩ ⟨j, hj⟩
    cases i using Fin.lastCases with
    | last =>
      have hv := congrArg Fin.val hj
      simp only [outputBlock, Fin.Embedding.snoc_last] at hv
      change S + E + j.val = S + dest.val at hv
      have := dest.isLt
      omega
    | cast i =>
      have hv := congrArg Fin.val hj
      simp only [outputBlock, Fin.Embedding.snoc_castSucc] at hv
      change S + E + j.val = i.val at hv
      have := i.isLt
      omega)

/-- Private work tapes occupy the beginning of the reusable scratch prefix. -/
@[simp] theorem outputTapes_work {k S E : ℕ} (hk : k ≤ S) (dest : Fin E) (i : Fin k) :
    outputTapes hk dest (i.castSucc.castAdd 2) =
      ((Fin.castLE hk i).castAdd E).castAdd 2 := by
  simp [outputTapes, outputBlock, scratchTapes]

/-- The native output goes to the selected protected word. -/
@[simp] theorem outputTapes_output {k S E : ℕ} (hk : k ≤ S) (dest : Fin E) :
    outputTapes hk dest ((Fin.last k).castAdd 2) = (Fin.natAdd S dest).castAdd 2 := by
  simp [outputTapes, outputBlock]

/-- The serialized source is the penultimate ambient tape. -/
@[simp] theorem outputTapes_input {k S E : ℕ} (hk : k ≤ S) (dest : Fin E) :
    outputTapes hk dest (Fin.natAdd (k + 1) 0) = Fin.natAdd (S + E) 0 := by
  simp [outputTapes]

/-- The source boundary marker is the final ambient tape. -/
@[simp] theorem outputTapes_marker {k S E : ℕ} (hk : k ≤ S) (dest : Fin E) :
    outputTapes hk dest (Fin.natAdd (k + 1) 1) = Fin.natAdd (S + E) 1 := by
  simp [outputTapes]

/-- Only the selected output and private scratch must be blank; other protected words are free. -/
theorem outputTapes_blank {k S E : ℕ} (hk : k ≤ S) (dest : Fin E)
    (words : Fin (S + E + 2) → List Bool)
    (hscratch : ∀ i : Fin S, words ((i.castAdd E).castAdd 2) = [])
    (hdest : words ((Fin.natAdd S dest).castAdd 2) = [])
    (hmarker : words (Fin.natAdd (S + E) 1) = []) :
    ∀ j ≠ Fin.natAdd (k + 1) 0, words (outputTapes hk dest j) = [] := by
  intro j hj
  cases j using Fin.addCases with
  | left j =>
    cases j using Fin.lastCases with
    | last => simpa only [outputTapes_output] using hdest
    | cast j => simpa only [outputTapes_work] using hscratch (Fin.castLE hk j)
  | right j =>
    fin_cases j
    · exact (hj rfl).elim
    · change words (outputTapes hk dest (Fin.natAdd (k + 1) 1)) = []
      simpa only [outputTapes_marker] using hmarker

/-- Choose one finite native word machine before all ambient parameters. Each instantiation
writes one protected word and returns the host head to its left blank in two additional steps. -/
theorem exists_of_polyTime {α β : Type} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    {f : α → β} (hf : ComputableInPolyTime f encIn encOut) :
    ∃ (k : ℕ) (Q : Type) (_ : Finite Q) (tm : MultiTapeTM (k + 1 + 2) Bool Q) (c d : ℕ),
      ∀ (S E : ℕ) (hk : k ≤ S) (dest : Fin E) (input : List Bool) (a : α)
        (words : Fin (S + E + 2) → List Bool) (out : List Bool),
        (∀ i : Fin S, words ((i.castAdd E).castAdd 2) = []) →
        words ((Fin.natAdd S dest).castAdd 2) = [] →
        words (Fin.natAdd (S + E) 0) = encIn a →
        words (Fin.natAdd (S + E) 1) = [] →
        RunsBetween (input := input) ((tm.extendTapes (outputTapes hk dest)).fromLeftBlank)
          { tapesCfg input words 0 0 out with inputPos := 0 }
          { tapesCfg input
              (Function.update words ((Fin.natAdd S dest).castAdd 2) (encOut (f a)))
              0 0 out with inputPos := 0 }
          (c * ((encIn a).length + 1) ^ d + 2)
          ((S + E + 2) * (c * ((encIn a).length + 1) ^ d + 1) + 4 * (S + E + 2)) := by
  obtain ⟨k, Q, hQ, tm, c, d, htm⟩ := WordFunction.exists_of_polyTime hf
  refine ⟨k, Q, hQ, tm, c, d, ?_⟩
  intro S E hk dest input a words out hscratch hdest hsource hmarker
  have hr := htm (S + E + 2) (outputTapes hk dest) input a words out
    (by simpa only [outputTapes_input] using hsource)
    (outputTapes_blank hk dest words hscratch hdest hmarker)
  simpa only [outputTapes_output] using hr.fromLeftBlank rfl rfl

end Turing.MultiTapeTM.WordFunctionLayout
