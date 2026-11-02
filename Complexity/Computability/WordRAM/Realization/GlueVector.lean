/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Realization.Basic
public import Complexity.Computability.WordRAM.Glue

/-!
# Certified finite-result word glue

A finite family of scalar `GlueComputes` certificates realizes one faithfully encoded result.
The scalar witnesses are selected before every runtime input and word width. All coordinates
reuse a static auxiliary bank disjoint from the output slots, and each computed coordinate is
copied into its final slot. Both those copies and the empty-vector case are charged.

`optionWords` supplies the shared two-word result convention needed by memory-stack and queue
clients: `none` is `(0,0)` and `some v` is `(1,v)`. The payload is not incremented, so the largest
fitting word remains representable. `boolWords` retains a zero slot for active-loop tests; a
true tag still requires the visible word-fit condition for `1`.

## Main definitions

* `optionWords`: a faithful tag/payload encoding of optional natural words.
* `boolWords`: a Boolean tag with a retained zero slot for native comparisons.

## Main results

* `Realizes.glueVector`: realize a finite result using certified scalar coordinate computations.

This is a realization rule over the existing memory client and structured native code, not an
additional program syntax or execution judgment.
-/

@[expose] public section

namespace Cslib.WordRAM.Realization

open Cslib.DataStructure

variable {B : Basis} {δ α : Type} {k l r : ℕ}

/-- A presence tag and unshifted payload distinguish `none` from every `some v`. -/
def optionWords : Option ℕ ↪ (Fin 2 → ℕ) where
  toFun
    | none => ![0, 0]
    | some v => ![1, v]
  inj' := by
    intro a b h
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some v => have hh := congrFun h 0; simp at hh
    | some u =>
      cases b with
      | none => have hh := congrFun h 0; simp at hh
      | some v => exact congrArg some (congrFun h 1)

@[simp] theorem optionWords_none : optionWords none = ![0, 0] := rfl
@[simp] theorem optionWords_some (v : ℕ) : optionWords (some v) = ![1, v] := rfl

/-- A Boolean tag with a retained zero slot supports native comparisons without immediates. -/
def boolWords : Bool ↪ (Fin 2 → ℕ) where
  toFun b := ![b.toNat, 0]
  inj' := by
    intro a b h
    have hh := congrFun h 0
    cases a <;> cases b <;> simp_all

@[simp] theorem boolWords_false : boolWords false = ![0, 0] := rfl
@[simp] theorem boolWords_true : boolWords true = ![1, 0] := rfl

private def coordinateSeq (code : Fin l → Code B r) (idle : Fin r) : List (Fin l) → Code B r
  | [] => .op (.copy idle idle)
  | i :: is => .seq (code i) (coordinateSeq code idle is)

private theorem coordinateSeq_glue (code : Fin l → Code B r) (idle : Fin r)
    (h : ∀ i, (code i).IsGlue) (is : List (Fin l)) : (coordinateSeq code idle is).IsGlue := by
  induction is with
  | nil => trivial
  | cons i is ih => exact ⟨h i, ih⟩

namespace Realizes

/-- Compute every output coordinate using actual certified scalar code. The common domain and
all coordinate envelopes remain visible, while code, exchange constant and scratch are uniform.
A final neutral copy pays for the empty result without materializing a non-fitting constant. -/
theorem glueVector (input : δ ↪ (Fin k → ℕ)) (output : α ↪ (Fin l → ℕ))
    (f : δ → α) (g bound : Fin l → (Fin k → ℕ) → ℕ) (time : Fin l → ℕ)
    {P : (Fin k → ℕ) → Prop}
    (hresult : ∀ d i, output (f d) i = g i (input d))
    (hcoord : ∀ i, GlueComputes B P (g i) (bound i) (time i)) :
    Realizes B (fun d => pure (f d)) input output
      (fun w d _ => P (input d) ∧ ∀ i, Fits w (bound i (input d)))
      (fun _ _ => (∑ i, time i) + l) := by
  classical
  choose n emit he using fun i => (hcoord i).2
  let N := ∑ i, n i
  have hn (i : Fin l) : n i ≤ N :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i)
  refine ⟨N, 1, fun _ src tmp =>
    coordinateSeq (fun i => .seq
      (emit i src (fun j => tmp ⟨l + j.val, by have := hn i; omega⟩))
      (.op (.copy (tmp (Fin.castAdd (N + 1) i)) (tmp ⟨l, by omega⟩))))
      (tmp ⟨l, by omega⟩) (List.finRange l), ?_⟩
  intro r frontier src tmp hi hd hf hs
  let dst : Fin l → Fin r := fun i => tmp (Fin.castAdd (N + 1) i)
  let aux : ∀ i : Fin l, Fin (n i + 1) → Fin r :=
    fun i j => tmp ⟨l + j.val, by have := hn i; omega⟩
  let scratch : Fin (N + 1) → Fin r := fun j => tmp ⟨l + j.val, by omega⟩
  let coord : Fin l → Code B r := fun i =>
    .seq (emit i src (aux i)) (.op (.copy (dst i) (scratch 0)))
  have hdsti : Function.Injective dst := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun a : Fin (l + N + 1) => a.val) (hi hij)
  have hauxi (i : Fin l) : Function.Injective (aux i) := by
    intro a b hab
    apply Fin.ext
    have h := congrArg (fun a : Fin (l + N + 1) => a.val) (hi hab)
    dsimp only [aux] at h
    omega
  have had (i : Fin l) (j : Fin k) (a : Fin (n i + 1)) : src j ≠ aux i a := hd _ _
  have hauxDst (i : Fin l) (j : Fin l) : ∀ a, aux i a ≠ dst j := by
    intro a h
    have hh := congrArg (fun a : Fin (l + N + 1) => a.val) (hi h)
    dsimp only [aux, dst] at hh
    simp only [Fin.val_castAdd] at hh
    omega
  have hcglue (i : Fin l) : (coord i).IsGlue :=
    ⟨(he i src (aux i) (hauxi i) (had i)).1, trivial⟩
  refine ⟨(coordinateSeq_glue coord (scratch 0) hcglue _).not_readsWidth, ?_⟩
  intro w d x hx hin hsafe hv
  have hruni (i : Fin l) (a : Data r) (ha : a.regs ∘ src = input d) :
      ∃ b, ExecWithin w (coord i) a b (time i + 1) ∧ b.mem = a.mem ∧
        b.regs ∘ src = input d ∧ b.regs (dst i) = output (f d) i ∧
        ∀ j, (∀ z, scratch z ≠ j) → dst i ≠ j → b.regs j = a.regs j := by
    obtain ⟨b, hb, hbo, hbm, hbf⟩ :=
      (he i src (aux i) (hauxi i) (had i)).2 w a (ha.symm ▸ hsafe.1)
        (ha.symm ▸ hsafe.2 i)
    let c := b.set (dst i) (g i (input d))
    have ho : b.regs (scratch 0) = g i (input d) := by
      have hz : aux i 0 = scratch 0 := by
        apply congrArg tmp
        apply Fin.ext
        rfl
      rw [← hz]
      simpa only [ha] using hbo
    have hc : ExecWithin (B := B) w (.op (.copy (dst i) (scratch 0))) b c 1 := by
      simpa only [ho] using
        (ExecWithin.copy (B := B) (w := w) (d := dst i) (s := scratch 0) (x := b))
    refine ⟨c, hb.seq hc, hbm, ?_, ?_, ?_⟩
    · funext j
      change c.regs (src j) = input d j
      rw [show c.regs (src j) = b.regs (src j) from Function.update_of_ne (hd _ _) _ _,
        hbf _ (fun a => (had i j a).symm)]
      exact congrFun ha j
    · change (b.set (dst i) _).regs (dst i) = _
      simp [Data.set, hresult]
    · intro j hsj hdj
      rw [show c.regs j = b.regs j from Function.update_of_ne hdj.symm _ _,
        hbf j (fun z => ?_)]
      exact hsj ⟨z.val, by have := hn i; omega⟩
  have hseq (is : List (Fin l)) (hnodup : is.Nodup) (a : Data r)
      (ha : a.regs ∘ src = input d) :
      ∃ b, ExecWithin w (coordinateSeq coord (scratch 0) is) a b
          ((is.map fun i => time i + 1).sum + 1) ∧
        b.mem = a.mem ∧ b.regs ∘ src = input d ∧
        (∀ i ∈ is, b.regs (dst i) = output (f d) i) ∧
        ∀ j, (∀ z, scratch z ≠ j) → (∀ i ∈ is, dst i ≠ j) → b.regs j = a.regs j := by
    induction is generalizing a with
    | nil =>
      have hself : ExecWithin (B := B) w (.op (.copy (scratch 0) (scratch 0))) a a 1 := by
        convert (ExecWithin.copy (B := B) (w := w) (d := scratch 0) (s := scratch 0)
          (x := a)) using 1
        apply Data.ext <;> simp [Data.set]
      exact ⟨a, hself, rfl, ha, by simp, fun _ _ _ => rfl⟩
    | cons i is ih =>
      obtain ⟨b, hb, hbm, hbs, hbo, hbf⟩ := hruni i a ha
      obtain ⟨c, hc, hcm, hcs, hco, hcf⟩ := ih hnodup.of_cons b hbs
      refine ⟨c, (hb.seq hc).mono (by simp; omega), hcm.trans hbm, hcs, ?_, ?_⟩
      · intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · rw [hcf _ (fun z => ?_) (fun j hj h => ?_)]
          · exact hbo
          · intro hh
            have hval := congrArg (fun a : Fin (l + N + 1) => a.val) (hi hh)
            dsimp only [scratch, dst] at hval
            simp only [Fin.val_castAdd] at hval
            omega
          · exact (List.nodup_cons.mp hnodup).1 (hdsti h ▸ hj)
        · exact hco j hj
      · intro j hsj hdj
        rw [hcf j hsj (fun i hi => hdj i (by simp [hi]))]
        exact hbf j hsj (hdj i (by simp))
  obtain ⟨y, hy, hym, _, hyo, hyf⟩ := hseq (List.finRange l) (List.nodup_finRange l) x hin
  refine ⟨y, hy.mono ?_, ?_, fun i => hyo i (by simp), ?_⟩
  · change ((List.finRange l).map fun i => time i + 1).sum + 1 ≤
      1 * (0 + ((∑ i, time i) + l) + 1)
    rw [← List.sum_toFinset (fun i => time i + 1) (List.nodup_finRange l)]
    simp [Finset.sum_add_distrib]
  · apply Memory.State.ext
    · exact hym
    · exact hyf frontier (fun _ => hf _) (fun _ _ => hf _)
  · intro i hif htmp
    exact hyf i (fun _ => htmp _) (fun _ _ => htmp _)

end Realizes
end Cslib.WordRAM.Realization
