/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
public import Mathlib.Data.ZMod.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinarySizeFacts
import Complexity.Tactic.EncLen
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn

/-!
# Canonical field coordinates from padded register points

The raw evaluator stores each register coordinate with modulus padding. Reducing the actual
stored point modulo that modulus gives the canonical unsigned coordinates used by the gate
interpolation specification. Reduction preserves list length and never enlarges a cell encoding.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.NormalizePoint

open MultiTapeTM MultiTapeTM.ComputableInSpace

/-- Reduce every explicitly stored coordinate to its canonical residue. -/
@[expose] def normalize (p : ℕ) (point : List ℕ) : List ℕ := point.map (fun v => v % p)

/-- Modulus and actual stored point. -/
abbrev Args := ℕ × List ℕ

/-- Both the modulus and the complete point storage are charged. -/
@[expose] noncomputable def encArgs : Args ↪ List Bool := encPair encNat (encList encNat)

/-- Canonicalization preserves the actual number of point coordinates. -/
theorem length_normalize (p : ℕ) (point : List ℕ) :
    (normalize p point).length = point.length := List.length_map ..

/-- Coordinate lookup commutes with normalization, with zero as the missing-coordinate value. -/
theorem getD_normalize (p : ℕ) (point : List ℕ) (i : ℕ) :
    (normalize p point).getD i 0 = point.getD i 0 % p := by
  simpa only [normalize, Nat.zero_mod] using
    (List.getD_map point 0 (n := i) (fun v => v % p))

/-- Normalization does not change the field point, including missing coordinates. -/
theorem getD_normalize_cast (p : ℕ) (point : List ℕ) (i : ℕ) :
    ((normalize p point).getD i 0 : ZMod p) = (point.getD i 0 : ZMod p) := by
  rw [getD_normalize, ZMod.natCast_mod]

/-- The evaluator's padded coordinates reduce to their canonical unsigned field values. -/
theorem normalize_ofFn {p n : ℕ} (hp : 0 < p) (x : Fin n → ZMod p) :
    normalize p (List.ofFn (fun i => p + (x i).val)) =
      List.ofFn (fun i => (x i).val) := by
  have : NeZero p := ⟨hp.ne'⟩
  simp only [normalize, List.map_ofFn]
  congr 1
  funext i
  change (p + (x i).val) % p = (x i).val
  rw [Nat.add_mod_left, Nat.mod_eq_of_lt (ZMod.val_lt (x i))]

private theorem length_enc_normalize_le (p : ℕ) (point : List ℕ) :
    (encList encNat (normalize p point)).length ≤ (encList encNat point).length := by
  apply length_encList_map_le encNat encNat
  intro v _hv
  exact ComputableTidilyInO.length_encNat_mono (Nat.mod_le v p)

private theorem fold_normalize (p : ℕ) (point out : List ℕ) :
    point.foldl (fun acc v => acc ++ [v % p]) out = out ++ normalize p point := by
  induction point generalizing out with
  | nil => simp [normalize]
  | cons v point ih => simp [List.foldl_cons, normalize, ih, List.append_assoc]

/-- Native reduction uses space linear in actual modulus and point storage. -/
theorem normalize_inSpace :
    ComputableInSpace (fun a : Args => normalize a.1 a.2) encArgs (encList encNat)
      (fun a => (encArgs a).length) := by
  have hp := fst encNat (encList encNat)
  have hl := snd encNat (encList encNat)
  have hinit : ComputableInSpace (fun _ : Args => ([] : List ℕ)) encArgs (encList encNat)
      (fun a => (encArgs a).length) := budget_const [] (.refl _)
  have hstep : ComputableInSpace (fun a : (ℕ × List ℕ) × ℕ => a.1.2 ++ [a.2 % a.1.1])
      (encPair (encPair encNat (encList encNat)) encNat) (encList encNat)
      (fun a => (encPair (encPair encNat (encList encNat)) encNat a).length) := by
    have hs := fst (encPair encNat (encList encNat)) encNat
    have hv := snd (encPair encNat (encList encNat)) encNat
    exact budget_snoc hs.snd' (budget_natMod hv hs.fst')
  have hstates (a : Args) (i : ℕ) (_hi : i ≤ a.2.length) :
      (encList encNat ((a.2.take i).foldl (fun acc v => acc ++ [v % a.1]) [])).length ≤
        (encArgs a).length := by
    rw [fold_normalize, List.nil_append]
    have hn := length_enc_normalize_le a.1 (a.2.take i)
    have ht := length_encList_take_le encNat a.2 i
    enc_len [encArgs]
  have hspace (a : Args) (i : ℕ) (hi : i < a.2.length) :
      (encPair (encPair encNat (encList encNat)) encNat
        ((a.1, (a.2.take i).foldl (fun acc v => acc ++ [v % a.1]) []), a.2[i])).length ≤
          16 * ((encArgs a).length + 1) := by
    have hs := hstates a i hi.le
    have hv := length_le_encList_of_mem encNat (List.getElem_mem hi)
    enc_len [encArgs] at *
  have hfold := ComputableInSpace.foldlWith
    (encIn := encArgs) (encP := encNat) (encA := encNat) (encL := encList encNat)
    (encB := encList encNat) (par := fun a : Args => a.1) (list := fun a : Args => a.2)
    (init := fun _ : Args => ([] : List ℕ))
    (step := fun p acc v => acc ++ [v % p])
    (Sp := fun a => (encArgs a).length) (Sl := fun a => (encArgs a).length)
    (Si := fun a => (encArgs a).length)
    (Q := fun a => 16 * ((encArgs a).length + 1)) (B := fun a => (encArgs a).length)
    hp hl hinit hstep hspace hstates
  refine hfold.weaken (.of_le_linear 100 100 fun a => by enc_len [encArgs]) |>.of_enc_eq ?_
  intro a
  simp only [fold_normalize, List.nil_append]

end Turing.MultiTapePTM.BlockComputation.NormalizePoint
