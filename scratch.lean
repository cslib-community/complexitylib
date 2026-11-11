import CslibFrontier.Computability.Complexity.FineGrained.LCS

open Cslib.Complexity.OV
open Cslib.Algorithms.Lean.EditDistance
open Turing.MultiTapeTM
open Cslib.Complexity

theorem comp_extractA : ComputableInO extractA encOV encOV
  (fun p => (encOV p).length + 1) (fun p => (encOV p).length + 1) := by
  have id : ComputableInO (fun p : _ × _ => p) encOV encOV _ _ := ComputableInO.of_linear (.of_eq fun _ => rfl)
  have fst : ComputableInO (fun p : _ × _ => p.1) encOV (encList encBits) _ _ :=
    ComputableInO.fst' (enc₁ := encList encBits) (enc₂ := encList encBits) id
  have nil : ComputableInO (fun p : _ × _ => ([] : List (List Bool))) encOV (encList encBits) _ _ :=
    ComputableInO.const []
  have pair := ComputableInO.prod fst nil
  exact pair.mono 2 (fun p => by omega) (fun p => by omega)

