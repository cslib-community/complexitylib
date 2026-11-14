/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MQOM.CorrelatedTree

/-!
# MQOM correlated-tree and validation-transcript clients

These clients pin the convention-sensitive behavior of MQOM v3 Algorithms 22--23 and Definition
2: one-based heap nodes, bottom-up sibling paths, newest-first transcripts, failed-query accounting,
and a final accepted output that was not among the preceding calls.
-/

public section

namespace CslibFrontierTests.Crypto.MQOMCorrelatedTree

open Cslib.Crypto.MQOM

-- With `N = 8`, leaf five is node 13 and has bottom-up siblings 12, 7 and 2.
example : leafNode (⟨5, by decide⟩ : LeafIndex 3) = 13 := by decide
example : siblingPathNodes (⟨5, by decide⟩ : LeafIndex 3) = [12, 7, 2] := by decide

-- A different leaf checks that the sibling path is not accidentally root-first.
example : siblingPathNodes (⟨0, by decide⟩ : LeafIndex 3) = [9, 5, 3] := by decide

/-- The designated two-coordinate prefix. -/
def secretPrefix : ValidationPrefix Bool 2 := fun i => decide (i = 0)

/-- A wrong candidate differing in the first coordinate. -/
def wrongPrefix : ValidationPrefix Bool 2 := fun _ => false

example : List.ofFn secretPrefix = [true, false] := by decide
example : validationReply secretPrefix wrongPrefix = false := by decide
example : validationReply secretPrefix secretPrefix = true := by decide

-- Calls are supplied chronologically but stored newest first, with failed calls retained.
example :
    (validationTranscript secretPrefix [wrongPrefix, secretPrefix]).map
        (fun entry => (List.ofFn entry.1, entry.2)) =
      [([true, false], true), ([false, false], false)] := by
  decide

/-- One failed call followed by a correct final output that was never queried. -/
def failedThenCorrect : ValidationRun Bool 2 where
  queries := [wrongPrefix]
  output := secretPrefix

example : failedThenCorrect.queryCount = 1 := by decide
example : secretPrefix ∉ failedThenCorrect.queries := by decide
example :
    (failedThenCorrect.transcript secretPrefix).map
        (fun entry => (List.ofFn entry.1, entry.2)) =
      [([false, false], false)] := by
  decide
example : failedThenCorrect.accepted secretPrefix = true := by decide

-- Repeated failed calls are separate entries and separate queries.
example : (validationTranscript secretPrefix [wrongPrefix, wrongPrefix]).length = 2 := by decide

end CslibFrontierTests.Crypto.MQOMCorrelatedTree
