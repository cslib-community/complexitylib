/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine.Call
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Cases

/-!
# Native space certificates for same-input calls

The composite stores a caller state or a suspended caller paired with a callee state.
These component certificates charge that compact encoded state, independently of the original
read-only input. Calls return the callee state; they do not accumulate its output stream.
-/

public section

namespace Turing.QueryMachine

open MultiTapeTM MultiTapeTM.ComputableInSpace

variable {σ τ : Type} (M : QueryMachine σ) (N : QueryMachine τ)
  (request : σ → Option τ) (resume : σ → τ → σ)
  (encS : σ ↪ List Bool) (encT : τ ↪ List Bool)

/-- A caller state pays only its payload and the sum tag. -/
theorem withCalls_encoding_inl_length (s : σ) :
    (encSum encS (encPair encS encT) (.inl s)).length = (encS s).length + 1 := rfl

/-- A suspended call stores one caller and one callee, with explicit framing overhead. -/
theorem withCalls_encoding_inr_length (s : σ) (t : τ) :
    (encSum encS (encPair encS encT) (.inr (s, t))).length =
      2 * (encS s).length + (encT t).length + 2 := by
  simp only [encSum_inr, List.length_cons, length_encPair]
  omega

/-- The composite halt test uses only the caller's halt test. -/
theorem withCalls_halted_inSpace
    (hhalted : ComputableInSpace M.halted encS encBool fun s => (encS s).length) :
    ComputableInSpace (M.withCalls N request resume).halted
      (encSum encS (encPair encS encT)) encBool
      (fun s => (encSum encS (encPair encS encT) s).length) := by
  exact (sumElim hhalted
    (budget_const (encIn := encPair encS encT) false (.refl _))).of_enc_eq
      fun s => by cases s <;> rfl

/-- Only the caller contributes the final output word. -/
theorem withCalls_finish_inSpace
    (hfinish : ComputableInSpace M.finish encS encBits fun s => (encS s).length) :
    ComputableInSpace (M.withCalls N request resume).finish
      (encSum encS (encPair encS encT)) encBits
      (fun s => (encSum encS (encPair encS encT) s).length) := by
  exact (sumElim hfinish
    (budget_const (encIn := encPair encS encT) [] (.refl _))).of_enc_eq
      fun s => by cases s <;> rfl

/-- A call queries the original input through its active machine, without copying that input. -/
theorem withCalls_query_inSpace
    (hqueryM : ComputableInSpace M.query encS encNat fun s => (encS s).length)
    (hqueryN : ComputableInSpace N.query encT encNat fun t => (encT t).length)
    (hrequest : ComputableInSpace request encS (encOption encT)
      fun s => (encS s).length) :
    ComputableInSpace (M.withCalls N request resume).query
      (encSum encS (encPair encS encT)) encNat
      (fun s => (encSum encS (encPair encS encT) s).length) := by
  have hid : ComputableInSpace (fun s : σ => s) encS encS
      (fun s => (encS s).length) := of_inO ComputableInDegree.id'.inO_one
  have hleft := budget_comp_linear
    (optionElimSnd hqueryM
      (budget_const (encIn := encPair encS encT) (encB := encNat) 0 (.refl _)))
    (budget_prod hid hrequest)
  have hright := budget_comp_linear hqueryN (snd encS encT)
  refine (sumElim hleft hright).of_enc_eq ?_
  rintro (s | ⟨s, t⟩)
  · cases h : request s <;> simp [withCalls, h]
  · rfl

/-- The callee output stream is discarded, so only ordinary caller steps emit. -/
theorem withCalls_emit_inSpace
    (hemit : ComputableInSpace M.emit (encPair encS (encOption encBool)) encBits
      fun p => (encPair encS (encOption encBool) p).length)
    (hrequest : ComputableInSpace request encS (encOption encT)
      fun s => (encS s).length) :
    ComputableInSpace (M.withCalls N request resume).emit
      (encPair (encSum encS (encPair encS encT)) (encOption encBool)) encBits
      (fun p => (encPair (encSum encS (encPair encS encT)) (encOption encBool) p).length) := by
  let encSB := encPair encS (encOption encBool)
  have hid : ComputableInSpace (fun p : σ × Option Bool => p) encSB encSB
      (fun p => (encSB p).length) := of_inO ComputableInDegree.id'.inO_one
  have hreq := budget_comp_linear hrequest (fst encS (encOption encBool))
  have hleft := budget_comp_linear
    (optionElimSnd hemit
      (budget_const (encIn := encPair encSB encT) (encB := encBits) [] (.refl _)))
    (budget_prod hid hreq)
  refine (sumElimFst hleft
    (budget_const (encIn := encPair (encPair encS encT) (encOption encBool))
      (encB := encBits) [] (.refl _))).of_enc_eq ?_
  rintro ⟨s | ⟨s, t⟩, b⟩
  · cases h : request s <;> simp [withCalls, h]
  · rfl

/-- Entering, running and returning from a call preserve linear compact-state space. -/
theorem withCalls_next_inSpace
    (hnextM : ComputableInSpace M.next (encPair encS (encOption encBool)) encS
      fun p => (encPair encS (encOption encBool) p).length)
    (hnextN : ComputableInSpace N.next (encPair encT (encOption encBool)) encT
      fun p => (encPair encT (encOption encBool) p).length)
    (hhaltedN : ComputableInSpace N.halted encT encBool fun t => (encT t).length)
    (hrequest : ComputableInSpace request encS (encOption encT)
      fun s => (encS s).length)
    (hresume : ComputableInSpace (fun p : σ × τ => resume p.1 p.2)
      (encPair encS encT) encS fun p => (encPair encS encT p).length) :
    ComputableInSpace (M.withCalls N request resume).next
      (encPair (encSum encS (encPair encS encT)) (encOption encBool))
      (encSum encS (encPair encS encT))
      (fun p => (encPair (encSum encS (encPair encS encT)) (encOption encBool) p).length) := by
  let encSB := encPair encS (encOption encBool)
  let encST := encPair encS encT
  have hinl := of_inO (ComputableInO.inl encS encST)
  have hinr := of_inO (ComputableInO.inr encS encST)
  have hid : ComputableInSpace (fun p : σ × Option Bool => p) encSB encSB
      (fun p => (encSB p).length) := of_inO ComputableInDegree.id'.inO_one
  have hnormal := budget_comp_linear hinl hnextM
  have henter := budget_comp_linear hinr
    (budget_prod (fst' (fst encSB encT)) (snd encSB encT))
  have hreq := budget_comp_linear hrequest (fst encS (encOption encBool))
  have hleft := budget_comp_linear (optionElimSnd hnormal henter)
    (budget_prod hid hreq)
  have hs := fst' (fst encST (encOption encBool))
  have ht := snd' (fst encST (encOption encBool))
  have hb := snd encST (encOption encBool)
  have hcallee := budget_comp_linear hnextN (budget_prod ht hb)
  have hrun := budget_comp_linear hinr (budget_prod hs hcallee)
  have hreturn := budget_comp_linear hinl
    (budget_comp_linear hresume (fst encST (encOption encBool)))
  have hhalt := budget_comp_linear hhaltedN ht
  have hright := budget_ite hhalt hreturn hrun
  refine (sumElimFst hleft hright).of_enc_eq ?_
  rintro ⟨s | ⟨s, t⟩, b⟩
  · cases h : request s <;> simp [withCalls, h, encST]
  · rfl

end Turing.QueryMachine
