/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/
module
-- upstream: candidate
public import CslibFrontier.Crypto.Computational.Encryption.Authenticated
public import CslibFrontier.Crypto.Computational.MAC
import CslibFrontier.Crypto.Computational.PseudorandomFunction.RandomOracle
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Oracle.Tidy
import CslibFrontier.Crypto.Game.Hybrid
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Probability.BitString.List
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT

public section
namespace Cslib.Crypto
open Cslib.Probability ProbComp OracleComp BitString Turing.MultiTapeTM

noncomputable def macThenEncrypt (E : SymmetricCipher) (M : MACScheme)
  (h_dec : ∀ n ke km msg tag,
    ke ∈ (ProbComp.eval (E.keyGen n)).support →
    km ∈ (ProbComp.eval (M.keyGen n)).support →
    msg.length = n →
    tag ∈ (ProbComp.eval (M.sign km msg)).support →
    ∀ ct ∈ (ProbComp.eval (E.encrypt n ke (encPair encBits encBits (msg, tag)))).support,
    E.decrypt n ke ct = some (encPair encBits encBits (msg, tag))) : SymmetricCipher where
  keyGen n := do
    let ke ← E.keyGen n
    let km ← M.keyGen n
    return encPair encBits encBits (ke, km)
  encrypt n k msg := do
    let tag ← M.sign (dropFrame k) msg
    E.encrypt n (unframe k) (encPair encBits encBits (msg, tag))
  decrypt n k ct := do
    let p ← E.decrypt n (unframe k) ct
    let msg := unframe p
    let tag := dropFrame p
    if encPair encBits encBits (msg, tag) == p && M.verify (dropFrame k) msg tag then
      some msg
    else
      none
  keyGen_ppt := by ppt
  encrypt_ppt := by ppt
  decrypt_polyTime := by polyTime
  decrypt_encrypt := by
    intro n k hk msg hmsg ct hct
    simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
      PMF.mem_support_pure_iff] at hk hct
    obtain ⟨ke, hke, km, hkm, rfl⟩ := hk
    have hunframe_k : unframe (encPair encBits encBits (ke, km)) = ke := by
      simp [encPair_apply, unframe_frame_append]
    have hdrop_k : dropFrame (encPair encBits encBits (ke, km)) = km := by
      simp [encPair_apply, dropFrame_frame_append]
    rw [hunframe_k, hdrop_k] at hct
    obtain ⟨tag, htag, hct2⟩ := hct
    have hdec : E.decrypt n ke ct = some (encPair encBits encBits (msg, tag)) :=
      h_dec n ke km msg tag hke hkm hmsg htag ct hct2
    have hunframe_p : unframe (encPair encBits encBits (msg, tag)) = msg := by
      simp [encPair_apply, unframe_frame_append]
    have hdrop_p : dropFrame (encPair encBits encBits (msg, tag)) = tag := by
      simp [encPair_apply, dropFrame_frame_append]
    have hver : M.verify km msg tag = true := M.verify_sign n km hkm msg hmsg tag htag
    rw [hunframe_k, hdrop_k, hdec]
    simp [hunframe_p, hdrop_p, hver]

noncomputable def extendCipher (E : SymmetricCipher) : SymmetricCipher where
  keyGen := E.keyGen
  encrypt n k msg := do
    let c ← E.encrypt n k msg
    return c ++ [false]
  decrypt n k ct :=
    if ct.length == 0 then none else
      E.decrypt n k (ct.take (ct.length - 1))
  keyGen_ppt := E.keyGen_ppt
  encrypt_ppt := by ppt
  decrypt_polyTime := by polyTime
  decrypt_encrypt := by
    intro n k hk msg hmsg ct hct
    simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
      PMF.mem_support_pure_iff] at hct
    obtain ⟨c, hc, rfl⟩ := hct
    have hdec : E.decrypt n k c = some msg := E.decrypt_encrypt n k hk msg hmsg c hc
    have ht : (c ++ [false]).length = c.length + 1 := by simp
    have hne0 : (c ++ [false]).length ≠ 0 := by rw [ht]; exact Nat.succ_ne_zero _
    have heq : (c ++ [false]).take ((c ++ [false]).length - 1) = c := by
      rw [ht, Nat.add_sub_cancel]
      exact List.take_left c [false]
    simp [hne0, heq, hdec]

end Cslib.Crypto
