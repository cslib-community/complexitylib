/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.EXP
public import CslibFrontier.Computability.Complexity.Classes.Hierarchy.LazyDiagonal
public import CslibFrontier.Computability.Complexity.Classes.Hierarchy.Time
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.BitLength
import CslibFrontier.Computability.Complexity.Classes.Hierarchy.LazyDiagonalBounds
import CslibFrontier.Computability.Complexity.Classes.Time.BoundedExists
import CslibFrontier.Computability.Complexity.Classes.Time.Verifier
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.TwoPow
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential
import CslibFrontier.Tactic.EncLen

/-!
# A nondeterministic exponential time hierarchy by lazy diagonalization

For every `k`, nondeterministic time `O(2 ^ (k * n))` is strictly contained in nondeterministic
time `O(2 ^ (e * n))` on bit strings whenever `8 * k + 16 ≤ e`
(`Cslib.Complexity.NTIME_two_pow_ssubset_NTIME_two_pow_of_le`). In particular `NE` is not contained
in `NTIME (2 ^ (k * n))` for any `k` (`Cslib.Complexity.exists_mem_NE_notMem_NTIME_two_pow`). This
is a coarse exponential form of the nondeterministic time hierarchy theorem
[Arora and Barak, Theorem 3.3][AroraBarak07], proved by lazy diagonalization [Žák][Zak1983].
The separating problem is explicit: `Cslib.Complexity.expLazyDiagonal k`.

Padding transfers inclusions between nondeterministic time classes only upward, so the
polynomial hierarchy of `Cslib.Complexity.NTIME_succ_pow_ssubset_NTIME_succ_pow_of_le` does not give
this separation; the lazy diagonal is run again with exponential certificates.

## The lazy diagonal

The exponential lazy diagonal is the generic construction `Cslib.Complexity.Diagonal.lazyLanguage`
with certificates of length `certLen k m = 2 ^ ((k + 1) * (m + 1))` on words of length `m`, the step
budget `((frame y ++ v).length + 1) ^ 2` on the pair `(y, v)`, and the horizon
`horizon k m = 2 ^ ((k + 2) * (m + 1))`: the interval of a word `w` ends below `2 ^ horizon k P`,
where `P = 2 * w.length + 1`.

* **Upper bound** (`Cslib.Complexity.expLazyDiagonal_mem_NTIME`). Guess the certificate and run the
  verifier (`Cslib.Complexity.setOf_exists_mem_NTIME`). The simulation takes time polynomial in the
  certificate, `O(2 ^ ((8 * k + 16) * n))`. The brute force takes time `2 ^ O(certLen k P)`
  (`Cslib.Complexity.exists_computableInO_any_enumList`), which is `O(n)` at the end of the
  interval, where `n + 1 = 2 ^ horizon k P` and `horizon k P = 2 ^ (P + 1) * certLen k P`.
* **Lower bound** (`Cslib.Complexity.expLazyDiagonal_notMem_NTIME`). A verifier for a problem in
  `NTIME (2 ^ (k * n))` accepts certificates of every length at least `c * 2 ^ (k * n) + c`, and
  runs within `c₂` times its input length; `certLen k` and the step budget eventually exceed both
  (`Cslib.Complexity.Diagonal.lazyLanguage_notMem_NTIME`).

Unlike `Cslib.Complexity.lazyDiagonal`, the simulation clock is the square of the length of the
simulated pair rather than a function of the input length alone. It is then polynomial in the
certificate, so the brute force at the end of an interval is a polynomial-time test tried on every
certificate.

## Main definitions

* `Cslib.Complexity.ExpLazyDiagonal.verifier`: the verifier of the lazy diagonal for `k`.
* `Cslib.Complexity.expLazyDiagonal`: the exponential lazy diagonal problem for `k`.

## Main results

* `Cslib.Complexity.expLazyDiagonal_mem_NTIME`: the lazy diagonal is in
  `NTIME (2 ^ ((8 * k + 16) * n))`.
* `Cslib.Complexity.expLazyDiagonal_notMem_NTIME`: the lazy diagonal is not in
  `NTIME (2 ^ (k * n))`.
* `Cslib.Complexity.NTIME_two_pow_ssubset_NTIME_two_pow_of_le`: the hierarchy.
* `Cslib.Complexity.exists_mem_NE_notMem_NTIME_two_pow`: `NE ⊄ NTIME (2 ^ (k * n))`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft of January
  2007][AroraBarak07]
* [S. Žák, *A Turing machine time hierarchy*][Zak1983]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal

namespace ExpLazyDiagonal

/-- The certificate length of the lazy diagonal on words of length `m`:
`2 ^ ((k + 1) * (m + 1))`. -/
def certLen (k m : ℕ) : ℕ := 2 ^ ((k + 1) * (m + 1))

/-- The horizon of the lazy diagonal: the interval of lengths starting at `m` ends below
`2 ^ horizon k m`, where `horizon k m = 2 ^ ((k + 2) * (m + 1)) = 2 ^ (m + 1) * certLen k m`. -/
def horizon (k m : ℕ) : ℕ := 2 ^ ((k + 2) * (m + 1))

/-- The machine described by `c`, run as a verifier on the pair `(y, v)` with the universal
function for `((frame y ++ v).length + 1) ^ 2` steps, has halted with output `[true]`. -/
def accepts : List Bool → List Bool → List Bool → Bool :=
  Diagonal.lazyAccepts fun y v => ((frame y ++ v).length + 1) ^ 2

/-- **The verifier of the exponential lazy diagonal** (`Cslib.Complexity.Diagonal.lazyVerifier`)
with the budget `((frame y ++ v).length + 1) ^ 2` for the pair `(y, v)`, certificates of length
`certLen k` and horizon `horizon k`. -/
def verifier (k : ℕ) : List Bool × List Bool → Bool :=
  Diagonal.lazyVerifier (fun y v => ((frame y ++ v).length + 1) ^ 2) (certLen k) (horizon k)

end ExpLazyDiagonal

open ExpLazyDiagonal

/-- **The exponential lazy diagonal language** for `k`: the words `x` with a certificate of length
`2 ^ ((k + 1) * (x.length + 2))` accepted by `Cslib.Complexity.ExpLazyDiagonal.verifier k`. -/
def expLazyDiagonal (k : ℕ) : Set (List Bool) :=
  Diagonal.lazyLanguage (fun y v => ((frame y ++ v).length + 1) ^ 2) (certLen k) (horizon k)

/-! ### The lazy diagonal is not in `NTIME (2 ^ (k * n))` -/

/-- The lengths at which certificates of length `certLen k m` suffice for a verifier with constant
`c`. -/
private theorem exists_le_certLen (k c : ℕ) :
    ∃ M, ∀ m, M ≤ m → c * 2 ^ (k * m) + c ≤ certLen k m := by
  refine ⟨c, fun m hm => ?_⟩
  have hc : 2 * c ≤ 2 ^ (m + 1) := by
    have := Nat.lt_two_pow_self (n := m)
    rw [pow_succ]; omega
  have e : certLen k m = 2 ^ (k * m) * 2 ^ k * 2 ^ (m + 1) := by
    simp only [certLen, ← pow_add]; congr 1; ring
  rw [e]
  calc c * 2 ^ (k * m) + c ≤ 2 * c * 2 ^ (k * m) := by
        rw [two_mul, add_mul]
        exact Nat.add_le_add_left (Nat.le_mul_of_pos_right _ Nat.one_le_two_pow) _
    _ ≤ 2 ^ (m + 1) * 2 ^ (k * m) := Nat.mul_le_mul_right _ hc
    _ ≤ 2 ^ (k * m) * 2 ^ k * 2 ^ (m + 1) := by
      rw [mul_comm (2 ^ (m + 1)), mul_assoc]
      exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ Nat.one_le_two_pow)

/-- **The exponential lazy diagonal is not decidable in nondeterministic time
`O(2 ^ (k * n))`** (`Cslib.Complexity.Diagonal.lazyLanguage_notMem_NTIME`): certificates of length
`certLen k m` eventually suffice for a verifier of a problem in that class, and so do
`((frame y ++ v).length + 1) ^ 2` simulated steps on the pair `(y, v)`. -/
theorem expLazyDiagonal_notMem_NTIME (k : ℕ) :
    expLazyDiagonal k ∉ NTIME encBits fun n => 2 ^ (k * n) :=
  Diagonal.lazyLanguage_notMem_NTIME (exists_le_certLen k)
    (fun c₂ => ⟨c₂, fun y v hy _ => by
      simp only [encPair_apply, encBits_apply, List.length_append, length_frame, sq]
      exact Nat.mul_le_mul_right _ (by omega)⟩)
    fun P => by
      have : P + 1 ≤ horizon k P :=
        Nat.lt_two_pow_self.le.trans
          (Nat.pow_le_pow_right Nat.one_lt_two.le (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)))
      exact this.trans_lt Nat.lt_two_pow_self

/-! ### The lazy diagonal is in nondeterministic exponential time -/

/-- The bound on the simulation of `Cslib.Complexity.ExpLazyDiagonal.accepts`, for a decoder of
degree below `D`: polynomial in the description, the input and the certificate. -/
private def accBound (D : ℕ) (q : List Bool × List Bool × List Bool) : ℕ :=
  ((q.1.length + 1) ^ D + q.2.1.length + q.2.2.length + 1) ^ 4 *
    ((frame q.2.1 ++ q.2.2).length + 1) ^ 4

/-- The binary length of the clock is linear in the length of the simulated word. -/
private theorem length_encNat_sq_le (W : ℕ) : (encNat ((W + 1) ^ 2)).length ≤ 2 * (W + 1) := by
  rw [encNat_apply, Nat.size_eq_bits_len, Nat.size_le, mul_comm, pow_mul]
  exact Nat.pow_lt_pow_left Nat.lt_two_pow_self (by omega)

/-- The simulation runs within time polynomial in the description, the input and the
certificate. -/
private theorem exists_computableInO_accepts : ∃ D, ComputableInO
    (fun q : List Bool × List Bool × List Bool => accepts q.1 q.2.1 q.2.2)
    (encPair encBits (encPair encBits encBits)) encBool (accBound D) (accBound D) := by
  obtain ⟨dd, ed, hdec⟩ := exists_computableInDegree_decodeDesc
  set enc := encPair encBits (encPair encBits encBits)
  have hdesc := hdec.inO.comp (ComputableInO.fst encBits (encPair encBits encBits))
  have hword : ComputableInO (fun q : List Bool × List Bool × List Bool => frame q.2.1 ++ q.2.2)
      enc encBits (fun q => (enc q).length) (fun q => (enc q).length) :=
    (ComputableInO.snd encBits (encPair encBits encBits)).of_enc_eq fun _ => rfl
  have hsym := Universal.computableTidilyInDegree_map_eBit.inO_one.computableInO.comp hword
  have hclock := timeConstructible_succ_sq.computableInO.comp hword
  have hU := computableInO_universal.comp (hdesc.prod (hsym.prod hclock))
  have hv := Diagonal.computableInO_verdict.comp hU
  have hnot := (ComputableInDegree.of_finite (encIn := encBool) (encMid := encBool)
    (fun b : Bool => !b)).inO_one.comp hv
  obtain ⟨cD, hcD⟩ := hdesc.length_le
  obtain ⟨cO, hcO⟩ := hU.length_le
  obtain ⟨K, hK⟩ := LazyDiagonal.accBound_aux 0 cD cO
  have hbounds (q : List Bool × List Bool × List Bool) := by
    have hD := hcD q
    have hE := hcO q
    have hNl := length_encList_map_eBit_le (frame q.2.1 ++ q.2.2)
    have hc : q.1.length + 1 ≤ (q.1.length + 1) ^ (dd + 1) :=
      Nat.le_self_pow (Nat.succ_ne_zero _) _
    have hA : (q.1.length + 1) ^ dd ≤ (q.1.length + 1) ^ (dd + 1) :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_succ _)
    have hL := length_encNat_sq_le (frame q.2.1 ++ q.2.2).length
    simp only [Function.comp_apply, encBits_apply, enc, length_encPair, List.length_append,
      length_frame] at hD hE hNl hL ⊢
    exact hK (X := (q.1.length + 1) ^ (dd + 1) + q.2.1.length + q.2.2.length + 1)
      (by omega) (by omega) (by omega) hD hNl (by omega) (by omega)
      (Nat.one_le_pow _ _ (Nat.succ_pos _)) hE
  have e (q : List Bool × List Bool × List Bool) : accBound (dd + 1) q =
      ((q.1.length + 1) ^ (dd + 1) + q.2.1.length + q.2.2.length + 1) ^ 4 *
        (((frame q.2.1 ++ q.2.2).length + 1) ^ 2) ^ 2 := by
    rw [accBound, ← pow_mul]
  have hb (b : Bool) : (encBool b).length = 1 := rfl
  refine ⟨dd + 1, (hnot.mono K (fun q => ?_) fun q => ?_).of_enc_eq fun q => rfl⟩
  all_goals
    refine le_trans ?_ (Nat.mul_le_mul_left K (Nat.le_succ _))
    rw [e]
    have ⟨h₁, h₂⟩ := hbounds q
    enc_len [Function.comp_apply, enc, hb] at h₁ h₂ ⊢

/-- The numeric facts behind the bound of the brute force: the encoded pair of length `N`, the
certificate length `c`, the unary certificate length and the search. -/
private theorem brute_bound_aux (C K₀ N c : ℕ) (hc : 1 ≤ c) :
    N + (C * 2 ^ N + c * c) + 2 ^ (K₀ * (2 * N + 1 + c + c)) ≤
      (C + 3) * (2 ^ ((3 * K₀ + 4) * (N + c)) + 1) := by
  set B := 2 ^ ((3 * K₀ + 4) * (N + c))
  have hN : 2 ^ N ≤ B :=
    Nat.pow_le_pow_right Nat.one_lt_two.le
      ((Nat.le_add_right N c).trans (Nat.le_mul_of_pos_left _ (by omega)))
  have hN' : N < 2 ^ N := Nat.lt_two_pow_self
  have hcc : c * c ≤ B := by
    have h₁ : c * c ≤ 2 ^ (c + c) := by
      rw [pow_add]
      exact Nat.mul_le_mul Nat.lt_two_pow_self.le Nat.lt_two_pow_self.le
    exact h₁.trans (Nat.pow_le_pow_right Nat.one_lt_two.le
      ((by omega : c + c ≤ 4 * (N + c)).trans (Nat.mul_le_mul_right _ (by omega))))
  have hs : 2 ^ (K₀ * (2 * N + 1 + c + c)) ≤ B :=
    Nat.pow_le_pow_right Nat.one_lt_two.le
      ((Nat.mul_le_mul_left K₀ (by omega : 2 * N + 1 + c + c ≤ 3 * (N + c))).trans
        ((le_of_eq (by ring : K₀ * (3 * (N + c)) = 3 * K₀ * (N + c))).trans
          (Nat.mul_le_mul_right _ (by omega))))
  have hC : C * 2 ^ N ≤ C * B := Nat.mul_le_mul_left _ hN
  have e : (C + 3) * (B + 1) = C * B + 3 * B + (C + 3) := by ring
  omega

attribute [local fun_prop] ComputableInPolyTime.fst' ComputableInPolyTime.snd' in
/-- The brute force at the end of an interval runs within time exponential in the description,
the input and the certificate length. The certificate length is first written in unary, and every
certificate of that length is tried with the polynomial-time simulation. -/
private theorem exists_computableInO_brute (k : ℕ) : ∃ K, ComputableInO
    (fun q : List Bool × List Bool =>
      (Cslib.BitString.enumList (certLen k q.2.length)).any (accepts q.1 q.2))
    (encPair encBits encBits) encBool
    (fun q => 2 ^ (K * ((encPair encBits encBits q).length + certLen k q.2.length)))
    (fun q => 2 ^ (K * ((encPair encBits encBits q).length + certLen k q.2.length))) := by
  obtain ⟨D, hacc⟩ := exists_computableInO_accepts
  set encQ := encPair encBits encBits with hencQ
  set encB := encPair encQ encUnary with hencB
  set enc := encPair encB encBits with henc
  -- the search, with the certificate length given in unary
  have hB := ComputableInO.fst encB encBits
  have hre := (hB.fst'.fst').prod (hB.fst'.snd'.prod (ComputableInO.snd encB encBits))
  have hf := hacc.comp hre
  have hlen (r : ((List Bool × List Bool) × ℕ) × List Bool) :
      r.1.1.1.length ≤ (enc r).length ∧ r.1.1.2.length ≤ (enc r).length ∧
        r.2.length ≤ (enc r).length ∧ (encB r.1).length ≤ (enc r).length := by
    have e₁ : (enc r).length = 2 * (encB r.1).length + 1 + r.2.length := by
      rw [henc, length_encPair, encBits_apply]
    have e₂ : (encB r.1).length = 2 * (encQ r.1.1).length + 1 + r.1.2 := by
      rw [hencB, length_encPair, encUnary_apply, List.length_replicate]
    have e₃ : (encQ r.1.1).length = 2 * r.1.1.1.length + 1 + r.1.1.2.length := by
      rw [hencQ, length_encPair, encBits_apply, encBits_apply]
    omega
  have hf' : ComputableInO (fun r : ((List Bool × List Bool) × ℕ) × List Bool =>
      accepts r.1.1.1 r.1.1.2 r.2) enc encBool
      (fun r => 6 * (enc r).length + accBound D (r.1.1.1, r.1.1.2, r.2))
      (fun r => 6 * (enc r).length + accBound D (r.1.1.1, r.1.1.2, r.2)) := by
    refine hf.mono_le (fun r => ?_) (fun r => ?_) <;>
    · rw [← henc]
      omega
  have hpoly : PolyBounded (fun r => (enc r).length) fun r =>
      6 * (enc r).length + accBound D (r.1.1.1, r.1.1.2, r.2) :=
    (PolyBounded.of_polynomiallyBounded (fun r => (enc r).length)
      (bound := fun n => 6 * n + ((n + 1) ^ D + n + n + 1) ^ 4 * (2 * n + 1 + n + 1) ^ 4)
      (by fun_prop)).mono fun r => by
        obtain ⟨h₁, h₂, h₃, -⟩ := hlen r
        simp only [accBound, List.length_append, length_frame]
        gcongr
  have hℓ : ComputableInPolyTime (fun b : (List Bool × List Bool) × ℕ => b.2) encB encUnary := by
    fun_prop
  obtain ⟨K₀, hsearch⟩ := exists_computableInO_any_enumList hf' hpoly hpoly hℓ
  -- the certificate length in unary
  have hL : ComputableInPolyTime (fun q : List Bool × List Bool => (k + 1) * (q.2.length + 1))
      encQ encUnary := by
    fun_prop
  obtain ⟨C, hcl⟩ := hL.exists_computableInO_unary_two_pow
  have hpair := (ComputableInO.of_eq (f := fun q : List Bool × List Bool => q) (encIn := encQ)
    (encMid := encQ) fun _ => rfl).prod hcl
  have h := hsearch.comp hpair
  -- the bounds
  refine ⟨3 * K₀ + 4, (h.mono (C + 3) (fun q => ?_) fun q => ?_).of_enc_eq fun q => rfl⟩
  all_goals
    have e₁ : (encB (q, 2 ^ ((k + 1) * (q.2.length + 1)))).length =
        2 * (encQ q).length + 1 + 2 ^ ((k + 1) * (q.2.length + 1)) := by
      rw [hencB, length_encPair, encUnary_apply, List.length_replicate]
    have e₂ : (4 : ℕ) ^ ((k + 1) * (q.2.length + 1)) =
        2 ^ ((k + 1) * (q.2.length + 1)) * 2 ^ ((k + 1) * (q.2.length + 1)) := by
      rw [← mul_pow]
      norm_num
    have hc : 1 ≤ 2 ^ ((k + 1) * (q.2.length + 1)) := Nat.one_le_two_pow
    have h := brute_bound_aux C K₀ (encQ q).length _ hc
    have hcc := Nat.le_mul_of_pos_left (2 ^ ((k + 1) * (q.2.length + 1))) hc
    simp only [e₁, e₂, certLen] at h ⊢
    omega

/-- The cost of the tests of the verifier: quadratic in the encoded input, times the square of a
bound `4 ^ ((k + 2) * (n + 1))` on the horizon, which the tests write in unary. -/
private def cheap (k : ℕ) (p : List Bool × List Bool) : ℕ :=
  ((encPair encBits encBits p).length + 1) ^ 2 * (4 ^ ((k + 2) * (p.1.length + 1))) ^ 2

/-- The horizon of the interval of `unframe x` is at most `4 ^ ((k + 2) * (x.length + 1))`, and the
cost of writing it in unary is at most twice that bound plus its square. -/
private theorem horizon_le (k C : ℕ) (x : List Bool) :
    horizon k (2 * (unframe x).length + 1) ≤ 4 ^ ((k + 2) * (x.length + 1)) ∧
      C * 2 ^ (2 * (unframe x).length + 1) + 4 ^ ((k + 2) * (2 * (unframe x).length + 1 + 1)) ≤
        2 * C * 4 ^ ((k + 2) * (x.length + 1)) + (4 ^ ((k + 2) * (x.length + 1))) ^ 2 := by
  have hu := length_unframe_le x
  have h4 (a : ℕ) : (4 : ℕ) ^ a = 2 ^ (2 * a) := by rw [pow_mul]; norm_num
  have hk : (k + 2) * (2 * (unframe x).length + 1 + 1) ≤ 2 * ((k + 2) * (x.length + 1)) :=
    (Nat.mul_le_mul_left (k + 2)
      (by omega : 2 * (unframe x).length + 1 + 1 ≤ 2 * (x.length + 1))).trans_eq (by ring)
  refine ⟨?_, ?_⟩
  · rw [horizon, h4]
    exact Nat.pow_le_pow_right Nat.one_lt_two.le hk
  · have h₁ : 2 ^ (2 * (unframe x).length + 1) ≤ 2 * 4 ^ ((k + 2) * (x.length + 1)) := by
      rw [h4, pow_succ, mul_comm]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right Nat.one_lt_two.le
        ((by omega : 2 * (unframe x).length ≤ 2 * (x.length + 1)).trans
          (Nat.mul_le_mul_left 2 (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)))))
    have h₂ : 4 ^ ((k + 2) * (2 * (unframe x).length + 1 + 1)) ≤
        (4 ^ ((k + 2) * (x.length + 1))) ^ 2 := by
      rw [← pow_mul, mul_comm ((k + 2) * _)]
      exact Nat.pow_le_pow_right (by norm_num) hk
    have := Nat.mul_le_mul_left C h₁
    have e : C * (2 * 4 ^ ((k + 2) * (x.length + 1))) = 2 * C * 4 ^ ((k + 2) * (x.length + 1)) := by
      ring
    omega

attribute [local fun_prop] ComputableInPolyTime.fst' ComputableInPolyTime.snd' in
/-- **The verifier of the exponential lazy diagonal is computable**, within the cost of its tests
plus the cost of the branch taken: the simulation, or the brute force at the end of an interval. -/
private theorem exists_computableInO_verifier (k : ℕ) :
    ∃ (D K : ℕ) (S : List Bool × List Bool → ℕ),
    ComputableInO (verifier k) (encPair encBits encBits) encBool
      (fun p => cheap k p + if Diagonal.shortDesc (unframe p.1) then
        (cheap k p + if Nat.size (p.1.length + 1) ≤ horizon k (2 * (unframe p.1).length + 1) then
          cheap k p + accBound D (unframe (unframe p.1), p.1 ++ [false], p.2)
        else (cheap k p + if Nat.size p.1.length ≤ horizon k (2 * (unframe p.1).length + 1) then
          cheap k p + 2 ^ (K * ((encPair encBits encBits (unframe (unframe p.1),
            frame (unframe p.1))).length + certLen k (2 * (unframe p.1).length + 1)))
          else cheap k p))
        else cheap k p) S := by
  obtain ⟨D, hacc⟩ := exists_computableInO_accepts
  obtain ⟨K, hbrute⟩ := exists_computableInO_brute k
  have hx := ComputableInO.fst encBits encBits
  have hun : ComputableInO unframe encBits encBits (fun z => z.length) (fun z => z.length) :=
    ComputableInO.of_linear (.of_unframe fun _ => rfl)
  have hfr : ComputableInO frame encBits encBits (fun z => z.length) (fun z => z.length) :=
    ComputableInO.of_linear (.of_frame fun _ => rfl)
  have hw := hun.comp hx
  have hcode := hun.comp hw
  have hbase := hfr.comp hw
  have hsnoc : ComputableInO (fun p : List Bool × List Bool => p.1 ++ [false])
      (encPair encBits encBits) encBits
      (fun p => (encPair encBits encBits p).length + (encPair encBits encBits p).length)
      (fun p => (encPair encBits encBits p).length + (encPair encBits encBits p).length) :=
    hx.append (ComputableInO.const (encMid := encBits) [false]) fun _ => rfl
  have hsz : ComputableInO (fun z : List Bool => Nat.size z.length) encBits encUnary
      (fun z => (z.length + 1) ^ 2 + (encNat z.length).length)
      (fun z => z.length + 1 + (encNat z.length).length) :=
    (ComputableInO.lengthUnary.comp ((ComputableInO.lengthNat.mono 1
      (T' := fun z : List Bool => (z.length + 1) ^ 2) (S' := fun z => z.length + 1)
      (fun z => by nlinarith) fun z => by omega).of_enc_eq (encC := encBits)
      (g := fun z : List Bool => encNat z.length) fun _ => rfl)).of_enc_eq fun z => by
        simp [encNat_apply, Nat.size_eq_bits_len]
  have hL : ComputableInPolyTime (fun z : List Bool => (k + 2) * (z.length + 1)) encBits
      encUnary := by
    fun_prop
  obtain ⟨CE, hE₀⟩ := hL.exists_computableInO_unary_two_pow
  have hE := hE₀.comp hbase
  -- the numeric facts about the tests
  have hfacts (p : List Bool × List Bool) : (unframe p.1).length ≤ p.1.length ∧
      p.1.length ≤ (encPair encBits encBits p).length ∧
      (encPair encBits encBits p).length + 1 ≤ cheap k p ∧
      (horizon k (2 * (unframe p.1).length + 1) + 1) ^ 2 ≤ 25 * cheap k p ∧
      (2 * (encPair encBits encBits p).length + 4 +
        horizon k (2 * (unframe p.1).length + 1)) ^ 2 ≤ 25 * cheap k p ∧
      CE * 2 ^ (2 * (unframe p.1).length + 1) +
        4 ^ ((k + 2) * (2 * (unframe p.1).length + 1 + 1)) ≤ (2 * CE + 1) * cheap k p := by
    have hu := length_unframe_le p.1
    have hn : p.1.length ≤ (encPair encBits encBits p).length := by enc_len
    obtain ⟨hZ, hE'⟩ := horizon_le k CE p.1
    set Y := 4 ^ ((k + 2) * (p.1.length + 1))
    have hY : 1 ≤ Y := Nat.one_le_pow _ _ (by norm_num)
    obtain ⟨h₁, h₂, h₃⟩ := LazyDiagonal.cheap_aux 1 hn hY
      (Z := horizon k (2 * (unframe p.1).length + 1)) (by omega)
    have hc : cheap k p = ((encPair encBits encBits p).length + 1) ^ 2 * Y ^ 2 := rfl
    have hY₁ : Y ≤ Y ^ 2 := Nat.le_self_pow two_ne_zero _
    have hY₂ : Y ^ 2 ≤ cheap k p := by
      rw [hc]; exact Nat.le_mul_of_pos_left _ (Nat.pow_pos (Nat.succ_pos _))
    have e : (2 * CE + 1) * cheap k p = 2 * CE * cheap k p + cheap k p := by ring
    have := Nat.mul_le_mul_left (2 * CE) (hY₁.trans hY₂)
    norm_num only at h₂ h₃
    rw [hc]
    exact ⟨hu, hn, hc ▸ h₁, h₂, h₃, by rw [← hc]; omega⟩
  set A := 8 + 4 * 25 + (2 * CE + 1)
  have e (p : List Bool × List Bool) : A * (cheap k p + 1) =
      8 * cheap k p + 4 * (25 * cheap k p) + (2 * CE + 1) * cheap k p + A := by ring
  have hc₀ := ComputableInO.mono_time (Diagonal.computableInO_shortDesc.comp hw) (T' := cheap k)
      A fun p => by
    obtain ⟨hu, hn, h₁, -, h₃, -⟩ := hfacts p
    have : ((unframe p.1).length + 1) ^ 2 ≤ (2 * (encPair encBits encBits p).length + 4 +
        horizon k (2 * (unframe p.1).length + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    simp only [Function.comp_apply] at ⊢
    have := e p; omega
  have hc₁ := (ComputableInO.mono_time (ComputableInO.unaryLe.comp ((hsz.comp hsnoc).prod hE))
      (T' := cheap k) A fun p => by
    obtain ⟨hu, hn, h₁, h₂, h₃, h₄⟩ := hfacts p
    have hs := Nat.size_le.mpr (Nat.lt_two_pow_self (n := p.1.length + 1))
    have he := Universal.length_encNat_le (p.1.length + 1)
    have hsq : (p.1.length + 1 + 1) ^ 2 ≤ (2 * (encPair encBits encBits p).length + 4 +
        horizon k (2 * (unframe p.1).length + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hsq' : (2 * Nat.size (p.1.length + 1) + 1 + horizon k (2 * (unframe p.1).length + 1)
        + 1) ^ 2 ≤ (2 * (encPair encBits encBits p).length + 4 +
          horizon k (2 * (unframe p.1).length + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    simp only [Function.comp_apply, length_encPair (enc₁ := encUnary) (enc₂ := encUnary),
      encUnary_apply, List.length_replicate, List.length_append, List.length_singleton,
      length_frame, encBits_apply] at ⊢
    simp only [horizon] at hsq hsq' h₂ h₃
    have := e p; omega).of_enc_eq (encC := encBool) (g := fun p : List Bool × List Bool =>
      decide (Nat.size (p.1.length + 1) ≤ horizon k (2 * (unframe p.1).length + 1))) fun p => by
    simp only [Function.comp_apply, horizon, length_frame, List.length_append,
      List.length_singleton]
    rfl
  have hc₂ := (ComputableInO.mono_time (ComputableInO.unaryLe.comp ((hsz.comp hx).prod hE))
      (T' := cheap k) A fun p => by
    obtain ⟨hu, hn, h₁, h₂, h₃, h₄⟩ := hfacts p
    have hs := Nat.size_le.mpr (Nat.lt_two_pow_self (n := p.1.length))
    have he := Universal.length_encNat_le p.1.length
    have hsq : (p.1.length + 1) ^ 2 ≤ (2 * (encPair encBits encBits p).length + 4 +
        horizon k (2 * (unframe p.1).length + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hsq' : (2 * Nat.size p.1.length + 1 + horizon k (2 * (unframe p.1).length + 1)
        + 1) ^ 2 ≤ (2 * (encPair encBits encBits p).length + 4 +
          horizon k (2 * (unframe p.1).length + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    simp only [Function.comp_apply, length_encPair (enc₁ := encUnary) (enc₂ := encUnary),
      encUnary_apply, List.length_replicate, length_frame, encBits_apply] at ⊢
    simp only [horizon] at hsq hsq' h₂ h₃
    have := e p; omega).of_enc_eq (encC := encBool) (g := fun p : List Bool × List Bool =>
      decide (Nat.size p.1.length ≤ horizon k (2 * (unframe p.1).length + 1))) fun p => by
    simp only [Function.comp_apply, horizon, length_frame]
    rfl
  have hf₁ := ComputableInO.mono_time
      (hacc.comp (hcode.prod (hsnoc.prod (ComputableInO.snd encBits encBits))))
      (T' := fun p => cheap k p + accBound D (unframe (unframe p.1), p.1 ++ [false], p.2)) 7
      fun p => by
    obtain ⟨hu, hn, h₁, -⟩ := hfacts p
    simp only [Function.comp_apply] at ⊢
    have e : 7 * (cheap k p + accBound D (unframe (unframe p.1), p.1 ++ [false], p.2) + 1) =
        7 * cheap k p + 7 * accBound D (unframe (unframe p.1), p.1 ++ [false], p.2) + 7 := by
      ring
    omega
  have hf₂ := ComputableInO.mono_time ((ComputableInDegree.of_finite (encIn := encBool)
    (encMid := encBool) (fun b : Bool => !b)).inO_one.comp (hbrute.comp (hcode.prod hbase)))
      (T' := fun p => cheap k p + 2 ^ (K * ((encPair encBits encBits (unframe (unframe p.1),
        frame (unframe p.1))).length + certLen k (2 * (unframe p.1).length + 1)))) 7
      fun p => by
    obtain ⟨hu, hn, h₁, -⟩ := hfacts p
    have hb : (encBool ((Cslib.BitString.enumList (certLen k (frame (unframe p.1)).length)).any
        (accepts (unframe (unframe p.1)) (frame (unframe p.1))))).length = 1 := rfl
    simp only [Function.comp_apply, hb] at ⊢
    rw [length_frame]
    set B := 2 ^ (K * ((encPair encBits encBits (unframe (unframe p.1),
        frame (unframe p.1))).length + certLen k (2 * (unframe p.1).length + 1)))
    have e : 7 * (cheap k p + B + 1) = 7 * cheap k p + 7 * B + 7 := by ring
    omega
  have hfalse := ComputableInO.mono_time (ComputableInO.const (encIn := encPair encBits encBits)
    (encMid := encBool) false) (T' := cheap k) 1 fun p => by
    obtain ⟨hu, hn, h₁, -⟩ := hfacts p; omega
  have h := hc₀.ite (hc₁.ite hf₁ (hc₂.ite hf₂ hfalse)) hfalse
  refine ⟨D, K, _, (h.of_enc_eq fun p => ?_).mono_le (fun p => le_of_eq ?_) fun p => le_rfl⟩
  · congr 1
    simp only [verifier, Diagonal.lazyVerifier, accepts, Function.comp_apply, decide_eq_true_eq,
      length_frame]
  · simp only [Function.comp_apply, decide_eq_true_eq]

/-- `2 ^ a ≤ 2 ^ b * 2 ^ c` whenever `a ≤ c + b`. -/
private theorem two_pow_le_two_pow_mul {a b c : ℕ} (h : a ≤ c + b) : 2 ^ a ≤ 2 ^ b * 2 ^ c := by
  rw [← pow_add]
  exact Nat.pow_le_pow_right Nat.one_lt_two.le (by omega)

/-- **The exponential lazy diagonal is decidable in nondeterministic time
`O(2 ^ ((8 * k + 16) * n))`.** Guess a certificate of length `2 ^ ((k + 1) * (n + 2))` and run the
verifier (`Cslib.Complexity.setOf_exists_mem_NTIME`). Below the end of an interval, the verifier
simulates a verifier on the input one bit longer with a certificate of that length, within time
polynomial in the certificate. At the end of an interval of start `P`, it tries every certificate
on the input of length `P`, within time `2 ^ O(certLen k P)`, which is linear in the length `n` of
the input, since `n + 1 = 2 ^ horizon k P` there and `horizon k P = 2 ^ (P + 1) * certLen k P`. -/
theorem expLazyDiagonal_mem_NTIME (k : ℕ) :
    expLazyDiagonal k ∈ NTIME encBits fun n => 2 ^ ((8 * k + 16) * n) := by
  obtain ⟨D, K, S, hV⟩ := exists_computableInO_verifier k
  have hL : ComputableInPolyTime (fun x : List Bool => (k + 1) * (x.length + 2)) encBits
      encUnary := by
    fun_prop
  obtain ⟨Cℓ, hℓ₀⟩ := hL.exists_computableInO_unary_two_pow
  have hℓ := hℓ₀.of_enc_eq (encC := encUnary)
    (g := fun x : List Bool => certLen k (x.length + 1)) fun x => rfl
  obtain ⟨CD, hCD⟩ := PolynomiallyBounded.exists_le_mul_two_pow (p := fun m => (m + 1) ^ D)
    (by fun_prop)
  set B₀ := 3 * K * 2 ^ ((k + 1) * (3 * K)) with hB₀
  set A₁ := 2 ^ (8 * k + 14) with hA₁
  set A₂ := 81 * (CD + 3) ^ 4 * 2 ^ (16 * k + 16) with hA₂
  set A₃ := Cℓ + 2 ^ (4 * k + 4) with hA₃
  refine setOf_exists_mem_NTIME hℓ hV (C := 2 + A₃ + 4 * A₁ + A₂ + 2 ^ B₀) fun x v hv => ?_
  clear hL hℓ₀ hℓ hV
  simp only [encBits_apply]
  set n := x.length with hn
  set V := 2 ^ ((k + 1) * (n + 2)) with hVdef
  have hv' : v.length = V := hv
  set M := 2 ^ ((8 * k + 16) * n) with hM
  have hnV : 4 * n + 4 ≤ V :=
    calc 4 * n + 4 ≤ 2 ^ (n + 2) := by
          have := Nat.lt_two_pow_self (n := n)
          rw [pow_succ, pow_succ]; omega
      _ ≤ V := Nat.pow_le_pow_right Nat.one_lt_two.le (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
  have h₁ : 2 ^ n ≤ M :=
    Nat.pow_le_pow_right Nat.one_lt_two.le (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
  have hnM : n + 1 ≤ M := Nat.lt_two_pow_self.trans_le h₁
  -- the certificate length
  have hTℓ : Cℓ * 2 ^ n + 4 ^ ((k + 1) * (n + 2)) ≤ A₃ * M := by
    have h₂ : 4 ^ ((k + 1) * (n + 2)) ≤ 2 ^ (4 * k + 4) * M := by
      rw [show (4 : ℕ) = 2 ^ 2 by rfl, ← pow_mul]
      exact two_pow_le_two_pow_mul (by ring_nf; omega)
    have e : A₃ * M = Cℓ * M + 2 ^ (4 * k + 4) * M := by ring
    have := Nat.mul_le_mul_left Cℓ h₁
    omega
  -- the tests
  have hcheap : cheap k (x, v) ≤ A₁ * M := by
    have hN : (encPair encBits encBits (x, v)).length + 1 ≤ 2 * V := by enc_len [hv', ← hn]
    calc cheap k (x, v) = ((encPair encBits encBits (x, v)).length + 1) ^ 2 *
          (4 ^ ((k + 2) * (n + 1))) ^ 2 := rfl
      _ ≤ (2 * V) ^ 2 * (4 ^ ((k + 2) * (n + 1))) ^ 2 :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hN 2)
      _ = 2 ^ (2 + 2 * ((k + 1) * (n + 2)) + 4 * ((k + 2) * (n + 1))) := by
          rw [hVdef, show (4 : ℕ) = 2 ^ 2 by rfl]
          simp only [mul_pow, ← pow_mul, ← pow_add]
          ring_nf
      _ ≤ A₁ * M := two_pow_le_two_pow_mul (by ring_nf; omega)
  -- the simulation, when the description is short
  have hacc (h₀ : Diagonal.shortDesc (unframe x) = true) :
      accBound D (unframe (unframe x), x ++ [false], v) ≤ A₂ * M := by
    have hs : 2 ^ (unframe (unframe x)).length ≤ (unframe x).length := of_decide_eq_true h₀
    have hu := length_unframe_le x
    have hD : ((unframe (unframe x)).length + 1) ^ D ≤ CD * n :=
      (hCD _).trans (Nat.mul_le_mul_left _ (hs.trans hu))
    have hb : ((unframe (unframe x)).length + 1) ^ D + (n + 1) + V + 1 ≤ (CD + 3) * V := by
      have h₂ : CD * n ≤ CD * V := Nat.mul_le_mul_left _ (by omega)
      have e : (CD + 3) * V = CD * V + 3 * V := by ring
      omega
    have hw : (frame (x ++ [false]) ++ v).length + 1 ≤ 3 * V := by
      simp only [List.length_append, length_frame, List.length_singleton, hv', ← hn]; omega
    calc accBound D (unframe (unframe x), x ++ [false], v) =
          (((unframe (unframe x)).length + 1) ^ D + (n + 1) + V + 1) ^ 4 *
            ((frame (x ++ [false]) ++ v).length + 1) ^ 4 := by
          simp only [accBound, List.length_append, List.length_singleton, hv', ← hn]
      _ ≤ ((CD + 3) * V) ^ 4 * (3 * V) ^ 4 :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hb 4) (Nat.pow_le_pow_left hw 4)
      _ = 81 * (CD + 3) ^ 4 * 2 ^ (8 * ((k + 1) * (n + 2))) := by
          rw [hVdef]
          simp only [mul_pow, ← pow_mul]
          ring
      _ ≤ 81 * (CD + 3) ^ 4 * (2 ^ (16 * k + 16) * M) :=
          Nat.mul_le_mul_left _ (two_pow_le_two_pow_mul (by ring_nf; omega))
      _ = A₂ * M := by ring
  clear_value B₀ A₁ A₂ A₃ M V
  -- the brute force, at the end of an interval
  have hbrute (h₁ : ¬Nat.size (n + 1) ≤ horizon k (2 * (unframe x).length + 1)) :
      2 ^ (K * ((encPair encBits encBits (unframe (unframe x), frame (unframe x))).length +
        certLen k (2 * (unframe x).length + 1))) ≤ n + 1 + 2 ^ B₀ := by
    set P := 2 * (unframe x).length + 1 with hP
    have hE : 2 ^ horizon k P ≤ n + 1 := by
      rw [Nat.size_le, not_lt] at h₁
      exact h₁
    have hc := length_unframe_le (unframe x)
    have hPc : P + 1 ≤ certLen k P :=
      Nat.lt_two_pow_self.le.trans
        (Nat.pow_le_pow_right Nat.one_lt_two.le (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)))
    have hlen : (encPair encBits encBits (unframe (unframe x), frame (unframe x))).length +
        certLen k P ≤ 3 * certLen k P := by enc_len
    rcases le_or_gt (3 * K) (2 ^ (P + 1)) with hK | hK
    · have hle : K * ((encPair encBits encBits (unframe (unframe x), frame (unframe x))).length +
          certLen k P) ≤ horizon k P :=
        calc _ ≤ K * (3 * certLen k P) := Nat.mul_le_mul_left _ hlen
          _ = 3 * K * certLen k P := by ring
          _ ≤ 2 ^ (P + 1) * certLen k P := Nat.mul_le_mul_right _ hK
          _ = horizon k P := by
              rw [certLen, horizon, ← pow_add]; congr 1; ring
      exact ((Nat.pow_le_pow_right Nat.one_lt_two.le hle).trans hE).trans (Nat.le_add_right _ _)
    · have hP3 : P + 1 ≤ 3 * K := (Nat.lt_two_pow_self.trans hK).le
      have hle : K * ((encPair encBits encBits (unframe (unframe x), frame (unframe x))).length +
          certLen k P) ≤ B₀ :=
        calc _ ≤ K * (3 * certLen k P) := Nat.mul_le_mul_left _ hlen
          _ = 3 * K * certLen k P := by ring
          _ ≤ B₀ := by
              rw [hB₀]
              exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right Nat.one_lt_two.le
                (Nat.mul_le_mul_left _ hP3))
      exact (Nat.pow_le_pow_right Nat.one_lt_two.le hle).trans (Nat.le_add_left _ _)
  clear hB₀ hA₁ hA₂ hA₃ hM hVdef hCD
  have e : (2 + A₃ + 4 * A₁ + A₂ + 2 ^ B₀) * M =
      2 * M + A₃ * M + 4 * (A₁ * M) + A₂ * M + 2 ^ B₀ * M := by ring
  have hB : 2 ^ B₀ ≤ 2 ^ B₀ * M :=
    Nat.le_mul_of_pos_right _ (Nat.lt_of_lt_of_le (Nat.succ_pos _) hnM)
  generalize 2 + A₃ + 4 * A₁ + A₂ + 2 ^ B₀ = C at *
  generalize 2 ^ B₀ = Q at *
  split_ifs with h₀ h₁ h₂
  · have := hacc h₀
    omega
  · have := hbrute h₁
    omega
  · omega
  · omega

/-! ### The hierarchy -/

/-- **A nondeterministic exponential time hierarchy.** For every `k`, nondeterministic time
`O(2 ^ (k * n))` is strictly contained in nondeterministic time `O(2 ^ (e * n))` whenever
`8 * k + 16 ≤ e`. The exponential lazy diagonal `Cslib.Complexity.expLazyDiagonal k` separates them
(`Cslib.Complexity.expLazyDiagonal_mem_NTIME`, `Cslib.Complexity.expLazyDiagonal_notMem_NTIME`).
This is a coarse exponential form of the nondeterministic time hierarchy theorem
[Arora and Barak, Theorem 3.3][AroraBarak07]. -/
theorem NTIME_two_pow_ssubset_NTIME_two_pow_of_le {k e : ℕ} (h : 8 * k + 16 ≤ e) :
    NTIME encBits (fun n => 2 ^ (k * n)) ⊂ NTIME encBits fun n => 2 ^ (e * n) := by
  have hsub : ∀ {a b : ℕ}, a ≤ b →
      NTIME encBits (fun n => 2 ^ (a * n)) ⊆ NTIME encBits fun n => 2 ^ (b * n) :=
    fun hab => NTIME_mono fun n => Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ hab)
  exact (Set.ssubset_iff_of_subset (hsub (by omega))).mpr
    ⟨expLazyDiagonal k, hsub h (expLazyDiagonal_mem_NTIME k), expLazyDiagonal_notMem_NTIME k⟩

/-- **`NE` is not contained in `NTIME (2 ^ (k * n))`**, for any `k`: the exponential lazy diagonal
`Cslib.Complexity.expLazyDiagonal k` is in `NE` and not in `NTIME (2 ^ (k * n))`. -/
theorem exists_mem_NE_notMem_NTIME_two_pow (k : ℕ) :
    ∃ H ∈ NE encBits, H ∉ NTIME encBits fun n => 2 ^ (k * n) :=
  ⟨expLazyDiagonal k, Set.mem_iUnion.mpr ⟨_, expLazyDiagonal_mem_NTIME k⟩,
    expLazyDiagonal_notMem_NTIME k⟩

end Cslib.Complexity
