/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Hierarchy.LazyDiagonal
public import CslibFrontier.Computability.Complexity.Classes.Hierarchy.Time
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.BitLength
import CslibFrontier.Computability.Complexity.Classes.Hierarchy.LazyDiagonalBounds
import CslibFrontier.Computability.Complexity.Classes.Time.BoundedExists
import CslibFrontier.Computability.Complexity.Classes.Time.Verifier
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential
import CslibFrontier.Tactic.EncLen

/-!
# A nondeterministic time hierarchy by lazy diagonalization

For every degree `d`, nondeterministic time `O((n + 1) ^ d)` is strictly contained in
nondeterministic time `O((n + 1) ^ e)` on bit strings whenever `6 * d + 14 ≤ e`
(`Cslib.Complexity.NTIME_succ_pow_ssubset_NTIME_succ_pow_of_le`). This is a coarse form of the
nondeterministic time hierarchy theorem [Arora and Barak, Theorem 3.3][AroraBarak07], proved by
lazy diagonalization [Žák][Zak1983]. The separating problem is explicit: the lazy diagonal
`Cslib.Complexity.lazyDiagonal d`.

## The lazy diagonal

The lazy diagonal is the generic construction `Cslib.Complexity.Diagonal.lazyLanguage` with
certificates of length `certLen d m = (m + 1) ^ (d + 2)` on words of length `m`, and the clock
`clock d m = (m + 1) ^ (d + 3)` as both the step budget on the input `y` (`clock d y.length`) and
the horizon: the interval of a word `w` ends below `2 ^ clock d P`, where `P = 2 * w.length + 1`.

* **Upper bound** (`Cslib.Complexity.lazyDiagonal_mem_NTIME`). Guess the certificate and run the
  verifier (`Cslib.Complexity.setOf_exists_mem_NTIME`). The simulation takes time
  `O((n + 1) ^ (6 * d + 14))`: polynomial in the input, the certificate and the clock, through the
  native universal machine. The brute force takes time `2 ^ O((P + 1) ^ (d + 2))`
  (`Cslib.Complexity.exists_computableInO_any_enumList`), which is `O(n)` at the end of the
  interval, where `n + 1 = 2 ^ ((P + 1) ^ (d + 3))`.
* **Lower bound** (`Cslib.Complexity.lazyDiagonal_notMem_NTIME`). A verifier for a problem in
  `NTIME ((n + 1) ^ d)` accepts certificates of every length at least `c * (n + 1) ^ d + c`, and
  runs within `c₂` times its input length; `certLen d` and `clock d` eventually exceed both
  (`Cslib.Complexity.Diagonal.lazyLanguage_notMem_NTIME`).

The gap `6 * d + 14` is the polynomial overhead of the native universal machine and of the
certificate length, not the textbook `f (n + 1) = o (g n)`.

## Main definitions

* `Cslib.Complexity.LazyDiagonal.verifier`: the verifier of the lazy diagonal for degree `d`.
* `Cslib.Complexity.lazyDiagonal`: the lazy diagonal problem for degree `d`.

## Main results

* `Cslib.Complexity.lazyDiagonal_mem_NTIME`: the lazy diagonal is in
  `NTIME ((n + 1) ^ (6 * d + 14))`.
* `Cslib.Complexity.lazyDiagonal_notMem_NTIME`: the lazy diagonal is not in `NTIME ((n + 1) ^ d)`.
* `Cslib.Complexity.NTIME_succ_pow_ssubset_NTIME_succ_pow_of_le`: the hierarchy.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft of January
  2007][AroraBarak07]
* [S. Žák, *A Turing machine time hierarchy*][Zak1983]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal

namespace LazyDiagonal

/-- The certificate length of the lazy diagonal on words of length `m`: `(m + 1) ^ (d + 2)`. -/
def certLen (d m : ℕ) : ℕ := (m + 1) ^ (d + 2)

/-- The clock of the lazy diagonal on words of length `m`: `(m + 1) ^ (d + 3)`. It bounds the
simulated steps on `m`, and the interval of lengths starting at `m` ends below `2 ^ clock d m`. -/
def clock (d m : ℕ) : ℕ := (m + 1) ^ (d + 3)

/-- The machine described by `c`, run as a verifier on the pair `(y, v)` for `clock d y.length`
steps with the universal function, has halted with output `[true]`. -/
def accepts (d : ℕ) : List Bool → List Bool → List Bool → Bool :=
  Diagonal.lazyAccepts fun y _ => clock d y.length

/-- **The verifier of the lazy diagonal** (`Cslib.Complexity.Diagonal.lazyVerifier`) with the
budget `clock d y.length` for the input `y`, certificates of length `certLen d` and horizon
`clock d`. -/
def verifier (d : ℕ) : List Bool × List Bool → Bool :=
  Diagonal.lazyVerifier (fun y _ => clock d y.length) (certLen d) (clock d)

end LazyDiagonal

open LazyDiagonal

/-- **The lazy diagonal language** for degree `d`: the words `x` with a certificate of length
`(x.length + 2) ^ (d + 2)` accepted by `Cslib.Complexity.LazyDiagonal.verifier d`. -/
def lazyDiagonal (d : ℕ) : Set (List Bool) :=
  Diagonal.lazyLanguage (fun y _ => clock d y.length) (certLen d) (clock d)

/-! ### The lazy diagonal is not in `NTIME ((n + 1) ^ d)` -/

/-- The lengths at which certificates of length `certLen d m` and `clock d m` simulated steps
suffice for a verifier with constants `c` and `c₂`. -/
private theorem exists_le_certLen_clock (d c c₂ : ℕ) : ∃ M, ∀ m, M ≤ m →
    c * (m + 1) ^ d + c ≤ certLen d m ∧ c₂ * (2 * m + 1 + certLen d m + 1) ≤ clock d m := by
  refine ⟨2 * c + 3 * c₂, fun m hm => ⟨?_, ?_⟩⟩
  · have hX : 1 ≤ (m + 1) ^ d := Nat.one_le_pow _ _ (by omega)
    have h₁ : c * (m + 1) ^ d + c ≤ (2 * c) * (m + 1) ^ d := by
      have := Nat.le_mul_of_pos_right c hX
      have : (2 * c) * (m + 1) ^ d = c * (m + 1) ^ d + c * (m + 1) ^ d := by ring
      omega
    have h₂ : 2 * c ≤ (m + 1) ^ 2 :=
      (by omega : 2 * c ≤ m + 1).trans (Nat.le_self_pow two_ne_zero _)
    exact h₁.trans ((Nat.mul_le_mul_right _ h₂).trans (le_of_eq (by simp only [certLen]; ring)))
  · have hX : 1 ≤ (m + 1) ^ d := Nat.one_le_pow _ _ (by omega)
    set Y := certLen d m
    have hY : m + 1 ≤ Y :=
      (Nat.le_self_pow two_ne_zero _).trans
        ((Nat.le_mul_of_pos_left _ hX).trans (le_of_eq (by simp only [Y, certLen]; ring)))
    have h₁ : c₂ * (2 * m + 1 + Y + 1) ≤ (3 * c₂) * Y :=
      (Nat.mul_le_mul_left c₂ (by omega : 2 * m + 1 + Y + 1 ≤ 3 * Y)).trans (le_of_eq (by ring))
    exact h₁.trans ((Nat.mul_le_mul_right Y (by omega : 3 * c₂ ≤ m + 1)).trans
      (le_of_eq (by simp only [Y, certLen, clock]; ring)))

/-- **The lazy diagonal is not decidable in nondeterministic time `O((n + 1) ^ d)`**
(`Cslib.Complexity.Diagonal.lazyLanguage_notMem_NTIME`): certificates of length `certLen d m` and
`clock d m` simulated steps eventually suffice for a verifier of a problem in that class. -/
theorem lazyDiagonal_notMem_NTIME (d : ℕ) :
    lazyDiagonal d ∉ NTIME encBits fun n => (n + 1) ^ d :=
  Diagonal.lazyLanguage_notMem_NTIME
    (fun c => (exists_le_certLen_clock d c 0).imp fun _ h m hm => (h m hm).1)
    (fun c₂ => (exists_le_certLen_clock d 0 c₂).imp fun _ h y v hy hv => by
      have := (h y.length hy).2
      simp only [encPair_apply, encBits_apply, List.length_append, length_frame, hv]
      omega)
    fun P => (Nat.le_self_pow (by omega) (P + 1)).trans_lt Nat.lt_two_pow_self

/-! ### The lazy diagonal is in nondeterministic polynomial time -/

/-- The bound on the simulation of `Cslib.Complexity.LazyDiagonal.accepts`, for a decoder of
degree below `D`. -/
private def accBound (d D : ℕ) (q : List Bool × List Bool × List Bool) : ℕ :=
  ((q.1.length + 1) ^ D + q.2.1.length + q.2.2.length + 1) ^ 4 * (q.2.1.length + 1) ^ (2 * d + 6)

/-- The binary length of the clock is linear in the length of the input. -/
private theorem length_encNat_clock_le (d y : ℕ) :
    (encNat ((y + 1) ^ (d + 3))).length ≤ (d + 3) * (y + 1) := by
  rw [encNat_apply, Nat.size_eq_bits_len, Nat.size_le, mul_comm, pow_mul]
  exact Nat.pow_lt_pow_left Nat.lt_two_pow_self (by omega)

/-- The simulation runs within time polynomial in the description, the input and the
certificate. -/
private theorem exists_computableInO_accepts (d : ℕ) : ∃ D, ComputableInO
    (fun q : List Bool × List Bool × List Bool => accepts d q.1 q.2.1 q.2.2)
    (encPair encBits (encPair encBits encBits)) encBool (accBound d D) (accBound d D) := by
  obtain ⟨dd, ed, hdec⟩ := exists_computableInDegree_decodeDesc
  set enc := encPair encBits (encPair encBits encBits)
  have hdesc := hdec.inO.comp (ComputableInO.fst encBits (encPair encBits encBits))
  have hword : ComputableInO (fun q : List Bool × List Bool × List Bool => frame q.2.1 ++ q.2.2)
      enc encBits (fun q => (enc q).length) (fun q => (enc q).length) :=
    (ComputableInO.snd encBits (encPair encBits encBits)).of_enc_eq fun _ => rfl
  have hsym := Universal.computableInO_map_eBit.comp hword
  have hy := (ComputableInO.snd encBits (encPair encBits encBits)).fst'
  have hclock := (timeConstructible_succ_pow (d + 3)).computableInO.comp hy
  have hU := computableInO_universal.comp (hdesc.prod (hsym.prod hclock))
  have hv := Diagonal.computableInO_verdict.comp hU
  have hnot := (ComputableInDegree.of_finite (encIn := encBool) (encMid := encBool)
    (fun b : Bool => !b)).inO_one.comp hv
  obtain ⟨cD, hcD⟩ := hdesc.length_le
  obtain ⟨cO, hcO⟩ := hU.length_le
  obtain ⟨K, hK⟩ := accBound_aux d cD cO
  have hbounds (q : List Bool × List Bool × List Bool) := by
    have hD := hcD q
    have hE := hcO q
    have hNl := length_encList_map_eBit_le (frame q.2.1 ++ q.2.2)
    have hc : q.1.length + 1 ≤ (q.1.length + 1) ^ (dd + 1) :=
      Nat.le_self_pow (Nat.succ_ne_zero _) _
    have hA : (q.1.length + 1) ^ dd ≤ (q.1.length + 1) ^ (dd + 1) :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_succ _)
    simp only [Function.comp_apply, encBits_apply, enc, length_encPair, List.length_append,
      length_frame] at hD hE hNl ⊢
    exact hK (X := (q.1.length + 1) ^ (dd + 1) + q.2.1.length + q.2.2.length + 1)
      (by omega) (by omega) (by omega) hD hNl
      ((length_encNat_clock_le d q.2.1.length).trans
        ((Nat.mul_le_mul_right _ (Nat.le_succ _)).trans (Nat.mul_le_mul_left (d + 4) (by omega))))
      (by omega) (Nat.one_le_pow _ _ (Nat.succ_pos _)) hE
  have e (q : List Bool × List Bool × List Bool) : accBound d (dd + 1) q =
      ((q.1.length + 1) ^ (dd + 1) + q.2.1.length + q.2.2.length + 1) ^ 4 *
        ((q.2.1.length + 1) ^ (d + 3)) ^ 2 := by
    rw [accBound, ← pow_mul, show (d + 3) * 2 = 2 * d + 6 by ring]
  have hb (b : Bool) : (encBool b).length = 1 := rfl
  refine ⟨dd + 1, (hnot.mono K (fun q => ?_) fun q => ?_).of_enc_eq fun q => rfl⟩
  all_goals
    refine le_trans ?_ (Nat.mul_le_mul_left K (Nat.le_succ _))
    rw [e]
    have ⟨h₁, h₂⟩ := hbounds q
    enc_len [Function.comp_apply, enc, hb] at h₁ h₂ ⊢

attribute [local fun_prop] ComputableInPolyTime.fst' ComputableInPolyTime.snd' in
/-- The brute force at the end of an interval runs within time exponential in the description,
the input and the certificate length. -/
private theorem exists_computableInO_brute (d : ℕ) : ∃ K, ComputableInO
    (fun q : List Bool × List Bool =>
      (Cslib.BitString.enumList (certLen d q.2.length)).any (accepts d q.1 q.2))
    (encPair encBits encBits) encBool
    (fun q => 2 ^ (K * ((encPair encBits encBits q).length + certLen d q.2.length)))
    (fun q => 2 ^ (K * ((encPair encBits encBits q).length + certLen d q.2.length))) := by
  obtain ⟨D, hacc⟩ := exists_computableInO_accepts d
  set enc := encPair (encPair encBits encBits) encBits
  have hre := ((ComputableInO.fst (encPair encBits encBits) encBits).fst').prod
    (((ComputableInO.fst (encPair encBits encBits) encBits).snd').prod
      (ComputableInO.snd (encPair encBits encBits) encBits))
  have hf := hacc.comp hre
  have hsize (q : (List Bool × List Bool) × List Bool) :
      q.1.1.length ≤ (enc q).length ∧ q.1.2.length ≤ (enc q).length ∧
        q.2.length ≤ (enc q).length := by enc_len [enc]
  have hpoly : PolyBounded (fun q => (enc q).length) fun q =>
      (enc q).length + ((enc q).length + (enc q).length) +
        accBound d D (q.1.1, q.1.2, q.2) :=
    ((PolyBounded.self.add (PolyBounded.self.add .self)).add
      ((PolyBounded.of_polynomiallyBounded (fun q => (enc q).length)
        (bound := fun n => ((n + 1) ^ D + n + n + 1) ^ 4 * (n + 1) ^ (2 * d + 6))
        (by fun_prop)).mono fun q => by
          obtain ⟨h₁, h₂, h₃⟩ := hsize q
          simp only [accBound]
          gcongr))
  have hℓ : ComputableInPolyTime (fun q : List Bool × List Bool => certLen d q.2.length)
      (encPair encBits encBits) encUnary := by
    unfold certLen
    fun_prop
  exact exists_computableInO_any_enumList hf hpoly hpoly hℓ

/-- The cost of the tests of the verifier: quadratic in the encoded input, times a power of the
length of the input that pays for the clock in unary. -/
private def cheap (d : ℕ) (p : List Bool × List Bool) : ℕ :=
  ((encPair encBits encBits p).length + 1) ^ 2 * ((p.1.length + 1) ^ (d + 3)) ^ 2

/-- **The verifier of the lazy diagonal is computable**, within the cost of its tests plus the
cost of the branch taken: the simulation, or the brute force at the end of an interval. -/
private theorem exists_computableInO_verifier (d : ℕ) :
    ∃ (D K : ℕ) (S : List Bool × List Bool → ℕ),
    ComputableInO (verifier d) (encPair encBits encBits) encBool
      (fun p => cheap d p + if Diagonal.shortDesc (unframe p.1) then
        (cheap d p + if Nat.size (p.1.length + 1) ≤ clock d (2 * (unframe p.1).length + 1) then
          cheap d p + accBound d D (unframe (unframe p.1), p.1 ++ [false], p.2)
        else (cheap d p + if Nat.size p.1.length ≤ clock d (2 * (unframe p.1).length + 1) then
          cheap d p + 2 ^ (K * ((encPair encBits encBits (unframe (unframe p.1),
            frame (unframe p.1))).length + certLen d (2 * (unframe p.1).length + 1)))
          else cheap d p))
        else cheap d p) S := by
  obtain ⟨D, hacc⟩ := exists_computableInO_accepts d
  obtain ⟨K, hbrute⟩ := exists_computableInO_brute d
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
  have hE := (ComputableInO.natToUnary.mono_time 1 (T' := fun n => (n + 1) ^ 2)
    fun n => by nlinarith).comp ((timeConstructible_succ_pow (d + 3)).computableInO.comp hbase)
  -- the numeric facts about the tests
  set G := 2 ^ (d + 3)
  set A := 8 + 4 * (G + 4) ^ 2
  have hfacts (p : List Bool × List Bool) : (unframe p.1).length ≤ p.1.length ∧
      p.1.length ≤ (encPair encBits encBits p).length ∧
      (encPair encBits encBits p).length + 1 ≤ cheap d p ∧
      ((2 * (unframe p.1).length + 1 + 1) ^ (d + 3) + 1) ^ 2 ≤ (G + 4) ^ 2 * cheap d p ∧
      (2 * (encPair encBits encBits p).length + 4 +
        (2 * (unframe p.1).length + 1 + 1) ^ (d + 3)) ^ 2 ≤ (G + 4) ^ 2 * cheap d p := by
    have hu := length_unframe_le p.1
    have hn : p.1.length ≤ (encPair encBits encBits p).length := by enc_len
    have hZ : (2 * (unframe p.1).length + 1 + 1) ^ (d + 3) ≤
        2 ^ (d + 3) * (p.1.length + 1) ^ (d + 3) := by
      rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) _
    exact ⟨hu, hn, cheap_aux G hn (Nat.one_le_pow _ _ (by omega)) hZ⟩
  have e (p : List Bool × List Bool) : A * (cheap d p + 1) =
      8 * cheap d p + 4 * ((G + 4) ^ 2 * cheap d p) + A := by ring
  have hc₀ := ComputableInO.mono_time (Diagonal.computableInO_shortDesc.comp hw) (T' := cheap d)
      A fun p => by
    obtain ⟨hu, hn, h₁, -, h₃⟩ := hfacts p
    have : ((unframe p.1).length + 1) ^ 2 ≤ (2 * (encPair encBits encBits p).length + 4 +
        (2 * (unframe p.1).length + 1 + 1) ^ (d + 3)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    simp only [Function.comp_apply] at ⊢
    have := e p; omega
  have hZ_sq (Z : ℕ) : Z ≤ (Z + 1) ^ 2 := (Nat.le_succ _).trans (Nat.le_self_pow two_ne_zero _)
  have hc₁ := ComputableInO.mono_time (ComputableInO.unaryLe.comp ((hsz.comp hsnoc).prod hE))
      (T' := cheap d) A fun p => by
    obtain ⟨hu, hn, h₁, h₂, h₃⟩ := hfacts p
    have hs := Nat.size_le.mpr (Nat.lt_two_pow_self (n := p.1.length + 1))
    have he := Universal.length_encNat_le (p.1.length + 1)
    have hsq : (p.1.length + 1 + 1) ^ 2 ≤ (2 * (encPair encBits encBits p).length + 4 +
        (2 * (unframe p.1).length + 1 + 1) ^ (d + 3)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hsq' : (2 * Nat.size (p.1.length + 1) + 1 + (2 * (unframe p.1).length + 1 + 1) ^ (d + 3)
        + 1) ^ 2 ≤ (2 * (encPair encBits encBits p).length + 4 +
          (2 * (unframe p.1).length + 1 + 1) ^ (d + 3)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hZ := hZ_sq ((2 * (unframe p.1).length + 1 + 1) ^ (d + 3))
    simp only [Function.comp_apply, length_encPair (enc₁ := encUnary) (enc₂ := encUnary),
      encUnary_apply, List.length_replicate, List.length_append, List.length_singleton,
      length_frame] at ⊢
    have := e p; omega
  have hc₂ := ComputableInO.mono_time (ComputableInO.unaryLe.comp ((hsz.comp hx).prod hE))
      (T' := cheap d) A fun p => by
    obtain ⟨hu, hn, h₁, h₂, h₃⟩ := hfacts p
    have hs := Nat.size_le.mpr (Nat.lt_two_pow_self (n := p.1.length))
    have he := Universal.length_encNat_le p.1.length
    have hsq : (p.1.length + 1) ^ 2 ≤ (2 * (encPair encBits encBits p).length + 4 +
        (2 * (unframe p.1).length + 1 + 1) ^ (d + 3)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hsq' : (2 * Nat.size p.1.length + 1 + (2 * (unframe p.1).length + 1 + 1) ^ (d + 3)
        + 1) ^ 2 ≤ (2 * (encPair encBits encBits p).length + 4 +
          (2 * (unframe p.1).length + 1 + 1) ^ (d + 3)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hZ := hZ_sq ((2 * (unframe p.1).length + 1 + 1) ^ (d + 3))
    simp only [Function.comp_apply, length_encPair (enc₁ := encUnary) (enc₂ := encUnary),
      encUnary_apply, List.length_replicate, length_frame] at ⊢
    have := e p; omega
  have hc₁' := hc₁.of_enc_eq (encC := encBool) (g := fun p : List Bool × List Bool =>
      decide (Nat.size (p.1.length + 1) ≤ clock d (2 * (unframe p.1).length + 1))) fun p => by
    simp only [Function.comp_apply, clock, length_frame, List.length_append,
      List.length_singleton]; rfl
  have hc₂' := hc₂.of_enc_eq (encC := encBool) (g := fun p : List Bool × List Bool =>
      decide (Nat.size p.1.length ≤ clock d (2 * (unframe p.1).length + 1))) fun p => by
    simp only [Function.comp_apply, clock, length_frame]; rfl
  have hf₁ := ComputableInO.mono_time
      (hacc.comp (hcode.prod (hsnoc.prod (ComputableInO.snd encBits encBits))))
      (T' := fun p => cheap d p + accBound d D (unframe (unframe p.1), p.1 ++ [false], p.2)) 7
      fun p => by
    obtain ⟨hu, hn, h₁, -⟩ := hfacts p
    simp only [Function.comp_apply] at ⊢
    have : 7 * (cheap d p + accBound d D (unframe (unframe p.1), p.1 ++ [false], p.2) + 1) =
        7 * cheap d p + 7 * accBound d D (unframe (unframe p.1), p.1 ++ [false], p.2) + 7 := by ring
    omega
  have hf₂ := ComputableInO.mono_time ((ComputableInDegree.of_finite (encIn := encBool)
    (encMid := encBool) (fun b : Bool => !b)).inO_one.comp (hbrute.comp (hcode.prod hbase)))
      (T' := fun p => cheap d p + 2 ^ (K * ((encPair encBits encBits (unframe (unframe p.1),
        frame (unframe p.1))).length + certLen d (2 * (unframe p.1).length + 1)))) 7
      fun p => by
    obtain ⟨hu, hn, h₁, -⟩ := hfacts p
    have hb : (encBool ((Cslib.BitString.enumList (certLen d (frame (unframe p.1)).length)).any
        (accepts d (unframe (unframe p.1)) (frame (unframe p.1))))).length = 1 := rfl
    simp only [Function.comp_apply, hb] at ⊢
    rw [length_frame]
    set B := 2 ^ (K * ((encPair encBits encBits (unframe (unframe p.1),
        frame (unframe p.1))).length + certLen d (2 * (unframe p.1).length + 1)))
    have : 7 * (cheap d p + B + 1) = 7 * cheap d p + 7 * B + 7 := by ring
    omega
  have hfalse := ComputableInO.mono_time (ComputableInO.const (encIn := encPair encBits encBits)
    (encMid := encBool) false) (T' := cheap d) 1 fun p => by
    obtain ⟨hu, hn, h₁, -⟩ := hfacts p; omega
  have h := hc₀.ite (hc₁'.ite hf₁ (hc₂'.ite hf₂ hfalse)) hfalse
  refine ⟨D, K, _, (h.of_enc_eq fun p => ?_).mono_le (fun p => le_of_eq ?_) fun p => le_rfl⟩
  · congr 1
    simp only [verifier, Diagonal.lazyVerifier, accepts, Function.comp_apply, decide_eq_true_eq,
      length_frame]
  · simp only [Function.comp_apply, decide_eq_true_eq]

/-- **The lazy diagonal is decidable in nondeterministic time `O((n + 1) ^ (6 * d + 14))`.** Guess
a certificate of length `(n + 2) ^ (d + 2)` and run the verifier
(`Cslib.Complexity.setOf_exists_mem_NTIME`). Below the end of an interval, the verifier simulates
a verifier on the input one bit longer with a certificate of that length, within time polynomial
in both. At the end of an interval of start `P`, it tries every certificate on the input of
length `P`, within time `2 ^ O((P + 1) ^ (d + 2))`, which is linear in the length `n` of the
input, since `n + 1 = 2 ^ ((P + 1) ^ (d + 3))` there. -/
theorem lazyDiagonal_mem_NTIME (d : ℕ) :
    lazyDiagonal d ∈ NTIME encBits fun n => (n + 1) ^ (6 * d + 14) := by
  obtain ⟨D, K, S, hV⟩ := exists_computableInO_verifier d
  have hsnoc : ComputableInO (fun x : List Bool => x ++ [false]) encBits encBits
      (fun x => x.length + x.length) (fun x => x.length + x.length) :=
    (ComputableInO.of_eq (f := fun x : List Bool => x) (encIn := encBits) (encMid := encBits)
      fun _ => rfl).append (ComputableInO.const (encMid := encBits) [false]) fun _ => rfl
  have hℓ := ((ComputableInO.natToUnary.mono_time 1 (T' := fun n => (n + 1) ^ 2)
    fun n => by nlinarith).comp ((timeConstructible_succ_pow (d + 2)).computableInO.comp
      hsnoc)).of_enc_eq (encC := encUnary) (g := fun x : List Bool => certLen d (x.length + 1))
      fun x => by simp [certLen]
  obtain ⟨CD, hCD⟩ := PolynomiallyBounded.exists_le_mul_two_pow (p := fun m => (m + 1) ^ D)
    (by fun_prop)
  set B₀ := 3 * K * (3 * K) ^ (d + 2) with hB₀
  set A₁ := 9 * 2 ^ (2 * d + 4) with hA₁
  set A₂ := (CD + 3) ^ 4 * 2 ^ (6 * d + 14) with hA₂
  set A₃ := 7 * 2 ^ (2 * d + 4) with hA₃
  refine setOf_exists_mem_NTIME hℓ hV (C := 2 + A₃ + 4 * A₁ + A₂ + 2 ^ B₀) fun x v hv => ?_
  clear hsnoc hℓ hV
  simp only [encBits_apply]
  set n := x.length with hn
  have hv' : v.length = (n + 2) ^ (d + 2) := hv
  set M := (n + 1) ^ (6 * d + 14)
  have h2 (k : ℕ) : (n + 2) ^ k ≤ 2 ^ k * (n + 1) ^ k :=
    (Nat.pow_le_pow_left (by omega) k).trans_eq (mul_pow 2 (n + 1) k)
  have hMk (k : ℕ) (hk : k ≤ 6 * d + 14) : (n + 1) ^ k ≤ M :=
    Nat.pow_le_pow_right (Nat.succ_pos _) hk
  have hnM : n + 1 ≤ M := Nat.le_self_pow (Nat.succ_ne_zero _) _
  clear_value B₀ A₁ A₂ A₃ M
  -- the certificate length
  have hTℓ : n + n + ((x ++ [false]).length + 1) ^ (d + 2) +
      (((fun x : List Bool => (x.length + 1) ^ (d + 2)) ∘ fun x => x ++ [false]) x + 1) ^ 2 ≤
        A₃ * M := by
    simp only [Function.comp_apply, List.length_append, List.length_singleton, add_assoc,
      Nat.reduceAdd, ← hn]
    have h₁ : n + 2 ≤ (n + 2) ^ (d + 2) := Nat.le_self_pow (Nat.succ_ne_zero _) _
    have h₂ : ((n + 2) ^ (d + 2) + 1) ^ 2 ≤ 4 * (n + 2) ^ (2 * d + 4) :=
      (Nat.pow_le_pow_left (m := 2 * (n + 2) ^ (d + 2)) (by omega) 2).trans_eq (by ring)
    have h₃ : (n + 2) ^ (d + 2) ≤ (n + 2) ^ (2 * d + 4) := by gcongr <;> omega
    have h₄ : 7 * (n + 2) ^ (2 * d + 4) ≤ A₃ * M :=
      calc _ ≤ 7 * (2 ^ (2 * d + 4) * (n + 1) ^ (2 * d + 4)) := Nat.mul_le_mul_left _ (h2 _)
        _ = A₃ * (n + 1) ^ (2 * d + 4) := by rw [hA₃]; ring
        _ ≤ A₃ * M := Nat.mul_le_mul_left _ (hMk _ (by omega))
    omega
  -- the tests
  have hcheap : cheap d (x, v) ≤ A₁ * M := by
    have hN : (encPair encBits encBits (x, v)).length + 1 ≤ 3 * (n + 2) ^ (d + 2) := by
      simp only [length_encPair, encBits_apply, hv']
      have : n + 2 ≤ (n + 2) ^ (d + 2) := Nat.le_self_pow (Nat.succ_ne_zero _) _
      omega
    calc cheap d (x, v) = ((encPair encBits encBits (x, v)).length + 1) ^ 2 *
          ((n + 1) ^ (d + 3)) ^ 2 := rfl
      _ ≤ (3 * (n + 2) ^ (d + 2)) ^ 2 * ((n + 1) ^ (d + 3)) ^ 2 := by gcongr
      _ = 9 * (n + 2) ^ (2 * d + 4) * (n + 1) ^ (2 * d + 6) := by ring
      _ ≤ 9 * (2 ^ (2 * d + 4) * (n + 1) ^ (2 * d + 4)) * (n + 1) ^ (2 * d + 6) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (h2 _))
      _ = A₁ * (n + 1) ^ (4 * d + 10) := by rw [hA₁]; ring
      _ ≤ A₁ * M := Nat.mul_le_mul_left _ (hMk _ (by omega))
  -- the simulation, when the description is short
  have hacc (h₀ : Diagonal.shortDesc (unframe x) = true) :
      accBound d D (unframe (unframe x), x ++ [false], v) ≤ A₂ * M := by
    have hs : 2 ^ (unframe (unframe x)).length ≤ (unframe x).length := of_decide_eq_true h₀
    have hu := length_unframe_le x
    have hD : ((unframe (unframe x)).length + 1) ^ D ≤ CD * n :=
      (hCD _).trans (Nat.mul_le_mul_left _ (hs.trans hu))
    have hb : ((unframe (unframe x)).length + 1) ^ D + (n + 1) + (n + 2) ^ (d + 2) + 1 ≤
        (CD + 3) * (n + 2) ^ (d + 2) := by
      have h₁ : n + 2 ≤ (n + 2) ^ (d + 2) := Nat.le_self_pow (Nat.succ_ne_zero _) _
      have h₂ : CD * n ≤ CD * (n + 2) ^ (d + 2) := Nat.mul_le_mul_left _ (by omega)
      have e : (CD + 3) * (n + 2) ^ (d + 2) = CD * (n + 2) ^ (d + 2) + 3 * (n + 2) ^ (d + 2) := by
        ring
      omega
    calc accBound d D (unframe (unframe x), x ++ [false], v) =
          (((unframe (unframe x)).length + 1) ^ D + (n + 1) + (n + 2) ^ (d + 2) + 1) ^ 4 *
            (n + 2) ^ (2 * d + 6) := by
          simp only [accBound, List.length_append, List.length_singleton, hv', ← hn, add_assoc,
            Nat.reduceAdd]
      _ ≤ ((CD + 3) * (n + 2) ^ (d + 2)) ^ 4 * (n + 2) ^ (2 * d + 6) := by gcongr
      _ = (CD + 3) ^ 4 * (n + 2) ^ (6 * d + 14) := by ring
      _ ≤ (CD + 3) ^ 4 * (2 ^ (6 * d + 14) * (n + 1) ^ (6 * d + 14)) :=
          Nat.mul_le_mul_left _ (h2 _)
      _ ≤ (CD + 3) ^ 4 * (2 ^ (6 * d + 14) * M) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (hMk _ le_rfl))
      _ = A₂ * M := by rw [hA₂]; ring
  -- the brute force, at the end of an interval
  have hbrute (h₁ : ¬Nat.size (n + 1) ≤ clock d (2 * (unframe x).length + 1)) :
      2 ^ (K * ((encPair encBits encBits (unframe (unframe x), frame (unframe x))).length +
        certLen d (2 * (unframe x).length + 1))) ≤ n + 1 + 2 ^ B₀ := by
    set P := 2 * (unframe x).length + 1 with hP
    have hE : 2 ^ clock d P ≤ n + 1 := by
      rw [Nat.size_le, not_lt] at h₁
      exact h₁
    have hc := length_unframe_le (unframe x)
    have hlen : (encPair encBits encBits (unframe (unframe x), frame (unframe x))).length +
        certLen d P ≤ 3 * (P + 1) ^ (d + 2) := by
      simp only [length_encPair, encBits_apply, length_frame, certLen]
      have : P + 1 ≤ (P + 1) ^ (d + 2) := Nat.le_self_pow (Nat.succ_ne_zero _) _
      omega
    rcases le_or_gt (3 * K) (P + 1) with hK | hK
    · have hle : K * ((encPair encBits encBits (unframe (unframe x), frame (unframe x))).length +
          certLen d P) ≤ clock d P :=
        calc _ ≤ K * (3 * (P + 1) ^ (d + 2)) := Nat.mul_le_mul_left _ hlen
          _ = 3 * K * (P + 1) ^ (d + 2) := by ring
          _ ≤ (P + 1) * (P + 1) ^ (d + 2) := Nat.mul_le_mul_right _ hK
          _ = clock d P := by rw [clock]; ring
      exact ((Nat.pow_le_pow_right Nat.one_lt_two.le hle).trans hE).trans (Nat.le_add_right _ _)
    · have hle : K * ((encPair encBits encBits (unframe (unframe x), frame (unframe x))).length +
          certLen d P) ≤ B₀ :=
        calc _ ≤ K * (3 * (P + 1) ^ (d + 2)) := Nat.mul_le_mul_left _ hlen
          _ = 3 * K * (P + 1) ^ (d + 2) := by ring
          _ ≤ B₀ := by rw [hB₀]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hK.le _)
      exact (Nat.pow_le_pow_right Nat.one_lt_two.le hle).trans (Nat.le_add_left _ _)
  clear hB₀ hA₁ hA₂ hA₃ h2 hMk hCD
  have e : (2 + A₃ + 4 * A₁ + A₂ + 2 ^ B₀) * M =
      2 * M + A₃ * M + 4 * (A₁ * M) + A₂ * M + 2 ^ B₀ * M := by ring
  have hB : 2 ^ B₀ ≤ 2 ^ B₀ * M :=
    Nat.le_mul_of_pos_right _ (Nat.lt_of_lt_of_le (Nat.succ_pos _) hnM)
  generalize 2 + A₃ + 4 * A₁ + A₂ + 2 ^ B₀ = C at *
  generalize 2 ^ B₀ = P at *
  split_ifs with h₀ h₁ h₂
  · have := hacc h₀
    omega
  · have := hbrute h₁
    omega
  · omega
  · omega

/-! ### The hierarchy -/

/-- **A nondeterministic time hierarchy for polynomial degrees.** For every degree `d`,
nondeterministic time `O((n + 1) ^ d)` is strictly contained in nondeterministic time
`O((n + 1) ^ e)` whenever `6 * d + 14 ≤ e`. The lazy diagonal `Cslib.Complexity.lazyDiagonal d`
separates them (`Cslib.Complexity.lazyDiagonal_mem_NTIME`,
`Cslib.Complexity.lazyDiagonal_notMem_NTIME`). This is a coarse form of the nondeterministic time
hierarchy theorem [Arora and Barak, Theorem 3.3][AroraBarak07]: the gap is the polynomial
overhead of the native universal machine and of the certificates, not `f (n + 1) = o (g n)`. -/
theorem NTIME_succ_pow_ssubset_NTIME_succ_pow_of_le {d e : ℕ} (h : 6 * d + 14 ≤ e) :
    NTIME encBits (fun n => (n + 1) ^ d) ⊂ NTIME encBits fun n => (n + 1) ^ e := by
  have hsub : ∀ {a b : ℕ}, a ≤ b →
      NTIME encBits (fun n => (n + 1) ^ a) ⊆ NTIME encBits fun n => (n + 1) ^ b :=
    fun hab => NTIME_mono fun n => Nat.pow_le_pow_right (by omega) hab
  exact (Set.ssubset_iff_of_subset (hsub (by omega))).mpr
    ⟨lazyDiagonal d, hsub h (lazyDiagonal_mem_NTIME d), lazyDiagonal_notMem_NTIME d⟩

end Cslib.Complexity
