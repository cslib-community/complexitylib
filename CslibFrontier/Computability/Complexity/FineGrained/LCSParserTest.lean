module
public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.FineGrained.OrthogonalVectors
public import CslibFrontier.Algorithms.Lean.EditDistance.LCS
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Complexity.FineGrained.Diameter
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Streaming

open Turing.MultiTapeTM
open Cslib.Complexity
open Cslib.Complexity.OV

it reads the marker of a bit of the outer frame of `A` (or the first bit of `encOV`), whether the
bit it reads is a frame marker, the coordinate of the current bit, and the number of the current
vector. -/
abbrev LCSParseState : Type := (((Bool × Bool) × Bool) × ℕ) × ℕ

/-- The encoding of the parser state. -/
abbrev encLCSParseState : LCSParseState ↪ List Bool :=
  encPair (encPair (encPair (encPair encBool encBool) encBool) encNat) encNat

/-- A round of the parser, reading one bit. In the first list each bit `c` of the inner frames
comes as `[true, c]` in the outer frame, and the first unmarked bit ends the first list. In the
inner frames, a marker `true` announces a bit of the vector and `false` ends the vector. -/
def lcsParseStep (p : LCSParseState × Bool) : LCSParseState :=
  if !p.1.1.1.1.1 && !p.1.1.1.1.2 then
    if p.2 then ((((false, true), p.1.1.1.2), p.1.1.2), p.1.2)
    else ((((true, false), false), p.1.1.2), p.1.2)
  else if p.1.1.1.2 then ((((p.1.1.1.1.1, false), false), p.1.1.2 + 1), p.1.2)
  else if p.2 then ((((p.1.1.1.1.1, false), true), p.1.1.2), p.1.2)
  else ((((p.1.1.1.1.1, false), false), 0), p.1.2 + 1)

/-- The output of a round of the parser: `f k i b` for the bit `b` of coordinate `i` of the vector
numbered `k`, and `g s k` at the end of the vector numbered `k` of the list `s`. -/
def lcsParseEmit {β : Type} (f : ℕ → ℕ → Bool → List β) (g : Bool → ℕ → List β)
    (p : LCSParseState × Bool) : List β :=
  if !p.1.1.1.1.1 && !p.1.1.1.1.2 then []
  else if p.1.1.1.2 then f p.1.2 p.1.1.2 p.2
  else if p.2 then []
  else g p.1.1.1.1.1 p.1.2

/-- **One pass of the parser** over a list of bits, from a state. -/
def lcsParseRun {β : Type} (f : ℕ → ℕ → Bool → List β) (g : Bool → ℕ → List β) :
    LCSParseState → List Bool → List β
  | _, [] => []
  | s, b :: l => lcsParseEmit f g (s, b) ++ lcsParseRun f g (lcsParseStep (s, b)) l

section Stream

variable {β : Type} {f : ℕ → ℕ → Bool → List β} {g : Bool → ℕ → List β}

/-- The streamed output of the parser rounds is the encoded output of the pass. -/
theorem streamEmit_eq_lcsParseRun {enc : β ↪ List Bool} (s : LCSParseState) (l : List Bool) :
    streamEmit lcsParseStep (fun p => encList enc (lcsParseEmit f g p)) s l =
      encList enc (lcsParseRun f g s l) := by
  induction l generalizing s with
  | nil => rfl
  | cons b l ih => rw [streamEmit, ih, lcsParseRun, encList_append]

/-- In the second phase, a frame `[true, b₁, …, true, bₙ, false]` is one vector. -/
theorem lcsParseRun_frame_snd (i k : ℕ) (v : List Bool) (rest : List Bool) :
    lcsParseRun f g ((((true, false), false), i), k) (frame v ++ rest) =
      bitsOut (f k) i v ++ g true k ++ lcsParseRun f g ((((true, false), false), 0), k + 1) rest := by
  induction v generalizing i with
  | nil => simp [frame_nil, lcsParseRun, lcsParseEmit, lcsParseStep, bitsOut]
  | cons b v ih =>
    simp only [frame_cons, List.cons_append, lcsParseRun, lcsParseEmit, lcsParseStep, bitsOut]
    simp [ih, List.append_assoc]

/-- In the second phase, the frames of a list of vectors. -/
theorem lcsParseRun_frames_snd (k : ℕ) (vs : List (List Bool)) (rest : List Bool) :
    lcsParseRun f g ((((true, false), false), 0), k) (vs.flatMap frame ++ rest) =
      vecsOut f (g true) k vs ++
        lcsParseRun f g ((((true, false), false), 0), k + vs.length) rest := by
  induction vs generalizing k with
  | nil => simp [vecsOut]
  | cons v vs ih =>
    rw [List.flatMap_cons, List.append_assoc, lcsParseRun_frame_snd, ih]
    simp [vecsOut, List.append_assoc, Nat.add_assoc, Nat.add_comm 1 vs.length]

/-- In the first phase, the outer frame marks each bit `c` of the inner frames as `[true, c]`. -/
theorem lcsParseRun_frame_fst (i k : ℕ) (v : List Bool) (rest : List Bool) :
    lcsParseRun f g ((((false, false), false), i), k)
        ((frame v).flatMap (fun b => [true, b]) ++ rest) =
      bitsOut (f k) i v ++ g false k ++
        lcsParseRun f g ((((false, false), false), 0), k + 1) rest := by
  induction v generalizing i with
  | nil => simp [lcsParseRun, lcsParseEmit, lcsParseStep, bitsOut]
  | cons b v ih =>
    simp only [frame_cons, List.flatMap_cons, List.cons_append, List.nil_append]
    cases b <;> simp [lcsParseRun, lcsParseEmit, lcsParseStep, bitsOut, ih, List.append_assoc]

/-- In the first phase, the outer frame of the inner frames of a list of vectors. -/
theorem lcsParseRun_frames_fst (k : ℕ) (vs : List (List Bool)) (rest : List Bool) :
    lcsParseRun f g ((((false, false), false), 0), k)
        ((vs.flatMap frame).flatMap (fun b => [true, b]) ++ rest) =
      vecsOut f (g false) k vs ++
        lcsParseRun f g ((((false, false), false), 0), k + vs.length) rest := by
  induction vs generalizing k with
  | nil => simp [vecsOut]
  | cons v vs ih =>
    rw [List.flatMap_cons, List.flatMap_append, List.append_assoc, lcsParseRun_frame_fst, ih]
    simp [vecsOut, List.append_assoc, Nat.add_assoc, Nat.add_comm 1 vs.length]

/-- **The parser on an encoded instance**: it emits the outputs of the first list, then those of
the second, numbering the vectors of both lists consecutively. -/
theorem lcsParseRun_encOV (p : List (List Bool) × List (List Bool)) :
    lcsParseRun f g ((((false, false), false), 0), 0) (encOV p) =
      vecsOut f (g false) 0 p.1 ++ vecsOut f (g true) p.1.length p.2 := by
  have hl (l : List (List Bool)) : encList encBits l = l.flatMap frame := rfl
  have e : encOV p = (p.1.flatMap frame).flatMap (fun b => [true, b]) ++
      (false :: p.2.flatMap frame ++ []) := by
    simp only [encOV, encPair_apply, frame, hl, List.append_nil, List.append_assoc,
      List.singleton_append]
  have h₁ : lcsParseStep (((((false, false), false), 0), 0 + p.1.length), false) =
      ((((true, false), false), 0), p.1.length) := by simp [lcsParseStep]
  have h₂ : lcsParseEmit f g (((((false, false), false), 0), 0 + p.1.length), false) = [] := by
    simp [lcsParseEmit]
  rw [e, lcsParseRun_frames_fst, List.cons_append, lcsParseRun, h₁, h₂, List.nil_append,
    lcsParseRun_frames_snd]
  simp [lcsParseRun]

end Stream

/-! ### The size of the parser state -/

/-- A round increases the coordinate plus the vector number by at most one. -/
private theorem lcsParseStep_le (s : LCSParseState) (b : Bool) :
    (lcsParseStep (s, b)).1.2 + (lcsParseStep (s, b)).2 ≤ s.1.2 + s.2 + 1 := by
  unfold lcsParseStep
  split_ifs <;> simp only <;> omega

/-- The coordinate plus the vector number grow by at most the number of rounds. -/
private theorem foldl_lcsParseStep_le (s : LCSParseState) (l : List Bool) :
    (l.foldl (fun s b => lcsParseStep (s, b)) s).1.2 + (l.foldl (fun s b => lcsParseStep (s, b)) s).2 ≤
      s.1.2 + s.2 + l.length := by
  induction l generalizing s with
  | nil => simp
  | cons b l ih =>
    have := ih (lcsParseStep (s, b))
    have := lcsParseStep_le s b
    simp only [List.foldl_cons, List.length_cons]
    omega

/-- The length of an encoded parser state. -/
private theorem length_encLCSParseState (s : LCSParseState) :
    (encLCSParseState s).length = 43 + 2 * Nat.size s.1.2 + Nat.size s.2 := by
  simp only [length_encPair, encBool_apply, encNat_apply, Nat.size_eq_bits_len,
    List.length_singleton]
  omega

/-- The parser state after `j` bits holds numbers at most `j`. -/
private theorem length_encLCSParseState_streamState_le (x : List Bool) (j : ℕ) :
    (encLCSParseState (streamState ((((false, false), false), 0), 0) lcsParseStep x j)).length ≤
      43 + 3 * Nat.size x.length := by
  have h₁ : (streamState ((((false, false), false), 0), 0) lcsParseStep x j).1.2 +
      (streamState ((((false, false), false), 0), 0) lcsParseStep x j).2 ≤ x.length := by
    have := foldl_lcsParseStep_le ((((false, false), false), 0), 0) (x.take j)
    simp only [List.length_take, Nat.zero_add] at this
    exact this.trans (min_le_right _ _)
  have h₂ := Nat.size_le_size (show
    (streamState ((((false, false), false), 0), 0) lcsParseStep x j).1.2 ≤ x.length by omega)
  have h₃ := Nat.size_le_size (show
    (streamState ((((false, false), false), 0), 0) lcsParseStep x j).2 ≤ x.length by omega)
  rw [length_encLCSParseState]
  omega

open ComputableInPolyTime in
/-- A round of the parser is computable in polynomial time. -/
theorem computableInPolyTime_lcsParseStep :
    ComputableInPolyTime lcsParseStep (encPair encLCSParseState encBool) encLCSParseState := by
  unfold lcsParseStep
  fun_prop

open ComputableInPolyTime in
/-- The output of a round of the parser is computable in polynomial time when its outputs are. -/
theorem computableInPolyTime_lcsParseEmit {β : Type} {enc : β ↪ List Bool} {f : ℕ → ℕ → Bool → List β}
    {g : Bool → ℕ → List β}
    (hf : ComputableInPolyTime (fun p : LCSParseState × Bool => f p.1.2 p.1.1.2 p.2)
      (encPair encLCSParseState encBool) (encList enc))
    (hg : ComputableInPolyTime (fun p : LCSParseState × Bool => g p.1.1.1.1.1 p.1.2)
      (encPair encLCSParseState encBool) (encList enc)) :
    ComputableInPolyTime (lcsParseEmit f g) (encPair encLCSParseState encBool) (encList enc) := by
  have hnil : ComputableInPolyTime (fun _ : LCSParseState × Bool => ([] : List β))
      (encPair encLCSParseState encBool) (encList enc) := by fun_prop
  have hc₁ : ComputableInPolyTime (fun p : LCSParseState × Bool => !p.1.1.1.1.1 && !p.1.1.1.1.2)
      (encPair encLCSParseState encBool) encBool := by fun_prop
  have hc₂ : ComputableInPolyTime (fun p : LCSParseState × Bool => p.1.1.1.2)
      (encPair encLCSParseState encBool) encBool := by fun_prop
  have hc₃ : ComputableInPolyTime (fun p : LCSParseState × Bool => p.2)
      (encPair encLCSParseState encBool) encBool := by fun_prop
  exact ite' hc₁ hnil (ite' hc₂ hf (ite' hc₃ hnil hg))

open ComputableInPolyTime in
/-- **One pass of the parser** over an encoded instance runs within time `L (log L) ^ D` on inputs
of length `L`, when its outputs are computable in polynomial time. -/
theorem computableInO_lcsParseRun {β : Type} {enc : β ↪ List Bool} {f : ℕ → ℕ → Bool → List β}
    {g : Bool → ℕ → List β} (fin : List β)
    (hfg : ComputableInPolyTime (lcsParseEmit f g) (encPair encLCSParseState encBool) (encList enc)) :
    ∃ D, ComputableInO
      (fun x : List Bool => lcsParseRun f g ((((false, false), false), 0), 0) x ++ fin)
      encBits (encList enc) (fun x => (x.length + 1) * (Nat.size x.length + 1) ^ D)
      fun x => (x.length + 1) * (Nat.size x.length + 1) ^ D := by
  obtain ⟨dN, _, hN_deg⟩ := computableInPolyTime_lcsParseStep.exists_degree
  obtain ⟨tN, sN, ⟨cN, htN⟩, ⟨cN', hsN⟩, hN⟩ := Internal.NormalForm.degree hN_deg
  obtain ⟨dE, _, hE_deg⟩ := hfg.exists_degree
  obtain ⟨tE, sE, ⟨cE, htE⟩, ⟨cE', hsE⟩, hE⟩ := Internal.NormalForm.degree hE_deg
  obtain ⟨cI, hI⟩ := computableInTimeAndSpace_of_const (α := List Bool) (encIn := encBits)
    (encOut := encLCSParseState) ((((false, false), false), 0), 0)
  obtain ⟨cF, hF⟩ := computableInTimeAndSpace_of_const (α := LCSParseState) (encIn := encLCSParseState)
    (encOut := encList enc) fin
  let reader : InputReader Bool Unit := ⟨(), fun _ b => (none, some b)⟩
  have hI' : ComputableTidilyInTimeAndSpace (fun _ : List Bool => ((((false, false), false), 0), 0))
      encBits encLCSParseState (fun _ => 2 * cI + 2) (fun _ => 0) := hI.computableTidilyInTimeAndSpace
  have hF' : ComputableTidilyInTimeAndSpace (fun _ : LCSParseState => fin) encLCSParseState (encList enc)
      (fun _ => 2 * cF + 2) (fun _ => 0) := hF.computableTidilyInTimeAndSpace
  -- the rounds take time polylogarithmic in the input length
  have hpow (x : List Bool) (d : ℕ) (hd : d ≤ dN + dE + 1) :
      (2 * (43 + 3 * Nat.size x.length) + 3) ^ d ≤
        89 ^ d * (Nat.size x.length + 1) ^ (dN + dE + 1) :=
    calc (2 * (43 + 3 * Nat.size x.length) + 3) ^ d ≤ (89 * (Nat.size x.length + 1)) ^ d :=
          Nat.pow_le_pow_left (by omega) d
      _ = 89 ^ d * (Nat.size x.length + 1) ^ d := Nat.mul_pow _ _ _
      _ ≤ 89 ^ d * (Nat.size x.length + 1) ^ (dN + dE + 1) := by gcongr
  have hround (x : List Bool) (j : ℕ) (hj : j < x.length) (c₁ c₂ : ℕ)
      (u₁ u₂ : LCSParseState × Bool → ℕ)
      (h₁ : ∀ a, u₁ a ≤ c₁ * ((encPair encLCSParseState encBool a).length + 1) ^ dN)
      (h₂ : ∀ a, u₂ a ≤ c₂ * ((encPair encLCSParseState encBool a).length + 1) ^ dE) :
      u₁ (streamState ((((false, false), false), 0), 0) lcsParseStep x j, x[j]) +
        u₂ (streamState ((((false, false), false), 0), 0) lcsParseStep x j, x[j]) ≤
      c₁ * (2 * (43 + 3 * Nat.size x.length) + 3) ^ dN +
        c₂ * (2 * (43 + 3 * Nat.size x.length) + 3) ^ dE := by
    have hs : (encLCSParseState
        (streamState ((((false, false), false), 0), 0) lcsParseStep x j, x[j]).1).length ≤
        43 + 3 * Nat.size x.length := length_encLCSParseState_streamState_le x j
    have e : (encPair encLCSParseState encBool
        (streamState ((((false, false), false), 0), 0) lcsParseStep x j, x[j])).length + 1 ≤
        2 * (43 + 3 * Nat.size x.length) + 3 := by
      rw [length_encPair, encBool_apply, List.length_singleton]
      omega
    exact Nat.add_le_add ((h₁ _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left e _)))
      ((h₂ _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left e _)))
  obtain ⟨c, h⟩ := ComputableTidilyInTimeAndSpace.streamFold reader (fun b => [b])
    (fun _ => List.cons_ne_nil _ _) (fun a rest => by simp [reader, InputReader.read])
    (encA := encBool) (fun x => x) (fun x => by simp) hI' hN hE hF'
    (g := fun x : List Bool => lcsParseRun f g ((((false, false), false), 0), 0) x ++ fin)
    (fun x => by rw [encList_append, streamEmit_eq_lcsParseRun])
    (tMax := fun x => cN * (2 * (43 + 3 * Nat.size x.length) + 3) ^ dN +
      cE * (2 * (43 + 3 * Nat.size x.length) + 3) ^ dE)
    (sMax := fun x => cN' * (2 * (43 + 3 * Nat.size x.length) + 3) ^ dN +
      cE' * (2 * (43 + 3 * Nat.size x.length) + 3) ^ dE)
    (lMax := fun x => 43 + 3 * Nat.size x.length)
    (fun x j hj => hround x j hj cN cE tN tE htN htE)
    (fun x j hj => hround x j hj cN' cE' sN sE hsN hsE)
    (fun x j _ => length_encLCSParseState_streamState_le x j)
    (fun x j hj => by rw [encBool_apply, List.length_singleton]; omega)
  set M := cN * 89 ^ dN + cE * 89 ^ dE + cN' * 89 ^ dN + cE' * 89 ^ dE
  have key (L Y t l a b : ℕ) (hY : 1 ≤ Y) (ht : t ≤ M * Y) (hl : l ≤ 43 * Y) :
      a + b + L + L * (t + l + 1) + l + 1 ≤ (a + b + M + 100) * ((L + 1) * Y + 1) := by
    nlinarith [Nat.mul_le_mul_left L ht, Nat.mul_le_mul_left L hl, Nat.mul_le_mul_left L hY]
  have hY (x : List Bool) : 1 ≤ (Nat.size x.length + 1) ^ (dN + dE + 1) :=
    Nat.one_le_pow _ _ (by omega)
  have hl (x : List Bool) : 43 + 3 * Nat.size x.length ≤
      43 * (Nat.size x.length + 1) ^ (dN + dE + 1) := by
    have := Nat.le_self_pow (show dN + dE + 1 ≠ 0 by omega) (Nat.size x.length + 1)
    omega
  have ht (x : List Bool) : cN * (2 * (43 + 3 * Nat.size x.length) + 3) ^ dN +
      cE * (2 * (43 + 3 * Nat.size x.length) + 3) ^ dE ≤
      M * (Nat.size x.length + 1) ^ (dN + dE + 1) := by
    have h₁ := Nat.mul_le_mul_left cN (hpow x dN (by omega))
    have h₂ := Nat.mul_le_mul_left cE (hpow x dE (by omega))
    simp only [M, Nat.add_mul, Nat.mul_assoc] at h₁ h₂ ⊢
    omega
  have hs (x : List Bool) : cN' * (2 * (43 + 3 * Nat.size x.length) + 3) ^ dN +
      cE' * (2 * (43 + 3 * Nat.size x.length) + 3) ^ dE ≤
      M * (Nat.size x.length + 1) ^ (dN + dE + 1) := by
    have h₁ := Nat.mul_le_mul_left cN' (hpow x dN (by omega))
    have h₁ := Nat.mul_le_mul_left cN' (hpow x dN (by omega))
    have h₂ := Nat.mul_le_mul_left cE' (hpow x dE (by omega))
    simp only [M, Nat.add_mul, Nat.mul_assoc] at h₁ h₂ ⊢
    omega
  refine ⟨dN + dE + 1, ComputableInO.of_bounds h.computableInTimeAndSpace
    (c * (2 * cI + 2 + (2 * cF + 2) + M + 100)) (fun x => ?_) (fun x => ?_)
    (fun x => (h.computableInTimeAndSpace.length_le x).trans ?_)⟩
  · rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left
    rw [encBits_apply]
    exact key _ _ _ _ _ _ (hY x) (ht x) (hl x)
  · rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left
    have h₁ := hs x
    have h₂ := hl x
    have h₃ := hY x
    have h₄ : (Nat.size x.length + 1) ^ (dN + dE + 1) ≤
        (x.length + 1) * (Nat.size x.length + 1) ^ (dN + dE + 1) :=
      Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    nlinarith
  · rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left
    rw [encBits_apply]
    exact key _ _ _ _ _ _ (hY x) (ht x) (hl x)

