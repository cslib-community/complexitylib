import os

lcs_path = ".worktrees/218c-copositive/CslibFrontier/Computability/Complexity/FineGrained/LCS.lean"

with open(lcs_path, "r") as f:
    lcs_content = f.read()

end_mark = "end Cslib.Complexity.OV"
if lcs_content.endswith(end_mark) or lcs_content.strip().endswith(end_mark):
    idx = lcs_content.rfind(end_mark)
    
    append_str = """    have h₂ := Nat.mul_le_mul_left cE' (hpow x dE (by omega))
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

"""
    lcs_content = lcs_content[:idx] + append_str + end_mark + "\n"

with open(lcs_path, "w") as f:
    f.write(lcs_content)
print("Appended.")
