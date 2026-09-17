namespace Toy

def A (n : Nat) : Prop :=
  n + 1 ≤ n + 2

def B (n : Nat) : Prop :=
  n + 2 ≤ n + 3

theorem lemma1 (n : Nat) : A n := by
  unfold A
  omega

theorem lemma2 (n : Nat) : A (n + 1) := by
  unfold A
  omega

theorem lemma3 (n : Nat) : A n ∧ B (n + 1) := by
  have h := lemma2 (n + 1)
  exact h

theorem main (n : Nat) : A n ∧ B (n + 1) := by
  constructor
  · exact lemma1 n
  · exact lemma3 (n + 1)

end Toy
