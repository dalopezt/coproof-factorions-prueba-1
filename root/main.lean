import «upper_bound».«main»
import «finite_verification».«main»
import Definitions
theorem root : {n : ℕ | digitFactorialSum n = n} = {1, 2, 145, 40585} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    have hle : n ≤ 2540160 := upper_bound n h
    have hmem : n ∈ {n : ℕ | n ≤ 2540160 ∧ digitFactorialSum n = n} := ⟨hle, h⟩
    rw [finite_verification] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    exact hmem
  · intro h
    have hmem : n ∈ ({1, 2, 145, 40585} : Set ℕ) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact h
    have : ({1, 2, 145, 40585} : Set ℕ) ⊆ {n : ℕ | n ≤ 2540160 ∧ digitFactorialSum n = n} := by
      rw [← finite_verification]
    exact (this hmem).2
