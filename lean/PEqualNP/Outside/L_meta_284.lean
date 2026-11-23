import PEqualNP.Defs

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_284 :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 11]⟩], output := 12 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 7 ∧ ∀ x : Fin 6 → Bool, ((List.ofFn x).count true ≤ 2 → (C.eval (List.ofFn x) = true ↔ (∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) ∧ (¬ (C.eval (List.ofFn x) = true ↔ (∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) ↔ (x 3 = true ∧ x 4 = true ∧ x 5 = true ∧ ¬ (∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) := by
  intro C h
  subst C
  constructor
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · constructor
    · rfl
    · intro x
      have hx : (![x 0, x 1, x 2, x 3, x 4, x 5] : Fin 6 → Bool) = x := by
        funext i
        fin_cases i <;> rfl
      rw [← hx]
      generalize x 0 = b0, x 1 = b1, x 2 = b2, x 3 = b3, x 4 = b4, x 5 = b5
      cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;>
        simp [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
          PEqualNP.CircuitLowerBounds.GateOp.eval, Fin.exists_fin_succ]
