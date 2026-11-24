import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2001_8
  (colors : ∀ (n k : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, C.eval (List.ofFn x) = decide (∃ u v, G.Adj u v ∧ x u=true ∧ x v=true)) → ∀ col : Fin n → Fin k, (∀ u v, G.Adj u v → col u≠col v) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size+1 ≤ (k*k+2)*(C.size+1) ∧ ∀ x y : Fin n → Bool, D.eval (List.ofFn x ++ List.ofFn y)=decide (∃ u v, G.Adj u v ∧ x u=true ∧ y v=true))
  (high : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (¬∃ col : Fin x2 → Fin x1, ∀ u v, x3.Adj u v → col u ≠ col v) → (∀ (x5 : Fin x2), x3.degree x5 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x5) → (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → (∀ (x9 : Fin x2 → Bool), x7.eval (List.ofFn x9) = Decidable.decide (∃ (x10 : Fin x2) (x11 : Fin x2), x3.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true)) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ x10.size + (1 : ℕ) ≤ x1 * (x7.size + (1 : ℕ)) ∧ ∀ (x11 x12 : Fin x2 → Bool), x10.eval (List.ofFn x11 ++ List.ofFn x12) = Decidable.decide (∃ (x13 : Fin x2) (x14 : Fin x2), x3.Adj x13 x14 ∧ x11 x13 = Bool.true ∧ x12 x14 = Bool.true)) :
  ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2), x3.degree x5 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x5) → (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → (∀ (x9 : Fin x2 → Bool), x7.eval (List.ofFn x9) = Decidable.decide (∃ (x10 : Fin x2) (x11 : Fin x2), x3.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true)) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ x10.size + (1 : ℕ) ≤ x1 * (x7.size + (1 : ℕ)) ∧ ∀ (x11 x12 : Fin x2 → Bool), x10.eval (List.ofFn x11 ++ List.ofFn x12) = Decidable.decide (∃ (x13 : Fin x2) (x14 : Fin x2), x3.Adj x13 x14 ∧ x11 x13 = Bool.true ∧ x12 x14 = Bool.true) := by
  classical
  obtain ⟨k,large⟩ := high
  refine ⟨max k (k*k+2),?_⟩
  intro n G dec deg cycles C hm hc
  by_cases small : ∃ col : Fin n → Fin k, ∀ u v, G.Adj u v → col u ≠ col v
  · obtain ⟨col,sep⟩ := small
    obtain ⟨D,hmD,bound,correct⟩ := colors n k G C hm hc col sep
    exact ⟨D,hmD,bound.trans (Nat.mul_le_mul_right _ (le_max_right _ _)),correct⟩
  · obtain ⟨D,hmD,bound,correct⟩ := large n G small deg cycles C hm hc
    exact ⟨D,hmD,bound.trans (Nat.mul_le_mul_right _ (le_max_left _ _)),correct⟩
