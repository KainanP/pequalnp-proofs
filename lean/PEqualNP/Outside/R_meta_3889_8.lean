import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3889_8
  (specializeTrue : ∀ (C : Circuit) (n : Nat), FanInTwo C → C.output≠n →
    ∃ D : Circuit, FanInTwo D ∧ D.size=C.size ∧ ∀ w : List Bool, w.length=n → ∀ b : Bool,
      D.eval (w++[b])=C.eval (w++[true]))
  (complement : ∀ (C : Circuit), FanInTwo C → C.size≤13 → ∃ x : Fin 9 → Bool,
    let u := x 0 || x 2
    C.eval (List.ofFn x ++ [u,!u]) ≠ ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any
      (fun e => x e.1 && x e.2)) :
∀ (x1 : Fin (11 : ℕ)),   x1 = (9 : Fin (11 : ℕ)) ∨ x1 = (10 : Fin (11 : ℕ)) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ))];             x3.eval (x7 ++ [!x7.getD (↑x1) Bool.false]) ≠ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x8 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x6 x8.1 && x6 x8.2 := by
  intro k hk C fan size
  rcases hk with rfl|rfl
  · obtain ⟨x,hx⟩ := complement C fan size
    refine ⟨x,?_⟩
    simpa [List.getD_eq_getElem?_getD, List.getElem?_append] using hx
  · by_cases output : C.output=10
    · refine ⟨fun _ => false,?_⟩
      let w : List Bool := List.replicate 9 false ++ [false,true]
      have raw (gs : List Gate) (v : List Bool) (i : Nat) (bound : i<v.length) :
          ((Circuit.mk gs 0).wires v).getD i false=v.getD i false := by
        induction gs generalizing v with
        | nil => rfl
        | cons g gs ih =>
          change ((Circuit.mk gs 0).wires (v++[_])).getD i false=_
          rw [ih _ (by simp;omega),List.getD_append _ _ _ _ bound]
      have hit : C.eval w=true := by
        change ((Circuit.mk C.gates 0).wires w).getD C.output false=true
        rw [output,raw _ w 10 (by decide)];rfl
      change C.eval w≠false
      simp [hit]
    · obtain ⟨D,okD,same,e⟩ := specializeTrue C 10 fan output
      obtain ⟨x,hx⟩ := complement D okD (same ▸ size)
      let u := x 0 || x 2
      let w := List.ofFn x ++ [u]
      have lengthW : w.length=10 := by simp [w]
      have miss : w.getD 10 false=false := List.getD_eq_default _ _ (by omega)
      refine ⟨x,?_⟩
      change C.eval (w++[!w.getD 10 false])≠_
      rw [miss];change C.eval (w++[true])≠_
      rw [←e w lengthW (!u)]
      simpa only [w,List.append_assoc,List.cons_append,List.nil_append] using hx
