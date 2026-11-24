import Mathlib.Data.Fin.Basic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.R_meta_3020_2
  (old :
    let F := fun x : Fin 9 → Bool => [1,12,23,34,40,5,16,27,38,57,68,85].any (fun k : Nat => x (Fin.ofNat 9 (k / 10)) && x (Fin.ofNat 9 (k % 10)))
    let W := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 2]
    let fail := fun u : (Fin 9 → Bool) → Bool => ∀ C : Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 → ∃ x, C.eval (W x ++ [u x]) ≠ F x
    ∀ k : Fin 12, fail (fun x => if k.val = 11 then true else (W x).getD k.val false))
  (fresh :
    let F := fun x : Fin 9 → Bool => [1,12,23,34,40,5,16,27,38,57,68,85].any (fun k : Nat => x (Fin.ofNat 9 (k / 10)) && x (Fin.ofNat 9 (k % 10)))
    let W := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 2]
    let fail := fun u : (Fin 9 → Bool) → Bool => ∀ C : Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 → ∃ x, C.eval (W x ++ [u x]) ≠ F x
    ∀ i j : Nat, i < j → j < 10 →
    (j = 9 → i ≠ 0 ∧ i ≠ 2) → fail (fun x => (W x).getD i false && (W x).getD j false)) :
  ∀ (x1 : List (Fin (11 : ℕ))),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin (11 : ℕ)) => x7.getD (↑x8) Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  let F := fun x : Fin 9 → Bool => [1,12,23,34,40,5,16,27,38,57,68,85].any (fun k : Nat => x (Fin.ofNat 9 (k / 10)) && x (Fin.ofNat 9 (k % 10)))
  let W := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 2]
  let fail := fun u : (Fin 9 → Bool) → Bool => ∀ C : Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 → ∃ x, C.eval (W x ++ [u x]) ≠ F x
  let D (a : Fin 11) (x : Fin 9 → Bool) := (W x).getD a.val false
  have oldWire (a : Fin 11) : fail (D a) := by
    have hn : a.val ≠ 11 := by omega
    simpa only [Fin.val_castSucc,if_neg hn] using old a.castSucc
  have top : fail (fun _ => true) := old (11 : Fin 12)
  have empty (x) : D (10 : Fin 11) x = false := by
    change (W x).getD 10 false = false
    apply List.getD_eq_default
    simp [W]
  have bottom : fail (fun _ => false) := by
    have e : D (10 : Fin 11) = fun _ => false := funext empty
    rw [← e]
    exact oldWire _
  have sorted (a b : Fin 11) (le : a.val ≤ b.val) :
      fail (fun x => D a x && D b x) := by
    by_cases same : a = b
    · subst b; simpa only [Bool.and_self] using oldWire a
    have lt : a.val < b.val := by
      have ne : a.val ≠ b.val := fun e => same (Fin.ext e)
      omega
    by_cases high : b.val = 10
    · have eb : b = (10 : Fin 11) := Fin.ext high
      subst b; simpa only [empty,Bool.and_false] using bottom
    by_cases absorb : b.val=9 ∧ (a.val=0 ∨ a.val=2)
    · have eb : b = (9 : Fin 11) := Fin.ext absorb.1
      subst b
      have iden : (fun x => D a x && D (9 : Fin 11) x) = D a := by
        funext x
        have h9 : D (9 : Fin 11) x = (x 0 || x 2) := rfl
        rw [h9]
        rcases absorb.2 with e|e
        · have ea : a = (0 : Fin 11) := Fin.ext e
          subst a
          change (x 0 && (x 0 || x 2)) = x 0
          cases x 0 <;> rfl
        · have ea : a = (2 : Fin 11) := Fin.ext e
          subst a
          change (x 2 && (x 0 || x 2)) = x 2
          cases x 2 <;> cases x 0 <;> rfl
      rw [iden]
      exact oldWire _
    · exact fresh a.val b.val lt (by omega) (fun eq => ⟨fun h => absorb ⟨eq,Or.inl h⟩,fun h => absorb ⟨eq,Or.inr h⟩⟩)
  intro args len
  have choose : fail (fun x => GateOp.and.eval (args.map fun i => D i x)) := by
    cases args with
    | nil => exact top
    | cons a as =>
      cases as with
      | nil =>
        change fail (fun x => D a x && true)
        simpa only [Bool.and_true] using oldWire a
      | cons b bs =>
        have en : bs = [] := by simpa using len
        subst bs
        change fail (fun x => D a x && (D b x && true))
        simp only [Bool.and_true]
        by_cases order : a.val ≤ b.val
        · exact sorted a b order
        · have e : (fun x => D a x && D b x) = (fun x => D b x && D a x) :=
            funext fun x => Bool.and_comm _ _
          rw [e]
          exact sorted b a (by omega)
  intro C hf hc
  obtain ⟨x,hx⟩ := choose C hf hc
  refine ⟨x,?_⟩
  have targetEq : F x =
    (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
     x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
    dsimp [F,List.any]
    simp only [Bool.or_false,Bool.or_assoc]
    rfl
  exact fun eq => hx (eq.trans targetEq.symm)
