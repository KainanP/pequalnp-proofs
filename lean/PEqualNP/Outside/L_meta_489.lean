import PEqualNP.Defs

private lemma meta489Length (φ : PEqualNP.Search.CNF) :
    (φ.flatMap (fun c => c.map some ++ [none])).length ≤
      (PEqualNP.Search.encodeCNF φ).length := by
  have literalLength (l : PEqualNP.Search.Literal) :
      1 ≤ (PEqualNP.Search.encodeLiteral l).length := by
    simp [PEqualNP.Search.encodeLiteral]
  have clauseLength (c : PEqualNP.Search.Clause) :
      c.length + 1 ≤ (PEqualNP.Search.encodeClause c).length := by
    induction c with
    | nil => decide
    | cons l rest ih =>
      simp only [PEqualNP.Search.encodeClause, List.flatMap_cons, List.length_append,
        List.length_cons, List.length_nil] at ih ⊢
      have hl := literalLength l
      omega
  induction φ with
  | nil => decide
  | cons c rest ih =>
    simp only [PEqualNP.Search.encodeCNF, List.flatMap_cons, List.length_append,
      List.length_map, List.length_cons, List.length_nil] at ih ⊢
    exact Nat.add_le_add (clauseLength c) ih

theorem PEqualNP.Outside.L_meta_489 :
    ∀ (φ : PEqualNP.Search.CNF) (e : ℕ → ℕ), (∀ z, e z = (φ.flatMap (fun c => c.map some ++ [none])).findIdx (fun o => o.any (fun l => l.1 == z))) → (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z < (PEqualNP.Search.encodeCNF φ).length) ∧ ∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∀ z' ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z = e z' → z = z' := by
  intro φ e he
  let items : List (Option PEqualNP.Search.Literal) :=
    φ.flatMap (fun c => c.map some ++ [none])
  let matchesVar (z : ℕ) (item : Option PEqualNP.Search.Literal) : Bool :=
    item.any (fun l => l.1 == z)
  have hits (z : ℕ) (hz : z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ) :
      e z < items.length ∧
        ∃ l : PEqualNP.Search.Literal, items[e z]? = some (some l) ∧ l.1 = z := by
    have witness : ∃ o ∈ items, matchesVar z o = true := by
      simp only [PEqualNP.MetaComplexity.CoverPromise.vars, List.mem_toFinset,
        List.mem_flatMap, List.mem_map] at hz
      rcases hz with ⟨c, hc, l, hl, rfl⟩
      refine ⟨some l, ?_, by simp [matchesVar]⟩
      simp only [items, List.mem_flatMap, List.mem_append, List.mem_map]
      exact ⟨c, hc, Or.inl ⟨l, hl, rfl⟩⟩
    have hidx : e z = items.findIdx (matchesVar z) := he z
    rw [hidx]
    have hlt := List.findIdx_lt_length_of_exists witness
    refine ⟨hlt, ?_⟩
    have hmatch := List.findIdx_getElem (w := hlt)
    cases hitem : items[items.findIdx (matchesVar z)]'hlt with
    | none => simp [matchesVar, hitem] at hmatch
    | some l =>
      exact ⟨l, by rw [List.getElem?_eq_getElem hlt, hitem], by simpa [matchesVar, hitem] using hmatch⟩
  constructor
  · intro z hz
    exact lt_of_lt_of_le (hits z hz).1 (meta489Length φ)
  · intro z hz z' hz' heq
    obtain ⟨l, hl, hlz⟩ := (hits z hz).2
    obtain ⟨l', hl', hlz'⟩ := (hits z' hz').2
    rw [heq, hl'] at hl
    have same : l = l' := by simpa using hl.symm
    exact hlz.symm.trans ((congrArg Prod.fst same).trans hlz')
