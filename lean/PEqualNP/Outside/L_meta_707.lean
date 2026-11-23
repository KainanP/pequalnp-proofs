import PEqualNP.Defs

-- Generic circuit evaluation and projection lemmas adapted from the checked L-meta-634.
namespace PEqualNP.Outside.L_meta_707

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

theorem sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v w : Fin k → Bool) (h : ∀ j, j < i → v j = w j) :
    sideTrue U B F i v = sideTrue U B F i w := by
  unfold sideTrue
  congr 1
  apply propext
  constructor
  · rintro (h1 | ⟨j, hj, hji, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hji, by rw [← h j hji]; exact hv⟩
  · rintro (h1 | ⟨j, hj, hji, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hji, by rw [h j hji]; exact hv⟩

theorem sideTrue_iff {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v : Fin k → Bool) :
    sideTrue U B F i v = true ↔ ((∃ x ∈ B, x ∈ U) ∨ ∃ j ∈ F, j < i ∧ v j = true) := by
  unfold sideTrue
  exact decide_eq_true_iff

theorem sideTrue_mono {n k : ℕ} (U U' B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v w : Fin k → Bool) (hU : U ⊆ U') (h : ∀ j, j < i → v j = true → w j = true)
    (hs : sideTrue U B F i v = true) : sideTrue U' B F i w = true := by
  rw [sideTrue_iff] at hs ⊢
  rcases hs with ⟨x, hx, hxU⟩ | ⟨j, hj, hji, hv⟩
  · exact Or.inl ⟨x, hx, hU hxU⟩
  · exact Or.inr ⟨j, hj, hji, h j hji hv⟩

theorem fuel_succ {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ d : ℕ, ∀ i : Fin C.size, i.val < d →
      gateValFuel C U (d + 1) i = gateValFuel C U d i := by
  intro d
  induction d with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ d ih =>
    intro i hi
    show (sideTrue U (C.leftVars i) (C.leftGates i) i (gateValFuel C U (d + 1)) &&
        sideTrue U (C.rightVars i) (C.rightGates i) i (gateValFuel C U (d + 1))) =
      (sideTrue U (C.leftVars i) (C.leftGates i) i (gateValFuel C U d) &&
        sideTrue U (C.rightVars i) (C.rightGates i) i (gateValFuel C U d))
    have hc : ∀ j : Fin C.size, j < i → gateValFuel C U (d + 1) j = gateValFuel C U d j := by
      intro j hji
      apply ih
      have : j.val < i.val := hji
      omega
    rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hc,
      sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hc]

theorem gateVal_rec {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i = (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
      sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have h := fuel_succ C U C.size i i.isLt
  exact h.symm

theorem gateVal_iff {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i = true ↔
      (((∃ x ∈ C.leftVars i, x ∈ U) ∨ ∃ j ∈ C.leftGates i, j < i ∧ C.gateVal U j = true) ∧
       ((∃ x ∈ C.rightVars i, x ∈ U) ∨ ∃ j ∈ C.rightGates i, j < i ∧ C.gateVal U j = true)) := by
  rw [gateVal_rec, Bool.and_eq_true, sideTrue_iff, sideTrue_iff]

theorem gateVal_iff_wf {n : ℕ} (C : AndCountCircuit n) (hC : C.WellFormed) (U : Finset (Fin n))
    (i : Fin C.size) :
    C.gateVal U i = true ↔
      (((∃ x ∈ C.leftVars i, x ∈ U) ∨ ∃ j ∈ C.leftGates i, C.gateVal U j = true) ∧
       ((∃ x ∈ C.rightVars i, x ∈ U) ∨ ∃ j ∈ C.rightGates i, C.gateVal U j = true)) := by
  rw [gateVal_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rcases h1 with h | ⟨j, hj, _, hv⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, hv⟩
    · rcases h2 with h | ⟨j, hj, _, hv⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, hv⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rcases h1 with h | ⟨j, hj, hv⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, (hC i).1 j hj, hv⟩
    · rcases h2 with h | ⟨j, hj, hv⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, (hC i).2 j hj, hv⟩

theorem eval_iff {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    C.eval U = true ↔
      ((∃ v ∈ C.outVars, v ∈ U) ∨ ∃ j ∈ C.outGates, C.gateVal U j = true) := by
  unfold AndCountCircuit.eval
  exact decide_eq_true_iff

abbrev Hit {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (v : Fin k → Bool) :=
  (∃ x ∈ B, x ∈ U) ∨ ∃ j ∈ F, v j = true

theorem joinHit {n k l : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k))
    (a : Fin k → Finset (Fin n)) (t : Fin k → Finset (Fin l))
    (v : Fin k → Bool) (w : Fin l → Bool)
    (h : ∀ j ∈ F, v j = true ↔ Hit U (a j) (t j) w) :
    Hit U B F v ↔ Hit U (B ∪ F.biUnion a) (F.biUnion t) w := by
  unfold Hit at *
  simp only [Finset.mem_union,Finset.mem_biUnion]
  constructor
  · rintro (⟨x,hx,hu⟩ | ⟨j,hj,hv⟩)
    · exact Or.inl ⟨x,Or.inl hx,hu⟩
    · rcases (h j hj).mp hv with ⟨x,hx,hu⟩ | ⟨z,hz,hw⟩
      · exact Or.inl ⟨x,Or.inr ⟨j,hj,hx⟩,hu⟩
      · exact Or.inr ⟨z,⟨j,hj,hz⟩,hw⟩
  · rintro (⟨x,hx,hu⟩ | ⟨z,⟨j,hj,hz⟩,hw⟩)
    · rcases hx with hx | ⟨j,hj,hx⟩
      · exact Or.inl ⟨x,hx,hu⟩
      · exact Or.inr ⟨j,hj,(h j hj).mpr (Or.inl ⟨x,hx,hu⟩)⟩
    · exact Or.inr ⟨j,hj,(h j hj).mpr (Or.inr ⟨z,hz,hw⟩)⟩

theorem flattened {n : ℕ} (C : AndCountCircuit n) (D : Set (Finset (Fin n)))
    (S : Finset (Fin C.size)) (repl : ∀ i ∈ S, ∃ B F, (∀ j ∈ F, j < i) ∧
      ∀ U ∈ D, C.gateVal U i = true ↔ Hit U B F (C.gateVal U)) (i : Fin C.size) :
    ∃ A K, (∀ j ∈ K, j ∉ S ∧ j ≤ i) ∧ ∀ U ∈ D, C.gateVal U i = true ↔ Hit U A K (C.gateVal U) := by
  classical
  apply wellFounded_lt.induction i
  intro i ih
  by_cases hi : i ∈ S
  · obtain ⟨B,F,hlt,hval⟩ := repl i hi
    have pick (j : Fin C.size) : ∃ A K, j ∈ F → (∀ z ∈ K, z ∉ S ∧ z ≤ j) ∧
        ∀ U ∈ D, C.gateVal U j = true ↔ Hit U A K (C.gateVal U) := by
      by_cases hj : j ∈ F
      · obtain ⟨A,K,hk,hs⟩ := ih j (hlt j hj)
        exact ⟨A,K,fun _ => ⟨hk,hs⟩⟩
      · exact ⟨∅,∅,fun h => (hj h).elim⟩
    choose a t ht using pick
    refine ⟨B ∪ F.biUnion a,F.biUnion t,?_,?_⟩
    · intro z hz
      obtain ⟨j,hj,hz'⟩ := Finset.mem_biUnion.mp hz
      obtain ⟨h1,h2⟩ := (ht j hj).1 z hz'
      exact ⟨h1,h2.trans (hlt j hj).le⟩
    · intro U hU
      exact (hval U hU).trans (joinHit U B F a t _ _ (fun j hj => (ht j hj).2 U hU))
  · refine ⟨∅,{i},?_,?_⟩
    · intro j hj
      have : j = i := Finset.mem_singleton.mp hj
      simpa [this] using And.intro hi (le_refl i)
    · intro U _
      simp [Hit]

end PEqualNP.Outside.L_meta_707

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit PEqualNP.Outside.L_meta_707 in
theorem PEqualNP.Outside.L_meta_707 : ∀ (n : ℕ) (C : PEqualNP.AndCount.AndCountCircuit n), C.WellFormed →
    ∀ (D : Set (Finset (Fin n))) (S : Finset (Fin C.size)),
      (∀ i ∈ S, ∃ B : Finset (Fin n), ∃ F : Finset (Fin C.size), (∀ j ∈ F, j < i) ∧
        ∀ U ∈ D, C.gateVal U i = true ↔ ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, C.gateVal U j = true)) →
      ∃ C' : PEqualNP.AndCount.AndCountCircuit n, C'.WellFormed ∧ C'.size + S.card ≤ C.size ∧
        ∀ U ∈ D, C'.eval U = C.eval U := by
  classical
  intro n C wf D S repl
  choose a t earlier spec using flattened C D S repl
  let K := Finset.univ \ S
  let e := K.orderEmbOfFin rfl
  have onto (j : Fin C.size) (hj : j ∉ S) : ∃ i : Fin K.card, e i = j := by
    have mem : j ∈ K := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hj⟩
    let u : K := ⟨j,mem⟩
    exact ⟨(K.orderIsoOfFin rfl).symm u,congrArg Subtype.val ((K.orderIsoOfFin rfl).apply_symm_apply u)⟩
  let A (B : Finset (Fin n)) (F : Finset (Fin C.size)) := B ∪ F.biUnion a
  let R (F : Finset (Fin C.size)) := Finset.univ.filter (fun i : Fin K.card => e i ∈ F.biUnion t)
  let C' : AndCountCircuit n := ⟨K.card, fun i => A (C.leftVars (e i)) (C.leftGates (e i)),
    fun i => R (C.leftGates (e i)), fun i => A (C.rightVars (e i)) (C.rightGates (e i)),
    fun i => R (C.rightGates (e i)), A C.outVars C.outGates, R C.outGates⟩
  have prev (i : Fin K.card) (F : Finset (Fin C.size)) (hl : ∀ j ∈ F, j < e i) :
      ∀ h ∈ R F, h < i := by
    intro h hh
    obtain ⟨j,hj,hz⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hh).2
    exact e.lt_iff_lt.mp (lt_of_le_of_lt (earlier j (e h) hz).2 (hl j hj))
  have wf' : C'.WellFormed := fun i => ⟨prev i _ (wf (e i)).1,prev i _ (wf (e i)).2⟩
  refine ⟨C',wf',?_,?_⟩
  · have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
    change K.card + S.card ≤ C.size
    simpa [K] using h.le
  · intro U hU
    have transfer (B : Finset (Fin n)) (F : Finset (Fin C.size))
        (correct : ∀ h ∈ R F, C'.gateVal U h = C.gateVal U (e h)) :
        Hit U (A B F) (R F) (C'.gateVal U) ↔ Hit U B F (C.gateVal U) := by
      rw [joinHit U B F a t (C.gateVal U) (C.gateVal U) (fun j _ => (spec j) U hU)]
      change (_ ∨ _) ↔ (_ ∨ _)
      apply or_congr_right
      constructor
      · rintro ⟨h,hh,hv⟩
        exact ⟨e h,(Finset.mem_filter.mp hh).2,(correct h hh) ▸ hv⟩
      · rintro ⟨z,hz,hv⟩
        obtain ⟨j,hj,hz'⟩ := Finset.mem_biUnion.mp hz
        obtain ⟨h,rfl⟩ := onto z (earlier j z hz').1
        have hh : h ∈ R F := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩
        exact ⟨h,hh,(correct h hh).symm ▸ hv⟩
    have corr (i : Fin K.card) : C'.gateVal U i = C.gateVal U (e i) := by
      apply wellFounded_lt.induction i
      intro j ih
      apply Bool.eq_iff_iff.mpr
      rw [gateVal_iff_wf C' wf',gateVal_iff_wf C wf]
      exact and_congr (transfer _ _ (fun h hh => ih h ((wf' j).1 h hh)))
        (transfer _ _ (fun h hh => ih h ((wf' j).2 h hh)))
    apply Bool.eq_iff_iff.mpr
    rw [eval_iff,eval_iff]
    exact transfer _ _ (fun h _ => corr h)
