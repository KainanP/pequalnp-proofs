import Mathlib
import PEqualNP.Defs

private abbrev Gct208Emb := Fin 4 ↪ Fin 6

private abbrev gct208Enumeration : Fintype Gct208Emb :=
  Fintype.ofEquiv {f : Fin 4 → Fin 6 // Function.Injective f}
    (Equiv.subtypeInjectiveEquivEmbedding (Fin 4) (Fin 6))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private lemma gct208One (i : Fin 4) (j : Fin 6) :
    (Finset.univ.filter fun f : Gct208Emb => f i = j).card = 60 := by
  have h := Subsingleton.elim (inferInstance : Fintype Gct208Emb) gct208Enumeration
  rw [show (Finset.univ : Finset Gct208Emb) = gct208Enumeration.elems from
    congrArg (fun enumeration : Fintype Gct208Emb => enumeration.elems) h]
  fin_cases i <;> fin_cases j <;> decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private lemma gct208Two (i : Fin 4) (j : Fin 6) (hi : i ≠ 0) (hj : j ≠ 0) :
    (Finset.univ.filter fun f : Gct208Emb => f 0 = j ∧ f i = 0).card = 12 := by
  have h := Subsingleton.elim (inferInstance : Fintype Gct208Emb) gct208Enumeration
  rw [show (Finset.univ : Finset Gct208Emb) = gct208Enumeration.elems from
    congrArg (fun enumeration : Fintype Gct208Emb => enumeration.elems) h]
  fin_cases i <;> fin_cases j <;> first | contradiction | decide

private lemma gct208SumFilter {α : Type} [Fintype α] (p : α → Prop) [DecidablePred p]
    (z : ℂ) :
    (∑ x, if p x then z else 0) = ((Finset.univ.filter p).card : ℂ) * z := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

private lemma gct208SumRow (a : Fin 6 → ℂ) :
    (∑ f : Gct208Emb, a (f 0)) = 60 * ∑ j, a j := by
  calc
    _ = ∑ f : Gct208Emb, ∑ j : Fin 6, if f 0 = j then a j else 0 := by
      apply Finset.sum_congr rfl
      intro f _
      simp
    _ = ∑ j : Fin 6, ∑ f : Gct208Emb, if f 0 = j then a j else 0 := Finset.sum_comm
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [gct208SumFilter, gct208One]
      norm_num

private lemma gct208SumCross (a : Fin 6 → ℂ) (b : Fin 4 → ℂ)
    (ha0 : a 0 = 0) (ha : ∑ j, a j = 0) (i : Fin 4) :
    (∑ f : Gct208Emb, a (f 0) * (if f i = 0 then b i else 0)) = 0 := by
  by_cases hi : i = 0
  · subst i
    apply Finset.sum_eq_zero
    intro f _
    split_ifs with h <;> simp [h, ha0]
  calc
    _ = ∑ f : Gct208Emb, ∑ j : Fin 6,
          if f 0 = j ∧ f i = 0 then a j * b i else 0 := by
      apply Finset.sum_congr rfl
      intro f _
      by_cases h : f i = 0 <;> simp [h]
    _ = ∑ j : Fin 6, ∑ f : Gct208Emb,
          if f 0 = j ∧ f i = 0 then a j * b i else 0 := Finset.sum_comm
    _ = ∑ j : Fin 6, 12 * (a j * b i) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j = 0
      · subst j
        simp [ha0]
      · rw [gct208SumFilter, gct208Two i j hi hj]
        norm_num
    _ = 0 := by rw [← Finset.mul_sum, ← Finset.sum_mul, ha, zero_mul, mul_zero]

private def gct208Row (x : Fin 7 → ℂ) : Fin 6 → ℂ :=
  ![0, x 0, x 1, x 2, x 3, -(x 0 + x 1 + x 2 + x 3)]

private def gct208Col (x : Fin 7 → ℂ) : Fin 4 → ℂ :=
  ![-(x 4 + x 5 + x 6), x 4, x 5, x 6]

private def gct208Cross (a : Fin 6 → ℂ) (b : Fin 4 → ℂ) (p : Fin 4 × Fin 6) : ℂ :=
  (if p.1 = 0 then a p.2 else 0) + (if p.2 = 0 then b p.1 else 0)

private noncomputable def gct208Map : (Fin 7 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 6 → ℂ) where
  toFun x := gct208Cross (gct208Row x) (gct208Col x)
  map_add' x y := by
    funext p
    obtain ⟨i, j⟩ := p
    fin_cases i <;> fin_cases j <;>
      simp [gct208Cross, gct208Row, gct208Col, Pi.add_apply] <;> ring
  map_smul' c x := by
    funext p
    obtain ⟨i, j⟩ := p
    fin_cases i <;> fin_cases j <;>
      simp [gct208Cross, gct208Row, gct208Col, Pi.smul_apply, smul_eq_mul] <;> ring

private lemma gct208Injective : Function.Injective gct208Map := by
  intro x y h
  have h0 := congrFun h (0, 1)
  have h1 := congrFun h (0, 2)
  have h2 := congrFun h (0, 3)
  have h3 := congrFun h (0, 4)
  have h4 := congrFun h (1, 0)
  have h5 := congrFun h (2, 0)
  have h6 := congrFun h (3, 0)
  simp [gct208Map, gct208Cross, gct208Row, gct208Col] at h0 h1 h2 h3 h4 h5 h6
  funext k
  fin_cases k <;> assumption

private lemma gct208Product (a : Fin 6 → ℂ) (b : Fin 4 → ℂ) (ha0 : a 0 = 0)
    (f : Gct208Emb) :
    (∏ i, (1 + gct208Cross a b (i, f i))) =
      (1 + a (f 0)) * (1 + ∑ i, if f i = 0 then b i else 0) := by
  have distinct {i j : Fin 4} (hij : i ≠ j) (hi : f i = 0) : f j ≠ 0 :=
    fun hj => hij (f.injective (hi.trans hj.symm))
  simp only [Fin.prod_univ_four, Fin.sum_univ_four]
  by_cases h0 : f 0 = 0
  · have h1 := distinct (j := 1) (by decide) h0
    have h2 := distinct (j := 2) (by decide) h0
    have h3 := distinct (j := 3) (by decide) h0
    simp [gct208Cross, h0, h1, h2, h3, ha0]
  by_cases h1 : f 1 = 0
  · have h2 := distinct (j := 2) (by decide) h1
    have h3 := distinct (j := 3) (by decide) h1
    simp [gct208Cross, h0, h1, h2, h3]
  by_cases h2 : f 2 = 0
  · have h3 := distinct (j := 3) (by decide) h2
    simp [gct208Cross, h0, h1, h2, h3]
  simp [gct208Cross, h0, h1, h2]

private lemma gct208Total (a : Fin 6 → ℂ) (b : Fin 4 → ℂ)
    (ha0 : a 0 = 0) (ha : ∑ j, a j = 0) (hb : ∑ i, b i = 0) :
    (∑ f : Gct208Emb, ∏ i, (1 + gct208Cross a b (i, f i))) = 360 := by
  have hrow : (∑ f : Gct208Emb, a (f 0)) = 0 := by
    rw [gct208SumRow, ha, mul_zero]
  have hcol : (∑ f : Gct208Emb, ∑ i : Fin 4, if f i = 0 then b i else 0) = 0 := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ i : Fin 4, 60 * b i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [gct208SumFilter, gct208One]
        norm_num
      _ = 0 := by rw [← Finset.mul_sum, hb, mul_zero]
  have hcross : (∑ f : Gct208Emb, a (f 0) * ∑ i : Fin 4, if f i = 0 then b i else 0) = 0 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun i _ => gct208SumCross a b ha0 ha i
  have hsize : Fintype.card Gct208Emb = 360 := by
    rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]
    decide
  simp_rw [gct208Product a b ha0, add_mul, mul_add, one_mul, mul_one, Finset.sum_add_distrib]
  rw [hrow, hcol, hcross]
  simp [hsize]

theorem PEqualNP.Outside.L_gct_208 :
    ∃ L : Submodule ℂ (Fin 4 × Fin 6 → ℂ), (∀ t ∈ L, (∑ f : Fin 4 ↪ Fin 6, ∏ i, (1 + t (i, f i))) = 360) ∧ Module.finrank ℂ L = 7 := by
  refine ⟨LinearMap.range gct208Map, ?_, ?_⟩
  · intro t ht
    rcases ht with ⟨x, rfl⟩
    change (∑ f : Gct208Emb, ∏ i, (1 + gct208Cross (gct208Row x) (gct208Col x) (i, f i))) = 360
    apply gct208Total
    · rfl
    · simp [gct208Row, Fin.sum_univ_succ]
    · simp [gct208Col, Fin.sum_univ_four]; ring
  · rw [LinearMap.finrank_range_of_inj gct208Injective, Module.finrank_pi, Fintype.card_fin]
