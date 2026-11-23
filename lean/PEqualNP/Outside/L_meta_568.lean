import PEqualNP.Defs

-- Initial reader arguments adapted from the checked L-meta-168 and L-meta-169.
-- Wire reindexing adapted from Library/Helpers/RRDistinguisher.lean.

/-! The gate-elimination argument adapts `MetaComplexity/Helpers/Elim.lean`.
  The helpers are private because this gap allows only `Mathlib` and `PEqualNP.Defs`. -/

namespace PEqualNP.Outside

namespace L_meta_168_helpers

open PEqualNP.CircuitLowerBounds

/-- Reading a list at a position other than its length ignores a snoc. -/
private theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ)
    (h : j ≠ L.length) : (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

/-- Reading a snoc at the length of the list gives the new element. -/
private theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) :
    (L ++ [S]).getD L.length d = S := by
  simp

private theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ)
    (h : L.length = k) : (L ++ [S]).getD k d = S := by
  subst h; simp

/-- Run gates on a wire list: the fold inside `Circuit.wires`. -/
private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

private theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

private theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

/-- The bits already on the wire list are untouched by later gates. -/
private theorem getD_wiresFrom_input (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length →
      (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i h
    have h' : i < (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length := by
      simp; omega
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i h'
    exact this.trans (List.getD_append _ _ _ _ h)

/-- Membership in a one-element take is a head. -/
private theorem mem_take_one {α : Type} {a : α} (l : List α) :
    a ∈ l.take 1 ↔ l.head? = some a := by
  rw [List.take_one]
  cases l <;> simp [eq_comm]

/-- A NOT gate reads only its first wire: drop the others. -/
private def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

private theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

/-- The allowed gates: AND, OR, NOT reading at most two wires. -/
private def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

private theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

private theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

/-- The normalised predicate of the statement: a gate reads input `n`. -/
private theorem mem_normGate_inputs_iff (n : ℕ) (g : Gate) :
    n ∈ (normGate g).inputs ↔
      (g.op = GateOp.not ∧ g.inputs.head? = some n) ∨
      (g.op ≠ GateOp.not ∧ n ∈ g.inputs) := by
  obtain ⟨op, inputs⟩ := g
  cases op with
  | not =>
    simp only [normGate]
    rw [mem_take_one inputs]
    simp
  | and => simp [normGate]
  | or => simp [normGate]
  | mod m => simp [normGate]
  | maj => simp [normGate]

/-- The status of an old wire: a constant, or the wire `j` of the new circuit. -/
private abbrev Stat := Sum Bool ℕ

private def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

private def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

private def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

private def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

private def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

/-- What a gate becomes, given the statuses of the wires it reads; `m` is the number of the
  next new wire. The result is the gate to emit, if any, and the status of the gate's wire. -/
private def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

private theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

private theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

private theorem simplify_sound (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

/-- One step of the pass: `acc.1` holds the statuses of the old wires, `acc.2` the new gates. -/
private def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

private def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

private theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

private theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

private theorem elim_len_add_count_le (n k : ℕ) (gs : List Gate) :
    ∀ acc : List Stat × List Gate,
      (∀ g ∈ gs, NOk g) → k < acc.1.length →
      (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
      (elim n gs acc).2.length + gs.countP (fun g => decide (k ∈ g.inputs))
        ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _; simp [elim]
  | cons g gs ih =>
    intro acc hok hk hc
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3]
    have hok' : ∀ g' ∈ gs, NOk g' := fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')
    have hk' : k < (elimStep n acc g).1.length := by simp [elimStep]; omega
    have hc' : ∃ c, (elimStep n acc g).1.getD k (Sum.inl false) = Sum.inl c := by
      obtain ⟨c, hc⟩ := hc
      refine ⟨c, ?_⟩
      simp only [elimStep]
      rw [getD_snoc_ne _ _ _ _ (by omega)]
      exact hc
    have hih := ih (elimStep n acc g) hok' hk' hc'
    by_cases hkg : k ∈ g.inputs
    · have hcnt : (g :: gs).countP (fun g => decide (k ∈ g.inputs))
          = gs.countP (fun g => decide (k ∈ g.inputs)) + 1 := by
        rw [List.countP_cons]
        simp [hkg]
      have hsim : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact (hok g List.mem_cons_self).1.1
        · simpa using (hok g List.mem_cons_self).1.2
        · intro h; simpa using (hok g List.mem_cons_self).2 h
        · obtain ⟨c, hc⟩ := hc
          exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        simp only [elimStep, List.length_append]
        rw [hsim]; simp
      rw [hcnt, List.length_cons]
      omega
    · have hcnt : (g :: gs).countP (fun g => decide (k ∈ g.inputs))
          = gs.countP (fun g => decide (k ∈ g.inputs)) := by
        rw [List.countP_cons]
        simp [hkg]
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      rw [hcnt, List.length_cons]
      omega

private theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

private theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

/-- The invariant of the pass, for one input `y` of the new circuit: `w` are the old wires,
  and every old wire has a valid status whose value on the new wires is the old value. -/
private def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

private theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

/-- The statuses at the start: the first `n` old wires are the new input wires, and the last
  input is the constant `b`. -/
private def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Sum.inr (i : ℕ)) ++ [Sum.inl b]

private theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat))).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, Stat.Valid, Stat.val, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

private theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

/-- If no gate reads wire `n`, two wire lists of the same length that agree off `n` stay in
  agreement off `n` after the gates run. -/
private theorem wiresFrom_agree_off {n : ℕ} (gs : List Gate)
    (hno : ∀ g ∈ gs, n ∉ g.inputs) :
    ∀ w w' : List Bool, w.length = w'.length →
      (∀ i, i ≠ n → w.getD i false = w'.getD i false) →
      ∀ j, j ≠ n → (wiresFrom gs w).getD j false = (wiresFrom gs w').getD j false := by
  induction gs with
  | nil =>
    intro w w' _ hagree j hj
    exact hagree j hj
  | cons g gs ih =>
    intro w w' hlen hagree j hj
    have hno' : ∀ g' ∈ gs, n ∉ g'.inputs :=
      fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')
    have hgn : n ∉ g.inputs := hno g List.mem_cons_self
    have hlen1 : (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length
        = (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)]).length := by
      simp [hlen]
    have hagree1 : ∀ i, i ≠ n →
        (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD i false
        = (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)]).getD i false := by
      intro i hi
      by_cases hlt : i < w.length
      · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (by omega)]
        exact hagree i hi
      · by_cases heq : i = w.length
        · subst heq
          rw [getD_snoc_len w _ _ w.length rfl, getD_snoc_len w' _ _ w.length hlen.symm]
          congr 1
          apply List.map_congr_left
          intro a ha
          exact hagree a (fun e => hgn (e ▸ ha))
        · have hwl : i ≠ w'.length := by omega
          rw [getD_snoc_ne _ _ _ _ heq, getD_snoc_ne _ _ _ _ hwl]
          exact hagree i hi
    exact ih hno'
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
      hlen1 hagree1 j hj

private theorem two_le_countP_of_two_getElem {α : Type} (p : α → Bool) (l : List α)
    (i j : ℕ) (hi : i < l.length) (hj : j < l.length) (hij : i ≠ j)
    (hpi : p l[i] = true) (hpj : p l[j] = true) : 2 ≤ l.countP p := by
  induction l generalizing i j with
  | nil => simp at hi
  | cons a l ih =>
    match i, j with
    | 0, 0 => exact absurd rfl hij
    | 0, j + 1 =>
      have ha : p a = true := by simpa using hpi
      have hj' : j < l.length := by simpa using hj
      have hpj' : p l[j] = true := by simpa using hpj
      rw [List.countP_cons, if_pos ha]
      have hpos : 1 ≤ l.countP p := by
        rw [List.one_le_countP_iff]
        exact ⟨l[j], List.getElem_mem hj', hpj'⟩
      omega
    | i + 1, 0 =>
      have ha : p a = true := by simpa using hpj
      have hi' : i < l.length := by simpa using hi
      have hpi' : p l[i] = true := by simpa using hpi
      rw [List.countP_cons, if_pos ha]
      have hpos : 1 ≤ l.countP p := by
        rw [List.one_le_countP_iff]
        exact ⟨l[i], List.getElem_mem hi', hpi'⟩
      omega
    | i + 1, j + 1 =>
      have hi' : i < l.length := by simpa using hi
      have hj' : j < l.length := by simpa using hj
      have hij' : i ≠ j := by omega
      have hpi' : p l[i] = true := by simpa using hpi
      have hpj' : p l[j] = true := by simpa using hpj
      have hrec := ih i j hi' hj' hij' hpi' hpj'
      rw [List.countP_cons]
      have hle : l.countP p ≤ l.countP p + (if p a then 1 else 0) := Nat.le_add_right _ _
      omega

end L_meta_168_helpers

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open L_meta_168_helpers

private theorem l568_first_unique : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit (n + 1) C → (∃ y : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y false) ≠ PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y true)) → (∃ y y' : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y false) ≠ PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y' false)) → (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n (fun y : Fin n → Bool => PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y false)) s → C.size ≤ s + 1) → ∃ j : Fin C.gates.length, ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some n ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ n ∈ (C.gates.get j).inputs) ∧ ∀ j' : Fin C.gates.length, ((C.gates.get j').op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j').inputs.head? = some n ∨ (C.gates.get j').op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ n ∈ (C.gates.get j').inputs) → j' = j := by
  intro n C hmin hdep hnc hsize
  obtain ⟨hCok, _⟩ := hmin
  set gs : List Gate := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hCok g0 hg0)
  have hout : C.output ≠ n := by
    intro houtn
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    have hv : ∀ z : Fin n → Bool, circuitFun (n + 1) C (Fin.snoc z false) = false := by
      intro z
      show (wiresFrom C.gates (List.ofFn (Fin.snoc z false))).getD C.output false = false
      rw [houtn]
      rw [getD_wiresFrom_input C.gates _ n (by
        rw [List.length_ofFn]; exact Nat.lt_succ_self n)]
      rw [ofFn_snoc]
      rw [getD_snoc_len _ _ _ n (by simp [List.length_ofFn])]
    rw [hv y, hv y']
  have hex : ∃ j : Fin C.gates.length, n ∈ (normGate (C.gates.get j)).inputs := by
    by_contra hnone
    push_neg at hnone
    have hno : ∀ g ∈ gs, n ∉ g.inputs := by
      intro g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
      obtain ⟨i, hi⟩ := List.mem_iff_get.1 hg0
      rw [← hi]
      exact hnone i
    obtain ⟨y, hne⟩ := hdep
    have hlen : (List.ofFn (Fin.snoc y false)).length
        = (List.ofFn (Fin.snoc y true)).length := by simp
    have hagree : ∀ i, i ≠ n →
        (List.ofFn (Fin.snoc y false)).getD i false
          = (List.ofFn (Fin.snoc y true)).getD i false := by
      intro i hi
      rw [ofFn_snoc, ofFn_snoc]
      by_cases hlt : i < n
      · rw [List.getD_append _ _ _ _ (by simpa [List.length_ofFn] using hlt),
            List.getD_append _ _ _ _ (by simpa [List.length_ofFn] using hlt)]
      · have hli : i ≠ (List.ofFn y).length := by simp [List.length_ofFn]; omega
        rw [getD_snoc_ne _ _ _ _ hli, getD_snoc_ne _ _ _ _ hli]
    have hEq := wiresFrom_agree_off (n := n) gs hno _ _ hlen hagree C.output hout
    apply hne
    show (wiresFrom C.gates (List.ofFn (Fin.snoc y false))).getD C.output false
        = (wiresFrom C.gates (List.ofFn (Fin.snoc y true))).getD C.output false
    simpa [hgs, wiresFrom_norm] using hEq
  set acc : List Stat × List Gate := elim n gs (initStats n false, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y false))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n (List.ofFn y) (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n false y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y))
        = circuitFun (n + 1) C (Fin.snoc y false) := by
    intro y
    rw [((hinv y).2 C.output).2]
    rw [hgs, wiresFrom_norm]
    rfl
  have hcs : HasCircuitSize n
      (fun y : Fin n → Bool => circuitFun (n + 1) C (Fin.snoc y false)) acc.2.length := by
    cases hst : acc.1.getD C.output (Sum.inl false) with
    | inl c =>
      exfalso
      obtain ⟨y, y', hne⟩ := hnc
      apply hne
      rw [← hval y, ← hval y', hst]
      rfl
    | inr j =>
      refine ⟨⟨acc.2, j⟩, ?_, le_rfl, ?_⟩
      · intro g hg
        exact elim_ok n gs (initStats n false, []) (by simp) g hg
      · intro y
        change (⟨acc.2, j⟩ : Circuit).eval (List.ofFn y)
          = circuitFun (n + 1) C (Fin.snoc y false)
        rw [← hval y, hst]
        rfl
  have hsize' : C.size ≤ acc.2.length + 1 := hsize acc.2.length hcs
  have hcount_bound : acc.2.length + gs.countP (fun g => decide (n ∈ g.inputs)) ≤ C.size := by
    have h := elim_len_add_count_le n n gs (initStats n false, []) hnok
      (by simp [initStats]) ⟨false, getD_snoc_len _ _ _ _ (by simp)⟩
    simpa [acc, hgs, Circuit.size, List.length_nil, Nat.zero_add] using h
  have hcount_le : gs.countP (fun g => decide (n ∈ g.inputs)) ≤ 1 := by omega
  obtain ⟨j0, hj0⟩ := hex
  refine ⟨j0, (mem_normGate_inputs_iff n (C.gates.get j0)).1 hj0, ?_⟩
  intro j' hj'
  by_contra hne
  have hdec0 : (fun g => decide (n ∈ (normGate g).inputs)) (C.gates.get j0) = true := by
    simpa using hj0
  have hdecj : (fun g => decide (n ∈ (normGate g).inputs)) (C.gates.get j') = true := by
    simpa using (mem_normGate_inputs_iff n (C.gates.get j')).2 hj'
  have hij : j0.val ≠ j'.val := by
    intro h
    exact (Ne.symm hne) (Fin.ext h)
  have h2' := two_le_countP_of_two_getElem (fun g => decide (n ∈ (normGate g).inputs))
    C.gates j0.val j'.val j0.isLt j'.isLt hij hdec0 hdecj
  have h2 : 2 ≤ gs.countP (fun g => decide (n ∈ g.inputs)) := by
    rw [hgs, List.countP_map]
    exact h2'
  omega

end PEqualNP.Outside


namespace PEqualNP.Outside.Meta169

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Constant propagation adapted from MetaComplexity/Helpers/Elim.lean.
private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

private theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht, List.append_assoc]
    rfl

private theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨tail, h, hlen⟩ := wiresFrom_prefix gs w
  simp [h, hlen]

private theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) :
    (L ++ [S]).getD L.length d = S := by
  simp

private def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

/-- A NOT gate reads only its first wire: drop the others. -/
private def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

private theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

/-- An allowed gate whose NOT gates read at most one wire. -/
private def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

private theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

private theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

/-- The status of an old wire: a constant, or the wire `j` of the new circuit. -/
private abbrev Stat := Sum Bool ℕ

private def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

private def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

private def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

private def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

private def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

/-- What a gate becomes, given the statuses of the wires it reads; `m` is the number of the
    next new wire. The result is the gate to emit, if any, and the status of the gate's wire. -/
private def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

private theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

private theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

private theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

/-- One step of the pass: `acc.1` holds the statuses of the old wires, `acc.2` the new gates. -/
private def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

private def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

private theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

private theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

private theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

private theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

private theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

/-- If the status of old wire `k` is a constant and some gate reads wire `k`, one gate is
    saved. -/
private theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

private theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

private theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

/-- The invariant of the pass, for one input `y` of the new circuit: `w` are the old wires,
    and every old wire has a valid status whose value on the new wires is the old value. -/
private def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

private theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

/-- The statuses at the start: the first `n` old wires are the new input wires, and the last
    input is the constant `b`. -/
private def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat)) ++ [Sum.inl b]

private theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat))).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, Stat.Valid, Stat.val, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

private theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

private theorem normGate_op (g : Gate) : (normGate g).op = g.op := by
  obtain ⟨op, ins⟩ := g
  cases op <;> rfl

private theorem normGate_of_ne_not (g : Gate) (h : g.op ≠ GateOp.not) : normGate g = g := by
  obtain ⟨op, ins⟩ := g
  cases op <;> simp_all [normGate]

private theorem normGate_read (g : Gate) (n : ℕ)
    (h : g.op = GateOp.not ∧ g.inputs.head? = some n ∨
      g.op ≠ GateOp.not ∧ n ∈ g.inputs) : n ∈ (normGate g).inputs := by
  rcases h with ⟨hop, hhead⟩ | ⟨hop, hmem⟩
  · have htake : g.inputs.take 1 = [n] := by
      rcases h : g.inputs with _ | ⟨a, ins⟩ <;> simp_all
    simp [normGate, hop, htake]
  · simpa only [normGate_of_ne_not g hop] using hmem

private theorem elim_stat_length (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elim]
  | cons g gs ih =>
    change (elim n gs (elimStep n acc g)).1.length = _
    rw [ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

private theorem elim_read_const (n k : ℕ) (acc : List Stat × List Gate) (g : Gate)
    (hg : NOk g) (hread : k ∈ g.inputs) (b : Bool)
    (hfix : acc.1.getD k (Sum.inl false) = Sum.inl b) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none :=
    simplify_count _ _ _ hg.1.1 (by simpa using hg.1.2)
      (fun h => by simpa using hg.2 h) ⟨b, List.mem_map.mpr ⟨k, hread, hfix⟩⟩
  change (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
  rw [hnone]
  simp

private theorem bad_reader_constant (n m : ℕ) (stats : List Stat) (g : Gate)
    (hg : NOk g) (hread : n ∈ g.inputs) (hfix : stats.getD n (Sum.inl false) = Sum.inl false)
    (hbad : ¬(g.op = GateOp.or ∧ g.inputs.length = 2 ∧
      ∃ w ∈ g.inputs, w ≠ n ∧ w < stats.length)) :
    ∃ b, (simplify g.op m (g.inputs.map fun i => stats.getD i (Sum.inl false))).2 =
      Sum.inl b := by
  obtain ⟨op, ins⟩ := g
  have hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not := hg.1.1
  have hlen : ins.length ≤ 2 := hg.1.2
  simp only [List.getD_eq_getElem?_getD] at hfix
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, rest⟩⟩⟩
    · simp at hread
    · have ha : n = a := by simpa using hread
      subst a
      exact ⟨false, by simp [simplify, simpAnd, hfix]⟩
    · have hmem : n = a ∨ n = b := by simpa using hread
      rcases hmem with ha | hb
      · subst a
        refine ⟨false, ?_⟩
        cases hb : stats[b]?.getD (Sum.inl false) <;> simp [simplify, simpAnd, hfix, hb]
      · subst b
        refine ⟨false, ?_⟩
        cases ha : stats[a]?.getD (Sum.inl false) <;> simp [simplify, simpAnd, hfix, ha]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, rest⟩⟩⟩
    · simp at hread
    · have ha : n = a := by simpa using hread
      subst a
      exact ⟨false, by simp [simplify, simpOr, hfix]⟩
    · have hout (w : ℕ) (hw : w ∈ [a, b]) :
          stats[w]?.getD (Sum.inl false) = Sum.inl false := by
        by_cases hn : w = n
        · simpa only [hn] using hfix
        · have hnlt : ¬w < stats.length := fun hlt => hbad ⟨rfl, rfl, w, hw, hn, hlt⟩
          exact List.getD_eq_default _ _ (Nat.le_of_not_gt hnlt)
      exact ⟨false, by simp [simplify, simpOr, hout a (by simp), hout b (by simp)]⟩
    · simp at hlen
  · have hone : ins.length ≤ 1 := hg.2 rfl
    rcases ins with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp at hread
    · have ha : n = a := by simpa using hread
      subst a
      exact ⟨true, by simp [simplify, simpNot, hfix]⟩
    · simp at hone

private theorem wires_agree (gs : List Gate) (bad : ℕ → Prop) (w w' : List Bool)
    (hlen : w.length = w'.length)
    (hw : ∀ i, ¬bad i → w.getD i false = w'.getD i false)
    (hgs : ∀ g ∈ gs, ∀ i ∈ g.inputs, ¬bad i) :
    ∀ i, ¬bad i → (wiresFrom gs w).getD i false = (wiresFrom gs w').getD i false := by
  induction gs generalizing w w' with
  | nil => exact hw
  | cons g gs ih =>
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    let v' := g.op.eval (g.inputs.map fun i => w'.getD i false)
    have hv : v = v' := by
      dsimp only [v, v']
      congr 1
      exact List.map_congr_left (fun i hi => hw i (hgs g List.mem_cons_self i hi))
    change ∀ i, ¬bad i → (wiresFrom gs (w ++ [v])).getD i false =
      (wiresFrom gs (w' ++ [v'])).getD i false
    apply ih _ _ (by simp [hlen]) _ (fun g hg => hgs g (List.mem_cons_of_mem _ hg))
    intro i hi
    by_cases heq : i = w.length
    · rw [getD_snoc_len _ _ _ _ heq.symm, getD_snoc_len _ _ _ _ (hlen.symm.trans heq.symm), hv]
    · rw [getD_snoc_ne _ _ _ _ heq, getD_snoc_ne _ _ _ _ (by omega)]
      exact hw i hi

end PEqualNP.Outside.Meta169

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.Meta169 in
private theorem PEqualNP.Outside.l568_first_or : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit (n + 1) C → (∃ y : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y false) ≠ PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y true)) → (∃ y y' : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y false) ≠ PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y' false)) → (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n (fun y : Fin n → Bool => PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y false)) s → C.size ≤ s + 1) → ∀ j : Fin C.gates.length, ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some n ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ n ∈ (C.gates.get j).inputs) → (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get j).inputs.length = 2 ∧ n ∈ (C.gates.get j).inputs ∧ ∃ w ∈ (C.gates.get j).inputs, w ≠ n ∧ w < n + 1 + j.val := by
  classical
  intro n C hmin hdep hnonconst htight j hreads
  by_contra hshape
  let gs := C.gates.map normGate
  let pre := gs.take j.val
  let g := normGate (C.gates.get j)
  let post := gs.drop (j.val + 1)
  let m := n + 1 + j.val
  let start : List Stat × List Gate := (initStats n false, [])
  let before := elim n pre start
  let after := elimStep n before g
  let final := elim n post after
  have hj : j.val < gs.length := by simp [gs]
  have hsplit : gs = pre ++ g :: post := by
    have hs := List.take_append_drop j.val gs
    rw [List.drop_eq_getElem_cons hj] at hs
    simpa [pre, g, post, gs, List.get_eq_getElem] using hs.symm
  have hPreLen : pre.length = j.val := by
    simp [pre, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hSize : C.size = pre.length + 1 + post.length := by
    have hs := congrArg List.length hsplit
    have hg : gs.length = C.size := by simp [gs, Circuit.size]
    simp only [List.length_append, List.length_cons] at hs
    omega
  have hok : ∀ k ∈ gs, NOk k := by
    intro k hk
    obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hk
    exact normGate_nok _ (hmin.1 _ hk')
  have hg : NOk g := hok g (by rw [hsplit]; simp)
  have hpre : ∀ k ∈ pre, NOk k := fun k hk =>
    hok k (by rw [hsplit]; exact List.mem_append_left _ hk)
  have hpost : ∀ k ∈ post, NOk k := fun k hk =>
    hok k (by rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hk))
  have hread : n ∈ g.inputs := normGate_read _ _ hreads
  have hm : before.1.length = m := by
    rw [elim_stat_length]
    simp [start, initStats, m, hPreLen]
  have hbad : ¬(g.op = GateOp.or ∧ g.inputs.length = 2 ∧
      ∃ w ∈ g.inputs, w ≠ n ∧ w < before.1.length) := by
    intro ⟨hop, hlen, w, hw, hne, hlt⟩
    have hop' : (C.gates.get j).op = GateOp.or := (normGate_op _).symm.trans hop
    have hgn : g = C.gates.get j := normGate_of_ne_not _ (by rw [hop']; simp)
    rw [hgn] at hlen hw
    exact hshape ⟨hop', hlen, by simpa only [hgn] using hread, w, hw, hne, by simpa [hm, m] using hlt⟩
  have hstart : n < start.1.length := by simp [start, initStats]
  have hfix : start.1.getD n (Sum.inl false) = Sum.inl false := by
    simp [start, initStats]
  have hbefore : before.1.getD n (Sum.inl false) = Sum.inl false := by
    exact (elim_getD n n _ pre start hstart).trans hfix
  -- A reader with the wrong shape becomes a constant after fixing the last input.
  obtain ⟨b, hconst⟩ := bad_reader_constant n (n + before.2.length) before.1 g hg hread hbefore hbad
  have hSaved : after.2.length = before.2.length := elim_read_const n n before g hg hread false hbefore
  have hAfterLen : after.1.length = m + 1 := by simp [after, elimStep, hm]
  have hAfterN : after.1.getD n (Sum.inl false) = Sum.inl false := by
    change (before.1 ++ [_]).getD n (Sum.inl false) = Sum.inl false
    rw [getD_snoc_ne _ _ _ _ (by rw [hm]; dsimp [m]; omega), hbefore]
  have hAfterM : after.1.getD m (Sum.inl false) = Sum.inl b := by
    change (before.1 ++ [_]).getD m (Sum.inl false) = Sum.inl b
    rw [getD_snoc_len _ _ _ _ hm, hconst]
  have hFinal : elim n gs start = final := by
    rw [hsplit]
    simp only [elim, List.foldl_append]
    rfl
  have heval (y : Fin n → Bool) :
      (final.1.getD C.output (Sum.inl false)).val (wiresFrom final.2 (List.ofFn y)) =
        circuitFun (n + 1) C (Fin.snoc y false) := by
    have hv := (inv_elim n (List.ofFn y) (by simp) gs _ start
      (fun k hk => (hok k hk).1) (inv_init n false y)).2 C.output
    rw [hFinal] at hv
    simp only [circuitFun, Circuit.eval, ofFn_snoc]
    change _ = (wiresFrom C.gates (List.ofFn y ++ [false])).getD C.output false
    rw [← wiresFrom_norm C.gates]
    exact hv.2
  obtain ⟨out, hout⟩ : ∃ out, final.1.getD C.output (Sum.inl false) = Sum.inr out := by
    cases h : final.1.getD C.output (Sum.inl false) with
    | inr out => exact ⟨out, rfl⟩
    | inl c =>
      obtain ⟨y, y', hne⟩ := hnonconst
      exfalso
      apply hne
      rw [← heval y, ← heval y', h]
      rfl
  have hOutN : C.output ≠ n := by
    intro h
    rw [h, elim_getD n n _ post after (by rw [hAfterLen]; dsimp [m]; omega), hAfterN] at hout
    cases hout
  have hOutM : C.output ≠ m := by
    intro h
    rw [h, elim_getD n m _ post after (by omega), hAfterM] at hout
    cases hout
  have hLower : C.size ≤ final.2.length + 1 := by
    apply htight final.2.length
    refine ⟨⟨final.2, out⟩, ?_, le_rfl, ?_⟩
    · have ho := elim_ok n gs start (by simp [start])
      rwa [hFinal] at ho
    · intro y
      have he := heval y
      rw [hout] at he
      exact he
  have hBeforeLen : before.2.length ≤ pre.length := by
    simpa [before, start] using elim_len n pre start
  have hFinalLen : final.2.length ≤ after.2.length + post.length :=
    elim_len n post after
  -- A second reader of either fixed wire would save a second gate.
  have noPre (k : Gate) (hk : k ∈ pre) : n ∉ k.inputs := by
    intro hr
    have h := elim_len_lt n n pre start hpre hstart ⟨false, hfix⟩ ⟨k, hk, hr⟩
    change before.2.length + 1 ≤ 0 + pre.length at h
    omega
  have noPost (k : Gate) (hk : k ∈ post) (i : ℕ) (hi : i ∈ k.inputs) :
      ¬(i = n ∨ i = m) := by
    intro hbadIndex
    rcases hbadIndex with hN | hM
    · subst i
      have h := elim_len_lt n n post after hpost
        (by rw [hAfterLen]; dsimp [m]; omega) ⟨false, hAfterN⟩ ⟨k, hk, hi⟩
      change final.2.length + 1 ≤ after.2.length + post.length at h
      omega
    · subst i
      have h := elim_len_lt n m post after hpost
        (by omega) ⟨b, hAfterM⟩ ⟨k, hk, hi⟩
      change final.2.length + 1 ≤ after.2.length + post.length at h
      omega
  -- Without a second reader, neither changed wire can affect the output.
  obtain ⟨y, hne⟩ := hdep
  apply hne
  let input (b : Bool) := List.ofFn y ++ [b]
  have hInputLen (b : Bool) : (input b).length = n + 1 := by simp [input]
  let w (b : Bool) := wiresFrom pre (input b)
  have hwLen (b : Bool) : (w b).length = m := by
    simp [w, length_wiresFrom, hInputLen, hPreLen, m]
  have hw : ∀ i, i ≠ n → (w false).getD i false = (w true).getD i false := by
    apply wires_agree pre (fun i => i = n) _ _ (by simp [hInputLen]) _
      (fun k hk i hi he => noPre k hk (he ▸ hi))
    intro i hi
    change (List.ofFn y ++ [false]).getD i false = (List.ofFn y ++ [true]).getD i false
    have hin : i ≠ (List.ofFn y).length := by simpa using hi
    rw [getD_snoc_ne _ _ _ _ hin, getD_snoc_ne _ _ _ _ hin]
  let extended (b : Bool) := w b ++ [g.op.eval (g.inputs.map fun i => (w b).getD i false)]
  have ha : ∀ i, ¬(i = n ∨ i = m) →
      (extended false).getD i false = (extended true).getD i false := by
    intro i hi
    have hin : i ≠ n := fun he => hi (Or.inl he)
    have him : i ≠ m := fun he => hi (Or.inr he)
    dsimp only [extended]
    rw [getD_snoc_ne _ _ _ _ (by simpa [hwLen] using him),
      getD_snoc_ne _ _ _ _ (by simpa [hwLen] using him)]
    exact hw i hin
  have hv := wires_agree post (fun i => i = n ∨ i = m) (extended false) (extended true)
    (by simp [extended, hwLen]) ha noPost C.output (by simp [hOutN, hOutM])
  simp only [circuitFun, Circuit.eval, ofFn_snoc]
  change (wiresFrom C.gates (input false)).getD C.output false =
    (wiresFrom C.gates (input true)).getD C.output false
  have hs : C.gates.map normGate = pre ++ g :: post := hsplit
  simp only [← wiresFrom_norm C.gates, hs, wiresFrom_append]
  exact hv


namespace PEqualNP.Outside.L568

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Shift a wire index past the extra input bits. -/
def shiftIdx (M N i : ℕ) : ℕ := if i < M then i else i + (N - M)

/-- Re-index a circuit built for inputs of length `M` to read inputs of length `N`. -/
def shiftCircuit (M N : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.map (fun g => ⟨g.op, g.inputs.map (shiftIdx M N)⟩), shiftIdx M N C.output⟩

theorem getD_shift (M N : ℕ) (T u : List Bool) (hM : M ≤ N) (hT : T.length = N) (i : ℕ) :
    (T ++ u).getD (shiftIdx M N i) false = (T.take M ++ u).getD i false := by
  have hTM : (T.take M).length = M := by simp [hT, hM]
  unfold shiftIdx
  split_ifs with h
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by omega), List.getElem?_append_left (by omega),
      List.getElem?_take_of_lt h]
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), hT, hTM]
    congr 2
    omega

theorem fold_shift (M N : ℕ) (T : List Bool) (hM : M ≤ N) (hT : T.length = N) :
    ∀ (gs : List Gate) (u : List Bool), ∃ u' : List Bool,
      (gs.map (fun g => (⟨g.op, g.inputs.map (shiftIdx M N)⟩ : Gate))).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (T ++ u)
        = T ++ u' ∧
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (T.take M ++ u) = T.take M ++ u' := by
  intro gs
  induction gs with
  | nil => intro u; exact ⟨u, rfl, rfl⟩
  | cons g gs ih =>
    intro u
    have key : (g.inputs.map (shiftIdx M N)).map (fun i => (T ++ u).getD i false)
        = g.inputs.map (fun i => (T.take M ++ u).getD i false) := by
      rw [List.map_map]
      exact List.map_congr_left (fun i _ => getD_shift M N T u hM hT i)
    obtain ⟨u', h1, h2⟩ := ih (u ++ [g.op.eval (g.inputs.map fun i => (T.take M ++ u).getD i false)])
    refine ⟨u', ?_, ?_⟩
    · simp only [List.map_cons, List.foldl_cons]
      rw [key, List.append_assoc]
      exact h1
    · simp only [List.foldl_cons]
      rw [List.append_assoc]
      exact h2

theorem eval_shift (M N : ℕ) (C : Circuit) (T : List Bool) (hM : M ≤ N) (hT : T.length = N) :
    (shiftCircuit M N C).eval T = C.eval (T.take M) := by
  obtain ⟨u', h1, h2⟩ := fold_shift M N T hM hT C.gates []
  simp only [List.append_nil] at h1 h2
  unfold Circuit.eval Circuit.wires shiftCircuit
  simp only
  rw [h1, h2]
  have := getD_shift M N T u' hM hT C.output
  exact this

def extendOR (n : ℕ) (C : Circuit) : Circuit :=
  let D := shiftCircuit n (n + 1) C
  ⟨D.gates ++ [⟨GateOp.or, [n, D.output]⟩], n + 1 + D.gates.length⟩

theorem extendOR_fanin (n : ℕ) (C : Circuit) (h : FanInTwo C) :
    FanInTwo (extendOR n C) := by
  intro g hg
  simp only [extendOR, shiftCircuit, List.mem_append, List.mem_singleton] at hg
  rcases hg with hm | rfl
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hm
    simpa using h u hu
  · simp

theorem extendOR_size (n : ℕ) (C : Circuit) : (extendOR n C).size = C.size + 1 := by
  simp [extendOR, shiftCircuit, Circuit.size]

theorem wireLength (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun u g => u ++ [g.op.eval (g.inputs.map fun i => u.getD i false)]) w).length =
      w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_nil, List.length_cons]
    omega

theorem wirePrefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl (fun u g => u ++ [g.op.eval (g.inputs.map fun j => u.getD j false)]) w).getD i false =
      w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

theorem extendOR_eval (n : ℕ) (C : Circuit) (x : Fin (n + 1) → Bool) :
    circuitFun (n + 1) (extendOR n C) x =
      (x (Fin.last n) || circuitFun n C (fun i => x i.castSucc)) := by
  let D := shiftCircuit n (n + 1) C
  let input := List.ofFn x
  have hinLen : input.length = n + 1 := by simp [input]
  have hin : input.getD n false = x (Fin.last n) := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    simp only [input, List.getElem_ofFn]
    rfl
  have hprefix : input.take n = List.ofFn (fun i : Fin n => x i.castSucc) := by
    apply List.ext_getElem
    · simp [input]
    · intro i hi hj
      simp only [input, List.getElem_take, List.getElem_ofFn]; rfl
  have hW : (D.wires input).length = n + 1 + D.gates.length := by
    simpa only [Circuit.wires, hinLen] using wireLength D.gates input
  have hGet : (D.wires input).getD n false = x (Fin.last n) := by
    rw [Circuit.wires, wirePrefix _ _ _ (by omega), hin]
  change Circuit.eval ⟨D.gates ++ [⟨GateOp.or, [n, D.output]⟩], n + 1 + D.gates.length⟩ input = _
  unfold Circuit.eval at *
  simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
  change ((D.wires input) ++ [GateOp.or.eval [((D.wires input).getD n false),
    ((D.wires input).getD D.output false)]]).getD (n + 1 + D.gates.length) false = _
  rw [← hW, List.getD_append_right _ _ _ _ (Nat.le_refl _)]
  simp only [Nat.sub_self, List.getD_cons_zero, GateOp.eval, List.any_cons, List.any_nil, id_eq,
    Bool.or_false, hGet]
  congr 1
  have hs := eval_shift n (n+1) C input (Nat.le_succ _) hinLen
  rw [hprefix] at hs
  exact hs

end PEqualNP.Outside.L568


namespace PEqualNP.Outside.L568Cut

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (input : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) input

theorem run_length (gs : List Gate) (input : List Bool) :
    (run gs input).length = input.length + gs.length := by
  induction gs generalizing input with
  | nil => simp [run]
  | cons g gs ih =>
    simp only [run, List.foldl_cons] at *
    rw [ih]
    simp
    omega

theorem run_append (a b : List Gate) (input : List Bool) :
    run (a ++ b) input = run b (run a input) := by
  simp [run, List.foldl_append]

theorem list_from_fin (xs : List Bool) :
    List.ofFn (fun i : Fin xs.length => xs[i]) = xs := by
  apply List.ext_getElem
  · simp
  · simp

def splice (pre : List Gate) (D : Circuit) : Circuit :=
  ⟨pre ++ D.gates, D.output⟩

theorem eval_splice (pre : List Gate) (D : Circuit) (input : List Bool) :
    (splice pre D).eval input = D.eval (run pre input) := by
  change (run (pre ++ D.gates) input).getD D.output false = _
  rw [run_append]
  rfl

theorem splice_ok (pre : List Gate) (D : Circuit)
    (hp : FanInTwo ⟨pre, 0⟩) (hd : FanInTwo D) :
    FanInTwo (splice pre D) := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact hp g hg
  · exact hd g hg

def tail (C : Circuit) (j : ℕ) : Circuit :=
  ⟨C.gates.drop j, C.output⟩

theorem splice_tail (C : Circuit) (j : ℕ) : splice (C.gates.take j) (tail C j) = C := by
  cases C
  simp [splice, tail]

theorem eval_on_lists {D E : Circuit} {m : ℕ} (h : circuitFun m D = circuitFun m E)
    (xs : List Bool) (hx : xs.length = m) : D.eval xs = E.eval xs := by
  subst m
  have he := congrFun h (fun i : Fin xs.length => xs[i])
  simpa only [circuitFun, list_from_fin] using he

theorem minimal_tail (n : ℕ) (C : Circuit) (hmin : IsMinimalCircuit n C)
    (j : ℕ) (hj : j ≤ C.gates.length) : IsMinimalCircuit (n + j) (tail C j) := by
  constructor
  · intro g hg
    exact hmin.1 g (List.mem_of_mem_drop hg)
  · intro D hd he
    let pre := C.gates.take j
    have hp : FanInTwo ⟨pre, 0⟩ := fun g hg => hmin.1 g (List.mem_of_mem_take hg)
    have eq : circuitFun n (splice pre D) = circuitFun n C := by
      funext x
      change (splice pre D).eval (List.ofFn x) = C.eval (List.ofFn x)
      rw [← splice_tail C j, eval_splice, eval_splice]
      have hlen : (run pre (List.ofFn x)).length = n + j := by
        simp [run_length, pre, Nat.min_eq_left hj]
      exact eval_on_lists he _ hlen
    have hsize := hmin.2 (splice pre D) (splice_ok pre D hp hd) eq
    simp only [Circuit.size, splice, List.length_append, pre, List.length_take,
      Nat.min_eq_left hj] at hsize
    change (C.gates.drop j).length ≤ D.gates.length
    rw [List.length_drop]
    omega

end PEqualNP.Outside.L568Cut


namespace PEqualNP.Outside.Meta169

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def initId (n : ℕ) : List Stat :=
  List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat))

private theorem inv_init_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (initId n, []) := by
  refine ⟨by simp [initId], ?_⟩
  intro i
  by_cases hi : i < n
  · simp [initId, hi, Stat.Valid, Stat.val, wiresFrom]
  · have hstat : (initId n).getD i (Sum.inl false) = Sum.inl false := by
      apply List.getD_eq_default
      simpa [initId] using Nat.le_of_not_gt hi
    have hinput : (List.ofFn y).getD i false = false := by
      apply List.getD_eq_default
      simpa using Nat.le_of_not_gt hi
    rw [hstat,hinput]
    exact ⟨trivial, rfl⟩

theorem first_read_available (n : ℕ) (g : Gate) (rest : List Gate) (out : ℕ)
    (hmin : IsMinimalCircuit n ⟨g :: rest, out⟩)
    (hnc : ∃ a b : Fin n → Bool,
      circuitFun n ⟨g :: rest, out⟩ a ≠ circuitFun n ⟨g :: rest, out⟩ b)
    (i : ℕ) (hi : i ∈ (normGate g).inputs) : i < n := by
  by_contra hn
  let gn := normGate g
  let gs := rest.map normGate
  let init : List Stat × List Gate := (initId n, [])
  let after := elimStep n init gn
  let final := elim n gs after
  have hnorm : ∀ a ∈ gn :: gs, NOk a := by
    change ∀ a ∈ (g :: rest).map normGate, NOk a
    intro a ha
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ha
    exact normGate_nok u (hmin.1 u hu)
  have hfirst : NOk gn := hnorm gn List.mem_cons_self
  let ins := gn.inputs.map (fun k => (initId n).getD k (Sum.inl false))
  have hstat : (initId n).getD i (Sum.inl false) = Sum.inl false := by
    apply List.getD_eq_default
    simpa [initId] using Nat.le_of_not_gt hn
  have hm : Sum.inl false ∈ ins := by
    exact List.mem_map.mpr ⟨i, hi, hstat⟩
  have hnone : (simplify gn.op n ins).1 = none :=
    simplify_count _ _ _ hfirst.1.1 (by simpa [ins] using hfirst.1.2)
      (by simpa [ins] using hfirst.2) ⟨false,hm⟩
  have hzero : after.2 = [] := by
    change [] ++ (simplify gn.op n ins).1.toList = []
    rw [hnone]
    rfl
  have hc : ∀ y : Fin n → Bool, (final.1.getD out (Sum.inl false)).val
      (wiresFrom final.2 (List.ofFn y)) = circuitFun n ⟨g :: rest, out⟩ y := by
    intro y
    have hv := (inv_elim n (List.ofFn y) (by simp) (gn :: gs) _ init
      (fun a ha => (hnorm a ha).1) ((inv_init_id n y))).2 out
    have he := hv.2
    change (final.1.getD out (Sum.inl false)).val (wiresFrom final.2 (List.ofFn y)) =
      (wiresFrom ((g :: rest).map normGate) (List.ofFn y)).getD out false at he
    rw [wiresFrom_norm] at he
    exact he
  obtain ⟨j,hj⟩ : ∃ j, final.1.getD out (Sum.inl false) = Sum.inr j := by
    cases he : final.1.getD out (Sum.inl false) with
    | inr j => exact ⟨j,rfl⟩
    | inl c =>
      exfalso
      obtain ⟨a,b,hab⟩ := hnc
      apply hab
      rw [← hc a, ← hc b, he]
      rfl
  have eq : circuitFun n ⟨final.2, j⟩ = circuitFun n ⟨g :: rest, out⟩ := by
    funext y
    have hcy := hc y
    rw [hj] at hcy
    exact hcy
  have hOK : FanInTwo ⟨final.2,j⟩ := by
    apply elim_ok n gs after
    simp [hzero]
  have hmin' := hmin.2 ⟨final.2,j⟩ hOK eq
  have hlen := elim_len n gs after
  rw [hzero] at hlen
  simp [Circuit.size] at hmin'
  change final.2.length ≤ [].length + gs.length at hlen
  simp [gs] at hlen
  omega

end PEqualNP.Outside.Meta169

namespace PEqualNP.Outside.L568Cut

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem eval_take_drop (C : Circuit) (j : ℕ) (input : List Bool) :
    C.eval input = (tail C j).eval (run (C.gates.take j) input) := by
  rw [← eval_splice, splice_tail]

theorem eval_splice_size_bound (n : ℕ) (C : Circuit) (hmin : IsMinimalCircuit n C)
    (j : ℕ) (hj : j ≤ C.gates.length) (D : Circuit) (hD : FanInTwo D)
    (h : ∀ x : Fin n → Bool, D.eval (run (C.gates.take j) (List.ofFn x)) = C.eval (List.ofFn x)) :
    (tail C j).size ≤ D.size := by
  let pre := C.gates.take j
  have hp : FanInTwo ⟨pre, 0⟩ := fun g hg => hmin.1 g (List.mem_of_mem_take hg)
  have eq : circuitFun n (splice pre D) = circuitFun n C := by
    funext x
    exact (eval_splice pre D _).trans (h x)
  have hm := hmin.2 (splice pre D) (splice_ok pre D hp hD) eq
  change C.gates.length ≤ (C.gates.take j ++ D.gates).length at hm
  rw [List.length_append, List.length_take, Nat.min_eq_left hj] at hm
  change (C.gates.drop j).length ≤ D.gates.length
  simp only [List.length_drop]
  omega

theorem tail_size_le_one_more (n m : ℕ) (C : Circuit) (hmin : IsMinimalCircuit n C)
    (j : ℕ) (hj : j ≤ C.gates.length)
    (h : ∀ x : Fin n → Bool, ∃ a : Fin (m+1) → Bool,
      List.ofFn a = run (C.gates.take j) (List.ofFn x) ∧
      circuitFun (m+1) (tail C j) a =
        (a (Fin.last m) || circuitFun (m+1) (tail C j)
          (Fin.snoc (fun i => a i.castSucc) false))) :
    ∀ s, HasCircuitSize m (fun y => circuitFun (m+1) (tail C j) (Fin.snoc y false)) s →
      (tail C j).size ≤ s + 1 := by
  intro s ⟨D,hD,hdSize,hdEval⟩
  have hN := eval_splice_size_bound n C hmin j hj (L568.extendOR m D) (L568.extendOR_fanin m D hD)
    (by
      intro x
      obtain ⟨a,ha,had⟩ := h x
      rw [← ha, eval_take_drop C j (List.ofFn x), ← ha]
      change circuitFun (m+1) (L568.extendOR m D) a = circuitFun (m+1) (tail C j) a
      rw [L568.extendOR_eval, had]
      congr 1
      exact hdEval _)
  rw [L568.extendOR_size] at hN
  omega

end PEqualNP.Outside.L568Cut


namespace PEqualNP.Outside.L568Cut

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def Reads (g : Gate) (i : ℕ) : Prop :=
  (g.op = GateOp.not ∧ g.inputs.head? = some i) ∨
    (g.op ≠ GateOp.not ∧ i ∈ g.inputs)

theorem tail_reader_or_output (n m : ℕ) (C : Circuit) (hmin : IsMinimalCircuit n C)
    (j : ℕ) (hj : j ≤ C.gates.length) (hindex : n + j = m+1)
    (hdep : ∃ y : Fin m → Bool,
      circuitFun (m+1) (tail C j) (Fin.snoc y false) = false ∧
      circuitFun (m+1) (tail C j) (Fin.snoc y true) = true)
    (h : ∀ x : Fin n → Bool, ∃ a : Fin (m+1) → Bool,
      List.ofFn a = run (C.gates.take j) (List.ofFn x) ∧
      circuitFun (m+1) (tail C j) a =
        (a (Fin.last m) || circuitFun (m+1) (tail C j)
          (Fin.snoc (fun i => a i.castSucc) false))) :
    (j = C.gates.length ∧ C.output = m) ∨
    (C.output ≠ m ∧ ∃ k : Fin (tail C j).gates.length,
      ((tail C j).gates.get k).op = GateOp.or ∧
      ((tail C j).gates.get k).inputs.length = 2 ∧
      m ∈ ((tail C j).gates.get k).inputs ∧
      (∃ w ∈ ((tail C j).gates.get k).inputs, w ≠ m ∧ w < m + 1 + k.val) ∧
      ∀ k', Reads ((tail C j).gates.get k') m → k' = k) := by
  let S := tail C j
  let B := fun y : Fin m → Bool => circuitFun (m+1) S (Fin.snoc y false)
  by_cases hnc : ∃ a b, B a ≠ B b
  · right
    have hOut : C.output ≠ m := by
      intro he
      have hf (a : Fin m → Bool) : B a = false := by
        change (S.wires (List.ofFn (Fin.snoc a false))).getD S.output false = false
        have hpos : m < (List.ofFn (Fin.snoc a false)).length := by simp
        have hout : S.output = m := he
        rw [Circuit.wires, hout]
        change (S.gates.foldl (fun u g => u ++ [g.op.eval (g.inputs.map fun k => u.getD k false)])
          (List.ofFn (Fin.snoc a false))).getD m false = false
        rw [L568.wirePrefix _ _ _ hpos, List.getD_eq_getElem _ _ hpos]
        simp only [List.getElem_ofFn]
        exact @Fin.snoc_last m (fun _ => Bool) false a
      obtain ⟨a,b,hab⟩ := hnc
      exact hab ((hf a).trans (hf b).symm)
    refine ⟨hOut, ?_⟩
    have hS := minimal_tail n C hmin j hj
    rw [hindex] at hS
    have hd : ∃ y : Fin m → Bool,
        circuitFun (m+1) S (Fin.snoc y false) ≠
        circuitFun (m+1) S (Fin.snoc y true) := by
      obtain ⟨y,hf,ht⟩ := hdep
      exact ⟨y, by rw [hf,ht]; decide⟩
    have hs := tail_size_le_one_more n m C hmin j hj h
    obtain ⟨k,hk,hu⟩ := l568_first_unique m S hS hd hnc hs
    obtain ⟨hop,harity,hread,hw⟩ := l568_first_or m S hS hd hnc hs k hk
    exact ⟨k,hop,harity,hread,hw,hu⟩
  · left
    obtain ⟨y,hf,ht⟩ := hdep
    have hb (a : Fin m → Bool) : B a = false := by
      by_contra hn
      exact hnc ⟨a,y,fun eq => hn (eq.trans hf)⟩
    have hzero := eval_splice_size_bound n C hmin j hj ⟨[],m⟩
      (by intro g hg; simp at hg) (by
        intro x
        obtain ⟨a,ha,he⟩ := h x
        rw [eval_take_drop C j (List.ofFn x), ← ha]
        change (List.ofFn a).getD m false = circuitFun (m+1) S a
        rw [he]
        change (List.ofFn a).getD m false = (a (Fin.last m) || B _)
        rw [hb, Bool.or_false, List.getD_eq_getElem _ _ (by simp)]
        simp only [List.getElem_ofFn]
        rfl)
    have hj' : j = C.gates.length := by
      change (C.gates.drop j).length ≤ 0 at hzero
      simp only [List.length_drop] at hzero
      omega
    have hnil : S.gates = [] := by simp [S,tail,hj']
    have houtput : S.output = m := by
      by_contra hm
      have hsame : circuitFun (m+1) S (Fin.snoc y false) =
          circuitFun (m+1) S (Fin.snoc y true) := by
        simp only [circuitFun, Circuit.eval, Circuit.wires, hnil, List.foldl_nil]
        rw [List.ofFn_succ', List.ofFn_succ']
        simp only [Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append]
        change (List.ofFn y ++ [false]).getD S.output false = (List.ofFn y ++ [true]).getD S.output false
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
        by_cases hlt : S.output < m
        · rw [List.getElem?_append_left (by simpa using hlt),
              List.getElem?_append_left (by simpa using hlt)]
        · have hgt : m + 1 ≤ S.output := by omega
          rw [List.getElem?_eq_none (by simpa using hgt), List.getElem?_eq_none (by simpa using hgt)]
      rw [hf,ht] at hsame
      cases hsame
    exact ⟨hj',houtput⟩

end PEqualNP.Outside.L568Cut


namespace PEqualNP.Outside.Meta169

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity L568Cut

theorem norm_read_iff (g : Gate) (i : ℕ) : i ∈ (normGate g).inputs ↔ Reads g i := by
  constructor
  · intro h
    by_cases hnot : g.op = GateOp.not
    · left
      refine ⟨hnot,?_⟩
      cases hins : g.inputs with
      | nil => simp [normGate,hnot,hins] at h
      | cons a l =>
        have eq : i = a := by simpa [normGate,hnot,hins] using h
        simp [eq]
    · right
      exact ⟨hnot, by simpa [normGate_of_ne_not g hnot] using h⟩
  · exact normGate_read g i

theorem eval_agree (D : Circuit) (bad : ℕ → Prop) (xs ys : List Bool)
    (hl : xs.length = ys.length)
    (ha : ∀ i, ¬bad i → xs.getD i false = ys.getD i false)
    (hr : ∀ g ∈ D.gates, ∀ i, Reads g i → ¬bad i)
    (ho : ¬bad D.output) : D.eval xs = D.eval ys := by
  have hn : ∀ g ∈ D.gates.map normGate, ∀ i ∈ g.inputs, ¬bad i := by
    intro g hg i hi
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hg
    exact hr u hu i ((norm_read_iff u i).mp hi)
  have h := wires_agree (D.gates.map normGate) bad xs ys hl ha hn D.output ho
  rwa [wiresFrom_norm, wiresFrom_norm] at h

theorem paired_true (m : ℕ) (D : Circuit) (bad : ℕ → Prop)
    (hr : ∀ g ∈ D.gates, ∀ i, Reads g i → ¬bad i)
    (ho : ¬bad D.output)
    (x y : Fin m → Bool)
    (he : ∀ i : Fin m, ¬bad i.val → x i = y i)
    (hy : circuitFun (m+1) D (Fin.snoc y true) = true) :
    circuitFun (m+1) D (Fin.snoc x true) = true := by
  refine Eq.trans ?_ hy
  change D.eval (List.ofFn (Fin.snoc x true)) = D.eval (List.ofFn (Fin.snoc y true))
  rw [ofFn_snoc, ofFn_snoc]
  apply eval_agree D bad _ _ (by simp) _ hr ho
  intro i hi
  by_cases hit : i < m
  · have hx : i < (List.ofFn x).length := by simpa using hit
    have hy : i < (List.ofFn y).length := by simpa using hit
    rw [List.getD_append _ _ _ _ hx, List.getD_append _ _ _ _ hy]
    simp [hit, he ⟨i,hit⟩ hi]
  · rw [List.getD_append_right _ _ _ _ (by simp; omega),
        List.getD_append_right _ _ _ _ (by simp; omega)]
    simp

end PEqualNP.Outside.Meta169


namespace PEqualNP.Outside.L568Cut

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def view (m : ℕ) (w : List Bool) : Fin m → Bool :=
  fun i => w.getD i.val false

theorem ofFn_view (m : ℕ) (w : List Bool) (h : w.length = m) :
    List.ofFn (view m w) = w := by
  subst m
  apply List.ext_getElem
  · simp
  · intro i ha hb
    rw [List.getElem_ofFn]
    simp only [view]
    exact List.getD_eq_getElem _ _ hb

theorem tail_nonconstant (n : ℕ) (C : Circuit) (j : ℕ) (hj : j ≤ C.gates.length)
    (hnc : ∃ a b : Fin n → Bool, circuitFun n C a ≠ circuitFun n C b) :
    ∃ a b : Fin (n+j) → Bool, circuitFun (n+j) (tail C j) a ≠ circuitFun (n+j) (tail C j) b := by
  obtain ⟨a,b,hab⟩ := hnc
  let ws := fun x : Fin n → Bool => run (C.gates.take j) (List.ofFn x)
  have len (x : Fin n → Bool) : (ws x).length = n+j := by
    simp [ws, run_length, Nat.min_eq_left hj]
  refine ⟨view (n+j) (ws a), view (n+j) (ws b), ?_⟩
  intro eq
  apply hab
  change (tail C j).eval (List.ofFn (view (n+j) (ws a))) =
    (tail C j).eval (List.ofFn (view (n+j) (ws b))) at eq
  rw [ofFn_view _ _ (len a), ofFn_view _ _ (len b)] at eq
  exact (eval_take_drop C j _).trans (eq.trans (eval_take_drop C j _).symm)

theorem read_available (n : ℕ) (C : Circuit) (hmin : IsMinimalCircuit n C)
    (hnc : ∃ a b : Fin n → Bool, circuitFun n C a ≠ circuitFun n C b)
    (j : Fin C.gates.length) (i : ℕ) (hi : Reads (C.gates.get j) i) :
    i < n + j.val := by
  have hminTail := minimal_tail n C hmin j.val j.isLt.le
  have hncTail := tail_nonconstant n C j.val j.isLt.le hnc
  have hdrop : C.gates.drop j.val = C.gates.get j :: C.gates.drop (j.val+1) := by
    exact List.drop_eq_getElem_cons j.isLt
  have htail : tail C j.val = ⟨C.gates.get j :: C.gates.drop (j.val+1), C.output⟩ := by
    exact congrArg (fun gs => (⟨gs, C.output⟩ : Circuit)) hdrop
  rw [htail] at hminTail hncTail
  exact Meta169.first_read_available _ _ _ _ hminTail hncTail i
    ((Meta169.norm_read_iff _ _).mpr hi)

end PEqualNP.Outside.L568Cut


namespace PEqualNP.Outside.Meta169

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity L568Cut

theorem run_agree (gs : List Gate) (bad : ℕ → Prop) (xs ys : List Bool)
    (hl : xs.length = ys.length)
    (ha : ∀ i, ¬bad i → xs.getD i false = ys.getD i false)
    (hr : ∀ g ∈ gs, ∀ i, Reads g i → ¬bad i) :
    ∀ i, ¬bad i → (run gs xs).getD i false = (run gs ys).getD i false := by
  have hn : ∀ g ∈ gs.map normGate, ∀ i ∈ g.inputs, ¬bad i := by
    intro g hg i hi
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hg
    exact hr u hu i ((norm_read_iff u i).mp hi)
  intro i hi
  have h := wires_agree (gs.map normGate) bad xs ys hl ha hn i hi
  rwa [wiresFrom_norm, wiresFrom_norm] at h

theorem advance_values (m : ℕ) (mid : List Gate) (g : Gate)
    (bad : ℕ → Prop) (xs ys : List Bool)
    (hlx : xs.length = m+1) (hly : ys.length = m+1)
    (ha : ∀ i, ¬(bad i ∨ i = m) → xs.getD i false = ys.getD i false)
    (hr : ∀ g' ∈ mid, ∀ i, Reads g' i → ¬(bad i ∨ i = m))
    (ht : ys.getD m false = true) (hop : g.op = GateOp.or)
    (hread : m ∈ g.inputs) :
    (run (mid ++ [g]) ys).getD (m+1+mid.length) false = true ∧
    ∀ i, ¬(bad i ∨ i=m ∨ i=m+1+mid.length) →
      (run (mid ++ [g]) xs).getD i false = (run (mid ++ [g]) ys).getD i false := by
  let vx := run mid xs
  let vy := run mid ys
  have hlen : vx.length = m+1+mid.length := by simp [vx, run_length, hlx]
  have hlen' : vy.length = m+1+mid.length := by simp [vy, run_length, hly]
  have hc : vy.getD m false = true := by
    change (run mid ys).getD m false = true
    change (mid.foldl (fun w u => w ++ [u.op.eval (u.inputs.map fun i => w.getD i false)]) ys).getD m false = true
    rw [L568.wirePrefix _ _ _ (by omega), ht]
  have hg : g.op.eval (g.inputs.map fun i => vy.getD i false) = true := by
    rw [hop]
    change (g.inputs.map fun i => vy.getD i false).any id = true
    apply List.any_eq_true.mpr
    exact ⟨true, List.mem_map.mpr ⟨m, hread, hc⟩, rfl⟩
  rw [run_append, run_append]
  constructor
  · change (vy ++ [g.op.eval (g.inputs.map fun i => vy.getD i false)]).getD
      (m+1+mid.length) false = true
    rw [getD_snoc_len _ _ _ _ hlen', hg]
  · intro i hi
    change (vx ++ [g.op.eval (g.inputs.map fun j => vx.getD j false)]).getD i false =
      (vy ++ [g.op.eval (g.inputs.map fun j => vy.getD j false)]).getD i false
    have hne : i ≠ m+1+mid.length := fun he => hi (Or.inr (Or.inr he))
    rw [getD_snoc_ne _ _ _ _ (by rwa [hlen]), getD_snoc_ne _ _ _ _ (by rwa [hlen'])]
    exact run_agree mid (fun k => bad k ∨ k=m) xs ys (hlx.trans hly.symm) ha hr i
      (fun h => hi (h.elim Or.inl (fun h => Or.inr (Or.inl h))))

end PEqualNP.Outside.Meta169


namespace PEqualNP.Outside.L568Cut

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Meta169

theorem pairs_imply_cut (n m : ℕ) (C : Circuit) (j : ℕ) (hj : j ≤ C.gates.length)
    (hindex : (n+1)+j = m+1) (bad : ℕ → Prop)
    (hno : ∀ g ∈ (tail C j).gates, ∀ i, Reads g i → ¬bad i)
    (hOut : ¬bad C.output)
    (htrue : ∀ y : Fin n → Bool,
      (run (C.gates.take j) (List.ofFn (Fin.snoc y true))).getD m false = true)
    (hagree : ∀ (y : Fin n → Bool) (i : ℕ), ¬(bad i ∨ i=m) →
      (run (C.gates.take j) (List.ofFn (Fin.snoc y false))).getD i false =
      (run (C.gates.take j) (List.ofFn (Fin.snoc y true))).getD i false)
    (H : (Fin n → Bool) → Bool) (hf : ∃ y, H y = false)
    (h : ∀ x : Fin (n+1) → Bool,
      circuitFun (n+1) C x = (x (Fin.last n) || H (fun i => x i.castSucc))) :
    (∃ y : Fin m → Bool,
      circuitFun (m+1) (tail C j) (Fin.snoc y false) = false ∧
      circuitFun (m+1) (tail C j) (Fin.snoc y true) = true) ∧
    (∀ x : Fin (n+1) → Bool, ∃ a : Fin (m+1) → Bool,
      List.ofFn a = run (C.gates.take j) (List.ofFn x) ∧
      circuitFun (m+1) (tail C j) a =
        (a (Fin.last m) || circuitFun (m+1) (tail C j)
          (Fin.snoc (fun i => a i.castSucc) false))) := by
  let S := tail C j
  let pre := fun x : Fin (n+1) → Bool => run (C.gates.take j) (List.ofFn x)
  let a := fun (y : Fin n → Bool) (b : Bool) => view (m+1) (pre (Fin.snoc y b))
  let aInit := fun y b (i : Fin m) => a y b i.castSucc
  have hlen (x) : (pre x).length = m+1 := by
    simpa [pre,run_length,Nat.min_eq_left hj] using hindex
  have haList (y) (b) : List.ofFn (a y b) = pre (Fin.snoc y b) :=
    ofFn_view _ _ (hlen _)
  have hVal (y) (b) : circuitFun (m+1) S (a y b) = (b || H y) := by
    change S.eval (List.ofFn (a y b)) = _
    rw [haList, ← eval_take_drop C j]
    change circuitFun (n+1) C (Fin.snoc y b) = _
    rw [h]
    simp
  have hTrue (y) : circuitFun (m+1) S (Fin.snoc (aInit y true) true) = true := by
    have eq : Fin.snoc (aInit y true) true = a y true := by
      funext i
      refine Fin.lastCases ?_ (fun k => ?_) i
      · simpa [a,view,pre] using (htrue y).symm
      · simp [aInit]
    rw [eq,hVal]
    rfl
  have hInitTrue (y) : circuitFun (m+1) S (Fin.snoc (aInit y false) true) = true :=
    paired_true m S bad hno hOut (aInit y false) (aInit y true)
      (fun i hi => hagree y i.val (by simp [hi, Nat.ne_of_lt i.isLt])) (hTrue y)
  have hEq (y) (b) :
      circuitFun (m+1) S (Fin.snoc (aInit y b) (a y b (Fin.last m))) = circuitFun (m+1) S (a y b) := by
    congr 1
    funext i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simp
    · simp [aInit]
  have hOn (y) (b) :
      circuitFun (m+1) S (a y b) = (a y b (Fin.last m) ||
        circuitFun (m+1) S (Fin.snoc (aInit y b) false)) := by
    cases b
    · cases hb : a y false (Fin.last m)
      · simpa [hb] using (hEq y false).symm
      · have hv := hEq y false
        rw [hb, hInitTrue] at hv
        simpa [hb] using hv.symm
    · have hv : a y true (Fin.last m) = true := htrue y
      simp [hv,hVal]
  constructor
  · obtain ⟨y,hy⟩ := hf
    use aInit y false
    refine ⟨?_, hInitTrue y⟩
    have hh := hOn y false
    rw [hVal, hy] at hh
    exact (Bool.or_eq_false_iff.mp hh.symm).2
  · intro x
    let y := fun i : Fin n => x i.castSucc
    let b := x (Fin.last n)
    have eq : Fin.snoc y b = x := by
      funext i
      refine Fin.lastCases ?_ (fun k => ?_) i
      · simp [b]
      · simp [y]
    exact ⟨a y b, eq ▸ haList y b, hOn y b⟩

end PEqualNP.Outside.L568Cut


namespace PEqualNP.Outside.L568Cut

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Meta169

def Link (n : ℕ) (C : Circuit) (v : ℕ) (a : Fin C.gates.length) : Prop :=
  (C.gates.get a).op = GateOp.or ∧
  (C.gates.get a).inputs.length = 2 ∧
  v ∈ (C.gates.get a).inputs ∧
  (∃ w ∈ (C.gates.get a).inputs, w ≠ v ∧ w < n+1+a.val) ∧
  (∀ b : Fin C.gates.length, Reads (C.gates.get b) v → b = a)

namespace Link

theorem op {n C v a} (h : Link n C v a) : (C.gates.get a).op = GateOp.or := h.1
theorem arity {n C v a} (h : Link n C v a) : (C.gates.get a).inputs.length = 2 := h.2.1
theorem input {n C v a} (h : Link n C v a) : v ∈ (C.gates.get a).inputs := h.2.2.1
theorem side {n C v a} (h : Link n C v a) :
    ∃ w ∈ (C.gates.get a).inputs, w ≠ v ∧ w < n+1+a.val := h.2.2.2.1
theorem only {n C v a} (h : Link n C v a) :
    ∀ b : Fin C.gates.length, Reads (C.gates.get b) v → b = a := h.2.2.2.2

end Link

def Route (n : ℕ) (C : Circuit) : ℕ → List (Fin C.gates.length) → Prop
  | j, [] => j = C.gates.length ∧ C.output = n+C.gates.length
  | j, a::r => j ≤ a.val ∧ Link n C (n+j) a ∧ Route n C (a.val+1) r

theorem Route.done {n C} (h : C.output = n+C.gates.length) :
    Route n C C.gates.length [] := ⟨rfl,h⟩

theorem Route.next {n C j r} (a : Fin C.gates.length) (hj : j ≤ a.val)
    (h : Link n C (n+j) a) (hr : Route n C (a.val+1) r) : Route n C j (a::r) :=
  ⟨hj,h,hr⟩

theorem take_split {α : Type} (xs : List α) (j k : ℕ) (hj : j ≤ xs.length) :
    xs.take (j+k) = xs.take j ++ (xs.drop j).take k := by
  induction j generalizing xs with
  | zero => simp
  | succ j ih =>
    cases xs with
    | nil => simp at hj
    | cons a xs =>
      have hj' : j ≤ xs.length := by simpa using hj
      change (a :: xs).take (j+1+k) = (a :: xs).take (j+1) ++ ((a :: xs).drop (j+1)).take k
      rw [show j+1+k = (j+k)+1 by omega]
      simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append]
      rw [ih _ hj']

theorem build_route (n : ℕ) (C : Circuit) (H : (Fin n → Bool) → Bool)
    (hmin : IsMinimalCircuit (n+1) C) (hnc : ∃ a b : Fin (n+1) → Bool,
      circuitFun (n+1) C a ≠ circuitFun (n+1) C b)
    (hf : ∃ y, H y = false)
    (h : ∀ x : Fin (n+1) → Bool,
      circuitFun (n+1) C x = (x (Fin.last n) || H (fun i => x i.castSucc))) :
    ∀ (remaining j : ℕ), j ≤ C.gates.length → C.gates.length - j = remaining →
    ∀ bad : ℕ → Prop,
    (∀ g ∈ (tail C j).gates, ∀ i, Reads g i → ¬bad i) → ¬bad C.output →
    (∀ y : Fin n → Bool,
      (run (C.gates.take j) (List.ofFn (Fin.snoc y true))).getD (n+j) false = true) →
    (∀ (y : Fin n → Bool) (i : ℕ), ¬(bad i ∨ i=n+j) →
      (run (C.gates.take j) (List.ofFn (Fin.snoc y false))).getD i false =
      (run (C.gates.take j) (List.ofFn (Fin.snoc y true))).getD i false) →
    ∃ r, Route n C j r := by
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | ind remaining ih =>
    intro j hj hremaining bad hb hOut hTrue hAgree
    let m := n+j
    have hindex : (n+1)+j = m+1 := by dsimp [m]; omega
    obtain ⟨hdep,hor⟩ := pairs_imply_cut n m C j hj hindex bad hb hOut hTrue hAgree H hf h
    rcases tail_reader_or_output (n+1) m C hmin j hj hindex hdep hor with he | ⟨hOut', k, hop, hAr, hIn, hSide, hOnly⟩
    · obtain ⟨rfl, hout⟩ := he
      exact ⟨[], Route.done hout⟩
    have hk : k.val < C.gates.length - j := by
      simpa [tail] using k.isLt
    let a : Fin C.gates.length := ⟨j+k.val, by omega⟩
    have ha : (tail C j).gates.get k = C.gates.get a := by
      exact List.getElem_drop
    rw [ha] at hop hAr hIn hSide
    have unq : ∀ b : Fin C.gates.length, Reads (C.gates.get b) m → b = a := by
      intro b hr
      have hbound := read_available (n+1) C hmin hnc b m hr
      have hb' : j ≤ b.val := by dsimp [m] at hbound; omega
      let q : Fin (tail C j).gates.length := ⟨b.val-j, by simp [tail]; omega⟩
      have he : (tail C j).gates.get q = C.gates.get b := by
        have hq : b.val-j < (C.gates.drop j).length := q.isLt
        have eq := List.getElem_drop (xs:=C.gates) (i:=j) (j:=b.val-j) (h:=hq)
        calc
          (tail C j).gates.get q = (C.gates.drop j)[b.val-j]'hq :=
            @List.get_eq_getElem Gate (C.gates.drop j) ⟨b.val-j,hq⟩
          _ = C.gates.get b := by
            simpa only [List.get_eq_getElem, Nat.add_sub_of_le hb'] using eq
      have eq := congrArg Fin.val (hOnly q (he.symm ▸ hr))
      apply Fin.ext
      change b.val-j = k.val at eq
      dsimp [a]
      omega
    have hLink : Link n C (n+j) a := by
      refine ⟨hop,hAr,hIn,?_,unq⟩
      obtain ⟨w,hw,hwne,hwlt⟩ := hSide
      refine ⟨w,hw,hwne,?_⟩
      dsimp [m,a] at *
      omega
    let next := a.val+1
    have hnext : next ≤ C.gates.length := a.isLt
    have hdecrease : C.gates.length - next < remaining := by
      dsimp [next,a]
      omega
    let mid := ((tail C j).gates).take k.val
    have hmidLen : mid.length = k.val := by
      simp [mid]
    have hsplit : C.gates.take next = C.gates.take j ++ (mid ++ [C.gates.get a]) := by
      change C.gates.take (j+k.val+1) = _
      rw [List.take_add_one, take_split C.gates j k.val hj, List.append_assoc]
      rw [List.getElem?_eq_getElem a.isLt]
      rfl
    let bad' := fun i => bad i ∨ i=m
    have hMid : ∀ g ∈ mid, ∀ i, Reads g i → ¬bad' i := by
      intro g hg i hr hc
      have hm := List.mem_of_mem_take hg
      rcases hc with hbad | hi
      · exact hb g hm i hr hbad
      · subst i
        obtain ⟨l,hl,hg'⟩ := List.mem_take_iff_getElem.mp hg
        let b : Fin C.gates.length := ⟨j+l,by omega⟩
        have hgb : C.gates.get b = g := by
          simpa [b,tail,List.getElem_drop] using hg'
        have he := congrArg Fin.val (unq b (hgb.symm ▸ hr))
        dsimp [a,b] at he
        omega
    have hNo : ∀ g ∈ (tail C next).gates, ∀ i, Reads g i → ¬bad' i := by
      intro g hg i hr hc
      obtain ⟨l,hl,hg'⟩ := List.mem_iff_getElem.mp hg
      have hl' : l < C.gates.length-next := by simpa [tail] using hl
      let b : Fin C.gates.length := ⟨next+l,by omega⟩
      have hgb : C.gates.get b = g := by
        simpa [b,tail,List.getElem_drop] using hg'
      rcases hc with hbad | hi
      · apply hb g ?_ i hr hbad
        have hsub : j ≤ b.val := by dsimp [b,next,a]; omega
        have hbLen : b.val-j < (tail C j).gates.length := by
          simp [tail]; have := b.isLt; omega
        apply List.mem_iff_getElem.mpr
        refine ⟨b.val-j,hbLen,?_⟩
        have hjl : b.val-j < (C.gates.drop j).length := hbLen
        have eq := List.getElem_drop (xs:=C.gates) (i:=j) (j:=b.val-j) (h:=hjl)
        have eq' : (C.gates.drop j)[b.val-j]'hjl = C.gates.get b := by
          simpa only [List.get_eq_getElem, Nat.add_sub_of_le hsub] using eq
        exact eq'.trans hgb
      · subst i
        have he := congrArg Fin.val (unq b (hgb.symm ▸ hr))
        dsimp [b,next] at he
        omega
    have hBadOut : ¬bad' C.output := by exact fun he => he.elim hOut hOut'
    have hVals (y : Fin n → Bool) := advance_values m mid (C.gates.get a) bad
      (run (C.gates.take j) (List.ofFn (Fin.snoc y false)))
      (run (C.gates.take j) (List.ofFn (Fin.snoc y true)))
      (by simp [run_length,Nat.min_eq_left hj,hindex])
      (by simp [run_length,Nat.min_eq_left hj,hindex])
      (hAgree y) hMid (hTrue y) hop hIn
    have hNextIndex : n+next = m+1+mid.length := by
      rw [hmidLen]
      dsimp [next,m,a]
      omega
    have hNextTrue (y : Fin n → Bool) :
        (run (C.gates.take next) (List.ofFn (Fin.snoc y true))).getD (n+next) false = true := by
      rw [hsplit,run_append,hNextIndex]
      exact (hVals y).1
    have hNextAgree (y : Fin n → Bool) (i : ℕ) (hi : ¬(bad' i ∨ i=n+next)) :
        (run (C.gates.take next) (List.ofFn (Fin.snoc y false))).getD i false =
        (run (C.gates.take next) (List.ofFn (Fin.snoc y true))).getD i false := by
      simp only [hsplit, run_append (C.gates.take j) (mid ++ [C.gates.get a])]
      apply (hVals y).2 i
      simpa only [bad',or_assoc,hNextIndex] using hi
    obtain ⟨r,hr⟩ := ih _ hdecrease next hnext rfl bad' hNo hBadOut hNextTrue hNextAgree
    exact ⟨a::r, Route.next a (by dsimp [a]; omega) hLink hr⟩

end PEqualNP.Outside.L568Cut


namespace PEqualNP.Outside.L568Cut

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wire (n : ℕ) {C : Circuit} (a : Fin C.gates.length) := n+1+a.val

private theorem or_ne_not : GateOp.or ≠ GateOp.not := by
  intro h
  cases h

def Edge (n : ℕ) (C : Circuit) (v w : ℕ) :=
  ∃ a : Fin C.gates.length, w = wire n a ∧ Reads (C.gates.get a) v

theorem Route.lower {n C j r} (hr : Route n C j r) :
    ∀ a ∈ r, j ≤ (a : Fin C.gates.length).val := by
  induction r generalizing j with
  | nil => simp
  | cons a r ih =>
    obtain ⟨hj,hlink,hs⟩ := hr
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hj
    · exact hj.trans ((Nat.le_succ _).trans (ih hs _ hp))

theorem Route.increasing {n C j r} (hr : Route n C j r) : r.Pairwise (· < ·) := by
  induction r generalizing j with
  | nil => simp
  | cons a r ih =>
    obtain ⟨hj,hlink,hs⟩ := hr
    apply List.pairwise_cons.mpr
    exact ⟨fun b hb => hs.lower b hb, ih hs⟩

theorem Route.links {n C j r} (hr : Route n C j r) :
    (∀ a, r[0]? = some a → Link n C (n+j) a) ∧
    (∀ i a b, r[i]? = some a → r[i+1]? = some b → Link n C (wire n a) b) := by
  induction r generalizing j with
  | nil => simp
  | cons a r ih =>
    obtain ⟨hj,hlink,hs⟩ := hr
    constructor
    · intro p hp
      have he : a = p := by simpa using hp
      exact he ▸ hlink
    · intro i p q hp hq
      cases i with
      | zero =>
        have he : a = p := by simpa using hp
        subst p
        have hh := (ih hs).1 q (by simpa using hq)
        simpa [wire, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
      | succ i =>
        exact (ih hs).2 i p q (by simpa using hp) (by simpa [Nat.add_assoc] using hq)

theorem Route.nil_end {n C j} (hr : Route n C j []) :
    j = C.gates.length ∧ C.output = n + C.gates.length := hr

theorem Route.last {n C j r} (hr : Route n C j r) :
    ∀ a, r.getLast? = some a → a.val+1 = C.gates.length ∧ C.output = wire n a := by
  induction r generalizing j with
  | nil => simp
  | cons a r ih =>
    obtain ⟨hj,hlink,hs⟩ := hr
    intro b hb
    cases r with
    | nil =>
      have he : a = b := by simpa using hb
      subst b
      obtain ⟨hEnd,hOut⟩ := hs.nil_end
      refine ⟨hEnd,?_⟩
      unfold wire
      omega
    | cons p ps =>
      exact ih hs b (by simpa using hb)

theorem Route.reachable {n C j r} (hr : Route n C j r)
    (available : ∀ (a : Fin C.gates.length) v, Reads (C.gates.get a) v → v < wire n a) :
    ∀ v, Relation.TransGen (Edge n C) (n+j) v ↔ ∃ a ∈ r, v = wire n a := by
  induction r generalizing j with
  | nil =>
    obtain ⟨rfl,_⟩ := hr.nil_end
    intro v
    constructor
    · intro h
      obtain ⟨w, ⟨a,ha,hread⟩, ht⟩ := Relation.TransGen.head'_iff.mp h
      have hh := available a _ hread
      have hk := a.isLt
      unfold wire at hh
      omega
    · simp
  | cons a r ih =>
    obtain ⟨hj,hlink,hs⟩ := hr
    intro v
    have ha : Edge n C (n+j) (wire n a) :=
      ⟨a,rfl,Or.inr ⟨fun eq => or_ne_not (hlink.op.symm.trans eq), hlink.input⟩⟩
    have hwire : n+(a.val+1) = wire n a := by unfold wire; omega
    constructor
    · intro h
      obtain ⟨w, ⟨b,rfl,hread⟩, ht⟩ := Relation.TransGen.head'_iff.mp h
      have he := hlink.only b hread
      subst b
      rcases Relation.reflTransGen_iff_eq_or_transGen.mp ht with eq | ht
      · exact ⟨a,List.mem_cons_self,eq⟩
      · rw [← hwire] at ht
        obtain ⟨p,hp,he⟩ := (ih hs v).mp ht
        exact ⟨p,List.mem_cons_of_mem _ hp,he⟩
    · rintro ⟨p,hp,rfl⟩
      rcases List.mem_cons.mp hp with rfl | hp
      · exact Relation.TransGen.single ha
      · have ht := (ih hs (wire n p)).mpr ⟨p,hp,rfl⟩
        rw [hwire] at ht
        exact ht.head ha

end PEqualNP.Outside.L568Cut

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.Outside.L568Cut in
theorem PEqualNP.Outside.L_meta_568 :
    ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (H : (Fin n → Bool) → Bool), PEqualNP.MetaComplexity.IsMinimalCircuit (n + 1) C → (∃ y y' : Fin n → Bool, H y ≠ H y') → (∀ x : Fin (n + 1) → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C x = (x (Fin.last n) || H (fun i : Fin n => x i.castSucc))) → ∃ (k : ℕ) (c : Fin (k + 1) → Fin C.gates.length), StrictMono c ∧ (c (Fin.last k)).val + 1 = C.gates.length ∧ C.output = n + 1 + (c (Fin.last k)).val ∧ (∀ i : Fin (k + 1), (C.gates.get (c i)).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get (c i)).inputs.length = 2) ∧ n ∈ (C.gates.get (c 0)).inputs ∧ (∀ i : Fin k, n + 1 + (c i.castSucc).val ∈ (C.gates.get (c i.succ)).inputs) ∧ (∀ j : Fin C.gates.length, ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some n ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ n ∈ (C.gates.get j).inputs) → j = c 0) ∧ (∀ (i : Fin k) (j : Fin C.gates.length), ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some (n + 1 + (c i.castSucc).val) ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (n + 1 + (c i.castSucc).val) ∈ (C.gates.get j).inputs) → j = c i.succ) ∧ (∀ j : Fin C.gates.length, Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n (n + 1 + j.val) ↔ ∃ i : Fin (k + 1), c i = j) ∧ (∃ w ∈ (C.gates.get (c 0)).inputs, w ≠ n ∧ w < n + 1 + (c 0).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n w) ∧ (∀ i : Fin k, ∃ w ∈ (C.gates.get (c i.succ)).inputs, w ≠ n + 1 + (c i.castSucc).val ∧ w ≠ n ∧ w < n + 1 + (c i.succ).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n w) := by
  intro n C H hmin hnc h
  have h0 : ∃ y, H y = false := by
    obtain ⟨a,b,hab⟩ := hnc
    cases ha : H a
    · exact ⟨a,ha⟩
    · cases hb : H b
      · exact ⟨b,hb⟩
      · exact (hab (ha.trans hb.symm)).elim
  have h1 : ∃ y, H y = true := by
    obtain ⟨a,b,hab⟩ := hnc
    cases ha : H a
    · cases hb : H b
      · exact (hab (ha.trans hb.symm)).elim
      · exact ⟨b,hb⟩
    · exact ⟨a,ha⟩
  have hEval (y : Fin n → Bool) (b : Bool) :
      circuitFun (n+1) C (Fin.snoc y b) = (b || H y) := by rw [h]; simp
  have hncC : ∃ x x' : Fin (n+1) → Bool, circuitFun (n+1) C x ≠ circuitFun (n+1) C x' := by
    obtain ⟨y,hy⟩ := h0
    refine ⟨Fin.snoc y false, Fin.snoc y true, ?_⟩
    rw [hEval,hEval,hy]
    decide
  have hVec (y : Fin n → Bool) (b : Bool) :
      List.ofFn (Fin.snoc y b) = List.ofFn y ++ [b] := by
    rw [List.ofFn_succ']
    simp
  have hnOut : C.output ≠ n := by
    intro eq
    obtain ⟨y,hy⟩ := h1
    have he := hEval y false
    change (C.wires (List.ofFn (Fin.snoc y false))).getD C.output false = (false || H y) at he
    rw [Circuit.wires, eq, L568.wirePrefix _ _ _ (by simp), hVec,
      List.getD_append_right _ _ _ _ (by simp), hy] at he
    simp at he
  obtain ⟨r,hr⟩ := build_route n C H hmin hncC h0 h C.gates.length 0
    (Nat.zero_le _) (Nat.sub_zero _) (fun _ => False)
    (by simp) (by simp)
    (by
      intro y
      simp only [List.take_zero, run, List.foldl_nil, Nat.add_zero]
      rw [hVec, List.getD_append_right _ _ _ _ (by simp)]
      simp)
    (by
      intro y i hi
      simp only [List.take_zero, run, List.foldl_nil, Nat.add_zero, false_or] at hi ⊢
      rw [hVec,hVec]
      by_cases hlt : i < n
      · rw [List.getD_append _ _ _ _ (by simpa using hlt),
          List.getD_append _ _ _ _ (by simpa using hlt)]
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)])
  cases r with
  | nil =>
    obtain ⟨hlen,hout⟩ := hr.nil_end
    exact (hnOut (by omega)).elim
  | cons a r =>
    let k := r.length
    let c : Fin (k+1) → Fin C.gates.length := fun i => (a::r)[i.val]'(by simpa [k] using i.isLt)
    have hget (i : Fin (k+1)) : (a::r)[i.val]? = some (c i) :=
      List.getElem?_eq_getElem (by simpa [k] using i.isLt)
    have hm : StrictMono c := by
      intro i j hij
      exact List.pairwise_iff_getElem.mp hr.increasing i.val j.val
        (by simpa [k] using i.isLt) (by simpa [k] using j.isLt) hij
    have hlast : (a::r).getLast? = some (c (Fin.last k)) := by
      rw [List.getLast?_eq_getElem?]
      simpa [k] using hget (Fin.last k)
    obtain ⟨hl,ho⟩ := hr.last _ hlast
    have first : Link n C n (c 0) := by
      simpa only [Nat.add_zero] using hr.links.1 (c 0) (hget 0)
    have next (i : Fin k) : Link n C (wire n (c i.castSucc)) (c i.succ) :=
      hr.links.2 i.val _ _ (hget i.castSucc) (hget i.succ)
    have hav (a : Fin C.gates.length) (w : ℕ) (hw : Reads (C.gates.get a) w) : w < wire n a :=
      read_available (n+1) C hmin hncC a w hw
    have hReach (v : ℕ) : Relation.TransGen (Edge n C) n v ↔
        ∃ i : Fin (k+1), v = wire n (c i) := by
      have hR := hr.reachable hav v
      simp only [Nat.add_zero] at hR
      rw [hR]
      constructor
      · rintro ⟨b,hb,rfl⟩
        obtain ⟨i,hi,hb⟩ := List.mem_iff_getElem.mp hb
        exact ⟨⟨i,by simpa [k] using hi⟩, by rw [← hb]⟩
      · rintro ⟨i,rfl⟩
        exact ⟨c i,List.mem_iff_getElem?.mpr ⟨i.val,hget i⟩,rfl⟩
    have hEdge (i j : Fin (k+1)) : wire n (c i) < wire n (c j) → i < j := by
      intro hlt
      apply lt_of_not_ge
      intro hge
      have hb := hm.monotone hge
      change (c j).val ≤ (c i).val at hb
      unfold wire at hlt
      omega
    have allOp (i : Fin (k+1)) :
        (C.gates.get (c i)).op = GateOp.or ∧ (C.gates.get (c i)).inputs.length = 2 := by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact Fin.cases ⟨first.op, first.arity⟩ (fun j => ⟨(next j).op, (next j).arity⟩) (Fin.last k)
      · exact Fin.cases ⟨first.op, first.arity⟩ (fun j => ⟨(next j).op, (next j).arity⟩) j.castSucc
    refine ⟨k,c,hm,hl,ho,allOp,first.input,(fun i => (next i).input),
      first.only,(fun i => (next i).only),?_,?_,?_⟩
    · intro b
      change Relation.TransGen (Edge n C) n (wire n b) ↔ _
      rw [hReach]
      constructor
      · rintro ⟨i,hi⟩
        refine ⟨i,Fin.ext ?_⟩
        unfold wire at hi
        omega
      · rintro ⟨i,rfl⟩
        exact ⟨i,rfl⟩
    · obtain ⟨w,hw,hwne,hwlt⟩ := first.side
      refine ⟨w,hw,hwne,hwlt,?_⟩
      change ¬Relation.TransGen (Edge n C) n w
      intro hReachW
      obtain ⟨i,hew⟩ := (hReach w).mp hReachW
      rw [hew] at hwlt
      have hlt := hEdge i 0 hwlt
      exact Fin.not_lt_zero i hlt
    · intro i
      obtain ⟨w,hw,hwne,hwlt⟩ := (next i).side
      have read : Reads (C.gates.get (c i.succ)) w :=
        Or.inr ⟨(fun eq => or_ne_not ((next i).op.symm.trans eq)), hw⟩
      have hne : w ≠ n := by
        intro he
        have heq := first.only (c i.succ) (he ▸ read)
        have he' := congrArg Fin.val (hm.injective heq)
        simp at he'
      refine ⟨w,hw,hwne,hne,hwlt,?_⟩
      change ¬Relation.TransGen (Edge n C) n w
      intro hReachW
      obtain ⟨a,ha⟩ := (hReach w).mp hReachW
      rw [ha] at hwlt
      have hal := hEdge a i.succ hwlt
      let b : Fin k := ⟨a.val, by have := i.isLt; exact lt_of_lt_of_le hal (Nat.succ_le_of_lt i.isLt)⟩
      have hb : b.castSucc = a := Fin.ext rfl
      have read' : Reads (C.gates.get (c i.succ)) (wire n (c b.castSucc)) := by
        rw [hb, ← ha]
        exact read
      have eq := (next b).only (c i.succ) read'
      have hp : i = b := Fin.ext (by
        have he := congrArg Fin.val (hm.injective eq)
        simpa only [Fin.val_succ, Nat.add_right_cancel_iff] using he)
      apply hwne
      rw [hp,hb,ha]
