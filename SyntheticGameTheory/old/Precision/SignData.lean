import SyntheticGameTheory.Precision.CellGame

namespace SyntheticGameTheory

-- ================================================================
-- Section 1: Sign type
-- ================================================================

/-- The sign of a preference difference at a grid point.
    - `pos`: player strictly prefers action with higher index
    - `zero`: player is indifferent
    - `neg`: player strictly prefers action with lower index -/
inductive Sign where
  | pos : Sign
  | neg : Sign
  | zero : Sign
  deriving DecidableEq, Repr

instance Sign.instFintype : Fintype Sign :=
  ⟨{.pos, .neg, .zero}, by intro x; cases x <;> simp⟩

namespace Sign

/-- Flip: pos ↔ neg, zero stays. -/
def flip : Sign → Sign
  | pos => neg
  | neg => pos
  | zero => zero

@[simp] theorem flip_pos : flip pos = neg := rfl
@[simp] theorem flip_neg : flip neg = pos := rfl
@[simp] theorem flip_zero : flip zero = zero := rfl
@[simp] theorem flip_flip (s : Sign) : s.flip.flip = s := by cases s <;> rfl

end Sign

-- ================================================================
-- Section 2: Midpoint sign coherence table
-- ================================================================

/-- The midpoint sign constraint from the affine coherence table.
    Given signs at adjacent level-k points, constrains the midpoint sign at level k+1.
    Returns `none` if unconstrained (opposite nonzero signs),
    or `some s` if the midpoint must be `s`. -/
def forcedMidpointSign (sx sy : Sign) : Option Sign :=
  match sx, sy with
  | .pos, .pos => some .pos
  | .neg, .neg => some .neg
  | .zero, .zero => some .zero
  | .pos, .zero => some .pos
  | .zero, .pos => some .pos
  | .neg, .zero => some .neg
  | .zero, .neg => some .neg
  | .pos, .neg => none
  | .neg, .pos => none

-- ================================================================
-- Section 3: Sign extraction from GridPrefSystem
-- ================================================================

/-- Extract the preference sign of player i at opponent grid point j,
    comparing adjacent actions lo and lo+1.
    - pos: strictly prefers lo+1 over lo (¬pref lo hi, hence pref hi lo by totality)
    - neg: strictly prefers lo over lo+1 (pref lo hi ∧ ¬pref hi lo)
    - zero: indifferent (pref both ways) -/
noncomputable def GridPrefSystem.signAt (gps : GridPrefSystem k) (i : Fin 2)
    (j : Fin (2 ^ k + 1)) (lo : Fin (2 ^ k)) : Sign :=
  let hi : Fin (2 ^ k + 1) := ⟨lo.val + 1, by omega⟩
  let lo' : Fin (2 ^ k + 1) := ⟨lo.val, by omega⟩
  if gps.pref i j lo' hi then
    if gps.pref i j hi lo' then .zero else .neg
  else .pos

-- signAt characterizes the preference relation
theorem GridPrefSystem.signAt_pos_iff (gps : GridPrefSystem k) (i : Fin 2)
    (j : Fin (2 ^ k + 1)) (e : Fin (2 ^ k)) :
    gps.signAt i j e = .pos ↔
      ¬gps.pref i j ⟨e.val, by omega⟩ ⟨e.val + 1, by omega⟩ := by
  simp only [GridPrefSystem.signAt]
  split_ifs <;> simp_all

theorem GridPrefSystem.signAt_neg_iff (gps : GridPrefSystem k) (i : Fin 2)
    (j : Fin (2 ^ k + 1)) (e : Fin (2 ^ k)) :
    gps.signAt i j e = .neg ↔
      gps.pref i j ⟨e.val, by omega⟩ ⟨e.val + 1, by omega⟩ ∧
      ¬gps.pref i j ⟨e.val + 1, by omega⟩ ⟨e.val, by omega⟩ := by
  simp only [GridPrefSystem.signAt]
  split_ifs <;> simp_all

theorem GridPrefSystem.signAt_zero_iff (gps : GridPrefSystem k) (i : Fin 2)
    (j : Fin (2 ^ k + 1)) (e : Fin (2 ^ k)) :
    gps.signAt i j e = .zero ↔
      gps.pref i j ⟨e.val, by omega⟩ ⟨e.val + 1, by omega⟩ ∧
      gps.pref i j ⟨e.val + 1, by omega⟩ ⟨e.val, by omega⟩ := by
  simp only [GridPrefSystem.signAt]
  split_ifs <;> simp_all

-- ================================================================
-- Section 4: Local sign data types
-- ================================================================

/-- Local sign data at a profile: for each player, a pair of signs
    at the left and right grid points of the opponent's cell. -/
abbrev LocalSignData := Fin 2 → Sign × Sign

/-- Midpoint data: for each player, the midpoint sign at the opponent's cell. -/
abbrev MidpointSignData := Fin 2 → Sign

/-- Extract local signs from a GridPrefSystem at a cell profile.
    Player i's signs come from the opponent's cell grid points.
    - Player i on vertex: (zero, zero)
    - Opponent on vertex j: (signAt at j, signAt at j) — same sign repeated
    - Both on edges: (signAt at opponent's left endpoint, signAt at opponent's right) -/
noncomputable def GridPrefSystem.localSignsAt (gps : GridPrefSystem k)
    (σ : CellProfile1 k) : LocalSignData :=
  fun i =>
    match σ i, σ (1 - i) with
    | .vertex _, _ => (.zero, .zero)
    | .edge ei, .vertex j => (gps.signAt i j ei, gps.signAt i j ei)
    | .edge ei, .edge ej =>
      let jl : Fin (2 ^ k + 1) := ⟨ej.val, by omega⟩
      let jr : Fin (2 ^ k + 1) := ⟨ej.val + 1, by omega⟩
      (gps.signAt i jl ei, gps.signAt i jr ei)

-- ================================================================
-- Section 5: Sign patterns
-- ================================================================

/-- A sign pair is Nash-compatible: flip or all-zero. -/
def IsNashPair (p : Sign × Sign) : Prop :=
  p = (.pos, .neg) ∨ p = (.neg, .pos) ∨ p = (.zero, .zero)

instance IsNashPair.instDecidable {p : Sign × Sign} : Decidable (IsNashPair p) :=
  instDecidableOr

/-- Midpoint coherence: midpoint signs respect the affine constraint table. -/
def MidpointCoherent (σ : CellProfile1 k) (d : LocalSignData) (md : MidpointSignData) :
    Prop :=
  ∀ i : Fin 2, match σ (1 - i) with
    | .vertex _ => md i = .zero
    | .edge _ =>
        match forcedMidpointSign (d i).1 (d i).2 with
        | some s => md i = s
        | none => True

-- ================================================================
-- Section 6: CellDevLE reductions
-- ================================================================

-- These reduce CellDevLE to concrete pref checks, stripping away the
-- grid point membership quantifiers.

theorem CellDevLE_vertex_vertex (gps : GridPrefSystem k) (i : Fin 2)
    (σ : CellProfile1 k) (a b : Fin (2 ^ k + 1)) :
    CellDevLE gps i σ (.vertex a) (.vertex b) ↔
      ∀ q ∈ (σ (1 - i)).gridPoints,
        gps.pref i (GridPoint.toIndex1 q) a b := by
  constructor
  · intro h q hq
    have := h q hq (ElemCell1.gridPt a) (by simp) (ElemCell1.gridPt b) (by simp)
    simpa [GridPoint.toIndex1, GridPoint.ofIndex1] using this
  · intro h q hq a' ha' b' hb'
    simp [ElemCell1.gridPoints] at ha' hb'
    subst ha'; subst hb'
    simpa [GridPoint.toIndex1, GridPoint.ofIndex1] using h q hq

theorem CellDevLE_edge_vertex (gps : GridPrefSystem k) (i : Fin 2)
    (σ : CellProfile1 k) (e : Fin (2 ^ k)) (b : Fin (2 ^ k + 1)) :
    CellDevLE gps i σ (.edge e) (.vertex b) ↔
      ∀ q ∈ (σ (1 - i)).gridPoints,
        gps.pref i (GridPoint.toIndex1 q) ⟨e.val, by omega⟩ b ∧
        gps.pref i (GridPoint.toIndex1 q) ⟨e.val + 1, by omega⟩ b := by
  constructor
  · intro h q hq
    exact ⟨by have := h q hq (ElemCell1.gridPt ⟨e.val, by omega⟩)
                (by simp [ElemCell1.gridPoints])
                (ElemCell1.gridPt b) (by simp)
              simpa [GridPoint.toIndex1, GridPoint.ofIndex1] using this,
           by have := h q hq (ElemCell1.gridPt ⟨e.val + 1, by omega⟩)
                (by simp [ElemCell1.gridPoints])
                (ElemCell1.gridPt b) (by simp)
              simpa [GridPoint.toIndex1, GridPoint.ofIndex1] using this⟩
  · intro h q hq a ha b' hb'
    simp [ElemCell1.gridPoints] at ha hb'; subst hb'
    obtain ⟨h1, h2⟩ := h q hq
    rcases ha with rfl | rfl <;>
      simpa [ElemCell1.gridPt, GridPoint.toIndex1, GridPoint.ofIndex1]

theorem CellDevLE_vertex_edge (gps : GridPrefSystem k) (i : Fin 2)
    (σ : CellProfile1 k) (a : Fin (2 ^ k + 1)) (e : Fin (2 ^ k)) :
    CellDevLE gps i σ (.vertex a) (.edge e) ↔
      ∀ q ∈ (σ (1 - i)).gridPoints,
        gps.pref i (GridPoint.toIndex1 q) a ⟨e.val, by omega⟩ ∧
        gps.pref i (GridPoint.toIndex1 q) a ⟨e.val + 1, by omega⟩ := by
  constructor
  · intro h q hq
    exact ⟨by have := h q hq (ElemCell1.gridPt a) (by simp)
                (ElemCell1.gridPt ⟨e.val, by omega⟩)
                (by simp [ElemCell1.gridPoints])
              simpa [GridPoint.toIndex1, GridPoint.ofIndex1] using this,
           by have := h q hq (ElemCell1.gridPt a) (by simp)
                (ElemCell1.gridPt ⟨e.val + 1, by omega⟩)
                (by simp [ElemCell1.gridPoints])
              simpa [GridPoint.toIndex1, GridPoint.ofIndex1] using this⟩
  · intro h q hq a' ha' b hb
    simp [ElemCell1.gridPoints] at ha' hb; subst ha'
    obtain ⟨h1, h2⟩ := h q hq
    rcases hb with rfl | rfl <;>
      simpa [ElemCell1.gridPt, GridPoint.toIndex1, GridPoint.ofIndex1]

theorem CellDevLE_edge_edge (gps : GridPrefSystem k) (i : Fin 2)
    (σ : CellProfile1 k) (ea eb : Fin (2 ^ k)) :
    CellDevLE gps i σ (.edge ea) (.edge eb) ↔
      ∀ q ∈ (σ (1 - i)).gridPoints,
        gps.pref i (GridPoint.toIndex1 q) ⟨ea.val, by omega⟩ ⟨eb.val, by omega⟩ ∧
        gps.pref i (GridPoint.toIndex1 q) ⟨ea.val, by omega⟩ ⟨eb.val + 1, by omega⟩ ∧
        gps.pref i (GridPoint.toIndex1 q) ⟨ea.val + 1, by omega⟩ ⟨eb.val, by omega⟩ ∧
        gps.pref i (GridPoint.toIndex1 q) ⟨ea.val + 1, by omega⟩ ⟨eb.val + 1, by omega⟩ := by
  constructor
  · intro h q hq
    have mk := fun (a b : Fin (2 ^ k + 1)) (ha hb) =>
      h q hq (ElemCell1.gridPt a) ha (ElemCell1.gridPt b) hb
    simp [ElemCell1.gridPt, GridPoint.toIndex1, GridPoint.ofIndex1] at mk
    exact ⟨mk _ _ (by simp [ElemCell1.gridPoints]; left; rfl)
                   (by simp [ElemCell1.gridPoints]; left; rfl),
           mk _ _ (by simp [ElemCell1.gridPoints]; left; rfl)
                   (by simp [ElemCell1.gridPoints]; right; rfl),
           mk _ _ (by simp [ElemCell1.gridPoints]; right; rfl)
                   (by simp [ElemCell1.gridPoints]; left; rfl),
           mk _ _ (by simp [ElemCell1.gridPoints]; right; rfl)
                   (by simp [ElemCell1.gridPoints]; right; rfl)⟩
  · intro h q hq a ha b hb
    simp [ElemCell1.gridPoints] at ha hb
    obtain ⟨h1, h2, h3, h4⟩ := h q hq
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      simpa [ElemCell1.gridPt, GridPoint.toIndex1, GridPoint.ofIndex1]

-- ================================================================
-- Section 6b: Sign determines pref between adjacent grid actions
-- ================================================================

/-- If sign is zero, pref holds in both directions. -/
theorem GridPrefSystem.pref_of_signAt_zero (gps : GridPrefSystem k)
    (i : Fin 2) (j : Fin (2 ^ k + 1)) (e : Fin (2 ^ k))
    (h : gps.signAt i j e = .zero) :
    gps.pref i j ⟨e.val, by omega⟩ ⟨e.val + 1, by omega⟩ ∧
    gps.pref i j ⟨e.val + 1, by omega⟩ ⟨e.val, by omega⟩ :=
  (gps.signAt_zero_iff i j e).mp h

/-- Convenience: if sign is pos, strictly prefers hi (¬pref lo hi). -/
theorem GridPrefSystem.not_pref_lo_of_signAt_pos (gps : GridPrefSystem k)
    (i : Fin 2) (j : Fin (2 ^ k + 1)) (e : Fin (2 ^ k))
    (h : gps.signAt i j e = .pos) :
    ¬gps.pref i j ⟨e.val, by omega⟩ ⟨e.val + 1, by omega⟩ :=
  (gps.signAt_pos_iff i j e).mp h

/-- Convenience: if sign is neg, pref lo hi ∧ ¬pref hi lo. -/
theorem GridPrefSystem.pref_of_signAt_neg (gps : GridPrefSystem k)
    (i : Fin 2) (j : Fin (2 ^ k + 1)) (e : Fin (2 ^ k))
    (h : gps.signAt i j e = .neg) :
    gps.pref i j ⟨e.val, by omega⟩ ⟨e.val + 1, by omega⟩ ∧
    ¬gps.pref i j ⟨e.val + 1, by omega⟩ ⟨e.val, by omega⟩ :=
  (gps.signAt_neg_iff i j e).mp h

-- ================================================================
-- Section 6c: Coarsen preserves pref at embedded indices
-- ================================================================

/-- Coarsen preserves individual pref at embedded indices. -/
theorem GridPrefSystem.coarsen_pref_eq (gps : GridPrefSystem (k + 1))
    (i : Fin 2) (j a b : Fin (2 ^ k + 1)) :
    gps.coarsen.pref i j a b ↔
      gps.pref i (ElemCell1.embedIndex j) (ElemCell1.embedIndex a) (ElemCell1.embedIndex b) :=
  Iff.rfl

-- ================================================================
-- Section 6d: Extracting midpoint signs from gps' at k+1
-- ================================================================

/-- Extract the midpoint sign for player i from gps' at level k+1 relative to
    a profile σ at level k. When the opponent is on edge ej, the midpoint
    is at index 2*ej+1, and we look at player i's edge ei. -/
noncomputable def GridPrefSystem.midpointSignsAt (gps' : GridPrefSystem (k + 1))
    (σ : CellProfile1 k) : MidpointSignData :=
  fun i =>
    match σ i, σ (1 - i) with
    | .vertex _, _ => .zero
    | .edge _, .vertex _ => .zero
    | .edge ei, .edge ej =>
      gps'.signAt i (ElemCell1.midIndex ej) ⟨2 * ei.val, by omega⟩

-- ================================================================
-- Section 7: Refinement machinery
-- ================================================================

/-- Refine an edge cell using the opponent's signs and midpoint.
    For flip pairs, the midpoint sign determines the subcell:
    - If m agrees with sl (player prefers lo at midpoint too): pick left edge
    - If m agrees with sr (player prefers hi at midpoint too): pick right edge
    - If m = zero (indifferent at midpoint): pick midpoint vertex -/
def refineEdge (j : Fin (2 ^ k)) (sl sr m : Sign) : ElemCell1 (k + 1) :=
  have h := j.isLt
  let left : ElemCell1 (k + 1) := .edge ⟨2 * j.val, by omega⟩
  let right : ElemCell1 (k + 1) := .edge ⟨2 * j.val + 1, by omega⟩
  let mid : ElemCell1 (k + 1) := .vertex (ElemCell1.midIndex j)
  match sl, sr with
  | .pos, .neg => match m with
    | .pos => left     -- m agrees with sl: prefers lo at midpoint → left edge
    | .zero => mid     -- indifferent at midpoint → midpoint vertex
    | .neg => right    -- m agrees with sr: prefers hi at midpoint → right edge
  | .neg, .pos => match m with
    | .pos => left     -- m agrees with sr: prefers lo at midpoint → left edge
    | .zero => mid     -- indifferent at midpoint → midpoint vertex
    | .neg => right    -- m agrees with sl: prefers hi at midpoint → right edge
  | _, _ => left

/-- Refine a single cell using the opponent's sign data. -/
def refineCell (c : ElemCell1 k) (oppSigns : Sign × Sign) (oppMid : Sign) :
    ElemCell1 (k + 1) :=
  match c with
  | .vertex j => .vertex (ElemCell1.embedIndex j)
  | .edge j => refineEdge j oppSigns.1 oppSigns.2 oppMid

/-- The refined profile. Player i's cell is refined using player i's own sign data. -/
def refineProfile (σ : CellProfile1 k) (d : LocalSignData) (md : MidpointSignData) :
    CellProfile1 (k + 1) :=
  fun i => refineCell (σ i) (d i) (md i)

private theorem fin2_sub_sub (i : Fin 2) : 1 - (1 - i) = i := by omega

-- refineEdge always produces a subcell
theorem refineEdge_mem_subcells (j : Fin (2 ^ k)) (sl sr m : Sign) :
    refineEdge j sl sr m ∈ (ElemCell1.edge j).subcells := by
  simp only [refineEdge, ElemCell1.subcells]
  have h := j.isLt
  cases sl <;> cases sr <;> (try cases m) <;> simp_all [ElemCell1.midIndex]

/-- Refinement produces valid subcells. -/
theorem refineProfile_refines (σ : CellProfile1 k) (d : LocalSignData)
    (md : MidpointSignData) :
    (refineProfile σ d md).Refines σ := by
  intro i; simp only [refineProfile]
  cases σ i with
  | vertex j => simp [refineCell, ElemCell1.subcells]
  | edge j => exact refineEdge_mem_subcells j _ _ _

-- ================================================================
-- Section 8: Backward direction — extracting midpoint data
-- ================================================================

/-- Extract midpoint sign from a subcell position for a flip pair.
    For both (pos,neg) and (neg,pos) flip pairs:
    - left edge → pos (lower-preferring at midpoint)
    - midpoint vertex → zero (indifferent at midpoint)
    - right edge → neg (higher-preferring at midpoint) -/
def extractFlipMid (j : Fin (2 ^ k)) (sl sr : Sign) (c' : ElemCell1 (k + 1)) : Sign :=
  match sl, sr with
  | .pos, .neg | .neg, .pos =>
    match c' with
    | .vertex _ => .zero
    | .edge j' => if j'.val = 2 * j.val then .pos else .neg
  | _, _ => .zero

/-- extractFlipMid inverts refineEdge for flip Nash pairs. -/
theorem refineEdge_extractFlipMid (j : Fin (2 ^ k)) {sl sr : Sign}
    (hNP : IsNashPair (sl, sr)) (hFlip : (sl, sr) ≠ (.zero, .zero))
    (c' : ElemCell1 (k + 1)) (hMem : c' ∈ (ElemCell1.edge j).subcells) :
    refineEdge j sl sr (extractFlipMid j sl sr c') = c' := by
  simp [ElemCell1.subcells] at hMem
  have h := j.isLt
  rcases hNP with hp | hp | hp
  all_goals (have hl := congrArg Prod.fst hp; have hr := congrArg Prod.snd hp;
             simp at hl hr; subst hl; subst hr)
  · rcases hMem with rfl | rfl | rfl <;> simp [extractFlipMid, refineEdge, ElemCell1.midIndex]
  · rcases hMem with rfl | rfl | rfl <;> simp [extractFlipMid, refineEdge, ElemCell1.midIndex]
  · exact absurd rfl hFlip

/-- refineEdge is injective on the midpoint sign for flip Nash pairs. -/
theorem refineEdge_injective_flip (j : Fin (2 ^ k)) {sl sr : Sign}
    (hNP : IsNashPair (sl, sr)) (hFlip : (sl, sr) ≠ (.zero, .zero))
    {m1 m2 : Sign} (h : refineEdge j sl sr m1 = refineEdge j sl sr m2) : m1 = m2 := by
  have hj := j.isLt
  rcases hNP with hp | hp | hp
  all_goals (have hl := congrArg Prod.fst hp; have hr := congrArg Prod.snd hp;
             simp at hl hr; subst hl; subst hr)
  · cases m1 <;> cases m2 <;> simp_all [refineEdge, ElemCell1.midIndex]
  · cases m1 <;> cases m2 <;> simp_all [refineEdge, ElemCell1.midIndex]
  · exact absurd rfl hFlip

end SyntheticGameTheory
