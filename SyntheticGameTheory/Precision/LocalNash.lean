import SyntheticGameTheory
import SyntheticGameTheory.Precision.Grid
import SyntheticGameTheory.Precision.PrecisionGame
import SyntheticGameTheory.Precision.SignData

namespace SyntheticGameTheory

open Sign ElemCell1

-- ================================================================
-- Section 1: Local sign data (flat, non-dependent formulation)
-- ================================================================

/-- Local sign data at a profile: for each player, a pair of signs.
    When both players are on edges, the two signs are player i's preference
    signs at the left and right grid points of the opponent's cell.
    Otherwise, constrained to (zero, zero) by IsLocalNash. -/
abbrev LocalSignData := Fin 2 → Sign × Sign

/-- Midpoint data: for each player, the midpoint sign at the opponent's cell. -/
abbrev MidpointSignData := Fin 2 → Sign

/-- A sign pair is Nash-compatible: flip or all-zero. -/
def IsNashPair (p : Sign × Sign) : Prop :=
  p = (.pos, .neg) ∨ p = (.neg, .pos) ∨ p = (.zero, .zero)

instance : Decidable (IsNashPair p) := instDecidableOr

-- ================================================================
-- Section 2: Local Nash and coherence
-- ================================================================

/-- A profile is locally Nash if every player's sign data is Nash-consistent
    relative to the cell configuration. -/
def IsLocalNash (σ : ElemProfile1 k) (d : LocalSignData) : Prop :=
  ∀ i : Fin 2, match σ i, σ (1 - i) with
    | .vertex _, _ => d i = (.zero, .zero)
    | .edge _, .vertex _ => d i = (.zero, .zero)
    | .edge _, .edge _ => IsNashPair (d i)

/-- Midpoint coherence: midpoint signs respect the affine constraint table. -/
def MidpointCoherent (σ : ElemProfile1 k) (d : LocalSignData) (md : MidpointSignData) :
    Prop :=
  ∀ i : Fin 2, match σ (1 - i) with
    | .vertex _ => md i = .zero
    | .edge _ =>
        match forcedMidpointSign (d i).1 (d i).2 with
        | some s => md i = s
        | none => True

-- ================================================================
-- Section 3: Refinement
-- ================================================================

/-- Refine an edge cell using the opponent's signs and midpoint. -/
def refineEdge (j : Fin (2 ^ k)) (sl sr m : Sign) : ElemCell1 (k + 1) :=
  have h := j.isLt
  let left : ElemCell1 (k + 1) := .edge ⟨2 * j.val, by omega⟩
  let right : ElemCell1 (k + 1) := .edge ⟨2 * j.val + 1, by omega⟩
  let mid : ElemCell1 (k + 1) := .vertex (midIndex j)
  match sl, sr with
  | .pos, .neg => match m with
    | .pos => right
    | .zero => mid
    | .neg => left
  | .neg, .pos => match m with
    | .neg => right
    | .zero => mid
    | .pos => left
  | _, _ => left

/-- Refine a single cell using the opponent's sign data. -/
def refineCell (c : ElemCell1 k) (oppSigns : Sign × Sign) (oppMid : Sign) :
    ElemCell1 (k + 1) :=
  match c with
  | .vertex j => .vertex (embedIndex j)
  | .edge j => refineEdge j oppSigns.1 oppSigns.2 oppMid

/-- The refined profile. Player i's cell is refined using the opponent's data. -/
def refineProfile (σ : ElemProfile1 k) (d : LocalSignData) (md : MidpointSignData) :
    ElemProfile1 (k + 1) :=
  fun i => refineCell (σ i) (d (1 - i)) (md (1 - i))

/-- The induced local signs at the refined profile.
    Returns (zero, zero) when either the player or opponent refines to a vertex. -/
def refineLocalSigns (σ : ElemProfile1 k) (d : LocalSignData) (md : MidpointSignData) :
    LocalSignData :=
  fun i =>
    -- Check both players' original cells
    match σ i, σ (1 - i) with
    | .vertex _, _ => (.zero, .zero)
    | .edge _, .vertex _ => (.zero, .zero)
    | .edge ji, .edge jo =>
        -- Both original cells are edges.
        -- Check if player's own refinement produces a vertex (midpoint)
        match refineEdge ji (d (1 - i)).1 (d (1 - i)).2 (md (1 - i)) with
        | .vertex _ => (.zero, .zero)
        | .edge _ =>
          -- Player refines to edge. Check opponent's refinement.
          let (l, r) := d i
          let m := md i
          match refineEdge jo l r m with
          | .vertex _ => (.zero, .zero)
          | .edge j' =>
              if j'.val = 2 * jo.val then (l, m)
              else (m, r)

-- ================================================================
-- Section 4: Refinement is valid
-- ================================================================

private theorem refineEdge_mem_subcells (j : Fin (2 ^ k)) (sl sr m : Sign) :
    refineEdge j sl sr m ∈ (ElemCell1.edge j).subcells := by
  simp only [refineEdge, ElemCell1.subcells]
  have h := j.isLt
  cases sl <;> cases sr <;> (try cases m) <;> simp_all [midIndex]

theorem refineProfile_refines (σ : ElemProfile1 k) (d : LocalSignData)
    (md : MidpointSignData) :
    (refineProfile σ d md).Refines σ := by
  intro i; simp only [refineProfile]
  cases σ i with
  | vertex j => simp [refineCell, ElemCell1.subcells]
  | edge j => exact refineEdge_mem_subcells j _ _ _

-- ================================================================
-- Section 5: Key sign propagation lemma
-- ================================================================

/-- When signs are Nash and midpoint is coherent, refineEdge produces
    a sub-edge with Nash-compatible induced local signs, or a midpoint vertex. -/
private theorem refineEdge_localNash (j : Fin (2 ^ k)) {l r m : Sign}
    (hNash : IsNashPair (l, r))
    (hCoh : match forcedMidpointSign l r with | some s => m = s | none => True) :
    match refineEdge j l r m with
    | .vertex _ => True
    | .edge j' =>
        IsNashPair (if j'.val = 2 * j.val then (l, m) else (m, r)) := by
  unfold IsNashPair at hNash
  have h := j.isLt
  rcases hNash with hp | hp | hp
  · have hl := congrArg Prod.fst hp; have hr := congrArg Prod.snd hp
    simp at hl hr; subst hl; subst hr
    simp [forcedMidpointSign] at hCoh
    cases m <;> simp [refineEdge, midIndex, IsNashPair]
  · have hl := congrArg Prod.fst hp; have hr := congrArg Prod.snd hp
    simp at hl hr; subst hl; subst hr
    simp [forcedMidpointSign] at hCoh
    cases m <;> simp [refineEdge, midIndex, IsNashPair]
  · have hl := congrArg Prod.fst hp; have hr := congrArg Prod.snd hp
    simp at hl hr; subst hl; subst hr
    simp [forcedMidpointSign] at hCoh
    subst hCoh
    simp [refineEdge, IsNashPair]

-- ================================================================
-- Section 6: Refinement preserves local Nash
-- ================================================================

/-- Refinement preserves local Nash. -/
private theorem fin2_sub_sub (i : Fin 2) : 1 - (1 - i) = i := by omega

theorem localNash_refines (σ : ElemProfile1 k) (d : LocalSignData)
    (md : MidpointSignData) (hNash : IsLocalNash σ d)
    (hCoh : MidpointCoherent σ d md) :
    IsLocalNash (refineProfile σ d md) (refineLocalSigns σ d md) := by
  intro i
  -- Goal: match on refined cells. Unfold to expose σ i and σ (1-i).
  simp only [refineProfile, refineCell, refineLocalSigns, fin2_sub_sub]
  -- Case-split on original cells
  cases hci : σ i with
  | vertex vi =>
    -- Player i is on a vertex, so refineLocalSigns gives (zero, zero)
    -- and refineProfile gives vertex (embedIndex vi)
    cases hco : σ (1 - i) <;> simp_all
  | edge ji =>
    cases hco : σ (1 - i) with
    | vertex vo =>
      -- Opponent on vertex: refineLocalSigns gives (zero, zero)
      -- Refined player is edge, refined opponent is vertex
      simp
      -- Goal still has a match on refineEdge ji ... Need to case-split
      cases h : refineEdge ji (d (1 - i)).1 (d (1 - i)).2 (md (1 - i)) <;> simp
    | edge jo =>
      -- Both on edges: the interesting case
      simp
      have hNi : IsNashPair (d i) := by
        have := hNash i; simp [hci, hco] at this; exact this
      have hCohi : match forcedMidpointSign (d i).1 (d i).2 with
          | some s => md i = s | none => True := by
        have := hCoh i; simp [hco] at this; exact this
      -- The goal has nested matches on refineEdge for both players.
      -- refineLocalSigns depends on refineEdge jo (d i)... (opponent's edge with player's signs)
      -- IsLocalNash outer match depends on refineEdge ji (d (1-i))... and refineEdge jo (d i)...
      -- Case-split on player i's refinement first, then opponent's
      cases hRi : refineEdge ji (d (1 - i)).1 (d (1 - i)).2 (md (1 - i)) with
      | vertex _ =>
        -- Player refines to vertex: goal becomes True regardless of opponent
        cases refineEdge jo (d i).1 (d i).2 (md i) <;> simp_all
      | edge ji' =>
        -- Player refines to edge: need to case-split on opponent
        cases hRo : refineEdge jo (d i).1 (d i).2 (md i) with
        | vertex _ =>
          -- Opponent refines to vertex: refineLocalSigns gives (zero, zero)
          simp_all
        | edge jo' =>
          -- Both refine to edges: need IsNashPair of induced signs
          simp_all
          -- Now we need: IsNashPair of the induced signs
          -- This follows from refineEdge_localNash
          have key := refineEdge_localNash jo hNi hCohi
          rw [hRo] at key
          exact key

-- ================================================================
-- Section 7: Sign extraction from a game
-- ================================================================

/-- The sign of player i's preference between action 0 and action 1
    when the opponent plays `oppAction`.
    pos = strictly prefers 0, neg = strictly prefers 1, zero = indifferent. -/
noncomputable def prefSign (G : Game (Fin 2) (fun _ => Fin 2))
    (i : Fin 2) (oppAction : Fin 2) : Sign :=
  let p0 : PureProfile (Fin 2) (fun _ => Fin 2) :=
    Function.update (fun _ => oppAction) i 0
  let p1 : PureProfile (Fin 2) (fun _ => Fin 2) :=
    Function.update (fun _ => oppAction) i 1
  haveI := G.pref_decidable i
  if G.pref i p0 p1 then
    if G.pref i p1 p0 then Sign.zero else Sign.neg
  else Sign.pos

/-- Extract local sign data from a 2x2 game at a level-0 profile.
    For each player i:
    - If σ' i is a vertex: (zero, zero) (nothing to compare)
    - If σ' i is an edge: preference signs at the grid points of σ'(1-i) -/
noncomputable def signDataOf (G : Game (Fin 2) (fun _ => Fin 2))
    (σ' : ElemProfile1 0) : LocalSignData :=
  fun i =>
    match σ' i with
    | .vertex _ => (.zero, .zero)
    | .edge _ =>
      match σ' (1 - i) with
      | .vertex j => (prefSign G i j, prefSign G i j)
      | .edge _ => (prefSign G i 0, prefSign G i 1)

-- ================================================================
-- Section 8: Game-theoretic local Nash
-- ================================================================

/-- A profile σ' is locally Nash within ambient profile σ:
    no player i has a strict deviation from σ' to any subcell of σ i.
    This is the game-theoretic definition — it refers to the game's
    preference structure, not to sign data. -/
def Game.IsLocallyNash (G : Game (Fin 2) (fun _ => Fin 2))
    (σ' σ : ElemProfile1 0) : Prop :=
  ∀ i : Fin 2, ∀ A : ElemCell1 0, A.IsSubcell (σ i) →
    ¬G.StrictDev i (elemProfile1ZeroEquiv σ') (elemCell1ZeroEquiv A)

/-- When the ambient profile is maximal, local Nash = global Nash. -/
theorem Game.isLocallyNash_maximal_iff (G : Game (Fin 2) (fun _ => Fin 2))
    (σ' : ElemProfile1 0) :
    G.IsLocallyNash σ' maximalElemProfile1 ↔
      G.IsNash (elemProfile1ZeroEquiv σ') := by
  constructor
  · intro hLocal i A
    obtain ⟨B, rfl⟩ := elemCell1ZeroEquiv.surjective A
    apply hLocal i B
    intro q hq
    simp [maximalElemProfile1, ElemCell1.gridPoints]
    exact gridPoint0_cases q |>.elim
      (fun h => by simp [h]) (fun h => by simp [h])
  · intro hNash i A _
    exact hNash i (elemCell1ZeroEquiv A)

-- ================================================================
-- Section 9: Bridge — sign criterion characterizes Nash at the maximal profile
-- ================================================================

/-- prefSign encodes the pref relation: pos ↔ strictly prefers action 0. -/
private theorem prefSign_pos_iff (G : Game (Fin 2) (fun _ => Fin 2))
    (i : Fin 2) (a : Fin 2) :
    let p0 := Function.update (fun _ => a) i 0
    let p1 := Function.update (fun _ => a) i 1
    prefSign G i a = .pos ↔ ¬G.pref i p0 p1 := by
  simp only [prefSign]; haveI := G.pref_decidable i
  split_ifs <;> simp_all

private theorem prefSign_neg_iff (G : Game (Fin 2) (fun _ => Fin 2))
    (i : Fin 2) (a : Fin 2) :
    let p0 := Function.update (fun _ => a) i 0
    let p1 := Function.update (fun _ => a) i 1
    prefSign G i a = .neg ↔ G.pref i p0 p1 ∧ ¬G.pref i p1 p0 := by
  simp only [prefSign]; haveI := G.pref_decidable i
  split_ifs <;> simp_all

private theorem prefSign_zero_iff (G : Game (Fin 2) (fun _ => Fin 2))
    (i : Fin 2) (a : Fin 2) :
    let p0 := Function.update (fun _ => a) i 0
    let p1 := Function.update (fun _ => a) i 1
    prefSign G i a = .zero ↔ G.pref i p0 p1 ∧ G.pref i p1 p0 := by
  simp only [prefSign]; haveI := G.pref_decidable i
  split_ifs <;> simp_all

/-- At k=0 with both players on edges (the maximal profile),
    the sign criterion characterizes Nash. -/
theorem isNash_iff_isLocalNash_maximal (G : Game (Fin 2) (fun _ => Fin 2)) :
    G.IsNash (elemProfile1ZeroEquiv maximalElemProfile1) ↔
      IsLocalNash maximalElemProfile1 (signDataOf G maximalElemProfile1) := by
  sorry

end SyntheticGameTheory
