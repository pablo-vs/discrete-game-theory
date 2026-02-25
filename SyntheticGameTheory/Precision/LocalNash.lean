import SyntheticGameTheory.Precision.SignData

namespace SyntheticGameTheory

-- ================================================================
-- Section 1: IsLocalNash — local Nash refinement
-- ================================================================

/-- A cell profile σ' at level k+1 is a local Nash refinement of σ at level k
    under gps: σ' refines σ, and no player has a strict deviation within
    their parent cell's subcells. -/
def IsLocalNash (gps : GridPrefSystem (k + 1)) (σ : CellProfile1 k)
    (σ' : CellProfile1 (k + 1)) : Prop :=
  σ'.Refines σ ∧
  ∀ i : Fin 2, ∀ A ∈ (σ i).subcells, ¬CellStrictDev gps i σ' A

noncomputable instance IsLocalNash.instDecidable (gps : GridPrefSystem (k + 1))
    (σ : CellProfile1 k) (σ' : CellProfile1 (k + 1)) :
    Decidable (IsLocalNash gps σ σ') :=
  inferInstanceAs (Decidable (_ ∧ ∀ _, ∀ _ ∈ _, ¬_))

-- ================================================================
-- Section 2: CellIsNash implies local signs are Nash pairs
-- ================================================================

/-- Helper: at a single opponent grid point, CellIsNash on an edge forces
    both pref directions (indifference) between the edge endpoints. -/
private theorem edge_nash_forces_indiff_at (gps : GridPrefSystem k)
    (i : Fin 2) (ei : Fin (2 ^ k)) (q : GridPoint 1 k)
    -- CellDevLE conditions extracted from ¬CellStrictDev to vertex(lo) and vertex(hi)
    (hNoDevLo : ¬(gps.pref i (GridPoint.toIndex1 q) ⟨ei.val + 1, by omega⟩ ⟨ei.val, by omega⟩ ∧
      ¬gps.pref i (GridPoint.toIndex1 q) ⟨ei.val, by omega⟩ ⟨ei.val + 1, by omega⟩))
    (hNoDevHi : ¬(gps.pref i (GridPoint.toIndex1 q) ⟨ei.val, by omega⟩ ⟨ei.val + 1, by omega⟩ ∧
      ¬gps.pref i (GridPoint.toIndex1 q) ⟨ei.val + 1, by omega⟩ ⟨ei.val, by omega⟩)) :
    gps.pref i (GridPoint.toIndex1 q) ⟨ei.val, by omega⟩ ⟨ei.val + 1, by omega⟩ ∧
    gps.pref i (GridPoint.toIndex1 q) ⟨ei.val + 1, by omega⟩ ⟨ei.val, by omega⟩ := by
  push_neg at hNoDevLo hNoDevHi
  have htot1 := gps.pref_total i (GridPoint.toIndex1 q)
    ⟨ei.val, by omega⟩ ⟨ei.val + 1, by omega⟩
  have htot2 := gps.pref_total i (GridPoint.toIndex1 q)
    ⟨ei.val + 1, by omega⟩ ⟨ei.val, by omega⟩
  -- hNoDevLo : pref(hi,lo) → pref(lo,hi);  hNoDevHi : pref(lo,hi) → pref(hi,lo)
  exact htot1.elim (fun h => ⟨h, hNoDevHi h⟩) (fun h => ⟨hNoDevLo h, h⟩)

/-- If σ is CellIsNash, the local signs at σ form Nash pairs for each player. -/
theorem cellIsNash_implies_isNashPair (gps : GridPrefSystem k)
    (σ : CellProfile1 k) (hN : CellIsNash gps σ) (i : Fin 2) :
    IsNashPair (gps.localSignsAt σ i) := by
  simp only [GridPrefSystem.localSignsAt]
  match hσi : σ i, hσopp : σ (1 - i) with
  | .vertex _, _ =>
    right; right; rfl
  | .edge ei, .vertex j =>
    -- Local signs = (s, s) where s = signAt i j ei
    -- CellIsNash forces s = zero, giving (zero, zero)
    right; right
    suffices h : gps.signAt i j ei = .zero by simp [h]
    rw [GridPrefSystem.signAt_zero_iff]
    -- No strict dev to vertex(lo) or vertex(hi) from edge ei
    set lo : Fin (2 ^ k + 1) := ⟨ei.val, by omega⟩
    set hi : Fin (2 ^ k + 1) := ⟨ei.val + 1, by omega⟩
    have hNoLo := hN i (.vertex lo)
    have hNoHi := hN i (.vertex hi)
    simp only [CellStrictDev, hσi] at hNoLo hNoHi
    -- Apply helper at the single opponent grid point
    apply edge_nash_forces_indiff_at gps i ei (ElemCell1.gridPt j)
    · -- ¬(pref(hi, lo) ∧ ¬pref(lo, hi))
      intro ⟨hHL, hNotLH⟩
      apply hNoLo
      constructor
      · -- CellDevLE(edge ei, vertex lo)
        intro q hq a ha b hb
        simp [hσopp, ElemCell1.gridPoints_vertex, Finset.mem_singleton] at hq
        subst hq
        simp [ElemCell1.gridPoints] at ha hb; subst hb
        rcases ha with rfl | rfl <;>
          simp [ElemCell1.gridPt, GridPoint.toIndex1, GridPoint.ofIndex1]
        · exact gps.pref_refl _ _ _
        · exact hHL
      · -- ¬CellDevLE(vertex lo, edge ei)
        intro hContra
        apply hNotLH
        have := hContra (ElemCell1.gridPt j)
          (by simp [hσopp, ElemCell1.gridPoints_vertex])
          (ElemCell1.gridPt lo) (by simp) (ElemCell1.gridPt hi)
          (by simp [ElemCell1.gridPoints]; right; rfl)
        simpa [ElemCell1.gridPt, GridPoint.toIndex1, GridPoint.ofIndex1] using this
    · -- ¬(pref(lo, hi) ∧ ¬pref(hi, lo))
      intro ⟨hLH, hNotHL⟩
      apply hNoHi
      constructor
      · -- CellDevLE(edge ei, vertex hi)
        intro q hq a ha b hb
        simp [hσopp, ElemCell1.gridPoints_vertex, Finset.mem_singleton] at hq
        subst hq
        simp [ElemCell1.gridPoints] at ha hb; subst hb
        rcases ha with rfl | rfl <;>
          simp [ElemCell1.gridPt, GridPoint.toIndex1, GridPoint.ofIndex1]
        · exact hLH
        · exact gps.pref_refl _ _ _
      · -- ¬CellDevLE(vertex hi, edge ei)
        intro hContra
        apply hNotHL
        have := hContra (ElemCell1.gridPt j)
          (by simp [hσopp, ElemCell1.gridPoints_vertex])
          (ElemCell1.gridPt hi) (by simp) (ElemCell1.gridPt lo)
          (by simp [ElemCell1.gridPoints]; left; rfl)
        simpa [ElemCell1.gridPt, GridPoint.toIndex1, GridPoint.ofIndex1] using this
  | .edge ei, .edge ej =>
    -- Local signs = (signAt i jl ei, signAt i jr ei)
    set lo : Fin (2 ^ k + 1) := ⟨ei.val, by omega⟩
    set hi : Fin (2 ^ k + 1) := ⟨ei.val + 1, by omega⟩
    set jl : Fin (2 ^ k + 1) := ⟨ej.val, by omega⟩
    set jr : Fin (2 ^ k + 1) := ⟨ej.val + 1, by omega⟩
    set sl := gps.signAt i jl ei
    set sr := gps.signAt i jr ei
    -- Extract ¬CellStrictDev to vertex(lo) and vertex(hi)
    have hNoLo := hN i (.vertex lo)
    have hNoHi := hN i (.vertex hi)
    simp only [CellStrictDev, hσi] at hNoLo hNoHi
    -- push_neg gives implications
    push_neg at hNoLo hNoHi
    -- (A): CellDevLE(edge, vtx lo) → CellDevLE(vtx lo, edge)
    -- (B): CellDevLE(edge, vtx hi) → CellDevLE(vtx hi, edge)
    -- Now case split on sl to determine sr
    show IsNashPair (sl, sr)
    -- Key lemma: from ¬StrictDev to vertex(lo) and vertex(hi),
    -- derive: pref_q(hi,lo) at all opp points → pref_q(lo,hi) at all opp points (and vice versa)
    -- Then specialize at jl and jr to get sign pair conditions
    -- Step 1: extract the two implications from hNoLo, hNoHi
    -- ¬StrictDev(lo) = CellDevLE(edge,vtx lo) → CellDevLE(vtx lo, edge)
    -- Specialize at opponent grid points jl and jr
    have hjl_mem : ElemCell1.gridPt jl ∈ (σ (1 - i)).gridPoints := by
      rw [hσopp]; simp [ElemCell1.gridPoints]; left; rfl
    have hjr_mem : ElemCell1.gridPt jr ∈ (σ (1 - i)).gridPoints := by
      rw [hσopp]; simp [ElemCell1.gridPoints]; right; rfl
    -- Key reduction: from hNoLo, if pref(hi,lo) at BOTH opp points, get pref(lo,hi) at BOTH
    have key_lo : gps.pref i jl hi lo → gps.pref i jr hi lo →
        gps.pref i jl lo hi ∧ gps.pref i jr lo hi := by
      intro hjl_hl hjr_hl
      have hDevFwd : CellDevLE gps i σ (.edge ei) (.vertex lo) := by
        intro q hq a ha b hb
        simp [ElemCell1.gridPoints] at ha hb; subst hb
        rw [hσopp] at hq; simp [ElemCell1.gridPoints] at hq
        rcases ha with rfl | rfl <;>
          simp [ElemCell1.gridPt, GridPoint.toIndex1, GridPoint.ofIndex1] <;>
          rcases hq with rfl | rfl <;>
          simp [ElemCell1.gridPt, GridPoint.ofIndex1]
        · exact gps.pref_refl _ _ _
        · exact gps.pref_refl _ _ _
        · exact hjl_hl
        · exact hjr_hl
      have hDevBwd := hNoLo hDevFwd
      constructor
      · have := hDevBwd (ElemCell1.gridPt jl) hjl_mem (ElemCell1.gridPt lo) (by simp)
            (ElemCell1.gridPt hi) (by simp [ElemCell1.gridPoints]; right; rfl)
        simpa [ElemCell1.gridPt, GridPoint.toIndex1, GridPoint.ofIndex1] using this
      · have := hDevBwd (ElemCell1.gridPt jr) hjr_mem (ElemCell1.gridPt lo) (by simp)
            (ElemCell1.gridPt hi) (by simp [ElemCell1.gridPoints]; right; rfl)
        simpa [ElemCell1.gridPt, GridPoint.toIndex1, GridPoint.ofIndex1] using this
    have key_hi : gps.pref i jl lo hi → gps.pref i jr lo hi →
        gps.pref i jl hi lo ∧ gps.pref i jr hi lo := by
      intro hjl_lh hjr_lh
      have hDevFwd : CellDevLE gps i σ (.edge ei) (.vertex hi) := by
        intro q hq a ha b hb
        simp [ElemCell1.gridPoints] at ha hb; subst hb
        rw [hσopp] at hq; simp [ElemCell1.gridPoints] at hq
        rcases ha with rfl | rfl <;>
          simp [ElemCell1.gridPt, GridPoint.toIndex1, GridPoint.ofIndex1] <;>
          rcases hq with rfl | rfl <;>
          simp [ElemCell1.gridPt, GridPoint.ofIndex1]
        · exact hjl_lh
        · exact hjr_lh
        · exact gps.pref_refl _ _ _
        · exact gps.pref_refl _ _ _
      have hDevBwd := hNoHi hDevFwd
      constructor
      · have := hDevBwd (ElemCell1.gridPt jl) hjl_mem (ElemCell1.gridPt hi) (by simp)
            (ElemCell1.gridPt lo) (by simp [ElemCell1.gridPoints]; left; rfl)
        simpa [ElemCell1.gridPt, GridPoint.toIndex1, GridPoint.ofIndex1] using this
      · have := hDevBwd (ElemCell1.gridPt jr) hjr_mem (ElemCell1.gridPt hi) (by simp)
            (ElemCell1.gridPt lo) (by simp [ElemCell1.gridPoints]; left; rfl)
        simpa [ElemCell1.gridPt, GridPoint.toIndex1, GridPoint.ofIndex1] using this
    -- Step 2: case split on sl to determine sr
    show IsNashPair (sl, sr)
    simp only [sl, sr]
    rcases hsl : gps.signAt i jl ei with _ | _ | _
    · -- sl = pos: ¬pref_jl(lo, hi), hence pref_jl(hi, lo) by totality
      rw [GridPrefSystem.signAt_pos_iff] at hsl
      have hjl_hl := (gps.pref_total i jl lo hi).resolve_left hsl
      -- key_lo: pref_jr(hi,lo) → pref_jl(lo,hi). But ¬pref_jl(lo,hi). So ¬pref_jr(hi,lo).
      have hjr_not_hl : ¬gps.pref i jr hi lo := fun h => hsl (key_lo hjl_hl h).1
      have hjr_lh : gps.pref i jr lo hi := (gps.pref_total i jr lo hi).resolve_right
        (fun h => absurd h hjr_not_hl)
      have hsr : gps.signAt i jr ei = .neg := by
        rw [GridPrefSystem.signAt_neg_iff]; exact ⟨hjr_lh, hjr_not_hl⟩
      left; rw [hsr]
    · -- sl = neg: pref_jl(lo,hi) ∧ ¬pref_jl(hi,lo)
      rw [GridPrefSystem.signAt_neg_iff] at hsl
      have hjr_not_lh : ¬gps.pref i jr lo hi := fun h => hsl.2 (key_hi hsl.1 h).1
      have hsr : gps.signAt i jr ei = .pos := by
        rw [GridPrefSystem.signAt_pos_iff]; exact hjr_not_lh
      right; left; rw [hsr]
    · -- sl = zero: pref_jl(lo,hi) ∧ pref_jl(hi,lo)
      rw [GridPrefSystem.signAt_zero_iff] at hsl
      have hsr : gps.signAt i jr ei = .zero := by
        rw [GridPrefSystem.signAt_zero_iff]
        exact (gps.pref_total i jr lo hi).elim
          (fun h => ⟨h, (key_hi hsl.1 h).2⟩)
          (fun h => let both := key_lo hsl.2 h; ⟨both.2, h⟩)
      right; right; rw [hsr]

-- ================================================================
-- Section 3: Interpolation at level k+1 for embedded edge endpoints
-- ================================================================

/-- At level k+1, the embedded endpoints of a level-k edge satisfy HasGridMid1. -/
theorem hasGridMid1_embedded_edge (ei : Fin (2 ^ k)) :
    HasGridMid1 (k + 1) (ElemCell1.embedIndex ⟨ei.val, by omega⟩ : Fin (2 ^ (k+1) + 1))
                         (ElemCell1.embedIndex ⟨ei.val + 1, by omega⟩) := by
  have h := ei.isLt
  refine ⟨⟨1, by omega⟩, by simp, by omega, ?_⟩
  left
  simp [ElemCell1.embedIndex]; omega

/-- The midpoint of the embedded endpoints is the midIndex. -/
theorem gridMid1_embedded_edge (ei : Fin (2 ^ k)) :
    gridMid1 (ElemCell1.embedIndex (⟨ei.val, by omega⟩ : Fin (2 ^ k + 1)))
             (ElemCell1.embedIndex ⟨ei.val + 1, by omega⟩) =
      ElemCell1.midIndex ei := by
  apply Fin.ext
  simp [gridMid1, ElemCell1.embedIndex, ElemCell1.midIndex]; omega

/-- Interpolation for player i's edge ei at any opponent grid point q:
    pref between the embedded endpoints implies pref through the midpoint. -/
theorem GridPrefSystem.interpolation_edge (gps' : GridPrefSystem (k + 1))
    (i : Fin 2) (q : Fin (2 ^ (k + 1) + 1)) (ei : Fin (2 ^ k)) :
    let lo := ElemCell1.embedIndex (⟨ei.val, by omega⟩ : Fin (2 ^ k + 1))
    let hi := ElemCell1.embedIndex (⟨ei.val + 1, by omega⟩ : Fin (2 ^ k + 1))
    let mid := ElemCell1.midIndex ei
    (gps'.pref i q lo hi → gps'.pref i q lo mid ∧ gps'.pref i q mid hi) ∧
    (gps'.pref i q hi lo → gps'.pref i q hi mid ∧ gps'.pref i q mid lo) := by
  intro lo hi mid
  have hmid := hasGridMid1_embedded_edge ei
  have hmid_eq := gridMid1_embedded_edge ei
  have result := gps'.interpolation i q lo hi hmid
  rw [hmid_eq] at result
  exact result

/-- Negative interpolation: ¬pref between embedded endpoints implies ¬pref through midpoint. -/
theorem GridPrefSystem.interpolation_neg_edge (gps' : GridPrefSystem (k + 1))
    (i : Fin 2) (q : Fin (2 ^ (k + 1) + 1)) (ei : Fin (2 ^ k)) :
    let lo := ElemCell1.embedIndex (⟨ei.val, by omega⟩ : Fin (2 ^ k + 1))
    let hi := ElemCell1.embedIndex (⟨ei.val + 1, by omega⟩ : Fin (2 ^ k + 1))
    let mid := ElemCell1.midIndex ei
    (¬gps'.pref i q lo hi → ¬gps'.pref i q lo mid ∧ ¬gps'.pref i q mid hi) ∧
    (¬gps'.pref i q hi lo → ¬gps'.pref i q hi mid ∧ ¬gps'.pref i q mid lo) := by
  intro lo hi mid
  have hmid := hasGridMid1_embedded_edge ei
  have hmid_eq := gridMid1_embedded_edge ei
  have result := gps'.interpolation_neg i q lo hi hmid
  rw [hmid_eq] at result
  exact result

-- ================================================================
-- Section 4: Forward direction — existence of local Nash refinement
-- ================================================================

-- Interpolation helper: HasGridMid1 for embLo_i and embHi_i at level k+1.
private theorem hasGridMid1_ee (ei : Fin (2 ^ k)) :
    HasGridMid1 (k + 1) (ElemCell1.embedIndex (⟨ei.val, by omega⟩ : Fin (2 ^ k + 1)))
                         (ElemCell1.embedIndex ⟨ei.val + 1, by omega⟩) := by
  have h := ei.isLt
  refine ⟨⟨1, by omega⟩, by simp, by omega, ?_⟩; left; simp [ElemCell1.embedIndex]; omega

private theorem gridMid1_ee (ei : Fin (2 ^ k)) :
    gridMid1 (ElemCell1.embedIndex (⟨ei.val, by omega⟩ : Fin (2 ^ k + 1)))
             (ElemCell1.embedIndex ⟨ei.val + 1, by omega⟩) = ElemCell1.midIndex ei := by
  apply Fin.ext; simp [gridMid1, ElemCell1.embedIndex, ElemCell1.midIndex]; omega

/-- midIndex ej is in every subcell of edge ej. -/
private theorem midIndex_in_all_subcells (ej : Fin (2 ^ k)) (c_opp : ElemCell1 (k + 1))
    (hc : c_opp ∈ (ElemCell1.edge ej).subcells) :
    ElemCell1.gridPt (ElemCell1.midIndex ej) ∈ c_opp.gridPoints := by
  have hej := ej.isLt
  simp [ElemCell1.subcells] at hc
  rcases hc with rfl | rfl | rfl
  · simp [ElemCell1.gridPoints, ElemCell1.gridPt]; right; rfl
  · simp [ElemCell1.gridPoints]
  · simp [ElemCell1.gridPoints, ElemCell1.gridPt]; left; rfl

/-- From a zero signAt at ⟨2*ei, _⟩ at any point q, derive ALL 6 prefs between
    embLo_i, mid_i, embHi_i at q. Key: uses interpolation between embLo and embHi. -/
private theorem zero_sign_all_prefs (gps' : GridPrefSystem (k + 1)) (i : Fin 2)
    (q : Fin (2 ^ (k + 1) + 1)) (ei : Fin (2 ^ k))
    (h_zero : gps'.signAt i q ⟨2 * ei.val, by omega⟩ = .zero) :
    let embLo := ElemCell1.embedIndex (⟨ei.val, by omega⟩ : Fin (2 ^ k + 1))
    let embHi := ElemCell1.embedIndex (⟨ei.val + 1, by omega⟩ : Fin (2 ^ k + 1))
    let mid := ElemCell1.midIndex ei
    gps'.pref i q embLo mid ∧ gps'.pref i q mid embLo ∧
    gps'.pref i q mid embHi ∧ gps'.pref i q embHi mid ∧
    gps'.pref i q embLo embHi ∧ gps'.pref i q embHi embLo := by
  intro embLo embHi mid
  have h := (gps'.signAt_zero_iff i q ⟨2 * ei.val, by omega⟩).mp h_zero
  have hei := ei.isLt
  have h1 : gps'.pref i q embLo mid := by convert h.1 using 2
  have h2 : gps'.pref i q mid embLo := by convert h.2 using 2
  have hmid := hasGridMid1_ee ei; have hmid_eq := gridMid1_ee ei
  have interp := gps'.interpolation i q embLo embHi hmid; rw [hmid_eq] at interp
  have interp_neg := gps'.interpolation_neg i q embLo embHi hmid; rw [hmid_eq] at interp_neg
  have h_lo_hi : gps'.pref i q embLo embHi := by by_contra h_not; exact (interp_neg.1 h_not).1 h1
  have h_hi_lo : gps'.pref i q embHi embLo := by by_contra h_not; exact (interp_neg.2 h_not).2 h2
  exact ⟨h1, h2, (interp.1 h_lo_hi).2, (interp.2 h_hi_lo).1, h_lo_hi, h_hi_lo⟩

/-- From a coarsen zero sign, derive all 6 prefs at the embedded opponent point. -/
private theorem coarsen_zero_all_prefs (gps' : GridPrefSystem (k + 1)) (i : Fin 2)
    (ei : Fin (2 ^ k)) (j : Fin (2 ^ k + 1))
    (hzero : gps'.coarsen.signAt i j ei = .zero) :
    let embJ := ElemCell1.embedIndex j
    let embLo := ElemCell1.embedIndex (⟨ei.val, by omega⟩ : Fin (2 ^ k + 1))
    let embHi := ElemCell1.embedIndex (⟨ei.val + 1, by omega⟩ : Fin (2 ^ k + 1))
    let mid := ElemCell1.midIndex ei
    gps'.pref i embJ embLo mid ∧ gps'.pref i embJ mid embLo ∧
    gps'.pref i embJ mid embHi ∧ gps'.pref i embJ embHi mid ∧
    gps'.pref i embJ embLo embHi ∧ gps'.pref i embJ embHi embLo := by
  intro embJ embLo embHi mid
  have h := (gps'.coarsen.signAt_zero_iff i j ei).mp hzero
  have h_lo_hi : gps'.pref i embJ embLo embHi := by
    show gps'.coarsen.pref i j ⟨ei.val, by omega⟩ ⟨ei.val + 1, by omega⟩; exact h.1
  have h_hi_lo : gps'.pref i embJ embHi embLo := by
    show gps'.coarsen.pref i j ⟨ei.val + 1, by omega⟩ ⟨ei.val, by omega⟩; exact h.2
  have hmid := hasGridMid1_ee ei; have hmid_eq := gridMid1_ee ei
  have interp := gps'.interpolation i embJ embLo embHi hmid; rw [hmid_eq] at interp
  exact ⟨(interp.1 h_lo_hi).1, (interp.2 h_hi_lo).2,
         (interp.1 h_lo_hi).2, (interp.2 h_hi_lo).1, h_lo_hi, h_hi_lo⟩

/-- From neg sign at ⟨2*ei, _⟩, derive ¬pref(embHi, mid) at the same point.
    Key: interpolation forces the second sign to also be neg. -/
private theorem neg_sign_not_pref_hi_mid (gps' : GridPrefSystem (k + 1)) (i : Fin 2)
    (q : Fin (2 ^ (k + 1) + 1)) (ei : Fin (2 ^ k))
    (h_neg : gps'.signAt i q ⟨2 * ei.val, by omega⟩ = .neg) :
    ¬gps'.pref i q (ElemCell1.embedIndex ⟨ei.val + 1, by omega⟩) (ElemCell1.midIndex ei) := by
  have hei := ei.isLt
  have h := (gps'.signAt_neg_iff i q ⟨2 * ei.val, by omega⟩).mp h_neg
  set embLo := ElemCell1.embedIndex (⟨ei.val, by omega⟩ : Fin (2 ^ k + 1))
  set embHi := ElemCell1.embedIndex (⟨ei.val + 1, by omega⟩ : Fin (2 ^ k + 1))
  set mid := ElemCell1.midIndex ei
  have h1 : gps'.pref i q embLo mid := by convert h.1 using 2
  have h2 : ¬gps'.pref i q mid embLo := by convert h.2 using 2
  have hmid := hasGridMid1_ee ei; have hmid_eq := gridMid1_ee ei
  have interp := gps'.interpolation i q embLo embHi hmid; rw [hmid_eq] at interp
  have interp_neg := gps'.interpolation_neg i q embLo embHi hmid; rw [hmid_eq] at interp_neg
  intro h_hi_mid
  rcases gps'.pref_total i q embHi embLo with h_ge | h_le
  · exact h2 (interp.2 h_ge).2
  · exact h_hi_mid |> fun hp => absurd hp (interp_neg.2 (by
      intro h_contra; exact h2 (interp.2 h_contra).2)).1

/-- From pos sign at ⟨2*ei, _⟩ at any point q, derive full ordering: hi > mid > lo.
    Specifically: ¬pref(lo,mid), ¬pref(mid,hi), ¬pref(lo,hi), plus their reverses by totality. -/
private theorem pos_sign_full_neg_prefs (gps' : GridPrefSystem (k + 1)) (i : Fin 2)
    (q : Fin (2 ^ (k + 1) + 1)) (ei : Fin (2 ^ k))
    (h_pos : gps'.signAt i q ⟨2 * ei.val, by omega⟩ = .pos) :
    let embLo := ElemCell1.embedIndex (⟨ei.val, by omega⟩ : Fin (2 ^ k + 1))
    let embHi := ElemCell1.embedIndex (⟨ei.val + 1, by omega⟩ : Fin (2 ^ k + 1))
    let mid := ElemCell1.midIndex ei
    ¬gps'.pref i q embLo mid ∧ ¬gps'.pref i q mid embHi ∧ ¬gps'.pref i q embLo embHi := by
  intro embLo embHi mid
  have hei := ei.isLt
  have h := (gps'.signAt_pos_iff i q ⟨2 * ei.val, by omega⟩).mp h_pos
  have h_not_lo_mid : ¬gps'.pref i q embLo mid := by convert h using 2
  have hmid := hasGridMid1_ee ei; have hmid_eq := gridMid1_ee ei
  have interp_neg := gps'.interpolation_neg i q embLo embHi hmid
  rw [hmid_eq] at interp_neg
  have interp := gps'.interpolation i q embLo embHi hmid
  rw [hmid_eq] at interp
  have h_not_lo_hi : ¬gps'.pref i q embLo embHi := by
    intro hp; exact h_not_lo_mid (interp.1 hp).1
  have h_not_mid_hi : ¬gps'.pref i q mid embHi := (interp_neg.1 h_not_lo_hi).2
  exact ⟨h_not_lo_mid, h_not_mid_hi, h_not_lo_hi⟩

/-- From neg sign at ⟨2*ei, _⟩ at any point q, derive full ordering: lo > mid > hi.
    Specifically: ¬pref(mid,lo), ¬pref(hi,mid), ¬pref(hi,lo), plus their reverses by totality. -/
private theorem neg_sign_full_neg_prefs (gps' : GridPrefSystem (k + 1)) (i : Fin 2)
    (q : Fin (2 ^ (k + 1) + 1)) (ei : Fin (2 ^ k))
    (h_neg : gps'.signAt i q ⟨2 * ei.val, by omega⟩ = .neg) :
    let embLo := ElemCell1.embedIndex (⟨ei.val, by omega⟩ : Fin (2 ^ k + 1))
    let embHi := ElemCell1.embedIndex (⟨ei.val + 1, by omega⟩ : Fin (2 ^ k + 1))
    let mid := ElemCell1.midIndex ei
    ¬gps'.pref i q mid embLo ∧ ¬gps'.pref i q embHi mid ∧ ¬gps'.pref i q embHi embLo := by
  intro embLo embHi mid
  have hei := ei.isLt
  have h := (gps'.signAt_neg_iff i q ⟨2 * ei.val, by omega⟩).mp h_neg
  have h_not_mid_lo : ¬gps'.pref i q mid embLo := by convert h.2 using 2
  have h_not_hi_mid := neg_sign_not_pref_hi_mid gps' i q ei h_neg
  have hmid := hasGridMid1_ee ei; have hmid_eq := gridMid1_ee ei
  have interp_neg := gps'.interpolation_neg i q embLo embHi hmid
  rw [hmid_eq] at interp_neg
  have interp := gps'.interpolation i q embLo embHi hmid
  rw [hmid_eq] at interp
  have h_not_hi_lo : ¬gps'.pref i q embHi embLo := by
    intro hp; exact h_not_mid_lo (interp.2 hp).2
  exact ⟨h_not_mid_lo, h_not_hi_mid, h_not_hi_lo⟩

/-- From coarsen pos sign, derive ¬pref at the embedded point: ¬pref(lo,mid), ¬pref(mid,hi), ¬pref(lo,hi). -/
private theorem coarsen_pos_full_neg_prefs (gps' : GridPrefSystem (k + 1)) (i : Fin 2)
    (j : Fin (2 ^ k + 1)) (ei : Fin (2 ^ k))
    (h_pos : gps'.coarsen.signAt i j ei = .pos) :
    let embJ := ElemCell1.embedIndex j
    let embLo := ElemCell1.embedIndex (⟨ei.val, by omega⟩ : Fin (2 ^ k + 1))
    let embHi := ElemCell1.embedIndex (⟨ei.val + 1, by omega⟩ : Fin (2 ^ k + 1))
    let mid := ElemCell1.midIndex ei
    ¬gps'.pref i embJ embLo mid ∧ ¬gps'.pref i embJ mid embHi ∧ ¬gps'.pref i embJ embLo embHi := by
  intro embJ embLo embHi mid
  have hei := ei.isLt
  have h_not_lo_hi : ¬gps'.pref i embJ embLo embHi :=
    (gps'.coarsen.signAt_pos_iff i j ei).mp h_pos
  have hmid := hasGridMid1_ee ei; have hmid_eq := gridMid1_ee ei
  have interp_neg := gps'.interpolation_neg i embJ embLo embHi hmid
  rw [hmid_eq] at interp_neg
  exact ⟨(interp_neg.1 h_not_lo_hi).1, (interp_neg.1 h_not_lo_hi).2, h_not_lo_hi⟩

/-- From coarsen neg sign, derive ¬pref at the embedded point: ¬pref(mid,lo), ¬pref(hi,mid), ¬pref(hi,lo). -/
private theorem coarsen_neg_full_neg_prefs (gps' : GridPrefSystem (k + 1)) (i : Fin 2)
    (j : Fin (2 ^ k + 1)) (ei : Fin (2 ^ k))
    (h_neg : gps'.coarsen.signAt i j ei = .neg) :
    let embJ := ElemCell1.embedIndex j
    let embLo := ElemCell1.embedIndex (⟨ei.val, by omega⟩ : Fin (2 ^ k + 1))
    let embHi := ElemCell1.embedIndex (⟨ei.val + 1, by omega⟩ : Fin (2 ^ k + 1))
    let mid := ElemCell1.midIndex ei
    ¬gps'.pref i embJ mid embLo ∧ ¬gps'.pref i embJ embHi mid ∧ ¬gps'.pref i embJ embHi embLo := by
  intro embJ embLo embHi mid
  have hei := ei.isLt
  have h := (gps'.coarsen.signAt_neg_iff i j ei).mp h_neg
  have h_not_hi_lo : ¬gps'.pref i embJ embHi embLo := by
    intro hp
    exact h.2 (show gps'.coarsen.pref i j ⟨ei.val + 1, by omega⟩ ⟨ei.val, by omega⟩ from hp)
  have hmid := hasGridMid1_ee ei; have hmid_eq := gridMid1_ee ei
  have interp_neg := gps'.interpolation_neg i embJ embLo embHi hmid
  rw [hmid_eq] at interp_neg
  exact ⟨(interp_neg.2 h_not_hi_lo).2, (interp_neg.2 h_not_hi_lo).1, h_not_hi_lo⟩

/-- Convert a sign to a subcell of an edge: pos → left, neg → right, zero → mid vertex. -/
private def cellFromSign (ei : Fin (2 ^ k)) (s : Sign) : ElemCell1 (k + 1) :=
  have hei := ei.isLt
  match s with
  | .pos => ElemCell1.edge ⟨2 * ei.val, by omega⟩
  | .neg => ElemCell1.edge ⟨2 * ei.val + 1, by omega⟩
  | .zero => ElemCell1.vertex (ElemCell1.midIndex ei)

private theorem cellFromSign_mem_subcells (ei : Fin (2 ^ k)) (s : Sign) :
    cellFromSign ei s ∈ (ElemCell1.edge ei).subcells := by
  simp [cellFromSign, ElemCell1.subcells]; have hei := ei.isLt
  cases s <;> simp [ElemCell1.midIndex]

/-- The coupled local Nash refinement construction.
    For edge-edge: player i's cell depends on both players' midpoint signs.
    - mi ≠ zero: use cellFromSign(mi) — safe at mid_{1-i} (in every opp subcell)
    - mi = zero, mj ≠ zero: use cellFromSign(coarsen sign at non-mid point of opp's cell)
    - mi = zero, mj = zero: use mid_vtx (full indifference at the single opp point) -/
private noncomputable def localNashCell (gps' : GridPrefSystem (k + 1))
    (i : Fin 2) (ei ej : Fin (2 ^ k)) : ElemCell1 (k + 1) :=
  have hei := ei.isLt; have hej := ej.isLt
  let mi := gps'.signAt i (ElemCell1.midIndex ej) ⟨2 * ei.val, by omega⟩
  let mj := gps'.signAt (1 - i) (ElemCell1.midIndex ei) ⟨2 * ej.val, by omega⟩
  match mi with
  | .pos => cellFromSign ei .pos
  | .neg => cellFromSign ei .neg
  | .zero => match mj with
    | .pos => -- opponent chose left. Non-mid point = embLo_j.
      -- Use coarsen sign at embLo_j for player i.
      cellFromSign ei (gps'.coarsen.signAt i ⟨ej.val, by omega⟩ ei)
    | .neg => -- opponent chose right. Non-mid point = embHi_j.
      cellFromSign ei (gps'.coarsen.signAt i ⟨ej.val + 1, by omega⟩ ei)
    | .zero => cellFromSign ei .zero

private theorem localNashCell_mem_subcells (gps' : GridPrefSystem (k + 1))
    (i : Fin 2) (ei ej : Fin (2 ^ k)) :
    localNashCell gps' i ei ej ∈ (ElemCell1.edge ei).subcells := by
  simp only [localNashCell]; split <;> (try split) <;> exact cellFromSign_mem_subcells _ _

/-- Helper: Fin 2 subtraction identity -/
private theorem fin2_one_sub_one_sub (i : Fin 2) : (1 : Fin 2) - (1 - i) = i := by omega

/-- Main theorem: local Nash refinement exists. -/
theorem exists_localNashRefinement (gps' : GridPrefSystem (k + 1))
    (σ : CellProfile1 k) (hN : CellIsNash gps'.coarsen σ) :
    ∃ σ' : CellProfile1 (k + 1), IsLocalNash gps' σ σ' := by
  -- Construct σ' by choosing a safe subcell for each player
  let σ' : CellProfile1 (k + 1) := fun i =>
    match σ i, σ (1 - i) with
    | .vertex j, _ => ElemCell1.vertex (ElemCell1.embedIndex j)
    | .edge ei, .vertex _ => ElemCell1.vertex (ElemCell1.midIndex ei)
    | .edge ei, .edge ej => localNashCell gps' i ei ej
  refine ⟨σ', ?_, ?_⟩
  · -- σ' refines σ
    intro i
    show (match σ i, σ (1-i) with | .vertex j, _ => _ | .edge ei, .vertex _ => _ | .edge ei, .edge ej => _) ∈ _
    match hσi : σ i, σ (1-i) with
    | .vertex j, _ => simp [ElemCell1.subcells]
    | .edge ei, .vertex _ => simp [ElemCell1.subcells, ElemCell1.midIndex]
    | .edge ei, .edge ej => exact localNashCell_mem_subcells gps' i _ _
  · -- No strict deviations
    intro i B hBsub
    -- Simplify σ' i and σ' (1-i)
    -- σ' i = match σ i, σ (1-i) with ...
    -- σ' (1-i) = match σ (1-i), σ (1-(1-i)) = match σ (1-i), σ i with ...
    have hσ'i_eq : σ' i = match σ i, σ (1 - i) with
        | .vertex j, _ => ElemCell1.vertex (ElemCell1.embedIndex j)
        | .edge ei, .vertex _ => ElemCell1.vertex (ElemCell1.midIndex ei)
        | .edge ei, .edge ej => localNashCell gps' i ei ej := rfl
    have hσ'opp_eq : σ' (1 - i) = match σ (1 - i), σ i with
        | .vertex j, _ => ElemCell1.vertex (ElemCell1.embedIndex j)
        | .edge ej, .vertex _ => ElemCell1.vertex (ElemCell1.midIndex ej)
        | .edge ej, .edge ei => localNashCell gps' (1 - i) ej ei := by
      show (match σ (1 - i), σ (1 - (1 - i)) with | .vertex j, _ => _ | .edge ei, .vertex _ => _ | .edge ei, .edge ej => _) = _
      rw [fin2_one_sub_one_sub]
    -- Case split on σ i and σ (1-i)
    match hσi : σ i, hσopp : σ (1 - i) with
    | .vertex j, _ =>
      -- σ' i = vertex(embedIndex j). subcells = [vertex(embedIndex j)].
      -- B must be the same cell → CellStrictDev contradicts itself.
      rw [hσi] at hBsub; simp [ElemCell1.subcells] at hBsub; subst hBsub
      simp only [CellStrictDev, hσ'i_eq, hσi]
      -- Goal: ¬(CellDevLE(vtx(embJ), vtx(embJ)) ∧ ¬CellDevLE(vtx(embJ), vtx(embJ)))
      exact fun ⟨_, h⟩ => h (fun q hq a ha b hb => by
        simp [ElemCell1.gridPoints] at ha hb; subst ha; subst hb; exact gps'.pref_refl _ _ _)
    | .edge ei, .vertex j =>
      -- σ' i = mid_vtx, σ' (1-i) = vertex(embedIndex j)
      -- CellIsNash of coarsen forces zero sign at embedded j for player i
      have hzero_coarsen : gps'.coarsen.signAt i j ei = .zero := by
        rw [GridPrefSystem.signAt_zero_iff]
        have hNoLo := hN i (.vertex ⟨ei.val, by omega⟩)
        have hNoHi := hN i (.vertex ⟨ei.val + 1, by omega⟩)
        simp only [CellStrictDev, hσi] at hNoLo hNoHi
        apply edge_nash_forces_indiff_at _ i ei (ElemCell1.gridPt j)
        · intro ⟨hHL, hNotLH⟩; apply hNoLo; constructor
          · intro q hq a ha b hb; rw [hσopp] at hq
            simp [ElemCell1.gridPoints] at ha hb hq; subst hq; subst hb
            rcases ha with rfl | rfl <;>
              simp [ElemCell1.gridPt, GridPoint.toIndex1, GridPoint.ofIndex1]
            · exact gps'.pref_refl _ _ _
            · exact hHL
          · intro hC; apply hNotLH
            have := hC (ElemCell1.gridPt j) (by rw [hσopp]; simp [ElemCell1.gridPoints])
              (ElemCell1.gridPt ⟨ei.val, by omega⟩) (by simp)
              (ElemCell1.gridPt ⟨ei.val + 1, by omega⟩) (by simp [ElemCell1.gridPoints])
            simpa [ElemCell1.gridPt, GridPoint.toIndex1, GridPoint.ofIndex1] using this
        · intro ⟨hLH, hNotHL⟩; apply hNoHi; constructor
          · intro q hq a ha b hb; rw [hσopp] at hq
            simp [ElemCell1.gridPoints] at ha hb hq; subst hq; subst hb
            rcases ha with rfl | rfl <;>
              simp [ElemCell1.gridPt, GridPoint.toIndex1, GridPoint.ofIndex1]
            · exact hLH
            · exact gps'.pref_refl _ _ _
          · intro hC; apply hNotHL
            have := hC (ElemCell1.gridPt j) (by rw [hσopp]; simp [ElemCell1.gridPoints])
              (ElemCell1.gridPt ⟨ei.val + 1, by omega⟩) (by simp)
              (ElemCell1.gridPt ⟨ei.val, by omega⟩) (by simp [ElemCell1.gridPoints])
            simpa [ElemCell1.gridPt, GridPoint.toIndex1, GridPoint.ofIndex1] using this
      -- Now use coarsen zero to get all prefs at the single opponent point
      have hall := coarsen_zero_all_prefs gps' i ei j hzero_coarsen
      -- σ' i = mid_vtx, σ' (1-i) = vertex(embedIndex j)
      simp only [CellStrictDev, CellDevLE, hσ'i_eq, hσi, hσopp, hσ'opp_eq]
      -- CellStrictDev = CellDevLE(mid_vtx, B) ∧ ¬CellDevLE(B, mid_vtx)
      -- Show CellDevLE(B, mid_vtx) holds (second conjunct false)
      intro ⟨_, hBwd⟩; apply hBwd
      intro q hq a ha b hb
      simp [ElemCell1.gridPoints_vertex, Finset.mem_singleton] at hq; subst hq
      simp [ElemCell1.gridPoints] at hb; subst hb
      -- a ∈ B.gridPoints, B ∈ subcells(edge ei)
      rw [hσi] at hBsub
      simp [ElemCell1.subcells] at hBsub
      rcases hBsub with rfl | rfl | rfl <;>
        simp [ElemCell1.gridPoints] at ha <;>
        (try rcases ha with rfl | rfl) <;>
        simp [ElemCell1.gridPt, GridPoint.toIndex1, GridPoint.ofIndex1,
          ElemCell1.midIndex]
      all_goals first
        | exact gps'.pref_refl _ _ _
        | exact hall.1 | exact hall.2.1 | exact hall.2.2.1 | exact hall.2.2.2.1
    | .edge ei, .edge ej =>
      -- The main case: both players on edges
      have hei := ei.isLt; have hej := ej.isLt
      -- Extract sign data
      set mi := gps'.signAt i (ElemCell1.midIndex ej) ⟨2 * ei.val, by omega⟩
      set mj := gps'.signAt (1 - i) (ElemCell1.midIndex ei) ⟨2 * ej.val, by omega⟩
      -- σ' i = localNashCell gps' i ei ej, σ' (1-i) = localNashCell gps' (1-i) ej ei
      have hσ'i : σ' i = localNashCell gps' i ei ej := by rw [hσ'i_eq, hσi, hσopp]
      have hσ'opp : σ' (1 - i) = localNashCell gps' (1 - i) ej ei := by rw [hσ'opp_eq, hσopp, hσi]
      -- B ∈ subcells of σ i = edge ei
      rw [hσi] at hBsub
      -- Unfold CellStrictDev with explicit σ' i and σ' (1-i)
      simp only [CellStrictDev, CellDevLE, hσ'i, hσ'opp]
      -- KEY: mid_j ∈ every subcell of edge ej, so mid_j ∈ (localNashCell (1-i) ej ei).gridPoints
      have hmid_j_mem : ElemCell1.gridPt (ElemCell1.midIndex ej) ∈
          (localNashCell gps' (1 - i) ej ei).gridPoints :=
        midIndex_in_all_subcells ej _ (localNashCell_mem_subcells gps' (1 - i) ej ei)
      -- Similarly, mid_i ∈ every subcell of edge ei
      have hmid_i_mem : ElemCell1.gridPt (ElemCell1.midIndex ei) ∈
          (localNashCell gps' i ei ej).gridPoints :=
        midIndex_in_all_subcells ei _ (localNashCell_mem_subcells gps' i ei ej)
      -- Case split on mi
      rcases hmi : mi with _ | _ | _
      · -- mi = pos: localNashCell i ei ej = cellFromSign ei .pos = left edge
        have hcell_i : localNashCell gps' i ei ej = cellFromSign ei .pos := by
          simp only [localNashCell, mi, hmi]
        intro ⟨hFwd, hBwd⟩
        rw [hcell_i] at hFwd hBwd
        have h_pos_at_mid := pos_sign_full_neg_prefs gps' i (ElemCell1.midIndex ej) ei hmi
        simp [ElemCell1.subcells] at hBsub
        rcases hBsub with rfl | rfl | rfl
        · -- B = left = A: CellDevLE(A,A) ∧ ¬CellDevLE(A,A) → contradiction
          exact hBwd hFwd
        · -- B = mid_vtx: CellDevLE(left, mid_vtx) needs pref(embLo, mid) at mid_j → fails
          exact h_pos_at_mid.1 (by
            simp only [cellFromSign] at hFwd
            have := hFwd _ hmid_j_mem (ElemCell1.gridPt ⟨2 * ei.val, by omega⟩)
              (by simp [ElemCell1.gridPoints]) (ElemCell1.gridPt (ElemCell1.midIndex ei))
              (by simp [ElemCell1.gridPoints])
            simpa [ElemCell1.gridPt, GridPoint.toIndex1, GridPoint.ofIndex1,
              ElemCell1.embedIndex, ElemCell1.midIndex] using this)
        · -- B = right: CellDevLE(left, right) needs pref(embLo, embHi) at mid_j → fails
          exact h_pos_at_mid.2.2 (by
            simp only [cellFromSign] at hFwd
            have := hFwd _ hmid_j_mem (ElemCell1.gridPt ⟨2 * ei.val, by omega⟩)
              (by simp [ElemCell1.gridPoints]) (ElemCell1.gridPt ⟨2 * ei.val + 2, by omega⟩)
              (by simp [ElemCell1.gridPoints])
            simpa [ElemCell1.gridPt, GridPoint.toIndex1, GridPoint.ofIndex1,
              ElemCell1.embedIndex] using this)
      · -- mi = neg: localNashCell i ei ej = cellFromSign ei .neg = right edge
        have hcell_i : localNashCell gps' i ei ej = cellFromSign ei .neg := by
          simp only [localNashCell, mi, hmi]
        intro ⟨hFwd, hBwd⟩
        rw [hcell_i] at hFwd hBwd
        have h_neg_at_mid := neg_sign_full_neg_prefs gps' i (ElemCell1.midIndex ej) ei hmi
        simp [ElemCell1.subcells] at hBsub
        rcases hBsub with rfl | rfl | rfl
        · -- B = left: CellDevLE(right, left) needs pref(mid, embLo) at mid_j → fails
          exact h_neg_at_mid.1 (by
            simp only [cellFromSign] at hFwd
            have := hFwd _ hmid_j_mem (ElemCell1.gridPt (ElemCell1.midIndex ei))
              (by simp [ElemCell1.gridPoints, ElemCell1.midIndex])
              (ElemCell1.gridPt ⟨2 * ei.val, by omega⟩)
              (by simp [ElemCell1.gridPoints])
            simpa [ElemCell1.gridPt, GridPoint.toIndex1, GridPoint.ofIndex1,
              ElemCell1.embedIndex, ElemCell1.midIndex] using this)
        · -- B = mid_vtx: CellDevLE(right, mid_vtx) needs pref(embHi, mid) at mid_j → fails
          exact h_neg_at_mid.2.1 (by
            simp only [cellFromSign] at hFwd
            have := hFwd _ hmid_j_mem (ElemCell1.gridPt ⟨2 * ei.val + 2, by omega⟩)
              (by simp [ElemCell1.gridPoints])
              (ElemCell1.gridPt (ElemCell1.midIndex ei)) (by simp [ElemCell1.gridPoints, ElemCell1.midIndex])
            simpa [ElemCell1.gridPt, GridPoint.toIndex1, GridPoint.ofIndex1,
              ElemCell1.embedIndex, ElemCell1.midIndex] using this)
        · -- B = right = A: contradiction
          exact hBwd hFwd
      · -- mi = zero: localNashCell depends on mj
        rcases hmj : mj with _ | _ | _
        · -- mi = zero, mj = pos: opponent chose left, use coarsen sign at embLo_j
          have hcell_i : localNashCell gps' i ei ej =
              cellFromSign ei (gps'.coarsen.signAt i ⟨ej.val, by omega⟩ ei) := by
            simp only [localNashCell, mi, hmi, mj, hmj]
          -- Opponent cell: localNashCell (1-i) ej ei
          -- mj = pos → opponent's mi is signAt (1-i) (midIndex ei) ⟨2*ej, _⟩ = pos
          -- So localNashCell (1-i) ej ei = cellFromSign ej .pos = left_j
          have hcell_opp : localNashCell gps' (1 - i) ej ei = cellFromSign ej .pos := by
            simp only [localNashCell, mj, hmj]
          -- Opponent's gridPoints = left_j.gp = {embLo_j, mid_j}
          -- At mid_j: mi=zero → all prefs → CellDevLE holds both ways → blocks strict dev
          -- At embLo_j: coarsen sign determines player i's cell
          intro ⟨hFwd, hBwd⟩
          -- Strategy: show CellDevLE(B, σ'(i)) holds, so hBwd fails
          -- OR: show CellDevLE(σ'(i), B) fails
          -- Approach: if sign at embLo_j is zero, all prefs → CellDevLE(B, σ'(i)) → ¬hBwd
          -- If sign at embLo_j is non-zero, blocking at embLo_j → CellDevLE(σ'(i), B) fails for B ≠ σ'(i)
          set cs := gps'.coarsen.signAt i ⟨ej.val, by omega⟩ ei
          rcases hcs : cs with _ | _ | _
          · -- cs = pos: σ'(i) = left_i. Block at embLo_j.
            have h_pos := coarsen_pos_full_neg_prefs gps' i ⟨ej.val, by omega⟩ ei hcs
            have embLo_j_mem : ElemCell1.gridPt (ElemCell1.embedIndex ⟨ej.val, by omega⟩) ∈
                (localNashCell gps' (1 - i) ej ei).gridPoints := by
              rw [hcell_opp]; simp [cellFromSign, ElemCell1.gridPoints, ElemCell1.embedIndex]
            rw [hcell_i, hcs] at hFwd hBwd
            simp [ElemCell1.subcells] at hBsub
            rcases hBsub with rfl | rfl | rfl
            · exact hBwd hFwd
            · exact h_pos.1 (by
                simp only [cellFromSign] at hFwd
                have := hFwd _ embLo_j_mem (ElemCell1.gridPt ⟨2 * ei.val, by omega⟩)
                  (by simp [ElemCell1.gridPoints]) (ElemCell1.gridPt (ElemCell1.midIndex ei))
                  (by simp [ElemCell1.gridPoints])
                simpa [ElemCell1.gridPt, GridPoint.toIndex1, GridPoint.ofIndex1,
                  ElemCell1.embedIndex, ElemCell1.midIndex] using this)
            · exact h_pos.2.2 (by
                simp only [cellFromSign] at hFwd
                have := hFwd _ embLo_j_mem (ElemCell1.gridPt ⟨2 * ei.val, by omega⟩)
                  (by simp [ElemCell1.gridPoints]) (ElemCell1.gridPt ⟨2 * ei.val + 2, by omega⟩)
                  (by simp [ElemCell1.gridPoints])
                simpa [ElemCell1.gridPt, GridPoint.toIndex1, GridPoint.ofIndex1,
                  ElemCell1.embedIndex] using this)
          · -- cs = neg: σ'(i) = right_i. Block at embLo_j.
            have h_neg := coarsen_neg_full_neg_prefs gps' i ⟨ej.val, by omega⟩ ei hcs
            have embLo_j_mem : ElemCell1.gridPt (ElemCell1.embedIndex ⟨ej.val, by omega⟩) ∈
                (localNashCell gps' (1 - i) ej ei).gridPoints := by
              rw [hcell_opp]; simp [cellFromSign, ElemCell1.gridPoints, ElemCell1.embedIndex]
            rw [hcell_i, hcs] at hFwd hBwd
            simp [ElemCell1.subcells] at hBsub
            rcases hBsub with rfl | rfl | rfl
            · exact h_neg.1 (by
                simp only [cellFromSign] at hFwd
                have := hFwd _ embLo_j_mem (ElemCell1.gridPt (ElemCell1.midIndex ei))
                  (by simp [ElemCell1.gridPoints, ElemCell1.midIndex]) (ElemCell1.gridPt ⟨2 * ei.val, by omega⟩)
                  (by simp [ElemCell1.gridPoints])
                simpa [ElemCell1.gridPt, GridPoint.toIndex1, GridPoint.ofIndex1,
                  ElemCell1.embedIndex, ElemCell1.midIndex] using this)
            · exact h_neg.2.1 (by
                simp only [cellFromSign] at hFwd
                have := hFwd _ embLo_j_mem (ElemCell1.gridPt ⟨2 * ei.val + 2, by omega⟩)
                  (by simp [ElemCell1.gridPoints])
                  (ElemCell1.gridPt (ElemCell1.midIndex ei)) (by simp [ElemCell1.gridPoints])
                simpa [ElemCell1.gridPt, GridPoint.toIndex1, GridPoint.ofIndex1,
                  ElemCell1.embedIndex, ElemCell1.midIndex] using this)
            · exact hBwd hFwd
          · -- cs = zero: σ'(i) = mid_vtx. All prefs at embLo_j and mid_j.
            -- CellDevLE(B, mid_vtx) holds → hBwd fails
            apply hBwd
            rw [hcell_i, hcs]
            intro q hq a ha b hb
            rw [hcell_opp] at hq
            simp only [cellFromSign] at hq hb ⊢
            simp [ElemCell1.gridPoints] at hb; subst hb
            -- q ∈ left_j.gp = {embLo_j, mid_j}
            simp [ElemCell1.gridPoints] at hq
            rcases hq with rfl | rfl
            · -- q = embLo_j: coarsen sign zero → all prefs
              have hall := coarsen_zero_all_prefs gps' i ei ⟨ej.val, by omega⟩ hcs
              simp [ElemCell1.subcells] at hBsub
              rcases hBsub with rfl | rfl | rfl <;>
                simp [ElemCell1.gridPoints] at ha <;>
                (try rcases ha with rfl | rfl) <;>
                simp [ElemCell1.gridPt, GridPoint.toIndex1, GridPoint.ofIndex1,
                  ElemCell1.midIndex]
              all_goals first
                | exact gps'.pref_refl _ _ _
                | exact hall.1 | exact hall.2.1 | exact hall.2.2.1 | exact hall.2.2.2.1
            · -- q = mid_j: mi = zero → all prefs
              have hall := zero_sign_all_prefs gps' i (ElemCell1.midIndex ej) ei hmi
              simp [ElemCell1.subcells] at hBsub
              rcases hBsub with rfl | rfl | rfl <;>
                simp [ElemCell1.gridPoints] at ha <;>
                (try rcases ha with rfl | rfl) <;>
                simp [ElemCell1.gridPt, GridPoint.toIndex1, GridPoint.ofIndex1,
                  ElemCell1.midIndex]
              all_goals first
                | exact gps'.pref_refl _ _ _
                | exact hall.1 | exact hall.2.1 | exact hall.2.2.1 | exact hall.2.2.2.1
        · -- mi = zero, mj = neg: opponent chose right, use coarsen sign at embHi_j
          have hcell_i : localNashCell gps' i ei ej =
              cellFromSign ei (gps'.coarsen.signAt i ⟨ej.val + 1, by omega⟩ ei) := by
            simp only [localNashCell, mi, hmi, mj, hmj]
          have hcell_opp : localNashCell gps' (1 - i) ej ei = cellFromSign ej .neg := by
            simp only [localNashCell, mj, hmj]
          intro ⟨hFwd, hBwd⟩
          set cs := gps'.coarsen.signAt i ⟨ej.val + 1, by omega⟩ ei
          rcases hcs : cs with _ | _ | _
          · -- cs = pos: σ'(i) = left_i. Block at embHi_j.
            have h_pos := coarsen_pos_full_neg_prefs gps' i ⟨ej.val + 1, by omega⟩ ei hcs
            have embHi_j_mem : ElemCell1.gridPt (ElemCell1.embedIndex ⟨ej.val + 1, by omega⟩) ∈
                (localNashCell gps' (1 - i) ej ei).gridPoints := by
              rw [hcell_opp]; simp only [cellFromSign, ElemCell1.gridPoints, ElemCell1.embedIndex,
                Finset.mem_insert, Finset.mem_singleton]
              right; apply congr_arg ElemCell1.gridPt; ext; simp; omega
            rw [hcell_i, hcs] at hFwd hBwd
            simp [ElemCell1.subcells] at hBsub
            rcases hBsub with rfl | rfl | rfl
            · exact hBwd hFwd
            · exact h_pos.1 (by
                simp only [cellFromSign] at hFwd
                have := hFwd _ embHi_j_mem (ElemCell1.gridPt ⟨2 * ei.val, by omega⟩)
                  (by simp [ElemCell1.gridPoints]) (ElemCell1.gridPt (ElemCell1.midIndex ei))
                  (by simp [ElemCell1.gridPoints])
                simpa [ElemCell1.gridPt, GridPoint.toIndex1, GridPoint.ofIndex1,
                  ElemCell1.embedIndex, ElemCell1.midIndex] using this)
            · exact h_pos.2.2 (by
                simp only [cellFromSign] at hFwd
                have := hFwd _ embHi_j_mem (ElemCell1.gridPt ⟨2 * ei.val, by omega⟩)
                  (by simp [ElemCell1.gridPoints]) (ElemCell1.gridPt ⟨2 * ei.val + 2, by omega⟩)
                  (by simp [ElemCell1.gridPoints])
                simpa [ElemCell1.gridPt, GridPoint.toIndex1, GridPoint.ofIndex1,
                  ElemCell1.embedIndex] using this)
          · -- cs = neg: σ'(i) = right_i. Block at embHi_j.
            have h_neg := coarsen_neg_full_neg_prefs gps' i ⟨ej.val + 1, by omega⟩ ei hcs
            have embHi_j_mem : ElemCell1.gridPt (ElemCell1.embedIndex ⟨ej.val + 1, by omega⟩) ∈
                (localNashCell gps' (1 - i) ej ei).gridPoints := by
              rw [hcell_opp]; simp only [cellFromSign, ElemCell1.gridPoints, ElemCell1.embedIndex,
                Finset.mem_insert, Finset.mem_singleton]
              right; apply congr_arg ElemCell1.gridPt; ext; simp; omega
            rw [hcell_i, hcs] at hFwd hBwd
            simp [ElemCell1.subcells] at hBsub
            rcases hBsub with rfl | rfl | rfl
            · exact h_neg.1 (by
                simp only [cellFromSign] at hFwd
                have := hFwd _ embHi_j_mem (ElemCell1.gridPt (ElemCell1.midIndex ei))
                  (by simp [ElemCell1.gridPoints, ElemCell1.midIndex])
                  (ElemCell1.gridPt ⟨2 * ei.val, by omega⟩)
                  (by simp [ElemCell1.gridPoints])
                simpa [ElemCell1.gridPt, GridPoint.toIndex1, GridPoint.ofIndex1,
                  ElemCell1.embedIndex, ElemCell1.midIndex] using this)
            · exact h_neg.2.1 (by
                simp only [cellFromSign] at hFwd
                have := hFwd _ embHi_j_mem (ElemCell1.gridPt ⟨2 * ei.val + 2, by omega⟩)
                  (by simp [ElemCell1.gridPoints])
                  (ElemCell1.gridPt (ElemCell1.midIndex ei)) (by simp [ElemCell1.gridPoints, ElemCell1.midIndex])
                simpa [ElemCell1.gridPt, GridPoint.toIndex1, GridPoint.ofIndex1,
                  ElemCell1.embedIndex, ElemCell1.midIndex] using this)
            · exact hBwd hFwd
          · -- cs = zero: σ'(i) = mid_vtx. All prefs at embHi_j and mid_j.
            apply hBwd
            rw [hcell_i, hcs]
            intro q hq a ha b hb
            rw [hcell_opp] at hq
            simp only [cellFromSign] at hq hb ⊢
            simp [ElemCell1.gridPoints] at hb; subst hb
            simp [ElemCell1.gridPoints] at hq
            rcases hq with rfl | rfl
            · -- q = mid_j: mi = zero → all prefs
              have hall := zero_sign_all_prefs gps' i (ElemCell1.midIndex ej) ei hmi
              simp [ElemCell1.subcells] at hBsub
              rcases hBsub with rfl | rfl | rfl <;>
                simp [ElemCell1.gridPoints] at ha <;>
                (try rcases ha with rfl | rfl) <;>
                simp [ElemCell1.gridPt, GridPoint.toIndex1, GridPoint.ofIndex1,
                  ElemCell1.midIndex]
              all_goals first
                | exact gps'.pref_refl _ _ _
                | exact hall.1 | exact hall.2.1 | exact hall.2.2.1 | exact hall.2.2.2.1
            · -- q = embHi_j: coarsen sign zero → all prefs
              have hall := coarsen_zero_all_prefs gps' i ei ⟨ej.val + 1, by omega⟩ hcs
              simp [ElemCell1.subcells] at hBsub
              rcases hBsub with rfl | rfl | rfl <;>
                simp [ElemCell1.gridPoints] at ha <;>
                (try rcases ha with rfl | rfl) <;>
                simp [ElemCell1.gridPt, GridPoint.toIndex1, GridPoint.ofIndex1,
                  ElemCell1.midIndex]
              all_goals first
                | exact gps'.pref_refl _ _ _
                | exact hall.1 | exact hall.2.1 | exact hall.2.2.1 | exact hall.2.2.2.1
        · -- mi = zero, mj = zero: both mid_vtx
          have hcell_i : localNashCell gps' i ei ej = cellFromSign ei .zero := by
            simp only [localNashCell, mi, hmi, mj, hmj]
          have hcell_opp : localNashCell gps' (1 - i) ej ei = cellFromSign ej .zero := by
            simp only [localNashCell, mj, hmj, fin2_one_sub_one_sub, mi, hmi]
          -- Both are mid_vtx. Only opp point is mid_j. mi=zero → all prefs → CellDevLE both dirs.
          intro ⟨_, hBwd⟩; apply hBwd
          rw [hcell_i]
          intro q hq a ha b hb
          rw [hcell_opp] at hq
          simp only [cellFromSign] at hq hb ⊢
          simp [ElemCell1.gridPoints] at hb hq; subst hb; subst hq
          -- q = mid_j, b = mid_i. mi=zero → all prefs
          have hall := zero_sign_all_prefs gps' i (ElemCell1.midIndex ej) ei hmi
          simp [ElemCell1.subcells] at hBsub
          rcases hBsub with rfl | rfl | rfl <;>
            simp [ElemCell1.gridPoints] at ha <;>
            (try rcases ha with rfl | rfl) <;>
            simp [ElemCell1.gridPt, GridPoint.toIndex1, GridPoint.ofIndex1,
              ElemCell1.midIndex]
          all_goals first
            | exact gps'.pref_refl _ _ _
            | exact hall.1 | exact hall.2.1 | exact hall.2.2.1 | exact hall.2.2.2.1

-- ================================================================
-- Section 4: Backward direction — extract sign data from IsLocalNash
-- ================================================================

/-- From a refining profile σ', extract the midpoint sign data.
    Uses extractFlipMid for edge-edge players with flip Nash pairs.
    For vertex or zero-zero players, returns zero. -/
noncomputable def extractMidpointData (gps : GridPrefSystem k) (σ : CellProfile1 k)
    (σ' : CellProfile1 (k + 1)) : MidpointSignData :=
  fun i =>
    match σ i, σ (1 - i) with
    | .vertex _, _ => .zero
    | .edge _, .vertex _ => .zero
    | .edge ei, .edge _ =>
      let signs := gps.localSignsAt σ i
      extractFlipMid ei signs.1 signs.2 (σ' i)

/-- For flip Nash pairs (non-zero-zero), extractMidpointData recovers the cell. -/
theorem extractMidpointData_recovers_flip (gps : GridPrefSystem k)
    (σ : CellProfile1 k) (hN : CellIsNash gps σ)
    (σ' : CellProfile1 (k + 1)) (hRef : σ'.Refines σ)
    (i : Fin 2) (hσi : ∃ ei, σ i = .edge ei)
    (hFlip : gps.localSignsAt σ i ≠ (.zero, .zero)) :
    refineCell (σ i) (gps.localSignsAt σ i) (extractMidpointData gps σ σ' i) = σ' i := by
  obtain ⟨ei, hei⟩ := hσi
  simp only [hei, refineCell, extractMidpointData]
  have hNP := cellIsNash_implies_isNashPair gps σ hN i
  have hMem : σ' i ∈ (ElemCell1.edge ei).subcells := by
    have := hRef i; rw [hei] at this; exact this
  match hσopp : σ (1 - i) with
  | .vertex j =>
    exfalso; apply hFlip
    show gps.localSignsAt σ i = _
    simp only [GridPrefSystem.localSignsAt, hei, hσopp]
    have hNP' := hNP
    simp only [GridPrefSystem.localSignsAt, hei, hσopp, IsNashPair] at hNP'
    rcases hNP' with h | h | h
    all_goals (have h1 := congrArg Prod.fst h; have h2 := congrArg Prod.snd h; simp at h1 h2)
    · rw [h1] at h2; exact absurd h2 (by decide)
    · rw [h1] at h2; exact absurd h2 (by decide)
    · rw [h1]
  | .edge ej =>
    simp only [GridPrefSystem.localSignsAt, hei, hσopp]
    have hNP' := hNP
    simp only [GridPrefSystem.localSignsAt, hei, hσopp] at hNP' hFlip
    exact refineEdge_extractFlipMid ei hNP' hFlip (σ' i) hMem

end SyntheticGameTheory
