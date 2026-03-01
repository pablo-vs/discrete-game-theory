/-
# Refinement Tower for Unified Sign Games

Builds on Unified.lean to show that Nash equilibria at level k can be
refined to level k+1.

## Scope limitation

The interpolation constraint assumes 2-action base games: each player's
mixed strategy is a single parameter in [0,1], discretized to Fin(2^k + 1).
The payoff comparison sign₀(j, a, b) is affine in the opponent's mix j,
so interpolation along the opponent's grid axis suffices. For n-action
games (n > 2), multilinear interpolation would be needed.
-/
import SyntheticGameTheory.Unified
import Mathlib.Data.Finset.Max

namespace Unified

open Sign

-- ================================================================
-- Section 1: Grid arithmetic
-- ================================================================

/-- Grid size at level k: 2^k + 1 points discretizing [0,1]. -/
abbrev gridSize (k : ℕ) : ℕ := 2 ^ k + 1

/-- Number of edges (intervals) at level k: 2^k. -/
abbrev edgeCount (k : ℕ) : ℕ := 2 ^ k

-- omega can't handle 2^k. This unfolds pow_succ and lets omega finish.
macro "grid_omega" : tactic =>
  `(tactic| (simp only [gridSize, edgeCount, Nat.pow_succ, Nat.mul_comm] at *; omega))

-- ================================================================
-- Section 2: Grid embedding and midpoints
-- ================================================================

/-- Embed level-k grid point into level-(k+1) grid: j ↦ 2j. -/
def embed (k : ℕ) (j : Fin (gridSize k)) : Fin (gridSize (k + 1)) :=
  ⟨2 * j.val, by grid_omega⟩

/-- Midpoint between embedded grid points 2j and 2(j+1): maps to 2j+1. -/
def midpoint (k : ℕ) (j : Fin (edgeCount k)) : Fin (gridSize (k + 1)) :=
  ⟨2 * j.val + 1, by grid_omega⟩

theorem embed_injective (k : ℕ) : Function.Injective (embed k) := by
  intro a b h; simp [embed, Fin.ext_iff] at h; exact Fin.ext (by omega)

@[simp] theorem embed_val (k : ℕ) (j : Fin (gridSize k)) :
    (embed k j).val = 2 * j.val := rfl

@[simp] theorem midpoint_val (k : ℕ) (j : Fin (edgeCount k)) :
    (midpoint k j).val = 2 * j.val + 1 := rfl

-- ================================================================
-- Section 3: Elementary Cells (vertex and edge faces)
-- ================================================================

/-- Vertex cell: the singleton face {j}. -/
def cellVertex {k : ℕ} (j : Fin (gridSize k)) : Face (Fin (gridSize k)) :=
  Face.vertex j

/-- Edge cell: the pair {j, j+1} for adjacent grid points. -/
def cellEdge {k : ℕ} (j : Fin (edgeCount k)) : Face (Fin (gridSize k)) :=
  ⟨{⟨j.val, by grid_omega⟩, ⟨j.val + 1, by grid_omega⟩},
   ⟨⟨j.val, by grid_omega⟩, Finset.mem_insert_self _ _⟩⟩

-- ================================================================
-- Section 4: Coherence — level-(k+1) restricts to level-k
-- ================================================================

/-- A level-(k+1) sign game is coherent with a level-k game if
    restricting to even-indexed grid points recovers the coarser game. -/
structure Coherent {k : ℕ}
    (Gfine : SignGame (Fin (gridSize (k + 1))) (Fin (gridSize (k + 1))))
    (Gcoarse : SignGame (Fin (gridSize k)) (Fin (gridSize k))) : Prop where
  sign₀_eq : ∀ (j : Fin (gridSize k)) (a b : Fin (gridSize k)),
    Gfine.sign₀ (embed k j) (embed k a) (embed k b) = Gcoarse.sign₀ j a b
  sign₁_eq : ∀ (j : Fin (gridSize k)) (a b : Fin (gridSize k)),
    Gfine.sign₁ (embed k j) (embed k a) (embed k b) = Gcoarse.sign₁ j a b

-- ================================================================
-- Section 5: Interpolation — midpoint signs are constrained
-- ================================================================

/-- When both endpoint signs agree, the midpoint is forced.
    When they disagree (flip pair), the midpoint is free. -/
def forcedMidpointSign : Sign → Sign → Option Sign
  | .pos, .pos => some .pos
  | .neg, .neg => some .neg
  | .zero, .zero => some .zero
  | .pos, .zero => some .pos
  | .zero, .pos => some .pos
  | .neg, .zero => some .neg
  | .zero, .neg => some .neg
  | .pos, .neg => none  -- free: Nash boundary passes through
  | .neg, .pos => none  -- free: Nash boundary passes through

/-- forcedMidpointSign of two nonneg signs is nonneg. -/
theorem forcedMidpointSign_nonneg {s1 s2 s : Sign}
    (h1 : s1.nonneg) (h2 : s2.nonneg)
    (hf : forcedMidpointSign s1 s2 = some s) : s.nonneg := by
  cases s1 <;> cases s2 <;> simp [forcedMidpointSign, Sign.nonneg] at * <;> subst_eqs <;> trivial

-- Fin construction helpers: coarse-edge j ∈ Fin(edgeCount k) gives
-- fine-grid indices 2j, 2j+1, 2j+2 in Fin(gridSize(k+1)).
-- These are the left endpoint, midpoint, and right endpoint of the
-- coarse interval [j, j+1] embedded into the fine grid.

-- embed k j already provides ⟨2*j, _⟩ : Fin(gridSize(k+1))
-- midpoint k j already provides ⟨2*j+1, _⟩ : Fin(gridSize(k+1))
-- We need the right endpoint: embed k ⟨j+1, _⟩ = ⟨2*(j+1), _⟩

private theorem edgeSucc_lt {k : ℕ} (j : Fin (edgeCount k)) :
    j.val + 1 < gridSize k := by grid_omega

/-- Right endpoint of a coarse edge embedded into the fine grid. -/
def embedRight (k : ℕ) (j : Fin (edgeCount k)) : Fin (gridSize (k + 1)) :=
  embed k ⟨j.val + 1, edgeSucc_lt j⟩

theorem embedRight_val (k : ℕ) (j : Fin (edgeCount k)) :
    (embedRight k j).val = 2 * j.val + 2 := by
  simp [embedRight, embed_val]; omega

/-- The interpolation constraint: for each coarse edge, the midpoint sign
    in the fine grid must be consistent with the endpoint signs.

    Encodes that sign₀(-, a, b) is affine in the opponent's mix parameter.
    Scope: opponent axis only (sufficient for 2-action base games). -/
structure Interpolated {k : ℕ}
    (G : SignGame (Fin (gridSize (k + 1))) (Fin (gridSize (k + 1)))) : Prop where
  interp₀ : ∀ (j : Fin (edgeCount k)) (a b : Fin (gridSize (k + 1))),
    ∀ s, forcedMidpointSign
      (G.sign₀ (embed k ⟨j, by grid_omega⟩) a b)
      (G.sign₀ (embedRight k j) a b) = some s →
    G.sign₀ (midpoint k j) a b = s
  interp₁ : ∀ (j : Fin (edgeCount k)) (a b : Fin (gridSize (k + 1))),
    ∀ s, forcedMidpointSign
      (G.sign₁ (embed k ⟨j, by grid_omega⟩) a b)
      (G.sign₁ (embedRight k j) a b) = some s →
    G.sign₁ (midpoint k j) a b = s

-- ================================================================
-- Section 6: Profile refinement
-- ================================================================

/-- A fine-level face refines a coarse-level face if every fine grid point,
    when halved (rounded down), lands in the coarse face. -/
def FaceRefines {k : ℕ} (F' : Face (Fin (gridSize (k + 1))))
    (F : Face (Fin (gridSize k))) : Prop :=
  ∀ v ∈ F'.1, (⟨v.val / 2, by have := v.isLt; grid_omega⟩ : Fin (gridSize k)) ∈ F.1

/-- A fine profile refines a coarse profile componentwise. -/
def ProfileRefines {k : ℕ}
    (σ' : Face (Fin (gridSize (k + 1))) × Face (Fin (gridSize (k + 1))))
    (σ : Face (Fin (gridSize k)) × Face (Fin (gridSize k))) : Prop :=
  FaceRefines σ'.1 σ.1 ∧ FaceRefines σ'.2 σ.2

-- ================================================================
-- Section 7: Embedding faces and DevFaceLE transfer
-- ================================================================

/-- Embed a face from level k to level k+1. -/
def embedFace (k : ℕ) (F : Face (Fin (gridSize k))) : Face (Fin (gridSize (k + 1))) :=
  ⟨F.1.map ⟨embed k, embed_injective k⟩,
   let ⟨x, hx⟩ := F.2; ⟨embed k x, Finset.mem_map_of_mem _ hx⟩⟩

/-- Embedded faces refine their source. -/
theorem embedFace_refines {k : ℕ} (F : Face (Fin (gridSize k))) :
    FaceRefines (embedFace k F) F := by
  intro v hv
  simp only [embedFace, Finset.mem_map, Function.Embedding.coeFn_mk] at hv
  obtain ⟨w, hw, rfl⟩ := hv
  simp only [embed_val]
  have : (2 * w.val) / 2 = w.val := Nat.mul_div_cancel_left _ (by omega)
  have h_eq : (⟨(2 * w.val) / 2, by have := w.isLt; grid_omega⟩ : Fin (gridSize k)) = w := by
    ext; simp [this]
  rw [h_eq]
  exact hw

/-- Coherence transfers DevFaceLE₀ from coarse to fine (on embedded faces). -/
theorem DevFaceLE₀_embed {k : ℕ}
    {Gfine : SignGame (Fin (gridSize (k + 1))) (Fin (gridSize (k + 1)))}
    {Gcoarse : SignGame (Fin (gridSize k)) (Fin (gridSize k))}
    (hcoh : @Coherent k Gfine Gcoarse)
    {F₁ : Face (Fin (gridSize k))} {A B : Face (Fin (gridSize k))}
    (h : Gcoarse.DevFaceLE₀ F₁ A B) :
    Gfine.DevFaceLE₀ (embedFace k F₁) (embedFace k A) (embedFace k B) := by
  intro a ha j hj b hb
  simp only [embedFace, Finset.mem_map, Function.Embedding.coeFn_mk] at ha hj hb
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨j', hj', rfl⟩ := hj
  obtain ⟨b', hb', rfl⟩ := hb
  rw [hcoh.sign₀_eq]
  exact h a' ha' j' hj' b' hb'

/-- Coherence transfers DevFaceLE₁ from coarse to fine. -/
theorem DevFaceLE₁_embed {k : ℕ}
    {Gfine : SignGame (Fin (gridSize (k + 1))) (Fin (gridSize (k + 1)))}
    {Gcoarse : SignGame (Fin (gridSize k)) (Fin (gridSize k))}
    (hcoh : @Coherent k Gfine Gcoarse)
    {F₀ : Face (Fin (gridSize k))} {A B : Face (Fin (gridSize k))}
    (h : Gcoarse.DevFaceLE₁ F₀ A B) :
    Gfine.DevFaceLE₁ (embedFace k F₀) (embedFace k A) (embedFace k B) := by
  intro a ha j hj b hb
  simp only [embedFace, Finset.mem_map, Function.Embedding.coeFn_mk] at ha hj hb
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨j', hj', rfl⟩ := hj
  obtain ⟨b', hb', rfl⟩ := hb
  rw [hcoh.sign₁_eq]
  exact h a' ha' j' hj' b' hb'

-- ================================================================
-- Section 8: Sign Tower
-- ================================================================

/-- A tower of sign games at increasing precision levels. -/
structure SignTower where
  game : (k : ℕ) → SignGame (Fin (gridSize k)) (Fin (gridSize k))
  coherent : ∀ k, @Coherent k (game (k + 1)) (game k)
  interpolated : ∀ k, @Interpolated k (game (k + 1))

-- ================================================================
-- Section 9: Nash existence at every level
-- ================================================================

instance gridSize_nonempty (k : ℕ) : Nonempty (Fin (gridSize k)) :=
  ⟨⟨0, Nat.succ_pos _⟩⟩

/-- Nash equilibria exist at every level of the tower. -/
theorem SignTower.nash_exists_at (tower : SignTower) (k : ℕ) :
    ∃ σ : Face (Fin (gridSize k)) × Face (Fin (gridSize k)),
      (tower.game k).IsNash σ :=
  (tower.game k).nash_exists

-- ================================================================
-- Section 10: Embedded Nash is non-dominated at fine level
-- ================================================================

/-- If σ is Nash at level k, then the embedded profile at level k+1
    admits no strict deviation among embedded faces. -/
theorem IsNash_embed_no_strict_dev₀ {k : ℕ}
    {Gfine : SignGame (Fin (gridSize (k + 1))) (Fin (gridSize (k + 1)))}
    {Gcoarse : SignGame (Fin (gridSize k)) (Fin (gridSize k))}
    (hcoh : @Coherent k Gfine Gcoarse)
    {σ : Face (Fin (gridSize k)) × Face (Fin (gridSize k))}
    (hN : Gcoarse.IsNash σ)
    (A : Face (Fin (gridSize k))) :
    ¬Gfine.StrictDev₀ (embedFace k σ.1, embedFace k σ.2) (embedFace k A) := by
  intro ⟨hfwd, hbwd⟩
  apply hN.1 A
  constructor
  · intro a ha j hj b hb
    have := hfwd (embed k a) (Finset.mem_map_of_mem _ ha)
      (embed k j) (Finset.mem_map_of_mem _ hj)
      (embed k b) (Finset.mem_map_of_mem _ hb)
    rwa [hcoh.sign₀_eq] at this
  · exact fun h => hbwd (DevFaceLE₀_embed hcoh h)

theorem IsNash_embed_no_strict_dev₁ {k : ℕ}
    {Gfine : SignGame (Fin (gridSize (k + 1))) (Fin (gridSize (k + 1)))}
    {Gcoarse : SignGame (Fin (gridSize k)) (Fin (gridSize k))}
    (hcoh : @Coherent k Gfine Gcoarse)
    {σ : Face (Fin (gridSize k)) × Face (Fin (gridSize k))}
    (hN : Gcoarse.IsNash σ)
    (A : Face (Fin (gridSize k))) :
    ¬Gfine.StrictDev₁ (embedFace k σ.1, embedFace k σ.2) (embedFace k A) := by
  intro ⟨hfwd, hbwd⟩
  apply hN.2 A
  constructor
  · intro a ha j hj b hb
    have := hfwd (embed k a) (Finset.mem_map_of_mem _ ha)
      (embed k j) (Finset.mem_map_of_mem _ hj)
      (embed k b) (Finset.mem_map_of_mem _ hb)
    rwa [hcoh.sign₁_eq] at this
  · exact fun h => hbwd (DevFaceLE₁_embed hcoh h)

-- ================================================================
-- Section 11: Interpolation preserves nonneg along opponent axis
-- ================================================================

/-- Both nonneg endpoints force the midpoint sign to be nonneg-valued. -/
private theorem forcedMidpoint_of_nonneg_nonneg {s1 s2 : Sign}
    (h1 : s1.nonneg) (h2 : s2.nonneg) :
    ∃ s, forcedMidpointSign s1 s2 = some s ∧ s.nonneg := by
  cases s1 <;> cases s2 <;> simp [Sign.nonneg, forcedMidpointSign] at *

/-- Key interpolation lemma: if sign₀ is nonneg at both endpoints of a
    coarse edge, it is nonneg at the midpoint. -/
theorem nonneg_midpoint₀ {k : ℕ}
    {G : SignGame (Fin (gridSize (k + 1))) (Fin (gridSize (k + 1)))}
    (hint : @Interpolated k G)
    (j : Fin (edgeCount k)) (a b : Fin (gridSize (k + 1)))
    (hl : (G.sign₀ (embed k ⟨j, by grid_omega⟩) a b).nonneg)
    (hr : (G.sign₀ (embedRight k j) a b).nonneg) :
    (G.sign₀ (midpoint k j) a b).nonneg := by
  obtain ⟨s, hs, hs_nn⟩ := forcedMidpoint_of_nonneg_nonneg hl hr
  rw [hint.interp₀ j a b s hs]
  exact hs_nn

theorem nonneg_midpoint₁ {k : ℕ}
    {G : SignGame (Fin (gridSize (k + 1))) (Fin (gridSize (k + 1)))}
    (hint : @Interpolated k G)
    (j : Fin (edgeCount k)) (a b : Fin (gridSize (k + 1)))
    (hl : (G.sign₁ (embed k ⟨j, by grid_omega⟩) a b).nonneg)
    (hr : (G.sign₁ (embedRight k j) a b).nonneg) :
    (G.sign₁ (midpoint k j) a b).nonneg := by
  obtain ⟨s, hs, hs_nn⟩ := forcedMidpoint_of_nonneg_nonneg hl hr
  rw [hint.interp₁ j a b s hs]
  exact hs_nn

-- ================================================================
-- Section 12: FaceRefines is monotone under subface
-- ================================================================

/-- If F' ⊆ G' and G' refines F, then F' refines F. -/
theorem FaceRefines_mono {k : ℕ}
    {F' G' : Face (Fin (gridSize (k + 1)))} {F : Face (Fin (gridSize k))}
    (h_sub : Face.IsSubface F' G') (h_ref : FaceRefines G' F) :
    FaceRefines F' F :=
  fun v hv => h_ref v (h_sub hv)

-- ================================================================
-- Section 13: The Main Refinement Theorem
-- ================================================================

/-- Given OutsideDominated at the embedded profile, Nash descent produces
    a refining Nash at the next level. -/
theorem nash_refines_of_embed_OD {k : ℕ}
    (G : SignGame (Fin (gridSize (k + 1))) (Fin (gridSize (k + 1))))
    (σ : Face (Fin (gridSize k)) × Face (Fin (gridSize k)))
    (hEOD₀ : G.OutsideDominated₀ (embedFace k σ.1, embedFace k σ.2))
    (hEOD₁ : G.OutsideDominated₁ (embedFace k σ.1, embedFace k σ.2)) :
    ∃ σ' : Face (Fin (gridSize (k + 1))) × Face (Fin (gridSize (k + 1))),
      G.IsNash σ' ∧ ProfileRefines σ' σ := by
  obtain ⟨τ, hτN, hτ₀_sub, hτ₁_sub, _, _⟩ := G.nash_exists_sub_OD
    (embedFace k σ.1, embedFace k σ.2) hEOD₀ hEOD₁
  exact ⟨τ, hτN,
    FaceRefines_mono hτ₀_sub (embedFace_refines σ.1),
    FaceRefines_mono hτ₁_sub (embedFace_refines σ.2)⟩

-- ================================================================
-- Section 14: Full refinement from nash_exists_with_OD
-- ================================================================

/-- Nash existence with OutsideDominated invariants at every tower level. -/
theorem SignTower.nash_exists_with_OD (tower : SignTower) (k : ℕ) :
    ∃ σ : Face (Fin (gridSize k)) × Face (Fin (gridSize k)),
      (tower.game k).IsNash σ ∧
      (tower.game k).OutsideDominated₀ σ ∧
      (tower.game k).OutsideDominated₁ σ := by
  obtain ⟨σ, hN, _, _, hOD₀, hOD₁⟩ := (tower.game k).nash_exists_sub_OD
    (@Face.full _ _ _ (gridSize_nonempty k), @Face.full _ _ _ (gridSize_nonempty k))
    ((tower.game k).OutsideDominated₀_maximal)
    ((tower.game k).OutsideDominated₁_maximal)
  exact ⟨σ, hN, hOD₀, hOD₁⟩

-- ================================================================
-- Section 15: Bilinear grid axioms
-- ================================================================

/-- Grid monotonicity: sign₀(j, a, b) depends only on compare(a, b) and j.
    Captures bilinear payoff structure: u(a,j) - u(b,j) = (a-b)·f(j),
    so the sign depends on a vs b only through their grid ordering. -/
structure GridMonotone {n : ℕ} (G : SignGame (Fin n) (Fin n)) : Prop where
  mono₀ : ∀ (j : Fin n) (a b a' b' : Fin n),
    a.val < b.val → a'.val < b'.val → G.sign₀ j a b = G.sign₀ j a' b'
  mono₁ : ∀ (j : Fin n) (a b a' b' : Fin n),
    a.val < b.val → a'.val < b'.val → G.sign₁ j a b = G.sign₁ j a' b'

/-- Opponent convexity: the nonneg set { j | sign₀(j,a,b).nonneg } is an interval.
    Captures affine dependence on opponent mix: sign₀(j,a,b) = sign((a-b)(αj+β)),
    so the sign in j changes at most once. -/
structure OpponentConvex {n : ℕ} (G : SignGame (Fin n) (Fin n)) : Prop where
  conv₀ : ∀ (j₁ j₂ j : Fin n) (a b : Fin n),
    j₁ ≤ j → j ≤ j₂ → (G.sign₀ j₁ a b).nonneg → (G.sign₀ j₂ a b).nonneg →
    (G.sign₀ j a b).nonneg
  conv₁ : ∀ (j₁ j₂ j : Fin n) (a b : Fin n),
    j₁ ≤ j → j ≤ j₂ → (G.sign₁ j₁ a b).nonneg → (G.sign₁ j₂ a b).nonneg →
    (G.sign₁ j a b).nonneg

-- ================================================================
-- Section 16: Face min/max and interval closure
-- ================================================================

section IntervalClosure

noncomputable def faceMin {n : ℕ} (F : Face (Fin n)) : Fin n := Finset.min' F.1 F.2
noncomputable def faceMax {n : ℕ} (F : Face (Fin n)) : Fin n := Finset.max' F.1 F.2

variable {n : ℕ}

theorem faceMin_mem (F : Face (Fin n)) : faceMin F ∈ F.1 := Finset.min'_mem F.1 F.2
theorem faceMax_mem (F : Face (Fin n)) : faceMax F ∈ F.1 := Finset.max'_mem F.1 F.2
theorem faceMin_le (F : Face (Fin n)) {v : Fin n} (hv : v ∈ F.1) :
    faceMin F ≤ v := Finset.min'_le F.1 v hv
theorem le_faceMax (F : Face (Fin n)) {v : Fin n} (hv : v ∈ F.1) :
    v ≤ faceMax F := Finset.le_max' F.1 v hv
theorem faceMin_le_faceMax (F : Face (Fin n)) :
    faceMin F ≤ faceMax F := faceMin_le F (faceMax_mem F)

/-- Interval closure [min F, max F]. -/
noncomputable def intervalClosure (F : Face (Fin n)) : Face (Fin n) :=
  ⟨Finset.univ.filter (fun v => faceMin F ≤ v ∧ v ≤ faceMax F),
   ⟨faceMin F, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_refl _, faceMin_le_faceMax F⟩⟩⟩

theorem mem_closure {F : Face (Fin n)} {v : Fin n} :
    v ∈ (intervalClosure F).1 ↔ faceMin F ≤ v ∧ v ≤ faceMax F := by
  simp [intervalClosure, Finset.mem_filter]

theorem face_sub_closure (F : Face (Fin n)) :
    Face.IsSubface F (intervalClosure F) :=
  fun _ hv => mem_closure.mpr ⟨faceMin_le F hv, le_faceMax F hv⟩

end IntervalClosure

-- ================================================================
-- Section 17: DevFaceLE invariance under interval closure
-- ================================================================

section ClosureDevFaceLE

variable {n : ℕ} {G : SignGame (Fin n) (Fin n)}

private theorem nonneg_of_mono₀ (hm : GridMonotone G)
    {j a b a' b' : Fin n} (hab : a.val < b.val) (h' : a'.val < b'.val)
    (h : (G.sign₀ j a' b').nonneg) : (G.sign₀ j a b).nonneg := by
  rw [hm.mono₀ j a b a' b' hab h']; exact h

private theorem nonneg_of_mono₀_gt (hm : GridMonotone G)
    {j a b a' b' : Fin n} (hba : b.val < a.val) (h' : b'.val < a'.val)
    (h : (G.sign₀ j a' b').nonneg) : (G.sign₀ j a b).nonneg := by
  have eq : G.sign₀ j a b = G.sign₀ j a' b' := by
    rw [G.sign₀_antisym j a b, G.sign₀_antisym j a' b', hm.mono₀ j b a b' a' hba h']
  rw [eq]; exact h

private theorem nonneg_of_mono₁ (hm : GridMonotone G)
    {j a b a' b' : Fin n} (hab : a.val < b.val) (h' : a'.val < b'.val)
    (h : (G.sign₁ j a' b').nonneg) : (G.sign₁ j a b).nonneg := by
  rw [hm.mono₁ j a b a' b' hab h']; exact h

private theorem nonneg_of_mono₁_gt (hm : GridMonotone G)
    {j a b a' b' : Fin n} (hba : b.val < a.val) (h' : b'.val < a'.val)
    (h : (G.sign₁ j a' b').nonneg) : (G.sign₁ j a b).nonneg := by
  have eq : G.sign₁ j a b = G.sign₁ j a' b' := by
    rw [G.sign₁_antisym j a b, G.sign₁_antisym j a' b', hm.mono₁ j b a b' a' hba h']
  rw [eq]; exact h

-- Helper: the three cases for DevFaceLE closure (used by left, right, both)
private theorem nonneg_closure_action₀ (hm : GridMonotone G)
    {j : Fin n} {a b : Fin n}
    {lo hi : Fin n} (hlo : lo.val ≤ a.val) (hhi : a.val ≤ hi.val)
    (hlo_nn : (G.sign₀ j lo b).nonneg) (hhi_nn : (G.sign₀ j hi b).nonneg) :
    (G.sign₀ j a b).nonneg := by
  by_cases hab : a.val < b.val
  · exact nonneg_of_mono₀ hm hab (Nat.lt_of_le_of_lt hlo hab) hlo_nn
  · by_cases hba : b.val < a.val
    · exact nonneg_of_mono₀_gt hm hba (Nat.lt_of_lt_of_le hba hhi) hhi_nn
    · have : a = b := Fin.ext (by omega)
      subst this; rw [G.sign₀_refl]; exact nonneg_zero

/-- DevFaceLE₀ is preserved under interval closure of the left face. -/
theorem DevFaceLE₀_closure_left (hm : GridMonotone G)
    {F : Face (Fin n)} {A B : Face (Fin n)}
    (h : G.DevFaceLE₀ F A B) :
    G.DevFaceLE₀ F (intervalClosure A) B := by
  intro a ha j hj b hb
  rw [mem_closure] at ha
  exact nonneg_closure_action₀ hm (Fin.val_le_of_le ha.1) (Fin.val_le_of_le ha.2)
    (h _ (faceMin_mem A) j hj b hb) (h _ (faceMax_mem A) j hj b hb)

/-- DevFaceLE₀ is preserved under interval closure of the right face. -/
theorem DevFaceLE₀_closure_right (hm : GridMonotone G)
    {F : Face (Fin n)} {A B : Face (Fin n)}
    (h : G.DevFaceLE₀ F A B) :
    G.DevFaceLE₀ F A (intervalClosure B) := by
  intro a ha j hj b hb
  rw [mem_closure] at hb
  -- sign₀(j, a, b) with b ∈ [min B, max B]: reduce to endpoints
  by_cases hab : a.val < b.val
  · exact nonneg_of_mono₀ hm hab
      (Nat.lt_of_lt_of_le hab (Fin.val_le_of_le hb.2)) (h a ha j hj _ (faceMax_mem B))
  · by_cases hba : b.val < a.val
    · exact nonneg_of_mono₀_gt hm hba
        (Nat.lt_of_le_of_lt (Fin.val_le_of_le hb.1) hba) (h a ha j hj _ (faceMin_mem B))
    · have : a = b := Fin.ext (by omega)
      subst this; rw [G.sign₀_refl]; exact nonneg_zero

/-- DevFaceLE₀ is preserved under interval closure of the opponent face. -/
theorem DevFaceLE₀_closure_opp (hc : OpponentConvex G)
    {F : Face (Fin n)} {A B : Face (Fin n)}
    (h : G.DevFaceLE₀ F A B) :
    G.DevFaceLE₀ (intervalClosure F) A B := by
  intro a ha j hj b hb
  rw [mem_closure] at hj
  exact hc.conv₀ _ _ j a b hj.1 hj.2
    (h a ha _ (faceMin_mem F) b hb) (h a ha _ (faceMax_mem F) b hb)

-- Symmetric versions for sign₁
private theorem nonneg_closure_action₁ (hm : GridMonotone G)
    {j : Fin n} {a b : Fin n}
    {lo hi : Fin n} (hlo : lo.val ≤ a.val) (hhi : a.val ≤ hi.val)
    (hlo_nn : (G.sign₁ j lo b).nonneg) (hhi_nn : (G.sign₁ j hi b).nonneg) :
    (G.sign₁ j a b).nonneg := by
  by_cases hab : a.val < b.val
  · exact nonneg_of_mono₁ hm hab (Nat.lt_of_le_of_lt hlo hab) hlo_nn
  · by_cases hba : b.val < a.val
    · exact nonneg_of_mono₁_gt hm hba (Nat.lt_of_lt_of_le hba hhi) hhi_nn
    · have : a = b := Fin.ext (by omega)
      subst this; rw [G.sign₁_refl]; exact nonneg_zero

theorem DevFaceLE₁_closure_left (hm : GridMonotone G)
    {F : Face (Fin n)} {A B : Face (Fin n)}
    (h : G.DevFaceLE₁ F A B) :
    G.DevFaceLE₁ F (intervalClosure A) B := by
  intro a ha j hj b hb
  rw [mem_closure] at ha
  exact nonneg_closure_action₁ hm (Fin.val_le_of_le ha.1) (Fin.val_le_of_le ha.2)
    (h _ (faceMin_mem A) j hj b hb) (h _ (faceMax_mem A) j hj b hb)

theorem DevFaceLE₁_closure_right (hm : GridMonotone G)
    {F : Face (Fin n)} {A B : Face (Fin n)}
    (h : G.DevFaceLE₁ F A B) :
    G.DevFaceLE₁ F A (intervalClosure B) := by
  intro a ha j hj b hb
  rw [mem_closure] at hb
  by_cases hab : a.val < b.val
  · exact nonneg_of_mono₁ hm hab
      (Nat.lt_of_lt_of_le hab (Fin.val_le_of_le hb.2)) (h a ha j hj _ (faceMax_mem B))
  · by_cases hba : b.val < a.val
    · exact nonneg_of_mono₁_gt hm hba
        (Nat.lt_of_le_of_lt (Fin.val_le_of_le hb.1) hba) (h a ha j hj _ (faceMin_mem B))
    · have : a = b := Fin.ext (by omega)
      subst this; rw [G.sign₁_refl]; exact nonneg_zero

theorem DevFaceLE₁_closure_opp (hc : OpponentConvex G)
    {F : Face (Fin n)} {A B : Face (Fin n)}
    (h : G.DevFaceLE₁ F A B) :
    G.DevFaceLE₁ (intervalClosure F) A B := by
  intro a ha j hj b hb
  rw [mem_closure] at hj
  exact hc.conv₁ _ _ j a b hj.1 hj.2
    (h a ha _ (faceMin_mem F) b hb) (h a ha _ (faceMax_mem F) b hb)

end ClosureDevFaceLE

-- ================================================================
-- Section 18: Nash and OD preserved under interval closure
-- ================================================================

section ClosureNashOD

variable {n : ℕ} {G : SignGame (Fin n) (Fin n)}

/-- Interval-closing both faces preserves Nash. -/
theorem IsNash_intervalClosure (hm : GridMonotone G) (hc : OpponentConvex G)
    {σ : Face (Fin n) × Face (Fin n)} (hN : G.IsNash σ) :
    G.IsNash (intervalClosure σ.1, intervalClosure σ.2) := by
  refine ⟨fun A hA => ?_, fun A hA => ?_⟩
  · -- StrictDev₀ (closure σ.1, closure σ.2) A → StrictDev₀ σ A
    apply hN.1 A
    obtain ⟨hfwd, hbwd⟩ := hA
    constructor
    · -- DevFaceLE₀ (closure σ.2) A (closure σ.1) → DevFaceLE₀ σ.2 A σ.1
      exact G.DevFaceLE₀_antitone (face_sub_closure σ.2)
        (G.DevFaceLE₀_right_mono (face_sub_closure σ.1) hfwd)
    · -- ¬DevFaceLE₀ (closure σ.2) (closure σ.1) A → ¬DevFaceLE₀ σ.2 σ.1 A
      intro h
      exact hbwd (DevFaceLE₀_closure_left hm (DevFaceLE₀_closure_opp hc h))
  · -- Symmetric for player 1
    apply hN.2 A
    obtain ⟨hfwd, hbwd⟩ := hA
    constructor
    · exact G.DevFaceLE₁_antitone (face_sub_closure σ.1)
        (G.DevFaceLE₁_right_mono (face_sub_closure σ.2) hfwd)
    · intro h
      exact hbwd (DevFaceLE₁_closure_left hm (DevFaceLE₁_closure_opp hc h))

/-- Interval-closing both faces preserves OutsideDominated₀.
    Key insight: if v is outside [min σ.1, max σ.1], it's on one side of the extremes.
    Grid monotonicity reduces the comparison to an extreme-vs-v comparison.
    The extreme is in σ.1, and v is outside σ.1, so coarse OD applies. -/
theorem OutsideDominated₀_intervalClosure (hm : GridMonotone G) (hc : OpponentConvex G)
    {σ : Face (Fin n) × Face (Fin n)} (hOD : G.OutsideDominated₀ σ) :
    G.OutsideDominated₀ (intervalClosure σ.1, intervalClosure σ.2) := by
  -- Need: ∀ v ∉ closure(σ.1), w ∈ closure(σ.1),
  --   DevFaceLE₀ closure(σ.2) (vertex w) (vertex v)
  intro v hv w hw
  -- DevFaceLE₀: ∀ a ∈ {w}, j ∈ closure(σ.2), b ∈ {v}, sign₀(j, a, b).nonneg
  -- Simplifies to: ∀ j ∈ closure(σ.2), sign₀(j, w, v).nonneg
  rw [mem_closure] at hw
  have hv' : v ∉ σ.1.1 := fun hv_in =>
    hv (mem_closure.mpr ⟨faceMin_le σ.1 hv_in, le_faceMax σ.1 hv_in⟩)
  -- Helper: sign₀(j_endpoint, w, v).nonneg for any endpoint of σ.2
  -- by grid monotonicity on w and coarse OD
  have key : ∀ je ∈ σ.2.1, (G.sign₀ je w v).nonneg := by
    intro je hje
    exact nonneg_closure_action₀ hm (Fin.val_le_of_le hw.1) (Fin.val_le_of_le hw.2)
      (hOD v hv' (faceMin σ.1) (faceMin_mem σ.1)
        (faceMin σ.1) (Finset.mem_singleton_self _) je hje
        v (Finset.mem_singleton_self _))
      (hOD v hv' (faceMax σ.1) (faceMax_mem σ.1)
        (faceMax σ.1) (Finset.mem_singleton_self _) je hje
        v (Finset.mem_singleton_self _))
  -- Now prove DevFaceLE₀ (closure σ.2) (vertex w) (vertex v)
  intro a ha j hj b hb
  simp [Face.vertex, Finset.mem_singleton] at ha hb
  subst ha; subst hb
  rw [mem_closure] at hj
  exact hc.conv₀ _ _ j a b hj.1 hj.2
    (key _ (faceMin_mem σ.2)) (key _ (faceMax_mem σ.2))

/-- Interval-closing both faces preserves OutsideDominated₁ (symmetric). -/
theorem OutsideDominated₁_intervalClosure (hm : GridMonotone G) (hc : OpponentConvex G)
    {σ : Face (Fin n) × Face (Fin n)} (hOD : G.OutsideDominated₁ σ) :
    G.OutsideDominated₁ (intervalClosure σ.1, intervalClosure σ.2) := by
  intro v hv w hw
  rw [mem_closure] at hw
  have hv' : v ∉ σ.2.1 := fun hv_in =>
    hv (mem_closure.mpr ⟨faceMin_le σ.2 hv_in, le_faceMax σ.2 hv_in⟩)
  have key : ∀ je ∈ σ.1.1, (G.sign₁ je w v).nonneg := by
    intro je hje
    exact nonneg_closure_action₁ hm (Fin.val_le_of_le hw.1) (Fin.val_le_of_le hw.2)
      (hOD v hv' (faceMin σ.2) (faceMin_mem σ.2)
        (faceMin σ.2) (Finset.mem_singleton_self _) je hje
        v (Finset.mem_singleton_self _))
      (hOD v hv' (faceMax σ.2) (faceMax_mem σ.2)
        (faceMax σ.2) (Finset.mem_singleton_self _) je hje
        v (Finset.mem_singleton_self _))
  intro a ha j hj b hb
  simp [Face.vertex, Finset.mem_singleton] at ha hb
  subst ha; subst hb
  rw [mem_closure] at hj
  exact hc.conv₁ _ _ j a b hj.1 hj.2
    (key _ (faceMin_mem σ.1)) (key _ (faceMax_mem σ.1))

end ClosureNashOD

-- ================================================================
-- Section 19: Bilinear sign games (factored representation)
-- ================================================================

/-- A bilinear sign game is determined by two opponent-sign functions.
    The full sign₀(j, a, b) = cmpSign(b.val, a.val) * oppSign₀(j).
    This captures the cardinal-model factorization u₀(a,j) - u₀(b,j) = (a-b)·f(j). -/
private theorem mul_cmpSign_trans {a b c : ℕ} {s : Sign}
    (h1 : (Sign.mul (cmpSign b a) s).nonneg)
    (h2 : (Sign.mul (cmpSign c b) s).nonneg) :
    (Sign.mul (cmpSign c a) s).nonneg := by
  cases s with
  | zero => simp only [Sign.mul_zero]; exact nonneg_zero
  | pos =>
    -- mul_pos: mul s pos = s, so this is cmpSign nonneg transitivity
    simp only [Sign.mul_pos] at *
    exact cmpSign_trans h2 h1
  | neg =>
    -- mul (cmpSign b a) neg nonneg ↔ cmpSign b a ∈ {neg, zero} ↔ a ≤ b
    -- (because mul zero neg = zero, mul neg neg = pos, mul pos neg = neg)
    -- h1: a ≤ b, h2: b ≤ c, goal: a ≤ c
    -- Prove via case analysis on cmpSign
    simp only [Sign.mul, Sign.flip, cmpSign, Sign.nonneg] at *
    split_ifs at * <;> simp_all <;> omega

def bilinearGame (n : ℕ) (oppSign₀ oppSign₁ : Fin n → Sign) :
    SignGame (Fin n) (Fin n) where
  sign₀ j a b := Sign.mul (cmpSign b.val a.val) (oppSign₀ j)
  sign₁ j a b := Sign.mul (cmpSign b.val a.val) (oppSign₁ j)
  sign₀_refl j a := by simp [cmpSign_self]
  sign₁_refl j a := by simp [cmpSign_self]
  sign₀_antisym j a b := by simp [Sign.flip_mul, cmpSign_flip]
  sign₁_antisym j a b := by simp [Sign.flip_mul, cmpSign_flip]
  sign₀_trans j a b c h1 h2 := mul_cmpSign_trans h1 h2
  sign₁_trans j a b c h1 h2 := mul_cmpSign_trans h1 h2

-- ================================================================
-- Section 20: Bilinear tower
-- ================================================================

/-- A bilinear tower: at each level k, opponent-sign functions for both players,
    with coherence at even grid points and interpolation at odd midpoints.
    This is the factored version of SignTower for 2-action base games. -/
structure BilinearTower where
  oppSign₀ : (k : ℕ) → Fin (gridSize k) → Sign
  oppSign₁ : (k : ℕ) → Fin (gridSize k) → Sign
  coherent₀ : ∀ k (j : Fin (gridSize k)),
    oppSign₀ (k + 1) (embed k j) = oppSign₀ k j
  coherent₁ : ∀ k (j : Fin (gridSize k)),
    oppSign₁ (k + 1) (embed k j) = oppSign₁ k j
  interp₀ : ∀ k (j : Fin (edgeCount k)),
    ∀ s, forcedMidpointSign (oppSign₀ (k + 1) (embed k ⟨j, by grid_omega⟩))
                             (oppSign₀ (k + 1) (embedRight k j)) = some s →
    oppSign₀ (k + 1) (midpoint k j) = s
  interp₁ : ∀ k (j : Fin (edgeCount k)),
    ∀ s, forcedMidpointSign (oppSign₁ (k + 1) (embed k ⟨j, by grid_omega⟩))
                             (oppSign₁ (k + 1) (embedRight k j)) = some s →
    oppSign₁ (k + 1) (midpoint k j) = s
  oppConvex₀ : ∀ k (j₁ j₂ j : Fin (gridSize k)),
    j₁ ≤ j → j ≤ j₂ → (oppSign₀ k j₁).nonneg → (oppSign₀ k j₂).nonneg →
    (oppSign₀ k j).nonneg
  oppConvex₁ : ∀ k (j₁ j₂ j : Fin (gridSize k)),
    j₁ ≤ j → j ≤ j₂ → (oppSign₁ k j₁).nonneg → (oppSign₁ k j₂).nonneg →
    (oppSign₁ k j).nonneg
  oppConvexNeg₀ : ∀ k (j₁ j₂ j : Fin (gridSize k)),
    j₁ ≤ j → j ≤ j₂ → (oppSign₀ k j₁).flip.nonneg → (oppSign₀ k j₂).flip.nonneg →
    (oppSign₀ k j).flip.nonneg
  oppConvexNeg₁ : ∀ k (j₁ j₂ j : Fin (gridSize k)),
    j₁ ≤ j → j ≤ j₂ → (oppSign₁ k j₁).flip.nonneg → (oppSign₁ k j₂).flip.nonneg →
    (oppSign₁ k j).flip.nonneg

/-- The sign game at level k derived from a bilinear tower. -/
def BilinearTower.game (t : BilinearTower) (k : ℕ) : SignGame (Fin (gridSize k)) (Fin (gridSize k)) :=
  bilinearGame (gridSize k) (t.oppSign₀ k) (t.oppSign₁ k)

/-- A bilinear tower is coherent (as a SignTower). -/
private theorem cmpSign_double (a b : ℕ) : cmpSign (2 * a) (2 * b) = cmpSign a b := by
  unfold cmpSign; simp only [Nat.mul_lt_mul_left (show 0 < 2 by omega)]

theorem BilinearTower.game_coherent (t : BilinearTower) (k : ℕ) :
    @Coherent k (t.game (k + 1)) (t.game k) where
  sign₀_eq j a b := by
    simp only [game, bilinearGame, embed_val, cmpSign_double, t.coherent₀]
  sign₁_eq j a b := by
    simp only [game, bilinearGame, embed_val, cmpSign_double, t.coherent₁]

-- ================================================================
-- Section 21: OD at embedded intervals via bilinear factorization
-- ================================================================

section BilinearOD

variable (t : BilinearTower)

/-- Key lemma: if oppSign₀ is nonneg at all even points in [2c, 2d], it's nonneg
    at all points in [2c, 2d] (by interpolation).
    j is either even (direct) or odd (midpoint of two nonneg endpoints → forced nonneg). -/
theorem BilinearTower.oppSign₀_nonneg_interval {k : ℕ}
    {c d : Fin (gridSize k)}
    (h_even : ∀ (j : Fin (gridSize k)), c ≤ j → j ≤ d →
      (t.oppSign₀ (k + 1) (embed k j)).nonneg)
    {j : Fin (gridSize (k + 1))} (hj_lo : embed k c ≤ j) (hj_hi : j ≤ embed k d) :
    (t.oppSign₀ (k + 1) j).nonneg := by
  have hj_lo' : 2 * c.val ≤ j.val := by simp [embed_val, Fin.le_iff_val_le_val] at hj_lo; omega
  have hj_hi' : j.val ≤ 2 * d.val := by simp [embed_val, Fin.le_iff_val_le_val] at hj_hi; omega
  by_cases heven : j.val % 2 = 0
  · -- j is even: j = embed k (j/2)
    have hm : j.val / 2 < gridSize k := by grid_omega
    have hj_eq : j = embed k ⟨j.val / 2, hm⟩ := by ext; simp [embed_val]; omega
    rw [hj_eq]
    exact h_even ⟨j.val / 2, hm⟩
      (Fin.mk_le_mk.mpr (by omega)) (Fin.mk_le_mk.mpr (by omega))
  · -- j is odd: j = midpoint k (j.val / 2)
    have hodd : j.val % 2 = 1 := by omega
    have hm_lt : j.val / 2 < edgeCount k := by grid_omega
    have hj_eq : j = midpoint k ⟨j.val / 2, hm_lt⟩ := by ext; simp [midpoint_val]; omega
    rw [hj_eq]
    have hl := h_even ⟨j.val / 2, by grid_omega⟩
      (Fin.mk_le_mk.mpr (by omega)) (Fin.mk_le_mk.mpr (by omega))
    have hr_coarse := h_even ⟨j.val / 2 + 1, by grid_omega⟩
      (Fin.mk_le_mk.mpr (by omega)) (Fin.mk_le_mk.mpr (by omega))
    -- embedRight k ⟨m, _⟩ = embed k ⟨m+1, _⟩
    have hr_eq : embedRight k ⟨j.val / 2, hm_lt⟩ = embed k ⟨j.val / 2 + 1, by grid_omega⟩ := by
      ext; simp [embedRight_val, embed_val]; omega
    have hr : (t.oppSign₀ (k + 1) (embedRight k ⟨j.val / 2, hm_lt⟩)).nonneg := by
      rw [hr_eq]; exact hr_coarse
    obtain ⟨s, hs, hs_nn⟩ := forcedMidpoint_of_nonneg_nonneg hl hr
    rw [t.interp₀ k ⟨j.val / 2, hm_lt⟩ s hs]
    exact hs_nn

/-- Symmetric version for oppSign₁. -/
theorem BilinearTower.oppSign₁_nonneg_interval {k : ℕ}
    {c d : Fin (gridSize k)}
    (h_even : ∀ (j : Fin (gridSize k)), c ≤ j → j ≤ d →
      (t.oppSign₁ (k + 1) (embed k j)).nonneg)
    {j : Fin (gridSize (k + 1))} (hj_lo : embed k c ≤ j) (hj_hi : j ≤ embed k d) :
    (t.oppSign₁ (k + 1) j).nonneg := by
  have hj_lo' : 2 * c.val ≤ j.val := by simp [embed_val, Fin.le_iff_val_le_val] at hj_lo; omega
  have hj_hi' : j.val ≤ 2 * d.val := by simp [embed_val, Fin.le_iff_val_le_val] at hj_hi; omega
  by_cases heven : j.val % 2 = 0
  · have hm : j.val / 2 < gridSize k := by grid_omega
    have hj_eq : j = embed k ⟨j.val / 2, hm⟩ := by ext; simp [embed_val]; omega
    rw [hj_eq]
    exact h_even ⟨j.val / 2, hm⟩
      (Fin.mk_le_mk.mpr (by omega)) (Fin.mk_le_mk.mpr (by omega))
  · have hodd : j.val % 2 = 1 := by omega
    have hm_lt : j.val / 2 < edgeCount k := by grid_omega
    have hj_eq : j = midpoint k ⟨j.val / 2, hm_lt⟩ := by ext; simp [midpoint_val]; omega
    rw [hj_eq]
    have hl := h_even ⟨j.val / 2, by grid_omega⟩
      (Fin.mk_le_mk.mpr (by omega)) (Fin.mk_le_mk.mpr (by omega))
    have hr_coarse := h_even ⟨j.val / 2 + 1, by grid_omega⟩
      (Fin.mk_le_mk.mpr (by omega)) (Fin.mk_le_mk.mpr (by omega))
    have hr_eq : embedRight k ⟨j.val / 2, hm_lt⟩ = embed k ⟨j.val / 2 + 1, by grid_omega⟩ := by
      ext; simp [embedRight_val, embed_val]; omega
    have hr : (t.oppSign₁ (k + 1) (embedRight k ⟨j.val / 2, hm_lt⟩)).nonneg := by
      rw [hr_eq]; exact hr_coarse
    obtain ⟨s, hs, hs_nn⟩ := forcedMidpoint_of_nonneg_nonneg hl hr
    rw [t.interp₁ k ⟨j.val / 2, hm_lt⟩ s hs]
    exact hs_nn

end BilinearOD

-- ================================================================
-- Section 22: Bilinear games are GridMonotone and OpponentConvex
-- ================================================================

private theorem cmpSign_neg_of_gt {a b : ℕ} (h : a < b) : cmpSign b a = Sign.neg := by
  simp only [cmpSign]
  have h1 : ¬(b < a) := by omega
  have h2 : a < b := h
  simp [h1, h2]

theorem bilinearGame_gridMonotone (n : ℕ) (oppSign₀ oppSign₁ : Fin n → Sign) :
    GridMonotone (bilinearGame n oppSign₀ oppSign₁) where
  mono₀ j a b a' b' hab ha'b' := by
    simp only [bilinearGame, cmpSign_neg_of_gt hab, cmpSign_neg_of_gt ha'b']
  mono₁ j a b a' b' hab ha'b' := by
    simp only [bilinearGame, cmpSign_neg_of_gt hab, cmpSign_neg_of_gt ha'b']

theorem BilinearTower.game_gridMonotone (t : BilinearTower) (k : ℕ) :
    GridMonotone (t.game k) :=
  bilinearGame_gridMonotone _ _ _

private theorem oppConvex_to_mul_convex {oppSign : Fin n → Sign}
    (hconv : ∀ (j₁ j₂ j : Fin n), j₁ ≤ j → j ≤ j₂ →
      (oppSign j₁).nonneg → (oppSign j₂).nonneg → (oppSign j).nonneg)
    (hconvNeg : ∀ (j₁ j₂ j : Fin n), j₁ ≤ j → j ≤ j₂ →
      (oppSign j₁).flip.nonneg → (oppSign j₂).flip.nonneg → (oppSign j).flip.nonneg)
    (c : Sign) (j₁ j₂ j : Fin n) (hlo : j₁ ≤ j) (hhi : j ≤ j₂)
    (h1 : (Sign.mul c (oppSign j₁)).nonneg) (h2 : (Sign.mul c (oppSign j₂)).nonneg) :
    (Sign.mul c (oppSign j)).nonneg := by
  cases c with
  | zero => simp only [Sign.zero_mul]; exact nonneg_zero
  | pos => simp only [Sign.pos_mul] at *; exact hconv j₁ j₂ j hlo hhi h1 h2
  | neg => simp only [Sign.neg_mul] at *; exact hconvNeg j₁ j₂ j hlo hhi h1 h2

theorem bilinearGame_opponentConvex (n : ℕ) (oppSign₀ oppSign₁ : Fin n → Sign)
    (hconv₀ : ∀ (j₁ j₂ j : Fin n), j₁ ≤ j → j ≤ j₂ →
      (oppSign₀ j₁).nonneg → (oppSign₀ j₂).nonneg → (oppSign₀ j).nonneg)
    (hconvNeg₀ : ∀ (j₁ j₂ j : Fin n), j₁ ≤ j → j ≤ j₂ →
      (oppSign₀ j₁).flip.nonneg → (oppSign₀ j₂).flip.nonneg → (oppSign₀ j).flip.nonneg)
    (hconv₁ : ∀ (j₁ j₂ j : Fin n), j₁ ≤ j → j ≤ j₂ →
      (oppSign₁ j₁).nonneg → (oppSign₁ j₂).nonneg → (oppSign₁ j).nonneg)
    (hconvNeg₁ : ∀ (j₁ j₂ j : Fin n), j₁ ≤ j → j ≤ j₂ →
      (oppSign₁ j₁).flip.nonneg → (oppSign₁ j₂).flip.nonneg → (oppSign₁ j).flip.nonneg) :
    OpponentConvex (bilinearGame n oppSign₀ oppSign₁) where
  conv₀ j₁ j₂ j a b hlo hhi h1 h2 := by
    simp only [bilinearGame] at *
    exact oppConvex_to_mul_convex hconv₀ hconvNeg₀ _ j₁ j₂ j hlo hhi h1 h2
  conv₁ j₁ j₂ j a b hlo hhi h1 h2 := by
    simp only [bilinearGame] at *
    exact oppConvex_to_mul_convex hconv₁ hconvNeg₁ _ j₁ j₂ j hlo hhi h1 h2

theorem BilinearTower.game_opponentConvex (t : BilinearTower) (k : ℕ) :
    OpponentConvex (t.game k) :=
  bilinearGame_opponentConvex _ _ _
    (t.oppConvex₀ k) (t.oppConvexNeg₀ k) (t.oppConvex₁ k) (t.oppConvexNeg₁ k)

-- ================================================================
-- Section 23: flip.nonneg interpolation
-- ================================================================

/-- Both flip-nonneg endpoints force the midpoint sign to be flip-nonneg. -/
private theorem forcedMidpoint_of_flip_nonneg {s1 s2 : Sign}
    (h1 : s1.flip.nonneg) (h2 : s2.flip.nonneg) :
    ∃ s, forcedMidpointSign s1 s2 = some s ∧ s.flip.nonneg := by
  cases s1 <;> cases s2 <;> simp [Sign.nonneg, Sign.flip, forcedMidpointSign] at *

/-- Bilinear tower: oppSign₀ flip.nonneg at all even points in [2c, 2d]
    implies flip.nonneg at all points in [2c, 2d]. -/
theorem BilinearTower.oppSign₀_flip_nonneg_interval {k : ℕ} (t : BilinearTower)
    {c d : Fin (gridSize k)}
    (h_even : ∀ (j : Fin (gridSize k)), c ≤ j → j ≤ d →
      (t.oppSign₀ (k + 1) (embed k j)).flip.nonneg)
    {j : Fin (gridSize (k + 1))} (hj_lo : embed k c ≤ j) (hj_hi : j ≤ embed k d) :
    (t.oppSign₀ (k + 1) j).flip.nonneg := by
  have hj_lo' : 2 * c.val ≤ j.val := by simp [Fin.le_iff_val_le_val] at hj_lo; omega
  have hj_hi' : j.val ≤ 2 * d.val := by simp [Fin.le_iff_val_le_val] at hj_hi; omega
  by_cases heven : j.val % 2 = 0
  · have hm : j.val / 2 < gridSize k := by grid_omega
    have hj_eq : j = embed k ⟨j.val / 2, hm⟩ := by ext; simp [embed_val]; omega
    rw [hj_eq]
    exact h_even ⟨j.val / 2, hm⟩
      (Fin.mk_le_mk.mpr (by omega)) (Fin.mk_le_mk.mpr (by omega))
  · have hm_lt : j.val / 2 < edgeCount k := by grid_omega
    have hj_eq : j = midpoint k ⟨j.val / 2, hm_lt⟩ := by ext; simp [midpoint_val]; omega
    rw [hj_eq]
    have hl := h_even ⟨j.val / 2, by grid_omega⟩
      (Fin.mk_le_mk.mpr (by omega)) (Fin.mk_le_mk.mpr (by omega))
    have hr_coarse := h_even ⟨j.val / 2 + 1, by grid_omega⟩
      (Fin.mk_le_mk.mpr (by omega)) (Fin.mk_le_mk.mpr (by omega))
    have hr_eq : embedRight k ⟨j.val / 2, hm_lt⟩ = embed k ⟨j.val / 2 + 1, by grid_omega⟩ := by
      ext; simp [embedRight_val, embed_val]; omega
    have hr : (t.oppSign₀ (k + 1) (embedRight k ⟨j.val / 2, hm_lt⟩)).flip.nonneg := by
      rw [hr_eq]; exact hr_coarse
    obtain ⟨s, hs, hs_nn⟩ := forcedMidpoint_of_flip_nonneg hl hr
    rw [t.interp₀ k ⟨j.val / 2, hm_lt⟩ s hs]
    exact hs_nn

/-- Symmetric version for oppSign₁. -/
theorem BilinearTower.oppSign₁_flip_nonneg_interval {k : ℕ} (t : BilinearTower)
    {c d : Fin (gridSize k)}
    (h_even : ∀ (j : Fin (gridSize k)), c ≤ j → j ≤ d →
      (t.oppSign₁ (k + 1) (embed k j)).flip.nonneg)
    {j : Fin (gridSize (k + 1))} (hj_lo : embed k c ≤ j) (hj_hi : j ≤ embed k d) :
    (t.oppSign₁ (k + 1) j).flip.nonneg := by
  have hj_lo' : 2 * c.val ≤ j.val := by simp [Fin.le_iff_val_le_val] at hj_lo; omega
  have hj_hi' : j.val ≤ 2 * d.val := by simp [Fin.le_iff_val_le_val] at hj_hi; omega
  by_cases heven : j.val % 2 = 0
  · have hm : j.val / 2 < gridSize k := by grid_omega
    have hj_eq : j = embed k ⟨j.val / 2, hm⟩ := by ext; simp [embed_val]; omega
    rw [hj_eq]
    exact h_even ⟨j.val / 2, hm⟩
      (Fin.mk_le_mk.mpr (by omega)) (Fin.mk_le_mk.mpr (by omega))
  · have hm_lt : j.val / 2 < edgeCount k := by grid_omega
    have hj_eq : j = midpoint k ⟨j.val / 2, hm_lt⟩ := by ext; simp [midpoint_val]; omega
    rw [hj_eq]
    have hl := h_even ⟨j.val / 2, by grid_omega⟩
      (Fin.mk_le_mk.mpr (by omega)) (Fin.mk_le_mk.mpr (by omega))
    have hr_coarse := h_even ⟨j.val / 2 + 1, by grid_omega⟩
      (Fin.mk_le_mk.mpr (by omega)) (Fin.mk_le_mk.mpr (by omega))
    have hr_eq : embedRight k ⟨j.val / 2, hm_lt⟩ = embed k ⟨j.val / 2 + 1, by grid_omega⟩ := by
      ext; simp [embedRight_val, embed_val]; omega
    have hr : (t.oppSign₁ (k + 1) (embedRight k ⟨j.val / 2, hm_lt⟩)).flip.nonneg := by
      rw [hr_eq]; exact hr_coarse
    obtain ⟨s, hs, hs_nn⟩ := forcedMidpoint_of_flip_nonneg hl hr
    rw [t.interp₁ k ⟨j.val / 2, hm_lt⟩ s hs]
    exact hs_nn

-- ================================================================
-- Section 24: Interval closure of embedded faces
-- ================================================================

section EmbedIntervalClosure

variable {k : ℕ}

/-- The min of an embedded face is the embedding of the min. -/
theorem faceMin_embedFace (F : Face (Fin (gridSize k))) :
    faceMin (embedFace k F) = embed k (faceMin F) := by
  apply Fin.ext
  simp only [faceMin, embedFace]
  apply le_antisymm
  · -- min of mapped set ≤ image of min
    apply Fin.val_le_of_le
    apply Finset.min'_le
    exact Finset.mem_map_of_mem _ (Finset.min'_mem F.1 F.2)
  · -- image of min ≤ min of mapped set
    have hmin := Finset.min'_mem (F.1.map ⟨embed k, embed_injective k⟩)
      (embedFace k F).2
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hmin
    obtain ⟨w, hw, heq⟩ := hmin
    rw [← heq]
    simp only [embed_val]
    have := Fin.val_le_of_le (Finset.min'_le F.1 w hw)
    omega

/-- The max of an embedded face is the embedding of the max. -/
theorem faceMax_embedFace (F : Face (Fin (gridSize k))) :
    faceMax (embedFace k F) = embed k (faceMax F) := by
  apply Fin.ext
  simp only [faceMax, embedFace]
  apply le_antisymm
  · -- max of mapped set ≤ image of max
    have hmax := Finset.max'_mem (F.1.map ⟨embed k, embed_injective k⟩)
      (embedFace k F).2
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hmax
    obtain ⟨w, hw, heq⟩ := hmax
    rw [← heq]
    simp only [embed_val]
    have := Fin.val_le_of_le (Finset.le_max' F.1 w hw)
    omega
  · -- image of max ≤ max of mapped set
    apply Fin.val_le_of_le
    apply Finset.le_max'
    exact Finset.mem_map_of_mem _ (Finset.max'_mem F.1 F.2)

/-- If σ.1 is interval-closed (i.e., σ.1 = intervalClosure σ.1), then
    v ∉ intervalClosure(embedFace σ.1) implies v/2 ∉ σ.1 or v is outside the range. -/
theorem not_mem_intervalClosure_embed
    {F : Face (Fin (gridSize k))}
    {v : Fin (gridSize (k + 1))} (hv : v ∉ (intervalClosure (embedFace k F)).1) :
    v.val < (embed k (faceMin F)).val ∨ v.val > (embed k (faceMax F)).val := by
  rw [mem_closure] at hv; push_neg at hv
  simp only [faceMin_embedFace, faceMax_embedFace] at hv
  by_contra h; push_neg at h
  have h1 : embed k (faceMin F) ≤ v := Fin.le_iff_val_le_val.mpr h.1
  exact absurd (Fin.le_iff_val_le_val.mpr h.2) (not_le.mpr (hv h1))

/-- For v in intervalClosure(embedFace F), ⌊v/2⌋ ∈ F when F is interval-closed. -/
theorem half_mem_of_mem_intervalClosure_embed
    {F : Face (Fin (gridSize k))} (h_cl : F = intervalClosure F)
    {v : Fin (gridSize (k + 1))} (hv : v ∈ (intervalClosure (embedFace k F)).1) :
    (⟨v.val / 2, by have := v.isLt; grid_omega⟩ : Fin (gridSize k)) ∈ F.1 := by
  rw [mem_closure] at hv
  simp [faceMin_embedFace, faceMax_embedFace, embed_val, Fin.le_iff_val_le_val] at hv
  -- v.val is in [2 * (faceMin F).val, 2 * (faceMax F).val]
  -- so v.val / 2 is in [(faceMin F).val, (faceMax F).val]
  -- Since F is interval-closed, this means v/2 ∈ F
  have hv_half_ge : (faceMin F).val ≤ v.val / 2 := by omega
  have hv_half_le : v.val / 2 ≤ (faceMax F).val := by omega
  have h_mem_cl : (⟨v.val / 2, by have := v.isLt; grid_omega⟩ : Fin (gridSize k)) ∈
      (intervalClosure F).1 := by
    rw [mem_closure]
    exact ⟨Fin.mk_le_mk.mpr hv_half_ge, Fin.mk_le_mk.mpr hv_half_le⟩
  rwa [← h_cl] at h_mem_cl

/-- intervalClosure(embedFace F) refines F when F is interval-closed. -/
theorem intervalClosure_embedFace_refines
    {F : Face (Fin (gridSize k))} (h_cl : F = intervalClosure F) :
    FaceRefines (intervalClosure (embedFace k F)) F :=
  fun _v hv => half_mem_of_mem_intervalClosure_embed h_cl hv

end EmbedIntervalClosure

-- ================================================================
-- Section 25: OD transfer for bilinear tower
-- ================================================================

section BilinearODTransfer

variable (t : BilinearTower)

/-- Helper: coarse OD₀ + v below min of σ.1 → oppSign₀ nonneg on σ.2.
    The bilinear sign₀(j, w, v) = mul(cmpSign v w)(oppSign₀ j).
    When v < w, cmpSign v w = pos, so nonneg ↔ oppSign₀ j nonneg. -/
private theorem oppSign₀_nonneg_of_OD_below {k : ℕ}
    {σ : Face (Fin (gridSize k)) × Face (Fin (gridSize k))}
    (hOD : (t.game k).OutsideDominated₀ σ)
    {v : Fin (gridSize k)} (hv : v ∉ σ.1.1)
    (hv_lt : v < faceMin σ.1) (j : Fin (gridSize k)) (hj : j ∈ σ.2.1) :
    (t.oppSign₀ k j).nonneg := by
  have h := hOD v hv (faceMin σ.1) (faceMin_mem σ.1) (faceMin σ.1)
    (Finset.mem_singleton_self _) j hj v (Finset.mem_singleton_self _)
  change (Sign.mul (cmpSign v.val (faceMin σ.1).val) (t.oppSign₀ k j)).nonneg at h
  have hv_val : v.val < (faceMin σ.1).val := hv_lt
  have hcmp : cmpSign v.val (faceMin σ.1).val = Sign.pos := by
    simp only [cmpSign, hv_val, ↓reduceIte]
  rw [hcmp, Sign.pos_mul] at h
  exact h

/-- Helper: coarse OD₀ + v above max of σ.1 → oppSign₀ flip.nonneg on σ.2. -/
private theorem oppSign₀_flip_nonneg_of_OD_above {k : ℕ}
    {σ : Face (Fin (gridSize k)) × Face (Fin (gridSize k))}
    (hOD : (t.game k).OutsideDominated₀ σ)
    {v : Fin (gridSize k)} (hv : v ∉ σ.1.1)
    (hv_gt : faceMax σ.1 < v) (j : Fin (gridSize k)) (hj : j ∈ σ.2.1) :
    (t.oppSign₀ k j).flip.nonneg := by
  have hw := faceMax_mem σ.1
  have h := hOD v hv (faceMax σ.1) hw (faceMax σ.1)
    (Finset.mem_singleton_self _) j hj v (Finset.mem_singleton_self _)
  change (Sign.mul (cmpSign v.val (faceMax σ.1).val) (t.oppSign₀ k j)).nonneg at h
  have hv_val : (faceMax σ.1).val < v.val := hv_gt
  have h1 : ¬(v.val < (faceMax σ.1).val) := by omega
  have hcmp : cmpSign v.val (faceMax σ.1).val = Sign.neg := by
    simp only [cmpSign, h1, hv_val, ↓reduceIte]
  rw [hcmp, Sign.neg_mul] at h
  exact h

/-- Main OD transfer: OutsideDominated₀ at coarse level transfers to
    OutsideDominated₀ at intervalClosure(embed(σ)) at the fine level,
    for bilinear towers with interval-closed profiles. -/
theorem BilinearTower.OD₀_embed_intervalClosure {k : ℕ}
    {σ : Face (Fin (gridSize k)) × Face (Fin (gridSize k))}
    (hOD : (t.game k).OutsideDominated₀ σ)
    (_h_cl₁ : σ.1 = intervalClosure σ.1)
    (h_cl₂ : σ.2 = intervalClosure σ.2) :
    (t.game (k + 1)).OutsideDominated₀
      (intervalClosure (embedFace k σ.1), intervalClosure (embedFace k σ.2)) := by
  -- OD₀ at fine level with interval-closed embedded profile
  -- Reduce to oppSign₀ conditions via bilinear factorization
  intro v₁ hv₁ w₁ hw₁ a ha j hj b hb
  simp [Face.vertex, Finset.mem_singleton] at ha hb; subst ha; subst hb
  -- After subst: v₁→b (outside cl(embed σ.1)), w₁→a (inside), j ∈ cl(embed σ.2)
  -- Goal: (mul (cmpSign b.val a.val) (oppSign₀ (k+1) j)).nonneg
  simp only [game, bilinearGame]
  have hb_range := not_mem_intervalClosure_embed hv₁
  have ha_lo : 2 * (faceMin σ.1).val ≤ a.val := by
    rw [mem_closure] at hw₁
    simp only [faceMin_embedFace] at hw₁
    exact Fin.val_le_of_le hw₁.1
  have ha_hi : a.val ≤ 2 * (faceMax σ.1).val := by
    rw [mem_closure] at hw₁
    simp only [faceMax_embedFace] at hw₁
    exact Fin.val_le_of_le hw₁.2
  have hj_range : embed k (faceMin σ.2) ≤ j ∧ j ≤ embed k (faceMax σ.2) := by
    rw [mem_closure] at hj; simp [faceMin_embedFace, faceMax_embedFace] at hj; exact hj
  cases hb_range with
  | inl hb_below =>
    have hb_lt : b.val < 2 * (faceMin σ.1).val := by simp [embed_val] at hb_below; omega
    have hba : b.val < a.val := by omega
    have hcmp : cmpSign b.val a.val = Sign.pos := by
      simp only [cmpSign, hba, ↓reduceIte]
    rw [hcmp, Sign.pos_mul]
    have hmin_pos : 0 < (faceMin σ.1).val := by omega
    have hmin_pred_lt : (faceMin σ.1).val - 1 < gridSize k := by omega
    set coarseBelow : Fin (gridSize k) := ⟨(faceMin σ.1).val - 1, hmin_pred_lt⟩ with hcb_def
    have hcb_val : coarseBelow.val = (faceMin σ.1).val - 1 := rfl
    have hcb_not_mem : coarseBelow ∉ σ.1.1 := by
      intro hmem; have := Fin.val_le_of_le (faceMin_le σ.1 hmem); omega
    have hcb_below : coarseBelow < faceMin σ.1 := by
      simp [Fin.lt_def, hcb_val]; omega
    have h_nn_even : ∀ j' : Fin (gridSize k),
        faceMin σ.2 ≤ j' → j' ≤ faceMax σ.2 →
        (t.oppSign₀ (k + 1) (embed k j')).nonneg := by
      intro j' hlo hhi; rw [t.coherent₀]
      exact oppSign₀_nonneg_of_OD_below t hOD hcb_not_mem hcb_below j'
        (by rw [h_cl₂]; exact mem_closure.mpr ⟨hlo, hhi⟩)
    exact t.oppSign₀_nonneg_interval h_nn_even hj_range.1 hj_range.2
  | inr hb_above =>
    have hb_gt : b.val > 2 * (faceMax σ.1).val := by simp [embed_val] at hb_above; omega
    have hab : a.val < b.val := by omega
    have hcmp : cmpSign b.val a.val = Sign.neg := by
      have h1 : ¬(b.val < a.val) := by omega
      simp only [cmpSign, h1, hab, ↓reduceIte]
    rw [hcmp, Sign.neg_mul]
    -- Use faceMax + 1 as the coarse outside point
    have hmax_succ_lt : (faceMax σ.1).val + 1 < gridSize k := by
      have := b.isLt; grid_omega
    set coarseOut₀ : Fin (gridSize k) := ⟨(faceMax σ.1).val + 1, hmax_succ_lt⟩ with hco₀_def
    have hco₀_val : coarseOut₀.val = (faceMax σ.1).val + 1 := rfl
    have hco_not_mem : coarseOut₀ ∉ σ.1.1 := by
      intro hmem; have := Fin.val_le_of_le (le_faceMax σ.1 hmem); omega
    have hco_above : faceMax σ.1 < coarseOut₀ := by
      simp [Fin.lt_def, hco₀_val]
    have h_nn_even : ∀ j' : Fin (gridSize k),
        faceMin σ.2 ≤ j' → j' ≤ faceMax σ.2 →
        (t.oppSign₀ (k + 1) (embed k j')).flip.nonneg := by
      intro j' hlo hhi; rw [t.coherent₀]
      exact oppSign₀_flip_nonneg_of_OD_above t hOD hco_not_mem hco_above j'
        (by rw [h_cl₂]; exact mem_closure.mpr ⟨hlo, hhi⟩)
    exact t.oppSign₀_flip_nonneg_interval h_nn_even hj_range.1 hj_range.2

/-- Helper for OD₁: coarse OD₁ + v below min of σ.2 → oppSign₁ nonneg on σ.1. -/
private theorem oppSign₁_nonneg_of_OD_below {k : ℕ}
    {σ : Face (Fin (gridSize k)) × Face (Fin (gridSize k))}
    (hOD : (t.game k).OutsideDominated₁ σ)
    {v : Fin (gridSize k)} (hv : v ∉ σ.2.1)
    (hv_lt : v < faceMin σ.2) (j : Fin (gridSize k)) (hj : j ∈ σ.1.1) :
    (t.oppSign₁ k j).nonneg := by
  have h := hOD v hv (faceMin σ.2) (faceMin_mem σ.2) (faceMin σ.2)
    (Finset.mem_singleton_self _) j hj v (Finset.mem_singleton_self _)
  change (Sign.mul (cmpSign v.val (faceMin σ.2).val) (t.oppSign₁ k j)).nonneg at h
  have hv_val : v.val < (faceMin σ.2).val := hv_lt
  have hcmp : cmpSign v.val (faceMin σ.2).val = Sign.pos := by
    simp only [cmpSign, hv_val, ↓reduceIte]
  rw [hcmp, Sign.pos_mul] at h
  exact h

/-- Helper for OD₁: coarse OD₁ + v above max of σ.2 → oppSign₁ flip.nonneg on σ.1. -/
private theorem oppSign₁_flip_nonneg_of_OD_above {k : ℕ}
    {σ : Face (Fin (gridSize k)) × Face (Fin (gridSize k))}
    (hOD : (t.game k).OutsideDominated₁ σ)
    {v : Fin (gridSize k)} (hv : v ∉ σ.2.1)
    (hv_gt : faceMax σ.2 < v) (j : Fin (gridSize k)) (hj : j ∈ σ.1.1) :
    (t.oppSign₁ k j).flip.nonneg := by
  have h := hOD v hv (faceMax σ.2) (faceMax_mem σ.2) (faceMax σ.2)
    (Finset.mem_singleton_self _) j hj v (Finset.mem_singleton_self _)
  change (Sign.mul (cmpSign v.val (faceMax σ.2).val) (t.oppSign₁ k j)).nonneg at h
  have hv_val : (faceMax σ.2).val < v.val := hv_gt
  have h1 : ¬(v.val < (faceMax σ.2).val) := by omega
  have hcmp : cmpSign v.val (faceMax σ.2).val = Sign.neg := by
    simp only [cmpSign, h1, hv_val, ↓reduceIte]
  rw [hcmp, Sign.neg_mul] at h
  exact h

/-- Symmetric version for OD₁. -/
theorem BilinearTower.OD₁_embed_intervalClosure {k : ℕ}
    {σ : Face (Fin (gridSize k)) × Face (Fin (gridSize k))}
    (hOD : (t.game k).OutsideDominated₁ σ)
    (h_cl₁ : σ.1 = intervalClosure σ.1)
    (_h_cl₂ : σ.2 = intervalClosure σ.2) :
    (t.game (k + 1)).OutsideDominated₁
      (intervalClosure (embedFace k σ.1), intervalClosure (embedFace k σ.2)) := by
  -- OD₁: ∀ v ∉ cl(embed σ.2), w ∈ cl(embed σ.2),
  --   DevFaceLE₁ cl(embed σ.1) (vertex w) (vertex v)
  -- DevFaceLE₁: ∀ a ∈ {w}, j ∈ cl(embed σ.1), b ∈ {v}, sign₁(j, w, v).nonneg
  -- In bilinear game: sign₁(j, w, v) = mul(cmpSign v w)(oppSign₁ j)
  -- After intro + vertex simp + subst:
  -- v→b (the "outside" point), w→a (the "inside" point), j→j_opp
  intro v₀ hv₀ w₀ hw₀ a ha j_opp hj_opp b hb
  simp [Face.vertex, Finset.mem_singleton] at ha hb
  subst ha; subst hb
  -- Now: a = w₀ (inside cl(embed σ.2)), b = v₀ (outside), j_opp ∈ cl(embed σ.1)
  -- Goal: (mul (cmpSign b.val a.val) (oppSign₁ (k+1) j_opp)).nonneg
  simp only [game, bilinearGame]
  have hb_range := not_mem_intervalClosure_embed (k := k) hv₀
  have hj_range : embed k (faceMin σ.1) ≤ j_opp ∧ j_opp ≤ embed k (faceMax σ.1) := by
    rw [mem_closure] at hj_opp
    simp [faceMin_embedFace, faceMax_embedFace] at hj_opp
    exact hj_opp
  cases hb_range with
  | inl hb_below =>
    -- b.val < 2 * (faceMin σ.2).val ≤ a.val, so cmpSign b a = pos
    have hb_lt : b.val < 2 * (faceMin σ.2).val := by simp [embed_val] at hb_below; omega
    have ha_lo : 2 * (faceMin σ.2).val ≤ a.val := by
      rw [mem_closure] at hw₀
      simp only [faceMin_embedFace] at hw₀
      exact Fin.val_le_of_le hw₀.1
    have hba : b.val < a.val := by omega
    have hcmp : cmpSign b.val a.val = Sign.pos := by
      simp only [cmpSign, hba, ↓reduceIte]
    rw [hcmp, Sign.pos_mul]
    -- Use faceMin - 1 as the coarse outside point
    have hmin_pos : 0 < (faceMin σ.2).val := by omega
    have hmin_pred_lt : (faceMin σ.2).val - 1 < gridSize k := by omega
    set coarseBelow : Fin (gridSize k) := ⟨(faceMin σ.2).val - 1, hmin_pred_lt⟩ with hcb_def
    have hcb_val : coarseBelow.val = (faceMin σ.2).val - 1 := rfl
    have hcb_not_mem : coarseBelow ∉ σ.2.1 := by
      intro hmem; have := Fin.val_le_of_le (faceMin_le σ.2 hmem); omega
    have hcb_below : coarseBelow < faceMin σ.2 := by
      simp [Fin.lt_def, hcb_val]; omega
    have h_nn_coarse : ∀ j' : Fin (gridSize k), j' ∈ σ.1.1 →
        (t.oppSign₁ k j').nonneg :=
      fun j' hj' => oppSign₁_nonneg_of_OD_below t hOD hcb_not_mem hcb_below j' hj'
    have h_nn_even : ∀ j' : Fin (gridSize k),
        faceMin σ.1 ≤ j' → j' ≤ faceMax σ.1 →
        (t.oppSign₁ (k + 1) (embed k j')).nonneg := by
      intro j' hlo hhi; rw [t.coherent₁]
      exact h_nn_coarse j' (by rw [h_cl₁]; exact mem_closure.mpr ⟨hlo, hhi⟩)
    exact t.oppSign₁_nonneg_interval h_nn_even hj_range.1 hj_range.2
  | inr hb_above =>
    -- b.val > 2 * (faceMax σ.2).val ≥ a.val, so cmpSign b a = neg
    have ha_hi : a.val ≤ 2 * (faceMax σ.2).val := by
      rw [mem_closure] at hw₀
      simp only [faceMax_embedFace] at hw₀
      exact Fin.val_le_of_le hw₀.2
    have hb_gt : b.val > 2 * (faceMax σ.2).val := by simp [embed_val] at hb_above; omega
    have hab : a.val < b.val := by omega
    have hcmp : cmpSign b.val a.val = Sign.neg := by
      have h1 : ¬(b.val < a.val) := by omega
      simp only [cmpSign, h1, hab, ↓reduceIte]
    rw [hcmp, Sign.neg_mul]
    -- Use faceMax + 1 as the coarse outside point (avoids integer division boundary issue)
    have hmax_succ_lt : (faceMax σ.2).val + 1 < gridSize k := by
      have := b.isLt; grid_omega
    set coarseOut : Fin (gridSize k) := ⟨(faceMax σ.2).val + 1, hmax_succ_lt⟩ with hco_def
    have hco_val : coarseOut.val = (faceMax σ.2).val + 1 := rfl
    have hco_not_mem : coarseOut ∉ σ.2.1 := by
      intro hmem; have := Fin.val_le_of_le (le_faceMax σ.2 hmem); omega
    have hco_above : faceMax σ.2 < coarseOut := by
      simp [Fin.lt_def, hco_val]
    have h_nn_coarse : ∀ j' : Fin (gridSize k), j' ∈ σ.1.1 →
        (t.oppSign₁ k j').flip.nonneg :=
      fun j' hj' => oppSign₁_flip_nonneg_of_OD_above t hOD hco_not_mem hco_above j' hj'
    have h_nn_even : ∀ j' : Fin (gridSize k),
        faceMin σ.1 ≤ j' → j' ≤ faceMax σ.1 →
        (t.oppSign₁ (k + 1) (embed k j')).flip.nonneg := by
      intro j' hlo hhi; rw [t.coherent₁]
      exact h_nn_coarse j' (by rw [h_cl₁]; exact mem_closure.mpr ⟨hlo, hhi⟩)
    exact t.oppSign₁_flip_nonneg_interval h_nn_even hj_range.1 hj_range.2

end BilinearODTransfer

-- ================================================================
-- Section 26: Interval closure helpers for the main theorem
-- ================================================================

/-- If F ⊆ G, then faceMin G ≤ faceMin F (smaller set has larger min). -/
theorem faceMin_le_of_sub {F G : Face (Fin n)}
    (h : Face.IsSubface F G) : faceMin G ≤ faceMin F := by
  exact faceMin_le G (h (faceMin_mem F))

/-- If F ⊆ G, then faceMax F ≤ faceMax G (smaller set has smaller max). -/
theorem faceMax_le_of_sub {F G : Face (Fin n)}
    (h : Face.IsSubface F G) : faceMax F ≤ faceMax G := by
  exact le_faceMax G (h (faceMax_mem F))

/-- intervalClosure is idempotent. -/
theorem faceMin_intervalClosure (F : Face (Fin n)) :
    faceMin (intervalClosure F) = faceMin F := by
  apply le_antisymm
  · exact faceMin_le (intervalClosure F) (face_sub_closure F (faceMin_mem F))
  · exact (mem_closure.mp (faceMin_mem (intervalClosure F))).1

theorem faceMax_intervalClosure (F : Face (Fin n)) :
    faceMax (intervalClosure F) = faceMax F := by
  apply le_antisymm
  · exact (mem_closure.mp (faceMax_mem (intervalClosure F))).2
  · exact le_faceMax (intervalClosure F) (face_sub_closure F (faceMax_mem F))

theorem intervalClosure_idempotent (F : Face (Fin n)) :
    intervalClosure (intervalClosure F) = intervalClosure F := by
  apply Face.ext; ext v
  simp only [mem_closure, faceMin_intervalClosure, faceMax_intervalClosure]

/-- If F ⊆ G and G is interval-closed, then intervalClosure F ⊆ G. -/
theorem intervalClosure_sub_of_sub_closed {F G : Face (Fin n)}
    (h_sub : Face.IsSubface F G) (h_cl : G = intervalClosure G) :
    Face.IsSubface (intervalClosure F) G := by
  intro v hv
  rw [mem_closure] at hv
  rw [h_cl]
  exact mem_closure.mpr
    ⟨le_trans (faceMin_le_of_sub h_sub) hv.1,
     le_trans hv.2 (faceMax_le_of_sub h_sub)⟩

-- ================================================================
-- Section 27: Main Nash refining sequence theorem
-- ================================================================

variable {t : BilinearTower}

/-- At every level k, there exists a Nash equilibrium that is
    OutsideDominated and interval-closed. -/
theorem BilinearTower.nash_refining_sequence (t : BilinearTower) :
    ∀ k, ∃ σ : Face (Fin (gridSize k)) × Face (Fin (gridSize k)),
      (t.game k).IsNash σ ∧
      (t.game k).OutsideDominated₀ σ ∧
      (t.game k).OutsideDominated₁ σ ∧
      σ.1 = intervalClosure σ.1 ∧
      σ.2 = intervalClosure σ.2 := by
  intro k; induction k with
  | zero =>
    -- Base case: start from full face, descend to Nash + OD, then interval-close
    have hfull₀ := (t.game 0).OutsideDominated₀_maximal
    have hfull₁ := (t.game 0).OutsideDominated₁_maximal
    obtain ⟨τ, hN, _, _, hOD₀, hOD₁⟩ := (t.game 0).nash_exists_sub_OD
      (@Face.full _ _ _ (gridSize_nonempty 0), @Face.full _ _ _ (gridSize_nonempty 0))
      hfull₀ hfull₁
    let τ_cl : Face (Fin (gridSize 0)) × Face (Fin (gridSize 0)) :=
      (intervalClosure τ.1, intervalClosure τ.2)
    have hgm := t.game_gridMonotone 0
    have hoc := t.game_opponentConvex 0
    exact ⟨τ_cl,
      IsNash_intervalClosure hgm hoc hN,
      OutsideDominated₀_intervalClosure hgm hoc hOD₀,
      OutsideDominated₁_intervalClosure hgm hoc hOD₁,
      (intervalClosure_idempotent τ.1).symm,
      (intervalClosure_idempotent τ.2).symm⟩
  | succ k ih =>
    -- Inductive step: embed σ_k, interval-close, descend, interval-close again
    obtain ⟨σ_k, hN_k, hOD₀_k, hOD₁_k, hcl₁_k, hcl₂_k⟩ := ih
    -- Step 1: Embed and interval-close
    let σ_cl : Face (Fin (gridSize (k + 1))) × Face (Fin (gridSize (k + 1))) :=
      (intervalClosure (embedFace k σ_k.1), intervalClosure (embedFace k σ_k.2))
    -- Step 2: OD at σ_cl via the transfer theorems
    have hOD₀_cl : (t.game (k + 1)).OutsideDominated₀ σ_cl :=
      t.OD₀_embed_intervalClosure hOD₀_k hcl₁_k hcl₂_k
    have hOD₁_cl : (t.game (k + 1)).OutsideDominated₁ σ_cl :=
      t.OD₁_embed_intervalClosure hOD₁_k hcl₁_k hcl₂_k
    -- Step 3: Descend from σ_cl to Nash + OD
    obtain ⟨τ, hN_τ, hτ₁_sub, hτ₂_sub, hOD₀_τ, hOD₁_τ⟩ :=
      (t.game (k + 1)).nash_exists_sub_OD σ_cl hOD₀_cl hOD₁_cl
    -- Step 4: Interval-close τ
    let τ_cl : Face (Fin (gridSize (k + 1))) × Face (Fin (gridSize (k + 1))) :=
      (intervalClosure τ.1, intervalClosure τ.2)
    have hgm := t.game_gridMonotone (k + 1)
    have hoc := t.game_opponentConvex (k + 1)
    exact ⟨τ_cl,
      IsNash_intervalClosure hgm hoc hN_τ,
      OutsideDominated₀_intervalClosure hgm hoc hOD₀_τ,
      OutsideDominated₁_intervalClosure hgm hoc hOD₁_τ,
      (intervalClosure_idempotent τ.1).symm,
      (intervalClosure_idempotent τ.2).symm⟩

/-- At every level k, there exists a Nash equilibrium at level k+1 that refines
    a Nash equilibrium at level k. -/
theorem BilinearTower.nash_at_next_level_refines (t : BilinearTower) (k : ℕ) :
    ∃ σ : Face (Fin (gridSize k)) × Face (Fin (gridSize k)),
    ∃ σ' : Face (Fin (gridSize (k + 1))) × Face (Fin (gridSize (k + 1))),
      (t.game k).IsNash σ ∧
      (t.game (k + 1)).IsNash σ' ∧
      ProfileRefines σ' σ := by
  obtain ⟨σ_k, hN_k, hOD₀_k, hOD₁_k, hcl₁_k, hcl₂_k⟩ := t.nash_refining_sequence k
  -- Embed σ_k, interval-close, get OD, descend to Nash
  let σ_cl : Face (Fin (gridSize (k + 1))) × Face (Fin (gridSize (k + 1))) :=
    (intervalClosure (embedFace k σ_k.1), intervalClosure (embedFace k σ_k.2))
  have hOD₀_cl := t.OD₀_embed_intervalClosure hOD₀_k hcl₁_k hcl₂_k
  have hOD₁_cl := t.OD₁_embed_intervalClosure hOD₁_k hcl₁_k hcl₂_k
  obtain ⟨τ, hN_τ, hτ₁_sub, hτ₂_sub, _, _⟩ :=
    (t.game (k + 1)).nash_exists_sub_OD σ_cl hOD₀_cl hOD₁_cl
  exact ⟨σ_k, τ, hN_k, hN_τ,
    FaceRefines_mono hτ₁_sub (intervalClosure_embedFace_refines hcl₁_k),
    FaceRefines_mono hτ₂_sub (intervalClosure_embedFace_refines hcl₂_k)⟩

end Unified
