import DiscreteGameTheory.Base
import DiscreteGameTheory.Refinement
import DiscreteGameTheory.CompactGame

/-!
# Grid Tower — Concrete grid constructions and examples

Instantiates the abstract `SignTower` on dyadic refinement grids (`Fin (2^k + 1)`),
where betweenness is the natural order on `Fin n`.

## Main definitions

* `finBetweenness`: natural-order betweenness on `Fin n`
* `gridSize`, `gridEmbed`, `gridMidpoint`: dyadic refinement grid infrastructure
* `gridSignGame`: 2-player sign game from per-player opponent-sign functions
* `GridTower`: input data (opponent signs + axioms) for constructing a `SignTower (Fin 2)`
* `GridTower.toSignTower`: the main construction, verifying all `SignTower` axioms
* `pdTower`, `mpTower`, `symCoordTower`, `bosTower`: four canonical 2-player towers
* `leftChild`, `rightChild`: binary subdivision for self-similarity
* `compactMP`, `metaMP`, `lowerIsBetter`, `mpNat`: compact game examples

## Main results

* `affine_preserves_oppSign`: positive scaling preserves tower signs
* `counterexample_level2`: non-affine transform breaks level-2 signs
-/

open Base
open Base.SignGame (Dominates OutsideDom)
open Refinement

-- ================================================================
-- Finite grid betweenness and grid arithmetic
-- ================================================================

/-- Natural-order betweenness on `Fin n`: c is between a and b iff
    min(a,b) ≤ c ≤ max(a,b). This is the concrete betweenness used
    by all grid tower constructions. -/
instance finBetweenness (n : ℕ) : Betweenness (Fin n) where
  between c a b := min a b ≤ c ∧ c ≤ max a b
  between_refl_left a b := ⟨min_le_left a b, le_max_left a b⟩
  between_refl_right a b := ⟨min_le_right a b, le_max_right a b⟩
  between_symm a b _c h := ⟨min_comm a b ▸ h.1, max_comm a b ▸ h.2⟩
  between_self a _c h := le_antisymm (le_trans h.2 (max_le (le_refl a) (le_refl a)))
    (le_trans (le_min (le_refl a) (le_refl a)) h.1)
  between_dec _ _ _ := inferInstance

section FinGrid

/-- Grid size at level k: 2^k + 1 points discretizing [0,1].
    Grid point j represents the probability j/2^k. -/
abbrev gridSize (k : ℕ) : ℕ := 2 ^ k + 1

abbrev edgeCount (k : ℕ) : ℕ := 2 ^ k

/-- Unfolds `2^(k+1) = 2 * 2^k` so `omega` can handle grid bounds. -/
macro "grid_omega" : tactic =>
  `(tactic| (simp only [gridSize, edgeCount, Nat.pow_succ, Nat.mul_comm] at *; omega))

/-- Embed level-k grid point into level-(k+1): j ↦ 2j (preserves j/2^k = 2j/2^(k+1)). -/
def gridEmbed (k : ℕ) (j : Fin (gridSize k)) : Fin (gridSize (k + 1)) :=
  ⟨2 * j.val, by grid_omega⟩

lemma gridEmbed_injective (k : ℕ) : Function.Injective (gridEmbed k) := by
  intro a b h; simp [gridEmbed, Fin.ext_iff] at h; exact Fin.ext (by omega)

@[simp] lemma gridEmbed_val (k : ℕ) (j : Fin (gridSize k)) :
    (gridEmbed k j).val = 2 * j.val := rfl

/-- Midpoint between adjacent embedded points: edge j maps to fine point 2j+1. -/
def gridMidpoint (k : ℕ) (j : Fin (edgeCount k)) : Fin (gridSize (k + 1)) :=
  ⟨2 * j.val + 1, by grid_omega⟩

@[simp] lemma gridMidpoint_val (k : ℕ) (j : Fin (edgeCount k)) :
    (gridMidpoint k j).val = 2 * j.val + 1 := rfl

def gridEmbedRight (k : ℕ) (j : Fin (edgeCount k)) : Fin (gridSize (k + 1)) :=
  gridEmbed k ⟨j.val + 1, by grid_omega⟩

@[simp] lemma gridEmbedRight_val (k : ℕ) (j : Fin (edgeCount k)) :
    (gridEmbedRight k j).val = 2 * j.val + 2 := by
  simp [gridEmbedRight, gridEmbed_val]; omega

lemma gridEmbed_between (k : ℕ) (a b c : Fin (gridSize k))
    (h : (finBetweenness (gridSize k)).between c a b) :
    (finBetweenness (gridSize (k+1))).between (gridEmbed k c) (gridEmbed k a) (gridEmbed k b) := by
  simp only [finBetweenness] at *
  obtain ⟨hlo, hhi⟩ := h
  have hlo_v : min a.val b.val ≤ c.val := by
    rw [← Fin.coe_min]; exact Fin.val_le_of_le hlo
  have hhi_v : c.val ≤ max a.val b.val := by
    rw [← Fin.coe_max]; exact Fin.val_le_of_le hhi
  constructor <;> {
    rw [Fin.le_def]
    simp only [Fin.coe_min, Fin.coe_max, gridEmbed_val]
    omega
  }

lemma fine_between_gridEmbed (k : ℕ) (v : Fin (gridSize (k+1))) (a : Fin (gridSize k)) :
    ∃ b : Fin (gridSize k),
      (finBetweenness (gridSize (k+1))).between v (gridEmbed k a) (gridEmbed k b) := by
  simp only [finBetweenness]
  by_cases h : v.val ≤ 2 * a.val
  · refine ⟨⟨0, by grid_omega⟩, ?_⟩
    constructor <;> {
      rw [Fin.le_def]
      simp only [Fin.coe_min, Fin.coe_max, gridEmbed_val]
      omega
    }
  · push_neg at h
    refine ⟨⟨gridSize k - 1, by grid_omega⟩, ?_⟩
    constructor <;> {
      rw [Fin.le_def]
      simp only [Fin.coe_min, Fin.coe_max, gridEmbed_val]
      have := v.isLt
      grid_omega
    }

instance gridSize_inhabited (k : ℕ) : Inhabited (Fin (gridSize k)) :=
  ⟨⟨0, Nat.succ_pos _⟩⟩

instance gridSize_nonempty (k : ℕ) : Nonempty (Fin (gridSize k)) := ⟨default⟩

end FinGrid

-- ================================================================
-- Grid sign game
-- ================================================================

private lemma mul_cmpSign_trans {a b c : ℕ} {s : Sign}
    (h1 : (Sign.mul (cmpSign b a) s).nonneg)
    (h2 : (Sign.mul (cmpSign c b) s).nonneg) :
    (Sign.mul (cmpSign c a) s).nonneg := by
  cases s with
  | zero => simp only [Sign.mul_zero]; exact Sign.nonneg_zero
  | pos =>
    simp only [Sign.mul_pos] at *
    exact cmpSign_trans h2 h1
  | neg =>
    simp only [Sign.mul, Sign.flip, cmpSign, Sign.nonneg] at *
    split_ifs at * <;> simp_all <;> omega

/-- A 2-player sign game on `Fin n` where each player's preference between actions
    a and b factorizes as: which action has higher index (`cmpSign b a`) times a
    sign depending on the opponent's position (`oppSign`). The opponent sign
    determines *which direction* of mixing is favorable. -/
def gridSignGame (n : ℕ) (oppSign : Fin 2 → Fin n → Sign) :
    Base.SignGame (Fin 2) (fun _ : Fin 2 => Fin n) where
  sign i p a b :=
    Sign.mul (cmpSign b.val a.val) (oppSign i (p (1 - i)))
  sign_refl i p a := by simp [cmpSign_self]
  sign_antisym i p a b := by simp [Sign.flip_mul, cmpSign_flip]
  sign_trans i p a b c h1 h2 := mul_cmpSign_trans h1 h2
  sign_irrel i p q a b h := by
    have hopp : p (1 - i) = q (1 - i) :=
      h (1 - i) (by intro heq; exact absurd heq (by omega))
    simp only [hopp]

-- ================================================================
-- Interpolation infrastructure
-- ================================================================

/-- When both endpoint signs agree, the midpoint is forced to match.
    When they disagree (a sign change), the midpoint is unconstrained (none). -/
def forcedMidpointSign : Sign → Sign → Option Sign
  | .pos, .pos => some .pos
  | .neg, .neg => some .neg
  | .zero, .zero => some .zero
  | .pos, .zero => some .pos
  | .zero, .pos => some .pos
  | .neg, .zero => some .neg
  | .zero, .neg => some .neg
  | .pos, .neg => none
  | .neg, .pos => none

private lemma forcedMidpoint_of_nonneg_nonneg {s1 s2 : Sign}
    (h1 : s1.nonneg) (h2 : s2.nonneg) :
    ∃ s, forcedMidpointSign s1 s2 = some s ∧ s.nonneg := by
  cases s1 <;> cases s2 <;> simp [Sign.nonneg, forcedMidpointSign] at *

private lemma forcedMidpoint_of_flip_nonneg {s1 s2 : Sign}
    (h1 : s1.flip.nonneg) (h2 : s2.flip.nonneg) :
    ∃ s, forcedMidpointSign s1 s2 = some s ∧ s.flip.nonneg := by
  cases s1 <;> cases s2 <;> simp [Sign.nonneg, Sign.flip, forcedMidpointSign] at *

-- ================================================================
-- GridTower: input data for grid-based sign towers
-- ================================================================

/-- Input data for constructing a `SignTower (Fin 2)` on dyadic grids.

    A grid tower is determined by per-player opponent-sign functions `oppSign i k j`
    giving the sign at grid point j of level k for player i's opponent. The axioms:
    - **coherent**: embedded points keep their coarse signs
    - **interp**: midpoint signs are forced when both neighbors agree
    - **oppConvex/oppConvexNeg**: opponent signs are interval-convex (both for
      nonneg and flip-nonneg), ensuring the `opponentConvex` axiom of `SignTower` -/
structure GridTower where
  oppSign : Fin 2 → (k : ℕ) → Fin (gridSize k) → Sign
  coherent : ∀ (i : Fin 2) k (j : Fin (gridSize k)),
    oppSign i (k + 1) (gridEmbed k j) = oppSign i k j
  interp : ∀ (i : Fin 2) k (j : Fin (edgeCount k)),
    ∀ s, forcedMidpointSign (oppSign i (k + 1) (gridEmbed k ⟨j, by grid_omega⟩))
                             (oppSign i (k + 1) (gridEmbedRight k j)) = some s →
    oppSign i (k + 1) (gridMidpoint k j) = s
  oppConvex : ∀ (i : Fin 2) k (j₁ j₂ j : Fin (gridSize k)),
    j₁ ≤ j → j ≤ j₂ → (oppSign i k j₁).nonneg → (oppSign i k j₂).nonneg →
    (oppSign i k j).nonneg
  oppConvexNeg : ∀ (i : Fin 2) k (j₁ j₂ j : Fin (gridSize k)),
    j₁ ≤ j → j ≤ j₂ → (oppSign i k j₁).flip.nonneg → (oppSign i k j₂).flip.nonneg →
    (oppSign i k j).flip.nonneg

lemma cmpSign_double (a b : ℕ) : cmpSign (2 * a) (2 * b) = cmpSign a b := by
  unfold cmpSign; simp only [Nat.mul_lt_mul_left (show 0 < 2 by omega)]

namespace GridTower

variable (t : GridTower)

def game (k : ℕ) : Base.SignGame (Fin 2) (fun _ : Fin 2 => Fin (gridSize k)) :=
  gridSignGame (gridSize k) (fun i => t.oppSign i k)

/-- If a predicate P holds at all embedded (even) grid points in [c, d], and P is
    preserved by forced midpoints, then P holds at all fine grid points in
    [embed(c), embed(d)]. Used to lift oppConvex from coarse to fine level. -/
private lemma oppSign_interval_generic {k : ℕ}
    (oppSign_k1 : Fin (gridSize (k + 1)) → Sign)
    (interp : ∀ (j : Fin (edgeCount k)),
      ∀ s, forcedMidpointSign (oppSign_k1 (gridEmbed k ⟨j, by grid_omega⟩))
                               (oppSign_k1 (gridEmbedRight k j)) = some s →
      oppSign_k1 (gridMidpoint k j) = s)
    (P : Sign → Prop) (hP_forced : ∀ s1 s2, P s1 → P s2 →
      ∃ s, forcedMidpointSign s1 s2 = some s ∧ P s)
    {c d : Fin (gridSize k)}
    (h_even : ∀ (j : Fin (gridSize k)), c ≤ j → j ≤ d →
      P (oppSign_k1 (gridEmbed k j)))
    {j : Fin (gridSize (k + 1))} (hj_lo : gridEmbed k c ≤ j) (hj_hi : j ≤ gridEmbed k d) :
    P (oppSign_k1 j) := by
  have hj_lo' : 2 * c.val ≤ j.val := by rw [Fin.le_def] at hj_lo; simp at hj_lo; omega
  have hj_hi' : j.val ≤ 2 * d.val := by rw [Fin.le_def] at hj_hi; simp at hj_hi; omega
  by_cases heven : j.val % 2 = 0
  · have hm : j.val / 2 < gridSize k := by grid_omega
    have hj_eq : j = gridEmbed k ⟨j.val / 2, hm⟩ := by ext; simp [gridEmbed_val]; omega
    rw [hj_eq]
    exact h_even ⟨j.val / 2, hm⟩
      (Fin.mk_le_mk.mpr (by omega)) (Fin.mk_le_mk.mpr (by omega))
  · have hm_lt : j.val / 2 < edgeCount k := by grid_omega
    have hj_eq : j = gridMidpoint k ⟨j.val / 2, hm_lt⟩ := by ext; simp [gridMidpoint_val]; omega
    rw [hj_eq]
    have hl := h_even ⟨j.val / 2, by grid_omega⟩
      (Fin.mk_le_mk.mpr (by omega)) (Fin.mk_le_mk.mpr (by omega))
    have hr_coarse := h_even ⟨j.val / 2 + 1, by grid_omega⟩
      (Fin.mk_le_mk.mpr (by omega)) (Fin.mk_le_mk.mpr (by omega))
    have hr_eq : gridEmbedRight k ⟨j.val / 2, hm_lt⟩ = gridEmbed k ⟨j.val / 2 + 1, by grid_omega⟩ := by
      ext; simp [gridEmbedRight_val, gridEmbed_val]; omega
    have hr : P (oppSign_k1 (gridEmbedRight k ⟨j.val / 2, hm_lt⟩)) := by
      rw [hr_eq]; exact hr_coarse
    obtain ⟨s, hs, hs_P⟩ := hP_forced _ _ hl hr
    rw [interp ⟨j.val / 2, hm_lt⟩ s hs]; exact hs_P

lemma oppSign_nonneg_interval (i : Fin 2) {k : ℕ}
    {c d : Fin (gridSize k)}
    (h_even : ∀ (j : Fin (gridSize k)), c ≤ j → j ≤ d →
      (t.oppSign i (k + 1) (gridEmbed k j)).nonneg)
    {j : Fin (gridSize (k + 1))} (hj_lo : gridEmbed k c ≤ j) (hj_hi : j ≤ gridEmbed k d) :
    (t.oppSign i (k + 1) j).nonneg :=
  oppSign_interval_generic (t.oppSign i (k + 1)) (t.interp i k) Sign.nonneg
    (fun _ _ => forcedMidpoint_of_nonneg_nonneg) h_even hj_lo hj_hi

lemma oppSign_flip_nonneg_interval (i : Fin 2) {k : ℕ}
    {c d : Fin (gridSize k)}
    (h_even : ∀ (j : Fin (gridSize k)), c ≤ j → j ≤ d →
      (t.oppSign i (k + 1) (gridEmbed k j)).flip.nonneg)
    {j : Fin (gridSize (k + 1))} (hj_lo : gridEmbed k c ≤ j) (hj_hi : j ≤ gridEmbed k d) :
    (t.oppSign i (k + 1) j).flip.nonneg :=
  oppSign_interval_generic (t.oppSign i (k + 1)) (t.interp i k) (Sign.nonneg ∘ Sign.flip)
    (fun _ _ => forcedMidpoint_of_flip_nonneg) h_even hj_lo hj_hi

/-- Convexity of `mul(c, oppSign(j))` in j, given oppConvex and oppConvexNeg.
    The sign c determines which convexity axiom is needed: pos uses oppConvex,
    neg uses oppConvexNeg, zero is trivial. -/
private lemma oppConvex_to_mul_convex {n : ℕ} {oppSign : Fin n → Sign}
    (hconv : ∀ (j₁ j₂ j : Fin n), j₁ ≤ j → j ≤ j₂ →
      (oppSign j₁).nonneg → (oppSign j₂).nonneg → (oppSign j).nonneg)
    (hconvNeg : ∀ (j₁ j₂ j : Fin n), j₁ ≤ j → j ≤ j₂ →
      (oppSign j₁).flip.nonneg → (oppSign j₂).flip.nonneg → (oppSign j).flip.nonneg)
    (c : Sign) (j₁ j₂ j : Fin n) (hlo : j₁ ≤ j) (hhi : j ≤ j₂)
    (h1 : (Sign.mul c (oppSign j₁)).nonneg) (h2 : (Sign.mul c (oppSign j₂)).nonneg) :
    (Sign.mul c (oppSign j)).nonneg := by
  cases c with
  | zero => simp only [Sign.zero_mul]; exact Sign.nonneg_zero
  | pos => simp only [Sign.pos_mul] at *; exact hconv j₁ j₂ j hlo hhi h1 h2
  | neg => simp only [Sign.neg_mul] at *; exact hconvNeg j₁ j₂ j hlo hhi h1 h2

-- ================================================================
-- GridTower → SignTower construction
-- ================================================================

private lemma mul_cmpSign_between_left {n : ℕ} {a b c x : Fin n} {s : Sign}
    (hlo : min a.val b.val ≤ c.val) (hhi : c.val ≤ max a.val b.val)
    (ha : (Sign.mul (cmpSign x.val a.val) s).nonneg)
    (hb : (Sign.mul (cmpSign x.val b.val) s).nonneg) :
    (Sign.mul (cmpSign x.val c.val) s).nonneg := by
  by_cases hcx : c.val = x.val
  · rw [← hcx, cmpSign_self]; exact Sign.nonneg_zero
  · cases s <;> (
      simp only [Sign.mul, Sign.flip, cmpSign, Sign.nonneg] at ha hb ⊢
      split_ifs at ha hb ⊢ <;> simp_all <;> omega)

private lemma mul_cmpSign_between_right {n : ℕ} {a b c x : Fin n} {s : Sign}
    (hlo : min a.val b.val ≤ c.val) (hhi : c.val ≤ max a.val b.val)
    (ha : (Sign.mul (cmpSign a.val x.val) s).nonneg)
    (hb : (Sign.mul (cmpSign b.val x.val) s).nonneg) :
    (Sign.mul (cmpSign c.val x.val) s).nonneg := by
  by_cases hcx : c.val = x.val
  · rw [← hcx, cmpSign_self]; exact Sign.nonneg_zero
  · cases s <;> (
      simp only [Sign.mul, Sign.flip, cmpSign, Sign.nonneg] at ha hb ⊢
      split_ifs at ha hb ⊢ <;> simp_all <;> omega)

/-- The main construction: verify all `SignTower` axioms for a `GridTower`.
    Coherence follows from `cmpSign_double`; player convexity from
    `mul_cmpSign_between_left/right`; opponent convexity from
    `oppConvex_to_mul_convex`; spanning from `fine_between_gridEmbed`. -/
def toSignTower : SignTower (Fin 2) where
  V k _ := Fin (gridSize k)
  instDecEq _ _ := inferInstance
  instFintype _ _ := inferInstance
  instInhabited _ _ := ⟨⟨0, Nat.succ_pos _⟩⟩
  betw k _ := finBetweenness (gridSize k)
  game k := t.game k
  embed k _ := gridEmbed k
  embed_inj k _ := gridEmbed_injective k
  embed_between k _ := gridEmbed_between k
  coherent k i p a b := by
    show (t.game (k+1)).sign i (fun j => gridEmbed k (p j)) (gridEmbed k a) (gridEmbed k b)
      = (t.game k).sign i p a b
    simp only [game, gridSignGame, gridEmbed_val, cmpSign_double, t.coherent]
  playerConvex_left k i p a b c x hbtw ha hb := by
    simp only [game, gridSignGame] at *
    simp only [finBetweenness] at hbtw
    have hlo : min a.val b.val ≤ c.val := by
      rw [← Fin.coe_min]; exact Fin.val_le_of_le hbtw.1
    have hhi : c.val ≤ max a.val b.val := by
      rw [← Fin.coe_max]; exact Fin.val_le_of_le hbtw.2
    exact mul_cmpSign_between_left hlo hhi ha hb
  playerConvex_right k i p a b c x hbtw ha hb := by
    simp only [game, gridSignGame] at *
    simp only [finBetweenness] at hbtw
    have hlo : min a.val b.val ≤ c.val := by
      rw [← Fin.coe_min]; exact Fin.val_le_of_le hbtw.1
    have hhi : c.val ≤ max a.val b.val := by
      rw [← Fin.coe_max]; exact Fin.val_le_of_le hbtw.2
    exact mul_cmpSign_between_right hlo hhi ha hb
  opponentConvex k i j hj p q a b hp_eq r hr_eq hbtw hp hq := by
    simp only [game, gridSignGame] at *
    have hji : j = 1 - i := by fin_cases i <;> fin_cases j <;> simp_all
    subst hji
    simp only [finBetweenness] at hbtw
    have hbtw' : min (p (1-i)) (q (1-i)) ≤ r (1-i) ∧ r (1-i) ≤ max (p (1-i)) (q (1-i)) := hbtw
    have hmin_nn : ((cmpSign b.val a.val).mul (t.oppSign i k (min (p (1-i)) (q (1-i))))).nonneg := by
      rcases min_choice (p (1-i)) (q (1-i)) with h | h <;> rw [h] <;> assumption
    have hmax_nn : ((cmpSign b.val a.val).mul (t.oppSign i k (max (p (1-i)) (q (1-i))))).nonneg := by
      rcases max_choice (p (1-i)) (q (1-i)) with h | h <;> rw [h] <;> assumption
    exact oppConvex_to_mul_convex (t.oppConvex i k) (t.oppConvexNeg i k)
      (cmpSign b.val a.val) (min (p (1-i)) (q (1-i))) (max (p (1-i)) (q (1-i))) (r (1-i))
      hbtw'.1 hbtw'.2 hmin_nn hmax_nn
  fine_between_embedded_at k _ := fine_between_gridEmbed k

theorem nash_sequence :
    ∀ k, ∃ σ : Base.Profile (Fin 2) (fun _ : Fin 2 => Fin (gridSize k)),
      (t.game k).IsNash σ ∧
      (∀ i, (t.game k).OutsideDom i σ) ∧
      t.toSignTower.HasConvexFaces k σ :=
  t.toSignTower.nash_refining_sequence

theorem nash_refines (k : ℕ) :
    ∃ σ : Base.Profile (Fin 2) (fun _ : Fin 2 => Fin (gridSize k)),
    ∃ σ' : Base.Profile (Fin 2) (fun _ : Fin 2 => Fin (gridSize (k + 1))),
      (t.game k).IsNash σ ∧
      (t.game (k + 1)).IsNash σ' ∧
      t.toSignTower.ProfileRefines k σ' σ :=
  t.toSignTower.nash_at_next_level_refines k

end GridTower

-- ================================================================
-- Concrete tower examples
-- ================================================================

/-- Prisoner's Dilemma tower: opponent signs are always negative, so defection
    dominates at every mixing ratio. Unique Nash at every level. -/
def pdTower : GridTower where
  oppSign _ _ _ := .neg
  coherent _ _ _ := rfl
  interp _ _ _ s h := by simp [forcedMidpointSign] at h; exact h
  oppConvex _ _ _ _ _ _ _ h₁ _ := absurd h₁ Sign.not_nonneg_neg
  oppConvexNeg _ _ _ _ _ _ _ _ _ := trivial

theorem pdTower_nash_sequence :
    ∀ k, ∃ σ, (pdTower.game k).IsNash σ ∧
      (∀ i, (pdTower.game k).OutsideDom i σ) ∧
      pdTower.toSignTower.HasConvexFaces k σ :=
  pdTower.nash_sequence

/-- Matching Pennies tower: opponent signs flip at j=0 (the boundary).
    Player 0 has pos at j=0, neg elsewhere; player 1 is reversed.
    The unique mixed equilibrium refines toward p=1/2. -/
def mpTower : GridTower where
  oppSign i _ j := if j.val = 0 then (if (i : ℕ) = 0 then .pos else .neg)
                                 else (if (i : ℕ) = 0 then .neg else .pos)
  coherent _ k j := by
    simp only [gridEmbed_val]
    have : (2 * j.val = 0) ↔ (j.val = 0) := by omega
    split_ifs with h1 h2 <;> simp_all
  interp i k j s h := by
    simp only [gridMidpoint_val, gridEmbed_val, gridEmbedRight_val] at *
    have hm : 2 * j.val + 1 ≠ 0 := by omega
    simp only [hm, ↓reduceIte]
    by_cases hj0 : j.val = 0
    · -- j=0: endpoints disagree (sign flip at boundary), so forcedMidpointSign = none
      simp only [hj0, Nat.mul_zero, show (0 + 2 : ℕ) ≠ 0 from by omega, ↓reduceIte] at h
      fin_cases i <;> simp [forcedMidpointSign] at h
    · have h1 : 2 * j.val ≠ 0 := by omega
      have h2 : 2 * j.val + 2 ≠ 0 := by omega
      simp only [h1, h2, ↓reduceIte, forcedMidpointSign] at h
      fin_cases i <;> simp_all
  oppConvex i _ j₁ j₂ j hlo hhi h1 h2 := by
    fin_cases i <;> {
      split_ifs at h1 h2 ⊢ with h1' h2' <;>
        first | trivial | exact absurd h1 id | exact absurd h2 id |
        (have := Fin.val_le_of_le hlo; have := Fin.val_le_of_le hhi; omega) }
  oppConvexNeg i _ j₁ j₂ j hlo hhi h1 h2 := by
    fin_cases i <;> {
      split_ifs at h1 h2 ⊢ with h1' h2' <;> simp_all [Sign.flip, Sign.nonneg] }

theorem mpTower_nash_sequence :
    ∀ k, ∃ σ, (mpTower.game k).IsNash σ ∧
      (∀ i, (mpTower.game k).OutsideDom i σ) ∧
      mpTower.toSignTower.HasConvexFaces k σ :=
  mpTower.nash_sequence

/-- Symmetric Coordination tower: `oppSign = cmpSign(2j, 2^k)`, so the sign
    changes at the midpoint j = 2^(k-1). Equilibrium at p = 1/2. -/
def symCoordTower : GridTower where
  oppSign _ k j := cmpSign (2 * j.val) (2 ^ k)
  coherent _ k j := by
    show cmpSign (2 * (gridEmbed k j).val) (2 ^ (k + 1)) = cmpSign (2 * j.val) (2 ^ k)
    simp only [gridEmbed_val, show 2 ^ (k + 1) = 2 * 2 ^ k from by omega]
    exact cmpSign_double _ _
  interp _ k j s h := by
    show cmpSign (2 * (gridMidpoint k j).val) (2 ^ (k + 1)) = s
    simp only [gridEmbed_val, gridEmbedRight_val, gridMidpoint_val,
               show 2 ^ (k + 1) = 2 * 2 ^ k from by omega] at *
    have e1 : 2 * (2 * j.val) = 4 * j.val := by omega
    have e2 : 2 * (2 * j.val + 2) = 4 * j.val + 4 := by omega
    have e3 : 2 * (2 * j.val + 1) = 4 * j.val + 2 := by omega
    rw [e1, e2] at h; rw [e3]
    unfold cmpSign at *; simp only [forcedMidpointSign] at h
    split_ifs at h ⊢ <;> simp_all <;> omega
  oppConvex _ _ j₁ j₂ j hlo hhi h1 h2 := by
    show (cmpSign (2 * j.val) _).nonneg
    rw [cmpSign_nonneg_iff] at *
    have := Fin.val_le_of_le hlo; have := Fin.val_le_of_le hhi; omega
  oppConvexNeg _ _ j₁ j₂ j hlo hhi h1 h2 := by
    show (cmpSign (2 * j.val) _).flip.nonneg
    rw [cmpSign_flip] at *; rw [cmpSign_nonneg_iff] at *
    have := Fin.val_le_of_le hlo; have := Fin.val_le_of_le hhi; omega

theorem symCoordTower_nash_sequence :
    ∀ k, ∃ σ, (symCoordTower.game k).IsNash σ ∧
      (∀ i, (symCoordTower.game k).OutsideDom i σ) ∧
      symCoordTower.toSignTower.HasConvexFaces k σ :=
  symCoordTower.nash_sequence

-- Spot-check oppSign values at levels 0-2
example : symCoordTower.oppSign 0 0 ⟨0, by grid_omega⟩ = .pos := by decide
example : symCoordTower.oppSign 0 0 ⟨1, by grid_omega⟩ = .neg := by decide
example : symCoordTower.oppSign 0 1 ⟨0, by grid_omega⟩ = .pos := by decide
example : symCoordTower.oppSign 0 1 ⟨1, by grid_omega⟩ = .zero := by decide
example : symCoordTower.oppSign 0 1 ⟨2, by grid_omega⟩ = .neg := by decide

/-- Battle of the Sexes tower: `oppSign = cmpSign(4j, D·2^k)` where D=3 for
    player 0 and D=1 for player 1. Asymmetric indifference points at
    p = 3/4 (player 0) and p = 1/4 (player 1). -/
def bosTower : GridTower where
  oppSign i k j := cmpSign (4 * j.val) (if (i : ℕ) = 0 then 3 * 2 ^ k else 2 ^ k)
  coherent i k j := by
    simp only [gridEmbed_val]
    split_ifs with h
    · show cmpSign (4 * (2 * j.val)) (3 * 2 ^ (k + 1)) = cmpSign (4 * j.val) (3 * 2 ^ k)
      simp only [show 3 * 2 ^ (k + 1) = 2 * (3 * 2 ^ k) from by omega]
      have : 4 * (2 * j.val) = 2 * (4 * j.val) := by omega
      rw [this]; exact cmpSign_double _ _
    · show cmpSign (4 * (2 * j.val)) (2 ^ (k + 1)) = cmpSign (4 * j.val) (2 ^ k)
      simp only [show 2 ^ (k + 1) = 2 * 2 ^ k from by omega]
      have : 4 * (2 * j.val) = 2 * (4 * j.val) := by omega
      rw [this]; exact cmpSign_double _ _
  interp i k j s h := by
    simp only [gridEmbed_val, gridEmbedRight_val, gridMidpoint_val] at *
    split_ifs with hi <;> {
      simp only [show 2 ^ (k + 1) = 2 * 2 ^ k from by omega] at *
      have e1 : 4 * (2 * j.val) = 8 * j.val := by omega
      have e2 : 4 * (2 * j.val + 2) = 8 * j.val + 8 := by omega
      have e3 : 4 * (2 * j.val + 1) = 8 * j.val + 4 := by omega
      rw [e1, e2] at h; rw [e3]
      unfold cmpSign at *; simp only [forcedMidpointSign] at h
      split_ifs at h ⊢ <;> simp_all <;> omega }
  oppConvex _ _ j₁ j₂ j hlo hhi h1 h2 := by
    show (cmpSign (4 * j.val) _).nonneg
    split_ifs at h1 h2 ⊢ <;> rw [cmpSign_nonneg_iff] at * <;>
      (have := Fin.val_le_of_le hlo; have := Fin.val_le_of_le hhi; omega)
  oppConvexNeg _ _ j₁ j₂ j hlo hhi h1 h2 := by
    show (cmpSign (4 * j.val) _).flip.nonneg
    split_ifs at h1 h2 ⊢ <;> rw [cmpSign_flip] at * <;> rw [cmpSign_nonneg_iff] at * <;>
      (have := Fin.val_le_of_le hlo; have := Fin.val_le_of_le hhi; omega)

theorem bosTower_nash_sequence :
    ∀ k, ∃ σ, (bosTower.game k).IsNash σ ∧
      (∀ i, (bosTower.game k).OutsideDom i σ) ∧
      bosTower.toSignTower.HasConvexFaces k σ :=
  bosTower.nash_sequence

-- Spot-check: player 0's indifference at 3/4, player 1's at 1/4
example : bosTower.oppSign 0 0 ⟨0, by grid_omega⟩ = .pos := by decide
example : bosTower.oppSign 0 0 ⟨1, by grid_omega⟩ = .neg := by decide
example : bosTower.oppSign 1 0 ⟨0, by grid_omega⟩ = .pos := by decide
example : bosTower.oppSign 1 0 ⟨1, by grid_omega⟩ = .neg := by decide

example : bosTower.oppSign 0 1 ⟨0, by grid_omega⟩ = .pos := by decide
example : bosTower.oppSign 0 1 ⟨1, by grid_omega⟩ = .pos := by decide
example : bosTower.oppSign 0 1 ⟨2, by grid_omega⟩ = .neg := by decide
example : bosTower.oppSign 1 1 ⟨0, by grid_omega⟩ = .pos := by decide
example : bosTower.oppSign 1 1 ⟨1, by grid_omega⟩ = .neg := by decide
example : bosTower.oppSign 1 1 ⟨2, by grid_omega⟩ = .neg := by decide

-- ================================================================
-- Grid children (self-similarity)
-- ================================================================

namespace GridChildren

-- The level-(k+1) grid [0, 2^(k+1)] splits at the midpoint 2^k into two
-- copies of the level-k grid. The left child covers [0, 2^k], the right
-- child covers [2^k, 2^(k+1)], sharing the boundary point (see
-- `boundary_shared`).

/-- Left child: j ↦ j (identity on values). -/
def leftChild (k : ℕ) (j : Fin (gridSize k)) : Fin (gridSize (k + 1)) :=
  ⟨j.val, by grid_omega⟩

/-- Right child: j ↦ j + 2^k. -/
def rightChild (k : ℕ) (j : Fin (gridSize k)) : Fin (gridSize (k + 1)) :=
  ⟨j.val + 2 ^ k, by grid_omega⟩

@[simp] theorem leftChild_val (k : ℕ) (j : Fin (gridSize k)) :
    (leftChild k j).val = j.val := rfl

@[simp] theorem rightChild_val (k : ℕ) (j : Fin (gridSize k)) :
    (rightChild k j).val = j.val + 2 ^ k := rfl

lemma leftChild_injective (k : ℕ) : Function.Injective (leftChild k) := by
  intro a b h
  simp only [leftChild, Fin.mk.injEq] at h
  exact Fin.ext h

lemma rightChild_injective (k : ℕ) : Function.Injective (rightChild k) := by
  intro a b h
  simp only [rightChild, Fin.mk.injEq] at h
  exact Fin.ext (by omega)

lemma leftChild_strictMono (k : ℕ) : StrictMono (leftChild k) :=
  fun _ _ h => h

lemma rightChild_strictMono (k : ℕ) : StrictMono (rightChild k) := by
  intro a b h
  show rightChild k a < rightChild k b
  simp only [Fin.lt_def, rightChild_val]
  omega

lemma leftChild_between (k : ℕ) (a b c : Fin (gridSize k))
    (h : (finBetweenness (gridSize k)).between c a b) :
    (finBetweenness (gridSize (k + 1))).between
      (leftChild k c) (leftChild k a) (leftChild k b) := by
  -- leftChild preserves .val, so min/max are preserved as Fin values
  simp only [finBetweenness] at *
  exact h

lemma rightChild_between (k : ℕ) (a b c : Fin (gridSize k))
    (h : (finBetweenness (gridSize k)).between c a b) :
    (finBetweenness (gridSize (k + 1))).between
      (rightChild k c) (rightChild k a) (rightChild k b) := by
  simp only [finBetweenness] at *
  obtain ⟨hlo, hhi⟩ := h
  have hlo_v : min a.val b.val ≤ c.val := by
    rw [← Fin.coe_min]; exact Fin.val_le_of_le hlo
  have hhi_v : c.val ≤ max a.val b.val := by
    rw [← Fin.coe_max]; exact Fin.val_le_of_le hhi
  constructor <;> {
    show _ ≤ _
    simp only [Fin.le_def, Fin.coe_min, Fin.coe_max, rightChild_val]
    omega
  }

/-- The last point of the left child is the first point of the right child. -/
lemma boundary_shared (k : ℕ) :
    leftChild k ⟨2 ^ k, by grid_omega⟩ = rightChild k ⟨0, Nat.succ_pos _⟩ := by
  apply Fin.ext; simp only [leftChild_val, rightChild_val]; omega

/-- Spanning for left child. -/
lemma fine_between_leftChild (k : ℕ) (v : Fin (gridSize (k + 1)))
    (hv : v.val ≤ 2 ^ k)
    (a : Fin (gridSize k)) :
    ∃ b : Fin (gridSize k),
      (finBetweenness (gridSize (k + 1))).between
        v (leftChild k a) (leftChild k b) := by
  simp only [finBetweenness, leftChild]
  by_cases h : v.val ≤ a.val
  · refine ⟨⟨0, by grid_omega⟩, ?_⟩
    constructor <;> { rw [Fin.le_def]; simp only [Fin.coe_min, Fin.coe_max]; omega }
  · push_neg at h
    refine ⟨⟨2 ^ k, by grid_omega⟩, ?_⟩
    constructor <;> { rw [Fin.le_def]; simp only [Fin.coe_min, Fin.coe_max]; omega }

/-- Spanning for right child. -/
lemma fine_between_rightChild (k : ℕ) (v : Fin (gridSize (k + 1)))
    (hv : 2 ^ k ≤ v.val)
    (a : Fin (gridSize k)) :
    ∃ b : Fin (gridSize k),
      (finBetweenness (gridSize (k + 1))).between
        v (rightChild k a) (rightChild k b) := by
  simp only [finBetweenness, rightChild]
  have ha := a.isLt
  have hv' := v.isLt
  by_cases h : v.val ≤ a.val + 2 ^ k
  · refine ⟨⟨0, by grid_omega⟩, ?_⟩
    constructor <;> { rw [Fin.le_def]; simp only [Fin.coe_min, Fin.coe_max]; omega }
  · push_neg at h
    refine ⟨⟨2 ^ k, by grid_omega⟩, ?_⟩
    constructor <;> { rw [Fin.le_def]; simp only [Fin.coe_min, Fin.coe_max]; grid_omega }

lemma gridEmbed_zero_eq_leftChild_zero (k : ℕ) :
    gridEmbed k ⟨0, Nat.succ_pos _⟩ = leftChild k ⟨0, Nat.succ_pos _⟩ := by
  apply Fin.ext; simp only [gridEmbed_val, leftChild_val]

lemma leftChild_range (k : ℕ) (j : Fin (gridSize k)) :
    (leftChild k j).val ≤ 2 ^ k := by
  simp only [leftChild_val]; have := j.isLt; grid_omega

lemma rightChild_range (k : ℕ) (j : Fin (gridSize k)) :
    2 ^ k ≤ (rightChild k j).val := by
  simp only [rightChild_val]; omega

end GridChildren

-- ================================================================
-- Affine invariance and counterexample
-- ================================================================

lemma cmpSign_pos_mul (c : ℕ) (hc : 0 < c) (a b : ℕ) :
    cmpSign (c * a) (c * b) = cmpSign a b := by
  simp only [cmpSign]
  split_ifs <;> simp_all

/-- For grid towers where `oppSign(k, j) = cmpSign(c·j, D·2^k)`, scaling
    both c and D by a positive constant preserves all signs. This is the
    tower-level analogue of ordinal invariance: at each level k, the invariance
    group is the positive affine maps (not all monotone transforms). -/
lemma affine_preserves_oppSign (c D slope : ℕ) (hslope : 0 < slope) (k : ℕ)
    (j : Fin (gridSize k)) :
    cmpSign (slope * c * j.val) (slope * D * 2^k) = cmpSign (c * j.val) (D * 2^k) := by
  have h1 : slope * c * j.val = slope * (c * j.val) := Nat.mul_assoc _ _ _
  have h2 : slope * D * 2 ^ k = slope * (D * 2 ^ k) := Nat.mul_assoc _ _ _
  rw [h1, h2]
  exact cmpSign_pos_mul slope hslope _ _

/-- Opponent sign for a game with indifference at p = 2/5.
    Payoffs (3, 0, 0, 2) give expected payoff difference 5p - 2. -/
def exampleOppSign (k : ℕ) (j : Fin (gridSize k)) := cmpSign (5 * j.val) (2 * 2^k)

/-- Same game under g(x) = x³: payoffs become (27, 0, 0, 8), shifting the
    indifference point to p = 8/35 ≈ 0.229. -/
def transformedOppSign (k : ℕ) (j : Fin (gridSize k)) := cmpSign (35 * j.val) (8 * 2^k)

/-- The non-affine transform g(x) = x³ changes signs at level 2.
    At grid point j=1 (p = 1/4 = 0.25): the original indifference point 2/5 = 0.4
    is above 1/4, so the sign is pos. But the transformed indifference point
    8/35 ≈ 0.229 is below 1/4, so the sign flips to neg. -/
theorem counterexample_level2 :
    exampleOppSign 2 ⟨1, by grid_omega⟩ = .pos ∧
    transformedOppSign 2 ⟨1, by grid_omega⟩ = .neg := by
  constructor <;> decide

/-- But the same transform preserves level-0 signs — the indifference point
    moved within the same coarse interval. -/
theorem signs_agree_level0 :
    exampleOppSign 0 ⟨0, by grid_omega⟩ = transformedOppSign 0 ⟨0, by grid_omega⟩ ∧
    exampleOppSign 0 ⟨1, by grid_omega⟩ = transformedOppSign 0 ⟨1, by grid_omega⟩ := by
  constructor <;> decide

-- ================================================================
-- Compact game examples
-- ================================================================

section CompactExamples

open Refinement.SignTower

def compactMP : SignTower (Fin 2) := mpTower.toSignTower

/-- Meta-MP: the tower re-rooted at level k. The base game of `metaMP k`
    has 2^k + 1 actions per player — each "action" is a mixing ratio from
    the original MP. -/
def metaMP (k : ℕ) : SignTower (Fin 2) := compactMP.shift k

lemma metaMP_nash (k j : ℕ) :
    ∃ σ, ((metaMP k).game j).IsNash σ :=
  ((metaMP k).nash_refining_sequence j).imp fun _ h => h.1

lemma compactMP_od_base :
    ∀ i, (compactMP.game 0).OutsideDom i (fun _ => Face.full) :=
  fun i => OutsideDom.maximal (compactMP.game 0) i

/-- Nash equilibria at any level live inside the iterated embed-close
    of the base full profile — the OD core propagates upward. -/
lemma compactMP_nash_inside (n : ℕ) :
    ∃ τ, (compactMP.game (0 + n)).IsNash τ ∧
      (∀ i, Face.IsSubface (τ i)
        (iterEmbedClose compactMP 0 (fun _ => Face.full) n i)) :=
  (nash_inside_iterEmbedClose compactMP 0 n compactMP_od_base).imp
    fun _ ⟨hN, hsub, _⟩ => ⟨hN, hsub⟩

end CompactExamples

-- ================================================================
-- Infinite-action game examples
-- ================================================================

section InfiniteExamples

/-- A 2-player game on ℕ where lower indices are always preferred.
    The core {0} satisfies OD, so Nash exists despite infinite actions. -/
def lowerIsBetter : SignGame (Fin 2) (fun _ : Fin 2 => ℕ) where
  sign _i _p a b := cmpSign a b
  sign_refl := fun _ _ a => cmpSign_self a
  sign_antisym := fun _ _ a b => by rw [cmpSign_flip]
  sign_trans := fun _ _ _ _ _ hab hbc => cmpSign_trans hab hbc
  sign_irrel := fun _ _ _ _ _ _ => rfl

lemma lowerIsBetter_OD (i : Fin 2) :
    lowerIsBetter.OutsideDom i (fun _ => Face.vertex 0) := by
  intro v hv w hw
  simp [Face.vertex] at hv hw; subst hw
  intro a ha p _hp b hb
  simp [Face.vertex] at ha hb; subst ha; subst hb
  simp [lowerIsBetter, cmpSign_nonneg_iff]

theorem lowerIsBetter_nash : ∃ σ, lowerIsBetter.IsNash σ :=
  lowerIsBetter.nash_of_core
    (fun _ => Face.vertex 0)
    (fun i => lowerIsBetter_OD i)

/-- Matching Pennies on ℕ: actions {0, 1} play the standard MP game,
    actions > 1 are "junk" (heavily penalized). Demonstrates `nash_of_core`:
    the OD core {0, 1} reduces infinite MP to finite MP. -/
def mpNatPayoff (i : Fin 2) (p : ∀ _ : Fin 2, ℕ) : Int :=
  let me := p i
  let opp := p (1 - i)
  if me > 1 then -(me : Int) - 100
  else if opp > 1 then 0
  else -- both in {0, 1}
    if (i : ℕ) = 0 then (if me == opp then 1 else 0)
    else (if me != opp then 1 else 0)

def mpNat : SignGame (Fin 2) (fun _ : Fin 2 => ℕ) :=
  SignGame.ofPayoffs mpNatPayoff

/-- Every action v > 1 gets payoff ≤ -102, while actions in {0, 1} get ≥ 0. -/
lemma mpNat_od (i : Fin 2) :
    mpNat.OutsideDom i (fun _ => ⟨{0, 1}, by simp⟩) := by
  intro v hv w hw
  simp only [Finset.mem_singleton, Finset.mem_insert] at hv hw
  push_neg at hv
  intro a ha p hp b hb
  simp only [Face.vertex, Finset.mem_singleton] at ha hb
  subst ha; subst hb
  have hb_gt : b > 1 := by omega
  have ha_le : a ≤ 1 := by omega
  simp only [mpNat, SignGame.ofPayoffs]
  show (if mpNatPayoff i (Function.update p i a) > mpNatPayoff i (Function.update p i b)
        then Sign.pos
        else if mpNatPayoff i (Function.update p i a) = mpNatPayoff i (Function.update p i b)
        then Sign.zero else Sign.neg).nonneg
  have hpay_b : mpNatPayoff i (Function.update p i b) = -(b : Int) - 100 := by
    simp [mpNatPayoff, Function.update_self, show b > 1 from hb_gt]
  have hpay_a_ge : mpNatPayoff i (Function.update p i a) ≥ 0 := by
    simp only [mpNatPayoff, Function.update_self, show ¬(a > 1) from by omega, ↓reduceIte]
    split_ifs <;> omega
  rw [hpay_b]
  have : mpNatPayoff i (Function.update p i a) > -(b : Int) - 100 := by omega
  simp [this]

theorem mpNat_nash : ∃ σ, mpNat.IsNash σ :=
  mpNat.nash_of_core (fun _ => ⟨{0, 1}, by simp⟩) mpNat_od

end InfiniteExamples

