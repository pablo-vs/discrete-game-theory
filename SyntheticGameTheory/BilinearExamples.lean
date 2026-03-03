/-
# Bilinear Tower Examples on the General N-Player Theory

Constructs bilinear sign games and towers for 2-player games with Fin-grid
action spaces, using the GeneralSignTower framework from Refinement.

## Overview

- `bilinearSignGame`: 2-player sign game from opponent-sign functions
- `forcedMidpointSign`: interpolation constraint for midpoint signs
- `GenBilinearTower`: input data for constructing a `GeneralSignTower (Fin 2)`
- `GenBilinearTower.toGeneralSignTower`: the main construction
- Examples: PD, MP, SymCoord, BoS towers with Nash+OD at every level
-/

import SyntheticGameTheory.Refinement

namespace BilinearExamples

open Base
open Refinement

-- ================================================================
-- Section 1: Bilinear sign game
-- ================================================================

/-- Transitivity for mul(cmpSign, s). -/
private theorem mul_cmpSign_trans {a b c : ℕ} {s : Sign}
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

/-- A bilinear sign game for 2 players on Fin n.
    sign(i, p, a, b) = mul(cmpSign b a, oppSign_i(p(1-i)))
    where oppSign_i is a sign function depending on the opponent's action. -/
def bilinearSignGame (n : ℕ) (oppSign₀ oppSign₁ : Fin n → Sign) :
    Base.SignGame (Fin 2) (fun _ : Fin 2 => Fin n) where
  sign i p a b :=
    let opp := p (1 - i)
    if (i : ℕ) = 0 then Sign.mul (cmpSign b.val a.val) (oppSign₀ opp)
    else Sign.mul (cmpSign b.val a.val) (oppSign₁ opp)
  sign_refl i p a := by simp [cmpSign_self]
  sign_antisym i p a b := by
    split_ifs <;> simp [Sign.flip_mul, cmpSign_flip]
  sign_trans i p a b c h1 h2 := by
    simp only [] at *
    split_ifs at * <;> exact mul_cmpSign_trans h1 h2
  sign_irrel i p q a b h := by
    have hopp : p (1 - i) = q (1 - i) :=
      h (1 - i) (by intro heq; exact absurd heq (by omega))
    simp only [hopp]

-- ================================================================
-- Section 2: Interpolation infrastructure
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
  | .pos, .neg => none
  | .neg, .pos => none

/-- Both nonneg endpoints force the midpoint sign to be nonneg. -/
private theorem forcedMidpoint_of_nonneg_nonneg {s1 s2 : Sign}
    (h1 : s1.nonneg) (h2 : s2.nonneg) :
    ∃ s, forcedMidpointSign s1 s2 = some s ∧ s.nonneg := by
  cases s1 <;> cases s2 <;> simp [Sign.nonneg, forcedMidpointSign] at *

/-- Both flip-nonneg endpoints force the midpoint sign to be flip-nonneg. -/
private theorem forcedMidpoint_of_flip_nonneg {s1 s2 : Sign}
    (h1 : s1.flip.nonneg) (h2 : s2.flip.nonneg) :
    ∃ s, forcedMidpointSign s1 s2 = some s ∧ s.flip.nonneg := by
  cases s1 <;> cases s2 <;> simp [Sign.nonneg, Sign.flip, forcedMidpointSign] at *

-- ================================================================
-- Section 3: GenBilinearTower structure
-- ================================================================

/-- Input data for a bilinear tower on the general framework.
    Specifies opponent-sign functions at each level for both players,
    with coherence, interpolation, and convexity axioms. -/
structure GenBilinearTower where
  oppSign₀ : (k : ℕ) → Fin (gridSize k) → Sign
  oppSign₁ : (k : ℕ) → Fin (gridSize k) → Sign
  coherent₀ : ∀ k (j : Fin (gridSize k)),
    oppSign₀ (k + 1) (gridEmbed k j) = oppSign₀ k j
  coherent₁ : ∀ k (j : Fin (gridSize k)),
    oppSign₁ (k + 1) (gridEmbed k j) = oppSign₁ k j
  interp₀ : ∀ k (j : Fin (edgeCount k)),
    ∀ s, forcedMidpointSign (oppSign₀ (k + 1) (gridEmbed k ⟨j, by grid_omega⟩))
                             (oppSign₀ (k + 1) (gridEmbedRight k j)) = some s →
    oppSign₀ (k + 1) (gridMidpoint k j) = s
  interp₁ : ∀ k (j : Fin (edgeCount k)),
    ∀ s, forcedMidpointSign (oppSign₁ (k + 1) (gridEmbed k ⟨j, by grid_omega⟩))
                             (oppSign₁ (k + 1) (gridEmbedRight k j)) = some s →
    oppSign₁ (k + 1) (gridMidpoint k j) = s
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

namespace GenBilinearTower

variable (t : GenBilinearTower)

/-- The sign game at level k. -/
def game (k : ℕ) : Base.SignGame (Fin 2) (fun _ : Fin 2 => Fin (gridSize k)) :=
  bilinearSignGame (gridSize k) (t.oppSign₀ k) (t.oppSign₁ k)

-- ================================================================
-- Section 4: oppSign nonneg/flip interval lemmas
-- ================================================================

/-- oppSign₀ nonneg at even points in [c, d] → nonneg at all points in [embed c, embed d]. -/
theorem oppSign₀_nonneg_interval {k : ℕ}
    {c d : Fin (gridSize k)}
    (h_even : ∀ (j : Fin (gridSize k)), c ≤ j → j ≤ d →
      (t.oppSign₀ (k + 1) (gridEmbed k j)).nonneg)
    {j : Fin (gridSize (k + 1))} (hj_lo : gridEmbed k c ≤ j) (hj_hi : j ≤ gridEmbed k d) :
    (t.oppSign₀ (k + 1) j).nonneg := by
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
    have hr : (t.oppSign₀ (k + 1) (gridEmbedRight k ⟨j.val / 2, hm_lt⟩)).nonneg := by
      rw [hr_eq]; exact hr_coarse
    obtain ⟨s, hs, hs_nn⟩ := forcedMidpoint_of_nonneg_nonneg hl hr
    rw [t.interp₀ k ⟨j.val / 2, hm_lt⟩ s hs]
    exact hs_nn

/-- Symmetric version for oppSign₁. -/
theorem oppSign₁_nonneg_interval {k : ℕ}
    {c d : Fin (gridSize k)}
    (h_even : ∀ (j : Fin (gridSize k)), c ≤ j → j ≤ d →
      (t.oppSign₁ (k + 1) (gridEmbed k j)).nonneg)
    {j : Fin (gridSize (k + 1))} (hj_lo : gridEmbed k c ≤ j) (hj_hi : j ≤ gridEmbed k d) :
    (t.oppSign₁ (k + 1) j).nonneg := by
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
    have hr : (t.oppSign₁ (k + 1) (gridEmbedRight k ⟨j.val / 2, hm_lt⟩)).nonneg := by
      rw [hr_eq]; exact hr_coarse
    obtain ⟨s, hs, hs_nn⟩ := forcedMidpoint_of_nonneg_nonneg hl hr
    rw [t.interp₁ k ⟨j.val / 2, hm_lt⟩ s hs]
    exact hs_nn

/-- oppSign₀ flip.nonneg interval version. -/
theorem oppSign₀_flip_nonneg_interval {k : ℕ}
    {c d : Fin (gridSize k)}
    (h_even : ∀ (j : Fin (gridSize k)), c ≤ j → j ≤ d →
      (t.oppSign₀ (k + 1) (gridEmbed k j)).flip.nonneg)
    {j : Fin (gridSize (k + 1))} (hj_lo : gridEmbed k c ≤ j) (hj_hi : j ≤ gridEmbed k d) :
    (t.oppSign₀ (k + 1) j).flip.nonneg := by
  have hj_lo' : 2 * c.val ≤ j.val := by rw [Fin.le_def] at hj_lo; simp at hj_lo; omega
  have hj_hi' : j.val ≤ 2 * d.val := by rw [Fin.le_def] at hj_hi; simp at hj_hi; omega
  by_cases heven : j.val % 2 = 0
  · have hm : j.val / 2 < gridSize k := by grid_omega
    have hj_eq : j = gridEmbed k ⟨j.val / 2, hm⟩ := by ext; simp [gridEmbed_val]; omega
    rw [hj_eq]; exact h_even ⟨j.val / 2, hm⟩
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
    have hr : (t.oppSign₀ (k + 1) (gridEmbedRight k ⟨j.val / 2, hm_lt⟩)).flip.nonneg := by
      rw [hr_eq]; exact hr_coarse
    obtain ⟨s, hs, hs_nn⟩ := forcedMidpoint_of_flip_nonneg hl hr
    rw [t.interp₀ k ⟨j.val / 2, hm_lt⟩ s hs]; exact hs_nn

/-- oppSign₁ flip.nonneg interval version. -/
theorem oppSign₁_flip_nonneg_interval {k : ℕ}
    {c d : Fin (gridSize k)}
    (h_even : ∀ (j : Fin (gridSize k)), c ≤ j → j ≤ d →
      (t.oppSign₁ (k + 1) (gridEmbed k j)).flip.nonneg)
    {j : Fin (gridSize (k + 1))} (hj_lo : gridEmbed k c ≤ j) (hj_hi : j ≤ gridEmbed k d) :
    (t.oppSign₁ (k + 1) j).flip.nonneg := by
  have hj_lo' : 2 * c.val ≤ j.val := by rw [Fin.le_def] at hj_lo; simp at hj_lo; omega
  have hj_hi' : j.val ≤ 2 * d.val := by rw [Fin.le_def] at hj_hi; simp at hj_hi; omega
  by_cases heven : j.val % 2 = 0
  · have hm : j.val / 2 < gridSize k := by grid_omega
    have hj_eq : j = gridEmbed k ⟨j.val / 2, hm⟩ := by ext; simp [gridEmbed_val]; omega
    rw [hj_eq]; exact h_even ⟨j.val / 2, hm⟩
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
    have hr : (t.oppSign₁ (k + 1) (gridEmbedRight k ⟨j.val / 2, hm_lt⟩)).flip.nonneg := by
      rw [hr_eq]; exact hr_coarse
    obtain ⟨s, hs, hs_nn⟩ := forcedMidpoint_of_flip_nonneg hl hr
    rw [t.interp₁ k ⟨j.val / 2, hm_lt⟩ s hs]; exact hs_nn

-- ================================================================
-- Section 5: Convexity lemmas for bilinear games
-- ================================================================

/-- Helper: convexity of mul(c, oppSign) given oppConvex + oppConvexNeg. -/
private theorem oppConvex_to_mul_convex {n : ℕ} {oppSign : Fin n → Sign}
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
-- Section 6: GenBilinearTower → GeneralSignTower
-- ================================================================

private theorem cmpSign_double (a b : ℕ) : cmpSign (2 * a) (2 * b) = cmpSign a b := by
  unfold cmpSign; simp only [Nat.mul_lt_mul_left (show 0 < 2 by omega)]

/-- If c is between a and b (in val), then mul(cmpSign x c, s) is nonneg
    given that both mul(cmpSign x a, s) and mul(cmpSign x b, s) are nonneg. -/
private theorem mul_cmpSign_between_left {n : ℕ} {a b c x : Fin n} {s : Sign}
    (hlo : min a.val b.val ≤ c.val) (hhi : c.val ≤ max a.val b.val)
    (ha : (Sign.mul (cmpSign x.val a.val) s).nonneg)
    (hb : (Sign.mul (cmpSign x.val b.val) s).nonneg) :
    (Sign.mul (cmpSign x.val c.val) s).nonneg := by
  by_cases hcx : c.val = x.val
  · rw [← hcx, cmpSign_self]; exact Sign.nonneg_zero
  · cases s <;> (
      simp only [Sign.mul, Sign.flip, cmpSign, Sign.nonneg] at ha hb ⊢
      split_ifs at ha hb ⊢ <;> simp_all <;> omega)

/-- Right version: mul(cmpSign c x, s) convex. -/
private theorem mul_cmpSign_between_right {n : ℕ} {a b c x : Fin n} {s : Sign}
    (hlo : min a.val b.val ≤ c.val) (hhi : c.val ≤ max a.val b.val)
    (ha : (Sign.mul (cmpSign a.val x.val) s).nonneg)
    (hb : (Sign.mul (cmpSign b.val x.val) s).nonneg) :
    (Sign.mul (cmpSign c.val x.val) s).nonneg := by
  by_cases hcx : c.val = x.val
  · rw [← hcx, cmpSign_self]; exact Sign.nonneg_zero
  · cases s <;> (
      simp only [Sign.mul, Sign.flip, cmpSign, Sign.nonneg] at ha hb ⊢
      split_ifs at ha hb ⊢ <;> simp_all <;> omega)

/-- Convert a GenBilinearTower into a GeneralSignTower (Fin 2). -/
noncomputable def toGeneralSignTower : GeneralSignTower (Fin 2) where
  V k _ := Fin (gridSize k)
  instDecEq _ _ := inferInstance
  instFintype _ _ := inferInstance
  instNonempty _ _ := gridSize_nonempty _
  betw k _ := finBetweenness (gridSize k)
  game k := t.game k
  embed k _ := gridEmbed k
  embed_inj k _ := gridEmbed_injective k
  embed_between k _ := gridEmbed_between k
  coherent k i p a b := by
    -- sign at fine level with embedded profile/actions = sign at coarse level
    show (t.game (k+1)).sign i (fun j => gridEmbed k (p j)) (gridEmbed k a) (gridEmbed k b)
      = (t.game k).sign i p a b
    simp only [game, bilinearSignGame, gridEmbed_val, cmpSign_double]
    fin_cases i <;> simp [t.coherent₀, t.coherent₁]
  playerConvex_left k i p a b c x hbtw ha hb := by
    -- sign(p, c, x) nonneg given sign(p, a, x) and sign(p, b, x) nonneg, c between a b
    simp only [game, bilinearSignGame] at *
    simp only [finBetweenness] at hbtw
    have hlo : min a.val b.val ≤ c.val := by
      rw [← Fin.coe_min]; exact Fin.val_le_of_le hbtw.1
    have hhi : c.val ≤ max a.val b.val := by
      rw [← Fin.coe_max]; exact Fin.val_le_of_le hbtw.2
    -- sign = mul(cmpSign x c, oppSign(opp)), so this is mul_cmpSign_between_left
    fin_cases i <;> exact mul_cmpSign_between_left hlo hhi ha hb
  playerConvex_right k i p a b c x hbtw ha hb := by
    simp only [game, bilinearSignGame] at *
    simp only [finBetweenness] at hbtw
    have hlo : min a.val b.val ≤ c.val := by
      rw [← Fin.coe_min]; exact Fin.val_le_of_le hbtw.1
    have hhi : c.val ≤ max a.val b.val := by
      rw [← Fin.coe_max]; exact Fin.val_le_of_le hbtw.2
    -- sign = mul(cmpSign c x, oppSign(opp)), so this is mul_cmpSign_between_right
    fin_cases i <;> exact mul_cmpSign_between_right hlo hhi ha hb
  opponentConvex k i j hj p q a b hp_eq r hr_eq hbtw hp hq := by
    simp only [game, bilinearSignGame] at *
    -- j ≠ i in Fin 2 means j = 1 - i, so opp = p j = p(1-i)
    have hji : j = 1 - i := by fin_cases i <;> fin_cases j <;> simp_all
    subst hji
    simp only [finBetweenness] at hbtw
    -- The cmpSign(b,a) factor is fixed; oppSign varies with p(1-i), q(1-i), r(1-i)
    -- r(1-i) is between p(1-i) and q(1-i), so use oppConvex_to_mul_convex
    -- Need to handle the `if (i:ℕ) = 0` split
    fin_cases i
    · -- i = 0: oppSign₀ applied to p 1, q 1, r 1
      simp only [Fin.isValue, ite_true] at hp hq ⊢
      have hbtw' : min (p 1) (q 1) ≤ r 1 ∧ r 1 ≤ max (p 1) (q 1) := hbtw
      -- oppConvex takes j₁ ≤ j ≤ j₂; we pass min/max with betweenness
      have hmin_nn : ((cmpSign b.val a.val).mul (t.oppSign₀ k (min (p 1) (q 1)))).nonneg := by
        rcases min_choice (p 1) (q 1) with h | h <;> rw [h] <;> assumption
      have hmax_nn : ((cmpSign b.val a.val).mul (t.oppSign₀ k (max (p 1) (q 1)))).nonneg := by
        rcases max_choice (p 1) (q 1) with h | h <;> rw [h] <;> assumption
      exact oppConvex_to_mul_convex (t.oppConvex₀ k) (t.oppConvexNeg₀ k)
        (cmpSign b.val a.val) (min (p 1) (q 1)) (max (p 1) (q 1)) (r 1)
        hbtw'.1 hbtw'.2 hmin_nn hmax_nn
    · -- i = 1: oppSign₁ applied to p 0, q 0, r 0
      simp only [Fin.isValue] at hp hq ⊢
      have hbtw' : min (p 0) (q 0) ≤ r 0 ∧ r 0 ≤ max (p 0) (q 0) := hbtw
      have hmin_nn : ((cmpSign b.val a.val).mul (t.oppSign₁ k (min (p 0) (q 0)))).nonneg := by
        rcases min_choice (p 0) (q 0) with h | h <;> rw [h] <;> assumption
      have hmax_nn : ((cmpSign b.val a.val).mul (t.oppSign₁ k (max (p 0) (q 0)))).nonneg := by
        rcases max_choice (p 0) (q 0) with h | h <;> rw [h] <;> assumption
      exact oppConvex_to_mul_convex (t.oppConvex₁ k) (t.oppConvexNeg₁ k)
        (cmpSign b.val a.val) (min (p 0) (q 0)) (max (p 0) (q 0)) (r 0)
        hbtw'.1 hbtw'.2 hmin_nn hmax_nn
  fine_between_embedded_at k _ := fine_between_gridEmbed k

-- ================================================================
-- Section 7: Nash existence theorems
-- ================================================================

/-- Nash + OD + convex-closed at every level. -/
theorem nash_sequence :
    ∀ k, ∃ σ : Base.Profile (Fin 2) (fun _ : Fin 2 => Fin (gridSize k)),
      (t.game k).IsNash σ ∧
      (∀ i, (t.game k).OutsideDominated i σ) ∧
      t.toGeneralSignTower.IsConvexClosed k σ :=
  t.toGeneralSignTower.nash_refining_sequence

/-- Nash refinement at each level. -/
theorem nash_refines (k : ℕ) :
    ∃ σ : Base.Profile (Fin 2) (fun _ : Fin 2 => Fin (gridSize k)),
    ∃ σ' : Base.Profile (Fin 2) (fun _ : Fin 2 => Fin (gridSize (k + 1))),
      (t.game k).IsNash σ ∧
      (t.game (k + 1)).IsNash σ' ∧
      t.toGeneralSignTower.ProfileRefines k σ' σ :=
  t.toGeneralSignTower.nash_at_next_level_refines k

end GenBilinearTower

-- ================================================================
-- Section 8: cmpSign helpers for tower examples
-- ================================================================

private theorem cmpSign_mul2 {a b : ℕ} : cmpSign (2 * a) (2 * b) = cmpSign a b := by
  unfold cmpSign
  simp only [show ∀ a b : ℕ, (2 * a < 2 * b ↔ a < b) from fun a b => by omega]

-- ================================================================
-- Section 9: Prisoner's Dilemma tower
-- ================================================================

def genPdTower : GenBilinearTower where
  oppSign₀ _ _ := .neg
  oppSign₁ _ _ := .neg
  coherent₀ _ _ := rfl
  coherent₁ _ _ := rfl
  interp₀ _ _ s h := by simp [forcedMidpointSign] at h; exact h
  interp₁ _ _ s h := by simp [forcedMidpointSign] at h; exact h
  oppConvex₀ _ _ _ _ _ _ h₁ _ := absurd h₁ Sign.not_nonneg_neg
  oppConvex₁ _ _ _ _ _ _ h₁ _ := absurd h₁ Sign.not_nonneg_neg
  oppConvexNeg₀ _ _ _ _ _ _ _ _ := trivial
  oppConvexNeg₁ _ _ _ _ _ _ _ _ := trivial

theorem genPdTower_nash_sequence :
    ∀ k, ∃ σ, (genPdTower.game k).IsNash σ ∧
      (∀ i, (genPdTower.game k).OutsideDominated i σ) ∧
      genPdTower.toGeneralSignTower.IsConvexClosed k σ :=
  genPdTower.nash_sequence

-- ================================================================
-- Section 10: Matching Pennies tower
-- ================================================================

def genMpTower : GenBilinearTower where
  oppSign₀ _ j := if j.val = 0 then .pos else .neg
  oppSign₁ _ j := if j.val = 0 then .neg else .pos
  coherent₀ k j := by
    show (if (gridEmbed k j).val = 0 then _ else _) = (if j.val = 0 then _ else _)
    simp only [gridEmbed_val]
    have : (2 * j.val = 0) ↔ (j.val = 0) := by omega
    split_ifs with h1 h2 <;> simp_all
  coherent₁ k j := by
    show (if (gridEmbed k j).val = 0 then _ else _) = (if j.val = 0 then _ else _)
    simp only [gridEmbed_val]
    have : (2 * j.val = 0) ↔ (j.val = 0) := by omega
    split_ifs with h1 h2 <;> simp_all
  interp₀ k j s h := by
    show (if (gridMidpoint k j).val = 0 then _ else _) = s
    simp only [gridMidpoint_val]
    have hm : 2 * j.val + 1 ≠ 0 := by omega
    simp only [hm, ↓reduceIte]
    show Sign.neg = s
    simp only [gridEmbed_val, gridEmbedRight_val] at h
    change (forcedMidpointSign (if 2 * j.val = 0 then .pos else .neg)
            (if 2 * j.val + 2 = 0 then .pos else .neg) = some s) at h
    by_cases hj0 : j.val = 0
    · have h2 : (0 + 2 : ℕ) ≠ 0 := by omega
      simp only [hj0, Nat.mul_zero, ↓reduceIte, h2, forcedMidpointSign] at h
      exact absurd h nofun
    · have h1 : 2 * j.val ≠ 0 := by omega
      have h2 : 2 * j.val + 2 ≠ 0 := by omega
      simp only [h1, ↓reduceIte, h2, forcedMidpointSign] at h
      exact Option.some.inj h
  interp₁ k j s h := by
    show (if (gridMidpoint k j).val = 0 then _ else _) = s
    simp only [gridMidpoint_val]
    have hm : 2 * j.val + 1 ≠ 0 := by omega
    simp only [hm, ↓reduceIte]
    show Sign.pos = s
    simp only [gridEmbed_val, gridEmbedRight_val] at h
    change (forcedMidpointSign (if 2 * j.val = 0 then .neg else .pos)
            (if 2 * j.val + 2 = 0 then .neg else .pos) = some s) at h
    by_cases hj0 : j.val = 0
    · have h2 : (0 + 2 : ℕ) ≠ 0 := by omega
      simp only [hj0, Nat.mul_zero, ↓reduceIte, h2, forcedMidpointSign] at h
      exact absurd h nofun
    · have h1 : 2 * j.val ≠ 0 := by omega
      have h2 : 2 * j.val + 2 ≠ 0 := by omega
      simp only [h1, ↓reduceIte, h2, forcedMidpointSign] at h
      exact Option.some.inj h
  oppConvex₀ _ j₁ j₂ j hlo hhi h1 h2 := by
    show (if j.val = 0 then Sign.pos else Sign.neg).nonneg
    have h1' : (if j₁.val = 0 then Sign.pos else Sign.neg).nonneg := h1
    have h2' : (if j₂.val = 0 then Sign.pos else Sign.neg).nonneg := h2
    split_ifs at h1' h2' with h1'' h2''
    · have : j.val = 0 := by
        have := Fin.val_le_of_le hlo; have := Fin.val_le_of_le hhi; omega
      simp [this]
    · exact absurd h2' id
    · exact absurd h1' id
    · exact absurd h1' id
  oppConvex₁ _ j₁ _ j hlo _ h1 _ := by
    show (if j.val = 0 then Sign.neg else Sign.pos).nonneg
    have h1' : (if j₁.val = 0 then Sign.neg else Sign.pos).nonneg := h1
    split_ifs at h1' with h1''
    · exact absurd h1' id
    · have : j.val ≠ 0 := by have := Fin.val_le_of_le hlo; omega
      simp [this]
  oppConvexNeg₀ _ j₁ _ j hlo _ h1 _ := by
    show (if j.val = 0 then Sign.pos else Sign.neg).flip.nonneg
    have h1' : (if j₁.val = 0 then Sign.pos else Sign.neg).flip.nonneg := h1
    split_ifs at h1' with h1''
    · simp [Sign.flip, Sign.nonneg] at h1'
    · have : j.val ≠ 0 := by have := Fin.val_le_of_le hlo; omega
      simp [this, Sign.flip]
  oppConvexNeg₁ _ j₁ j₂ j hlo hhi h1 h2 := by
    show (if j.val = 0 then Sign.neg else Sign.pos).flip.nonneg
    have h1' : (if j₁.val = 0 then Sign.neg else Sign.pos).flip.nonneg := h1
    have h2' : (if j₂.val = 0 then Sign.neg else Sign.pos).flip.nonneg := h2
    split_ifs at h1' h2' with h1'' h2''
    · have : j.val = 0 := by
        have := Fin.val_le_of_le hlo; have := Fin.val_le_of_le hhi; omega
      simp [this, Sign.flip]
    · simp [Sign.flip, Sign.nonneg] at h2'
    · simp [Sign.flip, Sign.nonneg] at h1'
    · simp [Sign.flip, Sign.nonneg] at h1'

theorem genMpTower_nash_sequence :
    ∀ k, ∃ σ, (genMpTower.game k).IsNash σ ∧
      (∀ i, (genMpTower.game k).OutsideDominated i σ) ∧
      genMpTower.toGeneralSignTower.IsConvexClosed k σ :=
  genMpTower.nash_sequence

-- ================================================================
-- Section 11: Symmetric Coordination tower
-- ================================================================

def genSymCoordTower : GenBilinearTower where
  oppSign₀ k j := cmpSign (2 * j.val) (2 ^ k)
  oppSign₁ k j := cmpSign (2 * j.val) (2 ^ k)
  coherent₀ k j := by
    show cmpSign (2 * (gridEmbed k j).val) (2 ^ (k + 1)) = cmpSign (2 * j.val) (2 ^ k)
    simp only [gridEmbed_val, show 2 ^ (k + 1) = 2 * 2 ^ k from by omega]
    exact cmpSign_mul2
  coherent₁ k j := by
    show cmpSign (2 * (gridEmbed k j).val) (2 ^ (k + 1)) = cmpSign (2 * j.val) (2 ^ k)
    simp only [gridEmbed_val, show 2 ^ (k + 1) = 2 * 2 ^ k from by omega]
    exact cmpSign_mul2
  interp₀ k j s h := by
    show cmpSign (2 * (gridMidpoint k j).val) (2 ^ (k + 1)) = s
    simp only [gridEmbed_val, gridEmbedRight_val, gridMidpoint_val,
               show 2 ^ (k + 1) = 2 * 2 ^ k from by omega] at *
    have e1 : 2 * (2 * j.val) = 4 * j.val := by omega
    have e2 : 2 * (2 * j.val + 2) = 4 * j.val + 4 := by omega
    have e3 : 2 * (2 * j.val + 1) = 4 * j.val + 2 := by omega
    rw [e1, e2] at h; rw [e3]
    unfold cmpSign at *; simp only [forcedMidpointSign] at h
    split_ifs at h ⊢ <;> simp_all <;> omega
  interp₁ k j s h := by
    show cmpSign (2 * (gridMidpoint k j).val) (2 ^ (k + 1)) = s
    simp only [gridEmbed_val, gridEmbedRight_val, gridMidpoint_val,
               show 2 ^ (k + 1) = 2 * 2 ^ k from by omega] at *
    have e1 : 2 * (2 * j.val) = 4 * j.val := by omega
    have e2 : 2 * (2 * j.val + 2) = 4 * j.val + 4 := by omega
    have e3 : 2 * (2 * j.val + 1) = 4 * j.val + 2 := by omega
    rw [e1, e2] at h; rw [e3]
    unfold cmpSign at *; simp only [forcedMidpointSign] at h
    split_ifs at h ⊢ <;> simp_all <;> omega
  oppConvex₀ _ j₁ j₂ j hlo hhi h1 h2 := by
    show (cmpSign (2 * j.val) _).nonneg
    rw [cmpSign_nonneg_iff] at *
    have := Fin.val_le_of_le hlo; have := Fin.val_le_of_le hhi; omega
  oppConvex₁ _ j₁ j₂ j hlo hhi h1 h2 := by
    show (cmpSign (2 * j.val) _).nonneg
    rw [cmpSign_nonneg_iff] at *
    have := Fin.val_le_of_le hlo; have := Fin.val_le_of_le hhi; omega
  oppConvexNeg₀ _ j₁ j₂ j hlo hhi h1 h2 := by
    show (cmpSign (2 * j.val) _).flip.nonneg
    rw [cmpSign_flip] at *; rw [cmpSign_nonneg_iff] at *
    have := Fin.val_le_of_le hlo; have := Fin.val_le_of_le hhi; omega
  oppConvexNeg₁ _ j₁ j₂ j hlo hhi h1 h2 := by
    show (cmpSign (2 * j.val) _).flip.nonneg
    rw [cmpSign_flip] at *; rw [cmpSign_nonneg_iff] at *
    have := Fin.val_le_of_le hlo; have := Fin.val_le_of_le hhi; omega

theorem genSymCoordTower_nash_sequence :
    ∀ k, ∃ σ, (genSymCoordTower.game k).IsNash σ ∧
      (∀ i, (genSymCoordTower.game k).OutsideDominated i σ) ∧
      genSymCoordTower.toGeneralSignTower.IsConvexClosed k σ :=
  genSymCoordTower.nash_sequence

-- Sign examples at levels 0-2
example : genSymCoordTower.oppSign₀ 0 ⟨0, by grid_omega⟩ = .pos := by decide
example : genSymCoordTower.oppSign₀ 0 ⟨1, by grid_omega⟩ = .neg := by decide
example : genSymCoordTower.oppSign₀ 1 ⟨0, by grid_omega⟩ = .pos := by decide
example : genSymCoordTower.oppSign₀ 1 ⟨1, by grid_omega⟩ = .zero := by decide
example : genSymCoordTower.oppSign₀ 1 ⟨2, by grid_omega⟩ = .neg := by decide

-- ================================================================
-- Section 12: Battle of the Sexes tower
-- ================================================================

def genBosTower : GenBilinearTower where
  oppSign₀ k j := cmpSign (4 * j.val) (3 * 2 ^ k)
  oppSign₁ k j := cmpSign (4 * j.val) (2 ^ k)
  coherent₀ k j := by
    show cmpSign (4 * (gridEmbed k j).val) (3 * 2 ^ (k + 1)) = cmpSign (4 * j.val) (3 * 2 ^ k)
    simp only [gridEmbed_val, show 3 * 2 ^ (k + 1) = 2 * (3 * 2 ^ k) from by omega]
    show cmpSign (4 * (2 * j.val)) (2 * (3 * 2 ^ k)) = cmpSign (4 * j.val) (3 * 2 ^ k)
    have : 4 * (2 * j.val) = 2 * (4 * j.val) := by omega
    rw [this]; exact cmpSign_mul2
  coherent₁ k j := by
    show cmpSign (4 * (gridEmbed k j).val) (2 ^ (k + 1)) = cmpSign (4 * j.val) (2 ^ k)
    simp only [gridEmbed_val, show 2 ^ (k + 1) = 2 * 2 ^ k from by omega]
    show cmpSign (4 * (2 * j.val)) (2 * 2 ^ k) = cmpSign (4 * j.val) (2 ^ k)
    have : 4 * (2 * j.val) = 2 * (4 * j.val) := by omega
    rw [this]; exact cmpSign_mul2
  interp₀ k j s h := by
    show cmpSign (4 * (gridMidpoint k j).val) (3 * 2 ^ (k + 1)) = s
    simp only [gridEmbed_val, gridEmbedRight_val, gridMidpoint_val,
               show 3 * 2 ^ (k + 1) = 2 * (3 * 2 ^ k) from by omega] at *
    have e1 : 4 * (2 * j.val) = 8 * j.val := by omega
    have e2 : 4 * (2 * j.val + 2) = 8 * j.val + 8 := by omega
    have e3 : 4 * (2 * j.val + 1) = 8 * j.val + 4 := by omega
    rw [e1, e2] at h; rw [e3]
    unfold cmpSign at *; simp only [forcedMidpointSign] at h
    split_ifs at h ⊢ <;> simp_all <;> omega
  interp₁ k j s h := by
    show cmpSign (4 * (gridMidpoint k j).val) (2 ^ (k + 1)) = s
    simp only [gridEmbed_val, gridEmbedRight_val, gridMidpoint_val,
               show 2 ^ (k + 1) = 2 * 2 ^ k from by omega] at *
    have e1 : 4 * (2 * j.val) = 8 * j.val := by omega
    have e2 : 4 * (2 * j.val + 2) = 8 * j.val + 8 := by omega
    have e3 : 4 * (2 * j.val + 1) = 8 * j.val + 4 := by omega
    rw [e1, e2] at h; rw [e3]
    unfold cmpSign at *; simp only [forcedMidpointSign] at h
    split_ifs at h ⊢ <;> simp_all <;> omega
  oppConvex₀ _ j₁ j₂ j hlo hhi h1 h2 := by
    show (cmpSign (4 * j.val) _).nonneg
    rw [cmpSign_nonneg_iff] at *
    have := Fin.val_le_of_le hlo; have := Fin.val_le_of_le hhi; omega
  oppConvex₁ _ j₁ j₂ j hlo hhi h1 h2 := by
    show (cmpSign (4 * j.val) _).nonneg
    rw [cmpSign_nonneg_iff] at *
    have := Fin.val_le_of_le hlo; have := Fin.val_le_of_le hhi; omega
  oppConvexNeg₀ _ j₁ j₂ j hlo hhi h1 h2 := by
    show (cmpSign (4 * j.val) _).flip.nonneg
    rw [cmpSign_flip] at *; rw [cmpSign_nonneg_iff] at *
    have := Fin.val_le_of_le hlo; have := Fin.val_le_of_le hhi; omega
  oppConvexNeg₁ _ j₁ j₂ j hlo hhi h1 h2 := by
    show (cmpSign (4 * j.val) _).flip.nonneg
    rw [cmpSign_flip] at *; rw [cmpSign_nonneg_iff] at *
    have := Fin.val_le_of_le hlo; have := Fin.val_le_of_le hhi; omega

theorem genBosTower_nash_sequence :
    ∀ k, ∃ σ, (genBosTower.game k).IsNash σ ∧
      (∀ i, (genBosTower.game k).OutsideDominated i σ) ∧
      genBosTower.toGeneralSignTower.IsConvexClosed k σ :=
  genBosTower.nash_sequence

-- Sign examples
example : genBosTower.oppSign₀ 0 ⟨0, by grid_omega⟩ = .pos := by decide
example : genBosTower.oppSign₀ 0 ⟨1, by grid_omega⟩ = .neg := by decide
example : genBosTower.oppSign₁ 0 ⟨0, by grid_omega⟩ = .pos := by decide
example : genBosTower.oppSign₁ 0 ⟨1, by grid_omega⟩ = .neg := by decide

example : genBosTower.oppSign₀ 1 ⟨0, by grid_omega⟩ = .pos := by decide
example : genBosTower.oppSign₀ 1 ⟨1, by grid_omega⟩ = .pos := by decide
example : genBosTower.oppSign₀ 1 ⟨2, by grid_omega⟩ = .neg := by decide
example : genBosTower.oppSign₁ 1 ⟨0, by grid_omega⟩ = .pos := by decide
example : genBosTower.oppSign₁ 1 ⟨1, by grid_omega⟩ = .neg := by decide
example : genBosTower.oppSign₁ 1 ⟨2, by grid_omega⟩ = .neg := by decide

end BilinearExamples
