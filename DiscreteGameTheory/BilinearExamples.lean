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

import DiscreteGameTheory.Refinement

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
    sign(i, p, a, b) = mul(cmpSign b a, oppSign i (p(1-i)))
    where oppSign i is a sign function depending on the opponent's action. -/
def bilinearSignGame (n : ℕ) (oppSign : Fin 2 → Fin n → Sign) :
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
    Specifies per-player opponent-sign functions at each level,
    with coherence, interpolation, and convexity axioms. -/
structure GenBilinearTower where
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

theorem cmpSign_double (a b : ℕ) : cmpSign (2 * a) (2 * b) = cmpSign a b := by
  unfold cmpSign; simp only [Nat.mul_lt_mul_left (show 0 < 2 by omega)]

namespace GenBilinearTower

variable (t : GenBilinearTower)

/-- The sign game at level k. -/
def game (k : ℕ) : Base.SignGame (Fin 2) (fun _ : Fin 2 => Fin (gridSize k)) :=
  bilinearSignGame (gridSize k) (fun i => t.oppSign i k)

-- ================================================================
-- Section 4: oppSign nonneg/flip interval lemmas
-- ================================================================

/-- Generic interval lemma: if P holds at all even grid points in [c, d],
    and the interpolation and forced-midpoint properties match, then P holds
    at all fine grid points in [embed c, embed d]. -/
private theorem oppSign_interval_generic {k : ℕ}
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

/-- oppSign nonneg at even points in [c, d] → nonneg at all fine points in [embed c, embed d]. -/
theorem oppSign_nonneg_interval (i : Fin 2) {k : ℕ}
    {c d : Fin (gridSize k)}
    (h_even : ∀ (j : Fin (gridSize k)), c ≤ j → j ≤ d →
      (t.oppSign i (k + 1) (gridEmbed k j)).nonneg)
    {j : Fin (gridSize (k + 1))} (hj_lo : gridEmbed k c ≤ j) (hj_hi : j ≤ gridEmbed k d) :
    (t.oppSign i (k + 1) j).nonneg :=
  oppSign_interval_generic (t.oppSign i (k + 1)) (t.interp i k) Sign.nonneg
    (fun _ _ => forcedMidpoint_of_nonneg_nonneg) h_even hj_lo hj_hi

theorem oppSign_flip_nonneg_interval (i : Fin 2) {k : ℕ}
    {c d : Fin (gridSize k)}
    (h_even : ∀ (j : Fin (gridSize k)), c ≤ j → j ≤ d →
      (t.oppSign i (k + 1) (gridEmbed k j)).flip.nonneg)
    {j : Fin (gridSize (k + 1))} (hj_lo : gridEmbed k c ≤ j) (hj_hi : j ≤ gridEmbed k d) :
    (t.oppSign i (k + 1) j).flip.nonneg :=
  oppSign_interval_generic (t.oppSign i (k + 1)) (t.interp i k) (Sign.nonneg ∘ Sign.flip)
    (fun _ _ => forcedMidpoint_of_flip_nonneg) h_even hj_lo hj_hi

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
def toGeneralSignTower : GeneralSignTower (Fin 2) where
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
    simp only [game, bilinearSignGame, gridEmbed_val, cmpSign_double, t.coherent]
  playerConvex_left k i p a b c x hbtw ha hb := by
    simp only [game, bilinearSignGame] at *
    simp only [finBetweenness] at hbtw
    have hlo : min a.val b.val ≤ c.val := by
      rw [← Fin.coe_min]; exact Fin.val_le_of_le hbtw.1
    have hhi : c.val ≤ max a.val b.val := by
      rw [← Fin.coe_max]; exact Fin.val_le_of_le hbtw.2
    exact mul_cmpSign_between_left hlo hhi ha hb
  playerConvex_right k i p a b c x hbtw ha hb := by
    simp only [game, bilinearSignGame] at *
    simp only [finBetweenness] at hbtw
    have hlo : min a.val b.val ≤ c.val := by
      rw [← Fin.coe_min]; exact Fin.val_le_of_le hbtw.1
    have hhi : c.val ≤ max a.val b.val := by
      rw [← Fin.coe_max]; exact Fin.val_le_of_le hbtw.2
    exact mul_cmpSign_between_right hlo hhi ha hb
  opponentConvex k i j hj p q a b hp_eq r hr_eq hbtw hp hq := by
    simp only [game, bilinearSignGame] at *
    have hji : j = 1 - i := by fin_cases i <;> fin_cases j <;> simp_all
    subst hji
    simp only [finBetweenness] at hbtw
    -- The cmpSign(b,a) factor is fixed; oppSign varies with opponent's action
    -- Use min/max to apply oppConvex_to_mul_convex
    have hbtw' : min (p (1-i)) (q (1-i)) ≤ r (1-i) ∧ r (1-i) ≤ max (p (1-i)) (q (1-i)) := hbtw
    have hmin_nn : ((cmpSign b.val a.val).mul (t.oppSign i k (min (p (1-i)) (q (1-i))))).nonneg := by
      rcases min_choice (p (1-i)) (q (1-i)) with h | h <;> rw [h] <;> assumption
    have hmax_nn : ((cmpSign b.val a.val).mul (t.oppSign i k (max (p (1-i)) (q (1-i))))).nonneg := by
      rcases max_choice (p (1-i)) (q (1-i)) with h | h <;> rw [h] <;> assumption
    exact oppConvex_to_mul_convex (t.oppConvex i k) (t.oppConvexNeg i k)
      (cmpSign b.val a.val) (min (p (1-i)) (q (1-i))) (max (p (1-i)) (q (1-i))) (r (1-i))
      hbtw'.1 hbtw'.2 hmin_nn hmax_nn
  fine_between_embedded_at k _ := fine_between_gridEmbed k

-- ================================================================
-- Section 7: Nash existence theorems
-- ================================================================

/-- Nash + OD + convex-closed at every level. -/
theorem nash_sequence :
    ∀ k, ∃ σ : Base.Profile (Fin 2) (fun _ : Fin 2 => Fin (gridSize k)),
      (t.game k).IsNash σ ∧
      (∀ i, (t.game k).OutsideDom i σ) ∧
      t.toGeneralSignTower.HasConvexFaces k σ :=
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
-- Section 8: Prisoner's Dilemma tower
-- ================================================================

def genPdTower : GenBilinearTower where
  oppSign _ _ _ := .neg
  coherent _ _ _ := rfl
  interp _ _ _ s h := by simp [forcedMidpointSign] at h; exact h
  oppConvex _ _ _ _ _ _ _ h₁ _ := absurd h₁ Sign.not_nonneg_neg
  oppConvexNeg _ _ _ _ _ _ _ _ _ := trivial

theorem genPdTower_nash_sequence :
    ∀ k, ∃ σ, (genPdTower.game k).IsNash σ ∧
      (∀ i, (genPdTower.game k).OutsideDom i σ) ∧
      genPdTower.toGeneralSignTower.HasConvexFaces k σ :=
  genPdTower.nash_sequence

-- ================================================================
-- Section 10: Matching Pennies tower
-- ================================================================

def genMpTower : GenBilinearTower where
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
    -- At any midpoint (which is nonzero), oppSign i is the "nonzero" value
    -- The forced midpoint is only some when both endpoints agree
    by_cases hj0 : j.val = 0
    · -- j=0: left endpoint is the j=0 value, right is nonzero value → they disagree → none
      simp only [hj0, Nat.mul_zero, show (0 + 2 : ℕ) ≠ 0 from by omega, ↓reduceIte] at h
      fin_cases i <;> simp [forcedMidpointSign] at h
    · have h1 : 2 * j.val ≠ 0 := by omega
      have h2 : 2 * j.val + 2 ≠ 0 := by omega
      simp only [h1, h2, ↓reduceIte, forcedMidpointSign] at h
      fin_cases i <;> simp_all [forcedMidpointSign] <;> exact Option.some.inj h
  oppConvex i _ j₁ j₂ j hlo hhi h1 h2 := by
    fin_cases i <;> {
      simp only [Fin.isValue] at *
      split_ifs at h1 h2 ⊢ with h1' h2' <;>
        first | trivial | exact absurd h1 id | exact absurd h2 id |
        (have := Fin.val_le_of_le hlo; have := Fin.val_le_of_le hhi; omega) }
  oppConvexNeg i _ j₁ j₂ j hlo hhi h1 h2 := by
    fin_cases i <;> {
      simp only [Fin.isValue] at *
      split_ifs at h1 h2 ⊢ with h1' h2' <;> simp_all [Sign.flip, Sign.nonneg] <;>
        first | trivial | (have := Fin.val_le_of_le hlo; have := Fin.val_le_of_le hhi; omega) }

theorem genMpTower_nash_sequence :
    ∀ k, ∃ σ, (genMpTower.game k).IsNash σ ∧
      (∀ i, (genMpTower.game k).OutsideDom i σ) ∧
      genMpTower.toGeneralSignTower.HasConvexFaces k σ :=
  genMpTower.nash_sequence

-- ================================================================
-- Section 11: Symmetric Coordination tower
-- ================================================================

def genSymCoordTower : GenBilinearTower where
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

theorem genSymCoordTower_nash_sequence :
    ∀ k, ∃ σ, (genSymCoordTower.game k).IsNash σ ∧
      (∀ i, (genSymCoordTower.game k).OutsideDom i σ) ∧
      genSymCoordTower.toGeneralSignTower.HasConvexFaces k σ :=
  genSymCoordTower.nash_sequence

-- Sign examples at levels 0-2
example : genSymCoordTower.oppSign 0 0 ⟨0, by grid_omega⟩ = .pos := by decide
example : genSymCoordTower.oppSign 0 0 ⟨1, by grid_omega⟩ = .neg := by decide
example : genSymCoordTower.oppSign 0 1 ⟨0, by grid_omega⟩ = .pos := by decide
example : genSymCoordTower.oppSign 0 1 ⟨1, by grid_omega⟩ = .zero := by decide
example : genSymCoordTower.oppSign 0 1 ⟨2, by grid_omega⟩ = .neg := by decide

-- ================================================================
-- Section 12: Battle of the Sexes tower
-- ================================================================

def genBosTower : GenBilinearTower where
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
      simp only [show 3 * 2 ^ (k + 1) = 2 * (3 * 2 ^ k) from by omega,
                 show 2 ^ (k + 1) = 2 * 2 ^ k from by omega] at *
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

theorem genBosTower_nash_sequence :
    ∀ k, ∃ σ, (genBosTower.game k).IsNash σ ∧
      (∀ i, (genBosTower.game k).OutsideDom i σ) ∧
      genBosTower.toGeneralSignTower.HasConvexFaces k σ :=
  genBosTower.nash_sequence

-- Sign examples (player 0 = row, player 1 = column)
example : genBosTower.oppSign 0 0 ⟨0, by grid_omega⟩ = .pos := by decide
example : genBosTower.oppSign 0 0 ⟨1, by grid_omega⟩ = .neg := by decide
example : genBosTower.oppSign 1 0 ⟨0, by grid_omega⟩ = .pos := by decide
example : genBosTower.oppSign 1 0 ⟨1, by grid_omega⟩ = .neg := by decide

example : genBosTower.oppSign 0 1 ⟨0, by grid_omega⟩ = .pos := by decide
example : genBosTower.oppSign 0 1 ⟨1, by grid_omega⟩ = .pos := by decide
example : genBosTower.oppSign 0 1 ⟨2, by grid_omega⟩ = .neg := by decide
example : genBosTower.oppSign 1 1 ⟨0, by grid_omega⟩ = .pos := by decide
example : genBosTower.oppSign 1 1 ⟨1, by grid_omega⟩ = .neg := by decide
example : genBosTower.oppSign 1 1 ⟨2, by grid_omega⟩ = .neg := by decide

end BilinearExamples
