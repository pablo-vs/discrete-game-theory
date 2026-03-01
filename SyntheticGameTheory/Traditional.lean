/-
  Traditional.lean — Bridge to standard game theory vocabulary

  This file provides:
  1. Type aliases mapping SignGame concepts to standard game theory terminology
  2. Convenience theorems for payoff-based game construction
  3. Concrete BilinearTower examples (Prisoner's Dilemma, Matching Pennies)
  4. Interpretive theorems about the refinement tower
-/

import SyntheticGameTheory.Unified
import SyntheticGameTheory.Refinement

namespace Unified

-- ================================================================
-- Section 1: Standard game theory vocabulary
-- ================================================================

/-- A type whose elements are pure actions for a player. -/
abbrev ActionSet := Type*

/-- A mixed strategy is represented by its support — the set of actions
    played with positive probability. This is a nonempty finite subset. -/
abbrev MixedStrategy (V : ActionSet) [DecidableEq V] := Face V

/-- A strategy profile (for a 2-player game) is a pair of mixed strategies. -/
abbrev StrategyProfile (V₀ V₁ : ActionSet) [DecidableEq V₀] [DecidableEq V₁] :=
  Face V₀ × Face V₁

/-- A pure strategy is a single action. -/
abbrev PureStrategy (V : ActionSet) := V

/-- A pure strategy profile is a pair of actions (one per player). -/
abbrev PureProfile (V₀ V₁ : ActionSet) := V₀ × V₁

-- ================================================================
-- Section 2: Dominance and Nash as renamings
-- ================================================================

variable {V₀ V₁ : Type*} [DecidableEq V₀] [DecidableEq V₁]
variable (G : SignGame V₀ V₁)

/-- "Face A weakly dominates face B for player 0, given opponent support F₁."
    This is exactly `DevFaceLE₀`. -/
abbrev WeaklyDominates₀ := G.DevFaceLE₀

/-- "Face A weakly dominates face B for player 1, given opponent support F₀." -/
abbrev WeaklyDominates₁ := G.DevFaceLE₁

/-- "σ is a Nash equilibrium (in the support-level sense)." -/
abbrev NashEquilibrium := G.IsNash

/-- "p is a pure Nash equilibrium." -/
abbrev PureNashEquilibrium := G.IsPureNash

-- The correspondence is definitional (rfl):
theorem weaklyDominates₀_eq_devFaceLE₀ :
    @WeaklyDominates₀ V₀ V₁ _ _ G = G.DevFaceLE₀ := rfl

theorem weaklyDominates₁_eq_devFaceLE₁ :
    @WeaklyDominates₁ V₀ V₁ _ _ G = G.DevFaceLE₁ := rfl

theorem nashEquilibrium_eq_isNash :
    @NashEquilibrium V₀ V₁ _ _ G = G.IsNash := rfl

theorem pureNashEquilibrium_eq_isPureNash :
    @PureNashEquilibrium V₀ V₁ _ _ G = G.IsPureNash := rfl

-- ================================================================
-- Section 3: Payoff-based Nash existence
-- ================================================================

/-- Every finite 2-player game with integer payoffs has a Nash equilibrium
    (in the support-level sense: there exist nonempty subsets of actions
    for each player such that no player can profitably deviate). -/
theorem nash_exists_of_payoffs [Fintype V₀] [Fintype V₁]
    [Nonempty V₀] [Nonempty V₁]
    (u : V₀ → V₁ → Int) (v : V₀ → V₁ → Int) :
    ∃ σ : StrategyProfile V₀ V₁, (SignGame.ofPayoffs u v).IsNash σ :=
  (SignGame.ofPayoffs u v).nash_exists

-- ================================================================
-- Section 4: Sign patterns and game classification (2×2)
-- ================================================================

/-- A 2×2 sign pattern: the signs of player 0's payoff comparisons
    at each of the two opponent actions. -/
structure SignPattern₂ where
  atOpp0 : Sign  -- sign₀(opp=0, action 0 vs action 1)
  atOpp1 : Sign  -- sign₀(opp=1, action 0 vs action 1)

/-- A 2×2 game is fully classified by two sign patterns (one per player). -/
structure GameClass₂ where
  player0 : SignPattern₂
  player1 : SignPattern₂

/-- Extract the sign classification of a 2×2 SignGame. -/
def classify₂ (G : SignGame (Fin 2) (Fin 2)) : GameClass₂ where
  player0 := ⟨G.sign₀ 0 0 1, G.sign₀ 1 0 1⟩
  player1 := ⟨G.sign₁ 0 0 1, G.sign₁ 1 0 1⟩

/-- Full-support Nash exists iff both players have a "flip" sign pattern —
    one action is better against one opponent action, the other is better
    against the other. This is the generic case for mixed Nash equilibria. -/
def SignPattern₂.isFlip (p : SignPattern₂) : Prop :=
  (p.atOpp0 = .pos ∧ p.atOpp1 = .neg) ∨
  (p.atOpp0 = .neg ∧ p.atOpp1 = .pos)

-- ================================================================
-- Section 5: Bilinear tower examples
-- ================================================================

/-- Prisoner's Dilemma bilinear tower.
    At every level k, D dominates C: oppSign = neg everywhere.
    The Nash equilibrium is (D,D) at every resolution. -/
def pdTower : BilinearTower where
  -- Both opponent-sign functions are constantly neg (D always dominates C)
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

/-- The PD tower has Nash + OD + interval-closed at every level. -/
theorem pdTower_nash_sequence :
    ∀ k, ∃ σ : Face (Fin (gridSize k)) × Face (Fin (gridSize k)),
      (pdTower.game k).IsNash σ ∧
      (pdTower.game k).OutsideDominated₀ σ ∧
      (pdTower.game k).OutsideDominated₁ σ ∧
      σ.1 = intervalClosure σ.1 ∧
      σ.2 = intervalClosure σ.2 :=
  pdTower.nash_refining_sequence

/-- Matching Pennies bilinear tower.
    oppSign flips between pos and neg, creating the (H,T)/(H,T) mixed Nash.
    At each level k, the flip happens at a grid point determined by the
    midpoint signs. -/
def mpTower : BilinearTower where
  oppSign₀ _ j := if j.val = 0 then .pos else .neg
  oppSign₁ _ j := if j.val = 0 then .neg else .pos
  coherent₀ k j := by
    show (if (embed k j).val = 0 then _ else _) = (if j.val = 0 then _ else _)
    simp only [embed_val]
    have : (2 * j.val = 0) ↔ (j.val = 0) := by omega
    split_ifs with h1 h2 <;> simp_all
  coherent₁ k j := by
    show (if (embed k j).val = 0 then _ else _) = (if j.val = 0 then _ else _)
    simp only [embed_val]
    have : (2 * j.val = 0) ↔ (j.val = 0) := by omega
    split_ifs with h1 h2 <;> simp_all
  interp₀ k j s h := by
    show (if (midpoint k j).val = 0 then _ else _) = s
    simp only [midpoint_val]
    have hm : 2 * j.val + 1 ≠ 0 := by omega
    simp only [hm, ↓reduceIte]
    show Sign.neg = s
    simp only [embed_val, embedRight_val] at h
    change (forcedMidpointSign (if 2 * j.val = 0 then .pos else .neg)
            (if 2 * j.val + 2 = 0 then .pos else .neg) = some s) at h
    by_cases hj0 : j.val = 0
    · -- j=0: left=pos, right=neg → forcedMidpointSign pos neg = none → absurd
      have h2 : (0 + 2 : ℕ) ≠ 0 := by omega
      simp only [hj0, Nat.mul_zero, ↓reduceIte, h2, forcedMidpointSign] at h
      exact absurd h nofun
    · -- j>0: both neg → forced neg
      have h1 : 2 * j.val ≠ 0 := by omega
      have h2 : 2 * j.val + 2 ≠ 0 := by omega
      simp only [h1, ↓reduceIte, h2, forcedMidpointSign] at h
      exact Option.some.inj h
  interp₁ k j s h := by
    show (if (midpoint k j).val = 0 then _ else _) = s
    simp only [midpoint_val]
    have hm : 2 * j.val + 1 ≠ 0 := by omega
    simp only [hm, ↓reduceIte]
    show Sign.pos = s
    simp only [embed_val, embedRight_val] at h
    change (forcedMidpointSign (if 2 * j.val = 0 then .neg else .pos)
            (if 2 * j.val + 2 = 0 then .neg else .pos) = some s) at h
    by_cases hj0 : j.val = 0
    · -- j=0: forcedMidpointSign neg pos = none, so h is absurd
      have h2 : (0 + 2 : ℕ) ≠ 0 := by omega
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
    · -- j₁ = 0, j₂ = 0, so j = 0
      have : j.val = 0 := by
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

/-- The Matching Pennies tower has Nash + OD + interval-closed at every level. -/
theorem mpTower_nash_sequence :
    ∀ k, ∃ σ : Face (Fin (gridSize k)) × Face (Fin (gridSize k)),
      (mpTower.game k).IsNash σ ∧
      (mpTower.game k).OutsideDominated₀ σ ∧
      (mpTower.game k).OutsideDominated₁ σ ∧
      σ.1 = intervalClosure σ.1 ∧
      σ.2 = intervalClosure σ.2 :=
  mpTower.nash_refining_sequence

/-- The Matching Pennies tower has Nash refinement at each level. -/
theorem mpTower_nash_refines (k : ℕ) :
    ∃ σ : Face (Fin (gridSize k)) × Face (Fin (gridSize k)),
    ∃ σ' : Face (Fin (gridSize (k + 1))) × Face (Fin (gridSize (k + 1))),
      (mpTower.game k).IsNash σ ∧
      (mpTower.game (k + 1)).IsNash σ' ∧
      ProfileRefines σ' σ :=
  mpTower.nash_at_next_level_refines k

private theorem cmpSign_mul2 {a b : ℕ} : cmpSign (2 * a) (2 * b) = cmpSign a b := by
  unfold cmpSign
  simp only [show ∀ a b : ℕ, (2 * a < 2 * b ↔ a < b) from fun a b => by omega]

/-- Symmetric Coordination bilinear tower.
    Payoffs: (2,2)/(0,0)/(0,0)/(2,2). Both players prefer to coordinate.
    oppSign₀ = oppSign₁ = cmpSign(2j, 2^k): both players' incentives are symmetric.
    The Nash equilibrium resolves to the exact midpoint at every level. -/
def symCoordTower : BilinearTower where
  oppSign₀ k j := cmpSign (2 * j.val) (2 ^ k)
  oppSign₁ k j := cmpSign (2 * j.val) (2 ^ k)
  coherent₀ k j := by
    show cmpSign (2 * (embed k j).val) (2 ^ (k + 1)) = cmpSign (2 * j.val) (2 ^ k)
    simp only [embed_val, show 2 ^ (k + 1) = 2 * 2 ^ k from by omega]
    exact cmpSign_mul2
  coherent₁ k j := by
    show cmpSign (2 * (embed k j).val) (2 ^ (k + 1)) = cmpSign (2 * j.val) (2 ^ k)
    simp only [embed_val, show 2 ^ (k + 1) = 2 * 2 ^ k from by omega]
    exact cmpSign_mul2
  interp₀ k j s h := by
    show cmpSign (2 * (midpoint k j).val) (2 ^ (k + 1)) = s
    simp only [embed_val, embedRight_val, midpoint_val,
               show 2 ^ (k + 1) = 2 * 2 ^ k from by omega] at *
    have e1 : 2 * (2 * j.val) = 4 * j.val := by omega
    have e2 : 2 * (2 * j.val + 2) = 4 * j.val + 4 := by omega
    have e3 : 2 * (2 * j.val + 1) = 4 * j.val + 2 := by omega
    rw [e1, e2] at h; rw [e3]
    unfold cmpSign at *; simp only [forcedMidpointSign] at h
    split_ifs at h ⊢ <;> simp_all <;> omega
  interp₁ k j s h := by
    show cmpSign (2 * (midpoint k j).val) (2 ^ (k + 1)) = s
    simp only [embed_val, embedRight_val, midpoint_val,
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

/-- The Symmetric Coordination tower has Nash + OD + interval-closed at every level. -/
theorem symCoordTower_nash_sequence :
    ∀ k, ∃ σ : Face (Fin (gridSize k)) × Face (Fin (gridSize k)),
      (symCoordTower.game k).IsNash σ ∧
      (symCoordTower.game k).OutsideDominated₀ σ ∧
      (symCoordTower.game k).OutsideDominated₁ σ ∧
      σ.1 = intervalClosure σ.1 ∧
      σ.2 = intervalClosure σ.2 :=
  symCoordTower.nash_refining_sequence

/-- The Symmetric Coordination tower has Nash refinement at each level. -/
theorem symCoordTower_nash_refines (k : ℕ) :
    ∃ σ : Face (Fin (gridSize k)) × Face (Fin (gridSize k)),
    ∃ σ' : Face (Fin (gridSize (k + 1))) × Face (Fin (gridSize (k + 1))),
      (symCoordTower.game k).IsNash σ ∧
      (symCoordTower.game (k + 1)).IsNash σ' ∧
      ProfileRefines σ' σ :=
  symCoordTower.nash_at_next_level_refines k

-- Symmetric Coordination: both players have identical sign patterns.
-- The indifference point (zero) is at the exact midpoint j = 2^(k-1).

-- Level 0 (2-point grid): (pos, neg) — full support mixed Nash
example : symCoordTower.oppSign₀ 0 ⟨0, by grid_omega⟩ = .pos := by decide
example : symCoordTower.oppSign₀ 0 ⟨1, by grid_omega⟩ = .neg := by decide

-- Level 1 (3-point grid): (pos, zero, neg) — indifference at midpoint j=1
example : symCoordTower.oppSign₀ 1 ⟨0, by grid_omega⟩ = .pos := by decide
example : symCoordTower.oppSign₀ 1 ⟨1, by grid_omega⟩ = .zero := by decide
example : symCoordTower.oppSign₀ 1 ⟨2, by grid_omega⟩ = .neg := by decide

-- Level 2 (5-point grid): (pos, pos, zero, neg, neg) — indifference at midpoint j=2
example : symCoordTower.oppSign₀ 2 ⟨0, by grid_omega⟩ = .pos := by decide
example : symCoordTower.oppSign₀ 2 ⟨1, by grid_omega⟩ = .pos := by decide
example : symCoordTower.oppSign₀ 2 ⟨2, by grid_omega⟩ = .zero := by decide
example : symCoordTower.oppSign₀ 2 ⟨3, by grid_omega⟩ = .neg := by decide
example : symCoordTower.oppSign₀ 2 ⟨4, by grid_omega⟩ = .neg := by decide

/-- Battle of the Sexes bilinear tower.
    Payoffs: (3,1)/(0,0)/(0,0)/(1,3). Players prefer different coordination points.
    oppSign₀ = cmpSign(4j, 3·2^k): player 0 crosses at the 3/4 point.
    oppSign₁ = cmpSign(4j, 2^k): player 1 crosses at the 1/4 point.
    The Nash equilibrium resolves asymmetrically at every level. -/
def bosTower : BilinearTower where
  oppSign₀ k j := cmpSign (4 * j.val) (3 * 2 ^ k)
  oppSign₁ k j := cmpSign (4 * j.val) (2 ^ k)
  coherent₀ k j := by
    show cmpSign (4 * (embed k j).val) (3 * 2 ^ (k + 1)) = cmpSign (4 * j.val) (3 * 2 ^ k)
    simp only [embed_val, show 3 * 2 ^ (k + 1) = 2 * (3 * 2 ^ k) from by omega]
    show cmpSign (4 * (2 * j.val)) (2 * (3 * 2 ^ k)) = cmpSign (4 * j.val) (3 * 2 ^ k)
    have : 4 * (2 * j.val) = 2 * (4 * j.val) := by omega
    rw [this]; exact cmpSign_mul2
  coherent₁ k j := by
    show cmpSign (4 * (embed k j).val) (2 ^ (k + 1)) = cmpSign (4 * j.val) (2 ^ k)
    simp only [embed_val, show 2 ^ (k + 1) = 2 * 2 ^ k from by omega]
    show cmpSign (4 * (2 * j.val)) (2 * 2 ^ k) = cmpSign (4 * j.val) (2 ^ k)
    have : 4 * (2 * j.val) = 2 * (4 * j.val) := by omega
    rw [this]; exact cmpSign_mul2
  interp₀ k j s h := by
    show cmpSign (4 * (midpoint k j).val) (3 * 2 ^ (k + 1)) = s
    simp only [embed_val, embedRight_val, midpoint_val,
               show 3 * 2 ^ (k + 1) = 2 * (3 * 2 ^ k) from by omega] at *
    have e1 : 4 * (2 * j.val) = 8 * j.val := by omega
    have e2 : 4 * (2 * j.val + 2) = 8 * j.val + 8 := by omega
    have e3 : 4 * (2 * j.val + 1) = 8 * j.val + 4 := by omega
    rw [e1, e2] at h; rw [e3]
    unfold cmpSign at *; simp only [forcedMidpointSign] at h
    split_ifs at h ⊢ <;> simp_all <;> omega
  interp₁ k j s h := by
    show cmpSign (4 * (midpoint k j).val) (2 ^ (k + 1)) = s
    simp only [embed_val, embedRight_val, midpoint_val,
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

/-- The Battle of the Sexes tower has Nash + OD + interval-closed at every level. -/
theorem bosTower_nash_sequence :
    ∀ k, ∃ σ : Face (Fin (gridSize k)) × Face (Fin (gridSize k)),
      (bosTower.game k).IsNash σ ∧
      (bosTower.game k).OutsideDominated₀ σ ∧
      (bosTower.game k).OutsideDominated₁ σ ∧
      σ.1 = intervalClosure σ.1 ∧
      σ.2 = intervalClosure σ.2 :=
  bosTower.nash_refining_sequence

/-- The Battle of the Sexes tower has Nash refinement at each level. -/
theorem bosTower_nash_refines (k : ℕ) :
    ∃ σ : Face (Fin (gridSize k)) × Face (Fin (gridSize k)),
    ∃ σ' : Face (Fin (gridSize (k + 1))) × Face (Fin (gridSize (k + 1))),
      (bosTower.game k).IsNash σ ∧
      (bosTower.game (k + 1)).IsNash σ' ∧
      ProfileRefines σ' σ :=
  bosTower.nash_at_next_level_refines k

-- Battle of the Sexes: players have *different* sign patterns.
-- Player 0 crosses at j = 3·2^(k-2) (3/4 of grid), player 1 at j = 2^(k-2) (1/4).

-- Level 0 (2-point grid): both (pos, neg) — full support mixed Nash
example : bosTower.oppSign₀ 0 ⟨0, by grid_omega⟩ = .pos := by decide
example : bosTower.oppSign₀ 0 ⟨1, by grid_omega⟩ = .neg := by decide
example : bosTower.oppSign₁ 0 ⟨0, by grid_omega⟩ = .pos := by decide
example : bosTower.oppSign₁ 0 ⟨1, by grid_omega⟩ = .neg := by decide

-- Level 1 (3-point grid): P0 = (pos, pos, neg), P1 = (pos, neg, neg)
-- Players disagree at j=1: P0 still prefers action 0, P1 already prefers action 1
example : bosTower.oppSign₀ 1 ⟨0, by grid_omega⟩ = .pos := by decide
example : bosTower.oppSign₀ 1 ⟨1, by grid_omega⟩ = .pos := by decide
example : bosTower.oppSign₀ 1 ⟨2, by grid_omega⟩ = .neg := by decide
example : bosTower.oppSign₁ 1 ⟨0, by grid_omega⟩ = .pos := by decide
example : bosTower.oppSign₁ 1 ⟨1, by grid_omega⟩ = .neg := by decide
example : bosTower.oppSign₁ 1 ⟨2, by grid_omega⟩ = .neg := by decide

-- Level 2 (5-point grid):
-- P0 = (pos, pos, pos, zero, neg) — crosses at j=3
-- P1 = (pos, zero, neg, neg, neg) — crosses at j=1
-- This asymmetry reflects the (3/4, 1/4) mixed Nash of BoS
example : bosTower.oppSign₀ 2 ⟨0, by grid_omega⟩ = .pos := by decide
example : bosTower.oppSign₀ 2 ⟨2, by grid_omega⟩ = .pos := by decide
example : bosTower.oppSign₀ 2 ⟨3, by grid_omega⟩ = .zero := by decide
example : bosTower.oppSign₀ 2 ⟨4, by grid_omega⟩ = .neg := by decide
example : bosTower.oppSign₁ 2 ⟨0, by grid_omega⟩ = .pos := by decide
example : bosTower.oppSign₁ 2 ⟨1, by grid_omega⟩ = .zero := by decide
example : bosTower.oppSign₁ 2 ⟨2, by grid_omega⟩ = .neg := by decide
example : bosTower.oppSign₁ 2 ⟨4, by grid_omega⟩ = .neg := by decide

-- ================================================================
-- Section 6: Interpretive theorems
-- ================================================================

/-- At level 0, a bilinear tower's game has exactly 2 grid points (0 and 1),
    matching the 2 pure actions of the underlying 2-action game. -/
theorem level_zero_gridSize : gridSize 0 = 2 := by simp [gridSize]

/-- The tower is monotone: each level's sign data extends the previous
    via the coherence condition. -/
theorem tower_extends (t : BilinearTower) (k : ℕ) :
    @Coherent k (t.game (k + 1)) (t.game k) :=
  t.game_coherent k

/-- Nash equilibria refine: at each level there exists a Nash profile,
    and at the next level there exists a Nash profile that refines it. -/
theorem tower_nash_refines (t : BilinearTower) (k : ℕ) :
    ∃ σ : Face (Fin (gridSize k)) × Face (Fin (gridSize k)),
    ∃ σ' : Face (Fin (gridSize (k + 1))) × Face (Fin (gridSize (k + 1))),
      (t.game k).IsNash σ ∧
      (t.game (k + 1)).IsNash σ' ∧
      ProfileRefines σ' σ :=
  t.nash_at_next_level_refines k

/-- Each bilinear tower game is grid-monotone: sign comparisons depend only
    on the relative ordering of grid points, not their absolute positions. -/
theorem tower_gridMonotone (t : BilinearTower) (k : ℕ) :
    GridMonotone (t.game k) :=
  t.game_gridMonotone k

/-- Each bilinear tower game has opponent-convex sign structure: the set
    of opponent grid points where a comparison is nonneg forms an interval. -/
theorem tower_opponentConvex (t : BilinearTower) (k : ℕ) :
    OpponentConvex (t.game k) :=
  t.game_opponentConvex k

end Unified
