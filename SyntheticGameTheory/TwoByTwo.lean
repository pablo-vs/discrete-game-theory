/-
  2×2 Games, Crossing-Based Nash Proof, and Example Games

  This file contains the specialized 2×2 game theory machinery that is
  independent of the general Nash existence theorem. It demonstrates axiom
  economy (no Kakutani or order preservation needed — only Crossing Axiom)
  but is not on the critical path for the general framework.

  Moved from SyntheticGameTheory.lean to reduce main file size.
-/

import SyntheticGameTheory

universe u v

/-! ## 2×2 Games -/

section TwoByTwo

/-- A 2×2 game: two players, each with two actions -/
structure TwoByTwoGame where
  R : Type*
  instR : LinearOrder R
  u1_TL : R
  u1_TR : R
  u1_BL : R
  u1_BR : R
  u2_TL : R
  u2_TR : R
  u2_BL : R
  u2_BR : R

attribute [instance] TwoByTwoGame.instR

/-- Player 1's strategies -/
inductive P1Strategy | Top | Bottom
  deriving DecidableEq

instance : Fintype P1Strategy where
  elems := {P1Strategy.Top, P1Strategy.Bottom}
  complete := fun x => by cases x <;> simp

/-- Player 2's strategies -/
inductive P2Strategy | Left | Right
  deriving DecidableEq

instance : Fintype P2Strategy where
  elems := {P2Strategy.Left, P2Strategy.Right}
  complete := fun x => by cases x <;> simp

/-- A pure Nash exists if some cell is a mutual best response -/
def TwoByTwoGame.hasPureNash (G : TwoByTwoGame) : Prop :=
  (G.u1_BL ≤ G.u1_TL ∧ G.u2_TR ≤ G.u2_TL) ∨
  (G.u1_BR ≤ G.u1_TR ∧ G.u2_TL ≤ G.u2_TR) ∨
  (G.u1_TL ≤ G.u1_BL ∧ G.u2_BR ≤ G.u2_BL) ∨
  (G.u1_TR ≤ G.u1_BR ∧ G.u2_BL ≤ G.u2_BR)

/-- Best response cycling: no pure Nash, preferences cycle (player 2 only).
    Superseded by `fullCycling` but kept for compatibility. -/
@[deprecated "Use fullCycling instead." (since := "2026-01-31")]
def TwoByTwoGame.hasCycling (G : TwoByTwoGame) : Prop :=
  ¬G.hasPureNash ∧
  ((G.u2_TR < G.u2_TL ∧ G.u2_BL < G.u2_BR) ∨
   (G.u2_TL < G.u2_TR ∧ G.u2_BR < G.u2_BL))

/-- Full cycling: both players' preferences cross.
    Case 1: P1 prefers B@L, T@R; P2 prefers L@T, R@B
    Case 2: P1 prefers T@L, B@R; P2 prefers R@T, L@B -/
def TwoByTwoGame.fullCycling (G : TwoByTwoGame) : Prop :=
  (G.u1_TL < G.u1_BL ∧ G.u1_BR < G.u1_TR ∧
   G.u2_TR < G.u2_TL ∧ G.u2_BL < G.u2_BR) ∨
  (G.u1_BL < G.u1_TL ∧ G.u1_TR < G.u1_BR ∧
   G.u2_TL < G.u2_TR ∧ G.u2_BR < G.u2_BL)

/-- Full cycling implies (deprecated) player-2-only cycling. -/
lemma TwoByTwoGame.hasCycling_of_fullCycling (G : TwoByTwoGame) :
    G.fullCycling → G.hasCycling := by
  intro h
  rcases h with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · have hnp : ¬ G.hasPureNash := by
      intro hnp
      rcases hnp with h | h | h | h
      · exact (not_lt_of_ge h.1) h1
      · exact (not_lt_of_ge h.2) h3
      · exact (not_lt_of_ge h.2) h4
      · exact (not_lt_of_ge h.1) h2
    exact ⟨hnp, Or.inl ⟨h3, h4⟩⟩
  · have hnp : ¬ G.hasPureNash := by
      intro hnp
      rcases hnp with h | h | h | h
      · exact (not_lt_of_ge h.2) h3
      · exact (not_lt_of_ge h.1) h2
      · exact (not_lt_of_ge h.1) h1
      · exact (not_lt_of_ge h.2) h4
    exact ⟨hnp, Or.inr ⟨h3, h4⟩⟩

/-- In a 2×2 game with LinearOrder, absence of a pure Nash implies full cycling:
    both players' preferences must cross. -/
lemma TwoByTwoGame.no_pure_implies_full_cycling (G : TwoByTwoGame)
    (h : ¬G.hasPureNash) : G.fullCycling := by
  simp only [hasPureNash, not_or] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [not_and_or] at h1 h2 h3 h4
  simp only [not_le] at h1 h2 h3 h4
  unfold fullCycling
  rcases lt_trichotomy G.u2_TL G.u2_TR with htop | htop | htop
  · -- Case: u2_TL < u2_TR → second disjunct of fullCycling
    right
    have p2 : G.u1_TR < G.u1_BR := h2.resolve_right (not_lt.mpr (le_of_lt htop))
    have p4 : G.u2_BR < G.u2_BL := h4.resolve_left (not_lt.mpr (le_of_lt p2))
    have p3 : G.u1_BL < G.u1_TL := h3.resolve_right (not_lt.mpr (le_of_lt p4))
    exact ⟨p3, p2, htop, p4⟩
  · -- Case: u2_TL = u2_TR → contradiction
    have p1 : G.u1_TL < G.u1_BL := h1.resolve_right (htop ▸ lt_irrefl _)
    have p2 : G.u1_TR < G.u1_BR := h2.resolve_right (htop ▸ lt_irrefl _)
    have p4 : G.u2_BR < G.u2_BL := h4.resolve_left (not_lt.mpr (le_of_lt p2))
    have p3 : G.u1_BL < G.u1_TL := h3.resolve_right (not_lt.mpr (le_of_lt p4))
    exact absurd p3 (not_lt.mpr (le_of_lt p1))
  · -- Case: u2_TR < u2_TL → first disjunct of fullCycling
    left
    have p1 : G.u1_TL < G.u1_BL := h1.resolve_right (not_lt.mpr (le_of_lt htop))
    have p3 : G.u2_BL < G.u2_BR := h3.resolve_left (not_lt.mpr (le_of_lt p1))
    have p4 : G.u1_BR < G.u1_TR := h4.resolve_right (not_lt.mpr (le_of_lt p3))
    exact ⟨p1, p4, htop, p3⟩

/-- Generic crossing lemma: if f and g are betweenness-respecting and cross,
    there exists a common value. Wraps CrossingAxiom for direct use. -/
lemma crossing_gives_common_value {I : Type u} {R : Type*}
    [SyntheticInterval I] [LinearOrder R] [CrossingAxiom I R]
    {f g : I → R} (hf : weakBetweenness f) (hg : weakBetweenness g)
    (hf0_le_g0 : f SyntheticInterval.zero ≤ g SyntheticInterval.zero)
    (hg1_le_f1 : g SyntheticInterval.one ≤ f SyntheticInterval.one) :
    ∃ p : I, f p = g p :=
  CrossingAxiom.crossing_point f g hf hg (Or.inl ⟨hf0_le_g0, hg1_le_f1⟩)

/-- Symmetric version: g starts above f and f ends above g. -/
lemma crossing_gives_common_value' {I : Type u} {R : Type*}
    [SyntheticInterval I] [LinearOrder R] [CrossingAxiom I R]
    {f g : I → R} (hf : weakBetweenness f) (hg : weakBetweenness g)
    (hg0_le_f0 : g SyntheticInterval.zero ≤ f SyntheticInterval.zero)
    (hf1_le_g1 : f SyntheticInterval.one ≤ g SyntheticInterval.one) :
    ∃ p : I, f p = g p :=
  CrossingAxiom.crossing_point f g hf hg (Or.inr ⟨hg0_le_f0, hf1_le_g1⟩)

/-- Main theorem for 2×2 games: either a pure Nash exists, or given
    betweenness-respecting payoff extensions along the mixing edges,
    indifference points exist for both players.

    Boundary conventions:
    - f₁(0→1) = u1(Top, Left→Right): Player 1's Top payoff as P2 varies
    - g₁(0→1) = u1(Bottom, Left→Right): Player 1's Bottom payoff as P2 varies
    - f₂(0→1) = u2(Top→Bottom, Left): Player 2's Left payoff as P1 varies
    - g₂(0→1) = u2(Top→Bottom, Right): Player 2's Right payoff as P1 varies -/
theorem TwoByTwoGame.twoByTwo_nash_exists
    (G : TwoByTwoGame) (I : Type u) [SyntheticInterval I] [CrossingAxiom I G.R] :
    G.hasPureNash ∨ (∀ (f₁ g₁ f₂ g₂ : I → G.R),
      weakBetweenness f₁ → weakBetweenness g₁ →
      weakBetweenness f₂ → weakBetweenness g₂ →
      -- f₁ = P1's payoff from Top as P2 varies Left(0)→Right(1)
      f₁ SyntheticInterval.zero = G.u1_TL →
      f₁ SyntheticInterval.one = G.u1_TR →
      -- g₁ = P1's payoff from Bottom as P2 varies Left(0)→Right(1)
      g₁ SyntheticInterval.zero = G.u1_BL →
      g₁ SyntheticInterval.one = G.u1_BR →
      -- f₂ = P2's payoff from Left as P1 varies Top(0)→Bottom(1)
      f₂ SyntheticInterval.zero = G.u2_TL →
      f₂ SyntheticInterval.one = G.u2_BL →
      -- g₂ = P2's payoff from Right as P1 varies Top(0)→Bottom(1)
      g₂ SyntheticInterval.zero = G.u2_TR →
      g₂ SyntheticInterval.one = G.u2_BR →
      -- Both players have indifference points
      (∃ p : I, f₂ p = g₂ p) ∧ (∃ q : I, f₁ q = g₁ q)) := by
  by_cases h : G.hasPureNash
  · left; exact h
  · right
    intro f₁ g₁ f₂ g₂ hf₁ hg₁ hf₂ hg₂ hf₁0 hf₁1 hg₁0 hg₁1 hf₂0 hf₂1 hg₂0 hg₂1
    have hfc := G.no_pure_implies_full_cycling h
    constructor
    · -- Player 2's indifference point: f₂ and g₂ cross
      rcases hfc with ⟨_, _, h_p2_top, h_p2_bot⟩ | ⟨_, _, h_p2_top, h_p2_bot⟩
      · exact crossing_gives_common_value' hf₂ hg₂
          (by rw [hg₂0, hf₂0]; exact le_of_lt h_p2_top)
          (by rw [hf₂1, hg₂1]; exact le_of_lt h_p2_bot)
      · exact crossing_gives_common_value hf₂ hg₂
          (by rw [hf₂0, hg₂0]; exact le_of_lt h_p2_top)
          (by rw [hg₂1, hf₂1]; exact le_of_lt h_p2_bot)
    · -- Player 1's indifference point: f₁ and g₁ cross
      rcases hfc with ⟨h_p1_left, h_p1_right, _, _⟩ | ⟨h_p1_left, h_p1_right, _, _⟩
      · exact crossing_gives_common_value hf₁ hg₁
          (by rw [hf₁0, hg₁0]; exact le_of_lt h_p1_left)
          (by rw [hg₁1, hf₁1]; exact le_of_lt h_p1_right)
      · exact crossing_gives_common_value' hf₁ hg₁
          (by rw [hg₁0, hf₁0]; exact le_of_lt h_p1_left)
          (by rw [hf₁1, hg₁1]; exact le_of_lt h_p1_right)

end TwoByTwo


/-! ## Example Games -/

section Examples

/-- Matching Pennies: 2×2 game with no pure Nash equilibrium.
    Player 1 wins when both choose the same side, Player 2 wins on mismatch. -/
def matchingPennies : TwoByTwoGame where
  R := Fin 2
  instR := inferInstance
  u1_TL := 1; u1_TR := 0; u1_BL := 0; u1_BR := 1
  u2_TL := 0; u2_TR := 1; u2_BL := 1; u2_BR := 0

/-- Matching Pennies has no pure Nash equilibrium -/
theorem matchingPennies_no_pure_nash : ¬matchingPennies.hasPureNash := by
  simp only [matchingPennies, TwoByTwoGame.hasPureNash]
  rintro (⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩) <;> revert h <;> decide

/-- Matching Pennies exhibits full cycling -/
theorem matchingPennies_has_fullCycling : matchingPennies.fullCycling := by
  simp [matchingPennies, TwoByTwoGame.fullCycling]

/-- Matching Pennies exhibits cycling -/
@[deprecated "Use matchingPennies_has_fullCycling." (since := "2026-01-31")]
theorem matchingPennies_has_cycling : matchingPennies.hasCycling := by
  exact (TwoByTwoGame.hasCycling_of_fullCycling (G := matchingPennies)
    matchingPennies_has_fullCycling)

/-- Prisoner's Dilemma: 2×2 game with a unique pure Nash equilibrium (Defect, Defect).
    Utilities: 0=sucker, 1=punish, 2=reward, 3=temptation -/
def prisonersDilemma : TwoByTwoGame where
  R := Fin 4
  instR := inferInstance
  u1_TL := 2; u1_TR := 0; u1_BL := 3; u1_BR := 1
  u2_TL := 2; u2_TR := 3; u2_BL := 0; u2_BR := 1

/-- Prisoner's Dilemma has a pure Nash equilibrium (Bottom-Right = Defect-Defect) -/
theorem prisonersDilemma_has_pure_nash : prisonersDilemma.hasPureNash := by
  unfold prisonersDilemma TwoByTwoGame.hasPureNash
  right; right; right
  exact ⟨by decide, by decide⟩

/-- Battle of the Sexes: 2×2 game with two pure Nash equilibria -/
def battleOfSexes : TwoByTwoGame where
  R := Fin 3
  instR := inferInstance
  u1_TL := 2; u1_TR := 0; u1_BL := 0; u1_BR := 1
  u2_TL := 1; u2_TR := 0; u2_BL := 0; u2_BR := 2

/-- Battle of the Sexes has a pure Nash equilibrium -/
theorem battleOfSexes_has_pure_nash : battleOfSexes.hasPureNash := by
  unfold battleOfSexes TwoByTwoGame.hasPureNash
  left
  exact ⟨by decide, by decide⟩

/-- A common action type for both players in a 2×2 game (2 pure strategies each) -/
inductive TwoAction | A | B
  deriving DecidableEq

instance : Fintype TwoAction where
  elems := {TwoAction.A, TwoAction.B}
  complete := fun x => by cases x <;> simp

/-- Convert a TwoByTwoGame into a FiniteGame using a common action type.
    Player 0: A=Top, B=Bottom. Player 1: A=Left, B=Right. -/
noncomputable def TwoByTwoGame.toFiniteGame (G : TwoByTwoGame)
    (Δ : ∀ (_ : Fin 2), SyntheticSimplex TwoAction) : FiniteGame where
  numPlayers := 2
  Action := fun _ => TwoAction
  actionFintype := fun _ => inferInstance
  actionNonempty := fun _ => ⟨TwoAction.A⟩
  R := G.R
  instLinearOrder := G.instR
  simplex := Δ
  payoff := fun profile player =>
    match profile ⟨0, by omega⟩, profile ⟨1, by omega⟩, player with
    | TwoAction.A, TwoAction.A, ⟨0, _⟩ => G.u1_TL
    | TwoAction.A, TwoAction.B, ⟨0, _⟩ => G.u1_TR
    | TwoAction.B, TwoAction.A, ⟨0, _⟩ => G.u1_BL
    | TwoAction.B, TwoAction.B, ⟨0, _⟩ => G.u1_BR
    | TwoAction.A, TwoAction.A, ⟨1, _⟩ => G.u2_TL
    | TwoAction.A, TwoAction.B, ⟨1, _⟩ => G.u2_TR
    | TwoAction.B, TwoAction.A, ⟨1, _⟩ => G.u2_BL
    | TwoAction.B, TwoAction.B, ⟨1, _⟩ => G.u2_BR
    | _, _, ⟨n + 2, h⟩ => absurd h (by omega)

end Examples
