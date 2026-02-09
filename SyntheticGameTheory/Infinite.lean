import SyntheticGameTheory
import SyntheticGameTheory.DeviationGraph
import Mathlib.Data.Fintype.Sets

/-!
# Infinite Action Spaces and Finite Restrictions

With `Game` generalized to not require `Fintype`, we can define games over
infinite action spaces (e.g., ℕ). Nash equilibria may not exist in such games
— `nash_exists` requires `Fintype` for the well-founded descent.

The key operation is `restrictGame`: given finite subsets `S i` of each player's
action space, restrict to the subtype game. Since each `{ v // v ∈ S i }` is
`Fintype`, `nash_exists` applies, giving Nash existence for every finite
restriction. This is the *compactification* principle: finiteness restores
equilibrium existence.
-/

namespace SyntheticGameTheory

open Game

variable {N : Type*} [DecidableEq N] {V : N → Type*} [∀ i, DecidableEq (V i)]

-- ================================================================
-- Section 1: Restriction to Finite Action Subsets
-- ================================================================

/-- Restrict a game to finite subsets of each player's action space.
    The restricted game has the same preferences, evaluated on the
    underlying pure profiles. -/
noncomputable def Game.restrictGame (G : Game N V) (S : ∀ i, Finset (V i)) :
    Game N (fun i => { v // v ∈ S i }) where
  pref i p q := G.pref i (fun j => (p j).val) (fun j => (q j).val)
  pref_preorder i := {
    refl := fun _ => (G.pref_preorder i).refl _
    trans := fun {_ _ _} h1 h2 => (G.pref_preorder i).toIsTrans.trans _ _ _ h1 h2
  }
  pref_total i := ⟨fun _ _ => (G.pref_total i).total _ _⟩
  pref_decidable i _ _ := G.pref_decidable i _ _

/-- **Compactification principle**: Nash equilibrium exists in every finite
    restriction of a game. This holds even when the original game has infinite
    action spaces and no Nash equilibrium. -/
theorem Game.restrictGame_nash_exists [Fintype N] (G : Game N V)
    (S : ∀ i, Finset (V i)) (hS : ∀ i, (S i).Nonempty) :
    ∃ σ, (G.restrictGame S).IsNash σ := by
  haveI : ∀ i, Nonempty { v // v ∈ S i } := fun i =>
    let ⟨v, hv⟩ := hS i; ⟨⟨v, hv⟩⟩
  exact (G.restrictGame S).nash_exists

-- ================================================================
-- Section 2: Example — Selfish Naturals
-- ================================================================

/-- **Selfish naturals**: each of two players picks a natural number.
    Each player prefers their own number to be as high as possible,
    ignoring the other player's choice. -/
noncomputable def selfishNatGame : Game (Fin 2) (fun _ => ℕ) where
  pref i p q := p i ≥ q i
  pref_preorder _ := {
    refl := fun _ => le_refl _
    trans := fun {_ _ _} h1 h2 => le_trans h2 h1
  }
  pref_total _ := ⟨fun _ _ => le_total _ _⟩
  pref_decidable _ _ _ := inferInstance

/-- The selfish naturals game has no pure Nash equilibrium:
    for any profile, each player can deviate to a higher number. -/
theorem selfishNatGame_no_pureNash (p : PureProfile (Fin 2) (fun _ => ℕ)) :
    ¬selfishNatGame.IsPureNash p := by
  intro h
  have := h 0 (p 0 + 1)
  simp only [selfishNatGame, Function.update_self] at this
  omega

/-- Restricting to `{0, ..., B}` restores Nash existence. -/
theorem selfishNatGame_restricted_nash (B : ℕ) :
    ∃ σ, (selfishNatGame.restrictGame (fun _ => Finset.range (B + 1))).IsNash σ :=
  selfishNatGame.restrictGame_nash_exists _ (fun _ => ⟨0, Finset.mem_range.mpr (by omega)⟩)

end SyntheticGameTheory
