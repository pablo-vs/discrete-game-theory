import SyntheticGameTheory.Base

/-!
# Compact Games — Restriction to a Core

A game (possibly with infinitely many actions) can be restricted to a finite
"core" of actions, provided every action outside the core is dominated by
every action inside. This is exactly the `OutsideDominated` condition.

The main theorem `nash_of_core` says: if you can identify a core where OD
holds, Nash equilibria exist for the full game. The proof is immediate from
`nash_exists_of_OD` — the descent algorithm starts from the core profile
and stays within it, finding a Nash that's valid for the full game.
-/

namespace Base

-- ================================================================
-- Section 0: MixtureAlgebra & abstract Game
-- ================================================================

/-- An idempotent commutative monoid — the algebraic structure of mixing strategies.
    mix A B represents "some distribution supported on A ∪ B" without specifying which. -/
class MixtureAlgebra (S : Type*) where
  mix : S → S → S
  mix_comm : ∀ a b, mix a b = mix b a
  mix_idem : ∀ a, mix a a = a
  mix_assoc : ∀ a b c, mix (mix a b) c = mix a (mix b c)

instance {V : Type*} [DecidableEq V] : MixtureAlgebra (Face V) where
  mix := Face.mix
  mix_comm := Face.mix_comm
  mix_idem := Face.mix_idem
  mix_assoc := Face.mix_assoc

/-- Abstract game: the most general notion of strategic interaction.
    Each player has a strategy space with mixture, and a contextual preference
    relation: `pref i σ s t` means "player i, when opponents play σ,
    weakly prefers strategy s over t."

    The preference is a transitive relation but not necessarily reflexive
    (self-preference can fail for mixed strategies) or total (incomparable
    strategies arise naturally from universal quantification over opponents). -/
structure Game (I : Type*) where
  S : I → Type*
  mixture : ∀ i, MixtureAlgebra (S i)
  pref : (i : I) → (∀ j, S j) → S i → S i → Prop
  pref_trans : ∀ i σ (s t u : S i), pref i σ s t → pref i σ t u → pref i σ s u

namespace Game

variable {I : Type*} (G : Game I)

/-- Player i strictly prefers s over t in context σ: s ≥ t but not t ≥ s. -/
def StrictPref (i : I) (σ : ∀ j, G.S j) (s t : G.S i) : Prop :=
  G.pref i σ s t ∧ ¬G.pref i σ t s

/-- A profile is Nash if no player has a strategy strictly preferred to their current one. -/
def IsNash (σ : ∀ j, G.S j) : Prop :=
  ∀ i s, ¬G.StrictPref i σ s (σ i)

end Game

-- ================================================================
-- Section 0b: SignGame.toGame bridge
-- ================================================================

variable {I : Type*} [DecidableEq I] {V : I → Type*} [∀ i, DecidableEq (V i)]
variable (G : SignGame I V)

namespace SignGame

/-- Construct an abstract Game from a SignGame.
    Strategies are faces, mixture is union, preference is DevFaceLE. -/
def toGame : Game I where
  S := fun i => Face (V i)
  mixture := fun _ => inferInstance
  pref := fun i σ A B => G.DevFaceLE i σ A B
  pref_trans := fun _ _ _ _ _ hAB hBC => DevFaceLE.trans G hAB hBC

omit [DecidableEq I] in
/-- StrictPref in the abstract Game agrees with StrictDev in the SignGame. -/
theorem toGame_strictPref_iff {i : I} {σ : Profile I V} {A : Face (V i)} :
    G.toGame.StrictPref i σ A (σ i) ↔ G.StrictDev i σ A := by
  rfl

omit [DecidableEq I] in
/-- IsNash in the abstract Game agrees with IsNash in the SignGame. -/
theorem toGame_isNash_iff {σ : Profile I V} :
    G.toGame.IsNash σ ↔ G.IsNash σ := by
  rfl

/-- Nash existence lifts to the abstract Game. -/
theorem toGame_nash_exists [Fintype I] [∀ i, Fintype (V i)] [∀ i, Nonempty (V i)] :
    ∃ σ, G.toGame.IsNash σ :=
  G.nash_exists

end SignGame

-- ================================================================
-- Section 1: Restriction to a core
-- ================================================================

/-- Nash existence for games with a dominated complement.
    Given a finite core (a face per player) such that OutsideDominated holds
    at the core profile, Nash equilibria exist for the full game.

    This handles infinite action sets: the core is finite (it's a Face,
    i.e., a nonempty Finset), and actions outside are dominated. -/
theorem SignGame.nash_of_core [Fintype I]
    (core : ∀ i, Face (V i))
    (h_od : ∀ i, G.OutsideDominated i core) :
    ∃ σ, G.IsNash σ :=
  G.nash_exists_of_OD core h_od

-- ================================================================
-- Section 2: Example — infinite game with dominated tail
-- ================================================================

/-- A 2-player game on ℕ actions where lower indices are better.
    sign i p a b = cmpSign a b: pos when a < b (a is preferred to b).
    Note: cmpSign a b = pos means a < b as naturals. Here, lower index = better action,
    so a < b means a is the better action. -/
def lowerIsBetter : SignGame (Fin 2) (fun _ : Fin 2 => ℕ) where
  sign _i _p a b := cmpSign a b
  sign_refl := fun _ _ a => cmpSign_self a
  sign_antisym := fun _ _ a b => by rw [cmpSign_flip]
  sign_trans := fun _ _ _ _ _ hab hbc => cmpSign_trans hab hbc
  sign_irrel := fun _ _ _ _ _ _ => rfl

/-- The core {0} dominates everything in lowerIsBetter:
    OutsideDominated holds at the core profile. -/
theorem lowerIsBetter_OD (i : Fin 2) :
    lowerIsBetter.OutsideDominated i (fun _ => Face.vertex 0) := by
  intro v hv w hw
  simp [Face.vertex] at hv hw; subst hw
  intro a ha p _hp b hb
  simp [Face.vertex] at ha hb; subst ha; subst hb
  simp [lowerIsBetter, cmpSign_nonneg_iff]

/-- Nash existence for lowerIsBetter via core restriction. -/
theorem lowerIsBetter_nash : ∃ σ, lowerIsBetter.IsNash σ :=
  lowerIsBetter.nash_of_core
    (fun _ => Face.vertex 0)
    (fun i => lowerIsBetter_OD i)

end Base
