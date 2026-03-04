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

variable {I : Type*} [DecidableEq I] {V : I → Type*} [∀ i, DecidableEq (V i)]
variable (G : SignGame I V)

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
