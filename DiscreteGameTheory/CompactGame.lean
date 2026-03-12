import DiscreteGameTheory.Base
import DiscreteGameTheory.Refinement

/-!
# Compact Games — Towers as Games

A compact game is a `SignTower` with a finite base. This module develops
the theory of sign towers as games: OD propagation through towers, shift
(re-rooting), and examples showing how infinite-action games reduce to towers.

## Key ideas

**The tower IS the game.** Individual levels are finite approximations.
The "infinite limit" is implicit — we never construct it, but the tower
captures all its strategic content.

**OD profiles propagate.** An OD profile at level k lifts deterministically to
all higher levels via iterated embed-then-convex-close (`iterEmbedClose`). Nash
equilibria at higher levels live inside the lifted core.

**Shift as meta-game.** `T.shift k` re-roots the tower at level k. Level j of
the shifted tower is level k+j of the original. This captures the "meta-game"
interpretation: the level-k game, viewed as a compact game, is the meta-game of
the level-0 game refined k times. Each level of the tower is simultaneously a
meta-game of all lower levels.

**The two-axis picture.** For any tower (e.g., Matching Pennies):
- Horizontal axis (tower level k): refinement, adding midpoints
- Vertical axis (shift by n): meta-levels, where level-n "actions" were "faces"
  at level n-1
- Entry (n, k) = T.game (n + k) — the grid collapses to one sequence
- "Continuous meta-MP" is just the tower viewed from a high starting point

**Infinite-action games.** A game with infinitely many pure actions (e.g., MP on
ℕ where most actions are junk) can have an OD core that sits at the base of a
tower. The OD core is a finite restriction; the tower refines it. This is how
genuinely infinite games become compact: OD-restrict to a finite core, then the
tower handles all further structure.
-/

open Base
open Base.SignGame (Dominates OutsideDom)
open Refinement

-- ================================================================
-- Section 1: Core restriction (from Compact.lean)
-- ================================================================

variable {I : Type*} [DecidableEq I] {V : I → Type*} [∀ i, DecidableEq (V i)]

namespace Base.SignGame

/-- Nash existence for games with a dominated complement.
    Given a finite core (a face per player) such that OutsideDom holds
    at the core profile, Nash equilibria exist for the full game.

    This handles infinite action sets: the core is finite (it's a Face,
    i.e., a nonempty Finset), and actions outside are dominated. -/
theorem nash_of_core [Fintype I]
    (G : SignGame I V) (core : ∀ i, Face (V i))
    (h_od : ∀ i, G.OutsideDom i core) :
    ∃ σ, G.IsNash σ :=
  G.nash_exists_of_outsideDom core h_od

end Base.SignGame

-- ================================================================
-- Section 2: iterEmbedClose — deterministic OD propagation
-- ================================================================

variable [Fintype I]

namespace Refinement.SignTower

variable (T : SignTower I)

/-- Lift a profile from level k to level k+n by iterating embed-then-convex-close.
    This is the deterministic propagation of an OD core through the tower. -/
def iterEmbedClose (k : ℕ) (σ : Profile I (T.V k)) (n : ℕ) : Profile I (T.V (k + n)) :=
  Nat.rec (motive := fun n => Profile I (T.V (k + n))) σ
    (fun n τ => T.convexClosureProfile (k + n + 1)
      (embedProfile (T.embed (k + n)) (T.embed_inj (k + n)) τ)) n

@[simp] theorem iterEmbedClose_zero (k : ℕ) (σ : Profile I (T.V k)) :
    iterEmbedClose T k σ 0 = σ := rfl

lemma iterEmbedClose_succ (k n : ℕ) (σ : Profile I (T.V k)) :
    iterEmbedClose T k σ (n + 1) =
      T.convexClosureProfile (k + n + 1)
        (embedProfile (T.embed (k + n)) (T.embed_inj (k + n))
          (iterEmbedClose T k σ n)) := rfl

/-- OD propagates through iterEmbedClose: if σ has OD at level k, then
    iterEmbedClose k σ n has OD at level k+n. -/
lemma outsideDom_iterEmbedClose (k n : ℕ)
    {σ : Profile I (T.V k)}
    (h_od : ∀ i, (T.game k).OutsideDom i σ) :
    ∀ i, (T.game (k + n)).OutsideDom i (iterEmbedClose T k σ n) := by
  induction n with
  | zero => exact h_od
  | succ n ih =>
    rw [iterEmbedClose_succ]
    intro i
    exact T.outsideDom_embed_convClosure (k + n) ih i

/-- Nash equilibria at higher levels live inside the lifted core. -/
lemma nash_inside_iterEmbedClose (k n : ℕ)
    {σ : Profile I (T.V k)}
    (h_od : ∀ i, (T.game k).OutsideDom i σ) :
    ∃ τ, (T.game (k + n)).IsNash τ ∧
      (∀ i, Face.IsSubface (τ i) (iterEmbedClose T k σ n i)) ∧
      (∀ i, (T.game (k + n)).OutsideDom i τ) := by
  obtain ⟨τ, hN, hsub, hod⟩ :=
    (T.game (k + n)).nash_exists_sub_of_outsideDom
      (iterEmbedClose T k σ n) (outsideDom_iterEmbedClose T k n h_od)
  exact ⟨τ, hN, hsub, hod⟩

-- ================================================================
-- Section 4: Shift — re-rooting a tower
-- ================================================================

/-- Re-root a tower to start at level k. Level j of the shifted tower is
    level k+j of the original.

    The meta-game interpretation: T.shift k is the compact game whose base
    is the level-k game. Each level j of the shifted tower refines the
    level-k game j more times. In particular, (T.shift k).game 0 = T.game k.

    This captures the idea that "the level-k game, viewed as a compact game"
    is a well-defined object — it's just the original tower shifted. -/
def shift (k : ℕ) : SignTower I where
  V j := T.V (k + j)
  instDecEq j i := T.instDecEq (k + j) i
  instFintype j i := T.instFintype (k + j) i
  instInhabited j i := T.instInhabited (k + j) i
  betw j i := T.betw (k + j) i
  game j := T.game (k + j)
  embed j := T.embed (k + j)
  embed_inj j := T.embed_inj (k + j)
  embed_between j := T.embed_between (k + j)
  coherent j := T.coherent (k + j)
  playerConvex_left j := T.playerConvex_left (k + j)
  playerConvex_right j := T.playerConvex_right (k + j)
  opponentConvex j := T.opponentConvex (k + j)
  fine_between_embedded_at j := T.fine_between_embedded_at (k + j)

lemma shift_game (k j : ℕ) : (T.shift k).game j = T.game (k + j) := rfl

/-- The base of a shifted tower is the original tower's game at that level. -/
lemma shift_game_zero (k : ℕ) : (T.shift k).game 0 = T.game k := by
  simp [shift]

/-- Nash+OD+convex at every level of the shifted tower. -/
lemma shift_nash_refining_sequence (k j : ℕ) :
    ∃ σ : Profile I (T.V (k + j)),
      (T.game (k + j)).IsNash σ ∧
      (∀ i, (T.game (k + j)).OutsideDom i σ) ∧
      (T.shift k).HasConvexFaces j σ :=
  (T.shift k).nash_refining_sequence j

end Refinement.SignTower
