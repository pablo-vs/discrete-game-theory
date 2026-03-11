import DiscreteGameTheory.Base
import DiscreteGameTheory.Refinement
import DiscreteGameTheory.BilinearExamples

/-!
# Compact Games — Towers as Games

A compact game is a `GeneralSignTower` with a finite base. This module develops
the theory of compact games: OD propagation through towers, shift (re-rooting),
and examples showing how infinite-action games reduce to compact towers.

## Key ideas

**CompactGame = GeneralSignTower.** The tower IS the game. Individual levels are
finite approximations. The "infinite limit" is implicit — we never construct it,
but the tower captures all its strategic content.

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
open BilinearExamples

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
-- Section 2: CompactGame definition
-- ================================================================

variable [Fintype I]

/-- A compact game is a GeneralSignTower — a tower of sign games with finite
    actions at every level, connected by embeddings satisfying coherence and
    convexity axioms. The tower simultaneously represents:
    - The base game (level 0)
    - All its meta-iterates (each level is meta of the previous)
    - The "infinite limit" (implicit — never constructed) -/
abbrev CompactGame (I : Type*) [DecidableEq I] [Fintype I] := GeneralSignTower I

-- ================================================================
-- Section 3: iterEmbedClose — deterministic OD propagation
-- ================================================================

namespace Refinement.GeneralSignTower

variable (T : GeneralSignTower I)

/-- Lift a profile from level k to level k+n by iterating embed-then-convex-close.
    This is the deterministic propagation of an OD core through the tower. -/
def iterEmbedClose (k : ℕ) (σ : Profile I (T.V k)) (n : ℕ) : Profile I (T.V (k + n)) :=
  Nat.rec (motive := fun n => Profile I (T.V (k + n))) σ
    (fun n τ => T.convexClosureProfile (k + n + 1)
      (embedProfile (T.embed (k + n)) (T.embed_inj (k + n)) τ)) n

@[simp] theorem iterEmbedClose_zero (k : ℕ) (σ : Profile I (T.V k)) :
    iterEmbedClose T k σ 0 = σ := rfl

theorem iterEmbedClose_succ (k n : ℕ) (σ : Profile I (T.V k)) :
    iterEmbedClose T k σ (n + 1) =
      T.convexClosureProfile (k + n + 1)
        (embedProfile (T.embed (k + n)) (T.embed_inj (k + n))
          (iterEmbedClose T k σ n)) := rfl

/-- OD propagates through iterEmbedClose: if σ has OD at level k, then
    iterEmbedClose k σ n has OD at level k+n. -/
theorem outsideDom_iterEmbedClose (k n : ℕ)
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
theorem nash_inside_iterEmbedClose (k n : ℕ)
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
def shift (k : ℕ) : GeneralSignTower I where
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

theorem shift_game (k j : ℕ) : (T.shift k).game j = T.game (k + j) := rfl

/-- The base of a shifted tower is the original tower's game at that level. -/
theorem shift_game_zero (k : ℕ) : (T.shift k).game 0 = T.game k := by
  simp [shift]

/-- Nash+OD+convex at every level of the shifted tower. -/
theorem shift_nash_refining_sequence (k j : ℕ) :
    ∃ σ : Profile I (T.V (k + j)),
      (T.game (k + j)).IsNash σ ∧
      (∀ i, (T.game (k + j)).OutsideDom i σ) ∧
      (T.shift k).HasConvexFaces j σ :=
  (T.shift k).nash_refining_sequence j

end Refinement.GeneralSignTower

-- ================================================================
-- Section 5: Example — Matching Pennies as a compact game
-- ================================================================

section MPExamples

open Refinement.GeneralSignTower

/-- The Matching Pennies tower is a compact game. -/
def compactMP : CompactGame (Fin 2) := genMpTower.toGeneralSignTower

/-- Meta-MP at level k: the shifted MP tower starting from k-bit MP.
    The base game of metaMP k has 2^k + 1 actions per player. -/
def metaMP (k : ℕ) : CompactGame (Fin 2) := compactMP.shift k

/-- Nash exists for meta-MP at every internal level. -/
theorem metaMP_nash (k j : ℕ) :
    ∃ σ, ((metaMP k).game j).IsNash σ :=
  ((metaMP k).nash_refining_sequence j).imp fun _ h => h.1

/-- Starting from the base MP (2 actions), OD propagates to all levels.
    The full profile (both players play all actions) is OD at level 0. -/
theorem compactMP_od_base :
    ∀ i, (compactMP.game 0).OutsideDom i (fun _ => Face.full) :=
  fun i => OutsideDom.maximal (compactMP.game 0) i

/-- Nash equilibria at any level of the MP tower live inside the iterated
    embed-close of the base full profile. -/
theorem compactMP_nash_inside (n : ℕ) :
    ∃ τ, (compactMP.game (0 + n)).IsNash τ ∧
      (∀ i, Face.IsSubface (τ i)
        (iterEmbedClose compactMP 0 (fun _ => Face.full) n i)) :=
  (nash_inside_iterEmbedClose compactMP 0 n compactMP_od_base).imp
    fun _ ⟨hN, hsub, _⟩ => ⟨hN, hsub⟩

end MPExamples

-- ================================================================
-- Section 6: Example — lowerIsBetter (infinite game with dominated tail)
-- ================================================================

section LowerIsBetter

/-- A 2-player game on ℕ actions where lower indices are better.
    sign i p a b = cmpSign a b: pos when a < b (a is preferred to b). -/
def lowerIsBetter : SignGame (Fin 2) (fun _ : Fin 2 => ℕ) where
  sign _i _p a b := cmpSign a b
  sign_refl := fun _ _ a => cmpSign_self a
  sign_antisym := fun _ _ a b => by rw [cmpSign_flip]
  sign_trans := fun _ _ _ _ _ hab hbc => cmpSign_trans hab hbc
  sign_irrel := fun _ _ _ _ _ _ => rfl

/-- The core {0} dominates everything in lowerIsBetter. -/
theorem lowerIsBetter_OD (i : Fin 2) :
    lowerIsBetter.OutsideDom i (fun _ => Face.vertex 0) := by
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

end LowerIsBetter

-- ================================================================
-- Section 7: Example — MP on ℕ with dominated complement
-- ================================================================

section InfiniteExample

/-- Matching Pennies on ℕ: actions 0 and 1 play the MP game, all actions > 1
    are "junk" that is strictly worse for both players.

    Payoff for player i at profile p:
    - If my action > 1: heavily penalized (the further out, the worse)
    - If opponent's action > 1: indifferent (payoff 0)
    - If both in {0,1}: standard MP payoffs
      - Player 0 wants to match: payoff 1 if p 0 = p 1, else 0
      - Player 1 wants to differ: payoff 1 if p 0 ≠ p 1, else 0 -/
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

/-- The core {0, 1} satisfies OD for mpNat: every action v > 1 is dominated
    by every action w ∈ {0, 1}, because v gets payoff ≤ -102 while w gets
    payoff ≥ 0. -/
theorem mpNat_od (i : Fin 2) :
    mpNat.OutsideDom i (fun _ => ⟨{0, 1}, by simp⟩) := by
  intro v hv w hw
  simp only [Finset.mem_singleton, Finset.mem_insert] at hv hw
  push_neg at hv
  -- hv : v ≠ 0 ∧ v ≠ 1, hw : w = 0 ∨ w = 1
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

/-- Nash existence for mpNat via core restriction. This is a genuinely
    infinite-action game (every natural number is a valid action), but the
    core {0, 1} with OD reduces it to finite MP. -/
theorem mpNat_nash : ∃ σ, mpNat.IsNash σ :=
  mpNat.nash_of_core (fun _ => ⟨{0, 1}, by simp⟩) mpNat_od

end InfiniteExample

-- ================================================================
-- Section 8: Documentation — the full picture
-- ================================================================

/-!
## The compact game equivalence class

A compact game (tower T) implicitly defines an equivalence class of games
that all share the same Nash structure:

1. **The base game** T.game 0 — a finite SignGame
2. **Meta-games** (T.shift k).game 0 = T.game k — the level-k game as a base
3. **OD-expansions** — games with extra dominated actions (like mpNat)
4. **The infinite limit** — never constructed, but implicit in the tower

These are all "the same game" in the sense that their Nash equilibria correspond:
- Nash at level k refines Nash at level j < k (by `nash_at_next_level_refines`)
- OD-expanded games have the same Nash as the core (by `nash_of_core`)
- Meta-games are just the tower viewed from a different starting point

## The two-axis picture for Matching Pennies

Consider the MP tower `compactMP`:

```
Level 0:  {0, 1}           — 2 actions (H, T)
Level 1:  {0, 1, 2}        — 3 actions (grid on [0,1])
Level 2:  {0, 1, 2, 3, 4}  — 5 actions
Level k:  Fin (2^k + 1)    — 2^k + 1 actions
```

The two-axis interpretation:
- **Shift by 0** (compactMP): base = 2-action MP, tower refines mixing ratios
- **Shift by 1** (metaMP 1): base = 3-action game, "actions" are mixing ratios
  {0, 1/2, 1} of the original MP
- **Shift by k** (metaMP k): base = (2^k+1)-action game, each "action" was a
  face at level k-1

Entry (n, k) in the grid is `compactMP.game (n + k)`. The grid collapses to a
single sequence — the meta-structure is built into the tower.

At the "infinite limit" (tower continuing forever), we get:
- k → ∞: continuous MP on [0,1] with dyadic-rational mixing
- n → ∞: meta-MP where strategies are distributions over [0,1]
- Both limits are the same tower — there is no distinction between "refining"
  and "going meta"

## Infinite-action games as compact games

The mpNat example demonstrates the pattern:
1. Start with a genuinely infinite-action SignGame (mpNat on ℕ)
2. Identify an OD core ({0, 1}) — finite, capturing all strategic content
3. The core IS the base of a tower (level-0 MP)
4. iterEmbedClose propagates the core through all levels
5. Nash equilibria at every level live inside the propagated core

Any game that OD-restricts to a finite core is compact in this sense. The
infinite actions outside the core are strategic noise — dominated and irrelevant.
The tower structure of the core handles all the "interesting" strategic content.
-/
