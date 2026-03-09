# Synthetic Game Theory in Lean 4

A machine-checked formalization of finite game theory without real numbers, probability, or fixed-point theorems. Nash equilibria are computed by a terminating descent algorithm on finite face lattices.

## Quick Start

```bash
lake build
```

Requires Lean 4 and Mathlib. The `lakefile` handles dependency resolution.

## Theory Overview

**SignGame.** A game is specified by a *sign function* `s_i(p, a, b) in {+, -, 0}` — an ordinal comparison replacing cardinal payoffs. The sign records whether player `i` prefers action `a` over `b` when opponents play profile `p`, satisfying reflexivity, antisymmetry, transitivity, and irrelevance to `i`'s own "current" action.

**Face.** A mixed strategy is a *face* — a nonempty finite subset of actions — replacing probability distributions. The face `{a, b}` represents "some distribution over `a` and `b`" without specifying which one. Mixing is set union: commutative, associative, idempotent.

**DevFaceLE.** Face `A` dominates face `B` for player `i` when every action in `A` beats every action in `B` against every consistent opponent action. This conservative comparison produces a *partial* order — incomparability breaks deviation cycles and enables mixed Nash equilibria.

**Nash existence via OD descent.** The algorithm maintains the *OutsideDominated* invariant (every excluded action is dominated by every included action) while shrinking faces:

```
  Start: sigma = (full, full, ..., full)    [OD holds vacuously]
    |
    v
  Is sigma Nash? --yes--> Done: return sigma
    | no
    v
  Find player i with strict deviation A
    |
    v
  Restrict: find A' c sigma_i, A' != sigma_i, A' still strict dev
    |
    v
  Update: sigma_i <- A'    [profileSize decreases, OD preserved]
    |
    '-------> loop back to "Is sigma Nash?"
```

Profile size (sum of face cardinalities) is a natural number that strictly decreases each step, so the algorithm terminates.

## File Guide

| File | Purpose | Key exports |
|------|---------|-------------|
| `Base.lean` | Core theory | `Sign`, `Face`, `SignGame`, `DevFaceLE`, `IsNash`, `nash_exists` |
| `Examples.lean` | Classic 2x2 and 3-player games | `genPD`, `genMP`, `genSH`, `genBoS`, `coordGame3` |
| `Compact.lean` | Abstract `Game` structure, core restriction | `MixtureAlgebra`, `Game`, `toGame`, `nash_of_core` |
| `Refinement.lean` | Tower of refining sign games | `GeneralSignTower`, `nash_refining_sequence` |
| `Invariance.lean` | Ordinal vs cardinal invariance | `ofPayoffs_strictMono_invariant`, `counterexample_level2` |
| `SelfSimilarity.lean` | Tower decomposition | `iterEmbed`, `restrictGame`, `multiLevelGame` |
| `BilinearExamples.lean` | Concrete 2-player towers | `GenBilinearTower`, PD/MP/SymCoord/BoS towers |

## Base.lean — Core Theory

The foundation: sign games, faces, deviation ordering, Nash equilibrium, and the existence proof.

```
Sign                    -- inductive: pos | neg | zero
cmpSign (a b : Nat)     -- comparison sign of two naturals
Face V                  -- { S : Finset V // S.Nonempty }
  vertex, full, mix     -- singleton, universe, union
PureProfile I V         -- forall i, V i
Profile I V             -- forall i, Face (V i)
ConsistentAt sigma i p  -- forall j != i, p j in (sigma j)
SignGame I V            -- sign function + refl/antisym/trans/irrel axioms
DevFaceLE i sigma A B   -- A weakly dominates B for player i in context sigma
  .trans / .antitone / .mono_left / .mono_right
StrictDev i sigma A     -- DevFaceLE A (sigma i) and not DevFaceLE (sigma i) A
IsNash sigma            -- forall i A, not StrictDev i sigma A
OutsideDominated i sigma -- every excluded action dominated by every included
  .maximal              -- full profile is vacuously OD
  .preserved            -- OD preserved when player i restricts
  .preserved_other      -- OD preserved for other players j != i
exists_restrictingStrictDev -- strict dev can be restricted to subface of sigma_i
profileSize_decreases   -- restriction strictly decreases profile size
nash_exists_of_OD       -- Nash from any OD-satisfying profile (main algorithm)
nash_exists             -- Nash for any finite game
ofPayoffs               -- construct SignGame from payoff functions
IsPureNash              -- pure strategy Nash equilibrium
```

**OD descent intuition:**
- *Why OD?* An invariant ensuring removed actions were genuinely worse, so restriction doesn't lose the Nash guarantee.
- *Why restrict to sigma_i?* The backward witness (the action that makes sigma_i fail to dominate A) lives in sigma_i (`outsideDom_witness_mem`).
- *Why does size decrease?* The restricted face A' is a strict subface of sigma_i, so the sum of cardinalities drops.
- *Why is OD preserved?* For player i: A' dominates sigma_i, so it dominates the already-dominated outside actions. For j != i: antitonicity — shrinking i's face only makes domination easier for others.

## Examples.lean — Classic Games

```
  Prisoner's Dilemma     Matching Pennies      Stag Hunt          Battle of Sexes
    C    D                 H    T                S    H              O    F
C  3,3  0,5           H  1,0  0,1          S  4,4  0,3          O  3,2  0,0
D  5,0  1,1           T  0,1  1,0          H  3,0  3,3          F  0,0  2,3
```

- `genPD`: unique pure Nash at (D,D) — `genPD_unique_pureNash`
- `genMP`: no pure Nash — `genMP_no_pureNash`; full mix is Nash — `genMP_mixed_nash`
- `genSH`: two pure Nash at (S,S) and (H,H)
- `genBoS`: two pure Nash at (O,O) and (F,F)
- `genMP_partial_order`: neither {H} nor {T} dominates the other when opponent mixes
- `coordGame3`: 3-player coordination, Nash at all-true and all-false
- `symGame2x2`, `game2x2_rank`: readable game constructors from ranking functions
- `pd_rank`, `pd_rank_alt`, `pd_same_game`: ordinal invariance example

## Compact.lean — Abstract Game & Core Restriction

```
MixtureAlgebra S        -- class: mix with comm/idem/assoc
Game I                  -- structure: strategy spaces + contextual preference
  .StrictPref / .IsNash
SignGame.toGame         -- bridge: Nash definitions agree by rfl
SignGame.nash_of_core   -- Nash exists if a finite core satisfies OD
lowerIsBetter           -- example: infinite game on Nat, lower index preferred
```

## Refinement.lean — Tower Construction

A sequence of games on doubling grids with coherent signs and convex closures.

```
Level 0:  0---1                                   gridSize = 2
Level 1:  0---1---2                               gridSize = 3
Level 2:  0---1---2---3---4                       gridSize = 5
Level 3:  0---1---2---3---4---5---6---7---8       gridSize = 9
```

Grid embed maps j -> 2j (old points land on even indices at next level).

```
Betweenness V           -- class: between c a b
IsConvex / convClosure  -- convex sets and smallest convex superset
gridSize k = 2^k + 1   -- grid points at level k
gridEmbed k : Fin (gridSize k) -> Fin (gridSize (k+1))

GeneralSignTower I      -- structure with fields:
  V, game, embed        -- action types, sign games, embeddings per level
  coherent              -- signs at embedded points match coarse signs
  playerConvex_left/right, opponentConvex  -- convexity axioms
  fine_between_embedded_at  -- spanning axiom

DevFaceLE_convCloseProfile  -- DevFaceLE preserved under convex closure
OD_embed_convClosure    -- OD transfers from coarse to fine level (key result)
nash_refining_sequence  -- Nash + OD + convex-closed at every level k
nash_at_next_level_refines -- fine Nash refines coarse Nash
```

## Invariance.lean — Ordinal vs Cardinal

```
SignGame.ext'                      -- @[ext]: games equal iff sign functions equal
ofPayoffs_strictMono_invariant     -- StrictMono payoff transforms preserve sign game
affine_preserves_oppSign           -- positive scaling preserves tower signs
counterexample_level2              -- g(x) = x^3 changes sign at level 2, j=1
signs_agree_level0                 -- same g(x) preserves level-0 signs
```

Level 0: any strictly monotone transform preserves the game (ordinal invariance).
Level k >= 1: only affine transforms preserve tower signs.
Limit k -> infinity: recovers the von Neumann-Morgenstern uniqueness class.

## SelfSimilarity.lean — Tower Structure

```
iterEmbed k n i         -- iterate embedding n times from level k
coherent_iterEmbed      -- signs at level k+n match level k on embedded args
restrictGame G f        -- restrict sign game via per-player injections
multiLevelGame T kappa  -- per-player independent levels
leftChild / rightChild  -- grid splits into two halves at midpoint
boundary_shared         -- left endpoint of right child = right endpoint of left child
```

## BilinearExamples.lean — Concrete Towers

```
bilinearSignGame n oppSign    -- 2-player game: sign = mul(cmpSign b a, oppSign(opp))
GenBilinearTower              -- input data: per-player oppSign with axioms
  .toGeneralSignTower         -- construct GeneralSignTower (Fin 2)
  .nash_sequence              -- Nash + OD + convex-closed at every level
  .nash_refines               -- fine Nash refines coarse Nash

genPdTower                    -- all neg: defection always dominates
genMpTower                    -- flip at boundary: unique mixed equilibrium
genSymCoordTower              -- cmpSign threshold: equilibrium at p=1/2
genBosTower                   -- asymmetric thresholds (p=3/4 and p=1/4)
```

## Dependencies

Mathlib imports:
- `Mathlib.Data.Fintype.{Basic, Card, Powerset}`
- `Mathlib.Data.Finset.{Basic, Card}`
- `Mathlib.Logic.Function.Basic`
- `Mathlib.Algebra.Order.BigOperators.Group.Finset`
- `Mathlib.Tactic.FinCases`
- `Mathlib.Order.Monotone.Basic`
