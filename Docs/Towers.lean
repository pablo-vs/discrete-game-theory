import VersoManual
import DiscreteGameTheory.Refinement
import DiscreteGameTheory.Invariance
import DiscreteGameTheoryExamples.GridTower

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option pp.rawOnError true
set_option verso.exampleProject "."
set_option verso.exampleModule "DiscreteGameTheoryExamples.GridTower"

open Base Refinement

#doc (Manual) "Refinement Towers" =>

The level-0 theory keeps only ordinal information — which action is better, not by how much.
Can we add back cardinal information in a controlled way?

Yes. The idea is to refine the discrete simplex into finer grids, like zooming in on a number
line. At level 0, each player's strategy space is just their action set. At level k, we have
$`2^k + 1` grid points, where grid point j represents the probability $`j / 2^k`.

# Grid Structure

The grid at level k has $`2^k + 1` points. Grid points embed from one level to the next by
doubling: $`j \mapsto 2j`.

```anchor gridSize
abbrev gridSize (k : ℕ) : ℕ := 2 ^ k + 1
```

```anchor gridEmbed
def gridEmbed (k : ℕ) (j : Fin (gridSize k)) : Fin (gridSize (k + 1)) :=
  ⟨2 * j.val, by grid_omega⟩
```

This preserves the ratio since $`j/2^k = 2j/2^{k+1}`. The new midpoints (odd indices at the fine
level) are where new sign data is added.

# The Sign Tower

A *sign tower* is a sequence of sign games on these grids, with embeddings satisfying
coherence: signs at embedded points must match the coarse level.

The tower also requires a betweenness structure (an abstract notion of "c is between a and b")
and convexity axioms ensuring that signs are preserved under interpolation. These are what make
the OD transfer across levels work.

The key fields of a `SignTower`:

 * `game k`: a sign game at each level k

 * `embed k`: injection from level k into level k+1

 * `coherent`: signs at embedded points match the coarse level

 * `playerConvex`: betweenness in a player's own actions preserves signs

 * `opponentConvex`: betweenness in opponents' actions preserves signs

 * `fine_between_embedded_at`: every fine point lies between two embedded coarse points

# Invariance

At level 0, any strictly monotone transformation of payoffs preserves the game:

```lean
open Invariance in
example : ∀ {I : Type*} [DecidableEq I] [Fintype I]
    {V : I → Type*} [∀ i, DecidableEq (V i)]
    (u : (i : I) → (∀ j, V j) → Int)
    (f : (i : I) → Int → Int) (hf : ∀ i, StrictMono (f i)),
    SignGame.ofPayoffs (fun i q => f i (u i q)) = SignGame.ofPayoffs u :=
  fun u f hf => ofPayoffs_strictMono_invariant u f hf
```

At higher levels, only positive affine transformations preserve signs:

```lean
example : ∀ (c D slope : ℕ) (hslope : 0 < slope) (k : ℕ)
    (j : Fin (gridSize k)),
    cmpSign (slope * c * j.val) (slope * D * 2^k) = cmpSign (c * j.val) (D * 2^k) :=
  fun c D slope hslope k j => affine_preserves_oppSign c D slope hslope k j
```

Non-affine transforms can break signs. The cube function g(x) = x^3 preserves level-0 signs
but changes them at level 2:

```lean
example :
    exampleOppSign 2 ⟨1, by grid_omega⟩ = .pos ∧
    transformedOppSign 2 ⟨1, by grid_omega⟩ = .neg :=
  counterexample_level2

example :
    exampleOppSign 0 ⟨0, by grid_omega⟩ = transformedOppSign 0 ⟨0, by grid_omega⟩ ∧
    exampleOppSign 0 ⟨1, by grid_omega⟩ = transformedOppSign 0 ⟨1, by grid_omega⟩ :=
  signs_agree_level0
```

In the limit as k goes to infinity, the grid becomes dense and the invariance group shrinks to
positive affine maps — exactly the von Neumann-Morgenstern uniqueness class.

# Nash Refinement

Nash equilibria at coarser levels can always be refined to finer levels consistently.
At every level k, there exists a Nash equilibrium that is OD and has convex faces:

```lean
variable (T : SignTower (Fin 2))

example : ∀ (k : ℕ),
    ∃ σ : Profile (Fin 2) (T.V k),
      (T.game k).IsNash σ ∧
      (∀ i, (T.game k).OutsideDom i σ) ∧
      T.HasConvexFaces k σ :=
  fun k => T.nash_refining_sequence k
```

Moreover, Nash equilibria at adjacent levels are compatible — the fine-level equilibrium
refines the coarse-level one:

```lean
example : ∀ (k : ℕ),
    ∃ σ : Profile (Fin 2) (T.V k),
    ∃ σ' : Profile (Fin 2) (T.V (k+1)),
      (T.game k).IsNash σ ∧
      (T.game (k+1)).IsNash σ' ∧
      T.ProfileRefines k σ' σ :=
  fun k => T.nash_at_next_level_refines k
```

The proof embeds a coarse Nash equilibrium into the fine level, takes its convex closure, and
runs the descent algorithm. The key technical result is that OD transfers across levels after
embedding and convex closure.

# Concrete Towers

The formalization includes four canonical 2-player towers, constructed via `GridTower` — a
structure that specifies per-player opponent-sign functions on the dyadic grids:

 * _Prisoner's Dilemma_ (`pdTower`): opponent signs always negative, defection dominates at every mixing ratio.

 * _Matching Pennies_ (`mpTower`): opponent signs flip at the boundary, unique mixed equilibrium refining toward p = 1/2.

 * _Symmetric Coordination_ (`symCoordTower`): sign change at the midpoint, equilibrium at p = 1/2.

 * _Battle of the Sexes_ (`bosTower`): asymmetric indifference points at p = 3/4 and p = 1/4.

Each comes with a proof of Nash existence at every level:

```lean
example :
    ∀ k, ∃ σ, (pdTower.game k).IsNash σ ∧
      (∀ i, (pdTower.game k).OutsideDom i σ) ∧
      pdTower.toSignTower.HasConvexFaces k σ :=
  pdTower_nash_sequence

example :
    ∀ k, ∃ σ, (mpTower.game k).IsNash σ ∧
      (∀ i, (mpTower.game k).OutsideDom i σ) ∧
      mpTower.toSignTower.HasConvexFaces k σ :=
  mpTower_nash_sequence
```
