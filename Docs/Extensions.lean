import VersoManual
import DiscreteGameTheory.CompactGame
import DiscreteGameTheory.SelfSimilarity
import DiscreteGameTheoryExamples.GridTower

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option pp.rawOnError true
set_option verso.exampleProject "."
set_option verso.exampleModule "DiscreteGameTheory.CompactGame"

open Base Refinement

#doc (Manual) "Extensions" =>

The tower structure supports several extensions beyond the basic refinement story.

# Compact Games

A sign tower implicitly defines an equivalence class of games sharing the same Nash structure.
The tower itself _is_ the compact game — no limit construction is needed.

Two key operations on towers:

```lean -show
namespace Docs
variable {I : Type*} [DecidableEq I] [Fintype I]
variable (T : SignTower I)
```

_Shift_ re-roots a tower at level k, giving a meta-game where level-k actions become the base
actions. The shifted tower's level-0 game is the original tower's level-k game:

```lean
def shift (k : ℕ) : SignTower I := T.shift k
```

_OD propagation_ lifts an OD profile from level k to level k + n by repeatedly embedding and
taking convex closures:

```lean
def iterEmbedClose (k : ℕ)
    (σ : Profile I (T.V k)) (n : ℕ) :
    Profile I (T.V (k + n)) :=
  T.iterEmbedClose k σ n
```

```lean -show
end Docs
```

Nash equilibria at higher levels live inside the propagated core:

```lean
variable {I : Type*} [DecidableEq I] [Fintype I]
variable (T : SignTower I)

open SignTower in
example (n : ℕ)
    {σ : ∀ i, Face (T.V 0 i)}
    (h_od : ∀ i, (T.game 0).OutsideDom i σ) :
    ∃ τ, (T.game (0 + n)).IsNash τ ∧
      (∀ i, Face.IsSubface (τ i)
        (iterEmbedClose T 0 σ n i)) :=
  (nash_inside_iterEmbedClose T 0 n h_od).imp
    fun _ ⟨hN, hsub, _⟩ => ⟨hN, hsub⟩
```

# Infinite-Action Games

Games with infinitely many actions can be reduced to finite cores via the OD machinery.
If a finite subset of actions satisfies OD (every outside action is dominated), then Nash
equilibria exist — the infinite actions outside the core are strategic noise:

```lean
example :
    ∀ {I : Type*} [DecidableEq I] [Fintype I]
    {V : I → Type*} [∀ i, DecidableEq (V i)]
    (G : SignGame I V) (core : ∀ i, Face (V i))
    (h_od : ∀ i, G.OutsideDom i core),
    ∃ σ, G.IsNash σ :=
  fun G core h_od => G.nash_of_core core h_od
```

For example, Matching Pennies on the natural numbers has actions 0, 1, 2, ... where
actions above 1 are heavily penalized. The OD core is \{0, 1\}, reducing it to standard
2-action Matching Pennies:

```lean
example : ∃ σ, mpNat.IsNash σ := mpNat_nash
```

# Self-Similarity

The refinement tower has a self-similar structure. Single-step embeddings can be iterated:

```anchor embedIter (module := DiscreteGameTheory.SelfSimilarity)
def embedIter (T : SignTower I) (k n : ℕ) (i : I) : T.V k i → T.V (k + n) i :=
  match n with
  | 0 => id
  | n + 1 => T.embed (k + n) i ∘ T.embedIter k n i
```

Coherence extends to iterated embeddings: signs at level k + n, evaluated on iterated embeddings
of level-k arguments, equal the signs at level k.

Any level-(k+n) game can be _restricted_ to a level-k game via the iterated embedding, and by
coherence the restricted game has exactly the same signs as the original coarse game.

# Grid Children

For grid-based towers, the self-similarity is concrete. The level-(k+1) grid splits at its
midpoint into two copies of a level-k grid — a left child and a right child:

```anchor leftChild (module := DiscreteGameTheoryExamples.GridTower)
def leftChild (k : ℕ) (j : Fin (gridSize k)) : Fin (gridSize (k + 1)) :=
  ⟨j.val, by grid_omega⟩
```

```anchor rightChild (module := DiscreteGameTheoryExamples.GridTower)
def rightChild (k : ℕ) (j : Fin (gridSize k)) : Fin (gridSize (k + 1)) :=
  ⟨j.val + 2 ^ k, by grid_omega⟩
```

They share a boundary point — the last point of the left child is the first point of the
right child:

```lean
open GridChildren in
example : ∀ (k : ℕ),
    leftChild k ⟨2 ^ k, by grid_omega⟩ =
    rightChild k ⟨0, Nat.succ_pos _⟩ :=
  fun k => boundary_shared k
```

# Per-Player Independence

Different players can operate at different resolution levels and the game still makes sense.
The sign for each player is determined by their own level, because `sign_irrel` ensures it
depends only on opponents' actions, and coherence handles the type mismatch:

```lean
example : ∀ (T : SignTower I) (κ : I → ℕ),
    ∃ σ, (T.multiLevelGame κ).IsNash σ :=
  fun T κ => T.multiLevelGame_nash_exists κ
```
