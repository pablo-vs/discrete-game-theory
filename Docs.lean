import VersoManual
import DiscreteGameTheory.Base
import DiscreteGameTheory.Examples

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option pp.rawOnError true
set_option verso.exampleProject "."
set_option verso.exampleModule "DiscreteGameTheory.Base"

open Base

#doc (Manual) "Discrete Game Theory" =>

%%%
authors := ["Pablo Villalobos"]
%%%

This is a formalization of game theory fundamentals in Lean 4, without real numbers, probability,
or fixed-point theorems. Nash equilibria are computed by a terminating descent algorithm on finite
face lattices.

The key ideas:

 * Games record ordinal preferences — which action is better, not by how much.

 * The probabilistic simplex of strategies is replaced by a discrete version. A *face* of the simplex (nonempty subset of vertices) replaces probability distributions as the notion of mixed strategy.

 * Instead of using expected utility, preferences between faces are defined conservatively: A dominates B only when every action in A beats every action in B against every consistent opponent play. This produces a partial preference order on mixed strategies for each player.

 * *Nash equilibrium existence* follows from a terminating descent algorithm that starts considering the mixture of all actions and eliminates dominated actions.

 * The algorithm is not only provably terminating but directly *executable*: a computable `findNash` runs the descent and returns a concrete Nash profile on any finite game, ready for `#eval`.

# Games and Nash Equilibria

Game theory studies strategic interactions: a set of players, each choosing actions, each with
preferences over outcomes defined by a payoff table. The fundamental concept is *Nash equilibrium* — a combination of
strategies where no player can improve by changing only their own choice.

Standard game theory builds on real-valued payoffs and probability distributions, proving Nash
existence via topological fixed-point theorems. We replace all of this with discrete, finite
structures.

The main goal of this section is to prove that all games with finite players and
finite actions have at least one Nash equilibrium. Standard game theory uses a
non-constructive fixed point theorem to do this, but in our setup we can give a
constructive algorithm.

## Sign Games

A game has a finite set of players. Each player has a finite set of actions.
Given an index of players `I: Type` and a function `V: I → Type` of possible actions
for each player, a _pure profile_ is defined as a choice of action for every player.

```anchor PureProfile
/-- A pure profile is a choice of action for each player. -/
abbrev PureProfile := ∀ i : I, V i
```

In standard game theory, each player has a payoff function. We replace this with something weaker:
for each player and each pair of pure profiles, we record a _sign_ — positive if the
first profile is preferred, negative if the second is preferred, zero if equivalent.

```anchor Sign
inductive Sign where
  | pos : Sign
  | neg : Sign
  | zero : Sign
```

A sign game bundles these signs with the axioms of a preference relation: reflexivity (comparing
a profile to itself gives zero), antisymmetry (swapping the two profiles flips the sign), and
transitivity. Comparing two actions for player i at an opponent profile is then derived as the
sign between the corresponding single-player updates of that profile.

```anchor SignGame
structure SignGame where
  sign : (i : I) → PureProfile I V → PureProfile I V → Sign
  sign_refl : ∀ i p, sign i p p = .zero
  sign_antisym : ∀ i p q, sign i p q = (sign i q p).flip
  sign_trans : ∀ i p q r, (sign i p q).nonneg → (sign i q r).nonneg →
    (sign i p r).nonneg
```

A sign game can be constructed from integer payoff functions. The resulting signs just compare
payoff values. Crucially, any strictly monotone transformation of the payoffs produces the
same sign game — the theory is ordinal, not cardinal.

## Faces as Mixed Strategies

In standard game theory, players randomize using probability distributions over actions. We use
a discrete analogue: a _face_ is a nonempty subset of actions.  Intuitively
a face represents an unknown probability distribution.

```anchor Face
def Face (V : Type*) [DecidableEq V] := { S : Finset V // S.Nonempty }
```

The face \{a, b\} represents "some distribution supported on a and b," without specifying
which one. The name comes from the simplex, which all the possible mixtures of a set of
vertices form a face. A vertex \{a\} is a pure strategy. The full face (the whole simplex)
is the maximally mixed strategy. Mixing is set union — commutative, associative, idempotent.

A _profile_ assigns a face to each player.

```anchor Profile
/-- A profile is a choice of face (mixed strategy) for each player. -/
abbrev Profile := ∀ i : I, Face (V i)
```

## Dominance

In standard game theory one uses expected utility to extend a value function of pure actions
to one of probabilistic actions. The analogous ordinal concept is a preference order on faces
derived from the order on pure actions. Face A dominates face B for player i when every action
in A is at least as good as every action in B, against every consistent opponent play.

```anchor Dominates
def Dominates (i : I) (σ : Profile I V) (A B : Face (V i)) : Prop :=
  ∀ a ∈ A.1, ∀ p : PureProfile I V,
    ConsistentAt σ i p → ∀ b ∈ B.1, (G.signAction i p a b).nonneg
```

This conservative comparison produces a *partial order*. Two faces can be genuinely incomparable —
and this is the key insight that makes it possible to prove the existence of Nash equilibria,
as we'll see later.

A _strict deviation_ exists when A dominates the current face but not vice versa. A profile is
*Nash* when no player has a strict deviation:

```anchor StrictDom
def StrictDom (i : I) (σ : Profile I V) (A : Face (V i)) : Prop :=
  G.Dominates i σ A (σ i) ∧ ¬G.Dominates i σ (σ i) A

def IsNash (σ : Profile I V) : Prop :=
  ∀ (i : I) (A : Face (V i)), ¬G.StrictDom i σ A
```

## Examples

Consider two classic 2-player games where each player has two actions. We write C/D
(cooperate/defect) for the Prisoner's Dilemma and H/T (heads/tails) for Matching Pennies.

### Prisoner's Dilemma

For each player, defection is strictly preferred regardless of the opponent's action:

$$`\begin{array}{c|ccc} \textbf{Opp} & & \textbf{Player} & \\ \hline C & C & \prec & D \\ D & C & \prec & D \end{array}`

Since D is better against every opponent action, the face \{D\} dominates every other face.
The dominance order on faces (for either player, against a fully mixed opponent) is total:

$$`\begin{array}{c|ccccc} \textbf{Opp} & & & \textbf{Player} & & \\ \hline \{C\} & \{C\} & \prec & \{C,D\} & \prec & \{D\} \\ \{D\} & \{C\} & \prec & \{C,D\} & \prec & \{D\} \\ \{C,D\} & \{C\} & \prec & \{C,D\} & \prec & \{D\} \end{array}`

The unique Nash equilibrium is mutual defection — no player can deviate from \{D\}.

### Matching Pennies

Player 1 (matcher) wants to match; player 2 (mismatcher) wants to differ.
For the matcher:

$$`\begin{array}{c|ccc} \textbf{Opp} & & \textbf{Matcher} & \\ \hline H & H & \succ & T \\ T & H & \prec & T \end{array}`

The preferred action depends on the opponent — H is better against H, T is better against T.
When the opponent plays the full face \{H, T\}, neither action dominates the other.
The dominance order on faces (against the fully mixed opponent) is flat — everything is
incomparable:

$$`\begin{array}{c|ccccc} \textbf{Opp} & & & \textbf{Matcher} & & \\ \hline \{H,T\} & \{H\} & \parallel & \{T\} & \parallel & \{H,T\} \end{array}`

There is no pure Nash equilibrium. But the fully mixed profile (\{H,T\} for both players) _is_
Nash — no face strictly dominates \{H,T\}, because incomparability blocks every deviation.
This is the key mechanism: the deviation cycle HH $`\to` HT $`\to` TT $`\to` TH $`\to` HH dissolves into
incomparability when we move from pure to mixed strategies.


## Nash Existence
%%%
tag := "outside-dom"
%%%

Every finite game has a Nash equilibrium:

```anchor nash_exists
theorem nash_exists [Fintype I] [∀ i, Fintype (V i)] [∀ i, Nonempty (V i)] :
    ∃ σ, G.IsNash σ :=
```

The proof is a descent algorithm. It starts from the fully mixed profile (every player plays
a mix of every action) and iteratively eliminates dominated actions.

The algorithm maintains the *OutsideDom (OD)* invariant: for each player, every action outside
the current face is dominated by every action inside:


```anchor OutsideDom
def OutsideDom (i : I) (σ : Profile I V) : Prop :=
  ∀ v, v ∉ (σ i).1 → ∀ w, w ∈ (σ i).1 →
    G.Dominates i σ (Face.vertex w) (Face.vertex v)
```

This is the invariant of *iterated elimination of strictly dominated strategies* (IESDS): a
profile satisfying OD can be read as a state of IESDS where every eliminated action has been
shown to be dominated by every surviving one. In standard game theory, IESDS terminates at
the set of *rationalizable strategies*, which is generally larger than the set of Nash
equilibria — IESDS gives you the support but not the mixing weights, and you still need a
fixed-point argument to land on Nash. In the discrete theory there are no weights to solve
for: the face *is* the answer, so IESDS and Nash coincide, and the descent lands on a Nash
equilibrium directly.

The full profile is vacuously OD (no outside actions). At each step, if some player has a strict
deviation, we restrict their face to a strict subface. Profile size (sum of face cardinalities)
decreases, so the algorithm terminates.

OD is preserved because: for the restricting player, the new face dominates the old, so it
dominates the already-dominated outside actions. For other players, antitonicity applies —
shrinking an opponent's face only makes domination easier.

## Running the descent

The theorem `nash_exists` above is a pure existence statement — it uses `Classical.em` via
`by_cases` on `IsNash` and so is not directly executable. The same descent is also available
as a `def`, `findNash`, which returns a Nash profile as data rather than asserting its
existence:

```anchor findNash
def findNash [Nonempty I] [∀ i, Nonempty (V i)] :
    { σ : Profile I V // G.IsNash σ } :=
```

(the `Fintype` and `LinearOrder` instances on `I` and each `V i` come from the enclosing
section)

The extra `LinearOrder` assumptions exist only to make the search for a strict deviation
computable: `Finset.toList` is noncomputable (a `Finset` is a quotient of lists by
permutation, so picking a canonical list requires choice), so the deviation search instead
sorts the finite action set with `Finset.sort` and enumerates subsets via `List.sublists`.
All concrete finite games — `Fin n`, `Bool`, products of these — satisfy the requirement for
free.

Concretely, running `findNash` on the Prisoner's Dilemma yields the unique pure Nash
equilibrium `(D, D)`, and running it on Matching Pennies yields the fully mixed profile:

```
#eval (pd.findNash.1 0).1   -- {false} (D)
#eval (pd.findNash.1 1).1   -- {false} (D)
#eval (mp.findNash.1 0).1   -- {false, true}
#eval (mp.findNash.1 1).1   -- {false, true}
```

Both results are theorems proven by `native_decide` in `Examples.lean`, i.e. the kernel
actually runs the descent and checks the output.
