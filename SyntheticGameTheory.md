# Synthetic Game Theory: A Coordinate-Free Approach to Nash Equilibria

## Overview

This project formalizes game theory in Lean 4 without numerical probabilities or cardinal utilities. Mixed strategies live in **synthetic simplices** — abstract spaces with a mixing operation and order structure. Utilities are purely **ordinal**: we only compare payoffs, never add or multiply them.

The key axiom is the **Crossing Axiom**: when two betweenness-respecting functions swap order between the endpoints of a synthetic interval, they must agree somewhere in the interior. This captures the Intermediate Value Theorem without the real numbers.

For games beyond 2x2, a **Synthetic Fixed-Point Axiom** provides the multi-dimensional analog of Brouwer's theorem. No cardinal arithmetic is needed: the fixed-point property is axiomatized directly, and different models verify it differently — via Brouwer in the standard model, or by providing explicit witnesses in finitely-presented models.

## Motivation

Standard game theory relies on the structure of R:
- Mixed strategies are probability distributions in the standard simplex
- Expected utilities are computed via sums with real coefficients
- Nash existence uses Brouwer or Kakutani fixed-point theorems

But the core arguments only use:
1. **Convexity**: Mixing strategies is meaningful
2. **Order**: We can compare utilities
3. **Strict betweenness**: Mixing distinct points produces a genuinely intermediate point
4. **Crossing / Fixed points**: Certain maps have crossing or fixed points

Our approach axiomatizes exactly this structure. The synthetic interval is inspired by cubical type theory's abstract interval: not a subset of R, but a type with endpoints, mixing, and order.

## The Framework

### Synthetic Intervals

A **synthetic interval** I has:
- Endpoints: `zero` and `one`, with `zero != one`
- A total order: `le : I -> I -> Prop`
- A mixing operation: `mix : I -> I -> I`

The axioms:
- **Idempotence**: `mix(x, x) = x`
- **Symmetry**: `mix(x, y) = mix(y, x)`
- **Weak betweenness**: If `x <= y`, then `x <= mix(x,y) <= y`
- **Strict betweenness**: If `x < y`, then `x < mix(x,y) < y`

Strict betweenness is the density axiom: between any two distinct points, mix always produces a genuinely new point. This rules out degenerate models where mix collapses to an endpoint, and gives the interval enough structure for bisection arguments.

### Ordinal Utilities

An **ordinal utility type** R is a `LinearOrder` — a totally ordered set. We never add utilities, multiply them by probabilities, or compute expectations. The only question is: is u(s) <= u(t)?

We use Mathlib's `LinearOrder` directly, which provides `<=`, `<`, `min`, `max`, decidable comparisons, and all standard order lemmas.

### Betweenness for Functions

A function f: I -> R satisfies **weak betweenness** if:

    f(x) <= f(y)  implies  f(x) <= f(mix(x,y)) <= f(y)

(and symmetrically when f(y) <= f(x)). This is the order-theoretic version of "the expected utility of a mixture lies between the utilities of the components."

### The Crossing Axiom

Two functions f, g: I -> R **cross** if they swap order between endpoints:

    (f(0) <= g(0) and g(1) <= f(1))  or  (g(0) <= f(0) and f(1) <= g(1))

**Crossing Axiom**: If f and g both satisfy weak betweenness and they cross, then there exists p in I with f(p) = g(p).

This is a fundamental postulate. Different models realize it differently:
- In [0,1], it follows from the Intermediate Value Theorem
- In dyadic rationals, it follows from bisection search (using strict betweenness)
- In constructive settings, the crossing point can be computed to arbitrary precision

### Synthetic Simplices

A **synthetic simplex** over a finite vertex set V has:
- A carrier set
- An embedding `vertex : V -> carrier`
- A mixing operation `mix : carrier -> carrier -> carrier`

Each pair of vertices spans an **edge**, which is itself a synthetic interval with its own order. Edges are the one-dimensional slices where the crossing axiom applies.

### Finite Games

A **finite game** has:
- Finitely many players (indexed by `Fin n`)
- Finitely many pure strategies per player (with `Fintype` instances)
- An ordinal utility type R with `LinearOrder`
- A payoff function on pure strategy profiles
- A synthetic simplex per player (the mixed strategy space)

Mixed strategy profiles are elements of the product of simplex carriers.

### Extended Utilities

We postulate that the payoff function extends from pure profiles to mixed profiles while satisfying **betweenness in each coordinate**: when one player mixes along an edge of their simplex while others hold fixed, every player's utility satisfies weak betweenness along that edge.

This axiom replaces the expectation operator. It asserts that mixing interpolates utilities in the order-theoretic sense.

## Nash Equilibrium Existence

### Definition

A **Nash equilibrium** is a mixed strategy profile where every player is best-responding: no unilateral deviation improves any player's utility.

### Key Lemma: Best Responses Contain Pure Strategies

By betweenness, the utility of any mixed strategy lies between the utilities of the pure strategies it mixes. On a single edge (two pure strategies), this is immediate: the utility at any interior point is between the two vertex utilities, so the better vertex is at least as good.

For simplices with more than two vertices, this extends by induction on the mixing structure (requiring a reachability axiom: every simplex point is reachable from vertices by iterated mixing).

### The 2x2 Case (Proved from Crossing Axiom)

Consider a 2-player game where each player has 2 actions.

**Case 1: Pure Nash exists.** Some cell is a mutual best response. Done.

**Case 2: No pure Nash (cycling).** In a LinearOrder setting, the absence of a pure Nash equilibrium forces both players' preferences to cycle:
- Player 1 prefers Top against one of Player 2's actions and Bottom against the other
- Player 2 prefers Left against one of Player 1's actions and Right against the other

This cycling means the payoff functions cross. For player 2:
- Define f(t) = u2(t, Left) and g(t) = u2(t, Right) as Player 1 mixes from Top to Bottom
- These satisfy betweenness (by the extended utility axiom)
- They cross (by the cycling structure)
- By the Crossing Axiom, there exists t1* where f(t1*) = g(t1*) — Player 2 is indifferent

Similarly, there exists t2* where Player 1 is indifferent. The profile (t1*, t2*) is Nash: each player faces an indifferent opponent, so any strategy is a best response.

### The General Case (Synthetic Fixed-Point Axiom)

For games with more actions or players, the argument requires a multi-dimensional crossing/fixed-point axiom. The **Synthetic Fixed-Point Axiom** asserts:

> Any betweenness-respecting self-map of a product of simplices has a fixed point.

This is the synthetic analog of Brouwer's fixed-point theorem. No cardinal arithmetic is needed — the axiom captures the topological content directly.

The proof of general Nash existence:
1. Construct a "best-response map" F: for each player, F maps the current profile to a profile where that player plays a best response
2. Show F satisfies the betweenness condition (from the extended utility betweenness)
3. Apply the Synthetic Fixed-Point Axiom to obtain a fixed point
4. A fixed point of the best-response map is a Nash equilibrium

The best-response map uses `mix` to move toward the best pure response, and strict betweenness ensures that fixed points are exactly the profiles where no player can improve.

## Modular Axiom Architecture

Axioms are separate typeclasses, introduced where needed:

- `[SyntheticInterval I]` — interval structure with mixing and strict betweenness
- `[LinearOrder R]` — ordinal utility comparisons
- `[CrossingAxiom I R]` — crossing points exist for betweenness-respecting functions
- `[ExtendedUtility G]` — utilities extend from pure to mixed profiles with betweenness
- `[SyntheticFixedPoint G]` — self-maps of the product of simplices have fixed points

Each theorem states exactly the axioms it needs. For a concrete model, you provide separate instances:

```
instance : SyntheticInterval MyInterval where ...
instance : CrossingAxiom MyInterval (Fin 3) where ...
```

This is more modular than bundling everything into one class, and better for pedagogy — each axiom appears at the point where it's first used.

## Models

### Standard Model (R)

Take I = [0,1], mix(x,y) = (x+y)/2, order = usual. Strict betweenness holds (the midpoint of two distinct reals is strictly between them). The Crossing Axiom follows from the IVT. The Fixed-Point Axiom follows from Brouwer.

### Dyadic Rationals

Take I = {k/2^n : 0 <= k <= 2^n, n in N}. Mixing and order as in R. Strict betweenness holds. Crossing points are found by bisection (which converges because the interval is dense under mixing). Fully computable.

### Finitely-Presented Models

The carrier types may be infinite (forced by strict betweenness), but the model is *described* by finite data:
- A finitely-generated interval type (e.g., dyadic rationals up to a given precision, extended as needed)
- A finite utility type (e.g., `Fin n`)
- Explicit crossing-point witnesses for the specific functions arising in the game

Alternatively, for specific games, one can bypass the abstract theory entirely and provide a **Nash witness** directly: the equilibrium profile together with a proof that it satisfies the Nash condition. This is the "hard-coded equilibrium" approach — the axioms are verified for the specific game instance rather than universally.

### Constructive / Type-Theoretic

The interval can be a higher inductive type (as in cubical type theory). Crossing points are witnesses/data, not mere existence claims. A Nash equilibrium becomes a tuple: the equilibrium strategies together with the crossing-point certificates.

## The Lean Formalization

The file `SyntheticGameTheory.lean` structures the development as:

1. **`SyntheticInterval`**: Typeclass with mixing, order, and strict betweenness axioms
2. **`LinearOrder R`**: Mathlib's linear order serves as ordinal utilities
3. **`weakBetweenness`**: Predicate on functions I -> R
4. **`Crosses`**: Predicate for crossing function pairs
5. **`CrossingAxiom`**: Typeclass asserting crossing points exist
6. **`SyntheticSimplex`**: Structure for abstract mixed strategy spaces, with induction principle
7. **`Edge`**: Sub-structure of a simplex forming a synthetic interval
8. **`FiniteGame`**: Structure with players, actions, simplices, payoffs
9. **`ExtendedUtility`**: Typeclass for utility extension satisfying betweenness
10. **`isNashEquilibrium`**: Definition of Nash equilibrium
11. **`SyntheticFixedPoint`**: Fixed-point axiom for general Nash existence
12. **`TwoByTwoGame`**: Specialized 2x2 game structure with examples

### What Is Proved

- `indifference_point_exists`: The crossing argument for player 2 in a 2x2 game
- `matchingPennies_no_pure_nash`: Matching Pennies has no pure Nash equilibrium
- `matchingPennies_has_cycling`: Matching Pennies exhibits preference cycling
- `prisonersDilemma_has_pure_nash`: Prisoner's Dilemma has (Defect, Defect) as pure Nash
- `battleOfSexes_has_pure_nash`: Battle of the Sexes has a pure Nash equilibrium
- `Edge.toSyntheticInterval`: Edges of simplices are synthetic intervals

### What Remains

- `twoByTwo_nash_exists`: Player 1's crossing argument (symmetric to player 2's)
- `bestResponseContainsPure`: Vertex optimality for simplex utilities
- `nash_exists`: General Nash existence from the fixed-point axiom
- Finite model examples with explicit equilibria

## Summary

| Concept | Standard Theory | Synthetic Theory |
|---------|-----------------|------------------|
| Mixed strategies | Probability distributions in R^n | Points in synthetic simplex |
| Mixing | Convex combination with weights | Abstract `mix` with strict betweenness |
| Utilities | Real-valued expected utilities | Ordinal comparisons only |
| Nash existence (2x2) | IVT on [0,1] | Crossing Axiom |
| Nash existence (general) | Brouwer/Kakutani | Synthetic Fixed-Point Axiom |
| Computational content | Non-constructive | Can be constructive (bisection) |

The synthetic approach isolates the essential structure needed for Nash equilibria: order, mixing, strict betweenness, and crossing/fixed-point axioms. Probabilities, cardinal utilities, and the real number field are incidental to the standard presentation but not mathematically necessary.
