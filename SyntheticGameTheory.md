# Synthetic Game Theory: A Coordinate-Free Approach to Nash Equilibria

## Overview

This document describes a formalization of game theory that avoids numerical probabilities and cardinal utilities entirely. Instead of representing mixed strategies as probability distributions over actions, we work with **synthetic simplices**—abstract spaces characterized only by a mixing operation and order structure on edges. Utilities are purely **ordinal**: we only compare payoffs, never add or multiply them.

The key innovation is the **Crossing Axiom**, which asserts that when two order-respecting functions "cross" on an interval (one starts above and ends below the other), there exists a point where they are equal. This axiom captures the essence of the Intermediate Value Theorem without requiring the real numbers.

## Motivation

Standard game theory relies heavily on the structure of ℝ:
- Mixed strategies are probability distributions (elements of the standard simplex Δⁿ ⊂ ℝⁿ⁺¹)
- Expected utilities are computed via integrals or sums with real coefficients
- Nash existence proofs use Brouwer or Kakutani fixed-point theorems, which are fundamentally about ℝⁿ

But what structure is *actually* needed? The core arguments use:
1. **Convexity**: Mixing strategies is meaningful
2. **Order**: We can compare utilities
3. **Betweenness**: Mixing interpolates between extremes
4. **Crossing/Fixed Points**: Certain maps have fixed points or crossing points

Our approach axiomatizes exactly this structure, inspired by how **cubical type theory** treats the interval: not as a subset of ℝ, but as an abstract type with endpoints and paths between them.

## The Framework

### Synthetic Intervals

A **synthetic interval** $I$ has:
- Endpoints: `zero` and `one`
- A total order: `le : I → I → Prop`
- A mixing operation: `mix : I → I → I`

The mixing operation satisfies:
- **Idempotence**: `mix(x, x) = x`
- **Symmetry**: `mix(x, y) = mix(y, x)`
- **Weak betweenness**: If `x ≤ y`, then `x ≤ mix(x,y) ≤ y`

We do *not* require that `mix(x,y)` is the midpoint, or that there's any metric structure. The mix operation just produces *some* point between its arguments.

### Ordinal Utilities

An **ordinal utility type** $R$ is simply a totally ordered set. We never add utilities, multiply them by probabilities, or compute expectations. We only ask: is $u(σ) ≤ u(τ)$?

### Betweenness for Functions

A function $f: I → R$ satisfies **weak betweenness** if:
$$f(x) ≤ f(y) \implies f(x) ≤ f(\text{mix}(x,y)) ≤ f(y)$$

This is the order-theoretic version of "expected utility of a mixture lies between the utilities of the components."

### The Crossing Axiom

Two functions $f, g: I → R$ **cross** if:
$$(f(0) ≤ g(0) \text{ and } g(1) ≤ f(1)) \quad\text{or}\quad (g(0) ≤ f(0) \text{ and } f(1) ≤ g(1))$$

**Crossing Axiom**: If $f$ and $g$ both satisfy weak betweenness and they cross, then there exists $p ∈ I$ with $f(p) = g(p)$.

This axiom is *not* derived—it's a fundamental postulate of the theory. Different models realize it differently:
- In $[0,1] ⊂ ℝ$, it follows from the Intermediate Value Theorem
- In dyadic rationals, it follows from bisection search
- In constructive settings, the crossing point can be computed to arbitrary precision

### Synthetic Simplices

A **synthetic simplex** over vertices $V = \{v_1, \ldots, v_n\}$ consists of:
- A carrier set $Δ$
- An embedding $\text{vertex}: V → Δ$
- A mixing operation $\text{mix}: Δ × Δ → Δ$

Each pair of vertices spans an **edge**, which is itself a synthetic interval with an orientation.

### Finite Games

A **finite game** has:
- Finitely many players
- Finitely many pure strategies per player
- An ordinal utility type $R$
- A payoff function on pure strategy profiles

Mixed strategies for player $i$ are points in the synthetic simplex $Δ(A_i)$ over their pure strategies.

### Extended Utilities

We postulate that utilities extend from pure profiles to mixed profiles while satisfying **betweenness in each coordinate**: when one player mixes while others hold fixed, that player's opponents' utilities satisfy betweenness along the mixing path.

## Nash Equilibrium Existence

### Definition

A **Nash equilibrium** is a mixed strategy profile where every player is best-responding: no player can improve their utility by unilaterally changing strategy.

### Key Lemma: Best Responses Contain Pure Strategies

By betweenness, the utility of any mixed strategy lies between the utilities of the pure strategies it's built from. Therefore, the maximum utility is achieved at some pure strategy. This means:

> For any opponent profile, some pure strategy is always a best response.

### The 2×2 Case

Consider a 2-player game where each player has 2 actions: Player 1 has {Top, Bottom}, Player 2 has {Left, Right}.

**Case 1: Pure Nash exists.** Some cell $(a, b)$ has the property that neither player wants to deviate. Done.

**Case 2: No pure Nash (cycling).** The best-response structure cycles:
- Against Left, Player 1 prefers (say) Top
- Against Top, Player 2 prefers Right  
- Against Right, Player 1 prefers Bottom
- Against Bottom, Player 2 prefers Left
- ...and back to the start

In this case, Player 2's preference *crosses* as Player 1 moves from Top to Bottom:
- At Top: Player 2 prefers Left (i.e., $u_2(\text{Top}, L) > u_2(\text{Top}, R)$)
- At Bottom: Player 2 prefers Right (i.e., $u_2(\text{Bot}, L) < u_2(\text{Bot}, R)$)

Define:
- $f(τ_1) = u_2(τ_1, L)$: Player 2's payoff from Left as Player 1 mixes
- $g(τ_1) = u_2(τ_1, R)$: Player 2's payoff from Right as Player 1 mixes

Both $f$ and $g$ satisfy betweenness (by the extended utility axiom). They cross (by the cycling structure). Therefore, by the **Crossing Axiom**, there exists $τ_1^*$ where $f(τ_1^*) = g(τ_1^*)$—i.e., Player 2 is **indifferent** between Left and Right.

Similarly, there exists $τ_2^*$ where Player 1 is indifferent between Top and Bottom.

**Claim**: $(τ_1^*, τ_2^*)$ is a Nash equilibrium.

**Proof**: 
- Player 1 faces $τ_2^*$ where they're indifferent, so any strategy (including $τ_1^*$) is a best response.
- Player 2 faces $τ_1^*$ where they're indifferent, so any strategy (including $τ_2^*$) is a best response.

Both players are best-responding. ∎

### General Case

For games with more actions or players, the argument extends via a multi-dimensional version of the Crossing Axiom (essentially axiomatizing the conclusion of Brouwer's fixed-point theorem or Sperner's lemma).

The key insight remains: the Crossing Axiom, applied to the best-response structure, produces indifference points that form equilibria.

## The Lean Formalization

The accompanying Lean 4 file (`SyntheticGameTheory.lean`) structures the development as:

1. **`SyntheticInterval`**: Typeclass for abstract intervals with mixing
2. **`OrdinalUtility`**: Typeclass for totally ordered utility codomains
3. **`Betweenness` / `weakBetweenness`**: Predicates on functions
4. **`Crosses`**: Predicate for crossing functions
5. **`CrossingAxiom`**: Typeclass asserting crossing points exist
6. **`SyntheticSimplex`**: Structure for abstract mixed strategy spaces
7. **`FiniteGame`**: Structure for games with ordinal utilities
8. **`ExtendedUtility`**: Typeclass for utility extension satisfying betweenness
9. **`isNashEquilibrium`**: Definition of Nash equilibrium
10. **`nash_exists_2x2`** and **`nash_exists`**: Existence theorems

### Proof Obligations

The file contains `sorry` placeholders for:

- **Basic order lemmas** for `SyntheticInterval` (reflexivity, antisymmetry, transitivity on edges)
- **`Edge.toSyntheticInterval`**: Showing edges satisfy the interval axioms
- **`bestResponseContainsPure`**: That best responses always include a pure strategy
- **`indifference_point_exists`**: Using the Crossing Axiom to find indifference points
- **`twoByTwo_nash_exists`**: The full 2×2 theorem
- **`nash_exists`**: The general existence theorem

### Implementation Notes for the Coding Agent

1. **Type universe management**: The file uses `universe u v` for carrier types and utility types. Be careful with universe constraints in definitions.

2. **Fintype instances**: Pure strategies need `Fintype` instances. These should be inferred automatically for `Fin n` or explicit enumerations.

3. **The `MixedProfile` structure**: Currently a bit awkward because each player's simplex is bundled with the profile. You may want to refactor so simplices are fixed globally for the game.

4. **Extended utilities**: The `ExtendedUtility` class has placeholder conditions. The full statement should say that for fixed opponents, the function $τ_i ↦ u_j(σ_{-i}, τ_i)$ satisfies `weakBetweenness` when restricted to any edge of player $i$'s simplex.

5. **The crossing argument**: The key is showing that the cycling condition implies the functions $f$ (payoff from one action) and $g$ (payoff from another) satisfy `Crosses`. This is a straightforward case analysis on the cycling structure.

6. **Consider using Mathlib's `LinearOrder`** instead of rolling custom order typeclasses, if compatibility allows.

## Models

### Standard Model (ℝ)

Take $I = [0,1]$, $\text{mix}(x,y) = (x+y)/2$, order is the usual $≤$. The Crossing Axiom follows from the Intermediate Value Theorem.

### Dyadic Rationals

Take $I = \{k/2^n : 0 ≤ k ≤ 2^n, n ∈ ℕ\}$, with the same mixing and order. Crossing points are found by bisection. This model is fully computable.

### Constructive/Type-Theoretic

The interval can be taken as a higher inductive type (as in cubical type theory). Crossing points are then witnesses/data, not mere existence claims. A Nash equilibrium becomes a tuple that includes the equilibrium strategies *and* the crossing-point witnesses that certify it.

## Summary

| Concept | Standard Theory | Synthetic Theory |
|---------|-----------------|------------------|
| Mixed strategies | Probability distributions in Δⁿ ⊂ ℝⁿ⁺¹ | Points in synthetic simplex |
| Mixing | Convex combination with weights | Abstract `mix` operation |
| Utilities | Real-valued expected utilities | Ordinal comparisons only |
| Nash existence proof | Kakutani fixed-point theorem | Crossing Axiom |
| Computational content | Non-constructive (Brouwer) | Can be constructive (bisection) |

The synthetic approach isolates the essential structure needed for Nash equilibria: order, mixing, betweenness, and the existence of crossing points. Everything else—specific probabilities, cardinal utilities, the real number field—is incidental to the standard presentation but not mathematically necessary.
