# Discrete Game Theory

<!-- Code references: DiscreteGameTheory/<file>.lean#L<start>-L<end>
     To make clickable, prepend your repo URL: https://github.com/OWNER/REPO/blob/main/ -->


#### Summary

Game theory studies strategic interactions: a set of players, each choosing actions, each with preferences over outcomes. The central concept is Nash equilibrium — a combination of strategies where no player can improve their situation by changing only their own choice.

Standard game theory builds this on real-valued payoffs and probability distributions. Players randomize their strategies, expected utilities are computed, and the existence of Nash equilibria is proved using topological fixed-point theorems (Brouwer or Kakutani) applied to the space of probability distributions.

This post describes a simplified version that throws away the real numbers entirely. No probabilities, no expected utility — just discrete, finite structures. And yet it captures all the strategic content of the standard theory.

Why care?

- **Programs playing games.** When each game is described by discrete, finite data, it becomes much easier to reason formally about programs that play games. The theory of *program equilibrium* built on top of discrete game theory will be explained in a following post.
- **Formal verification.** Everything here is formalized in Lean 4 and machine-checked. None of the proofs require nonconstructive fixed-point theorems or sophisticated analysis — the Nash existence proof is a simple terminating algorithm.
- **Mathematical patterns.** The formalization illustrates a structural parallel between continuous and discrete mathematics: the same abstract pattern (monotone maps on structured spaces have fixed points) appears in both the standard and discrete theories, just instantiated in different categories.

All code blocks below are from the Lean formalization. They typecheck.

---

# Part 1: The theory

## Games and preferences

A game has a finite set of players $I$. Each player $i$ has a finite set of actions $V_i$. A *pure profile* is a choice of action for every player — a function assigning to each player one of their actions.

```lean
variable (I : Type*) (V : I → Type*)
abbrev PureProfile := ∀ i : I, V i
```
<!-- source: DiscreteGameTheory/Base.lean#L172-L175 -->

$$p \in \prod_{i \in I} V_i$$

In standard game theory, each player has a real-valued payoff function over profiles, and players prefer higher payoffs. We replace this with something weaker: each player just has a preference ordering over profiles.

More precisely, for each player $i$, each pure profile $p$, and each pair of actions $a, b$ available to player $i$, we record a *sign* — positive if $a$ is better, negative if $b$ is better, zero if they're equivalent. This sign is the player's preference between playing $a$ versus $b$, holding all other players' actions fixed at $p$.

```lean
inductive Sign where
  | pos : Sign
  | neg : Sign
  | zero : Sign
```
<!-- source: DiscreteGameTheory/Base.lean#L16-L19 -->

A sign game bundles these signs together with the axioms you'd expect of a preference relation: comparing an action to itself gives zero (reflexivity), swapping the two actions flips the sign (antisymmetry), and the ordering is transitive. There's one more axiom, `sign_irrel`, which says that player $i$'s preference between their own actions $a$ and $b$ depends only on what the *other* players are doing — not on what player $i$ "was" playing. This is natural: the sign compares two hypothetical choices for player $i$, so $i$'s "current" action shouldn't matter.

```lean
structure SignGame where
  sign : (i : I) → PureProfile I V → V i → V i → Sign
  sign_refl : ∀ i p a, sign i p a a = .zero
  sign_antisym : ∀ i p a b, sign i p a b = (sign i p b a).flip
  sign_trans : ∀ i p a b c, (sign i p a b).nonneg → (sign i p b c).nonneg →
    (sign i p a c).nonneg
  sign_irrel : ∀ i p q a b, (∀ j, j ≠ i → p j = q j) → sign i p a b = sign i q a b
```
<!-- source: DiscreteGameTheory/Base.lean#L203-L209 -->

A sign game is a function $s_i(p, a, b) \in \{+, -, 0\}$ for each player $i$, profile $p$, and pair of actions $a, b \in V_i$, satisfying:

$$s_i(p, a, a) = 0 \qquad s_i(p, a, b) = -s_i(p, b, a)$$
$$s_i(p, a, b) \geq 0 \;\wedge\; s_i(p, b, c) \geq 0 \;\Rightarrow\; s_i(p, a, c) \geq 0$$
$$(\forall j \neq i,\; p_j = q_j) \;\Rightarrow\; s_i(p, a, b) = s_i(q, a, b)$$

Technically, this makes each player's preferences a *total preorder* — a reflexive, transitive relation where any two elements are comparable — on their own actions, given any fixed choice by the opponents. "Total preorder" rather than "total order" because two different actions can be equally preferred (sign zero).

## The Prisoner's Dilemma

Here's the classic example. Two players each choose to cooperate (C) or defect (D). The game is symmetric — both players have the same preferences from their own perspective:

- I cooperate, they defect: worst
- We both defect: bad
- We both cooperate: good
- I defect, they cooperate: best

We encode C as `true`, D as `false`, and write the ranking as a function from (myAction, opponentAction) to a number. The numbers are just labels — only their ordering matters:

```lean
def pd_rank (me opp : Bool) : ℕ :=
  match me, opp with
  | true,  false => 0   -- I cooperate, they defect (worst)
  | false, false => 1   -- both defect
  | true,  true  => 2   -- both cooperate
  | false, true  => 3   -- I defect, they cooperate (best)

def genPD := symGame2x2 pd_rank
```
<!-- source: DiscreteGameTheory/Examples.lean#L213-L220 -->

To be clear: the numbers 0, 1, 2, 3 are not payoffs. They're just a compact way of writing down an ordering. Any other numbers with the same ordering produce the same game:

```lean
def pd_rank_alt (me opp : Bool) : ℕ :=
  match me, opp with
  | true,  false => 10
  | false, false => 20
  | true,  true  => 30
  | false, true  => 40

theorem pd_same_game :
    (symGame2x2 pd_rank).sign = (symGame2x2 pd_rank_alt).sign
```
<!-- source: DiscreteGameTheory/Examples.lean#L228-L239 -->

We'll prove this in general shortly — it's one of the main theorems.

## Nash equilibrium

A *deviation* for player $i$ is a switch from their current action to some alternative that's at least as good. A *strict deviation* is one where the alternative is strictly better — the player weakly prefers the new action over the old one, but not vice versa.

For example, in the Prisoner's Dilemma the graph of possible strict deviations looks like this:

[Diagram: The four pure profiles arranged in a square. Arrows point from (C,C) to (D,C) labeled "player 0 deviates", from (C,C) to (C,D) labeled "player 1 deviates", from (D,C) to (D,D) labeled "player 1 deviates", and from (C,D) to (D,D) labeled "player 0 deviates". (D,D) has no outgoing arrows.]

No matter where you start, the players end up at (D,D), where neither can improve by switching. This is a Nash equilibrium: a profile where no player has a *strict unilateral deviation* — a way to switch their own action and get a strictly better outcome. In the case of PD, only (D,D) is a Nash equilibrium.

So we define a pure profile as a Nash equilibrium if no player has a strict deviation, that is its comparison sign with any other actions of the player is nonnegative. This is the same definition as in standard game theory, just stated in terms of preference orderings instead of numerical payoffs.

```lean
def IsPureNash (p : PureProfile I V) : Prop :=
  ∀ (i : I) (v : V i), (G.sign i p (p i) v).nonneg

theorem genPD_unique_pureNash :
    ∀ p : PureProfile (Fin 2) (fun _ : Fin 2 => Bool),
    genPD.IsPureNash p ↔ p = (fun _ => false)
```
<!-- source: DiscreteGameTheory/Base.lean#L504-L505 + DiscreteGameTheory/Examples.lean#L131-L133 -->


## The problem with pure strategies

Not every game has a Nash equilibrium in pure strategies. Consider Matching Pennies: two players each choose Heads or Tails. Player 0 wants to match; player 1 wants to differ. This game isn't symmetric, so we use separate rankings:

```lean
def genMP := game2x2_rank
  (fun me opp => match me, opp with  -- P0 wants to match
    | true,  true  => 1
    | false, false => 1
    | _,     _     => 0)
  (fun me opp => match me, opp with  -- P1 wants to differ
    | true,  false => 1
    | false, true  => 1
    | _,     _     => 0)

theorem genMP_no_pureNash : ∀ p, ¬genMP.IsPureNash p
```
<!-- source: DiscreteGameTheory/Examples.lean#L245-L261 -->

Whatever pure profile you pick, one player wants to switch. The response "map" cycles: H→T→H→T→... The standard solution is to let players randomize their actions.

## Mixed strategies as faces

In standard game theory, players can play a mixed strategy: a probability distribution over actions. The set of all mixed strategies for a player with $n$ actions forms a simplex $\Delta^{n-1}$ — a convex body in $\mathbb{R}^{n-1}$ which looks like a higher-dimensional version of a triangle. The vertices are the actions, also called pure strategies, the interior points are the mixtures.

We do something analogous but discrete. A *mixed strategy* is just a nonempty subset of actions — a *face* of the simplex. The face $\{a, b\}$ represents "some distribution supported on $a$ and $b$," without specifying which one.

[Diagram: A triangle with vertices {a}, {b}, {c}. The edges are {a,b}, {b,c}, {a,c}. The interior is {a,b,c}. Label this "The discrete simplex (face lattice)" and contrast with the continuous simplex — a filled triangle — labeled "The continuous simplex".]

A vertex `{a}` is a pure strategy. The full face is the maximally mixed strategy. Mixing is just set union, and it satisfies the expected algebraic properties — it's commutative, associative, and idempotent:

```lean
def Face (V : Type*) [DecidableEq V] := { S : Finset V // S.Nonempty }

def vertex (v : V) : Face V :=
  ⟨{v}, Finset.singleton_nonempty v⟩

def full [Fintype V] [Nonempty V] : Face V :=
  ⟨Finset.univ, Finset.univ_nonempty⟩

def mix (A B : Face V) : Face V :=
  ⟨A.1 ∪ B.1, A.2.mono Finset.subset_union_left⟩
```
<!-- source: DiscreteGameTheory/Base.lean#L117-L136 -->

$$\text{Face}(V) = \{ S \subseteq V \mid S \neq \emptyset \}$$
$$\text{vertex}(v) = \{v\} \qquad \text{full} = V \qquad \text{mix}(A, B) = A \cup B$$

```lean
theorem mix_comm (A B : Face V) : mix A B = mix B A
theorem mix_idem (A : Face V) : mix A A = A
theorem mix_assoc (A B C : Face V) : mix (mix A B) C = mix A (mix B C)
```
<!-- source: DiscreteGameTheory/Base.lean#L140-L147 -->

We were working with pure profiles so far, in which every player plays a pure action. A general profile is now a choice of face for each player:

```lean
abbrev Profile := ∀ i : I, Face (V i)
```
<!-- source: DiscreteGameTheory/Base.lean#L175 -->

$$\sigma \in \prod_{i \in I} \text{Face}(V_i)$$

## Comparing mixed strategies

In standard game theory, players compare mixed strategies using expected utility. If I'm considering playing distribution $a$ versus distribution $b$ against opponent distribution $p$, I compute the expected payoff of each against every possible opponent action, weighted by their probability, and compare.

We need an analogous comparison for faces. The idea is conservative: face $A$ dominates face $B$ for player $i$ (written $A \geq B$) only when *every* action in $A$ is at least as good as *every* action in $B$, no matter what the opponents do within their current faces. The condition "opponents play within their faces" is named `ConsistentAt σ i p` — it says every opponent $j \neq i$ has $p_j \in \sigma_j$.

```lean
def Dominates (i : I) (σ : Profile I V) (A B : Face (V i)) : Prop :=
  ∀ a ∈ A.1, ∀ p : PureProfile I V,
    ConsistentAt σ i p → ∀ b ∈ B.1, (G.sign i p a b).nonneg
```
<!-- source: DiscreteGameTheory/Base.lean#L225-L227 -->

$$A \geq_i^\sigma B \;\;\iff\;\; \forall a \in A,\; \forall p \in \textstyle\prod_{j \neq i} \sigma_j,\; \forall b \in B,\quad s_i(p, a, b) \geq 0$$

Reading this: "$A$ dominates $B$ for player $i$ in profile $\sigma$" means: for every action $a$ in $A$, for every pure profile $p$ consistent with the opponents' faces in $\sigma$, for every action $b$ in $B$, player $i$ weakly prefers $a$ to $b$.

This is the right notion because we've forgotten the exact probability distribution each opponent plays. We only know the *support* — which actions are in play. So face $A$ can only be said to dominate face $B$ when it does so *for every possible distribution the opponents might use*.

An important consequence: **this ordering can be partial.** In the continuous theory, expected utility always gives a total order on strategies (any two distributions have comparable expected payoffs, given a fixed opponent strategy). But here, two faces can be genuinely incomparable.

Matching Pennies makes this concrete. When both players mix fully (every action in play), neither Heads nor Tails dominates the other for player 0:

```lean
theorem genMP_partial_order :
    let σ : Profile (Fin 2) (fun _ : Fin 2 => Bool) := fun _ => Face.full
    ¬genMP.Dominates 0 σ (Face.vertex true) (Face.vertex false) ∧
    ¬genMP.Dominates 0 σ (Face.vertex false) (Face.vertex true)
```
<!-- source: DiscreteGameTheory/Examples.lean#L162-L174 -->

Why? When the opponent plays Heads, player 0 prefers Heads. When the opponent plays Tails, player 0 prefers Tails. Since the opponent's face includes both, neither dominates — the comparison is ambiguous. This partiality is exactly what we need: it means **mixing creates incomparability, and incomparability breaks cycles.**

So we can define strict deviations for mixed profiles as well, and Nash equilibria are just the absence of any strict deviation for any player:

```lean
def StrictDom (i : I) (σ : Profile I V) (A : Face (V i)) : Prop :=
  G.Dominates i σ A (σ i) ∧ ¬G.Dominates i σ (σ i) A

def IsNash (σ : ∀ j, G.S j) : Prop :=
  ∀ i s, ¬G.StrictPref i σ s (σ i)
```
<!-- source: DiscreteGameTheory/Base.lean#L273-L278 + DiscreteGameTheory/Compact.lean#L59-L60 -->
Player $i$ has a strict deviation to $A$ from profile $\sigma$ when $A \geq_i^\sigma \sigma_i$ but $\sigma_i \not\geq_i^\sigma A$.

$$\text{IsNash}(\sigma) \;\;\iff\;\; \forall i \in I,\; \forall A \in \text{Face}(V_i),\quad \neg\big(A >_i^\sigma \sigma_i\big)$$

In the Matching Pennies deviation graph among pure profiles, we saw a cycle: H beats T beats H beats T... But when both players mix, neither H nor T strictly dominates the other. The cycle dissolves into incomparability. And the fully mixed profile is Nash:

```lean
theorem genMP_mixed_nash : genMP.IsNash (fun _ : Fin 2 => Face.full (V := Bool))
```
<!-- source: DiscreteGameTheory/Examples.lean#L149-L158 -->



## Existence of Nash equilibria

We can now state and prove the main theorem: every finite game has a Nash equilibrium.

```lean
theorem nash_exists [Fintype I] [∀ i, Fintype (V i)] [∀ i, Nonempty (V i)] :
    ∃ σ, G.IsNash σ
```
<!-- source: DiscreteGameTheory/Base.lean#L432-L434 -->

$$\forall G,\; \exists \sigma \in \textstyle\prod_i \text{Face}(V_i),\quad \text{IsNash}(\sigma)$$

The proof is a descent algorithm — a terminating loop that starts from the "maximally mixed" profile and iteratively removes dominated actions until no player has a strict deviation.

### The structural parallel

Before diving into the algorithm, let's see why Nash equilibria must exist at all. The argument has the same shape as the standard proof — they're both instances of the same abstract pattern.

In the standard theory: the space of mixed profiles is a product of simplices (compact, convex). The best-response correspondence is a map from this space to itself, and it's continuous in the right sense (upper hemicontinuous with convex values). Kakutani's fixed-point theorem says: continuous self-maps of compact convex sets have fixed points.

Here: the space of profiles is a product of face lattices (finite, with joins). The domination relation `Dominates` is monotone/antitone in the lattice operations — enlarging an opponent's face makes domination harder (antitone in opponents), and subfaces of a dominating face still dominate (monotone in the player's own face). This is the lattice-theoretic analogue of continuity: preservation of the lattice structure, the way continuous maps preserve limits.

Both proofs follow the same template: **the strategic structure respects the geometry of the mixing space, and that's enough to guarantee equilibrium.** The standard theory uses topological continuity on a compact convex set. The discrete theory uses order-theoretic monotonicity on a finite lattice. The standard proof invokes a fixed-point theorem. The discrete proof constructs the fixed point directly by descent — which is the constructive version of the same argument, made possible by finiteness.

### The algorithm

The algorithm maintains two invariants:

1. **OutsideDom (OD):** For each player $i$, every action *outside* the current face is dominated by every action *inside* the face. Intuitively: we've already checked that the removed actions are genuinely worse.

```lean
def OutsideDom (i : I) (σ : Profile I V) : Prop :=
  ∀ v, v ∉ (σ i).1 → ∀ w, w ∈ (σ i).1 →
    G.Dominates i σ (Face.vertex w) (Face.vertex v)
```
<!-- source: DiscreteGameTheory/Base.lean#L285-L287 -->

$$\text{OD}_i(\sigma) \;\;\iff\;\; \forall v \notin \sigma_i,\; \forall w \in \sigma_i,\quad \{w\} \geq_i^\sigma \{v\}$$

2. **Decreasing profile size:** Each step strictly shrinks some player's face, so the total number of actions across all players decreases.

```lean
def profileSize [Fintype I] (σ : Profile I V) : ℕ :=
  Finset.univ.sum (fun i => (σ i).1.card)
```
<!-- source: DiscreteGameTheory/Base.lean#L391-L392 -->

$$|\sigma| = \sum_{i \in I} |\sigma_i|$$

**Start:** The full profile — every player plays every action — is vacuously OD (there are no outside actions to check).

```lean
theorem OutsideDom.maximal (i : I)
    [∀ j, Fintype (V j)] [∀ j, Nonempty (V j)] :
    G.OutsideDom i (fun _ => Face.full) :=
  fun v hv => absurd (Finset.mem_univ v) hv
```
<!-- source: DiscreteGameTheory/Base.lean#L296-L299 -->

**Loop:** If the current profile $\sigma$ is already Nash, we're done. If not, some player $i$ has a strict deviation to some face $A$. The key lemma is that we can *restrict* this deviation: there exists a face $A' \subseteq \sigma_i$ with $A' \neq \sigma_i$ such that $A'$ is still a strict deviation.

```lean
theorem exists_restrictingStrictDom {i : I} {σ : Profile I V} {A : Face (V i)}
    (h_inv : G.OutsideDom i σ)
    (h_dev : G.StrictDom i σ A) :
    ∃ A' : Face (V i),
      G.StrictDom i σ A' ∧ Face.IsSubface A' (σ i) ∧ A' ≠ σ i
```
<!-- source: DiscreteGameTheory/Base.lean#L364-L368 -->

We replace $\sigma_i$ with $A'$, which is strictly smaller. Profile size decreases.

```lean
theorem profileSize_decreases [Fintype I] {i : I} {σ : Profile I V} {A : Face (V i)}
    (hsub : Face.IsSubface A (σ i)) (hne : A ≠ σ i) :
    profileSize (Function.update σ i A) < profileSize σ
```
<!-- source: DiscreteGameTheory/Base.lean#L395-L397 -->

**Preservation of OD:** Crucially, the OD invariant is preserved across the update. For the player $i$ who just changed, this holds because $A'$ dominates $\sigma_i$, so it certainly dominates the actions outside $\sigma_i$ (which were already dominated). For other players $j \neq i$, this holds by antitonicity: shrinking player $i$'s face only makes domination *easier* for other players (fewer opponent actions to worry about).

```lean
theorem OutsideDom.preserved {i : I} {σ : Profile I V} {A : Face (V i)}
    (h_inv : G.OutsideDom i σ)
    (h_sub : Face.IsSubface A (σ i))
    (h_dev : G.Dominates i σ A (σ i)) :
    G.OutsideDom i (Function.update σ i A)

theorem OutsideDom.preserved_other {i j : I} (hij : j ≠ i)
    {σ : Profile I V} {A : Face (V i)}
    (h_inv : G.OutsideDom j σ)
    (h_sub : Face.IsSubface A (σ i)) :
    G.OutsideDom j (Function.update σ i A)
```
<!-- source: DiscreteGameTheory/Base.lean#L303-L338 -->

**Termination:** Profile size is a natural number that decreases each step. So the algorithm terminates, producing a Nash equilibrium.

```lean
theorem nash_exists_of_outsideDom [Fintype I]
    (σ : Profile I V)
    (h_od : ∀ i, G.OutsideDom i σ) :
    ∃ τ, G.IsNash τ := by
  by_cases h : G.IsNash σ
  · exact ⟨σ, h⟩
  · simp only [IsNash, not_forall, not_not] at h
    obtain ⟨i₀, A, hA⟩ := h
    obtain ⟨A', hdev, hsub, hne⟩ := exists_restrictingStrictDom G (h_od i₀) hA
    have hdec := profileSize_decreases hsub hne
    exact nash_exists_of_outsideDom (Function.update σ i₀ A') (fun j => by
      by_cases hij : j = i₀
      · subst hij; exact OutsideDom.preserved G (h_od j) hsub hdev.1
      · exact OutsideDom.preserved_other G hij (h_od j) hsub)
  termination_by profileSize σ
```
<!-- source: DiscreteGameTheory/Base.lean#L416-L430 -->

The full theorem follows by starting from the full profile:

```lean
theorem nash_exists [Fintype I] [∀ i, Fintype (V i)] [∀ i, Nonempty (V i)] :
    ∃ σ, G.IsNash σ :=
  nash_exists_of_outsideDom G (fun _ => Face.full) (fun i => OutsideDom.maximal G i)
```
<!-- source: DiscreteGameTheory/Base.lean#L432-L434 -->

### A 3-player example

This works for any number of players. Here's a 3-player coordination game where each player has two actions and gets payoff 1 if all agree, 0 otherwise:

```lean
def coordGame3 : SignGame (Fin 3) (fun _ : Fin 3 => Bool) where
  sign i p a b :=
    let agree (x : Bool) : Bool :=
      (if (0 : Fin 3) = i then x else p 0) == (if (1 : Fin 3) = i then x else p 1) &&
      (if (1 : Fin 3) = i then x else p 1) == (if (2 : Fin 3) = i then x else p 2)
    let payA : Int := if agree a then 1 else 0
    let payB : Int := if agree b then 1 else 0
    intSign payA payB

theorem coordGame3_nash_allTrue : coordGame3.IsPureNash (fun _ => true)
theorem coordGame3_nash_allFalse : coordGame3.IsPureNash (fun _ => false)
```
<!-- source: DiscreteGameTheory/Examples.lean#L97-L120 -->

Both "everyone plays true" and "everyone plays false" are Nash — and the general `nash_exists` theorem guarantees that at least one equilibrium exists for any finite game, without us having to find it explicitly.

## Superrationality

A Nash equilibrium is "stable" — no one can improve unilaterally. But it might not be *good*. The Prisoner's Dilemma makes this vivid: mutual defection (D,D) is Nash, but mutual cooperation (C,C) is better for both players. Both players would prefer to coordinate on (C,C), but neither can get there by acting alone.

A profile where every player prefers it to all alternatives is called *Pareto optimal*. A *superrational* profile would be one that's Pareto optimal but not Nash — the kind of outcome that requires players to somehow "see past" their individual incentives.

The key observation is that while we can define *rationality* as a property of individual players (a player is rational if they always best-respond), superrationality is necessarily a property of *actions in context*, not of individual players. You can't be superrational alone — it requires coordinated deviation from what individual rationality would dictate.

In the next post, we'll see how modeling each player as a computer program — one that can inspect and reason about the other players' programs — lets us define and achieve superrationality in a precise sense.

---

# Part 2: Behind the scenes

What's the relationship between this ordinal theory and the standard cardinal theory? Why do I claim that the ordinal theory contains all the strategic content?

The short answer: the ordinal theory is the cardinal theory with some information forgotten. The sign game records only *which action is better*, not *by how much*. It records only *which actions are in play*, not *with what probability*. Everything we've thrown away is "cardinal" information — magnitudes, scales, exact numbers. Everything we've kept is "ordinal" — rankings, comparisons, structural relationships.

We can make this precise, and we can build a tower of theories that interpolates between the two.

## Level 0: Ordinal invariance

The sign game `ofPayoffs u` constructed from payoff functions $u$ depends only on the *ordinal ranking* of the payoffs, not their cardinal values. Any strictly monotone transformation of the payoffs produces the same sign game:

```lean
theorem ofPayoffs_strictMono_invariant [Fintype I]
    (u : (i : I) → (∀ j, V j) → Int)
    (f : (i : I) → Int → Int) (hf : ∀ i, StrictMono (f i)) :
    SignGame.ofPayoffs (fun i q => f i (u i q)) = SignGame.ofPayoffs u
```
<!-- source: DiscreteGameTheory/Invariance.lean#L57-L60 -->

$$\forall i,\; f_i \text{ strictly monotone} \;\;\Rightarrow\;\; \text{Game}(f_i \circ u_i) = \text{Game}(u_i)$$

Each player can have a *different* transformation — player 0's payoffs can be doubled while player 1's are cubed — and as long as each transformation is strictly monotone (preserves the ranking), the game is unchanged. This is the ordinal invariance theorem: Nash equilibria at level 0 depend only on the ordinal ranking of outcomes.

Concretely, the Prisoner's Dilemma with payoffs (3, 0, 5, 1) and payoffs (7, 1, 11, 3) — obtained by applying $f(x) = 2x + 1$ — produce the same sign game:

```lean
theorem pd_same_sign_game :
    SignGame.ofPayoffs pdPayoff' =
    SignGame.ofPayoffs pdPayoff (I := Fin 2) (V := fun _ : Fin 2 => Bool)
```
<!-- source: DiscreteGameTheory/Invariance.lean#L129-L134 -->

## The refinement tower

So the level-0 ordinal theory forgets a lot: it keeps only the ranking, not the magnitudes. Can we add back some of the forgotten information, in a controlled way?

Yes. The idea is to refine the discrete simplex into a finer grid, like zooming in on a number line. At level 0, each player's strategy space is just the set of vertices — individual actions. At level 1, we add midpoints between adjacent vertices, getting $2^1 + 1 = 3$ points. At level 2, we add midpoints of midpoints, getting $2^2 + 1 = 5$ points. At level $k$, we have $2^k + 1$ grid points.

```lean
abbrev gridSize (k : ℕ) : ℕ := 2 ^ k + 1

def gridEmbed (k : ℕ) (j : Fin (gridSize k)) : Fin (gridSize (k + 1)) :=
  ⟨2 * j.val, by grid_omega⟩
```
<!-- source: DiscreteGameTheory/Refinement.lean#L132-L143 -->

Each grid point represents a possible "mixing ratio." Grid point $j$ at level $k$ represents the probability $j / 2^k$. The level-$k$ grid is embedded into the level-$(k+1)$ grid by $j \mapsto 2j$ — doubling the index, which preserves the ratio since $j/2^k = 2j/2^{k+1}$.

At each level, we have a sign game on the grid, and the signs must be *coherent*: the sign between two embedded grid points at the fine level must match the sign between the original points at the coarse level.

The full tower structure is:

```lean
structure GeneralSignTower (I : Type*) [DecidableEq I] [Fintype I] where
  V : ℕ → I → Type*
  game : (k : ℕ) → Base.SignGame I (V k)
  embed : ∀ k i, V k i → V (k+1) i
  coherent : ∀ k i (p : PureProfile I (V k)) (a b : V k i),
    (game (k+1)).sign i (embedPureProfile (embed k) p) (embed k i a) (embed k i b)
    = (game k).sign i p a b
  -- plus: betweenness, convexity, embedding, and spanning axioms
```
<!-- source: DiscreteGameTheory/Refinement.lean#L246-L288 -->

A tower is a sequence of games $(G_k)_{k \geq 0}$ on action sets $(V_k)_{k \geq 0}$ with embeddings $e_k : V_k \hookrightarrow V_{k+1}$ satisfying coherence:

$$s_i^{(k+1)}(e_k(p),\; e_k(a),\; e_k(b)) \;=\; s_i^{(k)}(p, a, b)$$

The `coherent` axiom says exactly what we want: zooming in doesn't change the signs at the old grid points. The new grid points (the midpoints) get *new* sign data — this is the "cardinal" information being added.

### What determines the new signs?

Consider a 2-player game. At each level, each player's strategy is a grid point. The game's sign between two grid points for player 0 depends on what grid point player 1 is at. For bilinear games (which include most standard 2-player games), this takes the form:

```lean
def bilinearSignGame (n : ℕ) (oppSign₀ oppSign₁ : Fin n → Sign) :
    SignGame (Fin 2) (fun _ : Fin 2 => Fin n) where
  sign i p a b :=
    let opp := p (1 - i)
    if (i : ℕ) = 0 then Sign.mul (cmpSign b.val a.val) (oppSign₀ opp)
    else Sign.mul (cmpSign b.val a.val) (oppSign₁ opp)
```
<!-- source: DiscreteGameTheory/BilinearExamples.lean#L44-L55 -->

The sign is a product of two factors: the comparison between the two actions (which one has a higher index, representing "more mixing toward one pure strategy"), and the "opponent sign" — which depends on which grid point the opponent is at. The opponent sign tells you *which direction* of mixing is favorable, given the opponent's position.

When we refine from level $k$ to level $k+1$, the old grid points keep their old opponent signs (coherence). The new midpoints get new opponent signs, which are constrained by the convexity axioms: if both neighbors agree, the midpoint must agree; if they disagree (a sign change), the midpoint can go either way.

### Affine invariance

At level 0, any strictly monotone transformation preserves the game. At higher levels, the situation is different. The grid structure introduces genuine cardinal content: the sign at a midpoint depends on *where exactly* the indifference point falls, which is sensitive to the scale of payoffs.

Positive affine transformations — $f(x) = \alpha x + \beta$ with $\alpha > 0$ — preserve the signs at all levels:

```lean
theorem affine_preserves_oppSign (c D slope : ℕ) (hslope : 0 < slope) (k : ℕ)
    (j : Fin (gridSize k)) :
    cmpSign (slope * c * j.val) (slope * D * 2^k) = cmpSign (c * j.val) (D * 2^k)
```
<!-- source: DiscreteGameTheory/Invariance.lean#L154-L160 -->

But non-affine monotone transformations can change the signs. Here's a concrete example: consider a game where the indifference point is at probability $p = 2/5$. The original signs use $\text{cmpSign}(5j, 2 \cdot 2^k)$. Applying $g(x) = x^3$ to the payoffs shifts the indifference point to $p = 8/35 \approx 0.229$, giving signs $\text{cmpSign}(35j, 8 \cdot 2^k)$.

At level 0, both agree — the indifference point is between the same pair of grid points (0 and 1). But at level 2, the grid point $j = 1$ represents $p = 1/4 = 0.25$, which lies between $2/5$ and $8/35$. So the original and transformed games disagree at this grid point:

```lean
theorem counterexample_level2 :
    exampleOppSign 2 ⟨1, by grid_omega⟩ = .pos ∧
    transformedOppSign 2 ⟨1, by grid_omega⟩ = .neg
```
<!-- source: DiscreteGameTheory/Invariance.lean#L183-L186 -->

The first game says "action A is better at $p = 1/4$" (the indifference point $2/5$ is above $1/4$, so we're in A's region). The transformed game says "action B is better at $p = 1/4$" (the indifference point $8/35$ is below $1/4$, so we've crossed into B's region). Yet at level 0, they agree:

```lean
theorem signs_agree_level0 :
    exampleOppSign 0 ⟨0, by grid_omega⟩ = transformedOppSign 0 ⟨0, by grid_omega⟩ ∧
    exampleOppSign 0 ⟨1, by grid_omega⟩ = transformedOppSign 0 ⟨1, by grid_omega⟩
```
<!-- source: DiscreteGameTheory/Invariance.lean#L190-L193 -->

So the tower interpolates between the ordinal and cardinal theories. At level 0, the invariance group is all strictly monotone transformations (very large). At each level, the grid gets finer, and the invariance group shrinks — fewer transformations preserve all the signs. In the limit as $k \to \infty$, the grid becomes dense, and the only transformations that preserve signs at *every* level are the positive affine maps $f(x) = \alpha x + \beta$ with $\alpha > 0$. This is exactly the von Neumann–Morgenstern uniqueness class for expected utility.

### Nash refinement

The tower structure lets us prove something strong: Nash equilibria at coarser levels can always be refined to Nash equilibria at finer levels, in a consistent way.

```lean
theorem nash_refining_sequence (k : ℕ) :
    ∃ σ : Profile I (T.V k),
      (T.game k).IsNash σ ∧
      (∀ i, (T.game k).OutsideDom i σ) ∧
      T.HasConvexFaces k σ
```
<!-- source: DiscreteGameTheory/Refinement.lean#L648-L652 -->

At every level $k$, there exists a Nash equilibrium that's OD and convex-closed (its faces are convex in the grid's betweenness structure). Moreover, Nash equilibria at adjacent levels are compatible:

```lean
theorem nash_at_next_level_refines (k : ℕ) :
    ∃ σ : Profile I (T.V k),
    ∃ σ' : Profile I (T.V (k+1)),
      (T.game k).IsNash σ ∧
      (T.game (k+1)).IsNash σ' ∧
      T.ProfileRefines k σ' σ
```
<!-- source: DiscreteGameTheory/Refinement.lean#L683-L688 -->

The fine-level Nash equilibrium refines the coarse-level one: each player's face at the fine level is contained within the convex closure of the embedded coarse face. The equilibrium "zooms in" — it narrows down which part of each player's mixing interval is in play.

The proof works by:
1. Starting from a Nash equilibrium at level $k$ (which exists by `nash_exists`).
2. Embedding it into level $k+1$ via the grid embedding.
3. Taking the convex closure (filling in the midpoints).
4. Running the Nash descent algorithm at the fine level, starting from this embedded profile.

The key technical result is that the OD invariant transfers across levels: if every player is OD at the coarse level, then every player is still OD at the fine level after embedding and convex closure.

```lean
theorem outsideDom_embed_convClosure (k : ℕ)
    {σ : Profile I (T.V k)}
    (h_od : ∀ i, (T.game k).OutsideDom i σ) (i : I) :
    (T.game (k+1)).OutsideDom i
      (T.convexClosureProfile (k+1)
        (embedProfile (T.embed k) (T.embed_inj k) σ))
```
<!-- source: DiscreteGameTheory/Refinement.lean#L568-L573 -->

This is where the convexity axioms earn their keep. The proof needs to show that the embedded face dominates points outside the convex closure. It uses player convexity (betweenness in the player's own actions preserves the sign) and opponent convexity (betweenness in opponents' actions preserves the sign) to extend domination from the embedded grid points to all the midpoints.

## Self-similarity

The refinement tower has a self-similar structure. A level-$k$ game can be seen as a "tree" of level-0 games.

### Iterated embedding

The single-step embedding from level $k$ to level $k+1$ can be iterated:

```lean
def embedIter (T : GeneralSignTower I) (k n : ℕ) (i : I) : T.V k i → T.V (k + n) i :=
  match n with
  | 0 => id
  | n + 1 => T.embed (k + n) i ∘ T.embedIter k n i
```
<!-- source: DiscreteGameTheory/SelfSimilarity.lean#L34-L37 -->

And the coherence property extends: signs at level $k + n$, evaluated on iterated embeddings of level-$k$ arguments, equal the signs at level $k$.

```lean
theorem coherent_embedIter (T : GeneralSignTower I) (k n : ℕ) (i : I)
    (p : PureProfile I (T.V k)) (a b : T.V k i) :
    (T.game (k + n)).sign i
      (fun j => T.embedIter k n j (p j))
      (T.embedIter k n i a) (T.embedIter k n i b) =
    (T.game k).sign i p a b
```
<!-- source: DiscreteGameTheory/SelfSimilarity.lean#L70-L75 -->

$$s_i^{(k+n)}(e^n(p),\; e^n(a),\; e^n(b)) \;=\; s_i^{(k)}(p, a, b)$$

### Restriction

Any level-$(k+n)$ game can be *restricted* to a level-$k$ game via the iterated embedding. The restricted game just evaluates the fine-level sign function on embedded coarse-level arguments:

```lean
def restrictGame {W : I → Type*} [∀ i, DecidableEq (W i)]
    (G : SignGame I V) (f : ∀ i, W i → V i) : SignGame I W where
  sign i p a b := G.sign i (fun j => f j (p j)) (f i a) (f i b)
```
<!-- source: DiscreteGameTheory/SelfSimilarity.lean#L111-L118 -->

By coherence, this restricted game has exactly the same signs as the original coarse game:

```lean
theorem restrictGame_embedIter_eq
    (T : GeneralSignTower I) (k n : ℕ)
    (i : I) (p : PureProfile I (T.V k)) (a b : T.V k i) :
    (restrictGame (T.game (k + n)) (fun j => T.embedIter k n j)).sign i p a b =
    (T.game k).sign i p a b
```
<!-- source: DiscreteGameTheory/SelfSimilarity.lean#L129-L134 -->

So every "subtree" of the refinement tower — obtained by picking a starting level and restricting — behaves exactly like a game at that level. The tower is self-similar: the same structure repeats at every scale.

### Tree branching

For grid-based towers, the self-similarity is especially concrete. The level-$(k+1)$ grid splits into two halves — a left child and a right child — each isomorphic to a level-$k$ grid:

```lean
def leftChild (k : ℕ) (j : Fin (gridSize k)) : Fin (gridSize (k + 1)) :=
  ⟨j.val, by grid_omega⟩

def rightChild (k : ℕ) (j : Fin (gridSize k)) : Fin (gridSize (k + 1)) :=
  ⟨j.val + 2 ^ k, by grid_omega⟩
```
<!-- source: DiscreteGameTheory/SelfSimilarity.lean#L250-L256 -->

The left child maps grid point $j$ to itself (it occupies the first half). The right child maps grid point $j$ to $j + 2^k$ (shifting to the second half). They share a boundary point:

```lean
theorem boundary_shared (k : ℕ) :
    leftChild k ⟨2 ^ k, _⟩ = rightChild k ⟨0, _⟩
```
<!-- source: DiscreteGameTheory/SelfSimilarity.lean#L311-L313 -->

The last point of the left child is the first point of the right child. This is the tree branching: a level-$(k+1)$ interval $[0, 2^{k+1}]$ splits at its midpoint $2^k$ into two copies of a level-$k$ interval.

### Per-player independence

A surprising consequence of the tower structure: different players can operate at different resolution levels, and the game still makes sense.

```lean
noncomputable def multiLevelGame (T : GeneralSignTower I) (κ : I → ℕ) :
    SignGame I (fun i => T.V (κ i) i)
```
<!-- source: DiscreteGameTheory/SelfSimilarity.lean#L156-L161 -->

If player 0 is at level 3 and player 1 is at level 7, the sign for each player is determined by their own level — because `sign_irrel` ensures the sign depends only on opponents' actions, and the opponents' types are handled by coherence.

```lean
theorem multiLevelGame_nash_exists (T : GeneralSignTower I) (κ : I → ℕ) :
    ∃ σ, (T.multiLevelGame κ).IsNash σ
```
<!-- source: DiscreteGameTheory/SelfSimilarity.lean#L178-L180 -->

Nash equilibria exist in multi-level games too. And the multi-level sign is coherent with embedding:

```lean
theorem multiLevelGame_coherent_embed (T : GeneralSignTower I) (k n : ℕ)
    (i : I) (p : PureProfile I (T.V k)) (a b : T.V k i) :
    (T.multiLevelGame (fun _ => k + n)).sign i
      (fun j => T.embedIter k n j (p j))
      (T.embedIter k n i a)
      (T.embedIter k n i b) =
    (T.multiLevelGame (fun _ => k)).sign i p a b
```
<!-- source: DiscreteGameTheory/SelfSimilarity.lean#L199-L207 -->

### Level 0 determines everything

This is the punchline. Every level-$k$ game can be viewed as a level-0 game by "unmixing" — forgetting the betweenness structure and treating every grid point as an independent action. The Nash equilibria you find this way will always be convex faces of the original grid, because the betweenness structure is still there in the signs even though we're not explicitly tracking it. And these Nash equilibria, found at level 0, are the same ones the full tower machinery produces.

So the entire refinement tower — all the levels, all the convexity, all the coherence — is *determined* by the level-0 theory. The level-0 game contains all the information. The higher levels just make explicit what was already implicit: they decompose the coarse incomparabilities into finer comparisons, resolving ambiguities that were always latent in the ordinal structure.

The full structure self-assembles from level 0 without us needing to add anything. We just keep asking: "within this face of incomparable actions, can we resolve some comparisons by looking more carefully?" The tower is the answer.

### Concrete tower examples

The formalization includes full tower constructions for the standard 2-player games:

- **Prisoner's Dilemma:** `genPdTower` — opponent signs are always negative (defection always dominates regardless of mixing ratio), producing a unique Nash at every level.
- **Matching Pennies:** `genMpTower` — opponent signs flip between positive and negative at the boundary (the midpoint), capturing the unique mixed equilibrium.
- **Symmetric Coordination:** `genSymCoordTower` — opponent signs change at the midpoint, with the equilibrium at $p = 1/2$.
- **Battle of the Sexes:** `genBosTower` — asymmetric indifference points ($p = 3/4$ for player 0, $p = 1/4$ for player 1).

Each tower comes with a proof that Nash equilibria exist at every level, are OD, and have convex faces:

```lean
theorem genPdTower_nash_sequence :
    ∀ k, ∃ σ, (genPdTower.game k).IsNash σ ∧
      (∀ i, (genPdTower.game k).OutsideDom i σ) ∧
      genPdTower.toGeneralSignTower.HasConvexFaces k σ
```
<!-- source: DiscreteGameTheory/BilinearExamples.lean#L308-L312 -->

---

## Looking ahead

The discrete theory — level-0 sign games with the face lattice — captures all the strategic content of standard game theory, without real numbers or probability. The refinement tower shows exactly how the cardinal information emerges: it's a sequence of binary choices (what sign does each new midpoint get?) that progressively narrows the class of compatible utility functions from "all monotone transformations" down to "positive affine transformations only."

There's a suggestive analogy here. The natural numbers $\mathbb{N}$ are the simplest structure with a point and a nontrivial endomorphism: $0$ and the successor function $S$. The "model" of $\mathbb{N}$ is just a point and an arrow $\cdot \to \cdot$. But iterated application of the arrow produces the entire infinite chain $0 \to 1 \to 2 \to \cdots$, and the one-step chain $\cdot \to \cdot$ simultaneously describes every step.

Similarly, the level-0 theory (a game with finite actions and an ordering) is the simplest structure with the right properties (a finite lattice and monotone operations). The refinement tower is what you get by "unrolling" — repeatedly applying the refinement operation. But the level-0 theory already describes every level, because it can model any finite grid game by treating grid points as actions. The tower is not new information; it's a controlled way of unpacking what was already there.

In the next post, we'll use this discrete theory as the foundation for *program equilibrium*: what happens when each player is a computer program that can read and reason about the other players' code.
