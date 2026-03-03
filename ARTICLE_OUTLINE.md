#### Summary
Game theory in its most basic form studies the strategic interactions between a set of players who can take certain actions. The core concept is that of Nash equilibrium: a combination of player strategies that ensures no player can improve its outcome by unilateral action. This basic concept is enough to capture some of the challenges of coordination.

This is a description of a simplified version of game theory, which makes no use of probability, not even of real numbers, and yet captures all the strategic content of standard game theory.

This simplified theory is interesting for three reasons:
- By making each game describable with discrete, finite elements, it becomes much easier to reason formally about programs that play games. This was my original motivation, and the theory of *program equilibrium* built on top of synthetic game theory will be explained in a following post.
- The simplification makes it easy to reason about this theory with precision and formalize it in a proof assistant. None of the theorems require sophisticated mathematical machinery such as nonconstructive fixed point theorems.
- The formalization illustrates several mathematical techniques and patterns which generalize to other areas of mathematics.


# Part 1: The theory

## Basic definitions
A game has a finite number of players, N. Each player has a finite set of actions it can take, $V i$. When each player chooses an action, the game assigns a payoff to each player. In standard game theory, these payoffs are numbers. In this version we just assume players have a preference ordering. More precisely, we call a *pure profile* a selection of action for each player. Each player's payoff is encoded by an ordering (technically a total preorder) on pure profiles.

For example, here's the Prisoner's Dilemma, it has two players with two actions each, cooperate and defect. Each player has preferences CD < DD < CC < DC. Suppose that we start from some profile and let each player retroactively change its action to achieve a better outcome. Then (show graph of deviations) it's clear that the agents end up at DD, from which none can unilaterally improve their situation. We define a Nash equilibrium as a profile in which no player can unilaterally move to a strictly better profile. Such unilateral moves to better profiles are called deviations, so we can also say that a Nash equilibrium is a profile in which no player has a strict unilateral deviation.

As is well-known, there might be no Nash equilibrium among pure profiles. For example (some game like MP with no pure equilibrium). The problem is that the map from a profile to its best response has no fixed points. To ensure that a Nash equilibrium exists, we need a way to "contract" the cycle to a fixed point.

The standard theory solves this by letting players randomize their strategies. Each player can select a probability distribution over strategies, called a mixed strategy. The set of all mixed strategies forms a simplex (illustration), a convex set in which each distribution is a point.

The combination of mixed strategies for each player is called a mixed profile. The standard theory then shows that (the space of mixed profiles is compact, contractible, whatever), and uses the (X) fixed point theorem to show that a Nash equilibrium always exists.

We do something similar: a mixed strategy is just a formal combination of pure strategies. Meaning, if a and b are strategies, then mix(a,b) is a mixed strategy, and mix(a,mix(a,b)) = mix(mix(a,b),b) = mix(a,b). With this definition, the space of mixed strategies looks like a *discrete simplex* (illustration), where an element is just identified by which vertices are in the mixture. So the mixture just behaves like the union of subsets of vertices, and it represent all possible distributions whose support is in the mixture.

Pure profiles are a choice of pure action by each player, and profiles in general are a choice of strategy by each player. This means that, viewed as sets, profiles are the products of individual faces of each player's simplex.

In standard game theory, players can compare the value of mixed profiles by expected utility. In our version we have a similar extension of the order in pure profiles to an order in mixed profiles. The payoff orders extend to partial orders on each player's faces when conditioned on any particular profile. Two faces $A, B$ satisfy $A \leq B$ in profile $P$ when all $a \in A, b \in B$ satisfy $a \leq b$ in all pure profiles consistent with $P$.

Note that this order can be partial when conditioned on mixed profiles: if two faces A,B contain actions a,b that strictly dominate each other in different pure profiles p,q of a profile P, meaning (a < b | p) and (b < a | q), then we can't say that A <= B nor B <= A in P.

This happens because what we are secretly doing is forgetting information about which exact profile we are in, and what the payoffs are. (explain "up to monotone transformation"). So face A only dominates face B when we are absolutely sure that strategies in A dominate strategies in B no matter what the other players are doing.

Despite this order being partial, we can still define a Nash equilibrium, it's a (possibly mixed) profile such that no player has a strict deviation.

In the Matching Pennies example, we see that the only Nash equilibrium is that both players play a mixed strategy.
## Existence of Nash equilibria

With the basic definitions out of the way, we would now like to prove that every finite game has a Nash equilibrium.

(explain the reduction algorithm, invariants and proof).

## Superrationality

If a player always plays it's best response, we can with some justification call it rational. But Pareto profiles exist, they need not be Nash equilibria, all agents would prefer to move to a Pareto profile but can't do it unilaterally. We define a superrational profile as a Pareto profile which is not Nash. We note that while rationality can be defined for each player, we can only define superrationality as a property of particular actions, not of individual players.
In the next post we'll see how seeing each player as a computer program that reasons about the other players lets us define super-rationality.
# Part 2: Behind the scenes

What's the relationship between the ordinal theory and the cardinal theory? Why do I say that the ordinal theory contains all the strategic behavior? This part requires a bit more mathematical sophistication.

As we mentioned before, the ordinal theory can be interpreted as working "up to monotone transformations", both of payoffs and of probabilities. So the ordinal theory is just the cardinal theory after we forgot some information, or alternatively the cardinal theory is just the ordinal theory with some extra information. We can make this more precise, and interpolate between the two.

## Refinement

Define level k games: barycentric grids with total orders on grid profiles (or general refinement by induction if the code is more general than that, not sure right now)

A level k+1 game coarsens to a level k game.

We can move from a level k game to a level k+1 game by choosing some new signs.

Define level-k signs generated by a cardinal payoff. Show that affine transformations of the cardinal payoffs produce the same signs, while some non-affine transformations change the signs and some don't. Cardinal game theory is invariant to affine transformations. So at each level we are placing more and more constraints on the transformations we allow, until at the limit only affine transformations are left, and probabilities determine real numbers as sequences of nested closed intervals (this last part about limits is informal).

Choosing sign-data is equivalent to choosing a refinement of Nash profiles.

So, the refinement tower interpolates between the ordinal and cardinal theories. But, level 0 contains all the information in the tower

## Self-similarity

Level-k games as depth-k+1 trees, level 0 games as depth-1 trees from the root (a point). Types of embedding. Each k-subtree in a level j tree can be seen as a level k game

Unmixing, non-convex mixtures are irrelevant. And unmixing allows one to see any k-tree as a level 0 game, and find its Nash equilibria, which will always be convex faces of the level k game, because although we forgot the betweenness structure it is still there.

So each subtree of any tree can be modeled as a level 0 game. So the level 0 theory models all finite levels, and the full structure self-assembles from just the level 0 without us needing to input any more information. Level 0 games, ordinal games, already determine everything else.

TODO: compactness and continuity story. Some morphisms are discontinuous, some properties are not compact. Normally this is defined separately, in cases like this I think they are determined by the structure itself

Analogy: N is the simplest object that can contain a point and a nontrivial endomorphism: N -> N. So the basic model of N is just a point . and an endomorphism . -> . Repeated application of this endomorphism yields chains. But the one-step chain . -> . simultaneously describes all steps of the chain, and also the "reduction" of the chain itself by composition, 0 -> n.

Each level can be finite because it has absorbing mixtures. So given any theory which must be infinite because it is closed under some operation, you can define an axiomatic theory in which repeated application of the operation is absorbed, and then "unroll" the absorbers in a controlled way to rebuild the full theory.
