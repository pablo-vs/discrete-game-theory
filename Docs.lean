import VersoManual

import Docs.Games
import Docs.Towers
import Docs.Extensions

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Discrete Game Theory" =>

%%%
authors := ["Pablo Villalobos"]
%%%

This is a formalization of game theory fundamentals in Lean 4, without real numbers, probability,
or fixed-point theorems. Nash equilibria are computed by a terminating descent algorithm on finite
face lattices.

The key ideas:

 * A *sign game* records ordinal preferences — which action is better, not by how much.

 * A *face* (nonempty subset of actions) replaces probability distributions as the notion of mixed strategy.

 * *Dominance* between faces is conservative: A dominates B only when every action in A beats every action in B against every consistent opponent play. This produces a partial order where incomparability breaks deviation cycles.

 * *Nash equilibrium existence* follows from a terminating descent algorithm that starts fully mixed and eliminates dominated actions.

 * A *refinement tower* interpolates between ordinal and cardinal game theory by refining the discrete simplex into finer grids, recovering von Neumann-Morgenstern expected utility in the limit.

The formalization is fully constructive — no `classical`, `noncomputable`, `sorry`, or `axiom`.

{include 0 Docs.Games}

{include 0 Docs.Towers}

{include 0 Docs.Extensions}
