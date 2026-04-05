# Discrete Game Theory

A Lean 4 formalization of game theory fundamentals without real numbers, probability, or fixed-point theorems. Nash equilibria are computed by a terminating descent algorithm on finite face lattices.

The formalization is fully constructive — no `classical`, `noncomputable`, `sorry`, or `axiom`.

## Structure

- **`DiscreteGameTheory/Base.lean`** — core library: sign games, face lattices, dominance, Nash equilibrium existence.
- **`DiscreteGameTheory/Examples.lean`** — example games and Nash equilibrium computations.

## Building

Requires [elan](https://github.com/leanprover/elan) (Lean version manager).

```bash
lake build                    # build everything
lake build DiscreteGameTheory # library only
```

## Documentation

Interactive source code with proof states: [pablo-vs.github.io/discrete-game-theory](https://pablo-vs.github.io/discrete-game-theory/)

## Authorship

Most of the high-level theory and definitions are my own, but Claude wrote
almost all of the code, with some contributions from Codex and Gemini.

## License

Apache 2.0
