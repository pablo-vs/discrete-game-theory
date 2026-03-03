# Plan: Compact Games

## Goal

Extend the synthetic game theory formalization to handle infinite and continuous games. The architecture has three layers:

1. **Game** (abstract spec) — the most general notion: mixture algebra + partial preorder + Nash as absence of strict deviations. Both ordinal (partial order) and cardinal (total order / VNM) games are instances.
2. **Compact game** (concrete spec) — a game whose strategy space is "tame" because it arises from a tower. A compact game IS a tower, possibly with an additional dominated extension. Nash exists by the refinement machinery.
3. **Construction recipes** (implementations) — concrete methods for building compact games from infinite/continuous data. The main recipe: a two-axis tower combining mixture resolution with cost-bounded action expansion.

The key insight: we never construct infinite games directly. A compact game is specified by finite data at every level, and the infinite/continuous object it represents is the derived concept.

---

## Layer 1: Game (abstract spec)

**Status: definition clear, resolves previous uncertainty about total vs partial order**

### Definition

A game is the most general structure we recognize as a strategic interaction:

- A type `I` of players
- Per player: a type `S i` of strategies (no pure/mixed distinction)
- A mixture operation making each `S i` an idempotent commutative monoid (join-semilattice)
- A partial preorder per player on strategy profiles
- Nash = no strict deviations

```
structure MixtureAlgebra (S : Type*) where
  mix : S → S → S
  mix_comm : ∀ a b, mix a b = mix b a
  mix_idem : ∀ a, mix a a = a
  mix_assoc : ∀ a b c, mix (mix a b) c = mix a (mix b c)

structure Game (I : Type*) where
  S : I → Type*
  mixture : ∀ i, MixtureAlgebra (S i)
  pref : (i : I) → (∀ j, S j) → (∀ j, S j) → Prop   -- partial preorder
  pref_refl : ∀ i σ, pref i σ σ
  pref_trans : ∀ i σ τ ρ, pref i σ τ → pref i τ ρ → pref i σ ρ

def Game.StrictDev (G : Game I) (i : I) (σ : ∀ j, G.S j) (s : G.S i) : Prop :=
  G.pref i (Function.update σ i s) σ ∧ ¬G.pref i σ (Function.update σ i s)

def Game.IsNash (G : Game I) (σ : ∀ j, G.S j) : Prop :=
  ∀ i s, ¬G.StrictDev i σ s
```

### Design choices

**Partial preorder, not total.** This is the key change from the previous plan. With a partial preorder:
- Ordinal games (current `SignGame` + `DevFaceLE`) are games: the partial order on faces comes from the quantifier structure of DevFaceLE.
- Cardinal games are games where the preorder happens to be total, which by VNM gives expected utility.
- Nash = no strict deviations works identically for both.
- One definition, one Nash theorem infrastructure.

**No compatibility axiom between mixture and preferences.** In the current `SignGame`, the sign axioms (transitivity, antisymmetry, irrelevance) encode compatibility implicitly. In the general `Game`, we don't axiomatize how preferences interact with mixture — that's game-specific. The compatibility will be a *consequence* of how specific games are constructed (from sign data, from payoffs, from towers), not an axiom of the abstract spec.

**No `Face` in the abstract spec.** The abstract game uses raw strategy types `S i`. The face lattice, vertices, subfaces — these are features of *finite ordinal games*, not of games in general.

### Connection to existing formalization

The current `SignGame` gives rise to a `Game` by:
- `S i := Face (V i)`
- `mixture := Face.mix`
- `pref i σ τ := DevFaceLE i σ (τ i) (σ i)` (note: τ is preferred to σ when τ's face dominates σ's face)

This embedding should be stated as a construction `SignGame → Game` and the Nash definitions shown to agree.

### What goes in Lean

The `Game` structure and `IsNash` definition go in Lean — they're simple and provide the umbrella that everything else fits under. The `SignGame → Game` construction goes in Lean. The proof that the two Nash definitions agree goes in Lean.

### Resolved uncertainties

1. ~~Total vs partial order~~ → Partial. Both ordinal and cardinal are instances.
2. ~~Do we need this in Lean~~ → Yes, it's simple and unifying.
3. ~~Binary vs finitary mix~~ → Binary. Finitary follows by associativity.
4. ~~Compatibility axiom~~ → Not an axiom of Game. Consequence of construction.

---

## Layer 2: Compact game (concrete spec)

**Status: architecture clear, restriction condition intentionally left semi-formal**

### Definition

A compact game is a tower, possibly with a dominated extension:

```
structure CompactGame (I : Type*) where
  tower : GeneralSignTower I         -- the core finite-level structure
  -- Optional: an ambient game with a domination condition
  -- (left semi-formal for now — see below)
```

The tower provides:
- Finite action sets `V k i` at every level k
- Sign games at every level
- Embeddings with coherence, convexity, betweenness

### The game a compact game represents

A compact game represents a `Game` whose strategy space is the convex closure of tower sections (infinite compatible sequences of grid points). But we do NOT formalize this limit in Lean. Instead:

**The compact Nash existence theorem is stated purely in tower terms:**

```
∀ k, ∃ σ_k, Nash(σ_k) ∧ OD(σ_k) ∧ ConvexClosed(σ_k) ∧ Refines(σ_{k+1}, σ_k)
```

This is already proved (`nash_refining_sequence` + `nash_at_next_level_refines`). It says: at every finite resolution, there's a Nash equilibrium, and these equilibria are compatible across resolutions. This IS Nash existence for the compact game — we just don't construct the infinite limit object.

### The dominated extension (restriction)

For games whose strategy space exceeds what the tower captures:

The tower covers a "compact core." Strategies outside the core are dominated by strategies inside. For Nash purposes, the core suffices.

**We leave this intentionally semi-formal in the compact game definition.** The reason: the shape of the domination condition depends on the construction recipe (Layer 3). Different recipes give different notions of "outside the core" and "dominated." The compact game spec says *there exists* a core that suffices; the construction recipe says *how to find it*.

What we do formalize:
- A `RestrictedGame` construction: given a `SignGame` and a "core" (a subface per player), produce a new `SignGame` on the core.
- A theorem: if every action outside the core is dominated by some action inside, then Nash equilibria of the restricted game are Nash equilibria of the original.

This is the "restriction lemma" — it's clean, independent of how the core was found.

### Resolved uncertainties

1. ~~Formalize the limit?~~ → No. Tower-level Nash + compatibility IS the theorem.
2. ~~Tower paths?~~ → Implicit. We never define them as a type. The tower levels are the formalized objects.
3. ~~Mixture on paths?~~ → Not needed. Mixture exists at each finite level (Face.mix). The infinite mixture algebra is informal.
4. ~~Cofinality condition?~~ → Left semi-formal in the spec. Made precise by each construction recipe.

---

## Layer 3: Construction recipes

**Status: mathematically clear, formalization design in progress**

### Recipe 1: Pure tower (no extension)

The simplest case. The compact game IS the tower, with no dominated extension. The strategy space at the limit is exactly the set of tower sections.

**Examples:** All existing tower constructions (genPdTower, genMpTower, genBosTower, genSymCoordTower). Every finite game (trivial one-level tower).

**Formalization:** Already done — `GeneralSignTower` + `nash_refining_sequence`.

### Recipe 2: Finite restriction

A finite game with "too many" actions. Some actions are strictly dominated and can be removed, leaving a finite core. The core is a finite game — a trivial tower.

**Formalization:**
```
theorem nash_of_restriction [Fintype I] [∀ i, Fintype (V i)]
    (G : SignGame I V)
    (core : ∀ i, Face (V i))                     -- the compact core
    (h_dom : ∀ i v, v ∉ (core i).1 →
      ∃ w ∈ (core i).1, ∀ σ, G.DevFaceLE i σ (vertex w) (vertex v))
    : ∃ σ, G.IsNash σ
```

This factors through the general `nash_exists` but makes the restriction explicit.

### Recipe 3: Two-axis tower (the main new construction)

For infinite/continuous games. The tower has two axes of refinement:

**Axis 1: Mixture resolution** (already formalized)
- Level k has `2^k + 1` grid points per player
- Embedding doubles the grid, adding midpoints
- Coherence ensures consistency

**Axis 2: Action expansion with convex cost**
- At each level, the action set includes a finite "core" plus a single absorber action representing "everything else"
- The absorber is dominated by the core at cost threshold k
- Expanding the core (increasing k) includes more actions but the new ones are increasingly costly
- The cost structure is convex: cost grows at least as fast as the action space expands

The two axes combine: at level (k, m), we have k levels of mixture resolution and m levels of action expansion. The full tower is the diagonal or some interleaving.

**The key intuition:** the absorber at each level represents a placeholder for "all dominated strategies I haven't bothered to enumerate." The convex cost guarantees that for any bounded-value deviation, there exists a level where the cost of the absorber exceeds the value, so the absorber is dominated. This is the "rising cost eventually overcomes bounded value" principle.

**Formal shape (sketch):**
```
structure CostValueTower (I : Type*) where
  tower : GeneralSignTower I                     -- mixture resolution axis
  cost : (k : ℕ) → (i : I) → V k i → ℕ         -- cost of each action at level k
  value_bound : ℕ                                -- universal bound on value
  cost_absorber : ∀ k i, ∃ a : V k i,           -- the absorber action
    cost k i a ≥ value_bound                     -- its cost exceeds the value bound
  cost_monotone : ∀ k i a,                       -- cost increases with level
    cost k i a ≤ cost (k+1) i (embed k i a)
  core_dominated : ∀ k i a,                      -- high-cost actions are dominated
    cost k i a > value_bound →
    ∃ w, cost k i w ≤ value_bound ∧
    ∀ σ, DevFaceLE i σ (vertex w) (vertex a)
```

### Uncertainties (Layer 3 only)

1. **Interleaving the two axes.** Should the tower be indexed by `ℕ × ℕ` (mixture level, action level) or by a single `ℕ` with some interleaving? Single `ℕ` is simpler for the tower machinery. Interleaving by `k ↦ (k/2, k/2)` or similar.

2. **The absorber's sign structure.** The absorber represents "everything else." What signs does it have? It should be dominated by the core — but its signs against other absorbers are unconstrained (two "everything else" strategies are incomparable). This needs to be consistent with the sign axioms.

3. **Cost as an intrinsic vs extrinsic concept.** Is cost part of the game's preference structure, or a separate bookkeeping device? The sketch above makes it extrinsic (a separate function). It might be cleaner to encode it in the signs: "the absorber is dominated" is just a DevFaceLE statement, with cost being the *proof* that DevFaceLE holds, not separate data.

4. **Convexity of cost.** "Cost grows at least as fast as the action space expands" needs a precise formulation. In the grid setting: as we add midpoints, the cost of each midpoint is at least the average of its neighbors' costs. This is just convexity in the usual sense.

5. **Is the two-axis structure really needed, or is one axis enough?** For games where the action set is already finite (just continuous mixing), one axis (mixture resolution) suffices. The second axis is only needed when the action set itself is infinite. Should clarify when each is needed.

---

## Layer 0: Refactoring Base.lean

**Status: engineering, do first**

Before building Layers 1-3, refactor the existing code to cleanly separate the abstract spec from the concrete finite ordinal implementation.

### Current state

`Base.lean` defines `SignGame`, `Face`, `DevFaceLE`, `IsNash`, `nash_exists` as a monolithic unit. The Nash definition is specific to sign games.

### Target state

- `Game` structure with `IsNash` (the abstract spec) — top of the file or new file
- `SignGame` structure (unchanged)
- `SignGame.toGame : SignGame I V → Game I` construction
- `IsNash` agreement: `G.toGame.IsNash σ ↔ G.IsNash σ` (or definitional)
- `nash_exists` stated for `Game` when `S i = Face (V i)` (or: stated for `SignGame`, with a corollary for `Game`)
- Everything else in `Base.lean` unchanged

This is a small refactor — adding definitions on top, not changing existing code.

---

## Hierarchy summary

```
Game (abstract spec)
  │
  ├── SignGame.toGame : finite ordinal games
  │     │
  │     └── nash_exists : Nash existence for finite games
  │
  ├── CompactGame : tower-based games
  │     │
  │     ├── Pure tower (Recipe 1) — existing GeneralSignTower
  │     │     └── nash_refining_sequence
  │     │
  │     ├── Finite restriction (Recipe 2) — core extraction
  │     │     └── nash_of_restriction
  │     │
  │     └── Two-axis tower (Recipe 3) — mixture + cost expansion
  │           └── cost_value_nash_exists (future)
  │
  └── Cardinal games (total preorder) — VNM instance (article-only)
```

---

## File plan

| File | Contents | Status |
|------|----------|--------|
| `Base.lean` | SignGame, Face, DevFaceLE, nash_exists + new: Game, toGame | Refactor |
| `Refinement.lean` | GeneralSignTower, nash_refining_sequence | Unchanged |
| `SelfSimilarity.lean` | iterEmbed, multiLevelGame, grid children | Unchanged |
| `Invariance.lean` | Ordinal/affine invariance | Unchanged |
| `BilinearExamples.lean` | Concrete tower examples | Unchanged |
| `Compact.lean` | CompactGame, RestrictedGame, restriction lemma | New |
| `CostValue.lean` | CostValueTower, cost_value_nash_exists | New (future) |

---

## Iteration plan

### Round 1: Abstract spec + skeleton
- Add `Game`, `MixtureAlgebra`, `IsNash` to `Base.lean`
- Add `SignGame.toGame` construction
- Prove Nash definition agreement
- Show `Face.mix` is a `MixtureAlgebra`
- Skeleton `Compact.lean` with `RestrictedGame` definition
- Everything with `sorry` where needed — focus on types checking

### Round 2: Restriction lemma
- Prove `nash_of_restriction`: dominated actions can be removed
- Show that any finite game is a (trivial) compact game
- Test: express an existing tower as a compact game
- Test: define an infinite game on ℕ with dominated tail, restrict to finite core

### Round 3: Two-axis tower design
- Draft `CostValueTower` structure
- Resolve absorber sign structure
- Resolve axis interleaving
- Test against the Gaussian-on-circle example (informally)
- Skeleton `CostValue.lean` with types checking

### Round 4: Proofs + integration
- Prove cost-value Nash existence
- Connect to existing towers (show existing towers are cost-value towers with trivial cost)
- Article sections on compact games

Each round touches all layers. The goal is to reduce uncertainty uniformly, not to finish any layer before starting the next.

---

## Resolved questions

1. ~~Total vs partial preorder~~ → **Partial.** Both ordinal and cardinal games are instances.
2. ~~Do we formalize the limit~~ → **No.** Tower-level Nash + compatibility is the theorem.
3. ~~MixtureAlgebra vs SemilatticeSup~~ → **MixtureAlgebra.** Keep it plain; `≤` is game-dependent.
4. ~~Naming: "compact game"~~ → **Keep it.** The analogy to topological compactness is intentional.
5. ~~What goes in Lean vs article~~ → **Game, CompactGame, restriction lemma in Lean.** Cardinal/VNM, limit construction, cost-value sufficient conditions in article (initially).
6. ~~Compatibility axiom~~ → **Not an axiom.** Consequence of construction.

## Open questions

1. **Absorber sign structure.** How to assign signs to the absorber consistently with sign axioms while encoding "dominated by the core."
2. **Axis interleaving.** Single ℕ index vs ℕ × ℕ for the two-axis tower.
3. **Cost convexity formulation.** Precise statement of "cost grows convexly."
4. **When is the second axis needed?** Finite action set → one axis. Infinite action set → two axes. Is there a clean criterion?
