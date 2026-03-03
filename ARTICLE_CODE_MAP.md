# Article Outline → Code Map

Maps each paragraph/claim in the pedagogical article to specific Lean code.
All files are in `SyntheticGameTheory/`.

---

## Part 1: The theory

### Basic definitions

**"A game has a finite number of players, N. Each player has a finite set of actions V_i"**
- `Base.lean:149-150` — `PureProfile`, `Profile`
```lean
abbrev PureProfile := ∀ i : I, V i
abbrev Profile := ∀ i : I, Face (V i)
```

**"In this version we just assume players have a preference ordering... encoded by a sign function"**
- `Base.lean:159-165` — `SignGame` structure
```lean
structure SignGame where
  sign : (i : I) → PureProfile I V → V i → V i → Sign
  sign_refl : ∀ i p a, sign i p a a = .zero
  sign_antisym : ∀ i p a b, sign i p a b = (sign i p b a).flip
  sign_trans : ∀ i p a b c, (sign i p a b).nonneg → (sign i p b c).nonneg →
    (sign i p a c).nonneg
  sign_irrel : ∀ i p q a b, (∀ j, j ≠ i → p j = q j) → sign i p a b = sign i q a b
```

**"Here's the Prisoner's Dilemma"**
- `Base.lean:516-522` — `genPD`, `genPD_nash_DD`, `genPD_not_nash_CC`
- `Base.lean:632-647` — `genPD_unique_pureNash` (uniqueness of pure Nash)

**"We define a Nash equilibrium as a profile in which no player has a strict unilateral deviation"**
- `Base.lean:225-230` — `StrictDev`, `IsNash`
```lean
def StrictDev (i : I) (σ : Profile I V) (A : Face (V i)) : Prop :=
  G.DevFaceLE i σ A (σ i) ∧ ¬G.DevFaceLE i σ (σ i) A

def IsNash (σ : Profile I V) : Prop :=
  ∀ (i : I) (A : Face (V i)), ¬G.StrictDev i σ A
```

**"There might be no Nash equilibrium among pure profiles"**
- `Base.lean:524-551` — `genMP`, `genMP_no_pureNash`

**"a mixed strategy is just a formal combination of pure strategies... mix(a,b)"**
- `Base.lean:117` — `Face V` (nonempty finset = discrete simplex element)
```lean
def Face (V : Type*) [DecidableEq V] := { S : Finset V // S.Nonempty }
```
- `Base.lean:129-141` — `Face.mix` (union), `mix_comm`, `mix_idem`, `mix_assoc`
```lean
def mix (A B : Face V) : Face V :=
  ⟨A.1 ∪ B.1, A.2.mono Finset.subset_union_left⟩
```

**"profiles are the products of individual faces"**
- `Base.lean:150` — `Profile := ∀ i : I, Face (V i)`

**"Two faces A, B satisfy A ≤ B... DevFaceLE"**
- `Base.lean:181-183` — `DevFaceLE`
```lean
def DevFaceLE (i : I) (σ : Profile I V) (A B : Face (V i)) : Prop :=
  ∀ a ∈ A.1, ∀ p : PureProfile I V,
    (∀ j, j ≠ i → p j ∈ (σ j).1) → ∀ b ∈ B.1, (G.sign i p a b).nonneg
```

**"This order can be partial... if two faces contain actions that strictly dominate each other"**
- `Base.lean:675-694` — `genMP_partial_order`
```lean
theorem genMP_partial_order :
    let σ : Profile (Fin 2) (fun _ : Fin 2 => Bool) := fun _ => Face.full
    ¬genMP.DevFaceLE 0 σ (Face.vertex true) (Face.vertex false) ∧
    ¬genMP.DevFaceLE 0 σ (Face.vertex false) (Face.vertex true)
```

**"sign_irrel: we are forgetting information about which exact profile we are in"**
- `Base.lean:165` — `sign_irrel` axiom

**"In the Matching Pennies example, the only Nash equilibrium is fully mixed"**
- `Base.lean:524-551` — `genMP_no_pureNash` (no pure Nash)
- `Base.lean:649-672` — `genMP_mixed_nash` (fully mixed IS Nash)
```lean
theorem genMP_mixed_nash : genMP.IsNash (fun _ : Fin 2 => Face.full (V := Bool))
```

### Existence of Nash equilibria

**"OutsideDominated: every included action dominates every excluded action"**
- `Base.lean:237-239` — `OutsideDominated`
```lean
def OutsideDominated (i : I) (σ : Profile I V) : Prop :=
  ∀ v, v ∉ (σ i).1 → ∀ w, w ∈ (σ i).1 →
    G.DevFaceLE i σ (Face.vertex w) (Face.vertex v)
```

**"Start from the full profile"**
- `Base.lean:245-248` — `OutsideDominated_maximal` (full profile is vacuously OD)

**"Restrict deviations to subfaces"**
- `Base.lean:315-335` — `exists_restrictingStrictDev`

**"Profile size decreases"**
- `Base.lean:342-358` — `profileSize_decreases`
```lean
theorem profileSize_decreases [Fintype I] {i : I} {σ : Profile I V} {A : Face (V i)}
    (hsub : Face.IsSubface A (σ i)) (hne : A ≠ σ i) :
    profileSize (Function.update σ i A) < profileSize σ
```

**"The main descent loop"**
- `Base.lean:364-378` — `nash_exists_aux` (the algorithm)
```lean
private theorem nash_exists_aux [Fintype I]
    (σ : Profile I V)
    (h_od : ∀ i, G.OutsideDominated i σ) :
    ∃ τ, G.IsNash τ := by
  by_cases h : G.IsNash σ
  · exact ⟨σ, h⟩
  · -- find deviation, restrict, recurse
    ...
  termination_by profileSize σ
```

**"Nash equilibrium exists"**
- `Base.lean:380-382` — `nash_exists`
```lean
theorem nash_exists [Fintype I] [∀ i, Fintype (V i)] [∀ i, Nonempty (V i)] :
    ∃ σ, G.IsNash σ
```

**"OD and subface tracking preserved"**
- `Base.lean:256-276` — `OutsideDominated_preserved` (same player)
- `Base.lean:279-291` — `OutsideDominated_preserved_other` (different player)
- `Base.lean:388-414` — `nash_exists_sub_OD` (full tracking)

### Superrationality

**"Pure Nash: no player can improve by switching action"**
- `Base.lean:452-453` — `IsPureNash`
```lean
def IsPureNash (p : PureProfile I V) : Prop :=
  ∀ (i : I) (v : V i), (G.sign i p (p i) v).nonneg
```

*No code for Pareto/superrationality currently in the repo. Verbal claims only.*

---

## Part 2: Behind the scenes

### Refinement

**"Define level k games. A tower of sign games at increasing precision"**
- `Refinement.lean:240-283` — `GeneralSignTower` structure
  - `V : ℕ → I → Type*` (action types per level per player)
  - `game : (k : ℕ) → SignGame I (V k)` (game at each level)
  - `embed : ∀ k i, V k i → V (k+1) i` (embedding)
  - `coherent` (sign preservation under embedding)
  - `playerConvex_left/right`, `opponentConvex` (convexity axioms)
  - `fine_between_embedded_at` (spanning)

**"A level k+1 game coarsens to a level k game"**
- `Refinement.lean:253-255` — `coherent` field
```lean
coherent : ∀ k i (p : PureProfile I (V k)) (a b : V k i),
    (game (k+1)).sign i (embedPureProfile (embed k) p) (embed k i a) (embed k i b)
    = (game k).sign i p a b
```

**"Grid: level k has 2^k + 1 points"**
- `Refinement.lean:128-131` — `gridSize`, `edgeCount`
- `Refinement.lean:138-139` — `gridEmbed` (j ↦ 2j)

**"Define level-k signs generated by a cardinal payoff"**
- `BilinearExamples.lean:44-59` — `bilinearSignGame`
```lean
def bilinearSignGame (n : ℕ) (oppSign₀ oppSign₁ : Fin n → Sign) :
    SignGame (Fin 2) (fun _ : Fin 2 => Fin n)
-- sign(i, p, a, b) = mul(cmpSign(b, a), oppSign_i(p(1-i)))
```

**"Affine transformations of cardinal payoffs produce the same signs"**
- `Invariance.lean:55-66` — `ofPayoffs_strictMono_invariant` (level-0 ordinal invariance)
```lean
theorem ofPayoffs_strictMono_invariant [Fintype I]
    (u : (i : I) → (∀ j, V j) → Int)
    (f : (i : I) → Int → Int) (hf : ∀ i, StrictMono (f i)) :
    SignGame.ofPayoffs (fun i q => f i (u i q)) = SignGame.ofPayoffs u
```
- `Invariance.lean:137-147` — `affine_preserves_oppSign` (positive scaling preserves tower signs)
- `Invariance.lean:166-172` — `counterexample_level2` (non-affine g(x)=x³ breaks level-2 signs)
- `Invariance.lean:174-179` — `signs_agree_level0` (same non-affine transform preserves level-0)
- `Invariance.lean:108-120` — `pd_same_sign_game` (PD payoffs (3,0,5,1) and (7,1,11,3) give same game)

**"Choosing sign-data is equivalent to choosing a refinement of Nash profiles"**
- `Refinement.lean:641-668` — `nash_refining_sequence`
```lean
theorem nash_refining_sequence (k : ℕ) :
    ∃ σ : Profile I (T.V k),
      (T.game k).IsNash σ ∧
      (∀ i, (T.game k).OutsideDominated i σ) ∧
      T.IsConvexClosed k σ
```
- `Refinement.lean:676-700` — `nash_at_next_level_refines`

**"OD transfer: the key technical result"**
- `Refinement.lean:561-607` — `OD_embed_convClosure`

### Self-similarity

**"Iterated embedding from level k to level k+n"**
- `SelfSimilarity.lean:34-37` — `iterEmbed`
```lean
def iterEmbed (T : GeneralSignTower I) (k n : ℕ) (i : I) : T.V k i → T.V (k + n) i :=
  match n with
  | 0 => id
  | n + 1 => T.embed (k + n) i ∘ T.iterEmbed k n i
```

**"Signs preserved along the tree path"**
- `SelfSimilarity.lean:70-85` — `coherent_iterEmbed`
```lean
theorem coherent_iterEmbed (T : GeneralSignTower I) (k n : ℕ) (i : I)
    (p : PureProfile I (T.V k)) (a b : T.V k i) :
    (T.game (k + n)).sign i
      (fun j => T.iterEmbed k n j (p j))
      (T.iterEmbed k n i a) (T.iterEmbed k n i b) =
    (T.game k).sign i p a b
```

**"Tree branching: left and right children"**
- `SelfSimilarity.lean:250-256` — `leftChild`, `rightChild`
```lean
def leftChild (k : ℕ) (j : Fin (gridSize k)) : Fin (gridSize (k + 1)) :=
  ⟨j.val, by grid_omega⟩

def rightChild (k : ℕ) (j : Fin (gridSize k)) : Fin (gridSize (k + 1)) :=
  ⟨j.val + 2 ^ k, by grid_omega⟩
```
- `SelfSimilarity.lean:311-313` — `boundary_shared`
```lean
theorem boundary_shared (k : ℕ) :
    leftChild k ⟨2 ^ k, _⟩ = rightChild k ⟨0, _⟩
```

**"Each k-subtree can be seen as a level k game"**
- `SelfSimilarity.lean:111-118` — `restrictGame`
```lean
def restrictGame (G : SignGame I V) (f : ∀ i, W i → V i) : SignGame I W where
  sign i p a b := G.sign i (fun j => f j (p j)) (f i a) (f i b)
  ...
```
- `SelfSimilarity.lean:129-134` — `restrictGame_iterEmbed_eq`

**"Unmixing: convex closure absorbs betweenness"**
- `Refinement.lean:46-51` — `convClosure`
- `Refinement.lean:100-107` — `convClosure_of_convex` (already-convex faces are fixed)

**"Per-player independence: different players can be at different resolution levels"**
- `SelfSimilarity.lean:156-161` — `multiLevelGame`
```lean
noncomputable def multiLevelGame (T : GeneralSignTower I) (κ : I → ℕ) :
    SignGame I (fun i => T.V (κ i) i)
```
- `SelfSimilarity.lean:171-175` — `multiLevelGame_uniform_sign` (uniform = standard)
- `SelfSimilarity.lean:178-180` — `multiLevelGame_nash_exists`

**"Level 0 games determine everything else"**
- `SelfSimilarity.lean:199-207` — `multiLevelGame_coherent_embed`

---

## Concrete tower examples (supplementary)

**"Prisoner's Dilemma tower"** — `BilinearExamples.lean`, `genPdTower`
**"Matching Pennies tower"** — `BilinearExamples.lean`, `genMpTower`
**"Symmetric Coordination tower"** — `BilinearExamples.lean`, `genSymCoordTower`
**"Battle of the Sexes tower"** — `BilinearExamples.lean`, `genBosTower`

**"3-player example"** — `Base.lean:578-617` — `coordGame3`

---

## Coverage summary

| Article section | Code coverage | Notes |
|----------------|--------------|-------|
| Basic definitions | Complete | `SignGame`, `Face`, `Profile`, `PureProfile` |
| PD example | Complete | `genPD`, unique Nash, deviation graph |
| MP no pure Nash | Complete | `genMP_no_pureNash` |
| Mixed strategies (Face) | Complete | `Face`, `Face.mix`, `Face.vertex`, `Face.full` |
| DevFaceLE partial order | Complete | `DevFaceLE`, `genMP_partial_order` |
| sign_irrel | Complete | Axiom in `SignGame` |
| MP mixed Nash | Complete | `genMP_mixed_nash` |
| Nash existence algorithm | Complete | `nash_exists_aux`, `nash_exists` |
| OD invariant | Complete | `OutsideDominated_*` |
| Profile size descent | Complete | `profileSize_decreases` |
| Superrationality/Pareto | No code | Verbal only in article |
| Refinement tower | Complete | `GeneralSignTower`, `nash_refining_sequence` |
| Grid arithmetic | Complete | `gridSize`, `gridEmbed` |
| Bilinear sign games | Complete | `bilinearSignGame` |
| Affine invariance | Complete | `Invariance.lean`: ordinal + affine + counterexample |
| Self-similarity | Complete | `iterEmbed`, `coherent_iterEmbed` |
| Tree structure | Complete | `leftChild`, `rightChild`, `boundary_shared` |
| Restriction/unmixing | Complete | `restrictGame`, `convClosure` |
| Multi-level game | Complete | `multiLevelGame`, `multiLevelGame_nash_exists` |
| Concrete tower examples | Complete | PD, MP, SymCoord, BoS towers |
