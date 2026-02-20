import SyntheticGameTheory
import SyntheticGameTheory.Precision.Grid

namespace SyntheticGameTheory

-- ================================================================
-- Section 1: Elementary Profiles for 2-player, 2-action games
-- ================================================================

/-- A profile at level k: each of 2 players picks an elementary cell on a 1-simplex. -/
abbrev ElemProfile1 (k : Nat) := Fin 2 → ElemCell1 k

noncomputable instance ElemProfile1.instFintype : Fintype (ElemProfile1 k) := Pi.instFintype

noncomputable instance ElemProfile1.instDecidableEq : DecidableEq (ElemProfile1 k) :=
  inferInstance

-- ================================================================
-- Section 2: Refinement relation
-- ================================================================

/-- A profile σ' at level k+1 refines σ at level k iff each component
    is a sub-cell (appears in the canonical subdivision) of the corresponding
    component at level k. -/
def ElemProfile1.Refines (σ' : ElemProfile1 (k + 1)) (σ : ElemProfile1 k) : Prop :=
  ∀ i, σ' i ∈ (σ i).subcells

/-- Refinement is decidable (subcells is a finite list). -/
instance ElemProfile1.instDecidableRefines (σ' : ElemProfile1 (k + 1)) (σ : ElemProfile1 k) :
    Decidable (σ'.Refines σ) :=
  inferInstanceAs (Decidable (∀ i, σ' i ∈ (σ i).subcells))

-- ================================================================
-- Section 3: Bridge to DSimplex-based theory at k = 0
-- ================================================================

/-- Convert an ElemProfile1 at level 0 to a Profile in the core theory.
    Uses elemCell1ZeroEquiv to transport each component. -/
noncomputable def ElemProfile1.toProfile (σ : ElemProfile1 0) :
    Profile (Fin 2) (fun _ => Fin 2) :=
  fun i => ElemCell1.elemCell1ZeroEquiv (σ i)

/-- Convert a core Profile to an ElemProfile1 at level 0. -/
noncomputable def ElemProfile1.ofProfile (σ : Profile (Fin 2) (fun _ => Fin 2)) :
    ElemProfile1 0 :=
  fun i => ElemCell1.elemCell1ZeroEquiv.symm (σ i)

/-- The equivalence between ElemProfile1 0 and Profile (Fin 2) (fun _ => Fin 2). -/
noncomputable def elemProfile1ZeroEquiv :
    ElemProfile1 0 ≃ Profile (Fin 2) (fun _ => Fin 2) where
  toFun := ElemProfile1.toProfile
  invFun := ElemProfile1.ofProfile
  left_inv := by
    intro σ; ext i
    simp [ElemProfile1.toProfile, ElemProfile1.ofProfile]
  right_inv := by
    intro σ; ext i
    simp [ElemProfile1.toProfile, ElemProfile1.ofProfile]

-- ================================================================
-- Section 4: Grid-point consistency
-- ================================================================

/-- A pair of grid points (one per player) is consistent with an ElemProfile1
    when each grid point belongs to the corresponding cell's grid points. -/
def ElemConsistent (σ : ElemProfile1 k) (p : Fin 2 → GridPoint 1 k) : Prop :=
  ∀ i, p i ∈ (σ i).gridPoints

instance ElemConsistent.instDecidable (σ : ElemProfile1 k) (p : Fin 2 → GridPoint 1 k) :
    Decidable (ElemConsistent σ p) :=
  inferInstanceAs (Decidable (∀ i, p i ∈ (σ i).gridPoints))

-- ================================================================
-- Section 5: Transport lemmas (k=0 bridge properties)
-- ================================================================

private theorem gridPoint1Equiv_eq_zero_iff (q : GridPoint 1 0) :
    q = ElemCell1.gridPt (0 : Fin 2) ↔ GridPoint.gridPoint1Equiv q = (0 : Fin 2) := by
  constructor
  · intro h
    exact congrArg (fun t => (GridPoint.gridPoint1Equiv t : Fin 2)) h
  · intro h
    apply (Function.LeftInverse.injective GridPoint.ofIndex1_toIndex1)
    simpa [ElemCell1.gridPt] using h

private theorem gridPoint1Equiv_eq_one_iff (q : GridPoint 1 0) :
    q = ElemCell1.gridPt (1 : Fin 2) ↔ GridPoint.gridPoint1Equiv q = (1 : Fin 2) := by
  constructor
  · intro h
    exact congrArg (fun t => (GridPoint.gridPoint1Equiv t : Fin 2)) h
  · intro h
    apply (Function.LeftInverse.injective GridPoint.ofIndex1_toIndex1)
    simpa [ElemCell1.gridPt] using h

private theorem gridPoint0_cases (q : GridPoint 1 0) :
    q = ElemCell1.gridPt (0 : Fin 2) ∨ q = ElemCell1.gridPt (1 : Fin 2) := by
  let v : Nat := (GridPoint.toIndex1 q).val
  have hvlt : v < 2 := by
    simp [v]
  have hv : v = 0 ∨ v = 1 := by omega
  rcases hv with hv0 | hv1
  · left
    apply (Function.LeftInverse.injective GridPoint.ofIndex1_toIndex1)
    have hidx : GridPoint.toIndex1 q = (0 : Fin 2) := Fin.ext (by simpa [v] using hv0)
    simpa [ElemCell1.gridPt] using hidx
  · right
    apply (Function.LeftInverse.injective GridPoint.ofIndex1_toIndex1)
    have hidx : GridPoint.toIndex1 q = (1 : Fin 2) := Fin.ext (by simpa [v] using hv1)
    simpa [ElemCell1.gridPt] using hidx

private theorem elemCell_mem_zero_iff (c : ElemCell1 0) (q : GridPoint 1 0) :
    q ∈ c.gridPoints ↔ GridPoint.gridPoint1Equiv q ∈ (ElemCell1.elemCell1ZeroEquiv c).1 := by
  cases c with
  | vertex a =>
      have ha : a = (0 : Fin 2) ∨ a = (1 : Fin 2) := by
        let v : Nat := a.val
        have hvlt : v < 2 := by simp [v]
        have hv : v = 0 ∨ v = 1 := by omega
        rcases hv with hv0 | hv1
        · left
          exact Fin.ext (by simpa [v] using hv0)
        · right
          exact Fin.ext (by simpa [v] using hv1)
      rcases ha with rfl | rfl
      · simp [ElemCell1.gridPoints, ElemCell1.elemCell1ZeroEquiv, ElemCell1.toDSimplex2,
          gridPoint1Equiv_eq_zero_iff q]
      · simp [ElemCell1.gridPoints, ElemCell1.elemCell1ZeroEquiv, ElemCell1.toDSimplex2,
          gridPoint1Equiv_eq_one_iff q]
  | edge _ =>
      constructor
      · intro _
        simp [ElemCell1.elemCell1ZeroEquiv, ElemCell1.toDSimplex2]
      · intro _
        simpa [ElemCell1.gridPoints] using gridPoint0_cases q

/-- At k=0, elem-consistency transports to core Consistent. -/
theorem elemConsistent_zero_iff (σ : ElemProfile1 0) (p : Fin 2 → GridPoint 1 0) :
    ElemConsistent σ p ↔
      Consistent (elemProfile1ZeroEquiv σ)
        (fun i => (GridPoint.gridPoint1Equiv (p i) : Fin 2)) := by
  constructor
  · intro h i
    exact (elemCell_mem_zero_iff (σ i) (p i)).1 (h i)
  · intro h i
    exact (elemCell_mem_zero_iff (σ i) (p i)).2 (h i)

/-- Function.update transports through the equivalence. -/
noncomputable def elemProfile1ZeroEquiv_update (σ : ElemProfile1 0) (i : Fin 2)
    (A : ElemCell1 0) :
    elemProfile1ZeroEquiv (Function.update σ i A) =
      Function.update (elemProfile1ZeroEquiv σ) i (ElemCell1.elemCell1ZeroEquiv A) := by
  ext j
  by_cases hji : j = i
  · subst hji
    simp [ElemProfile1.toProfile, elemProfile1ZeroEquiv]
  · simp [ElemProfile1.toProfile, elemProfile1ZeroEquiv, hji]

-- ================================================================
-- Section 6: Cell subface relation (for deviation ordering)
-- ================================================================

/-- Cell A is a "sub-cell" of B if every grid point of A is also a grid point of B.
    This is the elementary-cell analogue of DSimplex.IsSubface. -/
def ElemCell1.IsSubcell (A B : ElemCell1 k) : Prop :=
  A.gridPoints ⊆ B.gridPoints

instance ElemCell1.instDecidableIsSubcell (A B : ElemCell1 k) :
    Decidable (A.IsSubcell B) :=
  inferInstanceAs (Decidable (A.gridPoints ⊆ B.gridPoints))

/-- At k=0, IsSubcell corresponds to DSimplex.IsSubface under elemCell1ZeroEquiv. -/
theorem ElemCell1.isSubcell_zero_iff (A B : ElemCell1 0) :
    A.IsSubcell B ↔
      DSimplex.IsSubface (ElemCell1.elemCell1ZeroEquiv A)
                         (ElemCell1.elemCell1ZeroEquiv B) := by
  revert A B
  decide

-- ================================================================
-- Section 7: Profile size (for well-foundedness arguments)
-- ================================================================

/-- The total number of grid points across all players' cells.
    Analogue of profileSize in the core theory. -/
noncomputable def elemProfileSize (σ : ElemProfile1 k) : Nat :=
  Finset.univ.sum (fun i => (σ i).gridPoints.card)

private theorem gridPt_injective {k : Nat} :
    Function.Injective (fun j : Fin (2 ^ k + 1) => (ElemCell1.gridPt j : GridPoint 1 k)) := by
  intro j₁ j₂ h
  have h' := congrArg GridPoint.toIndex1 h
  simpa [ElemCell1.gridPt] using h'

private theorem edge_gridPoints_card_two {k : Nat} (j : Fin (2 ^ k)) :
    (ElemCell1.edge j : ElemCell1 k).gridPoints.card = 2 := by
  let j₁ : Fin (2 ^ k + 1) := ⟨j.val, by omega⟩
  let j₂ : Fin (2 ^ k + 1) := ⟨j.val + 1, by omega⟩
  have hne : ElemCell1.gridPt j₁ ≠ ElemCell1.gridPt j₂ := by
    intro hEq
    have hIdx : j₁ = j₂ := by
      exact gridPt_injective (by simpa [ElemCell1.gridPt] using hEq)
    have : j.val = j.val + 1 := by
      simpa [j₁, j₂] using congrArg Fin.val hIdx
    omega
  simp [ElemCell1.gridPoints, j₁, j₂, hne]

private theorem edge_eq_of_gridPoints_eq {k : Nat} {j₁ j₂ : Fin (2 ^ k)}
    (hEq : (ElemCell1.edge j₁ : ElemCell1 k).gridPoints =
      (ElemCell1.edge j₂).gridPoints) : j₁ = j₂ := by
  let i₁ : Fin (2 ^ k + 1) := ⟨j₁.val, by omega⟩
  let i₁' : Fin (2 ^ k + 1) := ⟨j₁.val + 1, by omega⟩
  let i₂ : Fin (2 ^ k + 1) := ⟨j₂.val, by omega⟩
  let i₂' : Fin (2 ^ k + 1) := ⟨j₂.val + 1, by omega⟩
  have hSet : ({i₁, i₁'} : Finset (Fin (2 ^ k + 1))) = ({i₂, i₂'} : Finset (Fin (2 ^ k + 1))) := by
    have hMap := congrArg (Finset.image GridPoint.toIndex1) hEq
    simpa [ElemCell1.gridPoints, ElemCell1.gridPt, i₁, i₁', i₂, i₂'] using hMap
  have hmem₁ : i₁ ∈ ({i₂, i₂'} : Finset (Fin (2 ^ k + 1))) := by
    rw [← hSet]
    simp [i₁]
  have hmem₂ : i₂ ∈ ({i₁, i₁'} : Finset (Fin (2 ^ k + 1))) := by
    rw [hSet]
    simp [i₂]
  have h₁ : i₁ = i₂ ∨ i₁ = i₂' := by simpa using hmem₁
  have h₂ : i₂ = i₁ ∨ i₂ = i₁' := by simpa using hmem₂
  have h₁v : j₁.val = j₂.val ∨ j₁.val = j₂.val + 1 := by
    cases h₁ with
    | inl h12 => left; simpa [i₁, i₂] using congrArg Fin.val h12
    | inr h12 => right; simpa [i₁, i₂'] using congrArg Fin.val h12
  have h₂v : j₂.val = j₁.val ∨ j₂.val = j₁.val + 1 := by
    cases h₂ with
    | inl h21 => left; simpa [i₁, i₂] using congrArg Fin.val h21
    | inr h21 => right; simpa [i₂, i₁'] using congrArg Fin.val h21
  have hv : j₁.val = j₂.val := by omega
  exact Fin.ext hv

private theorem gridPoints_injective {k : Nat} :
    Function.Injective (fun c : ElemCell1 k => c.gridPoints) := by
  intro c₁ c₂ hEq
  cases c₁ with
  | vertex j₁ =>
      cases c₂ with
      | vertex j₂ =>
          have hpt : ElemCell1.gridPt j₁ = ElemCell1.gridPt j₂ := by
            exact Finset.singleton_inj.mp (by simpa [ElemCell1.gridPoints] using hEq)
          have hj : j₁ = j₂ := gridPt_injective hpt
          simp [hj]
      | edge j₂ =>
          have hcard := congrArg Finset.card hEq
          change 1 = (ElemCell1.edge j₂ : ElemCell1 k).gridPoints.card at hcard
          rw [edge_gridPoints_card_two j₂] at hcard
          omega
  | edge j₁ =>
      cases c₂ with
      | vertex j₂ =>
          have hcard := congrArg Finset.card hEq
          change (ElemCell1.edge j₁ : ElemCell1 k).gridPoints.card = 1 at hcard
          rw [edge_gridPoints_card_two j₁] at hcard
          omega
      | edge j₂ =>
          have hj : j₁ = j₂ := edge_eq_of_gridPoints_eq hEq
          simp [hj]

/-- Replacing a cell with a strict sub-cell decreases profile size. -/
theorem elemProfileSize_decreases {σ : ElemProfile1 k} {i : Fin 2} {A : ElemCell1 k}
    (hsub : A.IsSubcell (σ i)) (hne : A ≠ σ i) :
    elemProfileSize (Function.update σ i A) < elemProfileSize σ := by
  have hgrid_ne : A.gridPoints ≠ (σ i).gridPoints := by
    intro hEq
    apply hne
    exact gridPoints_injective hEq
  have hcard : A.gridPoints.card < (σ i).gridPoints.card := by
    exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hgrid_ne⟩)
  unfold elemProfileSize
  conv_lhs =>
    rw [← Finset.sum_erase_add Finset.univ
      (fun j => ((σ[i ↦ A]) j).gridPoints.card) (Finset.mem_univ i)]
  conv_rhs =>
    rw [← Finset.sum_erase_add Finset.univ
      (fun j => (σ j).gridPoints.card) (Finset.mem_univ i)]
  have h_at_i : ((σ[i ↦ A]) i).gridPoints.card = A.gridPoints.card := by
    show (Function.update σ i A i).gridPoints.card = A.gridPoints.card
    unfold Function.update
    split_ifs
    · rfl
    · contradiction
  have h_elsewhere :
      ∀ j ∈ Finset.univ.erase i, ((σ[i ↦ A]) j).gridPoints.card = (σ j).gridPoints.card := by
    intro j hj
    have hjne : j ≠ i := Finset.mem_erase.mp hj |>.1
    show (Function.update σ i A j).gridPoints.card = (σ j).gridPoints.card
    unfold Function.update
    split_ifs with h
    · subst h; contradiction
    · rfl
  rw [h_at_i]
  rw [Finset.sum_congr rfl h_elsewhere]
  omega

-- ================================================================
-- Section 8: Embedding cells across levels
-- ================================================================

/-- Embed a grid point from level k to level k+1 (coordinate doubling).
    This is just GridPoint.embed specialized to n=1. -/
abbrev embedGridPoint1 (p : GridPoint 1 k) : GridPoint 1 (k + 1) := GridPoint.embed p

private theorem embed_gridPt_eq {k : Nat} (j : Fin (2 ^ k + 1)) :
    GridPoint.embed (ElemCell1.gridPt j) = ElemCell1.gridPt (ElemCell1.embedIndex j) := by
  apply (Function.LeftInverse.injective GridPoint.ofIndex1_toIndex1)
  have hL : GridPoint.toIndex1 (GridPoint.embed (ElemCell1.gridPt j)) = ElemCell1.embedIndex j := by
    ext
    simp [ElemCell1.gridPt, ElemCell1.embedIndex, GridPoint.toIndex1, GridPoint.embed,
      GridPoint.ofIndex1]
  simpa [ElemCell1.gridPt] using hL

/-- The embedded grid points of a cell at level k are a subset of
    the grid points of its subdivision at level k+1. -/
theorem ElemCell1.embed_gridPoints_subset_subcells (c : ElemCell1 k) :
    c.gridPoints.image GridPoint.embed ⊆
      (c.subcells.map ElemCell1.gridPoints).foldl (· ∪ ·) ∅ := by
  intro x hx
  cases c with
  | vertex j =>
      simp [ElemCell1.subcells, ElemCell1.gridPoints] at hx ⊢
      rcases hx with rfl
      simp [embed_gridPt_eq]
  | edge j =>
      simp [ElemCell1.subcells, ElemCell1.gridPoints] at hx ⊢
      rcases hx with hx | hx
      · right
        right
        left
        rw [hx]
        have hidx : ElemCell1.embedIndex (⟨↑j, by omega⟩ : Fin (2 ^ k + 1)) =
            (⟨2 * ↑j, by omega⟩ : Fin (2 ^ (k + 1) + 1)) := by
          ext
          simp [ElemCell1.embedIndex]
        simp [embed_gridPt_eq, hidx]
      · left
        rw [hx]
        have hidx : ElemCell1.embedIndex (⟨↑j + 1, by omega⟩ : Fin (2 ^ k + 1)) =
            (⟨2 * ↑j + 1 + 1, by omega⟩ : Fin (2 ^ (k + 1) + 1)) := by
          ext
          simp [ElemCell1.embedIndex]
          omega
        simp [embed_gridPt_eq, hidx]

-- ================================================================
-- Section 9: Maximal and vertex profiles
-- ================================================================

/-- The maximal profile at level k: each player plays the full edge [0, 2^k].
    Only defined when k > 0 (at k=0, the full edge is the only edge). -/
def maximalElemProfile1 : ElemProfile1 0 :=
  fun _ => ElemCell1.edge ⟨0, by omega⟩

/-- At k=0, the maximal elem profile corresponds to the maximal profile
    in the core theory. -/
theorem maximalElemProfile1_toProfile :
    elemProfile1ZeroEquiv maximalElemProfile1 =
      (fun _ => (⟨Finset.univ, Finset.univ_nonempty⟩ : DSimplex (Fin 2))) := by
  rfl

-- ================================================================
-- Section 10: Vertex profiles at level 0
-- ================================================================

/-- A vertex profile: each player plays a specific vertex (pure strategy). -/
def vertexElemProfile1 (p : Fin 2 → Fin 2) : ElemProfile1 0 :=
  fun i => ElemCell1.vertex ⟨(p i).val, by have := (p i).isLt; omega⟩

/-- A vertex profile at k=0 corresponds to a vertex (singleton) DSimplex profile. -/
theorem vertexElemProfile1_toProfile (p : Fin 2 → Fin 2) :
    elemProfile1ZeroEquiv (vertexElemProfile1 p) =
      (fun i => DSimplex.vertex (p i)) := by
  ext i
  have hp : p i = (0 : Fin 2) ∨ p i = (1 : Fin 2) := by
    have hlt := (p i).isLt
    omega
  cases hp with
  | inl hp0 =>
      simp [vertexElemProfile1, elemProfile1ZeroEquiv, ElemProfile1.toProfile,
        ElemCell1.elemCell1ZeroEquiv, ElemCell1.toDSimplex2, hp0]
  | inr hp1 =>
      simp [vertexElemProfile1, elemProfile1ZeroEquiv, ElemProfile1.toProfile,
        ElemCell1.elemCell1ZeroEquiv, ElemCell1.toDSimplex2, hp1]

-- ================================================================
-- Section 11: Refinement chains
-- ================================================================

/-- A refinement chain from level 0 to level k: a sequence of profiles
    where each refines the previous. -/
def RefinementChain : (k : Nat) → Type
  | 0 => ElemProfile1 0
  | k + 1 => (RefinementChain k) × ElemProfile1 (k + 1)

/-- Extract the profile at the tip of a refinement chain. -/
def RefinementChain.tip : {k : Nat} → RefinementChain k → ElemProfile1 k
  | 0, σ => σ
  | _ + 1, ⟨_, σ'⟩ => σ'

/-- A refinement chain is valid if each level refines the previous. -/
def RefinementChain.IsValid : {k : Nat} → RefinementChain k → Prop
  | 0, _ => True
  | _ + 1, ⟨chain, σ'⟩ => chain.IsValid ∧ σ'.Refines chain.tip

end SyntheticGameTheory
