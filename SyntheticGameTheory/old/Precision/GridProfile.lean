import SyntheticGameTheory.Basic
import SyntheticGameTheory.Precision.Grid

namespace SyntheticGameTheory

-- ================================================================
-- Section 1: Elementary Cell Profiles (product of cells)
-- ================================================================

/-- A cell profile at level k: each of 2 players picks an elementary cell. -/
abbrev CellProfile1 (k : Nat) := Fin 2 → ElemCell1 k

noncomputable instance CellProfile1.instFintype : Fintype (CellProfile1 k) := Pi.instFintype

noncomputable instance CellProfile1.instDecidableEq : DecidableEq (CellProfile1 k) :=
  inferInstance

-- ================================================================
-- Section 2: Grid Point Profiles (product of grid points = pure profiles)
-- ================================================================

/-- A grid profile at level k: each of 2 players picks a grid point.
    This is the "pure strategy" notion at precision k. -/
abbrev GridProfile1 (k : Nat) := Fin 2 → GridPoint 1 k

noncomputable instance GridProfile1.instFintype : Fintype (GridProfile1 k) := Pi.instFintype

noncomputable instance GridProfile1.instDecidableEq : DecidableEq (GridProfile1 k) :=
  inferInstance

/-- Every grid profile determines a cell profile (each grid point is a vertex cell). -/
def GridProfile1.toCellProfile (p : GridProfile1 k) : CellProfile1 k :=
  fun i => ElemCell1.vertex (GridPoint.toIndex1 (p i))

/-- A grid profile is consistent with a cell profile when each grid point
    belongs to the corresponding cell's grid points. -/
def GridProfile1.ConsistentWith (p : GridProfile1 k) (σ : CellProfile1 k) : Prop :=
  ∀ i, p i ∈ (σ i).gridPoints

instance GridProfile1.instDecidableConsistentWith (p : GridProfile1 k) (σ : CellProfile1 k) :
    Decidable (p.ConsistentWith σ) :=
  inferInstanceAs (Decidable (∀ i, p i ∈ (σ i).gridPoints))

-- ================================================================
-- Section 3: Refinement relation
-- ================================================================

/-- A cell profile σ' at level k+1 refines σ at level k iff each component
    is a sub-cell (appears in the canonical subdivision) of the corresponding
    component at level k. -/
def CellProfile1.Refines (σ' : CellProfile1 (k + 1)) (σ : CellProfile1 k) : Prop :=
  ∀ i, σ' i ∈ (σ i).subcells

instance CellProfile1.instDecidableRefines (σ' : CellProfile1 (k + 1)) (σ : CellProfile1 k) :
    Decidable (σ'.Refines σ) :=
  inferInstanceAs (Decidable (∀ i, σ' i ∈ (σ i).subcells))

-- ================================================================
-- Section 4: Bridge to DSimplex-based theory at k = 0
-- ================================================================

/-- Convert a CellProfile1 at level 0 to a Profile in the core theory. -/
noncomputable def CellProfile1.toProfile (σ : CellProfile1 0) :
    Profile (Fin 2) (fun _ => Fin 2) :=
  fun i => ElemCell1.elemCell1ZeroEquiv (σ i)

/-- Convert a core Profile to a CellProfile1 at level 0. -/
noncomputable def CellProfile1.ofProfile (σ : Profile (Fin 2) (fun _ => Fin 2)) :
    CellProfile1 0 :=
  fun i => ElemCell1.elemCell1ZeroEquiv.symm (σ i)

/-- The equivalence between CellProfile1 0 and Profile (Fin 2) (fun _ => Fin 2). -/
noncomputable def cellProfile1ZeroEquiv :
    CellProfile1 0 ≃ Profile (Fin 2) (fun _ => Fin 2) where
  toFun := CellProfile1.toProfile
  invFun := CellProfile1.ofProfile
  left_inv := by
    intro σ; ext i
    simp [CellProfile1.toProfile, CellProfile1.ofProfile]
  right_inv := by
    intro σ; ext i
    simp [CellProfile1.toProfile, CellProfile1.ofProfile]

/-- Convert a GridProfile1 at level 0 to a PureProfile in the core theory. -/
def GridProfile1.toPureProfile (p : GridProfile1 0) :
    PureProfile (Fin 2) (fun _ => Fin 2) :=
  fun i => GridPoint.gridPoint1Equiv (p i)

/-- Convert a core PureProfile to a GridProfile1 at level 0. -/
def GridProfile1.ofPureProfile (p : PureProfile (Fin 2) (fun _ => Fin 2)) :
    GridProfile1 0 :=
  fun i => GridPoint.gridPoint1Equiv.symm (p i)

/-- The equivalence between GridProfile1 0 and PureProfile (Fin 2) (fun _ => Fin 2). -/
def gridProfile1ZeroEquiv :
    GridProfile1 0 ≃ PureProfile (Fin 2) (fun _ => Fin 2) where
  toFun := GridProfile1.toPureProfile
  invFun := GridProfile1.ofPureProfile
  left_inv := by
    intro p; ext i
    simp [GridProfile1.toPureProfile, GridProfile1.ofPureProfile]
  right_inv := by
    intro p; ext i
    simp [GridProfile1.toPureProfile, GridProfile1.ofPureProfile,
      GridPoint.gridPoint1Equiv]

-- ================================================================
-- Section 5: Utility lemmas for k=0 grid points
-- ================================================================

theorem gridPoint0_cases (q : GridPoint 1 0) :
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

-- ================================================================
-- Section 6: Refinement chains
-- ================================================================

/-- A refinement chain from level 0 to level k: a sequence of cell profiles
    where each refines the previous. -/
def RefinementChain : (k : Nat) → Type
  | 0 => CellProfile1 0
  | k + 1 => (RefinementChain k) × CellProfile1 (k + 1)

/-- Extract the profile at the tip of a refinement chain. -/
def RefinementChain.tip : {k : Nat} → RefinementChain k → CellProfile1 k
  | 0, σ => σ
  | _ + 1, ⟨_, σ'⟩ => σ'

/-- A refinement chain is valid if each level refines the previous. -/
def RefinementChain.IsValid : {k : Nat} → RefinementChain k → Prop
  | 0, _ => True
  | _ + 1, ⟨chain, σ'⟩ => chain.IsValid ∧ σ'.Refines chain.tip

end SyntheticGameTheory
