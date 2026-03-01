import SyntheticGameTheory.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace SyntheticGameTheory

-- ================================================================
-- Section 1: Dyadic Grid Points on the Standard Simplex
-- ================================================================

/-- A dyadic grid point of the n-simplex at precision k.
    Barycentric coordinates: n+1 natural numbers summing to 2^k. -/
structure GridPoint (n : Nat) (k : Nat) where
  coords : Fin (n + 1) → Nat
  sum_eq : Finset.univ.sum coords = 2 ^ k

namespace GridPoint

variable {n k : Nat}

@[ext]
theorem ext {x y : GridPoint n k} (h : x.coords = y.coords) : x = y := by
  cases x; cases y; congr

instance instDecidableEq : DecidableEq (GridPoint n k) := by
  intro x y
  have : Decidable (x.coords = y.coords) := inferInstance
  exact decidable_of_iff (x.coords = y.coords)
    ⟨fun h => ext h, fun h => congrArg coords h⟩

/-- Each coordinate of a grid point is at most 2^k. -/
theorem coord_le (p : GridPoint n k) (i : Fin (n + 1)) : p.coords i ≤ 2 ^ k := by
  calc p.coords i
      ≤ Finset.univ.sum p.coords :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    _ = 2 ^ k := p.sum_eq

noncomputable instance instFintype : Fintype (GridPoint n k) := by
  classical
  let S := { f : Fin (n + 1) → Fin (2 ^ k + 1) //
      Finset.univ.sum (fun i => (f i).val) = 2 ^ k }
  apply Fintype.ofSurjective (α := S)
    (fun ⟨f, hf⟩ => ⟨fun i => (f i).val, by simpa using hf⟩)
  intro ⟨g, hg⟩
  have hle : ∀ i, g i < 2 ^ k + 1 := fun i => by
    have : g i ≤ Finset.univ.sum g :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  exact ⟨⟨fun i => ⟨g i, hle i⟩, by simpa⟩, by ext1; ext; simp⟩

instance instNonempty : Nonempty (GridPoint n k) :=
  ⟨⟨fun i => if i = 0 then 2 ^ k else 0, by simp [Finset.sum_ite_eq']⟩⟩

-- ----------------------------------------------------------------
-- Vertices at precision 0
-- ----------------------------------------------------------------

/-- Standard basis vector e_j: coordinate j is 2^k, all others 0. -/
def basisVec (n : Nat) (k : Nat) (j : Fin (n + 1)) : GridPoint n k where
  coords := fun i => if i = j then 2 ^ k else 0
  sum_eq := by simp [Finset.sum_ite_eq']

/-- Standard basis vector at precision 0. -/
abbrev vertex (n : Nat) (j : Fin (n + 1)) : GridPoint n 0 := basisVec n 0 j

@[simp]
theorem vertex_coords (j i : Fin (n + 1)) :
    (vertex n j).coords i = if i = j then 1 else 0 := by
  simp [vertex, basisVec]

-- ----------------------------------------------------------------
-- Embedding: level k → level k+1 via coordinate doubling
-- ----------------------------------------------------------------

/-- Embed a level-k grid point into level-(k+1) by doubling all coordinates. -/
def embed (p : GridPoint n k) : GridPoint n (k + 1) where
  coords := fun i => 2 * p.coords i
  sum_eq := by rw [← Finset.mul_sum, p.sum_eq, Nat.pow_succ, Nat.mul_comm]

@[simp]
theorem embed_coords (p : GridPoint n k) (i : Fin (n + 1)) :
    (embed p).coords i = 2 * p.coords i := rfl

theorem embed_injective : Function.Injective (embed (n := n) (k := k)) := by
  intro x y h; ext i
  have : (embed x).coords i = (embed y).coords i := congrFun (congrArg coords h) i
  simp at this; omega

-- ----------------------------------------------------------------
-- Adjacency and midpoints
-- ----------------------------------------------------------------

/-- Two grid points are adjacent if they differ by +1 in one coordinate
    and -1 in another, with all others equal. -/
def Adjacent (x y : GridPoint n k) : Prop :=
  ∃ (a b : Fin (n + 1)), a ≠ b ∧
    x.coords a + 1 = y.coords a ∧
    y.coords b + 1 = x.coords b ∧
    ∀ c, c ≠ a → c ≠ b → x.coords c = y.coords c

/-- The componentwise sum of two level-k grid points is a level-(k+1) grid point. -/
def midpointOf (x y : GridPoint n k) : GridPoint n (k + 1) where
  coords := fun i => x.coords i + y.coords i
  sum_eq := by
    have := Finset.sum_add_distrib (f := x.coords) (g := y.coords) (s := Finset.univ)
    rw [this, x.sum_eq, y.sum_eq]; omega

@[simp]
theorem midpointOf_coords (x y : GridPoint n k) (i : Fin (n + 1)) :
    (midpointOf x y).coords i = x.coords i + y.coords i := rfl

end GridPoint

-- ================================================================
-- Section 2: Specialization to n = 1 (2-action players)
-- ================================================================

namespace GridPoint

variable {k : Nat}

/-- Convert a Fin index to a GridPoint on the 1-simplex. -/
def ofIndex1 (j : Fin (2 ^ k + 1)) : GridPoint 1 k where
  coords := fun i => if i = 0 then j.val else 2 ^ k - j.val
  sum_eq := by rw [Fin.sum_univ_two]; simp; omega

/-- Extract the first coordinate as a Fin index. -/
def toIndex1 (p : GridPoint 1 k) : Fin (2 ^ k + 1) :=
  ⟨p.coords 0, by have := coord_le p 0; omega⟩

@[simp] theorem toIndex1_ofIndex1 (j : Fin (2 ^ k + 1)) :
    toIndex1 (ofIndex1 j) = j := by
  ext; simp [toIndex1, ofIndex1]

@[simp] theorem ofIndex1_toIndex1 (p : GridPoint 1 k) :
    ofIndex1 (toIndex1 p) = p := by
  ext ⟨i, hi⟩
  simp [ofIndex1, toIndex1]
  have h1 : p.coords 0 + p.coords 1 = 2 ^ k := by
    rw [← Fin.sum_univ_two]; exact p.sum_eq
  match i with
  | 0 => simp
  | 1 => simp; omega

/-- GridPoint 1 k is equivalent to Fin (2^k + 1). -/
def gridPoint1Equiv : GridPoint 1 k ≃ Fin (2 ^ k + 1) where
  toFun := toIndex1
  invFun := ofIndex1
  left_inv := ofIndex1_toIndex1
  right_inv := toIndex1_ofIndex1

private theorem fin2_cases (c : Fin (1 + 1)) : c = 0 ∨ c = 1 := by
  match c with | ⟨0, _⟩ => left; rfl | ⟨1, _⟩ => right; rfl

/-- For n=1, adjacency means the first coordinates differ by exactly 1. -/
theorem adjacent1_iff (x y : GridPoint 1 k) :
    Adjacent x y ↔ (x.coords 0 + 1 = y.coords 0 ∨ y.coords 0 + 1 = x.coords 0) := by
  have hx : x.coords 0 + x.coords 1 = 2 ^ k := by
    rw [← Fin.sum_univ_two]; exact x.sum_eq
  have hy : y.coords 0 + y.coords 1 = 2 ^ k := by
    rw [← Fin.sum_univ_two]; exact y.sum_eq
  constructor
  · rintro ⟨a, b, hab, ha, hb, hc⟩
    match a, b with
    | ⟨0, _⟩, ⟨0, _⟩ => exact absurd rfl hab
    | ⟨0, _⟩, ⟨1, _⟩ => left; exact ha
    | ⟨1, _⟩, ⟨0, _⟩ => right; exact hb
    | ⟨1, _⟩, ⟨1, _⟩ => exact absurd rfl hab
  · rintro (h | h)
    · refine ⟨0, 1, Fin.zero_ne_one, h, by omega, ?_⟩
      intro c hc0 hc1
      match c with | ⟨0, _⟩ => exact absurd rfl hc0 | ⟨1, _⟩ => exact absurd rfl hc1
    · refine ⟨1, 0, Fin.zero_ne_one.symm, by omega, h, ?_⟩
      intro c hc1 hc0
      match c with | ⟨0, _⟩ => exact absurd rfl hc0 | ⟨1, _⟩ => exact absurd rfl hc1

end GridPoint

-- ================================================================
-- Section 3: Elementary Cells for n = 1
-- ================================================================

/-- Elementary cell on a 1-simplex at precision k.
    - `vertex j` = the grid point with first coordinate j (mixing weight j/2^k)
    - `edge j` = the interval [j/2^k, (j+1)/2^k] -/
inductive ElemCell1 (k : Nat) where
  | vertex : Fin (2 ^ k + 1) → ElemCell1 k
  | edge : Fin (2 ^ k) → ElemCell1 k
  deriving DecidableEq

namespace ElemCell1

variable {k : Nat}

noncomputable instance instFintype : Fintype (ElemCell1 k) := by
  classical
  exact Fintype.ofEquiv (Fin (2 ^ k + 1) ⊕ Fin (2 ^ k))
    { toFun := fun x => match x with | .inl j => vertex j | .inr j => edge j
      invFun := fun x => match x with | vertex j => .inl j | edge j => .inr j
      left_inv := by intro x; cases x <;> rfl
      right_inv := by intro x; cases x <;> rfl }

/-- The grid point at index j on the 1-simplex. -/
abbrev gridPt (j : Fin (2 ^ k + 1)) : GridPoint 1 k := GridPoint.ofIndex1 j

/-- Grid points inside an elementary cell. -/
def gridPoints : ElemCell1 k → Finset (GridPoint 1 k)
  | vertex j => {gridPt j}
  | edge j =>
    let j1 : Fin (2 ^ k + 1) := ⟨j.val, by omega⟩
    let j2 : Fin (2 ^ k + 1) := ⟨j.val + 1, by omega⟩
    {gridPt j1, gridPt j2}

@[simp] theorem gridPoints_vertex (j : Fin (2 ^ k + 1)) :
    (vertex j : ElemCell1 k).gridPoints = {gridPt j} := rfl

theorem gridPoints_nonempty (c : ElemCell1 k) : c.gridPoints.Nonempty := by
  cases c with
  | vertex j => exact Finset.singleton_nonempty _
  | edge j => exact ⟨_, Finset.mem_insert_self _ _⟩

/-- Double an index: j at level k maps to 2j at level k+1. -/
def embedIndex (j : Fin (2 ^ k + 1)) : Fin (2 ^ (k + 1) + 1) :=
  ⟨2 * j.val, by have := j.isLt; omega⟩

/-- The midpoint index: 2j+1 at level k+1. -/
def midIndex (j : Fin (2 ^ k)) : Fin (2 ^ (k + 1) + 1) :=
  ⟨2 * j.val + 1, by have := j.isLt; omega⟩

/-- Subdivision of an elementary cell into sub-cells at the next level.
    - vertex j → [vertex (2j)]
    - edge j → [edge (2j), vertex (2j+1), edge (2j+1)] -/
def subcells : ElemCell1 k → List (ElemCell1 (k + 1))
  | vertex j => [vertex (embedIndex j)]
  | edge j =>
    have h := j.isLt
    let ej : Fin (2 ^ (k + 1)) := ⟨2 * j.val, by omega⟩
    let ej1 : Fin (2 ^ (k + 1)) := ⟨2 * j.val + 1, by omega⟩
    #[edge ej, vertex (midIndex j), edge ej1].toList

-- ----------------------------------------------------------------
-- Bridge to DSimplex (Fin 2) at k = 0
-- ----------------------------------------------------------------

/-- Convert ElemCell1 0 → DSimplex (Fin 2).
    vertex 0 ↦ {0}, vertex 1 ↦ {1}, edge 0 ↦ {0,1}. -/
def toDSimplex2 : ElemCell1 0 → DSimplex (Fin 2)
  | vertex ⟨0, _⟩ => DSimplex.vertex 0
  | vertex ⟨1, _⟩ => DSimplex.vertex 1
  | edge _ => ⟨Finset.univ, Finset.univ_nonempty⟩

/-- Convert DSimplex (Fin 2) → ElemCell1 0. -/
noncomputable def ofDSimplex2 : DSimplex (Fin 2) → ElemCell1 0 := by
  classical
  intro ⟨s, hs⟩
  exact if h0 : (0 : Fin 2) ∈ s then
    if h1 : (1 : Fin 2) ∈ s then edge ⟨0, by omega⟩
    else vertex ⟨0, by omega⟩
  else vertex ⟨1, by omega⟩

noncomputable def elemCell1ZeroEquiv : ElemCell1 0 ≃ DSimplex (Fin 2) where
  toFun := toDSimplex2
  invFun := ofDSimplex2
  left_inv := by
    intro c
    cases c with
    | vertex j =>
      have hj : j.val = 0 ∨ j.val = 1 := by have := j.isLt; omega
      rcases hj with hj | hj
      · -- j.val = 0
        have hjeq : j = ⟨0, by omega⟩ := Fin.ext hj
        rw [hjeq]; simp [toDSimplex2, ofDSimplex2, DSimplex.vertex]
      · -- j.val = 1
        have hjeq : j = ⟨1, by omega⟩ := Fin.ext hj
        rw [hjeq]; simp [toDSimplex2, ofDSimplex2, DSimplex.vertex]
    | edge j =>
      have hjeq : j = ⟨0, by omega⟩ := Fin.ext (by have := j.isLt; omega)
      rw [hjeq]; simp [toDSimplex2, ofDSimplex2]
  right_inv := by
    intro ⟨s, hs⟩
    simp only [ofDSimplex2]
    split_ifs with h0 h1
    · -- 0, 1 ∈ s → s = univ
      simp [toDSimplex2]; ext x
      simp; exact Or.elim (show x = 0 ∨ x = 1 by omega) (· ▸ h0) (· ▸ h1)
    · -- 0 ∈ s, 1 ∉ s → s = {0}
      simp [toDSimplex2]; ext x; simp
      exact ⟨fun h => h ▸ h0,
        fun hx => Or.elim (show x = 0 ∨ x = 1 by omega) id (fun h => absurd (h ▸ hx) h1)⟩
    · -- 0 ∉ s → 1 ∈ s, s = {1}
      have h1 : (1 : Fin 2) ∈ s := by
        obtain ⟨x, hx⟩ := hs
        exact Or.elim (show x = 0 ∨ x = 1 by omega) (fun h => absurd (h ▸ hx) h0) (fun h => h ▸ hx)
      simp [toDSimplex2]; ext x; simp
      exact ⟨fun h => h ▸ h1,
        fun hx => Or.elim (show x = 0 ∨ x = 1 by omega) (fun h => absurd (h ▸ hx) h0) id⟩

end ElemCell1

end SyntheticGameTheory
