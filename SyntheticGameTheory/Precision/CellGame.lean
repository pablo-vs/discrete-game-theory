import SyntheticGameTheory
import SyntheticGameTheory.Precision.Grid
import SyntheticGameTheory.Precision.GridProfile

namespace SyntheticGameTheory

-- ================================================================
-- Section 1: Grid Midpoint — same-level partial operation
-- ================================================================

/-- Two grid points `a, b : Fin (2^k + 1)` are mixable iff they are endpoints
    of an edge at some coarser level, embedded into level k. Combinatorially:
    they differ by `2^s` for some `s ≥ 1`, and the smaller is divisible by `2^s`. -/
def HasGridMid1 (k : Nat) (a b : Fin (2 ^ k + 1)) : Prop :=
  ∃ s : Fin (k + 1), 1 ≤ s.val ∧ s.val ≤ k ∧
    ((a.val + 2 ^ s.val = b.val ∧ a.val % 2 ^ s.val = 0) ∨
     (b.val + 2 ^ s.val = a.val ∧ b.val % 2 ^ s.val = 0))

instance HasGridMid1.instDecidable {k : Nat} {a b : Fin (2 ^ k + 1)} :
    Decidable (HasGridMid1 k a b) :=
  inferInstanceAs (Decidable (∃ _ : Fin (k + 1), _))

/-- The midpoint of two grid points (always a valid grid index when HasGridMid1 holds). -/
def gridMid1 {k : Nat} (a b : Fin (2 ^ k + 1)) : Fin (2 ^ k + 1) :=
  ⟨(a.val + b.val) / 2, by have := a.isLt; have := b.isLt; omega⟩

private theorem two_dvd_of_pow_dvd {s a : Nat} (hs : 1 ≤ s) (h : a % 2 ^ s = 0) :
    2 ∣ a := by
  have h1 : 2 ^ s ∣ a := Nat.dvd_of_mod_eq_zero h
  have h2 : (2 : Nat) ∣ 2 ^ s := ⟨2 ^ (s - 1), by
    rw [show s = (s - 1) + 1 from by omega]; simp [Nat.pow_succ, Nat.mul_comm]⟩
  exact Nat.dvd_trans h2 h1

private theorem two_dvd_pow (s : Nat) (hs : 1 ≤ s) : 2 ∣ 2 ^ s :=
  ⟨2 ^ (s - 1), by rw [show s = (s - 1) + 1 from by omega]; simp [Nat.pow_succ, Nat.mul_comm]⟩

private theorem hasGridMid1_even {k : Nat} {a b : Fin (2 ^ k + 1)}
    (h : HasGridMid1 k a b) : 2 ∣ (a.val + b.val) := by
  obtain ⟨s_fin, hs1, _, hab⟩ := h
  rcases hab with ⟨_, h2⟩ | ⟨_, h2⟩
  · have := two_dvd_of_pow_dvd hs1 h2; have := two_dvd_pow s_fin.val hs1; omega
  · have := two_dvd_of_pow_dvd hs1 h2; have := two_dvd_pow s_fin.val hs1; omega

/-- When HasGridMid1 holds, the sum a + b is even, so gridMid1 is exact. -/
theorem gridMid1_spec {k : Nat} {a b : Fin (2 ^ k + 1)} (h : HasGridMid1 k a b) :
    2 * (gridMid1 a b).val = a.val + b.val := by
  simp only [gridMid1]; have := hasGridMid1_even h; omega

/-- At k=0, the grid is {0, 1} and no pair satisfies HasGridMid1. -/
theorem hasGridMid1_vacuous_zero {a b : Fin (2 ^ 0 + 1)} : ¬HasGridMid1 0 a b := by
  intro ⟨⟨s, hs_lt⟩, hs1, _, _⟩; omega

-- ================================================================
-- Section 2: GridPrefSystem — the core game structure
-- ================================================================

/-- A preference system on grid points at precision k.
    `pref i j a b` means: player i weakly prefers action b over action a,
    when the opponent plays grid point j. -/
structure GridPrefSystem (k : Nat) where
  pref : (i : Fin 2) → (j : Fin (2 ^ k + 1)) → (a b : Fin (2 ^ k + 1)) → Prop
  pref_refl : ∀ i j a, pref i j a a
  pref_trans : ∀ i j a b c, pref i j a b → pref i j b c → pref i j a c
  pref_total : ∀ i j a b, pref i j a b ∨ pref i j b a
  pref_decidable : ∀ i j a b, Decidable (pref i j a b)
  interpolation : ∀ i j a b, HasGridMid1 k a b →
    let c := gridMid1 a b
    (pref i j a b → pref i j a c ∧ pref i j c b) ∧
    (pref i j b a → pref i j b c ∧ pref i j c a)
  interpolation_neg : ∀ i j a b, HasGridMid1 k a b →
    let c := gridMid1 a b
    (¬pref i j a b → ¬pref i j a c ∧ ¬pref i j c b) ∧
    (¬pref i j b a → ¬pref i j b c ∧ ¬pref i j c a)

attribute [instance] GridPrefSystem.pref_decidable

-- ================================================================
-- Section 3: Construction from base game
-- ================================================================

/-- Build a GridPrefSystem at level 0 from a base 2×2 game.
    At k=0, `Fin (2^0 + 1) = Fin 2` definitionally, so grid indices are actions.
    Interpolation is vacuously true since HasGridMid1 0 never holds. -/
noncomputable def GridPrefSystem.ofGame
    (G : Game (Fin 2) (fun _ => Fin 2)) : GridPrefSystem 0 where
  pref i j a b :=
    G.pref i
      (fun p => if p = i then a else j)
      (fun p => if p = i then b else j)
  pref_refl _ _ _ := (G.pref_preorder _).toRefl.refl _
  pref_trans _ _ _ _ _ hab hbc :=
    (G.pref_preorder _).toIsTrans.trans _ _ _ hab hbc
  pref_total _ _ _ _ := (G.pref_total _).total _ _
  pref_decidable _ _ _ _ := G.pref_decidable _ _ _
  interpolation _ _ _ _ h := absurd h hasGridMid1_vacuous_zero
  interpolation_neg _ _ _ _ h := absurd h hasGridMid1_vacuous_zero

-- ================================================================
-- Section 4: CellDevLE, CellStrictDev, CellIsNash
-- ================================================================

/-- Player i weakly prefers cell B over cell A at cell profile σ. -/
def CellDevLE (gps : GridPrefSystem k) (i : Fin 2)
    (σ : CellProfile1 k) (A B : ElemCell1 k) : Prop :=
  ∀ q ∈ (σ (1 - i)).gridPoints,
    ∀ a ∈ A.gridPoints, ∀ b ∈ B.gridPoints,
      gps.pref i (GridPoint.toIndex1 q) (GridPoint.toIndex1 a) (GridPoint.toIndex1 b)

noncomputable instance CellDevLE.instDecidable (gps : GridPrefSystem k) (i : Fin 2)
    (σ : CellProfile1 k) (A B : ElemCell1 k) :
    Decidable (CellDevLE gps i σ A B) :=
  inferInstanceAs (Decidable (∀ q ∈ _, ∀ a ∈ _, ∀ b ∈ _, _))

/-- Player i has a strict deviation to cell A from cell profile σ. -/
def CellStrictDev (gps : GridPrefSystem k) (i : Fin 2)
    (σ : CellProfile1 k) (A : ElemCell1 k) : Prop :=
  CellDevLE gps i σ (σ i) A ∧ ¬CellDevLE gps i σ A (σ i)

noncomputable instance CellStrictDev.instDecidable (gps : GridPrefSystem k) (i : Fin 2)
    (σ : CellProfile1 k) (A : ElemCell1 k) :
    Decidable (CellStrictDev gps i σ A) :=
  inferInstanceAs (Decidable (_ ∧ ¬_))

/-- Cell profile σ is a Nash equilibrium under grid preference system gps. -/
def CellIsNash (gps : GridPrefSystem k) (σ : CellProfile1 k) : Prop :=
  ∀ i, ∀ A, ¬CellStrictDev gps i σ A

noncomputable instance CellIsNash.instDecidable (gps : GridPrefSystem k)
    (σ : CellProfile1 k) : Decidable (CellIsNash gps σ) :=
  inferInstanceAs (Decidable (∀ _, ∀ _, ¬_))

-- ================================================================
-- Section 5: Bridge at k = 0
-- ================================================================

-- Helper: CellDevLE at k=0 ↔ DevFaceLE for the corresponding DSimplex faces.
private theorem cellDevLE_zero_iff (G : Game (Fin 2) (fun _ => Fin 2))
    (i : Fin 2) (σ : CellProfile1 0) (A B : ElemCell1 0) :
    CellDevLE (GridPrefSystem.ofGame G) i σ A B ↔
      G.DevFaceLE i (cellProfile1ZeroEquiv σ) (ElemCell1.elemCell1ZeroEquiv A)
        (ElemCell1.elemCell1ZeroEquiv B) := by
  have i_cases : i = 0 ∨ i = 1 := by
    rcases i with ⟨_ | _ | _, _⟩ <;> simp_all; omega
  -- gridPoints ↔ DSimplex support
  have ofIndex1_inj : ∀ (x y : Fin (2 ^ 0 + 1)),
      GridPoint.ofIndex1 x = GridPoint.ofIndex1 y ↔ x = y := by
    intro x y; constructor
    · intro h; exact Fin.ext (by have := congrArg (·.coords 0) h; simp [GridPoint.ofIndex1] at this; exact this)
    · rintro rfl; rfl
  have gps_iff : ∀ (c : ElemCell1 0) (w : Fin (2 ^ 0 + 1)),
      GridPoint.ofIndex1 w ∈ c.gridPoints ↔ w ∈ (ElemCell1.elemCell1ZeroEquiv c).1 := by
    intro c w
    cases c with
    | vertex j =>
      simp only [ElemCell1.gridPoints_vertex, Finset.mem_singleton, ElemCell1.gridPt, ofIndex1_inj]
      have hj : j.val = 0 ∨ j.val = 1 := by have := j.isLt; omega
      rcases hj with hj | hj
      · have hjeq : j = (0 : Fin 2) := Fin.ext hj; subst hjeq
        simp [ElemCell1.elemCell1ZeroEquiv, ElemCell1.toDSimplex2, DSimplex.vertex]
      · have hjeq : j = (1 : Fin 2) := Fin.ext hj; subst hjeq
        simp [ElemCell1.elemCell1ZeroEquiv, ElemCell1.toDSimplex2, DSimplex.vertex]
    | edge j =>
      have hjeq : j = (0 : Fin 1) := Fin.ext (by have := j.isLt; omega); subst hjeq
      simp only [ElemCell1.elemCell1ZeroEquiv]
      constructor
      · intro _; exact Finset.mem_univ w
      · intro _
        simp only [ElemCell1.gridPoints, ElemCell1.gridPt, Finset.mem_insert,
          Finset.mem_singleton, ofIndex1_inj]
        have : w = (0 : Fin 2) ∨ w = (1 : Fin 2) := by
          rcases w with ⟨_ | _ | _, _⟩ <;> simp_all; omega
        exact this
  constructor
  · -- CellDevLE → DevFaceLE
    intro hCell p hCons b hbB
    have hpi : p i ∈ (ElemCell1.elemCell1ZeroEquiv A).1 := by
      have := hCons i; simp [Function.update, DSimplex.support] at this; exact this
    have hpj : p (1 - i) ∈ (ElemCell1.elemCell1ZeroEquiv (σ (1 - i))).1 := by
      have := hCons (1 - i)
      simp only [Function.update, DSimplex.support,
        show (1 - i : Fin 2) ≠ i from by omega, ↓reduceDIte] at this; exact this
    have key := hCell _ ((gps_iff _ _).mpr hpj) _ ((gps_iff _ _).mpr hpi) _ ((gps_iff _ _).mpr hbB)
    simp only [GridPrefSystem.ofGame, GridPoint.toIndex1, GridPoint.ofIndex1, ite_true] at key
    -- key involves ⟨(p i).val, _⟩ instead of p i. Show the functions are equal.
    have h1 : (fun k : Fin 2 => if k = i then (⟨(p i).val, by omega⟩ : Fin 2)
        else ⟨(p (1 - i)).val, by omega⟩) = p := by
      funext ⟨k, hk⟩; rcases i_cases with rfl | rfl <;> match k with | 0 => simp | 1 => simp
    have h2 : (fun k : Fin 2 => if k = i then (⟨b.val, by omega⟩ : Fin 2)
        else ⟨(p (1 - i)).val, by omega⟩) = Function.update p i b := by
      funext ⟨k, hk⟩; rcases i_cases with rfl | rfl <;> match k with
        | 0 => simp [Function.update] | 1 => simp [Function.update]
    rwa [h1, h2] at key
  · -- DevFaceLE → CellDevLE
    intro hDev q hq a ha b hb
    set qv := GridPoint.toIndex1 q; set av := GridPoint.toIndex1 a; set bv := GridPoint.toIndex1 b
    have hqv := (gps_iff _ _).mp (show GridPoint.ofIndex1 qv ∈ _ by rwa [GridPoint.ofIndex1_toIndex1])
    have hav := (gps_iff _ _).mp (show GridPoint.ofIndex1 av ∈ _ by rwa [GridPoint.ofIndex1_toIndex1])
    have hbv := (gps_iff _ _).mp (show GridPoint.ofIndex1 bv ∈ _ by rwa [GridPoint.ofIndex1_toIndex1])
    -- Build pure profile: p i = av, p (1-i) = qv
    set p : Fin 2 → Fin 2 := fun k => if k = i then av else qv
    have hp_cons : Consistent ((cellProfile1ZeroEquiv σ)[i ↦ ElemCell1.elemCell1ZeroEquiv A]) p := by
      intro k; simp only [p, DSimplex.support, Function.update]
      split_ifs with hk
      · subst hk; exact hav
      · have hk1 : k = 1 - i := by omega
        rw [hk1, show cellProfile1ZeroEquiv σ (1 - i) = ElemCell1.elemCell1ZeroEquiv (σ (1 - i)) from rfl]
        exact hqv
    have key := hDev p hp_cons bv hbv
    show (GridPrefSystem.ofGame G).pref i qv av bv
    simp only [GridPrefSystem.ofGame]
    have h_eq : (fun k : Fin 2 => if k = i then bv else qv) = Function.update p i bv := by
      funext ⟨k, hk⟩; rcases i_cases with rfl | rfl <;> match k with
        | 0 => simp [Function.update, p] | 1 => simp [Function.update, p]
    rw [show (fun k : Fin 2 => if k = i then av else qv) = p from rfl, h_eq]
    exact key

theorem cellIsNash_zero_iff (G : Game (Fin 2) (fun _ => Fin 2))
    (σ : CellProfile1 0) :
    CellIsNash (GridPrefSystem.ofGame G) σ ↔
      G.IsNash (cellProfile1ZeroEquiv σ) := by
  simp only [CellIsNash, Game.IsNash, CellStrictDev, Game.StrictDev]
  constructor
  · intro hCell i A
    set A' := ElemCell1.elemCell1ZeroEquiv.symm A
    rw [show A = ElemCell1.elemCell1ZeroEquiv A' from (Equiv.apply_symm_apply _ A).symm]
    intro ⟨h1, h2⟩
    exact hCell i A' ⟨(cellDevLE_zero_iff G i σ (σ i) A').mpr h1,
      fun h => h2 ((cellDevLE_zero_iff G i σ A' (σ i)).mp h)⟩
  · intro hGame i A ⟨h1, h2⟩
    exact hGame i (ElemCell1.elemCell1ZeroEquiv A)
      ⟨(cellDevLE_zero_iff G i σ (σ i) A).mp h1,
       fun h => h2 ((cellDevLE_zero_iff G i σ A (σ i)).mpr h)⟩

-- ================================================================
-- Section 6: Tower extraction via coarsening
-- ================================================================

private theorem coarsen_mod_lemma {s a : Nat} (h : a % 2 ^ s = 0) :
    (2 * a) % 2 ^ (s + 1) = 0 := by
  obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero h
  show (2 * a) % (2 ^ s * 2) = 0
  rw [hc, show 2 * (2 ^ s * c) = 2 ^ s * 2 * c from by
    simp [Nat.mul_comm, Nat.mul_left_comm]]
  exact Nat.mul_mod_right _ _

/-- Coarsen a GridPrefSystem from level k+1 to level k by restricting
    to even-indexed grid points (the embedded level-k grid). -/
def GridPrefSystem.coarsen (gps : GridPrefSystem (k + 1)) : GridPrefSystem k where
  pref i j a b := gps.pref i (ElemCell1.embedIndex j) (ElemCell1.embedIndex a) (ElemCell1.embedIndex b)
  pref_refl i j a := gps.pref_refl i _ _
  pref_trans i j a b c hab hbc := gps.pref_trans i _ _ _ _ hab hbc
  pref_total i j a b := gps.pref_total i _ _ _
  pref_decidable i j a b := gps.pref_decidable i _ _ _
  interpolation i j a b hmid := by
    set_option linter.unusedSimpArgs false in
    have hmid' : HasGridMid1 (k + 1) (ElemCell1.embedIndex a) (ElemCell1.embedIndex b) := by
      obtain ⟨⟨sv, hsv_lt⟩, hs1, hsk, hab⟩ := hmid
      simp only [Fin.val_mk] at hs1 hsk hab
      refine ⟨⟨sv + 1, by omega⟩, by simp only [Fin.val_mk]; omega,
             by simp only [Fin.val_mk]; omega, ?_⟩
      simp only [ElemCell1.embedIndex, Fin.val_mk]
      have hps : 2 ^ (sv + 1) = 2 ^ sv * 2 := Nat.pow_succ 2 sv
      rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; exact ⟨by omega, coarsen_mod_lemma h2⟩
      · right; exact ⟨by omega, coarsen_mod_lemma h2⟩
    have hmid_eq : gridMid1 (ElemCell1.embedIndex a) (ElemCell1.embedIndex b) =
        ElemCell1.embedIndex (gridMid1 a b) := by
      apply Fin.ext
      simp only [gridMid1, ElemCell1.embedIndex, Fin.val_mk]
      have h_even : 2 ∣ (a.val + b.val) := hasGridMid1_even hmid
      omega
    have result := gps.interpolation i (ElemCell1.embedIndex j)
      (ElemCell1.embedIndex a) (ElemCell1.embedIndex b) hmid'
    simp only [hmid_eq] at result
    exact result
  interpolation_neg i j a b hmid := by
    set_option linter.unusedSimpArgs false in
    have hmid' : HasGridMid1 (k + 1) (ElemCell1.embedIndex a) (ElemCell1.embedIndex b) := by
      obtain ⟨⟨sv, hsv_lt⟩, hs1, hsk, hab⟩ := hmid
      simp only [Fin.val_mk] at hs1 hsk hab
      refine ⟨⟨sv + 1, by omega⟩, by simp only [Fin.val_mk]; omega,
             by simp only [Fin.val_mk]; omega, ?_⟩
      simp only [ElemCell1.embedIndex, Fin.val_mk]
      have hps : 2 ^ (sv + 1) = 2 ^ sv * 2 := Nat.pow_succ 2 sv
      rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; exact ⟨by omega, coarsen_mod_lemma h2⟩
      · right; exact ⟨by omega, coarsen_mod_lemma h2⟩
    have hmid_eq : gridMid1 (ElemCell1.embedIndex a) (ElemCell1.embedIndex b) =
        ElemCell1.embedIndex (gridMid1 a b) := by
      apply Fin.ext
      simp only [gridMid1, ElemCell1.embedIndex, Fin.val_mk]
      have h_even : 2 ∣ (a.val + b.val) := hasGridMid1_even hmid
      omega
    have result := gps.interpolation_neg i (ElemCell1.embedIndex j)
      (ElemCell1.embedIndex a) (ElemCell1.embedIndex b) hmid'
    simp only [hmid_eq] at result
    exact result

/-- Extract the GridPrefSystem at level j from a level-k system, for j ≤ k. -/
def GridPrefSystem.towerAt (gps : GridPrefSystem k) : (j : Nat) → j ≤ k → GridPrefSystem j
  | j, hjk => by
    induction k with
    | zero => exact Nat.le_zero.mp hjk ▸ gps
    | succ k ih =>
      by_cases hjk' : j ≤ k
      · exact ih gps.coarsen hjk'
      · have : j = k + 1 := by omega
        exact this ▸ gps

end SyntheticGameTheory
