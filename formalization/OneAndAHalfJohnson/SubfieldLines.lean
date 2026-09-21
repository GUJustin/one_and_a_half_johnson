module

public import OneAndAHalfJohnson.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-! # Extracting a dense multiplicative translate by double counting -/
@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson

/-- For every finite group and finite family of group elements, some translate
meets a given set at least as often as the average translate. -/
theorem exists_dense_translate {G H : Type*} [Group G] [Fintype G] [Fintype H] [DecidableEq G]
    (t : H → G) (S : Finset G) :
    ∃ b : G, S.card * Fintype.card H ≤
      Fintype.card G * (Finset.univ.filter (fun h => b * t h ∈ S)).card := by
  classical
  let n (b : G) := (Finset.univ.filter (fun h => b * t h ∈ S)).card
  have havg : ∑ b, n b = S.card * Fintype.card H := by
    simp only [n, Finset.card_filter]
    rw [Finset.sum_comm]
    have hh (h : H) : (∑ b : G, if b * t h ∈ S then 1 else 0) = S.card := by
      rw [Fintype.sum_equiv (Equiv.mulRight (t h))
        (fun b => if b * t h ∈ S then 1 else 0)
        (fun b => if b ∈ S then 1 else 0) (fun _ => rfl)]
      simp
    simp_rw [hh]
    simp [mul_comm]
  obtain ⟨b, _, hb⟩ := Finset.exists_max_image Finset.univ n Finset.univ_nonempty
  refine ⟨b, ?_⟩
  rw [← havg]
  calc
    ∑ x, n x ≤ ∑ _ : G, n b := Finset.sum_le_sum (fun x hx => hb x hx)
    _ = Fintype.card G * n b := by simp

/-- A nonzero finite-field set has a subfield line meeting the density bound.
The count uses nonzero base-field scalars (units), so it counts distinct
nonzero points of that line. -/
theorem exists_dense_subfield_line {F E : Type*} [Field F] [Field E]
    [Fintype F] [Fintype E] [DecidableEq F] [DecidableEq E] [Algebra F E] (S : Finset E) (hzero : (0 : E) ∉ S) :
    ∃ b : Eˣ, S.card * (Fintype.card F - 1) ≤
      (Fintype.card E - 1) *
        (Finset.univ.filter (fun z : Fˣ => (b : E) * algebraMap F E (z : F) ∈ S)).card := by
  classical
  let T : Finset Eˣ := Finset.univ.filter (fun x => (x : E) ∈ S)
  have hcard : T.card = S.card := by
    apply Finset.card_bij (fun (x : Eˣ) _ => (x : E))
    · intro x hx; exact (Finset.mem_filter.mp hx).2
    · intro x hx y hy hxy; exact Units.ext hxy
    · intro y hy
      have hy0 : y ≠ 0 := by intro h; subst y; exact hzero hy
      refine ⟨Units.mk0 y hy0, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩
  obtain ⟨b, hb⟩ := exists_dense_translate (fun z : Fˣ => Units.map (algebraMap F E) z) T
  refine ⟨b, ?_⟩
  simpa [hcard, Fintype.card_units, T] using hb

/-- The dense-line bound with the coefficient counted in the base field itself. -/
theorem exists_dense_subfield_line_coefficients {F E : Type*} [Field F] [Field E]
    [Fintype F] [Fintype E] [DecidableEq F] [DecidableEq E] [Algebra F E]
    (S : Finset E) (hzero : (0 : E) ∉ S) :
    ∃ b : E, b ≠ 0 ∧ S.card * (Fintype.card F - 1) ≤
      (Fintype.card E - 1) *
        (Finset.univ.filter (fun z : F => b * algebraMap F E z ∈ S)).card := by
  classical
  obtain ⟨b, hb⟩ := exists_dense_subfield_line (F := F) S hzero
  refine ⟨b, b.ne_zero, ?_⟩
  have hcard :
      (Finset.univ.filter (fun z : Fˣ => (b : E) * algebraMap F E (z : F) ∈ S)).card =
      (Finset.univ.filter (fun z : F => (b : E) * algebraMap F E z ∈ S)).card := by
    apply Finset.card_bij (fun (z : Fˣ) _ => (z : F))
    · intro z hz; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2⟩
    · intro x hx y hy hxy; exact Units.ext hxy
    · intro z hz
      have hz0 : z ≠ 0 := by
        intro heq
        have hzS := (Finset.mem_filter.mp hz).2
        simp only [heq, map_zero, mul_zero] at hzS
        exact hzero hzS
      refine ⟨Units.mk0 z hz0, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2⟩
  rwa [hcard] at hb

end OneAndAHalfJohnson
