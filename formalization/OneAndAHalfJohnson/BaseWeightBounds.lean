module

public import OneAndAHalfJohnson.GeometryShorteningBounds
public import OneAndAHalfJohnson.Targets.Base
public import Mathlib.Tactic.FieldSimp

/-! Uniform real bounds for the exact base-code weights. -/
@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson.BaseWeightBounds
open Targets

/-- Polynomial identities for the three integer parameters after casting. -/
theorem parameter_identities (Q m : ℕ) (hQ : 32 < Q) (hm : 4 ≤ m) :
    let q : ℝ := Q
    let b : ℝ := Q ^ (m - 4)
    let n : ℝ := baseLength Q m
    let e : ℝ := incidenceWeight Q m
    let L : ℝ := lowWeightCutoff Q m
    32 < q ∧ 1 ≤ b ∧ 0 < n ∧
      n * (q - 1) = q ^ 4 * b - 1 ∧
      e * (q - 1) = q ^ 2 * b - 1 ∧
      L = 3 * q * b - 3 * b - 1 := by
  dsimp
  have hQ1 : 1 < Q := by omega
  have hb : 1 ≤ Q ^ (m - 4) := Nat.one_le_pow _ _ (by omega)
  have hn : baseLength Q m * (Q - 1) = Q ^ m - 1 := by
    unfold baseLength
    rw [← Nat.geomSum_eq hQ1]
    exact geom_sum_mul_of_one_le (by omega) _
  have he : incidenceWeight Q m * (Q - 1) = Q ^ (m - 2) - 1 := by
    unfold incidenceWeight
    rw [← Nat.geomSum_eq hQ1]
    exact geom_sum_mul_of_one_le (by omega) _
  have hp : Q ^ m = Q ^ 4 * Q ^ (m - 4) := by
    rw [← pow_add]; congr 1; omega
  have hp2 : Q ^ (m - 2) = Q ^ 2 * Q ^ (m - 4) := by
    rw [← pow_add]; congr 1; omega
  have hp3 : Q ^ (m - 3) = Q * Q ^ (m - 4) := by
    rw [show m - 3 = (m - 4) + 1 by omega, pow_succ']
  have hL : lowWeightCutoff Q m + 3 * Q ^ (m - 4) + 1 = 3 * Q * Q ^ (m - 4) := by
    unfold lowWeightCutoff
    rw [hp3]
    have : 3 * Q ^ (m - 4) + 1 ≤ 3 * Q * Q ^ (m - 4) := by nlinarith
    simp only [mul_assoc] at *
    omega
  have hnR : (baseLength Q m : ℝ) * ((Q : ℝ) - 1) = (Q : ℝ)^4 * (Q:ℝ)^(m-4) - 1 := by
    rw [hp] at hn
    have := congrArg (fun x : ℕ => (x : ℝ)) hn
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ Q), Nat.cast_one, Nat.cast_sub (by nlinarith [Nat.one_le_pow 4 Q (by omega : 1 ≤ Q), Nat.one_le_pow 2 Q (by omega : 1 ≤ Q)])] at this
    push_cast at this
    simpa only [hp, Nat.cast_mul, Nat.cast_pow] using this
  have heR : (incidenceWeight Q m : ℝ) * ((Q : ℝ) - 1) = (Q : ℝ)^2 * (Q:ℝ)^(m-4) - 1 := by
    rw [hp2] at he
    have := congrArg (fun x : ℕ => (x : ℝ)) he
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ Q), Nat.cast_one, Nat.cast_sub (by nlinarith [Nat.one_le_pow 4 Q (by omega : 1 ≤ Q), Nat.one_le_pow 2 Q (by omega : 1 ≤ Q)])] at this
    push_cast at this
    simpa only [hp2, Nat.cast_mul, Nat.cast_pow] using this
  have hqR : (32 : ℝ) < Q := by exact_mod_cast hQ
  have hbR : (1 : ℝ) ≤ (Q:ℝ)^(m-4) := by exact_mod_cast hb
  refine ⟨hqR, hbR, ?_, hnR, heR, ?_⟩
  · have hpow : (1 : ℝ) < (Q : ℝ)^4 := by nlinarith [sq_nonneg ((Q:ℝ) - 1), sq_nonneg ((Q:ℝ)^2 - 1)]
    have := mul_le_mul_of_nonneg_left hbR (by positivity : (0:ℝ) ≤ (Q:ℝ)^4)
    nlinarith
  · have := congrArg (fun x : ℕ => (x : ℝ)) hL
    push_cast at this
    linarith

/-- Denominator-free estimates used for all normalized weights. -/
theorem cleared_bounds (Q m : ℕ) (hQ : 32 < Q) (hm : 4 ≤ m) :
    let q : ℝ := Q
    let n : ℝ := baseLength Q m
    let e : ℝ := incidenceWeight Q m
    let L : ℝ := lowWeightCutoff Q m
    0 < n ∧ e * q^2 ≤ n ∧ (q^2-1)*n ≤ e*q^4 ∧
      (3*q-7)*n ≤ L*q^3 := by
  obtain ⟨hq, hb, hnpos, hn, he, hL⟩ := parameter_identities Q m hQ hm
  dsimp only at *
  let q : ℝ := Q
  let b : ℝ := (Q:ℝ)^(m-4)
  let n : ℝ := baseLength Q m
  let e : ℝ := incidenceWeight Q m
  let L : ℝ := lowWeightCutoff Q m
  change 0 < n ∧ e*q^2 ≤ n ∧ (q^2-1)*n ≤ e*q^4 ∧ (3*q-7)*n ≤ L*q^3
  change 32 < q at hq
  change 1 ≤ b at hb
  change n*(q-1)=q^4*b-1 at hn
  change e*(q-1)=q^2*b-1 at he
  change L=3*q*b-3*b-1 at hL
  have hq1 : 0 < q-1 := by linarith
  have hq2 : 1 < q^2 := by nlinarith [sq_nonneg (q-1)]
  refine ⟨hnpos, ?_, ?_, ?_⟩
  · have hh : (n-e*q^2)*(q-1)=q^2-1 := by linear_combination hn-q^2*he
    have : 0 ≤ (n-e*q^2)*(q-1) := by rw [hh]; linarith
    have := (mul_nonneg_iff_of_pos_right hq1).mp this
    linarith
  · have hh : (e*q^4-(q^2-1)*n)*(q-1)=q^4*(b-1)+q^2-1 := by
      linear_combination q^4*he-(q^2-1)*hn
    have : 0 ≤ (e*q^4-(q^2-1)*n)*(q-1) := by
      rw [hh]
      nlinarith [mul_nonneg (pow_nonneg (show 0 ≤ q by linarith) 4) (sub_nonneg.mpr hb)]
    have := (mul_nonneg_iff_of_pos_right hq1).mp this
    linarith
  · have hh : (L*q^3-(3*q-7)*n)*(q-1)=q^4*b+3*q^3*b-q^4+q^3+3*q-7 := by
      linear_combination q^3*(q-1)*hL-(3*q-7)*hn
    have hid : q^4*b+3*q^3*b-q^4+q^3+3*q-7 =
        q^4*(b-1)+q^3*(3*b+1)+3*q-7 := by ring
    have : 0 ≤ (L*q^3-(3*q-7)*n)*(q-1) := by
      rw [hh, hid]
      have h₁ : 0 ≤ q^4*(b-1) := mul_nonneg (pow_nonneg (by linarith) 4) (by linarith)
      have h₂ : 0 ≤ q^3*(3*b+1) := mul_nonneg (pow_nonneg (by linarith) 3) (by linarith)
      linarith
    have := (mul_nonneg_iff_of_pos_right hq1).mp this
    linarith

/-- Uniform envelopes for the incidence, distance, and source thresholds. -/
theorem normalized_bounds (Q m : ℕ) (hQ : 32 < Q) (hm : 4 ≤ m) :
    let q : ℝ := Q
    let n : ℝ := baseLength Q m
    let e : ℝ := incidenceWeight Q m
    let L : ℝ := lowWeightCutoff Q m
    e/n ≤ 1/q^2 ∧ 3*e/n ≤ 3/q^2 ∧
    (3-7/q)/q^2 ≤ L/n ∧
    (4/3-2/q^2)/q^2 ≤ 4*e/(3*n) := by
  obtain ⟨hn, he, helo, hL⟩ := cleared_bounds Q m hQ hm
  dsimp only at *
  let q : ℝ := Q
  let n : ℝ := baseLength Q m
  let e : ℝ := incidenceWeight Q m
  let L : ℝ := lowWeightCutoff Q m
  change 0 < n at hn
  change e*q^2 ≤ n at he
  change (q^2-1)*n ≤ e*q^4 at helo
  change (3*q-7)*n ≤ L*q^3 at hL
  change e/n ≤ 1/q^2 ∧ 3*e/n ≤ 3/q^2 ∧
    (3-7/q)/q^2 ≤ L/n ∧ (4/3-2/q^2)/q^2 ≤ 4*e/(3*n)
  have hq : 0 < q := by dsimp [q]; exact_mod_cast (by omega : 0 < Q)
  have hq2 : 0 < q^2 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (div_le_div_iff₀ hn hq2).mpr (by simpa using he)
  · exact (div_le_div_iff₀ hn hq2).mpr (by nlinarith [he])
  · apply (div_le_div_iff₀ hq2 hn).mpr
    apply (mul_le_mul_iff_left₀ hq).mp
    calc
      ((3-7/q)*n)*q = (3*q-7)*n := by field_simp
      _ ≤ L*q^3 := hL
      _ = (L*q^2)*q := by ring
  · apply (div_le_div_iff₀ hq2 (show 0 < 3*n by positivity)).mpr
    apply (mul_le_mul_iff_left₀ hq2).mp
    calc
      ((4/3-2/q^2)*(3*n))*q^2 = (4*q^2-6)*n := by field_simp; ring
      _ ≤ 4*(e*q^4) := by nlinarith [helo]
      _ = (4*e*q^2)*q^2 := by ring

/-- All three normalized thresholds lie in the unit interval. -/
theorem normalized_unit_interval (Q m : ℕ) (hQ : 32 < Q) (hm : 4 ≤ m) :
    let n : ℝ := baseLength Q m
    let e : ℝ := incidenceWeight Q m
    let L : ℝ := lowWeightCutoff Q m
    e/n ∈ Set.Icc 0 1 ∧ (3*e/n) ∈ Set.Icc 0 1 ∧
    (L/n) ∈ Set.Icc 0 1 ∧ (4*e/(3*n)) ∈ Set.Icc 0 1 := by
  obtain ⟨he, hthree, _, _⟩ := normalized_bounds Q m hQ hm
  have hn := (cleared_bounds Q m hQ hm).1
  dsimp only at *
  have hq : (32:ℝ) < Q := by exact_mod_cast hQ
  have hq2 : (3:ℝ) ≤ (Q:ℝ)^2 := by nlinarith [sq_nonneg ((Q:ℝ)-1)]
  have hq2pos : (0:ℝ) < (Q:ℝ)^2 := by positivity
  have hthreeone : 3*(incidenceWeight Q m:ℝ)/baseLength Q m ≤ 1 :=
    hthree.trans ((div_le_one hq2pos).mpr hq2)
  have hL : (lowWeightCutoff Q m:ℝ) ≤ 3*(incidenceWeight Q m:ℝ) := by
    have hh := Geometry.cutoff_add_three_overlap_lt_three_weight Q m hQ hm
    have : lowWeightCutoff Q m ≤ 3*incidenceWeight Q m := by unfold incidenceWeight; omega
    exact_mod_cast this
  have hfone : 4*(incidenceWeight Q m:ℝ)/(3*baseLength Q m) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    have hh := (div_le_one hn).mp hthreeone
    nlinarith [show (0:ℝ) ≤ incidenceWeight Q m by positivity]
  exact ⟨⟨by positivity, he.trans ((div_le_one hq2pos).mpr (by linarith))⟩,
    ⟨by positivity, hthreeone⟩,
    ⟨by positivity, (div_le_div_of_nonneg_right hL (le_of_lt hn)).trans hthreeone⟩,
    ⟨by positivity, hfone⟩⟩

end OneAndAHalfJohnson.BaseWeightBounds
