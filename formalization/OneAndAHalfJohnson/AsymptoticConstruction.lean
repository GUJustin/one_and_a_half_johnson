module

public import OneAndAHalfJohnson.MainTheorems.BaseConstruction
public import OneAndAHalfJohnson.BaseWeightBounds
public import OneAndAHalfJohnson.FieldTowerSizing
public import OneAndAHalfJohnson.RandomAmplification
public import OneAndAHalfJohnson.AmplificationSize
public import OneAndAHalfJohnson.SubfieldReduction
public import OneAndAHalfJohnson.AmplificationAssembly

/-! Actual construction at each sufficiently large field exponent and length.
All geometric, sampling, alphabet-reduction and completion steps are proved;
AD21 is the only external mathematical premise. -/
@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson.MainTheorems
open Geometry Targets

set_option maxRecDepth 2000 in
set_option maxHeartbeats 1200000 in
theorem asymptotic_code_at_size
    (p : ℕ) [Fact p.Prime] (hAD : AD21LowWeight p)
    (a t : ℕ) (ha : 1 ≤ a) (ξ δ ρ η : ℝ) (hξ : 0 < ξ)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hγ : 0 ≤ gamma δ)
    (hQ : 121 < p ^ a)
    (hclose : amplify t (1 / (p ^ a : ℝ)^2) + 3*ξ < ρ)
    (hfar : gamma δ + 3*ξ < amplify t ((4/3 - 2/(p ^ a : ℝ)^2)/(p ^ a : ℝ)^2))
    (hlower : δ + 3*ξ < amplify t ((3-7/(p ^ a : ℝ))/(p ^ a : ℝ)^2))
    (hupper : amplify t (3/(p ^ a : ℝ)^2) + 3*ξ < δ+η)
    (s N : ℕ) (hs : 0 < s) (hslarge : 4*(2*a) ≤ s) (hNs : s ≤ N)
    (hsmall : 1 / (p ^ s : ℝ) < ξ)
    (hN : amplificationSizeConstant p (2*a) (2^(2*(p^a-1))) ξ *
      (s:ℝ)^(2*(p^a-1)+1) ≤ N)
    (F : Type) [Field F] [Fintype F] [DecidableEq F] (hF : Fintype.card F = p ^ s) :
    ∃ (C : Submodule F (Fin N → F)) (f g : Fin N → F),
      C ≠ ⊥ ∧ |relativeDistance C - δ| < η ∧
      |rate C - (1-relativeDistance C)| ≤ 6/(s:ℝ) ∧
      Far C f (gamma δ) ∧ Far C g (gamma δ) ∧
      (1/(8*(p^a:ℝ)^4))*Fintype.card F ≤ (exceptional C f g ρ).card := by
  classical
  let : NeZero a := ⟨by omega⟩
  let K := GaloisField p a
  let : Fintype K := Fintype.ofFinite K
  have hK : Fintype.card K = p^a := by
    simpa only [Nat.card_eq_fintype_card] using GaloisField.card p (n := a) (by omega)
  let m := s / Nat.gcd s (2*a)
  let r := 2*a / Nat.gcd s (2*a)
  have hm : 4 ≤ m := gcd_base_dimension_ge a s 4 (by omega) hs hslarge
  have hms : m ≤ s := Nat.div_le_self _ _
  obtain ⟨E, _, _, _, _, _, hE, hEout⟩ := exists_sized_field_tower F p a s (by omega) hs hF
  let : DecidableEq E := Classical.decEq E
  have hEK : Fintype.card E = Fintype.card K^(2*m) := by simpa only [hK] using hE
  obtain ⟨C,f,g,hCD,hfD,hgD,hC,hlo,hhi,hf,hg,hcount⟩ := point_base_of_AD21
    p hAD K a hK (by omega) (by omega) (by omega) m hm E hEK
  let D := extendCode (K := E) (incidenceSpan K (ZMod p) m)
  let : Fintype D := Fintype.ofFinite D
  have hn : Fintype.card (Point K m) = baseLength (p^a) m := by
    simpa only [Nat.card_eq_fintype_card,hK,baseLength] using (point_card (K:=K) (m:=m))
  have hI : 0 < Fintype.card (Point K m) :=
    lt_of_lt_of_le (lt_of_le_of_lt (Nat.zero_le _) hlo) (Code.dist_le_card (C : Set (Point K m → E)))
  let : Nonempty (Point K m) := Fintype.card_pos_iff.mp hI
  let : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  have hIR : (0:ℝ) < Fintype.card (Point K m) := by exact_mod_cast hI
  obtain ⟨heenv,hhienv,hloenv,hfenv⟩ := BaseWeightBounds.normalized_bounds (p^a) m (by omega) hm
  obtain ⟨heunit,hhiunit,hLunit,hfunit⟩ := BaseWeightBounds.normalized_unit_interval (p^a) m (by omega) hm
  simp only [Nat.cast_pow] at heenv hhienv hloenv hfenv
  have hdlo : (3-7/(p^a:ℝ))/(p^a:ℝ)^2 ≤ relativeDistance C := by
    apply hloenv.trans
    rw [relativeDistance, ← hn]
    exact le_of_lt ((div_lt_div_iff_of_pos_right hIR).mpr (by rw [← hK]; exact_mod_cast hlo))
  have hdhi : relativeDistance C ≤ 3/(p^a:ℝ)^2 := by
    apply le_trans _ hhienv
    rw [relativeDistance, ← hn]
    apply le_of_lt ((div_lt_div_iff_of_pos_right hIR).mpr ?_)
    rw [← hK]
    exact_mod_cast hhi
  have hdone : relativeDistance C ≤ 1 := by
    unfold relativeDistance
    exact div_le_one_of_le₀ (by exact_mod_cast Code.dist_le_card (C : Set (Point K m → E))) (Nat.cast_nonneg _)
  have hqreal : (121:ℝ) < (p:ℝ)^a := by exact_mod_cast hQ
  have hthreeone : 3/(p^a:ℝ)^2 ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    nlinarith [sq_nonneg ((p:ℝ)^a-1)]
  have hdlower := amplify_mono t hdlo hdone
  have hdupper := amplify_mono t hdhi hthreeone
  have hpositive : 2*ξ < amplify t (relativeDistance C) := by linarith
  let c : ℝ := 1/(4*(p^a:ℝ)^4)
  have hc : 0 < c := by dsimp [c]; positivity
  have hdensity : c*Fintype.card E ≤ (exceptional C f g
      ((incidenceWeight (Fintype.card K) m:ℝ)/Fintype.card (Point K m))).card := by
    have hh := codimTwo_card_fraction K m hm
    have hh' : c*Fintype.card E ≤ (Nat.card (CodimTwo K m):ℝ) := by
      simpa only [c,hEK,hK,Nat.cast_pow] using hh
    exact hh'.trans (by exact_mod_cast hcount)
  have hρτ : (incidenceWeight (Fintype.card K) m:ℝ)/Fintype.card (Point K m) ≤
      4*(incidenceWeight (Fintype.card K) m:ℝ)/(3*Fintype.card (Point K m)) := by
    have hepos : (0:ℝ) ≤ incidenceWeight (Fintype.card K) m := Nat.cast_nonneg _
    apply (div_le_div_iff₀ hIR (by positivity)).mpr
    nlinarith
  obtain ⟨b,hb,T,_,hTcount,hf',hg',hT⟩ := exists_subfield_exceptional_reduction
    (F:=F) C f g _ _ c hc hf hg hρτ hdensity
  have hgbD : b • g ∈ D := D.smul_mem b hgD
  have hcard : Fintype.card D ≤ (p^s)^(r*(2^(2*(p^a-1))*s^(2*(p^a-1)))) := by
    simpa only [D, Nat.card_eq_fintype_card,hK] using
      extended_incidence_card_bound_in_exponent p K E m s r hs hms hEout
  have hfailure : 2*(Fintype.card D:ℝ)*Real.exp (-2*ξ^2*Fintype.card (Fin N)) < 1 := by
    rw [Fintype.card_fin]
    apply hoeffding_union_lt_one_of_polynomial_length p (2*a) (2*(p^a-1))
      (2^(2*(p^a-1))) ξ (Fact.out : p.Prime).two_le hξ s r
      (2^(2*(p^a-1))*s^(2*(p^a-1))) (Fintype.card D) N (by omega)
      (gcd_extension_degree_le a s) _ hcard hN
    push_cast
    exact le_rfl
  obtain ⟨A,hA⟩ := exists_linear_uniform_amplification (F:=F) (J:=Fin N)
    (fun v : D => (v : Point K m → E)) t ξ hξ hfailure
  have happrox : ∀ v ∈ D, |relativeWeight (A v)-amplify t (relativeWeight v)| ≤ 2*ξ := by
    intro v hv
    have hh := amplification_error_le_add_inv t (Fintype.card F:ℝ)
      (relativeWeight v) (relativeWeight (A v)) ξ
      (by exact_mod_cast Fintype.card_pos (α:=F))
      ⟨by unfold relativeWeight; positivity, relativeWeight_le_one v⟩ (hA ⟨v,hv⟩)
    have hsmall' : 1/(Fintype.card F:ℝ) < ξ := by simpa only [hF,Nat.cast_pow] using hsmall
    linarith
  have hfarMargin : gamma δ + 2*ξ < amplify t
      (4*(incidenceWeight (Fintype.card K) m:ℝ)/(3*Fintype.card (Point K m))) := by
    have hh := amplify_mono t hfenv hfunit.2
    rw [hK,hn]
    linarith
  have hcloseMargin : amplify t ((incidenceWeight (Fintype.card K) m:ℝ)/
      Fintype.card (Point K m))+2*ξ ≤ ρ := by
    have hqone : 1/(p^a:ℝ)^2 ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      nlinarith [sq_nonneg ((p:ℝ)^a-1)]
    have hh := amplify_mono t heenv hqone
    rw [hK,hn]
    linarith
  have hne : ∃ v ∈ C, v ≠ 0 := by
    by_contra hh
    push Not at hh
    apply hC
    exact le_antisymm (fun v hv => by simpa using hh v hv) bot_le
  obtain ⟨hC0,hC0lo,hC0hi,hf0,hg0,hcount0⟩ := amplified_image_parameters
    C D hCD A f (b•g) hfD hgbD t (2*ξ) _ _ (gamma δ) ρ T hI
    (by simpa using (show 0<N by omega)) hne happrox hpositive hf' hg' hfarMargin
    (by simpa only [hK,hn] using heunit.2) hcloseMargin
    (by intro z hz; simpa only [IsScalarTower.algebraMap_smul] using hT z hz)
  let C0 := (C.restrictScalars F).map A
  have hδ0 : δ < relativeDistance C0 := by dsimp [C0]; linarith
  have hδupper : relativeDistance C0 < δ+η := by dsimp [C0]; linarith
  have hne0 : ∃ v ∈ C0, v ≠ 0 := by
    by_contra hh
    push Not at hh
    apply hC0
    exact le_antisymm (fun v hv => by simpa using hh v hv) bot_le
  obtain ⟨C1,_,hC1,hd1,hf1,hg1,hcount1,hrate⟩ := exists_relative_nearMDS_completion
    C0 (A f) (A (b•g)) (gamma δ) ρ p s (Fact.out : p.Prime).two_le hs hF
    (by simpa using hNs) hne0 hγ ((gamma_lt_distance hδ hδ1).trans hδ0) hf0 hg0
  refine ⟨C1,A f,A (b•g),hC1,?_,hrate,hf1,hg1,?_⟩
  · rw [hd1,abs_of_pos (sub_pos.mpr hδ0)]
    linarith
  · have hh : (c/2)*Fintype.card F ≤ (exceptional C1 (A f) (A (b•g)) ρ).card :=
      hTcount.trans (by exact_mod_cast hcount0.trans hcount1)
    convert hh using 1
    dsimp [c]
    ring

end OneAndAHalfJohnson.MainTheorems
