module
public import OneAndAHalfJohnson.ConcreteConstruction
public import OneAndAHalfJohnson.ConcreteSampling
public import OneAndAHalfJohnson.Targets.Conditional
public import Mathlib.Algebra.CharP.CharAndCard
/-! Theorem 4.1 (pp. 15–20): the full explicit counterexample.
The only external mathematical premises are AD21 and the specialized Hamada
rank formula. The geometry, random-map existence and completion are proved. -/
@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson.MainTheorems
open Geometry Targets

/-- Full concrete existence over every field of cardinality 2^128. -/
theorem concreteTheorem_of_AD21_Hamada
    (hAD : AD21LowWeight 2) (hH : HamadaBinaryRank) : ConcreteTheorem := by
  classical
  intro F _ _ _ hF
  let : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  let : CharP F 2 := charP_of_card_eq_prime_pow hF
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let K := GaloisField 2 9
  let : Fintype K := Fintype.ofFinite K
  let : Fintype (CodimTwo K 5) := Fintype.ofFinite _
  have hK : Fintype.card K = 512 := by
    have hh := GaloisField.card 2 (n:=9) (by norm_num)
    simpa [Nat.card_eq_fintype_card,K] using hh
  have hI : Fintype.card (Point K 5) = 68853957121 := by
    have hh := point_card (K:=K) (m:=5)
    norm_num [Nat.card_eq_fintype_card,hK] at hh
    exact hh
  have hW : Fintype.card (CodimTwo K 5) = 18049720589484545 := by
    simpa only [Nat.card_eq_fintype_card] using codimTwo_card_512_five K hK
  obtain ⟨C,f,g,h₀,z,v,_,_,_,_,hdim,hd,hh₀,hh₀ne,hh₀weight,hf,hg,hz,hv⟩ :=
    concrete_base_of_AD21_Hamada hAD hH K F hK hF
  have hs0 := concrete_nonzero_failure_sum C hF hI hdim hd
  have hsf := concrete_affine_failure_sum C f hF hI hdim hd hf
  have hsg := concrete_affine_failure_sum C g hF hI hdim hd hg
  obtain ⟨A,hA0,hAf,hAg,hAh₀,hAv⟩ := exists_concrete_sampling_map
    (J:=Fin (2^36)) C f g h₀ v hF hI (Fintype.card_fin _) hW hd
    (affineCodeWords_min_of_source C f 350210 hf)
    (affineCodeWords_min_of_source C g 350210 hg)
    hh₀ne hh₀weight (fun w => (hv w).2.1) hs0 hsf hsg
  obtain ⟨C₁,hC₁,hdlo,hdhi,hrlo,hrhi,hf₁,hg₁,hradius,hcount⟩ :=
    concrete_code_of_sampled_bounds C f g h₀ z v A hF (Fintype.card_fin _)
      hdim.le hh₀ hh₀ne hz (fun w => (hv w).2.2) hA0 hAf hAg hAh₀ hAv
  exact ⟨C₁,A f,A g,hC₁,hdlo,hdhi,hrlo,hrhi,hf₁,hg₁,hradius,by rwa [hW] at hcount⟩

/-- The exact authorized conditional concrete contract. -/
theorem conditionalConcreteTheorem : ConditionalConcreteTheorem :=
  concreteTheorem_of_AD21_Hamada

end OneAndAHalfJohnson.MainTheorems
