module

public import OneAndAHalfJohnson.Geometry
public import OneAndAHalfJohnson.SubspacePolynomialMoments
public import OneAndAHalfJohnson.Targets.Base
public import Mathlib.Tactic.LinearCombination

/-!
# Concrete moment syndromes

The syndrome functionals sum powers over all vectors in each projective line.
This gives the same separating directions as the representative-based formula
in Lemma 3.5, and avoids a choice of representatives or division by `Q-1`.
-/

@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson.SyndromeConstruction
open Geometry SubspacePolynomial
attribute [local instance] Classical.propDecidable

variable {K : Type*} [Field K] [Fintype K] {m : ℕ}

omit [Fintype K] in
/-- A nonzero vector lies on exactly its own projective point. -/
theorem mem_line_iff (x : Fin m → K) (hx : x ≠ 0) (P : Point K m) :
    x ∈ P.submodule ↔ P = Projectivization.mk K x hx := by
  rw [Projectivization.submodule_eq, Submodule.mem_span_singleton,
    ← Projectivization.mk_eq_mk_iff' K x P.rep hx P.rep_nonzero,
    Projectivization.mk_rep, eq_comm]

/-- Sum a function over all vectors of a projective line, including zero. -/
def lineSum {F : Type*} [Field F] (f : (Fin m → K) → F) (P : Point K m) : F := by
  classical
  exact ∑ x : Fin m → K, if x ∈ P.submodule then f x else 0

/-- Summing the line weights of an incidence row partitions all its nonzero
vectors. The zero vector contributes zero, as assumed explicitly. -/
theorem incidence_lineSum {F : Type*} [Field F]
    (f : (Fin m → K) → F) (hf : f 0 = 0) (W : CodimTwo K m) :
    (∑ P : Point K m, incidenceWord F W P * lineSum f P) =
      ∑ x : Fin m → K, if x ∈ W.val then f x else 0 := by
  classical
  simp only [lineSum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hx0 : x = 0
  · simp [hx0, hf]
  · simp_rw [mem_line_iff x hx0]
    rw [Finset.sum_eq_single (Projectivization.mk K x hx0)]
    · simp [incidenceWord, incident_mk_iff]
    · intro P hP hne
      simp [hne]
    · simp

/-- The scalar-valued linear functional defined by the line weights. -/
def weightedSum {E : Type*} [Field E] (a : Point K m → E) :
    (Point K m → E) →ₗ[E] E where
  toFun v := ∑ P, v P * a P
  map_add' v w := by simp [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c v := by simp [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

variable {V E : Type*} [Field V] [Fintype V] [Algebra K V]
  [Field E] [Algebra V E]

/-- A power-sum functional on the full word space over the syndrome field. -/
def momentFunctional (Φ : (Fin m → K) ≃ₗ[K] V) (d : ℕ) :
    (Point K m → E) →ₗ[E] E :=
  weightedSum (fun P => algebraMap V E (lineSum (fun x => Φ x ^ d) P))

/-- Its value on an incidence vector is the actual moment of the image subspace. -/
theorem momentFunctional_incidence (Φ : (Fin m → K) ≃ₗ[K] V)
    (d : ℕ) (hd : 0 < d) (W : CodimTwo K m) :
    momentFunctional (E := E) Φ d (incidenceWord E W) =
      algebraMap V E (moment (W.val.map Φ.toLinearMap) d) := by
  classical
  have hf : (fun x => Φ x ^ d) 0 = 0 := by simp [hd.ne']
  have he := incidence_lineSum (fun x => Φ x ^ d) hf W
  have hmap : (∑ P : Point K m, incidenceWord E W P *
      algebraMap V E (lineSum (fun x => Φ x ^ d) P)) =
      algebraMap V E (∑ P : Point K m, incidenceWord V W P * lineSum (fun x => Φ x ^ d) P) := by
    simp only [map_sum, map_mul]
    congr 1
    funext P
    simp [incidenceWord]
  change (∑ P : Point K m, incidenceWord E W P *
    algebraMap V E (lineSum (fun x => Φ x ^ d) P)) = _
  rw [hmap, he]
  congr 1
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := fun x => x ∈ W.val) _ (by intro x; simp)]
  have hs := (Φ.submoduleMap W.val).toEquiv.sum_comp (fun w => (w : V) ^ d)
  change (∑ x : W.val, Φ x ^ d) = (∑ x : W.val.map Φ.toLinearMap, (x : V) ^ d) at hs
  unfold moment
  convert hs using 1
  congr 1
  ext x
  simp

/-- The three exponents in the subspace-polynomial moment construction. -/
def exponentZero (Q m : ℕ) : ℕ := Q ^ (m - 2) - 1

def exponentOne (Q m : ℕ) : ℕ := 2 * Q ^ (m - 2) - Q ^ (m - 3) - 1

def exponentTwo (Q m : ℕ) : ℕ := 2 * Q ^ (m - 2) - Q ^ (m - 4) - 1

/-- All three exponents are positive in the paper's dimension range. -/
theorem exponents_pos (Q m : ℕ) (hQ : 2 < Q) (hm : 4 ≤ m) :
    0 < exponentZero Q m ∧ 0 < exponentOne Q m ∧ 0 < exponentTwo Q m := by
  have h0 : 1 < Q ^ (m - 2) := Nat.one_lt_pow (by omega) (by omega)
  have h1 : Q ^ (m - 3) < Q ^ (m - 2) := Nat.pow_lt_pow_right (by omega) (by omega)
  have h2 : Q ^ (m - 4) < Q ^ (m - 2) := Nat.pow_lt_pow_right (by omega) (by omega)
  unfold exponentZero exponentOne exponentTwo
  omega

/-- The actual E-linear syndrome map on the full coordinate space. -/
def syndromeMap (Φ : (Fin m → K) ≃ₗ[K] V) (β : E) :
    (Point K m → E) →ₗ[E] (E × E) :=
  (momentFunctional Φ (exponentZero (Fintype.card K) m)).prod
    (momentFunctional Φ (exponentOne (Fintype.card K) m) +
      β • momentFunctional Φ (exponentTwo (Fintype.card K) m))

/-- The moment evaluation formula for a geometric incidence row. -/
theorem syndromeMap_incidence (Φ : (Fin m → K) ≃ₗ[K] V) (β : E)
    (hm : 4 ≤ m) (hQ : 2 < Fintype.card K) (W : CodimTwo K m) :
    let L := rootProduct (W.val.map Φ.toLinearMap)
    syndromeMap Φ β (incidenceWord E W) =
      (algebraMap V E (L.coeff 1),
       -(algebraMap V E (L.coeff 1)) *
         (algebraMap V E (L.coeff (Fintype.card K ^ (m - 3))) +
           β * algebraMap V E (L.coeff (Fintype.card K ^ (m - 4))))) := by
  dsimp only
  have hr : Module.finrank K (W.val.map Φ.toLinearMap) + 2 = m := by
    rw [← (Φ.submoduleMap W.val).finrank_eq]
    exact W.property
  have h := rootProduct_distinguished_moments (W.val.map Φ.toLinearMap) m hm hr hQ
  change moment (W.val.map Φ.toLinearMap) (exponentZero (Fintype.card K) m) = _ ∧
    moment (W.val.map Φ.toLinearMap) (exponentOne (Fintype.card K) m) = _ ∧
    moment (W.val.map Φ.toLinearMap) (exponentTwo (Fintype.card K) m) = _ at h
  obtain ⟨h0, h1, h2⟩ := h
  obtain ⟨hd0, hd1, hd2⟩ := exponents_pos (Fintype.card K) m hQ hm
  change (momentFunctional Φ _ (incidenceWord E W),
    momentFunctional Φ _ (incidenceWord E W) + β * momentFunctional Φ _ (incidenceWord E W)) = _
  rw [momentFunctional_incidence Φ _ hd0, momentFunctional_incidence Φ _ hd1,
    momentFunctional_incidence Φ _ hd2, h0, h1, h2]
  simp only [map_mul, map_neg]
  congr 1
  ring

omit [Fintype V] in
/-- A scalar outside the intermediate field encodes two field coefficients
injectively into one syndrome slope. -/
theorem affine_coefficients_injective (β : E) (hβ : β ∉ Set.range (algebraMap V E))
    (a b c d : V)
    (he : algebraMap V E a + β * algebraMap V E b =
      algebraMap V E c + β * algebraMap V E d) : a = c ∧ b = d := by
  have hb : b = d := by
    by_contra hbd
    have hn : algebraMap V E b - algebraMap V E d ≠ 0 := by
      rw [← map_sub]
      exact (map_ne_zero (algebraMap V E)).mpr (sub_ne_zero.mpr hbd)
    apply hβ
    refine ⟨(c - a) / (b - d), ?_⟩
    rw [map_div₀, map_sub, map_sub]
    apply (div_eq_iff hn).mpr
    linear_combination -he
  refine ⟨?_, hb⟩
  subst d
  have ha : algebraMap V E a = algebraMap V E c := add_right_cancel he
  exact (algebraMap V E).injective ha

/-- Nonzero multiples of two distinct affine slopes form an independent pair. -/
theorem independent_scaled_affine_pairs (u v s t : E) (hu : u ≠ 0) (hv : v ≠ 0)
    (hst : s ≠ t) : LinearIndependent E ![(u, -u * s), (v, -v * t)] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have h1 : a * u + b * v = 0 := by simpa using congrArg Prod.fst hab
  have h2 : a * (-u * s) + b * (-v * t) = 0 := by simpa using congrArg Prod.snd hab
  have hp : (a * u) * (s - t) = 0 := by linear_combination -h2 - t * h1
  have ha : a = 0 := (mul_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right
    (sub_ne_zero.mpr hst))).resolve_right hu
  refine ⟨ha, ?_⟩
  rw [ha, zero_mul, zero_add] at h1
  exact (mul_eq_zero.mp h1).resolve_right hv

/-- The first coordinate of every incidence syndrome is nonzero. This stronger
normalization property survives the finite-field existence construction. -/
theorem syndromeMap_incidence_fst_ne_zero (Φ : (Fin m → K) ≃ₗ[K] V) (β : E)
    (hm : 4 ≤ m) (hQ : 2 < Fintype.card K) (W : CodimTwo K m) :
    (syndromeMap Φ β (incidenceWord E W)).1 ≠ 0 := by
  rw [syndromeMap_incidence Φ β hm hQ W]
  exact (map_ne_zero (algebraMap V E)).mpr (rootProduct_coeff_one_ne_zero _)

/-- The first moment makes every incidence syndrome nonzero. -/
theorem syndromeMap_incidence_ne_zero (Φ : (Fin m → K) ≃ₗ[K] V) (β : E)
    (hm : 4 ≤ m) (hQ : 2 < Fintype.card K) (W : CodimTwo K m) :
    syndromeMap Φ β (incidenceWord E W) ≠ 0 := by
  rw [syndromeMap_incidence Φ β hm hQ W]
  intro h
  have hz := congrArg Prod.fst h
  exact (map_ne_zero (algebraMap V E)).mpr (rootProduct_coeff_one_ne_zero _) hz

/-- The constructed map separates every pair of distinct incidence directions,
under an explicit ordinary field tower and a scalar outside the middle field. -/
theorem syndromeMap_incidence_pair_independent (Φ : (Fin m → K) ≃ₗ[K] V)
    (β : E) (hβ : β ∉ Set.range (algebraMap V E))
    (hm : 4 ≤ m) (hQ : 2 < Fintype.card K)
    (W T : CodimTwo K m) (hne : W ≠ T) :
    LinearIndependent E ![syndromeMap Φ β (incidenceWord E W),
      syndromeMap Φ β (incidenceWord E T)] := by
  rw [syndromeMap_incidence Φ β hm hQ W, syndromeMap_incidence Φ β hm hQ T]
  apply independent_scaled_affine_pairs
  · exact (map_ne_zero (algebraMap V E)).mpr (rootProduct_coeff_one_ne_zero _)
  · exact (map_ne_zero (algebraMap V E)).mpr (rootProduct_coeff_one_ne_zero _)
  · intro he
    obtain ⟨h1, h2⟩ := affine_coefficients_injective β hβ _ _ _ _ he
    have hdim : Module.finrank K V = m := by
      rw [← Φ.finrank_eq]
      simp [Module.finrank_fintype_fun_eq_card]
    have hW : Module.finrank K (W.val.map Φ.toLinearMap) + 2 = m := by
      rw [← (Φ.submoduleMap W.val).finrank_eq]
      exact W.property
    have hT : Module.finrank K (T.val.map Φ.toLinearMap) + 2 = m := by
      rw [← (Φ.submoduleMap T.val).finrank_eq]
      exact T.property
    have heq := rootProduct_top_two_determine_subspace m hm hdim
      (W.val.map Φ.toLinearMap) (T.val.map Φ.toLinearMap) hW hT h1 h2
    apply hne
    apply Subtype.ext
    exact Submodule.map_injective_of_injective Φ.injective heq

/-- Restrict the concrete full-space map to the paper's actual extended
incidence code. This theorem assumes an ordinary finite-field tower and a
coordinate equivalence, not a syndrome or geometric-classification premise.
Constructing the tower from cardinalities is a separate field-theory step. -/
theorem exists_separating_syndrome_of_tower
    {p : ℕ} [Fact p.Prime]
    {K V E : Type} [Field K] [Fintype K] [Field V] [Fintype V] [Algebra K V]
    [Field E] [Algebra V E] [Algebra (ZMod p) E]
    {m : ℕ} (hm : 4 ≤ m) (hQ : 2 < Fintype.card K)
    (Φ : (Fin m → K) ≃ₗ[K] V) (β : E) (hβ : β ∉ Set.range (algebraMap V E)) :
    ∃ ψ : extendCode (K := E) (incidenceSpan K (ZMod p) m) →ₗ[E] (E × E),
      (∀ W : CodimTwo K m, ψ (Targets.extendedIncidence W) ≠ 0) ∧
      ∀ W T : CodimTwo K m, W ≠ T →
        LinearIndependent E ![ψ (Targets.extendedIncidence W), ψ (Targets.extendedIncidence T)] := by
  classical
  let D := extendCode (K := E) (incidenceSpan K (ZMod p) m)
  let ψ := (syndromeMap Φ β).comp D.subtype
  have he (W : CodimTwo K m) : ψ (Targets.extendedIncidence W) =
      syndromeMap Φ β (incidenceWord E W) := by
    change syndromeMap Φ β (embedWord (incidenceWord (ZMod p) W)) = _
    congr 1
    funext P
    simp [embedWord, incidenceWord]
  refine ⟨ψ, ?_, ?_⟩
  · intro W
    rw [he]
    exact syndromeMap_incidence_ne_zero Φ β hm hQ W
  · intro W T hWT
    rw [he, he]
    exact syndromeMap_incidence_pair_independent Φ β hβ hm hQ W T hWT

end OneAndAHalfJohnson.SyndromeConstruction
