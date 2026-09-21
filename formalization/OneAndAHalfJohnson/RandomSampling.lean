module

public import OneAndAHalfJohnson.RandomFunctional
public import OneAndAHalfJohnson.Amplification

/-!
# The paper's concrete linear amplification experiment

A row chooses t input coordinates with replacement and a linear functional
on the selected extension-field symbols. All choices are finite, and the
resulting map is genuinely linear over the output field.
-/

@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson

variable {F E I J : Type*} [Field F] [Field E] [Algebra F E]

/-- One coordinate sample together with its output-field linear functional. -/
abbrev SamplingRow (F E I : Type*) [Field F] [Field E] [Algebra F E] (t : ℕ) :=
  (Fin t → I) × Module.Dual F (Fin t → E)

/-- Actual sampled linear map, including alphabet reduction. -/
def sampledLinearMap {t : ℕ} (ω : J → SamplingRow F E I t) :
    (I → E) →ₗ[F] (J → F) where
  toFun v j := (ω j).2 (fun k => v ((ω j).1 k))
  map_add' u v := by
    funext j
    exact map_add (ω j).2 _ _
  map_smul' a v := by
    funext j
    exact map_smul (ω j).2 a _

/-- Coordinate sampling yields the all-zero tuple precisely when every
sampled coordinate is a zero of the input word. -/
theorem sampled_tuple_zero_iff (t : ℕ) (v : I → E) (s : Fin t → I) :
    (fun k => v (s k)) = 0 ↔ ∀ k, v (s k) = 0 := by
  exact funext_iff

/-- Exact with-replacement count of all-zero coordinate samples. -/
theorem zero_tuple_sample_count [Fintype I] [DecidableEq E]
    (t : ℕ) (v : I → E) :
    (Finset.univ.filter (fun s : Fin t → I => (fun k => v (s k)) = 0)).card =
      (Finset.univ.filter (fun i : I => v i = 0)).card ^ t := by
  classical
  let e : {s : Fin t → I // (fun k => v (s k)) = 0} ≃
      (Fin t → {i : I // v i = 0}) :=
    { toFun := fun s k => ⟨s.val k, congrFun s.property k⟩
      invFun := fun s => ⟨fun k => (s k).val, funext (fun k => (s k).property)⟩
      left_inv := by intro s; rfl
      right_inv := by intro s; rfl }
  simpa only [Fintype.card_subtype, Fintype.card_fun, Fintype.card_fin] using
    Fintype.card_congr e

/-- Enumeration of the finite set of output-field linear functionals. -/
noncomputable instance sampledDualFintype [Fintype F] [Fintype E] (t : ℕ) :
    Fintype (Module.Dual F (Fin t → E)) := by
  classical
  exact Fintype.ofInjective (fun φ => (φ : (Fin t → E) → F)) DFunLike.coe_injective

/-- Exact one-row success count, before normalization into a probability.
Coordinates are sampled with replacement and the functional is uniform. -/
theorem sampled_row_nonzero_count [Fintype F] [Fintype E] [Fintype I]
    [DecidableEq F] [DecidableEq E] (t : ℕ) (v : I → E) :
    Fintype.card F * (Finset.univ.filter (fun r : SamplingRow F E I t =>
      r.2 (fun k => v (r.1 k)) ≠ 0)).card =
      (Fintype.card I ^ t - (Finset.univ.filter (fun i : I => v i = 0)).card ^ t) *
        Fintype.card (Module.Dual F (Fin t → E)) * (Fintype.card F - 1) := by
  classical
  let x (s : Fin t → I) : Fin t → E := fun k => v (s k)
  have hsum : (Finset.univ.filter (fun r : SamplingRow F E I t => r.2 (x r.1) ≠ 0)).card =
      ∑ s : Fin t → I, (Finset.univ.filter
        (fun φ : Module.Dual F (Fin t → E) => φ (x s) ≠ 0)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [← Finset.univ_product_univ, Finset.sum_product]
  have hcount : (Finset.univ.filter (fun s : Fin t → I => x s ≠ 0)).card =
      Fintype.card I ^ t - (Finset.univ.filter (fun i : I => v i = 0)).card ^ t := by
    have hh := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin t → I))) (p := fun s => x s = 0)
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at hh
    have hz := zero_tuple_sample_count t v
    change (Finset.univ.filter (fun s : Fin t → I => x s = 0)).card = _ at hz
    have heq : (Finset.univ.filter (fun s : Fin t → I => x s ≠ 0)).card +
        (Finset.univ.filter (fun i : I => v i = 0)).card ^ t = Fintype.card I ^ t := by
      simpa only [hz, add_comm] using hh
    omega
  change Fintype.card F * (Finset.univ.filter
    (fun r : SamplingRow F E I t => r.2 (x r.1) ≠ 0)).card = _
  rw [hsum, Finset.mul_sum]
  calc
    _ = ∑ s : Fin t → I, if x s ≠ 0 then
        Fintype.card (Module.Dual F (Fin t → E)) * (Fintype.card F - 1) else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      by_cases hx : x s = 0
      · simp [hx]
      · simpa only [ite_eq_left hx] using dual_evaluation_nonzero_count (F := F) hx
    _ = (Finset.univ.filter (fun s : Fin t → I => x s ≠ 0)).card *
        (Fintype.card (Module.Dual F (Fin t → E)) * (Fintype.card F - 1)) := by
      rw [← Finset.sum_filter]
      simp
    _ = _ := by rw [hcount]; ring

end OneAndAHalfJohnson
