module

public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Avoiding a finite forbidden set while enlarging a code

A deterministic greedy alternative to the random-supercode completion on
pp. 15 and 20 of ePrint 2026/1894. Cardinality bounds ensure there is a new
vector outside every span of the current code and one forbidden word.
The actual forbidden sets and their Hamming-ball bounds remain separate.
-/

@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson

variable {F V : Type*} [Field F] [Fintype F] [AddCommGroup V] [Module F V]
  [Fintype V] [Module.Finite F V]

/-- One extra dimension can be added while avoiding all forbidden vectors. -/
theorem exists_avoiding_supercode_step
    (C : Submodule F V) (B : Finset V) (hB : B.Nonempty)
    (havoid : ∀ b ∈ B, b ∉ C)
    (hsize : B.card * Fintype.card F ^ (Module.finrank F C + 1) < Fintype.card V) :
    ∃ C' : Submodule F V, C ≤ C' ∧
      Module.finrank F C' = Module.finrank F C + 1 ∧ ∀ b ∈ B, b ∉ C' := by
  classical
  let T (b : V) : Finset V := Finset.univ.filter (fun v => v ∈ C ⊔ F ∙ b)
  have hcard (b : V) (hb : b ∈ B) :
      (T b).card = Fintype.card F ^ (Module.finrank F C + 1) := by
    have he : (T b).card = Fintype.card ↥(C ⊔ F ∙ b) := by
      simp [T, Fintype.card_subtype]
    rw [he, Module.card_eq_pow_finrank (K := F), Submodule.finrank_sup_span_singleton (havoid b hb)]
  have hunion : (B.biUnion T).card < Fintype.card V := by
    calc
      (B.biUnion T).card ≤ ∑ b ∈ B, (T b).card := Finset.card_biUnion_le
      _ = B.card * Fintype.card F ^ (Module.finrank F C + 1) := by
        rw [Finset.sum_congr rfl (fun b hb => hcard b hb)]
        simp
      _ < Fintype.card V := hsize
  obtain ⟨v, _, hv⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show (B.biUnion T).card < (Finset.univ : Finset V).card by simpa using hunion)
  have hvb (b : V) (hb : b ∈ B) : v ∉ C ⊔ F ∙ b := by
    intro h
    exact hv (Finset.mem_biUnion.mpr ⟨b, hb, by simp [T, h]⟩)
  have hvC : v ∉ C := by
    obtain ⟨b, hb⟩ := hB
    exact fun h => hvb b hb (Submodule.mem_sup_left h)
  refine ⟨C ⊔ F ∙ v, le_sup_left, Submodule.finrank_sup_span_singleton hvC, ?_⟩
  intro b hb hmem
  have hle : C ⊔ F ∙ b ≤ C ⊔ F ∙ v :=
    sup_le le_sup_left ((Submodule.span_singleton_le_iff_mem _ _).mpr hmem)
  have heq : C ⊔ F ∙ b = C ⊔ F ∙ v :=
    Submodule.eq_of_le_of_finrank_eq hle (by
      rw [Submodule.finrank_sup_span_singleton (havoid b hb),
        Submodule.finrank_sup_span_singleton hvC])
  apply hvb b hb
  rw [heq]
  exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)

/-- Enlarge to any prescribed dimension whose forbidden-span cardinality bound
fits in the ambient space. This is an existence theorem with only a numerical
size hypothesis, not an assumption that a suitable supercode already exists. -/
theorem exists_avoiding_supercode
    (C₀ : Submodule F V) (B : Finset V) (hB : B.Nonempty)
    (havoid : ∀ b ∈ B, b ∉ C₀) (K : ℕ)
    (hK : Module.finrank F C₀ ≤ K)
    (hsize : B.card * Fintype.card F ^ K < Fintype.card V) :
    ∃ C : Submodule F V, C₀ ≤ C ∧ Module.finrank F C = K ∧
      ∀ b ∈ B, b ∉ C := by
  induction K with
  | zero =>
    exact ⟨C₀, le_rfl, Nat.eq_zero_of_le_zero hK, havoid⟩
  | succ K ih =>
    by_cases heq : Module.finrank F C₀ = K + 1
    · exact ⟨C₀, le_rfl, heq, havoid⟩
    have hK' : Module.finrank F C₀ ≤ K := by omega
    have hsize' : B.card * Fintype.card F ^ K < Fintype.card V := by
      apply lt_of_le_of_lt _ hsize
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right Fintype.card_pos (Nat.le_succ K))
    obtain ⟨C, hC, hdim, hCB⟩ := ih hK' hsize'
    obtain ⟨C', hCC', hdim', hC'B⟩ := exists_avoiding_supercode_step C B hB hCB (by
      simpa only [hdim] using hsize)
    exact ⟨C', hC.trans hCC', by simpa only [hdim] using hdim', hC'B⟩

/-- The enlargement criterion in the dimension-and-field-size form used for
code completion. The ambient dimension bound follows from the strict cardinality
inequality; it need not be imposed as a separate assumption. -/
theorem exists_avoiding_supercode_of_pow_bound
    (C₀ : Submodule F V) (B : Finset V) (hB : B.Nonempty)
    (havoid : ∀ b ∈ B, b ∉ C₀) (K : ℕ)
    (hK : Module.finrank F C₀ ≤ K)
    (hsize : B.card * Fintype.card F ^ K <
      Fintype.card F ^ Module.finrank F V) :
    ∃ C : Submodule F V, C₀ ≤ C ∧ Module.finrank F C = K ∧
      ∀ b ∈ B, b ∉ C := by
  apply exists_avoiding_supercode C₀ B hB havoid K hK
  rw [Module.card_eq_pow_finrank (K := F) (V := V)]
  exact hsize

end OneAndAHalfJohnson
