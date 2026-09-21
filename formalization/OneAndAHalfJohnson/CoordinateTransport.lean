module
public import OneAndAHalfJohnson.Basic
/-! Coordinate relabelling preserves the code parameters used in the paper. -/
@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson
variable {F I J : Type*} [Field F] [DecidableEq F] [Fintype I] [Fintype J]
/-- Relabel a word along an equivalence of coordinate sets. -/
def reindexWord (e : I ≃ J) : (I → F) ≃ₗ[F] (J → F) :=
  LinearEquiv.funCongrLeft F F e.symm
/-- The same linear code on a relabelled coordinate set. -/
def reindexCode (e : I ≃ J) (C : Submodule F (I → F)) : Submodule F (J → F) :=
  C.map (reindexWord (F := F) e).toLinearMap
@[simp] theorem reindexWord_dist (e : I ≃ J) (v w : I → F) :
    hammingDist (reindexWord e v) (reindexWord e w) = hammingDist v w :=
by
  classical
  change hammingDist (fun j => v (e.symm j)) (fun j => w (e.symm j)) = _
  unfold hammingDist
  apply Finset.card_bij (fun j _ => e.symm j)
  · intro j hj
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hj
  · intro a ha b hb hab
    exact e.symm.injective hab
  · intro i hi
    exact ⟨e i, by simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply] using hi, e.symm_apply_apply i⟩
omit [DecidableEq F] [Fintype I] [Fintype J] in
@[simp] theorem mem_reindexCode (e : I ≃ J) (C : Submodule F (I → F)) (v : I → F) :
    reindexWord e v ∈ reindexCode e C ↔ v ∈ C := by
  simp [reindexCode]
@[simp] theorem reindexCode_close (e : I ≃ J) (C : Submodule F (I → F))
    (v : I → F) (ρ : ℝ) : Close (reindexCode e C) (reindexWord e v) ρ ↔ Close C v ρ := by
  constructor
  · rintro ⟨w, ⟨c, hc, rfl⟩, hd⟩
    exact ⟨c, hc, by simpa [Fintype.card_congr e] using hd⟩
  · rintro ⟨c, hc, hd⟩
    exact ⟨reindexWord e c, (mem_reindexCode e C c).2 hc,
      by simpa [Fintype.card_congr e] using hd⟩
@[simp] theorem reindexCode_far (e : I ≃ J) (C : Submodule F (I → F))
    (v : I → F) (ρ : ℝ) : Far (reindexCode e C) (reindexWord e v) ρ ↔ Far C v ρ := by
  constructor
  · intro h c hc
    simpa [Fintype.card_congr e] using h (reindexWord e c) ((mem_reindexCode e C c).2 hc)
  · intro h w hw
    obtain ⟨c, hc, rfl⟩ := hw
    simpa [Fintype.card_congr e] using h c hc
@[simp] theorem reindexCode_exceptional [Fintype F] (e : I ≃ J)
    (C : Submodule F (I → F)) (f g : I → F) (ρ : ℝ) :
    exceptional (reindexCode e C) (reindexWord e f) (reindexWord e g) ρ =
      exceptional C f g ρ := by
  ext z
  simp only [mem_exceptional, ← map_smul, ← map_add, reindexCode_close]
@[simp] theorem reindexCode_distance (e : I ≃ J) (C : Submodule F (I → F)) :
    Code.dist (reindexCode e C : Set (J → F)) = Code.dist (C : Set (I → F)) := by
  unfold Code.dist
  congr 1
  ext d
  constructor
  · rintro ⟨u, ⟨a, ha, rfl⟩, v, ⟨b, hb, rfl⟩, hn, hd⟩
    exact ⟨a, ha, b, hb, fun h => hn (congrArg (reindexWord e) h), by simpa using hd⟩
  · rintro ⟨a, ha, b, hb, hn, hd⟩
    exact ⟨reindexWord e a, (mem_reindexCode e C a).2 ha,
      reindexWord e b, (mem_reindexCode e C b).2 hb,
      fun h => hn ((reindexWord e).injective h), by simpa using hd⟩
@[simp] theorem reindexCode_relativeDistance (e : I ≃ J) (C : Submodule F (I → F)) :
    relativeDistance (reindexCode e C) = relativeDistance C := by
  simp [relativeDistance, Fintype.card_congr e]
omit [DecidableEq F] in
@[simp] theorem reindexCode_rate (e : I ≃ J) (C : Submodule F (I → F)) :
    rate (reindexCode e C) = rate C := by
  rw [rate, rate, reindexCode, LinearEquiv.finrank_map_eq]
  rw [Fintype.card_congr e]
end OneAndAHalfJohnson
