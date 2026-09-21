module
public import OneAndAHalfJohnson.ConcreteProbabilityCalculus
@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson.ConcreteAnalyticBounds

def rowSlope (w : ℝ) : ℝ :=
  (1-1/(2:ℝ)^128)*52500/68853957121*(1-w/68853957121)^52499

def layerExponent (a c w : ℝ) : ℝ :=
  w*(1+Real.log (68853957121/w)) + (w-784895)*c -
    2^36*bernoulliKL a (rowProbability w)

theorem hasDerivAt_layerExponent {a c w : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hw0 : 0 < w) (hwn : w ≤ 68853957121) :
    HasDerivAt (layerExponent a c)
      (Real.log (68853957121/w)+c -
        2^36*((rowProbability w-a)/(rowProbability w*(1-rowProbability w)))*rowSlope w) w := by
  have hp := rowProbability_mem_Ioo hw0 hwn
  have hlog := (((hasDerivAt_const w (68853957121:ℝ)).div (hasDerivAt_id w)
    (ne_of_gt hw0)).log (ne_of_gt (div_pos (by norm_num) hw0)))
  have hcount := (hasDerivAt_id w).mul ((hasDerivAt_const w 1).add hlog)
  have hKL := ((hasDerivAt_bernoulliKL ha0 ha1 hp.1 hp.2).comp w
    (hasDerivAt_rowProbability w)).const_mul ((2:ℝ)^36)
  have hlin := ((hasDerivAt_id w).sub_const 784895).mul_const c
  convert (hcount.add hlin).sub hKL using 1
  · rfl
  · dsimp
    unfold rowSlope
    generalize (1-w/68853957121)^52499 = z
    field_simp
    ring

end OneAndAHalfJohnson.ConcreteAnalyticBounds
