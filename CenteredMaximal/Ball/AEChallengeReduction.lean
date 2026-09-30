/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.AEObstacleTransfer
public import CenteredMaximal.Ball.ChallengeReduction

/-!
# Ball bounds from almost-everywhere obstacle certificates

The local weak obstacle construction naturally supplies Green comparison at almost every center.
These are the final numerical reductions once those certificates are established.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric
open scoped ENNReal

namespace CenteredMaximal.Ball

/-- The planar challenge follows from an almost-everywhere direct obstacle certificate. -/
theorem ballWeakTypeConstant_two_le_exp_of_ae_direct_certificates
    (h : HasAEDirectObstacleCertificates planarKernel) :
    ballWeakTypeConstant 2 ≤ ENNReal.ofReal (Real.exp 1) := by
  exact ballWeakTypeConstant_le_of_ae_direct_obstacle_certificates
    planarKernel (ENNReal.ofReal (Real.exp 1))
    (by positivity) ENNReal.ofReal_ne_top
    one_le_planarKernel_on_unit_ball
    (fun x r hr ↦ planarKernel_normalized_mass x hr) h

/-- The higher-dimensional challenge follows from an almost-everywhere direct obstacle
certificate for the Newtonian kernel. -/
theorem ballWeakTypeConstant_le_rpow_of_ae_direct_certificates
    (n : ℕ) (hn : 3 ≤ n)
    (h : HasAEDirectObstacleCertificates (newtonianKernel n)) :
    ballWeakTypeConstant n ≤
      ENNReal.ofReal (((n : ℝ) / 2) ^ ((n : ℝ) / ((n : ℝ) - 2))) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hCpos : 0 < greenBound n := by
    unfold greenBound
    have hnreal : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hbase : 0 < (n : ℝ) / 2 := by positivity
    exact Real.rpow_pos_of_pos hbase _
  simpa only [greenBound] using
    ballWeakTypeConstant_le_of_ae_direct_obstacle_certificates
      (newtonianKernel n) (ENNReal.ofReal (greenBound n))
      (by exact ENNReal.ofReal_pos.mpr hCpos) ENNReal.ofReal_ne_top
      (one_le_newtonianKernel_on_unit_ball n hn)
      (fun x r hr ↦ lintegral_normalized_newtonianKernel n hn x hr) h

end CenteredMaximal.Ball
