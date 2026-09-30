/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Numerics
public import CenteredMaximal.UpperBound
public import CenteredMaximal.Cauchy.Representation
public import CenteredMaximal.Lattice.LowerBound
public import CenteredMaximal.Ball.PlanarNormalized
public import CenteredMaximal.Ball.NewtonianMass
public import CenteredMaximal.Ball.ObstacleCriterion
public import CenteredMaximal.Ball.SmoothReduction
public import CenteredMaximal.Ball.PairingComparison
public import CenteredMaximal.Ball.GreenIdentity
public import CenteredMaximal.Ball.RadialGreenCalculus
public import CenteredMaximal.Ball.RadialMassDerivative
public import CenteredMaximal.Ball.RadialGreenLimit
public import CenteredMaximal.Ball.ObstacleExistence
public import CenteredMaximal.Ball.ChallengeReduction
public import CenteredMaximal.Ball.PlanarGreenPairing
public import CenteredMaximal.Ball.DirichletForm
public import CenteredMaximal.Ball.DirichletPoincareOneDim
public import CenteredMaximal.Ball.DirichletPoincareBounded
public import CenteredMaximal.Ball.ContactTruncation
public import CenteredMaximal.Ball.MonotoneSurjectivity
public import CenteredMaximal.Ball.L2Penalty
public import CenteredMaximal.Ball.BallPenalized
public import CenteredMaximal.Ball.BallSourceL2
public import CenteredMaximal.Ball.PenaltyCapSource
public import CenteredMaximal.Ball.L2PenaltyCap
public import CenteredMaximal.Ball.BallPenaltyCap
public import CenteredMaximal.Ball.PenaltyEnergyBound
public import CenteredMaximal.Ball.BallPenaltyLimit
public import CenteredMaximal.Ball.AEObstacleTransfer
public import CenteredMaximal.Ball.BallWeakDistribution

/-!
# The weak type constant of the centred maximal operator over cubes

The root module exports the upper bounds `c_d ≤ 2ᵈ` and `c₂ ≤ 3.879`, and the lower bound
`Φ ≤ c₂`. The Euclidean ball extension currently exports exact Green-kernel masses,
an obstacle-certificate criterion, and preparatory Dirichlet and Green-pairing results.
-/
