import AltOMD

/-! Build with `lake build AltOMD.Audit`, then run
`lake env lean AltOMD/Audit.lean` to inspect the trusted kernel
axioms. This audits the manuscript's BCH proposition, its application,
the final regret specialization, and supporting algebraic results, as well as
relative-gradient geometry, interior preservation, and trajectory existence. -/

#print axioms AltOMD.poissonBracket_jacobi
#print axioms AltOMD.Duality.fenchel_legendre_identities
#print axioms AltOMD.FormalEnergy.correctedHamiltonian_preserved
#print axioms AltOMD.norm_mixed_correction_le
#print axioms AltOMD.sum_le_four_thirds_first
#print axioms AltOMD.quartic_horizon_bound
#print axioms AltOMD.logarithmic_regret
#print axioms AltOMD.BilinearRegret.logarithmic_regret
#print axioms AltOMD.BilinearRegret.logarithmic_regret_of_primal_initialization
#print axioms AltOMD.PrimalDualStep.mirror_step_gradient_update
#print axioms AltOMD.ConjugateFeasibility.gradient_mem_and_conjugate_eq
#print axioms AltOMD.ConjugateFeasibility.compact_mirror_step
#print axioms AltOMD.PrimalRegret.gradient_dualLift
#print axioms AltOMD.PrimalRegret.logarithmic_regret
#print axioms AltOMD.PrimalRegret.logarithmic_regret_of_compact
#print axioms AltOMD.differentiableWithinAt_iff_affineChart
#print axioms AltOMD.relativeGradient_eq_gradient_affineChart
#print axioms AltOMD.LegendreBoundary.gradientBlowsUpAtBoundary_iff_intrinsicFrontier
#print axioms AltOMD.LegendreBoundary.mem_intrinsicInterior_of_support
#print axioms AltOMD.LegendreMirror.mirror_minimizer_mem_intrinsicInterior
#print axioms AltOMD.LegendreMirror.gradient_conjugate_mem_intrinsicInterior
#print axioms AltOMD.LegendreMirror.compact_mirror_step_interior
#print axioms AltOMD.LegendreTrajectory.IsPrimalMirrorTrajectory.interior
#print axioms AltOMD.LegendreTrajectory.IsPrimalMirrorTrajectory.toIsMirrorTrajectory
#print axioms AltOMD.LegendreTrajectory.exists_alternating_primal_trajectories
#print axioms AltOMD.LegendreRegret.logarithmic_regret

-- Reusable algebraic ingredients. These queries do not turn a theorem
-- hypothesis (such as the four-term defect condition) into a proved fact.
#print axioms PowerSeries.log_subst_exp_sub_one
#print axioms PowerSeries.exp_subst_log
#print axioms AltOMD.NoncommutativeSeries.evalAlgHom
#print axioms AltOMD.NoncommutativeSeries.eval_subst
#print axioms AltOMD.NoncommutativeSeries.expOf_logOf
#print axioms AltOMD.NoncommutativeSeries.logOf_expOf
#print axioms AltOMD.NoncommutativeSeries.bch_associative
#print axioms AltOMD.NoncommutativeSeries.bch_neg
#print axioms AltOMD.NoncommutativeSeries.bchCoefficient_smul
#print axioms AltOMD.NoncommutativeSeries.bchCoefficient_mem_of_four_term
#print axioms AltOMD.DynkinProjection.dynkin_mul_of_isLie
#print axioms AltOMD.BCHLieCriterion.mem_of_four_term
#print axioms AltOMD.BCHCoefficients.classicalDSWInput
#print axioms AltOMD.SeriesAction.act_mul
#print axioms AltOMD.SeriesAction.act_eval_exp

-- The full BCH theorem and the exact project specialization.
#print axioms AltOMD.BCH.propositionA1
#print axioms AltOMD.BCH.existsUnique_bch
#print axioms AltOMD.BCH.Phi_eq_dynkin
#print axioms AltOMD.NoncommutativeSeries.universalCoefficient_homogeneous
#print axioms AltOMD.NoncommutativeSeries.universalCoefficient_isLie
#print axioms AltOMD.NoncommutativeSeries.bchCoefficient_isLie
#print axioms AltOMD.NoncommutativeSeries.coeff_bch_eq_sum_bchCoefficient
#print axioms AltOMD.DynkinProjection.dynkin_eq_degree_smul_of_isLie
#print axioms AltOMD.DynkinProjection.inv_degree_smul_dynkin_of_isLie
#print axioms AltOMD.CompositionCoefficients.weighted_coeff_pow_sum
#print axioms AltOMD.WordSeries.coeff_lift_degree
#print axioms AltOMD.WordSeries.coeff_lift_eq_of_lt
#print axioms AltOMD.BCHTheorem.classicalBCHInput
#print axioms AltOMD.VerifiedRegret.logarithmic_regret

-- Concrete Shannon entropy, the appendix's analytic estimates, and the
-- alternating multiplicative-weights corollary with all inputs supplied.
#print axioms AltOMD.WeightedSeries.completeSpace
#print axioms AltOMD.WeightedSeries.coeff_ofCoefficients
#print axioms AltOMD.WeightedSeries.ofCoefficients_coeff
#print axioms AltOMD.WeightedSeries.norm_eq_weighted_sum
#print axioms AltOMD.WeightedSeries.coeff_mul
#print axioms AltOMD.WeightedSeries.norm_mul_le
#print axioms AltOMD.WeightedSeries.sum_eq
#print axioms AltOMD.WeightedSeries.iteratedDeriv_eq
#print axioms AltOMD.WeightedSeries.abs_iteratedDeriv_le
#print axioms AltOMD.Polarization.identity
#print axioms AltOMD.Polarization.real_polarization
#print axioms AltOMD.Polarization.exists_diagonal_norm_eq
#print axioms AltOMD.Polarization.norm_eq_diagonal_sup
#print axioms AltOMD.Polarization.euclidean_norm_eq_diagonal_sup
#print axioms AltOMD.Shannon.strictConvexOn_entropy
#print axioms AltOMD.Shannon.mem_intrinsicInterior_iff
#print axioms AltOMD.Shannon.contDiffOn_entropy_intrinsicInterior
#print axioms AltOMD.Shannon.gradientBlowsUpAtBoundary_entropy
#print axioms AltOMD.Shannon.effectiveDomain_extendedEntropy
#print axioms AltOMD.Shannon.extendedEntropy_proper
#print axioms AltOMD.Shannon.lowerSemicontinuous_extendedEntropy
#print axioms AltOMD.Shannon.convex_epigraph_extendedEntropy
#print axioms AltOMD.Shannon.isClosed_epigraph_extendedEntropy
#print axioms AltOMD.Shannon.extendedEntropy_fenchel_eq_logSumExp
#print axioms AltOMD.Shannon.conjugate_eq_logSumExp
#print axioms AltOMD.Shannon.gradient_conjugate
#print axioms AltOMD.Shannon.contDiff_logSumExp
#print axioms AltOMD.Shannon.norm_iteratedFDeriv_logSumExp_le_sharp
#print axioms AltOMD.Shannon.norm_iteratedFDeriv_logSumExp_le_manuscript
#print axioms AltOMD.Shannon.sup_norm_iteratedFDeriv_logSumExp_le_manuscript
#print axioms AltOMD.Shannon.norm_iteratedFDeriv_logSumExp_le
#print axioms AltOMD.Shannon.bregman_eq_kl
#print axioms AltOMD.Shannon.supremum_bregman_le_radius
#print axioms AltOMD.Shannon.uniform_pair_radius
#print axioms AltOMD.Shannon.softmax_sub_smul
#print axioms AltOMD.Shannon.minimizes_iff_multiplicativeWeights
#print axioms AltOMD.Shannon.isMirrorTrajectory_iff_multiplicativeWeights
#print axioms AltOMD.Shannon.multiplicativeWeights_isPrimalMirrorTrajectory
#print axioms AltOMD.Shannon.sum_sup_derivatives_le
#print axioms AltOMD.Shannon.gameConstant_four
#print axioms AltOMD.Shannon.logarithmic_regret
#print axioms AltOMD.Shannon.alternatingWeights_regret
#print axioms AltOMD.Shannon.logarithmic_regret_uniform
#print axioms AltOMD.Shannon.alternatingWeights_regret_uniform

-- Canonical source statements and literal source-domain representations.
#print axioms AltOMD.VerifiedRegret.logarithmic_regret_two_bounds
#print axioms AltOMD.VerifiedRegret.logarithmic_regret_source
#print axioms AltOMD.CanonicalHamiltonian.bilinear_formal_preservation
#print axioms AltOMD.CanonicalHamiltonian.bilinear_correction_representation_and_bound
#print axioms AltOMD.CanonicalHamiltonian.bilinear_truncated_defect_coefficient_eq_zero
#print axioms AltOMD.canonical_bilinear_modified_energy_estimates
#print axioms AltOMD.Shannon.simplexWeights_apply
#print axioms AltOMD.Shannon.alternatingSimplex_coe
#print axioms AltOMD.Shannon.alternatingSimplex_regret
#print axioms AltOMD.Shannon.alternatingSimplex_regret_uniform

-- Manuscript assumptions and conclusions, including extended-real regularizers.
#print axioms AltOMD.ScalarMajorant.inverseSquare_eq
#print axioms AltOMD.ScalarMajorant.lie_derivative_majorant
#print axioms AltOMD.ScalarMajorant.lie_derivative_majorant_source_ereal
#print axioms AltOMD.ManuscriptBounds.nested_bracket_bound
#print axioms AltOMD.ManuscriptBounds.nested_bracket_bound_source
#print axioms AltOMD.ManuscriptBounds.canonical_mixed_bound_of_nested
#print axioms AltOMD.ManuscriptBounds.canonical_mixed_bound_source
#print axioms AltOMD.BilinearSystem.taylor_remainder_source
#print axioms AltOMD.Polarization.euclidean_polarization
#print axioms AltOMD.ExtendedDuality.fenchel_legendre_identities
#print axioms AltOMD.Decomposition.regret_decomposition_all
#print axioms AltOMD.ExtendedRegret.logarithmic_regret
#print axioms AltOMD.ExtendedRegret.regret_decomposition_all
#print axioms AltOMD.Shannon.isLegendre_extendedEntropy
