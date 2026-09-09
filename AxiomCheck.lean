import TheoremB.RiccatiTrap
import TheoremB.SpectralNorms
import TheoremB.ConditionalTheoremB
import TheoremB.FourierDeriv
import TheoremB.GalerkinTrap
import TheoremB.NSGalerkin
import TheoremB.RealityProp
import TheoremB.GalerkinLocal
import TheoremB.GalerkinFlow
import TheoremB.NSFull
import TheoremB.ModeExtraction
import TheoremB.FlowBounds
import TheoremB.LimitPassage
import TheoremB.LimitHelpers
import TheoremB.ConvContinuity
import TheoremB.TheoremBGlobal
import TheoremB.LatticeKernel
import TheoremB.DefectCalculus
import TheoremB.PairingBound
import TheoremB.TailBounds
import TheoremB.FullUnique
import TheoremB.TorusSynthesis
import TheoremB.TorusStructure
import TheoremB.SpectralWeak
import TheoremB.CoeffExtract
import TheoremB.TheoremBTorus
import TheoremB.PhysicalPairing
import TheoremB.TestSeparation
import TheoremB.LerayHopfVocab
import TheoremB.SobolevNorms
import TheoremB.SobolevPairing
import TheoremB.SobolevTrap
import TheoremB.TheoremBSobolev
import TheoremB.ContinuousRep
import TheoremB.PeriodicLift
import TheoremB.TimeLayer
import TheoremB.Calibration
import TheoremB.Nonlinearity
import TheoremB.TheoremBSmooth
import TheoremB.ClassicalEquation
import TheoremB.EnergyDecay
import TheoremB.Bandwidth
import TheoremB.WindowDecay
import TheoremB.EnergyIntegrable
import TheoremB.ModesWindow
import TheoremB.DeterminingModes
import TheoremB.ModesFlow
import TheoremB.ModesProbe
import TheoremB.GalerkinDecay
import TheoremB.DecayFlow
import TheoremB.ForcedTrap
import TheoremB.ForcedGalerkin
import TheoremB.ForcedGalerkinFlow

#print axioms TheoremB.trap_forward_invariance
#print axioms TheoremB.riccati_window
#print axioms TheoremB.summable_inv_freq_pow_four
#print axioms TheoremB.ens_sq_le_en_mul_dis
#print axioms TheoremB.exists_spec1_sq_le_dis
#print axioms TheoremB.exists_spec1_pow_four_le_ens_mul_dis
#print axioms TheoremB.triMaj_le
#print axioms TheoremB.master_inequality
#print axioms TheoremB.conditional_trap
#print axioms TheoremB.conditional_safety_window
#print axioms TheoremB.fourierCoeff_hasDerivAt
#print axioms TheoremB.mFourierCoeff_deriv
#print axioms TheoremB.galerkin_conditional_trap
#print axioms TheoremB.galerkin_safety_window
#print axioms TheoremB.convGal_energy_pairing
#print axioms TheoremB.convGal_enstrophy_pairing
#print axioms TheoremB.ns_galerkin_trap
#print axioms TheoremB.divFree_propagates
#print axioms TheoremB.ns_galerkin_trap_leray
#print axioms TheoremB.ns_galerkin_trap_leray'
#print axioms TheoremB.realField_propagates
#print axioms TheoremB.ns_galerkin_trap_zero_data
#print axioms TheoremB.defect_vanishes_on'
#print axioms TheoremB.divFree_propagates_on
#print axioms TheoremB.realField_propagates_on
#print axioms TheoremB.galerkin_conditional_trap_on
#print axioms TheoremB.two_flow_forcing_bound
#print axioms TheoremB.ns_galerkin_unique_on
#print axioms TheoremB.ns_galerkin_trap_zero_data_on
#print axioms TheoremB.gflow_local_exists
#print axioms TheoremB.gflow_to_coeff
#print axioms TheoremB.coeff_le_sqrt_en
#print axioms TheoremB.ns_galerkin_local_existence
#print axioms TheoremB.ns_galerkin_unique_around
#print axioms TheoremB.ns_galerkin_trap_zero_data_icc
#print axioms TheoremB.ns_galerkin_global_wellposed
#print axioms TheoremB.ns_galerkin_global_flow
#print axioms TheoremB.convFull_eq_convGal
#print axioms TheoremB.norm_convFull_le_sqrt
#print axioms TheoremB.norm_lerayProj_le
#print axioms TheoremB.tail_en_le_ens
#print axioms TheoremB.finite_freq_le
#print axioms TheoremB.en_truncate_le
#print axioms TheoremB.ens_truncate_le
#print axioms TheoremB.realField_truncate
#print axioms TheoremB.divFree_truncate
#print axioms TheoremB.boxS_symm
#print axioms TheoremB.exists_boxS
#print axioms TheoremB.isCompact_modeSet
#print axioms TheoremB.mode_extraction
#print axioms TheoremB.galRHS_norm_le
#print axioms TheoremB.flow_mode_lipschitzOnWith
#print axioms TheoremB.flow_mode_mem_modeSet
#print axioms TheoremB.tendsto_convFull_of_modes
#print axioms TheoremB.integral_eq_of_hasDerivAt_Icc
#print axioms TheoremB.hasDerivAt_of_integral_eq
#print axioms TheoremB.tendsto_intervalIntegral_of_tendstoUniformlyOn
#print axioms TheoremB.convFull_zero_of_divFree
#print axioms TheoremB.continuousOn_convGal
#print axioms TheoremB.en_limit_le
#print axioms TheoremB.ens_limit_le
#print axioms TheoremB.divFree_limit
#print axioms TheoremB.realField_limit
#print axioms TheoremB.tendsto_convFull_uniformlyOn
#print axioms TheoremB.continuousOn_convFull
#print axioms TheoremB.integral_equation_limit
#print axioms TheoremB.galerkin_family
#print axioms TheoremB.theorem_B
#print axioms TheoremB.summable_freq_rpow_neg
#print axioms TheoremB.kernel_sum_le
#print axioms TheoremB.weighted_interp
#print axioms TheoremB.mixed_convMaj_le
#print axioms TheoremB.convFull_sub
#print axioms TheoremB.inner_lerayProj_left
#print axioms TheoremB.hasDerivAt_finset_sum_sq
#print axioms TheoremB.conv_corr_sq_le
#print axioms TheoremB.pairing_absorbed
#print axioms TheoremB.en_sub_le
#print axioms TheoremB.tail_en_lt
#print axioms TheoremB.tail_source
#print axioms TheoremB.gronwall_const_source
#print axioms TheoremB.theorem_B_cont
#print axioms TheoremB.theorem_B_unique
#print axioms TheoremB.ns_full_global_flow
#print axioms TheoremB.mFourierCoeff_synth
#print axioms TheoremB.sum_norm_synthT_sq
#print axioms TheoremB.continuousOn_synthT
#print axioms TheoremB.calibrated_integral_equation
#print axioms TheoremB.mFourierCoeff_star
#print axioms TheoremB.synthT_real
#print axioms TheoremB.synthT_divFree_spectral
#print axioms TheoremB.pairing_transfer
#print axioms TheoremB.spectral_weak_equation
#print axioms TheoremB.mode_equation_of_weak
#print axioms TheoremB.extractCoeff_synthT
#print axioms TheoremB.en_extractCoeff
#print axioms TheoremB.convFull_pairing_physical
#print axioms TheoremB.L2_ext_of_coeff
#print axioms TheoremB.synthT_extractCoeff
#print axioms TheoremB.theorem_B_torus
#print axioms TheoremB.theorem_B_torus_unique
#print axioms TheoremB.linear_pairing_physical
#print axioms TheoremB.convection_pairing_physical
#print axioms TheoremB.band_tests_separate
#print axioms TheoremB.mFourier_span_dense
#print axioms LHRestate.mem_L2Sigma_iff
#print axioms TheoremB.sob_zero_eq_en
#print axioms TheoremB.sob_one_eq_ens
#print axioms TheoremB.sob_truncate_le
#print axioms TheoremB.weighted_limit_le
#print axioms TheoremB.hasDerivAt_weighted_finset_sum_sq
#print axioms TheoremB.freq_triangle
#print axioms TheoremB.two_pow_split
#print axioms TheoremB.norm_freq_pow_split
#print axioms TheoremB.sob_summable_of_le
#print axioms TheoremB.summable_weighted_norm
#print axioms TheoremB.sobolev_pairing_absorbed
#print axioms TheoremB.sob_zero_bound
#print axioms TheoremB.galerkin_sobolev_bound_of_pairing
#print axioms TheoremB.galerkin_sobolev_bound
#print axioms TheoremB.theorem_B_sobolev
#print axioms TheoremB.ns_full_global_flow_sobolev
#print axioms TheoremB.hasSum_uCont
#print axioms TheoremB.uCont_apply
#print axioms TheoremB.toLp_uCont
#print axioms TheoremB.mFourierCoeff_uCont
#print axioms TheoremB.norm_uCont_le
#print axioms TheoremB.uCont_real_apply
#print axioms TheoremB.uLift_periodic
#print axioms TheoremB.contDiff_uLift_term
#print axioms TheoremB.hasDerivAt_charSum_insertNth
#print axioms TheoremB.continuous_charSum
#print axioms TheoremB.continuous_charSum_deriv
#print axioms TheoremB.uLift_eq_charSum
#print axioms TheoremB.contDiff_uLift
#print axioms TheoremB.tsum_weighted_norm_le
#print axioms TheoremB.tsum_weighted_norm_le_of_bound
#print axioms TheoremB.summable_convMaj_l1
#print axioms TheoremB.summable_norm_convFull
#print axioms TheoremB.hasDerivAt_weighted_tsum_flow
#print axioms TheoremB.continuousOn_weighted_tsum
#print axioms TheoremB.weighted_convMaj_le
#print axioms TheoremB.norm_mode_le_of_sob
#print axioms TheoremB.norm_nsRHS_le
#print axioms TheoremB.exists_summable_nsRHS_maj
#print axioms TheoremB.sob_le_sob
#print axioms TheoremB.norm_mFourier_apply
#print axioms TheoremB.twistFreq_apply
#print axioms TheoremB.norm_twistFreq_le
#print axioms TheoremB.summable_twistFreq
#print axioms TheoremB.laplacian_symbol
#print axioms TheoremB.hasDerivAt_charSum_insertNth_second
#print axioms TheoremB.laplacian_charSum
#print axioms TheoremB.viscous_eq_laplacian
#print axioms TheoremB.tsum_char_mul
#print axioms TheoremB.pressureCoeff
#print axioms TheoremB.lerayProj_convFull_apply
#print axioms TheoremB.summable_pressureCoeff
#print axioms TheoremB.summable_freq_pressureCoeff
#print axioms TheoremB.exists_fiber
#print axioms TheoremB.convFull_apply
#print axioms TheoremB.convection_classical
#print axioms TheoremB.theorem_B_smooth_classical
#print axioms TheoremB.hasDerivAt_pressure_insertNth
#print axioms TheoremB.theorem_B_smooth_classical_eq
#print axioms TheoremB.theorem_B_smooth
#print axioms TheoremB.en_le_ens
#print axioms TheoremB.galerkin_energy_decay
#print axioms TheoremB.theorem_B_bandwidth
#print axioms TheoremB.decay_of_window_integral_ineq
#print axioms TheoremB.box_tendsto_atTop
#print axioms TheoremB.en_sec_tendsto
#print axioms TheoremB.aestronglyMeasurable_en
#print axioms TheoremB.intervalIntegrable_en
#print axioms TheoremB.box_subset
#print axioms TheoremB.modes_window_ineq
#print axioms TheoremB.theorem_B_modes
#print axioms TheoremB.modes_hypotheses_consistent
#print axioms TheoremB.mean_zero_along_flow
#print axioms TheoremB.ns_full_global_flow_modes
#print axioms TheoremB.probe2_low_mode_at_4E
#print axioms TheoremB.probe_modes_composes_with_flow
#print axioms TheoremB.ns_galerkin_decay_leray
#print axioms TheoremB.galerkin_family_decay
#print axioms TheoremB.theorem_B_decay_cont
#print axioms TheoremB.ns_full_global_flow_decay
#print axioms TheoremB.barrier_forward_invariance
#print axioms TheoremB.forced_trap_forward_invariance
#print axioms TheoremB.forced_conditional_trap
#print axioms TheoremB.forced_thresholds_inhabited
#print axioms TheoremB.force_energy_pairing_le
#print axioms TheoremB.force_enstrophy_pairing_le
#print axioms TheoremB.galerkin_forced_trap_on
#print axioms TheoremB.divFree_propagates_on_forced
#print axioms TheoremB.realField_propagates_on_forced
#print axioms TheoremB.ns_galerkin_forced_trap_on
#print axioms TheoremB.ns_galerkin_forced_trap_icc
#print axioms TheoremB.ns_galerkin_unique_on_forced
#print axioms TheoremB.probe_forced_zero_feeds_frozen
#print axioms TheoremB.gfield_norm_le_ball
#print axioms TheoremB.gfield_lip_ball
#print axioms TheoremB.gflow_local_exists_forced
#print axioms TheoremB.gflow_to_coeff_forced
#print axioms TheoremB.ns_galerkin_local_existence_forced
#print axioms TheoremB.coeff_shift_forced
#print axioms TheoremB.ns_galerkin_unique_around_forced
#print axioms TheoremB.ns_galerkin_global_wellposed_forced
#print axioms TheoremB.ns_galerkin_global_flow_forced
