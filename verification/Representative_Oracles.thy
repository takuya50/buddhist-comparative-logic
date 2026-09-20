(* SPDX-License-Identifier: Apache-2.0 *)

theory Representative_Oracles
  imports
    Buddhist_Comparative_Logic.FDEProofTheory
    Buddhist_Comparative_Logic.HeartSutra_Emptiness
    Buddhist_Comparative_Logic.Dignaga_Hetucakra
    Buddhist_Comparative_Logic.Jaina_Saptabhangi
begin

thm_oracles
  fde_variable_sharing
  fde5_is_fde_plus_containment
  fde_dec_correct
  fde_countermodel_sound
  fde_countermodel_none_iff
  fde_countermodel_complete
  fde5_countermodel_sound
  fde5_countermodel_none_iff
  fde5_countermodel_complete
  countermodel_explosion
  countermodel_conj_elim
  countermodel5_atom_escape
  countermodel5_same_atoms
  emptiness.sarva_dharma_sunya
  sarva_dharma_sunya_from_core
  emptiness_without_mmk
  emptiness_without_pratitya
  emptiness_core_relative_independence
  hs10_fde_formula_iff_B
  anumana.wheel_valid_iff
  anumana.uniformity_iff_thesis_under_marks
  no_deductive_soundness
  saptabhangi_not_truth_functional
  all_seven_satisfiable
  seventh_mode_needs_three_nayas
  seventh_mode_supports_every_mode
  naya_small_model
  naya_small_model_UNIV
  naya_small_model_bound_sharp
  observation_variants_same_profile
  observation_variants_different_relation
  naya_profile_cannot_recover_relation

end
