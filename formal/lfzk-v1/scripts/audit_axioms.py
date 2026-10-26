#!/usr/bin/env python3
"""Axiom audit for the Longfellow NIZK development.

Runs `#print axioms` on every headline theorem and checks that each depends only on Lean's
foundational axioms (`propext`, `Classical.choice`, `Quot.sound`), plus — for the theorems stated
at a certified row — the `native_decide` auxiliaries that the row's own `native_decide` checks
own (`Lean.ofReduceBool`, and in Lean 4.31 the per-call `<decl>._native.native_decide.ax_i_j`).
Long axiom lists are wrapped over several lines by `#print axioms`; records are re-joined before
parsing, and any record that does not parse, or any headline that is not printed, fails the audit.
Also scans the four libraries' code (comments and docstrings excluded) for `sorry`, `admit` and
`axiom` declarations.

    python3 lfzk-v1/scripts/audit_axioms.py          # from formal/
"""
from __future__ import annotations

import re
import subprocess
import sys
import tempfile
from pathlib import Path

FORMAL = Path(__file__).resolve().parents[2]

FOUNDATIONAL = {"propext", "Classical.choice", "Quot.sound"}
NATIVE = {"Lean.ofReduceBool"}

# theorem -> native_decide allowed?
HEADLINES = {
    # Hahn/Delsarte masks composed through the deployed ZK verifier
    "Ligero.V1.ligerov1_roundByRound_mask_profiled": False,
    "LfzkV1.LigeroV1Rows.Row.arithProfile_eq_johnson": False,
    "LfzkV1.LigeroV1Rows.v7SigHahn_valid": True,
    "LfzkV1.LigeroV1Rows.v7SigHahn_sharp": True,
    "LfzkV1.CertifiedV1.v7SigHahn_valid": True,
    "LfzkV1.CompiledZk.v7SigHahn_core_le": True,
    "LfzkV1.CompiledZk.v7SigHahn_coefficient_le": True,
    "LfzkV1.CompiledZk.v7SigHahn_core_sharp": True,
    "LfzkV1.CompiledZk.v7SigHahn_tsec_slack": True,
    "LfzkV1.TSec.adaptiveNumerator_le_linear": False,
    "LfzkV1.TSec.tsec_of_linear_slack": False,
    "LfzkV1.CompiledZkProfileRows.v7SigHahn_zk_circuit_tsec": True,
    "LfzkV1.SoundnessAudit.quadratic_two_roots": False,
    "LfzkV1.SoundnessAudit.no_256bit_init_decoder": False,
    "LfzkV1.SoundnessAudit.hash_core_exceeds_116": True,
    "LfzkV1.SoundnessAudit.v7Hash1_challenge_escape_exact": True,
    "LfzkV1.SoundnessAudit.v7Hash1_cost_chain": True,
    "LfzkV1.SoundnessAudit.hash_round_charge_exceeds_117": True,
    "LfzkV1.SoundnessAudit.signature_core_improves": True,
    "LfzkV1.SoundnessAudit.hahn_twofield_linear_slack": True,
    "LfzkV1.SoundnessAudit.hahn_twofield_linear_rhs": True,
    "LfzkV1.SoundnessAudit.separate_blinds_collision": False,
    "LfzkV1.Mac.macTag_collision_unique": False,
    "LfzkV1.Mac.macTag_collision_card_le_one": False,
    "LfzkV1.Mac.shiftedMultiplier_collision_card_le_one": False,
    # Ligero V1, round by round
    "Ligero.V1.ligerov1_roundByRound_profiled": False,
    "LfzkV1.LigeroV1Rows.Row.rbr_soundness": False,
    # the sequential composed theorem
    "LfzkV1.CertifiedV1.Row.nizk_ratio_le": False,
    "LfzkV1.CertifiedV1.Row.nizk_ratio_le_family": False,
    # grinding, re-committing, compiled
    "LfzkV1.CertifiedV1.Row.fs_ratio_le_bound": False,
    "LfzkV1.CertifiedV1.Row.adaptive_ratio_le": False,
    "LfzkV1.CompiledLongfellow.hright_v1": False,
    # two-field
    "LfzkV1.TwoField.twofield_soundness": False,
    "LfzkV1.TwoFieldV1Rows.TwoFieldRowV1.nizk_ratio_le": False,
    # the compiled verifier against a re-committing prover, `hlig` and `hright` discharged
    "LfzkV1.CompiledLongfellowAdaptive.exists_msgLigeroData": False,
    "LfzkV1.CompiledLongfellowAdaptive.hright_v1": False,
    "LfzkV1.CompiledLongfellowAdaptive.CompiledSide.hright": False,
    "LfzkV1.CompiledLongfellowAdaptive.row_adaptive_ratio_le_v1": False,
    "LfzkV1.CompiledLongfellowAdaptive.twofield_adaptive_compiled_ratio_le": False,
    # zero knowledge: Ligero V1, the composed compiled argument, two-field, v7 numerals
    "LfzkV1.FromLigeroZK.V1.isLigeroZeroKnowledge_v1": False,
    "LfzkV1.CompiledLigeroZk.v1_compiled_zk_bits256_q115": False,
    "LfzkV1.ZkAdaptiveV1.statClose_adaptive": False,
    "LfzkV1.ZkAdaptiveV1.toSim_response": False,
    "LfzkV1.ZkAdaptiveV1.linCorr_unique": False,
    "LfzkV1.CompiledLongfellowZk.compiled_longfellow_zk": False,
    "LfzkV1.CompiledLongfellowZk.compiled_longfellow_zk_bits256": False,
    "LfzkV1.CompiledLongfellowZk.compiled_longfellow_zk_bits256_q115": False,
    "LfzkV1.CompiledLongfellowZk.compiled_longfellow_wi": False,
    "LfzkV1.CompiledLongfellowZkTwoField.twofield_wi": False,
    "LfzkV1.ZkFrontendOfSetup.compiled_longfellow_zk_of_setup": False,
    "LfzkV1.CompiledLongfellowZkTwoField.twofield_zk": False,
    "LfzkV1.CompiledLongfellowZkV7.row_compiled_zk": False,
    "LfzkV1.CompiledLongfellowZkV7.v7Sig_compiled_zk": False,
    "LfzkV1.CompiledLongfellowZkV7.v7Hash4_compiled_zk": False,
    "LfzkV1.CompiledLongfellowZkV7.twofield_zk_bits256": False,
    "LfzkV1.CompiledLongfellowZkV7.v7_twofield_zk_q115": False,
    "LfzkV1.ZkMerkleStat.leaf_statClose": False,
    "LfzkV1.ZkMerkleStat.digests_statClose": False,
    "LfzkV1.ZkMerkleStat.view_statClose": False,
    "LfzkV1.CompiledLongfellowZkStat.compiled_longfellow_zk_stat": False,
    "LfzkV1.CompiledLongfellowZkStat.twofield_zk_stat": False,
    "LfzkV1.CompiledLongfellowZkStat.v7_twofield_zk_stat542": False,
    # Fiat–Shamir at deployed hash inputs (message prefixes, total random oracle)
    "Bcs.TotalOracle.card_coord_le_const": False,
    "Bcs.TotalOracle.CtxGrinding.ratio_le": False,
    "Bcs.TotalOracle.Grinding.ratio_le": False,
    "Bcs.TotalOracleCommit.Setup.ratio_le": False,
    "Bcs.TotalOracleCommit.Setup.ratio_le_two": False,
    "LfzkV1.NizkDeployedHash.row_fs_ratio_le_bound": False,
    "LfzkV1.NizkDeployedHashAdaptive.row_adaptive_ratio_le": False,
    "LfzkV1.NizkDeployedHashAdaptive.row_adaptive_ratio_le_v1": False,
    "LfzkV1.NizkDeployedHashTwoField.twofield_adaptive_compiled_ratio_le": False,
    "LfzkV1.NizkDeployedHashV7.v7Sig_fs_ratio_le": True,
    "LfzkV1.NizkDeployedHashV7.v7Hash1_fs_ratio_le": True,
    "LfzkV1.NizkDeployedHashV7.v7Hash2_fs_ratio_le": True,
    "LfzkV1.NizkDeployedHashV7.v7Hash3_fs_ratio_le": True,
    "LfzkV1.NizkDeployedHashV7.v7Hash4_fs_ratio_le": True,
    "LfzkV1.NizkDeployedHashV7.v7Sig_adaptive_ratio_le": True,
    "LfzkV1.NizkDeployedHashV7.v7Hash1_adaptive_ratio_le": True,
    "LfzkV1.NizkDeployedHashV7.v7Hash2_adaptive_ratio_le": True,
    "LfzkV1.NizkDeployedHashV7.v7Hash3_adaptive_ratio_le": True,
    "LfzkV1.NizkDeployedHashV7.v7Hash4_adaptive_ratio_le": True,
    "LfzkV1.NizkDeployedHashV7.v7Sig_adaptive_compiled_ratio_le": True,
    "LfzkV1.NizkDeployedHashV7.v7Hash1_adaptive_compiled_ratio_le": True,
    "LfzkV1.NizkDeployedHashV7.v7Hash2_adaptive_compiled_ratio_le": True,
    "LfzkV1.NizkDeployedHashV7.v7Hash3_adaptive_compiled_ratio_le": True,
    "LfzkV1.NizkDeployedHashV7.v7Hash4_adaptive_compiled_ratio_le": True,
    "LfzkV1.NizkDeployedHashV7.v7P256Sha1_adaptive_compiled_ratio_le": True,
    "LfzkV1.NizkDeployedHashV7.v7P256Sha2_adaptive_compiled_ratio_le": True,
    "LfzkV1.NizkDeployedHashV7.v7P256Sha3_adaptive_compiled_ratio_le": True,
    "LfzkV1.NizkDeployedHashV7.v7P256Sha4_adaptive_compiled_ratio_le": True,
    # soundness against the deployed ZK verifier, the list factor at field slots only, and the
    # concrete arithmetization
    "LfzkV1.RbrLayerStepS.layerStep_ratio_le_mixed": False,
    "LfzkV1.RbrSplitS.FieldData.ratio_leS": False,
    "LfzkV1.CertifiedV1.Row.adaptive_ratio_leS": False,
    "LfzkV1.NizkAdaptiveTwoField.twofield_adaptive_ratio_leS": False,
    "LfzkV1.CompiledLongfellowAdaptive.row_adaptive_ratio_le_v1S": False,
    "LfzkV1.CompiledLongfellowAdaptive.twofield_adaptive_compiled_ratio_leS": False,
    "LfzkV1.RbrZkSplit.ZkFieldData.ratio_le": False,
    "LfzkV1.RbrZkSplit.hinit_of_output": False,
    "LfzkV1.CertifiedV1.Row.zk_adaptive_ratio_le": False,
    "LfzkV1.CompiledZk.hright_zk": False,
    "LfzkV1.CompiledZk.row_zk_compiled_ratio_le": False,
    "LfzkV1.NizkZkTwoField.twofield_zk_adaptive_ratio_le": False,
    "LfzkV1.CompiledZk.CompiledZkSide.hright": False,
    "LfzkV1.CompiledZk.twofield_zk_compiled_ratio_le": False,
    "LfzkV1.ZkArithInit.outExt_ne": False,
    "LfzkV1.ZkArithInit.zk_hinit": False,
    "LfzkV1.ZkArithInit.zkBoundaryOf": False,
    "LfzkV1.ZkArithInit.zkFieldDataOf": False,
    "LfzkV1.Arith.QuadCircuit.toLayered": False,
    "LfzkV1.Arith.QuadCircuit.toLayered_input_wMle": False,
    "LfzkV1.Arith.QuadCircuit.unsat_iff": False,
    "LfzkV1.Arith.QuadCircuit.toLayered_unsat_iff": False,
    "LfzkV1.Arith.QuadCircuit.toLayered_eqqAgree": False,
    "LfzkV1.Arith.QuadCircuit.top_harith": False,
    "LfzkV1.Arith.Cex.output_only_false": False,
    "LfzkV1.Arith.fieldData_harith_false": False,
    "LfzkV1.CompiledLongfellowAdaptive.v7Sig_adaptive_compiled_ratio_leS": True,
    "LfzkV1.CompiledLongfellowAdaptive.v7Hash1_adaptive_compiled_ratio_leS": True,
    "LfzkV1.CompiledLongfellowAdaptive.v7Hash2_adaptive_compiled_ratio_leS": True,
    "LfzkV1.CompiledLongfellowAdaptive.v7Hash3_adaptive_compiled_ratio_leS": True,
    "LfzkV1.CompiledLongfellowAdaptive.v7Hash4_adaptive_compiled_ratio_leS": True,
    "LfzkV1.CompiledLongfellowAdaptive.v7P256Sha1_adaptive_compiled_ratio_leS": True,
    "LfzkV1.CompiledLongfellowAdaptive.v7P256Sha2_adaptive_compiled_ratio_leS": True,
    "LfzkV1.CompiledLongfellowAdaptive.v7P256Sha3_adaptive_compiled_ratio_leS": True,
    "LfzkV1.CompiledLongfellowAdaptive.v7P256Sha4_adaptive_compiled_ratio_leS": True,
    "LfzkV1.CompiledZk.v7Hash1_zk_compiled_ratio_le": True,
    "LfzkV1.CompiledZk.v7Hash2_zk_compiled_ratio_le": True,
    "LfzkV1.CompiledZk.v7Hash3_zk_compiled_ratio_le": True,
    "LfzkV1.CompiledZk.v7Hash4_zk_compiled_ratio_le": True,
    "LfzkV1.CompiledZk.v7Sig_zk_compiled_ratio_le": True,
    "LfzkV1.CompiledZk.v7P256Sha1_zk_compiled_ratio_le": True,
    "LfzkV1.CompiledZk.v7P256Sha2_zk_compiled_ratio_le": True,
    "LfzkV1.CompiledZk.v7P256Sha3_zk_compiled_ratio_le": True,
    "LfzkV1.CompiledZk.v7P256Sha4_zk_compiled_ratio_le": True,
    # the deployed zero-knowledge verifier at deployed hash inputs
    "LfzkV1.NizkZkDeployedHash.zkChain_doomed_congr": False,
    "LfzkV1.NizkZkDeployedHash.row_zk_deployed_adaptive_ratio_le": False,
    "LfzkV1.NizkZkDeployedHash.twofield_zk_deployed_adaptive_ratio_le": False,
    "LfzkV1.CompiledZkDeployedHash.zkBuilt_congr": False,
    "LfzkV1.CompiledZkDeployedHash.hright_zkDH": False,
    "LfzkV1.CompiledZkDeployedHash.row_zk_deployed_ratio_le": False,
    "LfzkV1.CompiledZk.CompiledZkSide.hrightDH": False,
    "LfzkV1.CompiledZkDeployedHash.twofield_zk_deployed_ratio_le": False,
    "LfzkV1.CompiledZkDeployedHash.v7Hash1_zk_deployed_ratio_le": True,
    "LfzkV1.CompiledZkDeployedHash.v7Hash2_zk_deployed_ratio_le": True,
    "LfzkV1.CompiledZkDeployedHash.v7Hash3_zk_deployed_ratio_le": True,
    "LfzkV1.CompiledZkDeployedHash.v7Hash4_zk_deployed_ratio_le": True,
    "LfzkV1.CompiledZkDeployedHash.v7Sig_zk_deployed_ratio_le": True,
    "LfzkV1.CompiledZkDeployedHash.v7P256Sha1_zk_deployed_ratio_le": True,
    "LfzkV1.CompiledZkDeployedHash.v7P256Sha2_zk_deployed_ratio_le": True,
    "LfzkV1.CompiledZkDeployedHash.v7P256Sha3_zk_deployed_ratio_le": True,
    "LfzkV1.CompiledZkDeployedHash.v7P256Sha4_zk_deployed_ratio_le": True,
    # the arithmetization at the deployed width profile, and the end-to-end v7 headlines
    "LfzkV1.ZkArithProfile.cube_sum_hands": False,
    "LfzkV1.ZkArithProfile.lpoly_rel": False,
    "LfzkV1.ZkArithProfile.lpoly_quadratic": False,
    "LfzkV1.ZkArithProfile.cPendP_round": False,
    "LfzkV1.ZkArithProfile.zk_hinitP": False,
    "LfzkV1.ZkArithProfile.zkBoundaryP": False,
    "LfzkV1.ZkArithProfile.zkFieldDataP": False,
    "LfzkV1.ZkArithProfile.zkFieldDataP_exactAt": False,
    "LfzkV1.CompiledZkProfileRows.row_zk_deployed_circuit_ratio_le": False,
    "LfzkV1.CompiledZk.CircuitSide.toSide": False,
    "LfzkV1.CompiledZkProfileRows.v7Hash1_zk_circuit_ratio_le": True,
    "LfzkV1.CompiledZkProfileRows.v7Hash2_zk_circuit_ratio_le": True,
    "LfzkV1.CompiledZkProfileRows.v7Hash3_zk_circuit_ratio_le": True,
    "LfzkV1.CompiledZkProfileRows.v7Hash4_zk_circuit_ratio_le": True,
    "LfzkV1.CompiledZkProfileRows.v7Sig_zk_circuit_ratio_le": True,
    "LfzkV1.CompiledZkProfileRows.v7P256Sha1_zk_circuit_ratio_le": True,
    "LfzkV1.CompiledZkProfileRows.v7P256Sha2_zk_circuit_ratio_le": True,
    "LfzkV1.CompiledZkProfileRows.v7P256Sha3_zk_circuit_ratio_le": True,
    "LfzkV1.CompiledZkProfileRows.v7P256Sha4_zk_circuit_ratio_le": True,
    # no Merkle-query budget: the uncapped chain and T-security
    "LfzkV1.NizkZkDeployedHash.row_zk_deployed_adaptive_ratio_leT": False,
    "LfzkV1.NizkZkDeployedHash.twofield_zk_deployed_adaptive_ratio_leT": False,
    "LfzkV1.CompiledZkDeployedHash.row_zk_deployed_ratio_leT": False,
    "LfzkV1.CompiledZkDeployedHash.twofield_zk_deployed_ratio_leT": False,
    "LfzkV1.CompiledZkProfileRows.row_zk_deployed_circuit_ratio_leT": False,
    "LfzkV1.TSec.tsec_real": False,
    "LfzkV1.TSec.tsec_of_uncapped": False,
    "LfzkV1.TSec.row_tsec": False,
    "LfzkV1.TSec.twofield_tsec": False,
    "LfzkV1.CompiledZkProfileRows.v7Hash1_zk_circuit_tsec": True,
    "LfzkV1.CompiledZkProfileRows.v7Hash2_zk_circuit_tsec": True,
    "LfzkV1.CompiledZkProfileRows.v7Hash3_zk_circuit_tsec": True,
    "LfzkV1.CompiledZkProfileRows.v7Hash4_zk_circuit_tsec": True,
    "LfzkV1.CompiledZkProfileRows.v7Sig_zk_circuit_tsec": True,
    "LfzkV1.CompiledZkProfileRows.v7P256Sha1_zk_circuit_tsec": True,
    # the two-field MAC with separate private witnesses; the v7 MAC's zero knowledge
    "LfzkV1.MacSep.sepMacBad_card_le": False,
    "LfzkV1.NizkZkDeployedHash.twofield_zk_deployed_adaptive_ratio_leT_sep": False,
    "LfzkV1.CompiledZkDeployedHash.twofield_zk_deployed_ratio_leT_sep": False,
    "LfzkV1.CompiledZk.CircuitSide.cands_card_le": False,
    "LfzkV1.CompiledZk.CircuitSide.good_mem_cands": False,
    "LfzkV1.CompiledZkProfileRows.twofield_circuit_ratio_leT_sep": False,
    "LfzkV1.CompiledLongfellowZkV7Mac.twofield_zk_v7": False,
    "LfzkV1.CompiledLongfellowZkV7Mac.twofield_zk_v7_nonzero": False,
    "LfzkV1.CompiledLongfellowZkV7Mac.twofield_wi_v7": False,
    "LfzkV1.CompiledLongfellowZkV7Mac.v7mac_twofield_zk_q115": False,
    "LfzkV1.CompiledLongfellowZkV7Mac.v7mac_twofield_zk_q115_nonzero": False,
    "LfzkV1.CompiledLongfellowZkV7Mac.twofield_zk_stat_v7": False,
    "LfzkV1.CompiledLongfellowZkV7Mac.twofield_zk_stat_v7_nonzero": False,
    "LfzkV1.CompiledLongfellowZkV7Mac.v7mac_twofield_zk_stat542": False,
    "LfzkV1.CompiledZkProfileRows.v7P256Sha1_zk_circuit_tsec_sepMac": True,
    "LfzkV1.CompiledZkProfileRows.v7P256Sha1_zk_circuit_tsec_sepBlind": True,
    "LfzkV1.CompiledZkProfileRows.v7P256Sha2_zk_circuit_tsec_sepMac": True,
    "LfzkV1.CompiledZkProfileRows.v7P256Sha2_zk_circuit_tsec_sepBlind": True,
    "LfzkV1.CompiledZkProfileRows.v7P256Sha3_zk_circuit_tsec_sepMac": True,
    "LfzkV1.CompiledZkProfileRows.v7P256Sha3_zk_circuit_tsec_sepBlind": True,
    "LfzkV1.CompiledZkProfileRows.v7P256Sha4_zk_circuit_tsec_sepMac": True,
    "LfzkV1.CompiledZkProfileRows.v7P256Sha4_zk_circuit_tsec_sepBlind": True,
    "LfzkV1.TwoFieldV1Rows.v7P256Sha1_sep_mac_eq": True,
    "LfzkV1.TwoFieldV1Rows.v7P256Sha1_sep_slack_bound": True,
    "LfzkV1.TwoFieldV1Rows.v7P256Sha1_sep_slack_coeff": True,
    "LfzkV1.TwoFieldV1Rows.v7P256Sha1_sep_coeff_eq": True,
    "LfzkV1.TwoFieldV1Rows.v7P256Sha2_sep_mac_eq": True,
    "LfzkV1.TwoFieldV1Rows.v7P256Sha2_sep_slack_bound": True,
    "LfzkV1.TwoFieldV1Rows.v7P256Sha2_sep_slack_coeff": True,
    "LfzkV1.TwoFieldV1Rows.v7P256Sha2_sep_coeff_eq": True,
    "LfzkV1.TwoFieldV1Rows.v7P256Sha3_sep_mac_eq": True,
    "LfzkV1.TwoFieldV1Rows.v7P256Sha3_sep_slack_bound": True,
    "LfzkV1.TwoFieldV1Rows.v7P256Sha3_sep_slack_coeff": True,
    "LfzkV1.TwoFieldV1Rows.v7P256Sha3_sep_coeff_eq": True,
    "LfzkV1.TwoFieldV1Rows.v7P256Sha4_sep_mac_eq": True,
    "LfzkV1.TwoFieldV1Rows.v7P256Sha4_sep_slack_bound": True,
    "LfzkV1.TwoFieldV1Rows.v7P256Sha4_sep_slack_coeff": True,
    "LfzkV1.TwoFieldV1Rows.v7P256Sha4_sep_coeff_eq": True,
    "LfzkV1.CompiledZkProfileRows.v7P256Sha2_zk_circuit_tsec": True,
    "LfzkV1.CompiledZkProfileRows.v7P256Sha3_zk_circuit_tsec": True,
    "LfzkV1.CompiledZkProfileRows.v7P256Sha4_zk_circuit_tsec": True,
}


# the deployed-v7 rows and their instantiated headlines (`LigeroV1RowsV7`, `CertifiedV7`,
# `TwoFieldV7Rows`, `CompiledV7`)
V7_SIDES = ["v7Sig", "v7Hash1", "v7Hash2", "v7Hash3", "v7Hash4"]
V7_PAIRS = ["v7P256Sha1", "v7P256Sha2", "v7P256Sha3", "v7P256Sha4"]

HEADLINES.update({
    "LfzkV1.CertifiedV1.Row.fs_rhs_le_of": False,
    "LfzkV1.CertifiedV1.Row.adaptive_rhs_le_of_slack": False,
    "LfzkV1.TwoFieldV1Rows.TwoFieldRowV1.adaptive_rhs_le_of_slack": False,
})
for s in V7_SIDES:
    HEADLINES.update({
        f"LfzkV1.LigeroV1Rows.{s}_valid": True,
        f"LfzkV1.LigeroV1Rows.{s}_sharp": True,
        f"LfzkV1.CertifiedV1.{s}_valid": True,
        f"LfzkV1.CertifiedV1.{s}_sharp": True,
        f"LfzkV1.CertifiedV1.{s}_adaptive_rhs_le": True,
        f"LfzkV1.CertifiedV1.{s}_fs_rhs_le": True,
        f"LfzkV1.CertifiedV1.{s}_nizk_ratio_le": True,
        f"LfzkV1.CertifiedV1.{s}_fs_ratio_le": True,
        f"LfzkV1.CertifiedV1.{s}_adaptive_ratio_le": True,
        f"LfzkV1.CompiledLongfellow.{s}_compiled_fs_ratio_le": True,
        f"LfzkV1.CompiledLongfellowAdaptive.{s}_adaptive_compiled_ratio_le": True,
    })
for p in V7_PAIRS:
    HEADLINES.update({
        f"LfzkV1.TwoFieldV1Rows.{p}_valid": True,
        f"LfzkV1.TwoFieldV1Rows.{p}_sharp": True,
        f"LfzkV1.TwoFieldV1Rows.{p}_premises_satisfiable": True,
        f"LfzkV1.TwoFieldV1Rows.{p}_adaptive_rhs_le": True,
        f"LfzkV1.TwoFieldV1Rows.{p}_nizk_ratio_le_keyFirst": True,
        f"LfzkV1.NizkAdaptiveTwoField.{p}_adaptive_ratio_le": True,
        f"LfzkV1.CompiledLongfellowAdaptive.{p}_adaptive_compiled_ratio_le": True,
    })


# Lean 4.31's `native_decide` owns one auxiliary axiom per call, `<decl>._native.native_decide.ax_i_j`
NATIVE_AUX = re.compile(r"^LfzkV1\.[\w.']+\._native\.native_decide\.ax_\d+_\d+$")


def strip_comments(text: str) -> str:
    """Drop `--` line comments, nested `/- … -/` block comments (docstrings included) and string
    literals, so that the keyword scan below only sees code."""
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        if depth:
            if text.startswith("/-", i):
                depth, i = depth + 1, i + 2
            elif text.startswith("-/", i):
                depth, i = depth - 1, i + 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("/-", i):
            depth, i = 1, i + 2
        elif text.startswith("--", i):
            while i < n and text[i] != "\n":
                i += 1
        elif text[i] == '"':
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def keyword_hits() -> list[str]:
    hits = []
    for lib in ("lfzk-v1", "bcs", "merkle", "sumcheck-v1"):
        for f in sorted((FORMAL / lib).rglob("*.lean")):
            code = strip_comments(f.read_text())
            for k, line in enumerate(code.splitlines(), 1):
                if re.search(r"\b(sorry|admit)\b", line) or re.match(r"\s*(private\s+)?axiom\b", line):
                    hits.append(f"{f.relative_to(FORMAL)}:{k}: {line.strip()}")
    return hits


def main() -> int:
    bad = 0
    with tempfile.TemporaryDirectory() as d:
        src = Path(d) / "Audit.lean"
        src.write_text("import LfzkV1\n" + "".join(f"#print axioms {t}\n" for t in HEADLINES))
        out = subprocess.run(["lake", "env", "lean", str(src)], cwd=FORMAL, text=True,
                             capture_output=True)
        if out.returncode != 0:
            print(out.stdout[-4000:], out.stderr[-4000:])
            return 1
    seen = set()
    # `#print axioms` wraps long lists over several lines: one record per line starting with `'`
    for rec in re.split(r"\n(?=')", out.stdout.strip()):
        rec = " ".join(rec.split())
        m = re.match(r"^'([^']+)' depends on axioms: \[(.*)\]$", rec)
        if not m:
            m2 = re.match(r"^'([^']+)' does not depend on any axioms$", rec)
            if m2:
                seen.add(m2.group(1))
                print(f"ok     {m2.group(1)}: no axioms")
                continue
            bad += 1
            print("FAIL  unparsed output:", rec)
            continue
        name, axioms = m.group(1), {a.strip() for a in m.group(2).split(",") if a.strip()}
        seen.add(name)
        native = ({a for a in axioms if NATIVE_AUX.match(a)} | (axioms & NATIVE)
                  if HEADLINES.get(name) else set())
        extra = axioms - FOUNDATIONAL - native
        if extra:
            bad += 1
        status = "ok    " if not extra else "FAIL  "
        shown = sorted(axioms & FOUNDATIONAL) + ([f"+{len(native)} native_decide row facts"]
                                                 if native else [])
        print(f"{status} {name}: {shown}" + (f" EXTRA {sorted(extra)}" if extra else ""))
    missing = set(HEADLINES) - seen
    if missing:
        bad += 1
        print("FAIL  not printed:", sorted(missing))
    hits = keyword_hits()
    if hits:
        bad += 1
        print("FAIL  sorry/axiom/admit in code:")
        print("\n".join(hits))
    else:
        print("ok     no sorry/axiom/admit in lfzk-v1, bcs, merkle, sumcheck (comments excluded)")
    print(f"audit of {len(HEADLINES)} declarations", "FAILED" if bad else "passed")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
