/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Inversion.Normal
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Boundary.Initial
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Parallel.Counts

/-!
# Actual complete resident inversion resource consumers

The independent complete source ledger passes through the same generic
resident placement, original N control, typed physical frame and A/Y
reuse. The source program includes every initialization, chronological
body, terminal correction and unload. These are upper bounds, except
for the exact single-qubit count; they are not point-cost lower bounds.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Inversion

noncomputable section

open MAU.Inversion.SharedEEA.Scanned

lemma program_eventCost : program.eventCost =
    (ControlledParallel.program modulus modulus_nontrivial).eventCost := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, program_eventTrace,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost]

lemma program_toffoli_count_le :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      program.eventCost ≤ 210279839 := by
  rw [program_eventCost]
  exact ControlledParallel.p256_program_toffoli_direct

lemma program_cnot_count_le :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      program.eventCost ≤ 149962185 := by
  rw [program_eventCost]
  exact ControlledParallel.p256_program_cnot_direct

lemma program_singleQubit_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      program.eventCost = 62544356 := by
  rw [program_eventCost]
  exact ControlledParallel.p256_program_singleQubit_direct

lemma program_quantumTime_le :
    program.evaluatedEventDepth Resource.Event.quantumDuration ≤ 383077592 :=
  program_quantumTime.trans_le ControlledParallel.p256_program_quantumTime_direct

lemma normal_eventCost : Normal.program.eventCost = program.eventCost := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, Normal.program_eventTrace,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost]

lemma normal_quantumTime_le :
    Normal.program.evaluatedEventDepth Resource.Event.quantumDuration ≤ 383077592 :=
  Normal.program_quantumTime.trans_le program_quantumTime_le

private lemma reusedForward_eventTrace : Chain.Boundary.reusedForward.eventTrace =
    program.eventTrace :=
  ((Transport.program_eventTrace modulus_size _).trans
    ((ControlledResidentReuse.forward_eventTrace modulus modulus_nontrivial).trans
      ((ControlledResidentNormal.program_eventTrace modulus modulus_nontrivial).trans
        (ControlledResident.program_eventTrace modulus modulus_nontrivial)))).trans
          program_eventTrace.symm

lemma reusedForward_eventCost : Chain.Boundary.reusedForward.eventCost = program.eventCost := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, reusedForward_eventTrace,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost]

private lemma reusedForward_quantumTime :
    Chain.Boundary.reusedForward.evaluatedEventDepth Resource.Event.quantumDuration =
      program.evaluatedEventDepth Resource.Event.quantumDuration :=
  ((Transport.program_quantumTime modulus_size _).trans
    ((ControlledResidentReuse.forward_quantumTime modulus modulus_nontrivial).trans
      ((ControlledResidentNormal.program_quantumTime modulus modulus_nontrivial).trans
        (ControlledResident.program_quantumTime modulus modulus_nontrivial)))).trans
          program_quantumTime.symm

lemma reusedForward_quantumTime_le :
    Chain.Boundary.reusedForward.evaluatedEventDepth Resource.Event.quantumDuration ≤ 383077592 :=
  reusedForward_quantumTime.trans_le program_quantumTime_le

lemma reusedBackward_eventCost : Chain.Boundary.reusedBackward.eventCost = program.eventCost := by
  have typed : Chain.Boundary.reusedBackward.eventCost =
      (ControlledResidentReuse.backward modulus modulus_nontrivial).eventCost := by
    rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, Chain.Boundary.reusedBackward_eventTrace,
      UnitaryCircuit.ofList_eventTrace_eq_eventCost]
  have forward : (ControlledResidentReuse.forward modulus modulus_nontrivial).eventCost =
      Chain.Boundary.reusedForward.eventCost := by
    have trace := Transport.program_eventTrace modulus_size
      (ControlledResidentReuse.forward modulus modulus_nontrivial)
    have pools := congrArg
      (ResourcePool.ofList (model := .quantum AlgorithmGate.model .empty)) trace
    simpa only [Chain.Boundary.reusedForward,
      UnitaryCircuit.ofList_eventTrace_eq_eventCost] using pools.symm
  exact (typed.trans (ControlledResidentReuse.backward_eventCost modulus modulus_nontrivial)).trans
    (forward.trans reusedForward_eventCost)

lemma reusedBackward_quantumTime_le :
    Chain.Boundary.reusedBackward.evaluatedEventDepth Resource.Event.quantumDuration ≤
      383077592 := by
  have typed := Chain.Boundary.reusedBackward_quantumTime.trans
    (ControlledResidentReuse.backward_quantumTime modulus modulus_nontrivial)
  have forward := Transport.program_quantumTime modulus_size
    (ControlledResidentReuse.forward modulus modulus_nontrivial)
  exact (typed.trans forward.symm).trans_le reusedForward_quantumTime_le

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Inversion
