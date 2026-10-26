/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Resources.Native

/-!
# Complete same-path arithmetic-call bounds

The actual physical reset, selected same-mask feedback, paid classical
pack and native prefix all belong to one circuit path. These per-call
upper bounds are separate from the enclosing point, its six queries,
source-seed lifetime and final whole-bank reset.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Call

noncomputable section

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (sameWires : (QubitLayout.canonical Window.encoding.width).toQuantum.wires =
      ctx.quantumLayout.wires)
    (output : Fin 256 → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits 256))
    (kind : Kind) (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) (positive : 1 ≤ width)

include positive in
lemma circuit_toffoli_count_le
    (path : (circuit (services := services) sameWires output mask kind stream width bounded).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.gate .toffoli) ((circuit sameWires output mask kind stream width bounded).resourcePool
        path) ≤ 474737453 + 4 * EncodedBit.Word.OneDirtyLayout.gateCount (width + 1) := by
  have actual := circuit_gate_count_le sameWires output mask kind stream width bounded .toffoli path
  have native := native_toffoli_count_le kind stream width bounded positive
    (tailOutcome sameWires output mask kind stream width bounded path)
  simp only [nativePool, ResourcePool.count_add] at native
  simp only [reduceCtorEq, if_false, Nat.add_zero] at actual
  omega

include positive in
lemma circuit_cnot_count_le
    (path : (circuit (services := services) sameWires output mask kind stream width bounded).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.gate .cnot) ((circuit sameWires output mask kind stream width bounded).resourcePool path) ≤
        301982217 + Phase.selectedCount
          (tailOutcome sameWires output mask kind stream width bounded path) +
          4 * transferCnot kind := by
  have actual := circuit_gate_count_le sameWires output mask kind stream width bounded .cnot path
  have native := native_cnot_count_le kind stream width bounded positive
    (tailOutcome sameWires output mask kind stream width bounded path)
  simp only [nativePool, ResourcePool.count_add] at native
  simp only [reduceCtorEq, if_false, Nat.add_zero] at actual
  omega

include positive in
lemma circuit_singleQubit_count_le
    (path : (circuit (services := services) sameWires output mask kind stream width bounded).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.gate .singleQubit)
      ((circuit sameWires output mask kind stream width bounded).resourcePool path) ≤
        125477848 + 3 * Phase.selectedCount
          (tailOutcome sameWires output mask kind stream width bounded path) +
          4 * (2 * (width + 1) + 1) := by
  have actual := circuit_gate_count_le sameWires output mask kind stream width bounded
    .singleQubit path
  have native := native_singleQubit_count kind stream width bounded positive
    (tailOutcome sameWires output mask kind stream width bounded path)
  simp only [nativePool, ResourcePool.count_add] at native
  simp only [if_true] at actual
  omega

lemma circuit_complete_quantumTime_le
    (path : (circuit (services := services) sameWires output mask kind stream width bounded).Path) :
    (circuit sameWires output mask kind stream width bounded).depth
        Resource.Event.quantumDuration path ≤
      822778667 + 4 * Phase.selectedCount
        (tailOutcome sameWires output mask kind stream width bounded path) +
        4 * (2 * (width + 1) + EncodedBit.Word.OneDirtyLayout.gateCount (width + 1) + 1 +
          transferCnot kind) := by
  have actual := circuit_quantumTime_le sameWires output mask kind stream width bounded path
  have native := native_quantumTime_le kind stream width bounded
    (tailOutcome sameWires output mask kind stream width bounded path)
  omega

end

end Arithmetic.Call

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
