/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Write.Frame
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Length.Refresh

/-!
# Four actual scanned length writes in the original boundary order

The coefficient writes read Work2 then Work1; the divisor writes read
Work1 then Work2 at the newly updated coefficient boundary. Each emitted
write performs its full preparation, native quantum copy and adjoint.
The entire pool is restored between the writes. No selector enumeration
from the original implementation occurs in this actual program.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthRefresh

noncomputable section

open EncodedBit LengthCoordinates NumberTheory.SharedEEA

private def sourceWrite (width : Nat) (field : Field) (first : Bool)
    (state : Registers width) : Registers width :=
  if state.control then LengthSchedule.step width field first state else state

private lemma lengthStep_control (width : Nat) (field : Field) (first : Bool)
    (state : Registers width) :
    (LengthSchedule.step width field first state).control = state.control := by
  cases field <;> rfl

private lemma ordered_source (width : Nat) (state : Registers width) :
    sourceWrite width .divisor false
      (sourceWrite width .divisor true
        (sourceWrite width .coefficient true
          (sourceWrite width .coefficient false state))) =
      if state.control then SharedEEA.LengthRefresh.step state else state := by
  by_cases control : state.control = true
  · simp only [sourceWrite, lengthStep_control, control, if_true]
    exact SharedEEA.LengthRefresh.ordered_steps width state
  · simp only [sourceWrite, control, Bool.false_eq_true, if_false]

/-- The actual four native programs use one complete physical frame and the same shared pool. -/
def program (width : Nat) (capacity : width + 3 ≤ 2 ^ ScanMetadata.addressWidth width) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  (LengthRefreshWrite.program width .coefficient false capacity).seq
    ((LengthRefreshWrite.program width .coefficient true capacity).seq
      ((LengthRefreshWrite.program width .divisor true capacity).seq
        (LengthRefreshWrite.program width .divisor false capacity)))

/-- Complete source refresh under retained Ctrl, with the same entire pool returned. -/
lemma program_apply_source (width : Nat)
    (capacity : width + 3 ≤ 2 ^ ScanMetadata.addressWidth width)
    (environment : OracleModel.empty.Interpretation)
    (state : Data width) (prefixZero : state.2.2.1 = 0) (addressZero : state.2.1 = 0)
    (borrowZero : state.2.2.2 = false)
    (sentinelFits : width + 3 < 2 ^ ScanMetadata.addressWidth width) :
    (program width capacity).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode
          (if state.1.control then SharedEEA.LengthRefresh.step state.1 else state.1,
            state.2))) := by
  let first : Data width := (sourceWrite width .coefficient false state.1, state.2)
  let second : Data width := (sourceWrite width .coefficient true first.1, state.2)
  let third : Data width := (sourceWrite width .divisor true second.1, state.2)
  let fourth : Data width := (sourceWrite width .divisor false third.1, state.2)
  let ket (value : Data width) := NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
    ((encoding width).encode value))
  have firstActual := LengthRefreshWrite.program_apply_source width .coefficient false capacity
    environment state prefixZero addressZero borrowZero sentinelFits
  have secondActual := LengthRefreshWrite.program_apply_source width .coefficient true capacity
    environment first prefixZero addressZero borrowZero sentinelFits
  have thirdActual := LengthRefreshWrite.program_apply_source width .divisor true capacity
    environment second prefixZero addressZero borrowZero sentinelFits
  have fourthActual := LengthRefreshWrite.program_apply_source width .divisor false capacity
    environment third prefixZero addressZero borrowZero sentinelFits
  change (LengthRefreshWrite.program width .coefficient false capacity).applyNormalized
    environment (ket state) = ket first at firstActual
  change (LengthRefreshWrite.program width .coefficient true capacity).applyNormalized
    environment (ket first) = ket second at secondActual
  change (LengthRefreshWrite.program width .divisor true capacity).applyNormalized
    environment (ket second) = ket third at thirdActual
  change (LengthRefreshWrite.program width .divisor false capacity).applyNormalized
    environment (ket third) = ket fourth at fourthActual
  change (program width capacity).applyNormalized environment (ket state) =
    ket (if state.1.control then SharedEEA.LengthRefresh.step state.1 else state.1, state.2)
  rw [program, UnitaryCircuit.applyNormalized_seq, firstActual,
    UnitaryCircuit.applyNormalized_seq, secondActual, UnitaryCircuit.applyNormalized_seq,
    thirdActual, fourthActual]
  have sourceResult := ordered_source width state.1
  exact congrArg (fun result => ket (result, state.2)) sourceResult

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthRefresh
