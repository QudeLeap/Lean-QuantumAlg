/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Initialization.Reset
import all QuantumAlg.Components.QuditShift.Qubit
import all QuantumAlg.Components.QuditShift.Reset.Circuit.Sequence.Resources
import all QuantumAlg.Core.Execution.Time

/-!
# Quantum time of the actual streaming reset

Every resident wire is measured and corrected by the original identity/X
implementation. Measurement contributes zero canonical quantum duration;
each actual correction contributes at most one. The same complete reset
Path is projected through the real finite sequence. No classical scratch,
input-state condition or alternative reset circuit is introduced.


-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Initialization
namespace Time

noncomputable section

open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open scoped BigOperators

/-- Identity and X have their literal durations under every event-duration assignment. -/
lemma qubitShift_duration {count : Nat} (layout : QuantumLayout count) (wire : Fin count)
    (qubit : (layout.wire wire).dimension = 2) (oracles : OracleModel)
    (amount : Fin (layout.wire wire).dimension)
    (duration : Resource.Event (.quantum AlgorithmGate.model oracles) → Nat) :
    (QuditShift.qubitShiftCircuit layout wire qubit oracles amount).evaluatedEventDepth duration =
      if amount = 0 then 0 else duration (.gate .singleQubit) := by
  unfold QuditShift.qubitShiftCircuit
  split_ifs <;> rfl

/-- The same measured wire executes at most one quantum gate on every actual outcome. -/
lemma qubitResetWire_quantumTime_le {ctx : RuntimeCtx .quantum} {allowAllocation : Bool}
    (wire : Fin ctx.systemCount) (qubit : (ctx.quantumLayout.wire wire).dimension = 2)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (target : Fin (ctx.quantumLayout.wire wire).dimension)
    (path : (QuditShift.resetWireToBasis (allowAllocation := allowAllocation) wire
      (QuditShift.qubitRealizations ctx.quantumLayout wire qubit .empty) output target).Path) :
    (QuditShift.resetWireToBasis (allowAllocation := allowAllocation) wire
      (QuditShift.qubitRealizations ctx.quantumLayout wire qubit .empty) output target).quantumTime
        path ≤ 1 := by
  rw [Circuit.quantumTime, QuditShift.resetWireToBasis_duration]
  change 0 + (QuditShift.qubitShiftCircuit ctx.quantumLayout wire qubit .empty
    (target - path.2.1.toFin)).evaluatedEventDepth Resource.Event.quantumDuration ≤ 1
  rw [qubitShift_duration]
  split_ifs <;> decide

/-- The literal full reset is bounded by its resident-wire count, including zero systems. -/
lemma newReset_quantumTime_le {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (fieldTail m : Nat) (seed : AffinePoint E)
    (path : (newReset E fieldTail m seed).Path) :
    (newReset E fieldTail m seed).quantumTime path ≤
      (Recovery.Layout.terminal p.size m).systemCount := by
  change (QuditShift.resetToBasisOn (allowAllocation := false)
    (newResetImplementations p.size m) (Recovery.Layout.terminal p.size m).systemCount id
    (newResetCells p m) (newResetLabel E fieldTail m seed)).Path at path
  change (QuditShift.resetToBasisOn (allowAllocation := false)
    (newResetImplementations p.size m) (Recovery.Layout.terminal p.size m).systemCount id
    (newResetCells p m) (newResetLabel E fieldTail m seed)).depth
      Resource.Event.quantumDuration path ≤ _
  rw [QuditShift.resetToBasisOn_duration]
  calc
    _ ≤ ∑ _ : Fin (Recovery.Layout.terminal p.size m).systemCount, (1 : Nat) := by
      apply Finset.sum_le_sum
      intro wire _
      exact qubitResetWire_quantumTime_le wire (newReset_qubits p.size m wire)
        (newResetCells p m wire) (newResetLabel E fieldTail m seed wire)
        (Circuit.forRangeComponentPath (Recovery.Layout.terminal p.size m).systemCount _ path wire)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      Nat.mul_one]

end

end Time
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Initialization
