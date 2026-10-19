/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Initialization.Reset
import all QuantumAlg.Components.QuditShift.Reset.Circuit.Sequence.Resources
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Resources

/-!
# Every physical measurement and correction of the actual leading reset

The allowance counts every reset wire, its Z measurement and possible native X
correction, for every complete original Path without a state or positive-probability
premise.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Initialization
namespace Events

noncomputable section

open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open scoped BigOperators

private abbrev Model : ExecutionModel := .quantum AlgorithmGate.model .empty

/-- An independent allowance for one actual qubit measurement and possible X. -/
def wireBudget : ResourcePool Model :=
  ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty) (.measurement (2 : ℕ+)) +
    ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.singleQubit)

private lemma qubitResetWire_budget {ctx : RuntimeCtx .quantum}
    (wire : Fin ctx.systemCount) (qubit : (ctx.quantumLayout.wire wire).dimension = 2)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (value : Fin (ctx.quantumLayout.wire wire).dimension)
    (path : (QuditShift.resetWireToBasis (allowAllocation := false) wire
      (QuditShift.qubitRealizations ctx.quantumLayout wire qubit .empty) output value).Path) :
    (QuditShift.resetWireToBasis (allowAllocation := false) wire
      (QuditShift.qubitRealizations ctx.quantumLayout wire qubit .empty)
      output value).resourcePool path ≤ wireBudget := by
  rw [QuditShift.resetWireToBasis_pool]
  change ResourcePool.ofList (Circuit.zEvent (ctx.quantumLayout.wire wire).dimension ::
    (QuditShift.qubitShiftCircuit ctx.quantumLayout wire qubit .empty
      (value - path.2.1.toFin)).eventTrace) ≤ _
  rw [QuditShift.qubitShiftCircuit_events]
  by_cases zero : value - path.2.1.toFin = 0
  · rw [if_pos zero]
    change ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
      (.measurement (ctx.quantumLayout.wire wire).dimension) ≤ _
    rw [qubit]
    exact le_add_of_nonneg_right zero_le
  · rw [if_neg zero]
    change ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
      (.measurement (ctx.quantumLayout.wire wire).dimension) +
      ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
        (.gate AlgorithmGate.Coordinate.singleQubit) ≤ _
    rw [qubit]
    exact le_rfl

/-- All resident wires pay their actual measurement and selected correction once. -/
lemma newReset_budget {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (fieldTail m : Nat) (seed : AffinePoint E)
    (path : (newReset E fieldTail m seed).Path) :
    (newReset E fieldTail m seed).resourcePool path ≤
      (Recovery.Layout.terminal p.size m).systemCount • wireBudget := by
  change (Circuit.forRange (Recovery.Layout.terminal p.size m).systemCount (fun wire =>
    QuditShift.resetWireToBasis (allowAllocation := false) wire
      (newResetImplementations p.size m wire) (newResetCells p m wire)
      (newResetLabel E fieldTail m seed wire))).resourcePool path ≤ _
  refine (Circuit.forRange_pool_le_sum _ _ (fun _ => wireBudget)
    (fun wire child => qubitResetWire_budget wire (newReset_qubits p.size m wire)
      (newResetCells p m wire) (newResetLabel E fieldTail m seed wire) child) path).trans_eq ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

end

end Events
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Initialization
