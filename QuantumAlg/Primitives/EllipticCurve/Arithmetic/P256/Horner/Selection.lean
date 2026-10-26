/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.GateSpec

/-!
# Paid coherent bit selection before native arithmetic borrowing

The conjunction of the caller's selector and actual multiplier bit is
latched before the arithmetic body. The same Toffoli clears the original
clean latch after the body restores both control readouts. The multiplier
bit may occur in the body's borrowed source; no extra word is introduced.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Horner.Selection

noncomputable section

open QuantumAlg QuantumAlg.EncodedBit GateSpec

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
variable (outer multiplier latch : EncodedBit encoding)
  (outerMultiplier : outer.wire ≠ multiplier.wire)
  (outerLatch : outer.wire ≠ latch.wire) (multiplierLatch : multiplier.wire ≠ latch.wire)

/-- Both occurrences are actual Toffolis on three distinct existing caller wires. -/
def latchGate : GateSpec encoding :=
  .toffoli outer multiplier latch outerMultiplier outerLatch multiplierLatch

def gates (body : List (GateSpec encoding)) : List (GateSpec encoding) :=
  [latchGate outer multiplier latch outerMultiplier outerLatch multiplierLatch] ++ body ++
    [latchGate outer multiplier latch outerMultiplier outerLatch multiplierLatch]

def program (body : List (GateSpec encoding)) : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical encoding.width).toQuantum :=
  programList (QubitLayout.canonical _) .empty
    (gates outer multiplier latch outerMultiplier outerLatch multiplierLatch body)

/-- Literal full-label action retains the entire native body between the two latch gates. -/
lemma gates_step (body : List (GateSpec encoding)) (state : Data) :
    stepList (gates outer multiplier latch outerMultiplier outerLatch multiplierLatch body) state =
      toffoliStep outer multiplier latch
        (stepList body (toffoliStep outer multiplier latch state)) := by
  simp only [gates, stepList_append, stepList, latchGate, step, id_eq]

/-- The selected multiplier bit is read before any native arithmetic borrowing begins. -/
lemma latch_computed (state : Data) (clean : latch.get state = false) :
    latch.get (toffoliStep outer multiplier latch state) =
      (outer.get state && multiplier.get state) := by
  rw [toffoliStep_get_target, clean, Bool.false_xor]

/-- Restored controls clear the same original clean latch, even if the body borrowed them. -/
lemma latch_restored (body : List (GateSpec encoding)) (state : Data)
    (clean : latch.get state = false)
    (bodyLatch : latch.get (stepList body (toffoliStep outer multiplier latch state)) =
      latch.get (toffoliStep outer multiplier latch state))
    (bodyOuter : outer.get (stepList body (toffoliStep outer multiplier latch state)) =
      outer.get state)
    (bodyMultiplier : multiplier.get (stepList body (toffoliStep outer multiplier latch state)) =
      multiplier.get state) :
    latch.get (stepList
      (gates outer multiplier latch outerMultiplier outerLatch multiplierLatch body) state) =
        false := by
  rw [gates_step, toffoliStep_get_target, bodyLatch, bodyOuter, bodyMultiplier,
    latch_computed outer multiplier latch state clean]
  exact Bool.xor_self _

/-- The actual selected wrapper has an exact unitary action, with all relative phases retained. -/
lemma realizes (body : List (GateSpec encoding))
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes encoding
      (program outer multiplier latch outerMultiplier outerLatch multiplierLatch body)
      environment
      (stepList (gates outer multiplier latch outerMultiplier outerLatch multiplierLatch body)) :=
  realizesList (QubitLayout.canonical _) .empty
    (gates outer multiplier latch outerMultiplier outerLatch multiplierLatch body) environment

/-- Computing and clearing the actual conjunction costs exactly two extra Toffolis. -/
lemma toffoli_count (body : List (GateSpec encoding)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program outer multiplier latch outerMultiplier outerLatch multiplierLatch body).eventCost =
        (body.map toffoliMultiplicity).sum + 2 := by
  rw [program, programList_toffoli_count_eq_sum]
  simp only [gates, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, latchGate, toffoliMultiplicity_toffoli]
  omega

/-- The latch instructions add no CNOT occurrence to the actual body's ledger. -/
lemma cnot_count (body : List (GateSpec encoding)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program outer multiplier latch outerMultiplier outerLatch multiplierLatch body).eventCost =
        (body.map cnotMultiplicity).sum := by
  rw [program, programList_cnot_count_eq_sum]
  simp only [gates, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, latchGate, cnotMultiplicity_toffoli, Nat.zero_add, Nat.add_zero]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Horner.Selection
