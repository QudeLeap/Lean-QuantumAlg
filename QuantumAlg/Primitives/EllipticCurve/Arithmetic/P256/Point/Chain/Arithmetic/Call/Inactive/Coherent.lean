/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Coherent
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Inactive.Tail
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Inactive.State

/-!
# Exact common coefficient of both actual inactive arithmetic calls

The prefix saves the arbitrary original Y into A before the actual H,
measurement and physical reset. The same measured mask selects the paid
phase and actual swap. Every original physical coordinate and Reference
label returns with the same outcome-independent coefficient. The inactive
words are not restricted to canonical residues.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Call

noncomputable section

open Execution EncodedBit.WindowLookup NormalizedVector

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (sameWires : (QubitLayout.canonical Window.encoding.width).toQuantum.wires =
      ctx.quantumLayout.wires)
    (output : Fin 256 → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits 256))
    (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)

lemma division_branchOperator_disabled_ket
    (distinct : Function.Injective fun index => (output index).key)
    (store : Store ctx) (outcome : Word) (state : Window.Raw)
    (environment : OracleModel.empty.Interpretation) {Reference : Register}
    (reference : Reference.Index)
    (zero : Save.ports.target.value state.1 = Horner.zeroWord)
    (flags : ((Placement.layout Save.ports).grouping state.1).1.1.2 = false ∧
      ((Placement.layout Save.ports).grouping state.1).1.2.1 = false ∧
        ((Placement.layout Save.ports).grouping state.1).1.2.2 = false)
    (clean : Frame.CleanPool (Control.prepareStep stream width bounded state).1)
    (control : (Control.prepareStep stream width bounded state).1.1.1.1.control = false)
    (normal : (Control.prepareStep stream width bounded state).1.2.2.1 = false)
    (disabled : (Phase.physicalSelector .enable).get state.1 = false) :
    (branchOperator (services := services) sameWires output mask .division stream width bounded
      store (Reset.outcomePath (services := services) .numerator sameWires output outcome
        (afterSave .enable state)) environment Reference).applyVec
      (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (measuredEncodedBasis (QubitLayout.canonical _) sameWires state, reference)).vec =
      invSqrt2 ^ 256 • (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (measuredEncodedBasis (QubitLayout.canonical _) sameWires state, reference)).vec := by
  have headAction := divisionBeforeReset_disabled stream width bounded environment state zero
    flags clean control normal disabled
  have feedback := divisionTail_afterReset_disabled stream width bounded environment state
    outcome flags clean control normal disabled
  have restored := swap_afterReset_disabled .enable state zero flags disabled
  have originalY : Frame.numerator (afterSave .enable state).1 = Frame.numerator state.1 :=
    Save.savedState_multiplier Save.ports .enable state.1
  have actualTail : (tail .division stream width bounded outcome).applyVec environment
      (Window.ket (Reset.namedOutcome .numerator Reset.zeroOutcome
        (afterSave .enable state))).vec =
        WalshHadamard.walshSign outcome (Frame.numerator (afterSave .enable state).1) •
          (Window.ket state).vec := by
    rw [originalY]
    exact feedback.trans (congrArg
      (fun final => WalshHadamard.walshSign outcome (Frame.numerator state.1) •
        (Window.ket final).vec) restored)
  exact call_branchOperator_corrected_ket sameWires output mask .division stream width bounded
    distinct store outcome state (afterSave .enable state) state environment reference headAction
    actualTail

lemma multiplication_branchOperator_disabled_ket
    (distinct : Function.Injective fun index => (output index).key)
    (store : Store ctx) (outcome : Word) (state : Window.Raw)
    (environment : OracleModel.empty.Interpretation) {Reference : Register}
    (reference : Reference.Index)
    (zero : Save.ports.target.value state.1 = Horner.zeroWord)
    (flags : ((Placement.layout Save.ports).grouping state.1).1.1.2 = false ∧
      ((Placement.layout Save.ports).grouping state.1).1.2.1 = false ∧
        ((Placement.layout Save.ports).grouping state.1).1.2.2 = false)
    (clean : Frame.CleanPool (Window.Enable.step stream width bounded state).1)
    (control : (Window.Enable.step stream width bounded state).1.1.1.1.control = false)
    (normal : (Window.Enable.step stream width bounded state).1.2.2.1 = false) :
    (branchOperator (services := services) sameWires output mask .multiplication stream width
      bounded store (Reset.outcomePath (services := services) .numerator sameWires output outcome
        (afterSave .normal state)) environment Reference).applyVec
      (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (measuredEncodedBasis (QubitLayout.canonical _) sameWires state, reference)).vec =
      invSqrt2 ^ 256 • (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (measuredEncodedBasis (QubitLayout.canonical _) sameWires state, reference)).vec := by
  have disabled : (Phase.physicalSelector .normal).get state.1 = false :=
    (clear_normal stream width bounded state).symm.trans normal
  have headAction := multiplicationBeforeReset_disabled stream width bounded environment state zero
    flags disabled
  have feedback := multiplicationTail_afterReset_disabled stream width bounded environment state
    outcome flags clean control normal
  have restored := swap_afterReset_disabled .normal state zero flags disabled
  have originalY : Frame.numerator (afterSave .normal state).1 = Frame.numerator state.1 :=
    Save.savedState_multiplier Save.ports .normal state.1
  have actualTail : (tail .multiplication stream width bounded outcome).applyVec environment
      (Window.ket (Reset.namedOutcome .numerator Reset.zeroOutcome
        (afterSave .normal state))).vec =
        WalshHadamard.walshSign outcome (Frame.numerator (afterSave .normal state).1) •
          (Window.ket state).vec := by
    rw [originalY]
    exact feedback.trans (congrArg
      (fun final => WalshHadamard.walshSign outcome (Frame.numerator state.1) •
        (Window.ket final).vec) restored)
  exact call_branchOperator_corrected_ket sameWires output mask .multiplication stream width bounded
    distinct store outcome state (afterSave .normal state) state environment reference headAction
    actualTail

end

end Arithmetic.Call

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
