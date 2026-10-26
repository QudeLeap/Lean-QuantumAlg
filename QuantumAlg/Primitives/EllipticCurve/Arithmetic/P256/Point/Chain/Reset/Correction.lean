/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Reset.Instrument
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Reset.Coherent

/-!
# Same-record character cancellation by an actual native feedback tail

The premise concerns the supplied actual feedback circuit, selected by the
same real post-reset Store. Its arithmetic and phase law must be discharged
by the concrete caller. The conclusion gives the exact common coefficient
of that same complete retained instrument; it assumes no free phase operator
and makes no branch-normalization claim without an input isometry.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Reset

namespace Instrument

noncomputable section

open Execution EncodedBit.WindowLookup NormalizedVector
open scoped BigOperators

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (port : WordPort)
    (sameWires : (QubitLayout.canonical Window.encoding.width).toQuantum.wires =
      ctx.quantumLayout.wires)
    (output : Fin 256 → CWriteRef ctx (.finite 2))
    (mask : CWriteRef ctx (.bits 256))
    (tail : Fin (2 ^ 256) → UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical Window.encoding.width).toQuantum)

/-- The physical reset record and its packed Store are exactly those used by feedback. -/
lemma resetRecord_nextStore (store : Store ctx) (outcome : Fin (2 ^ 256)) (state : Window.Raw) :
    (resetRecord (services := services) port sameWires output mask store
      (outcomePath port sameWires output outcome state)).1 =
      nextStore (services := services) port sameWires output mask store outcome state := rfl

/-- The same actual mask-selected circuit cancels the exact original H character. -/
lemma branchOperator_corrected_ket
    (distinct : Function.Injective fun index => (output index).key)
    (store : Store ctx) (outcome : Fin (2 ^ 256)) (state final : Window.Raw)
    (environment : OracleModel.empty.Interpretation) {Reference : Register}
    (reference : Reference.Index)
    (actualTail :
      (UnitaryOperator.prodTensor
        ((unitaryOfEqualWires (QubitLayout.canonical _).toQuantum ctx.quantumLayout sameWires
          (tail outcome)).matrix environment) (1 : UnitaryOperator Reference)).applyVec
        (NormalizedVector.ket (R := Register.prod ctx.register Reference)
          (measuredEncodedBasis (QubitLayout.canonical _) sameWires
            (namedOutcome port zeroOutcome state), reference)).vec =
        WalshHadamard.walshSign outcome (port.value state.1) •
          (NormalizedVector.ket (R := Register.prod ctx.register Reference)
            (measuredEncodedBasis (QubitLayout.canonical _) sameWires final, reference)).vec) :
    (branchOperator (services := services) port sameWires output mask tail store
      (outcomePath port sameWires output outcome state) environment Reference).applyVec
      (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (measuredEncodedBasis (QubitLayout.canonical _) sameWires state, reference)).vec =
      invSqrt2 ^ 256 • (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (measuredEncodedBasis (QubitLayout.canonical _) sameWires final, reference)).vec := by
  have maskValue := (congrArg
    (fun selected : Store ctx => resultConstant (selected.read (.storage mask.toCStorageRef)))
      (resetRecord_nextStore (services := services) port sameWires output mask store outcome
        state)).trans
    (nextStore_mask (services := services) port sameWires output distinct mask store outcome state)
  have actual := Reset.branchOperator_ket (services := services) port sameWires output distinct mask
    store outcome
    state environment reference
  have feedbackEquality := congrArg
    (fun value => UnitaryOperator.prodTensor
      ((unitaryOfEqualWires (QubitLayout.canonical _).toQuantum ctx.quantumLayout sameWires
        (tail value)).matrix environment) (1 : UnitaryOperator Reference)) maskValue
  have correction := (congrArg
    (fun operator : UnitaryOperator (Register.prod ctx.register Reference) => operator.applyVec
      (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (measuredEncodedBasis (QubitLayout.canonical _) sameWires
          (namedOutcome port zeroOutcome state), reference)).vec) feedbackEquality).trans actualTail
  unfold branchOperator feedbackOperator
  change HilbertOperator.applyVec (R := Register.prod ctx.register Reference) _ _ = _ at correction
  change (measuredWordKraus (QubitLayout.canonical _) sameWires (Window.resultWord port)
    (Window.resultWord_distinct port) output mask store
    (outcomePath port sameWires output outcome state) environment Reference).applyVec _ = _
      at actual
  rw [HilbertOperator.mul_applyVec, actual, HilbertOperator.applyVec_smul, correction, smul_smul]
  have square := @WalshHadamard.walshSign_mul_self 256 outcome (port.value state.1)
  have coefficient : (invSqrt2 ^ 256 * WalshHadamard.walshSign outcome (port.value state.1)) *
      WalshHadamard.walshSign outcome (port.value state.1) = invSqrt2 ^ 256 := by
    rw [mul_assoc, square, mul_one]
  exact congrArg (fun scalar : ℂ => scalar • (NormalizedVector.ket
    (R := Register.prod ctx.register Reference)
    (measuredEncodedBasis (QubitLayout.canonical _) sameWires final, reference)).vec) coefficient

/-- A single actual outcome retains coherent active/inactive labels with the same coefficient. -/
lemma branchOperator_corrected_coherent
    (distinct : Function.Injective fun index => (output index).key)
    (store : Store ctx) (outcome : Fin (2 ^ 256)) (anchor : Window.Raw)
    (environment : OracleModel.empty.Interpretation) {Reference : Register}
    {Index : Type} [Fintype Index] (states final : Index → Window.Raw)
    (reference : Index → Reference.Index) (amplitude : Index → ℂ)
    (actualTail : ∀ index,
      (UnitaryOperator.prodTensor
        ((unitaryOfEqualWires (QubitLayout.canonical _).toQuantum ctx.quantumLayout sameWires
          (tail outcome)).matrix environment) (1 : UnitaryOperator Reference)).applyVec
        (NormalizedVector.ket (R := Register.prod ctx.register Reference)
          (measuredEncodedBasis (QubitLayout.canonical _) sameWires
            (namedOutcome port zeroOutcome (states index)), reference index)).vec =
        WalshHadamard.walshSign outcome (port.value (states index).1) •
          (NormalizedVector.ket (R := Register.prod ctx.register Reference)
            (measuredEncodedBasis (QubitLayout.canonical _) sameWires (final index),
              reference index)).vec) :
    (branchOperator (services := services) port sameWires output mask tail store
      (outcomePath port sameWires output outcome anchor) environment Reference).applyVec
      (∑ index, amplitude index • (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (measuredEncodedBasis (QubitLayout.canonical _) sameWires (states index),
          reference index)).vec) =
      ∑ index, (amplitude index * invSqrt2 ^ 256) •
        (NormalizedVector.ket (R := Register.prod ctx.register Reference)
          (measuredEncodedBasis (QubitLayout.canonical _) sameWires (final index),
            reference index)).vec := by
  rw [HilbertOperator.applyVec_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [HilbertOperator.applyVec_smul]
  have actual := branchOperator_corrected_ket (services := services) port sameWires output mask
    tail distinct store outcome (states index) (final index) environment (reference index)
    (actualTail index)
  have samePath := outcomePath_eq (services := services) port sameWires output outcome
    anchor (states index)
  have sameOperator := congrArg
    (fun path => branchOperator (services := services) port sameWires output mask tail store
      path environment Reference) samePath
  have column := (congrArg
    (fun operator : HilbertOperator (Register.prod ctx.register Reference) => operator.applyVec
      (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (measuredEncodedBasis (QubitLayout.canonical _) sameWires (states index),
          reference index)).vec) sameOperator).trans actual
  exact (congrArg (fun vector => amplitude index • vector) column).trans (smul_smul _ _ _)

end

end Instrument

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Reset
