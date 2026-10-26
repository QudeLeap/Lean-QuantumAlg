/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Reset.Correction
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Transport

/-!
# The actual arithmetic prefix and same-record corrected reset operator

Only equality of the complete ordered physical wires transports the native
program. The supplied equations concern this same prefix and mask-selected
tail. Concrete arithmetic consumers discharge them; this composition does
not substitute a unitary for the measured instrument or assert normalized
branch mass without the consumer's input isometry.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Call

noncomputable section

open Execution EncodedBit.WindowLookup NormalizedVector

private lemma reindex_smul {Source Target : Register}
    (coordinates : Source.Index ≃ Target.Index) (scalar : ℂ) (vector : HilbertVector Source) :
    HilbertVector.reindex coordinates (scalar • vector) =
      scalar • HilbertVector.reindex coordinates vector := by
  ext index
  rfl

private lemma normalized_action_vec {count : Nat} {physical : QuantumLayout count}
    (body : UnitaryCircuit AlgorithmGate.model .empty physical)
    (environment : OracleModel.empty.Interpretation)
    (initial final : NormalizedVector physical.register)
    (actual : body.applyNormalized environment initial = final) :
    body.applyVec environment initial.vec = final.vec :=
  congrArg (fun value : NormalizedVector physical.register => value.vec) actual

private lemma placed_reference_smul {count : Nat} (physical : QuantumLayout count)
    {ctx : RuntimeCtx .quantum} (sameWires : physical.wires = ctx.quantumLayout.wires)
    (body : UnitaryCircuit AlgorithmGate.model .empty physical)
    (environment : OracleModel.empty.Interpretation) (initial final : physical.Basis)
    (scalar : ℂ)
    (actual : body.applyVec environment (NormalizedVector.ket initial).vec =
      scalar • (NormalizedVector.ket final).vec)
    {Reference : Register} (reference : Reference.Index) :
    (UnitaryOperator.prodTensor
      ((unitaryOfEqualWires physical ctx.quantumLayout sameWires body).matrix environment)
      (1 : UnitaryOperator Reference)).applyVec
      (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (basisOfEqualWires physical ctx.quantumLayout sameWires initial, reference)).vec =
      scalar • (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (basisOfEqualWires physical ctx.quantumLayout sameWires final, reference)).vec := by
  let coordinates := basisOfEqualWires physical ctx.quantumLayout sameWires
  have original : (body.matrix environment).applyVec
      (NormalizedVector.ket (R := physical.register) initial).vec =
        scalar • (NormalizedVector.ket (R := physical.register) final).vec := actual
  have transported := congrArg
    (HilbertVector.reindex (R := physical.register) (S := ctx.register) coordinates) original
  rw [reindex_smul, HilbertVector.reindex_ket] at transported
  have placed : ((unitaryOfEqualWires physical ctx.quantumLayout sameWires body).matrix
      environment).applyVec (NormalizedVector.ket (R := ctx.register)
        (coordinates initial)).vec =
        scalar • (NormalizedVector.ket (R := ctx.register) (coordinates final)).vec := by
    rw [unitaryOfEqualWires_matrix]
    rw [← HilbertVector.reindex_ket
      (R := physical.register) (S := ctx.register) coordinates initial,
      UnitaryOperator.reindex_applyVec]
    exact transported
  change (UnitaryOperator.prodTensor
    ((unitaryOfEqualWires physical ctx.quantumLayout sameWires body).matrix environment)
    (1 : UnitaryOperator Reference)).applyVec
      (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (coordinates initial, reference)).vec =
      scalar • (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (coordinates final, reference)).vec
  rw [← HilbertVector.prodTensor_ket (R := ctx.register) (S := Reference)
      (coordinates initial) reference,
    ← HilbertVector.prodTensor_ket (R := ctx.register) (S := Reference)
      (coordinates final) reference,
    UnitaryOperator.prodTensor_applyVec_prodTensor, placed, UnitaryOperator.one_applyVec]
  ext index
  simp only [HilbertVector.prodTensor_apply, PiLp.smul_apply, smul_eq_mul]
  exact mul_assoc _ _ _

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (sameWires : (QubitLayout.canonical Window.encoding.width).toQuantum.wires =
      ctx.quantumLayout.wires)
    (output : Fin 256 → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits 256))
    (kind : Kind) (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)

/-- Prefix and paid same-mask character laws yield the common coefficient of the actual Call. -/
lemma call_branchOperator_corrected_ket
    (distinct : Function.Injective fun index => (output index).key)
    (store : Store ctx) (outcome : Word) (initial saved final : Window.Raw)
    (environment : OracleModel.empty.Interpretation) {Reference : Register}
    (reference : Reference.Index)
    (actualPrefix : (beforeReset kind stream width bounded).applyNormalized environment
      (Window.ket initial) = Window.ket saved)
    (actualTail : (tail kind stream width bounded outcome).applyVec environment
      (Window.ket (Reset.namedOutcome .numerator Reset.zeroOutcome saved)).vec =
        WalshHadamard.walshSign outcome (Frame.numerator saved.1) • (Window.ket final).vec) :
    (branchOperator (services := services) sameWires output mask kind stream width bounded store
      (Reset.outcomePath (services := services) .numerator sameWires output outcome saved)
      environment Reference).applyVec
      (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (measuredEncodedBasis (QubitLayout.canonical _) sameWires initial, reference)).vec =
      invSqrt2 ^ 256 • (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (measuredEncodedBasis (QubitLayout.canonical _) sameWires final, reference)).vec := by
  have prefixRaw : (beforeReset kind stream width bounded).applyVec environment
      (Window.ket initial).vec = (1 : ℂ) • (Window.ket saved).vec := by
    rw [one_smul]
    exact normalized_action_vec (beforeReset kind stream width bounded) environment
      (Window.ket initial) (Window.ket saved) actualPrefix
  have headAction := placed_reference_smul
    (QubitLayout.canonical Window.encoding.width).toQuantum sameWires
    (beforeReset kind stream width bounded) environment
    ((QubitLayout.canonical _).basisEquiv.symm (Window.encoding.encode initial))
    ((QubitLayout.canonical _).basisEquiv.symm (Window.encoding.encode saved)) 1 prefixRaw reference
  rw [one_smul] at headAction
  change (prefixOperator sameWires kind stream width bounded environment Reference).applyVec
    (NormalizedVector.ket (R := Register.prod ctx.register Reference)
      (measuredEncodedBasis (QubitLayout.canonical _) sameWires initial, reference)).vec =
        (NormalizedVector.ket (R := Register.prod ctx.register Reference)
          (measuredEncodedBasis (QubitLayout.canonical _) sameWires saved,
            reference)).vec at headAction
  have correction := Reset.Instrument.branchOperator_corrected_ket (services := services)
    .numerator sameWires output mask (tail kind stream width bounded) distinct store outcome
    saved final environment reference (placed_reference_smul
      (QubitLayout.canonical Window.encoding.width).toQuantum sameWires
      (tail kind stream width bounded outcome) environment
      ((QubitLayout.canonical _).basisEquiv.symm
        (Window.encoding.encode (Reset.namedOutcome .numerator Reset.zeroOutcome saved)))
      ((QubitLayout.canonical _).basisEquiv.symm (Window.encoding.encode final)) _ actualTail
      reference)
  unfold branchOperator
  rw [HilbertOperator.mul_applyVec, headAction]
  exact correction

end

end Arithmetic.Call

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
