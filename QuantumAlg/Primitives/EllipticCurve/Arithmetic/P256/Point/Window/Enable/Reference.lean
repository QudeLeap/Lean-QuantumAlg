/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Enable.Program
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Transport
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Reference

/-! # Actual complete enable computation beside arbitrary coherent data and Reference -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Enable

noncomputable section

open scoped BigOperators

lemma program_ket (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (environment : OracleModel.empty.Interpretation) (state : Raw) :
    (program stream width bounded).applyNormalized environment (ket state) =
      ket (step stream width bounded state) :=
  (program_realizes stream width bounded environment).apply_encoded_ket state

lemma inverseProgram_ket (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (environment : OracleModel.empty.Interpretation) (state : Raw) :
    (inverseProgram stream width bounded).applyNormalized environment (ket state) =
      ket (step stream width bounded state) :=
  (inverseProgram_realizes stream width bounded environment).apply_encoded_ket state

/-- The literal reversed native list clears the enable produced by the same actual forward. -/
lemma inverseProgram_after_program (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (environment : OracleModel.empty.Interpretation) (state : Raw) :
    (inverseProgram stream width bounded).applyNormalized environment
        ((program stream width bounded).applyNormalized environment (ket state)) = ket state := by
  rw [program_ket, inverseProgram_ket, step_step]

def referenceOperator (body : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical encoding.width).toQuantum)
    (environment : OracleModel.empty.Interpretation) (Reference : Register) :
    HilbertOperator ((QubitLayout.canonical encoding.width).toQuantum.register.prod Reference) :=
  UnitaryOperator.prodTensor (body.matrix environment) (1 : UnitaryOperator Reference)

/-- No normalization, separability, enable-zero or work-zero premise is imposed on the sum. -/
lemma program_reference (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (environment : OracleModel.empty.Interpretation) {Reference : Register}
    {Index : Type} [Fintype Index] (states : Index → Raw)
    (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    HilbertOperator.applyVec
        (referenceOperator (program stream width bounded) environment Reference)
        (referenceVector states reference amplitude) =
      referenceVector (fun index => step stream width bounded (states index)) reference amplitude :=
  Native.reference_sum_of_actual (program stream width bounded) environment _ _
    (fun index => program_ket stream width bounded environment (states index)) reference amplitude

lemma inverseProgram_reference (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (environment : OracleModel.empty.Interpretation) {Reference : Register}
    {Index : Type} [Fintype Index] (states : Index → Raw)
    (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    HilbertOperator.applyVec
        (referenceOperator (inverseProgram stream width bounded) environment Reference)
        (referenceVector states reference amplitude) =
      referenceVector (fun index => step stream width bounded (states index)) reference amplitude :=
  Native.reference_sum_of_actual (inverseProgram stream width bounded) environment _ _
    (fun index => inverseProgram_ket stream width bounded environment (states index))
    reference amplitude

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Enable
