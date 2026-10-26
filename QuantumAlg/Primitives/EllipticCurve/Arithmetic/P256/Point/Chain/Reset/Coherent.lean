/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Reset.Branch
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Outcome

/-! # One physical outcome path across arbitrary coherent original-word labels -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Reset

noncomputable section

open Execution EncodedBit.WindowLookup NormalizedVector
open scoped BigOperators

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (port : WordPort)
    (sameWires : (QubitLayout.canonical Window.encoding.width).toQuantum.wires =
      ctx.quantumLayout.wires)
    (output : Fin 256 → CWriteRef ctx (.finite 2))

/-- The actual physical outcome path depends on no original complement value. -/
lemma outcomePath_eq (outcome : Fin (2 ^ 256)) (first second : Window.Raw) :
    outcomePath (services := services) port sameWires output outcome first =
      outcomePath (services := services) port sameWires output outcome second := by
  apply (resultBasisPath_eq_iff (oracles := .empty) (services := services)
    (QubitLayout.canonical _) sameWires (Window.resultWord port) output _ _).mpr
  intro index
  rw [encodedPhysicalBit, encodedPhysicalBit]
  have same : ((Window.resultWord port).bit index).get (namedOutcome port outcome first) =
      ((Window.resultWord port).bit index).get (namedOutcome port outcome second) :=
    (resultSetConstant_get (Window.resultWord port) (Window.resultWord_distinct port)
      outcome first index).trans
      (resultSetConstant_get (Window.resultWord port) (Window.resultWord_distinct port)
        outcome second index).symm
  exact congrArg (fun bit => Fin.cast rfl (finTwoEquiv.symm bit)) same

lemma nextStore_eq (mask : CWriteRef ctx (.bits 256)) (store : Store ctx)
    (outcome : Fin (2 ^ 256)) (first second : Window.Raw) :
    nextStore (services := services) port sameWires output mask store outcome first =
      nextStore (services := services) port sameWires output mask store outcome second :=
  congrArg (measuredWordFinalStore (oracles := .empty) (services := services)
    (QubitLayout.canonical _) sameWires (Window.resultWord port) output mask store)
    (outcomePath_eq port sameWires output outcome first second)

lemma branchOperator_eq (mask : CWriteRef ctx (.bits 256)) (store : Store ctx)
    (outcome : Fin (2 ^ 256)) (first second : Window.Raw)
    (environment : OracleModel.empty.Interpretation) (Reference : Register) :
    branchOperator (services := services) port sameWires output mask store outcome first
        environment Reference =
      branchOperator (services := services) port sameWires output mask store outcome second
        environment Reference :=
  congrArg (fun path => measuredWordKraus (QubitLayout.canonical _) sameWires
    (Window.resultWord port) (Window.resultWord_distinct port) output mask store path
      environment Reference) (outcomePath_eq port sameWires output outcome first second)

/-- A single actual retained outcome acts linearly on arbitrary correlated original labels. -/
lemma branchOperator_coherent
    (distinct : Function.Injective fun index => (output index).key)
    (mask : CWriteRef ctx (.bits 256)) (store : Store ctx) (outcome : Fin (2 ^ 256))
    (anchor : Window.Raw) (environment : OracleModel.empty.Interpretation)
    {Reference : Register} {Index : Type} [Fintype Index]
    (states : Index → Window.Raw) (reference : Index → Reference.Index)
    (amplitude : Index → ℂ) :
    (branchOperator (services := services) port sameWires output mask store outcome anchor
      environment Reference).applyVec
      (∑ index, amplitude index • (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (measuredEncodedBasis (QubitLayout.canonical _) sameWires (states index),
          reference index)).vec) =
      ∑ index, (amplitude index *
        (invSqrt2 ^ 256 * WalshHadamard.walshSign outcome (port.value (states index).1))) •
          (NormalizedVector.ket (R := Register.prod ctx.register Reference)
            (measuredEncodedBasis (QubitLayout.canonical _) sameWires
              (namedOutcome port zeroOutcome (states index)), reference index)).vec := by
  rw [HilbertOperator.applyVec_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [HilbertOperator.applyVec_smul]
  have actual := branchOperator_ket (services := services) port sameWires output distinct mask
    store outcome
    (states index) environment (reference index)
  have same := branchOperator_eq (services := services) port sameWires output mask store outcome
    (states index) anchor environment Reference
  have column := (congrArg (fun operator : HilbertOperator (Register.prod ctx.register Reference) =>
    operator.applyVec (NormalizedVector.ket (R := Register.prod ctx.register Reference)
      (measuredEncodedBasis (QubitLayout.canonical _) sameWires (states index),
        reference index)).vec) same).symm.trans actual
  exact (congrArg (fun vector => amplitude index • vector) column).trans (smul_smul _ _ _)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Reset
