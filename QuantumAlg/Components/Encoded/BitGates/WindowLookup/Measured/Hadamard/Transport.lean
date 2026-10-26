/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Outcome
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Hadamard.Projection
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex

/-!
# Exact retained H columns on the original runtime wire positions

The actual ordered measurement path is used as its projector label. Its
projector agrees with the original physical result-value projector under
complete ordered-wire equality. The native H column and every complement
coordinate are transported by those same physical values, with no gate.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

open Execution

noncomputable section

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {oracles : OracleModel} {services : ClassicalOracleModel}
  {width : Nat}

/-- Local projector labelled by the same actual sequential result-measurement path. -/
def resultPathValueProjector (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width) (output : Fin width → CWriteRef ctx (.finite 2))
    (result : physical.toQuantum.Basis) : HilbertOperator ctx.register :=
  ZMeasurement.projector
    (Circuit.measurementBasisPath (gates := AlgorithmGate.model) (oracles := oracles)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts physical sameWires target output))
    (Circuit.measurementBasisPath (gates := AlgorithmGate.model) (oracles := oracles)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts physical sameWires target output)
      (basisOfEqualWires physical.toQuantum ctx.quantumLayout sameWires result))

/-- The actual runtime path projector transports the original physical value projector exactly. -/
lemma resultPathValueProjector_reindex_applyVec (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width) (output : Fin width → CWriteRef ctx (.finite 2))
    (result : physical.toQuantum.Basis) (vector : HilbertVector physical.toQuantum.register) :
    (resultPathValueProjector (oracles := oracles) (services := services)
      physical sameWires target output result).applyVec
        (HilbertVector.reindex
          (basisOfEqualWires physical.toQuantum ctx.quantumLayout sameWires) vector) =
      HilbertVector.reindex (basisOfEqualWires physical.toQuantum ctx.quantumLayout sameWires)
        ((wordValueProjector physical target result).applyVec vector) := by
  ext row
  rw [resultPathValueProjector, projector_applyVec_any, HilbertVector.reindex_apply,
    HilbertVector.reindex_apply, wordValueProjector, projector_applyVec_any]
  have paths := resultBasisPath_eq_iff (oracles := oracles) (services := services)
    physical sameWires target output
    ((basisOfEqualWires physical.toQuantum ctx.quantumLayout sameWires).symm row) result
  simp only [Equiv.apply_symm_apply] at paths
  exact if_congr (paths.trans ⟨fun same => funext same, fun same index => congrFun same index⟩)
    rfl rfl

private lemma vector_reindex_smul {Source Target : Register}
    (coordinates : Source.Index ≃ Target.Index) (scalar : ℂ) (vector : HilbertVector Source) :
    HilbertVector.reindex coordinates (scalar • vector) =
      scalar • HilbertVector.reindex coordinates vector := by
  ext index
  rfl

/-- The actual placed H bank and actual path projector retain the exact full physical column. -/
lemma resultHadamard_projected_ket (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width)
    (distinct : Function.Injective fun index => (target.bit index).wire)
    (output : Fin width → CWriteRef ctx (.finite 2)) (environment : oracles.Interpretation)
    (input result : physical.toQuantum.Basis)
    (complement : physical.toQuantum.restrictComplementBasis
        (Finset.univ.map (wordPosition target distinct)) result =
      physical.toQuantum.restrictComplementBasis
        (Finset.univ.map (wordPosition target distinct)) input) :
    (resultPathValueProjector (oracles := oracles) (services := services)
      physical sameWires target output result).applyVec
        (((unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
          (wordHadamardProgram physical oracles target distinct)).matrix environment).applyVec
            (NormalizedVector.ket (R := ctx.register)
              (basisOfEqualWires physical.toQuantum ctx.quantumLayout sameWires input)).vec) =
      wordHadamardAmplitude physical target result input •
        (NormalizedVector.ket (R := ctx.register)
          (basisOfEqualWires physical.toQuantum ctx.quantumLayout sameWires result)).vec := by
  let coordinates := basisOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
  have original := wordHadamard_projected_ket physical oracles target distinct environment
    input result complement
  rw [HilbertOperator.mul_applyVec] at original
  have transported := congrArg
    (HilbertVector.reindex (R := physical.toQuantum.register) (S := ctx.register) coordinates)
    original
  rw [vector_reindex_smul, HilbertVector.reindex_ket] at transported
  rw [unitaryOfEqualWires_matrix, ← HilbertVector.reindex_ket
      (R := physical.toQuantum.register) (S := ctx.register) coordinates input,
    UnitaryOperator.reindex_applyVec, resultPathValueProjector_reindex_applyVec]
  exact transported

end

end QuantumAlg.EncodedBit.WindowLookup
