/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.GateModel.Algorithm

import all QuantumAlg.Core.Execution.Instrument.Execution
import all QuantumAlg.Core.Execution.Instrument.Reference
import all
QuantumAlg.Core.Execution.Instrument.Basic
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Base.Tensor.Reference

/-!
# Exact local instruments of actual native unitary nodes

The operator is the original native program's matrix on the same full
physical context. Its real unique Path and unchanged Store accompany that
matrix. No arithmetic correctness or input-domain premise is needed.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Locality

noncomputable section

open Execution
open scoped BigOperators Kronecker

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

/-- The ordinary tensor-identity matrix has the same explicit local/reference entries. -/
lemma kronecker_referenceLift {Local Reference : Register} (operator : HilbertOperator Local) :
    operator ⊗ₖ (1 : HilbertOperator Reference) = Execution.Instrument.referenceLift Reference
      operator := by
  ext row column
  rw [Matrix.kronecker_apply]
  by_cases same : row.2 = column.2
  · simp only [Execution.Instrument.referenceLift, Matrix.one_apply, if_pos same]
  · simp only [Execution.Instrument.referenceLift, Matrix.one_apply, if_neg same]

/-- The actual tensor unitary uses that same complete local Kraus representation. -/
lemma unitary_referenceLift {Local Reference : Register} (operator : UnitaryOperator Local) :
    (UnitaryOperator.prodTensor operator (1 : UnitaryOperator Reference) :
      HilbertOperator (Local.prod Reference)) =
      Execution.Instrument.referenceLift Reference (operator : HilbertOperator Local) :=
  (unitaryOperator_prodTensor_identity operator).trans (kronecker_referenceLift _)

variable {ctx : RuntimeCtx .quantum} {operations : ClassicalOpModel}
  {services : ClassicalOracleModel} {allowAllocation : Bool}

/-- Full actual execution equation of the same native word, including its unique real Path. -/
def nativeInstrument (program : UnitaryCircuit AlgorithmGate.model .empty ctx.quantumLayout)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) :
    Execution.Instrument (Circuit.unitary (operations := operations) (classicalOracles := services)
      (allowAllocation := allowAllocation) program) Unit environment where
  record store _ := (store, ())
  operator _ _ := (program.matrix environment.quantum : HilbertOperator ctx.register)
  blocks := by
    intro Reference History _ state result
    rcases result with ⟨store, hidden, history, path⟩
    cases path
    refine (Circuit.execute_unitary_block_matrix (quantumEnvironment := environment)
      state program store hidden history).trans ?_
    simp only [Fintype.sum_unique, unitary_referenceLift]
    symm
    rw [Finset.sum_eq_single (store, (hidden, history))]
    · simp only [Execution.Instrument.retainedRecord]
      exact if_pos trivial
    · intro original _ different
      simp only [Execution.Instrument.retainedRecord]
      refine if_neg ?_
      intro same
      exact different (congrArg (fun value : Store ctx ×
        (services.HiddenState × (History × Unit)) =>
          (value.1, (value.2.1, value.2.2.1))) same)
    · intro absent
      exact (absent (Finset.mem_univ _)).elim

end

end Locality

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
