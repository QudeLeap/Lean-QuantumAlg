/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Execution
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Query.Insertion
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Cycle.Inserted

/-!
# Complete instrument of the actual point-window query

The complete arbitrary-input equation concerns the same load, native
arithmetic and same-table measured unlookup executed by QueryDirect.
It retains every actual Store, persistent service state, old History,
measurement record and external Reference. No graph or good-input
assumption is needed for this interpreter equation.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace QueryInsertion

noncomputable section

open Execution EncodedBit.WindowLookup
open scoped BigOperators

local instance {A : Type} : DecidableEq A := Classical.decEq A
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    {lowWidth highRemaining : Nat}

/-- The literal query's full output blocks use its actual loader/body/unlookup Kraus product. -/
lemma circuit_block_matrix
    (parameters : RuntimeTable.CycleParameters encoding ctx 256 lowWidth highRemaining)
    (body : UnitaryCircuit AlgorithmGate.model .empty ctx.quantumLayout)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (result : Store ctx × (services.HiddenState ×
      (History × (circuit (services := services) parameters body).Path))) :
    (((circuit parameters body).execute environment Reference state).block result).matrix =
      ∑ original : Store ctx × (services.HiddenState × History), ∑ path,
        if Execution.Instrument.retainedRecord (parameters.insertedRecord (services := services)
          body) original path =
            result then
          parameters.insertedBranchOperator body original.1 path environment.quantum Reference *
            (state.block original).matrix *
            (parameters.insertedBranchOperator body original.1 path
              environment.quantum Reference).conjTranspose
        else 0 := by
  have actual := parameters.insertedCircuit_block_matrix body environment Reference state result
  refine actual.trans ?_
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro path _
  split_ifs <;> rfl

end

end QueryInsertion

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
