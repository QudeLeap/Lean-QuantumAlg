/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Layout
import all QuantumAlg.Primitives.ShortDLP.Oracle.Stage
import all QuantumAlg.Core.Execution.Context.Layout.Unitary

/-!
# The declared short-DLP member on the original factoring bank

The parameter fixes one reversible group-operation query. Its complete
prepare-query-readout stage is placed on the bank's unchanged ordered wires.
Equal-wire transport adds no operation or new oracle capability.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native

noncomputable section

private abbrev stageLayout (N : Nat) : QuantumLayout
    (ShortDLP.totalQubits (parameters N)) :=
  (QuantumSignature.qubits (ShortDLP.totalQubits (parameters N))).canonicalPlacement.layout

private theorem stageLayout_wires (N : Nat) :
    (stageLayout N).wires = (layout N).wires := rfl

private theorem stageLayout_eq_layout (N : Nat) :
    stageLayout N = layout N := by
  apply QuantumLayout.eq_of_wire_eq
  funext index
  rfl

variable {ctx : RuntimeCtx .quantum} (N : Nat)
  (sameWires : ctx.quantumWires = (layout N).wires)

include sameWires in
private theorem stageContextWires :
    (stageLayout N).wires = ctx.quantumLayout.wires :=
  (stageLayout_wires N).trans (ctx.quantumLayout_wires.trans sameWires).symm

include sameWires in
/-- Binary coordinates of the fixed declared stage on the live original bank. -/
def declaredBasisEquiv : ctx.register.Index ≃
    (Qubits (ShortDLP.totalQubits (parameters N))).Index :=
  (Execution.basisOfEqualWires (stageLayout N) ctx.quantumLayout
    (stageContextWires N sameWires)).symm.trans
      (QuantumSignature.qubitsIndexEquiv
        (ShortDLP.totalQubits (parameters N)))

include sameWires in
/-- The declared stage's binary labels coincide with the original bank's
source labels, including all group-workspace coordinates. -/
theorem declaredBasisEquiv_eq_basisEquiv :
    declaredBasisEquiv N sameWires = basisEquiv N sameWires := by
  unfold declaredBasisEquiv basisEquiv
  cases stageLayout_eq_layout N
  rfl

include sameWires in
/-- The model-owned full short-DLP stage on the actual original-width bank. -/
def declaredMember (input : Input N) (parameter : (ParameterShape N).Value) :
    UnitaryCircuit AlgorithmGate.model
      (ShortDLP.declaredModel (encoding input))
      ctx.quantumLayout :=
  Execution.unitaryOfEqualWires (stageLayout N) ctx.quantumLayout
    (stageContextWires N sameWires)
    (ShortDLP.DeclaredStage.circuit (encoding input)
      (parameterUnit parameter) (parameterTarget parameter))

/-- Placement transports the exact complete operator, including the one
declared group permutation, into the live bank basis. -/
theorem declaredMember_matrix (input : Input N)
    (parameter : (ParameterShape N).Value) :
    (declaredMember N sameWires input parameter).matrix =
      UnitaryOperator.reindex
        (Execution.basisOfEqualWires (stageLayout N) ctx.quantumLayout
          (stageContextWires N sameWires))
        (ShortDLP.DeclaredStage.circuit (encoding input)
          (parameterUnit parameter) (parameterTarget parameter)).matrix := by
  exact Execution.unitaryOfEqualWires_matrix (stageLayout N) ctx.quantumLayout
    (stageContextWires N sameWires) _

/-- Equal-wire placement preserves the exact charged event ledger. -/
theorem declaredMember_eventCost (input : Input N)
    (parameter : (ParameterShape N).Value) :
    (declaredMember N sameWires input parameter).eventCost =
      (ShortDLP.DeclaredStage.circuit (encoding input)
        (parameterUnit parameter) (parameterTarget parameter)).eventCost := by
  exact Execution.unitaryOfEqualWires_cost (stageLayout N) ctx.quantumLayout
    (stageContextWires N sameWires) _ .empty .empty

/-- The physically placed member still makes exactly one group-operation query. -/
theorem declaredMember_groupQueryCount (input : Input N)
    (parameter : (ParameterShape N).Value) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model
        (ShortDLP.declaredModel (encoding input)))
      (.oracle .groupOperation)
      (declaredMember N sameWires input parameter).eventCost = 1 := by
  rw [declaredMember_eventCost]
  exact ShortDLP.DeclaredStage.circuit_groupQueryCount (encoding input)
    (parameterUnit parameter) (parameterTarget parameter)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native
