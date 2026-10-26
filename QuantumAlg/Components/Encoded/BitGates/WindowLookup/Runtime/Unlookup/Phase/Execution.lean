/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Unlookup.Phase.Half
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Unitary.Address

/-!
# Complete actual runtime split-address phase execution

The two real X gates reuse and restore the original top high-address bit.
Every half runs its full paid classical rows on the preceding actual Store.
Every selected operator uses the actual preceding Store. The intended
measured character and clean-prefix restoration are separate correctness laws.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.RuntimeUnlookup

open Execution

noncomputable section

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
  {resultWidth lowWidth highRemaining : Nat}
  (frame : UnlookupFrame encoding resultWidth lowWidth highRemaining)
  (physical : QubitLayout encoding.width)
  (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
  (measured : CInputRef ctx (.bits resultWidth))
  (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit)
  (temporary : CWriteRef ctx .bit)
  (table : Bool → Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) →
    CInputRef ctx (.unsignedWord resultWidth))

/-- The actual native flip of the existing high-address top bit, on the same physical systems. -/
def topFlipProgram : UnitaryCircuit AlgorithmGate.model .empty ctx.quantumLayout :=
  unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
    ((GateSpec.x (frame.high.stack ⟨0, by omega⟩)).program physical .empty)

/-- Complete real records from both paid halves and the two original native flip paths. -/
def phaseRecord (store : Store ctx) : Store ctx ×
    (phaseCircuit frame (services := services)
      physical sameWires measured parity temporary table).Path :=
  let left := halfRecord frame (services := services)
    physical sameWires measured parity temporary (table false) store
  let right := halfRecord frame (services := services)
    physical sameWires measured parity temporary (table true) left.1
  (right.1, ((), (left.2, ((), right.2))))

/-- Exact physical operator product with the true chronological intermediate paid-row Store. -/
def phaseOperator (environment : OracleModel.Interpretation .empty) (store : Store ctx) :
    UnitaryOperator ctx.register :=
  let left := halfRecord frame (services := services)
    physical sameWires measured parity temporary (table false) store
  halfOperator frame (services := services)
      physical sameWires measured parity temporary (table true) environment left.1 *
    (topFlipProgram frame physical sameWires).matrix environment *
    halfOperator frame (services := services)
      physical sameWires measured parity temporary (table false) environment store *
    (topFlipProgram frame physical sameWires).matrix environment

private lemma reference_product {Local Reference : Register}
    (second first : UnitaryOperator Local) :
    UnitaryOperator.prodTensor second (1 : UnitaryOperator Reference) *
        UnitaryOperator.prodTensor first (1 : UnitaryOperator Reference) =
      UnitaryOperator.prodTensor (second * first) (1 : UnitaryOperator Reference) := by
  apply Subtype.ext
  change (UnitaryOperator.prodTensor second (1 : UnitaryOperator Reference) :
      HilbertOperator (Register.prod Local Reference)) *
    (UnitaryOperator.prodTensor first (1 : UnitaryOperator Reference) :
      HilbertOperator (Register.prod Local Reference)) = _
  rw [unitaryOperator_prodTensor_identity, unitaryOperator_prodTensor_identity,
    unitaryOperator_prodTensor_identity, HilbertOperator.kronecker_identity_mul]
  rfl

/-- Both actual halves keep all old Store/history blocks and the arbitrary external reference. -/
lemma phaseCircuit_execute
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    (phaseCircuit frame physical sameWires measured parity temporary table).execute
      environment Reference state =
      (state.applyUnitary fun entry => UnitaryOperator.prodTensor
        (phaseOperator frame (services := services)
          physical sameWires measured parity temporary table environment.quantum entry.1)
        (1 : UnitaryOperator Reference)).mapClassical (fun entry =>
          let result := phaseRecord frame (services := services)
            physical sameWires measured parity temporary table entry.1
          (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  change ((Circuit.unitary (topFlipProgram frame physical sameWires)).seq
    ((halfCircuit frame physical sameWires measured parity temporary (table false)).seq
      ((Circuit.unitary (topFlipProgram frame physical sameWires)).seq
        (halfCircuit frame physical sameWires measured parity temporary (table true))))).execute
          environment Reference state = _
  rw [Circuit.execute_seq, Circuit.execute_unitary, Circuit.execute_seq,
    halfCircuit_execute frame physical sameWires measured parity temporary (table false),
    Circuit.execute_seq, Circuit.execute_unitary,
    halfCircuit_execute frame physical sameWires measured parity temporary (table true)]
  simp only [State.mapHistory, ExecutionState.applyUnitary_mapClassical,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def,
    ExecutionState.executionState_applyUnitary_comp, reference_product, mul_assoc,
    phaseOperator, phaseRecord]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.EncodedBit.WindowLookup.RuntimeUnlookup
