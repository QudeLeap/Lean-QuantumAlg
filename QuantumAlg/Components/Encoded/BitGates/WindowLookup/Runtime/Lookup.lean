/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Model.BitWord.Placement
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Unitary.Split.Reference
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Unitary.Split.Resources
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Circuit
import all QuantumAlg.Core.Execution.Selected.Store
import all QuantumAlg.Core.Execution.Circuit.Allocation
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting.QuantumTime

/-!
# Actual runtime table selection of the physical lookup template

The circuit reads the existing classical array through a real branch. Its
fixed branch family retains the previously proved native masked-X circuit
for that stored array. No environment, witness or mathematical table value
is an argument of the circuit constructor. Every branch keeps the actual
complete Store and its correlations with arbitrary quantum references.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.RuntimeTable

open Execution

noncomputable section

open scoped BigOperators

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {oracles : OracleModel} {services : ClassicalOracleModel}
  {width wordWidth : Nat}

/-- Full untruncated table address, including the original most significant bit. -/
def index (top : Bool) (address : Fin (2 ^ width)) : Fin (2 ^ (width + 1)) :=
  ⟨address.val + if top then 2 ^ width else 0, by
    have bounded := address.isLt
    rw [pow_succ]
    cases top <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega⟩

/-- Decode only the nominal unsigned-word representation read by the actual branch. -/
def wordEncoding : CShape.Value (.unsignedWord wordWidth) → Fin (2 ^ wordWidth)
  | .unsignedWord value => value

/-- The fixed template's literal words are selected by the array value actually read at runtime. -/
def tableValue (stored : CShape.Value (.fixedVector (2 ^ (width + 1))
    (.unsignedWord wordWidth))) (top : Bool) (address : Fin (2 ^ width)) :
    Fin (2 ^ wordWidth) := wordEncoding (stored.get (index top address))

/-- Each template row is exactly a structural read from the same real array. -/
lemma tableValue_read (source : CInputRef ctx
    (.fixedVector (2 ^ (width + 1)) (.unsignedWord wordWidth))) (store : Store ctx)
    (top : Bool) (address : Fin (2 ^ width)) :
    tableValue (store.read source) top address =
      wordEncoding (store.read (.vectorGet source (index top address))) := rfl

/-- One fixed finite branch family reads the actual stored table before its native lookup. -/
def lookupCircuit (source : CInputRef ctx
    (.fixedVector (2 ^ (width + 1)) (.unsignedWord wordWidth)))
    (frame : SelectorFrame encoding width) (target : LookupTarget frame wordWidth)
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires) (height : Nat) :
    Circuit (.quantum AlgorithmGate.model oracles BitWord.model services) ctx ctx false :=
  .branch source fun stored => SelectorFrame.placedCircuit physical sameWires
    (splitLookupProgram frame physical oracles target (tableValue stored) height)

/-- The real read, unchanged Store and exact selected physical matrix share the same record. -/
lemma lookupCircuit_execute (source : CInputRef ctx
    (.fixedVector (2 ^ (width + 1)) (.unsignedWord wordWidth)))
    (frame : SelectorFrame encoding width) (target : LookupTarget frame wordWidth)
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires) (height : Nat)
    (environment : (ExecutionModel.quantum AlgorithmGate.model oracles BitWord.model
      services).Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    (lookupCircuit source frame target physical sameWires height).execute
      environment Reference state =
      (state.applyUnitary fun entry => UnitaryOperator.prodTensor
        ((unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
          (splitLookupProgram frame physical oracles target
            (tableValue (entry.1.read source)) height)).matrix environment.quantum)
          (1 : UnitaryOperator Reference)).mapClassical
        (fun entry => (entry.1, (entry.2.1, (entry.2.2, ⟨entry.1.read source, ()⟩)))) :=
  Circuit.selectedUnitary_execute source (fun stored =>
    unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
      (splitLookupProgram frame physical oracles target (tableValue stored) height))
    environment state

/-- The actually selected native matrix gives dirty-target XOR on arbitrary coherent inputs. -/
lemma lookupBranch_coherent_reference (source : CInputRef ctx
    (.fixedVector (2 ^ (width + 1)) (.unsignedWord wordWidth))) (store : Store ctx)
    (frame : SelectorFrame encoding width) (target : LookupTarget frame wordWidth)
    (physical : QubitLayout encoding.width) (height : Nat) (covered : wordWidth ≤ 2 ^ height)
    (environment : oracles.Interpretation)
    {Reference : Register} {Index : Type} [Fintype Index] (state : Index → Data)
    (clean : ∀ label, frame.CleanFrom 0 (state label))
    (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    (splitLookupReferenceOperator frame physical oracles target
      (tableValue (store.read source)) height environment Reference).applyVec
      (∑ label, amplitude label •
        (NormalizedVector.ket (R := Register.prod physical.toQuantum.register Reference)
          (physical.basisEquiv.symm (encoding.encode (state label)), reference label)).vec) =
      ∑ label, amplitude label •
        (NormalizedVector.ket (R := Register.prod physical.toQuantum.register Reference)
          (physical.basisEquiv.symm (encoding.encode
            (splitLookupStep frame target (tableValue (store.read source)) (state label))),
              reference label)).vec :=
  splitLookup_coherent_reference frame physical oracles target
    (tableValue (store.read source)) height covered environment state clean reference amplitude

/-- Every actual branch retains exactly the selected template's native event pool. -/
lemma lookupCircuit_resourcePool (source : CInputRef ctx
    (.fixedVector (2 ^ (width + 1)) (.unsignedWord wordWidth)))
    (frame : SelectorFrame encoding width) (target : LookupTarget frame wordWidth)
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires) (height : Nat)
    (path : (lookupCircuit (oracles := oracles) (services := services)
      source frame target physical sameWires height).Path) :
    (lookupCircuit source frame target physical sameWires height).resourcePool path =
      (splitLookupProgram frame physical oracles target (tableValue path.1) height).eventCost
        BitWord.model services := by
  rcases path with ⟨stored, selected⟩
  change ResourcePool.ofList
    ((unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
      (splitLookupProgram frame physical oracles target (tableValue stored) height)).eventTrace
        BitWord.model services) = _
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost
    (unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
      (splitLookupProgram frame physical oracles target (tableValue stored) height))
        BitWord.model services, unitaryOfEqualWires_cost]

/-- Runtime table selection keeps the actual parallel masked-X CNOT ceiling. -/
lemma lookupCircuit_cnot_count_le (source : CInputRef ctx
    (.fixedVector (2 ^ (width + 1)) (.unsignedWord wordWidth)))
    (frame : SelectorFrame encoding width) (target : LookupTarget frame wordWidth)
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires) (height : Nat)
    (covered : wordWidth ≤ 2 ^ height)
    (path : (lookupCircuit (oracles := oracles) (services := services)
      source frame target physical sameWires height).Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles BitWord.model services) (.gate .cnot)
      ((lookupCircuit source frame target physical sameWires height).resourcePool path) ≤
        2 * (2 ^ width - 1) + 2 * 2 ^ width * (2 * wordWidth - 1) := by
  rw [lookupCircuit_resourcePool,
    UnitaryCircuit.unitaryCircuit_event_count_classical_context]
  exact splitLookupProgram_cnot_count_le frame physical oracles target
    (tableValue path.1) height covered

/-- No systems are added when the same native template is selected by an actual stored array. -/
lemma lookupCircuit_peakResidentSpace (source : CInputRef ctx
    (.fixedVector (2 ^ (width + 1)) (.unsignedWord wordWidth)))
    (frame : SelectorFrame encoding width) (target : LookupTarget frame wordWidth)
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires) (height : Nat)
    (path : (lookupCircuit (oracles := oracles) (services := services)
      source frame target physical sameWires height).Path) :
    (lookupCircuit source frame target physical sameWires height).peakResidentSpace path =
      ctx.residentSpace := Circuit.fixed_peakResidentSpace _ _

end

end QuantumAlg.EncodedBit.WindowLookup.RuntimeTable
