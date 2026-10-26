/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Transport
import all QuantumAlg.Core.Execution.Circuit.OwnedLayoutView
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Components.Classical.Model.BitWord
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting.QuantumTime

/-!
# Actual ordered views of the original 854-system owned window bank

The slices expose the original data bank, C, N, W and the current address.
Their complete ordered physical wire records concatenate to the same bank.
The allocation-free arithmetic child runs through the existing Core view;
the exact interpreter retains all classical values, histories and Reference.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

noncomputable section

open Execution

local instance {Data : Type} : DecidableEq Data := Classical.decEq Data

private lemma placed_trace_in_context {Source Target : Type}
    {source : BinaryLabelEncoding Source} {target : BinaryLabelEncoding Target}
    (placement : EncodedBit.FullPlacement source target)
    {gates : GateModel} {oracles : OracleModel}
    (body : UnitaryCircuit gates oracles (QubitLayout.canonical source.width).toQuantum)
    (operations : ClassicalOpModel) (services : ClassicalOracleModel) :
    (placement.place body).eventTrace operations services =
      body.eventTrace operations services := by
  unfold EncodedBit.FullPlacement.place UnitaryCircuit.placeAt
  change (body.relabel _).eventTrace operations services = _
  exact UnitaryCircuit.relabel_eventTrace _ _ _ _

private def contiguous (offset count : Nat) : QubitLayout count where
  physical_idx index := offset + index.val
  physical_idx_injective := by
    intro left right same
    apply Fin.ext
    change offset + left.val = offset + right.val at same
    exact Nat.add_left_cancel same

private lemma contiguous_append_wires (offset left right : Nat) :
    (contiguous offset left).toQuantum.wires ++
        (contiguous (offset + left) right).toQuantum.wires =
      (contiguous offset (left + right)).toQuantum.wires := by
  change List.ofFn (fun index : Fin left => (⟨offset + index.val, 2⟩ : QuantumWire)) ++
      List.ofFn (fun index : Fin right => (⟨offset + left + index.val, 2⟩ : QuantumWire)) =
    List.ofFn (fun index : Fin (left + right) => (⟨offset + index.val, 2⟩ : QuantumWire))
  rw [← List.ofFn_fin_append]
  apply congrArg List.ofFn
  funext index
  refine Fin.addCases (fun leftIndex => ?_) (fun rightIndex => ?_) index
  · simp only [Fin.append_left, Fin.val_castAdd]
  · simp only [Fin.append_right, Fin.val_natAdd, Nat.add_assoc]

private lemma contiguous_zero_wires (count : Nat) :
    (contiguous 0 count).toQuantum.wires =
      (QubitLayout.canonical count).toQuantum.wires := by
  change List.ofFn (fun index : Fin count => (⟨0 + index.val, 2⟩ : QuantumWire)) =
    List.ofFn (fun index : Fin count => (⟨index.val, 2⟩ : QuantumWire))
  simp only [Nat.zero_add]

/-- Every slice names already resident systems in their original order. -/
def slices (keys : Fin 5 → StorageKey) : List OwnedLayoutSlice :=
  [⟨keys 0, 836, (contiguous 0 836).toQuantum⟩,
    ⟨keys 1, 1, (contiguous 836 1).toQuantum⟩,
    ⟨keys 2, 1, (contiguous 837 1).toQuantum⟩,
    ⟨keys 3, 1, (contiguous 838 1).toQuantum⟩,
    ⟨keys 4, 15, (contiguous 839 15).toQuantum⟩]

lemma slices_wires (keys : Fin 5 → StorageKey) :
    ((slices keys).flatMap fun slice => slice.layout.wires) =
      (QubitLayout.canonical encoding.width).toQuantum.wires := by
  simp only [slices, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [contiguous_append_wires 838 1 15, contiguous_append_wires 837 1 16,
    contiguous_append_wires 836 1 17, contiguous_append_wires 0 836 18]
  rw [encoding_width]
  exact contiguous_zero_wires 854

/-- Lexical storage identities and the actual complete existing owned bank. -/
structure OwnedScope (ctx : RuntimeCtx .quantum) where
  before : List (RuntimeEntry .quantum)
  after : List (RuntimeEntry .quantum)
  bankKey : StorageKey
  originalEntries : ctx.entries = before ++
    .ownedLayout bankKey (QubitLayout.canonical encoding.width).toQuantum :: after
  sliceKeys : Fin 5 → StorageKey
  keysNodup : ((before ++ (slices sliceKeys).map OwnedLayoutSlice.entry ++ after).map
    RuntimeEntry.key).Nodup
  sameWires : (QubitLayout.canonical encoding.width).toQuantum.wires = ctx.quantumLayout.wires

namespace OwnedScope

variable {ctx : RuntimeCtx .quantum} (scope : OwnedScope ctx)

def viewed : RuntimeCtx .quantum :=
  OwnedLayoutView.scopedContext ctx scope.before scope.after scope.bankKey _
    scope.originalEntries (slices scope.sliceKeys) (slices_wires scope.sliceKeys) scope.keysNodup

def view : OwnedLayoutView ctx scope.viewed :=
  OwnedLayoutView.ofSlices ctx scope.before scope.after scope.bankKey _
    scope.originalEntries (slices scope.sliceKeys) (slices_wires scope.sliceKeys) scope.keysNodup

lemma viewed_wires :
    (QubitLayout.canonical encoding.width).toQuantum.wires = scope.viewed.quantumLayout.wires :=
  scope.sameWires.trans ((RuntimeCtx.quantumLayout_wires ctx).trans
    (scope.view.quantumWires_eq.trans (RuntimeCtx.quantumLayout_wires scope.viewed).symm))

def writable {shape : CShape} (ref : CWriteRef ctx shape) : CWriteRef scope.viewed shape where
  toCStorageRef := scope.view.storage ref.toCStorageRef
  writable := ref.writable

lemma writable_read (store : Store ctx) {shape : CShape} (ref : CWriteRef ctx shape) :
    (scope.view.store store).read (.storage (scope.writable ref).toCStorageRef) =
      store.read (.storage ref.toCStorageRef) :=
  scope.view.store_read store ref.toCStorageRef

/-- Every gate is the already certified native body on these identical ordered physical wires. -/
def physicalProgram (stream : Fin 2) (body : Native.Circuit) :
    UnitaryCircuit AlgorithmGate.model .empty scope.viewed.quantumLayout :=
  unitaryOfEqualWires _ _ scope.viewed_wires (program stream body)

def circuit {services : ClassicalOracleModel} (stream : Fin 2) (body : Native.Circuit) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false :=
  .ownedLayoutView scope.view (.unitary (scope.physicalProgram stream body))

lemma circuit_execute {services : ClassicalOracleModel}
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (stream : Fin 2) (body : Native.Circuit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    (scope.circuit stream body).execute environment Reference state =
      scope.view.join ((Circuit.unitary (operations := BitWord.model)
        (classicalOracles := services) (allowAllocation := false)
        (scope.physicalProgram stream body)).execute environment Reference
          (scope.view.split state)) :=
  Circuit.execute_ownedLayoutView scope.view _ environment Reference state

/-- The exact native operator acts on every complete Store/history block beside Reference. -/
lemma circuit_execute_complete {services : ClassicalOracleModel}
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (stream : Fin 2) (body : Native.Circuit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    (scope.circuit stream body).execute environment Reference state =
      scope.view.join (((scope.view.split state).applyUnitary fun _ =>
        UnitaryOperator.prodTensor ((scope.physicalProgram stream body).matrix environment.quantum)
          (1 : UnitaryOperator Reference)).mapClassical
            (fun entry => (entry.1, (entry.2.1, (entry.2.2, ()))))) :=
  (scope.circuit_execute environment stream body Reference state).trans
    (congrArg scope.view.join (Circuit.execute_unitary environment (scope.view.split state)
      (scope.physicalProgram stream body)))

lemma circuit_eventTrace {services : ClassicalOracleModel} (stream : Fin 2)
    (body : Native.Circuit) (path : (scope.circuit (services := services) stream body).Path) :
    (scope.circuit stream body).eventTrace path = body.eventTrace BitWord.model services := by
  change (scope.physicalProgram stream body).eventTrace BitWord.model services = _
  exact (unitaryOfEqualWires_trace _ _ scope.viewed_wires (program stream body)
    BitWord.model services).trans
      (placed_trace_in_context (streamPlacement stream) (suffixProgram body)
        BitWord.model services)

lemma circuit_quantumTime {services : ClassicalOracleModel} (stream : Fin 2)
    (body : Native.Circuit) (path : (scope.circuit (services := services) stream body).Path) :
    (scope.circuit stream body).quantumTime path =
      body.evaluatedEventDepth Resource.Event.quantumDuration := by
  change DepthExpr.depthEval Resource.Event.quantumDuration
    ((scope.physicalProgram stream body).eventDepth BitWord.model services) = _
  rw [physicalProgram, unitaryOfEqualWires_depth]
  exact (UnitaryCircuit.unitaryCircuit_quantumDuration_classical_context
    (program stream body) BitWord.model services).trans (program_quantumTime stream body)

lemma circuit_peakResidentSpace {services : ClassicalOracleModel} (stream : Fin 2)
    (body : Native.Circuit) (path : (scope.circuit (services := services) stream body).Path) :
    (scope.circuit stream body).peakResidentSpace path = ctx.residentSpace := by
  exact (scope.circuit stream body).fixed_peakResidentSpace path

lemma circuit_peakAuxiliarySpace {services : ClassicalOracleModel} (stream : Fin 2)
    (body : Native.Circuit) (path : (scope.circuit (services := services) stream body).Path) :
    (scope.circuit stream body).peakAuxiliarySpace path = ctx.auxiliarySpace := by
  exact (scope.circuit stream body).fixed_peakAuxiliarySpace path

end OwnedScope

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
