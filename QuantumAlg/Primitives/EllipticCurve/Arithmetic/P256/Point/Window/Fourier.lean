/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Enable.Ports
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Owned
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Program
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Execution.Context.OwnedLayoutView

/-!
# Literal recycled Fourier ports on the same 854-system window bank

The selected stream top is original C or W; its remaining bits are the same
15 address systems used by the actual query. The high four-bit tail uses
only the first three address systems. Every other physical system remains
in the complete owned view, and the actual inverse-Fourier program uses the
original two-stream classical result cells. No exponent-sized quantum bank
or runtime permutation is introduced.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Fourier

noncomputable section

open Execution

variable {ctx : RuntimeCtx .quantum} (scope : OwnedScope ctx)

/-- Original retained cells for both complete 260-bit chronological readouts. -/
structure Results (ctx : RuntimeCtx .quantum) where
  cells : QuantumFourierTransform.Semiclassical.Window.BitPosition 260 →
    CWriteRef ctx (.finite 2)
  distinct : Function.Injective (fun index => (cells index).key)

/-- The physical coordinate is induced by equality of the entire ordered wire records. -/
def wire (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (index : Fin (width + 1)) : Fin scope.viewed.systemCount :=
  positionsOfEqualWires (QubitLayout.canonical encoding.width).toQuantum
    scope.viewed.quantumLayout scope.viewed_wires
      (Enable.digitBit stream width bounded index).wire

lemma wire_injective (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) :
    Function.Injective (wire scope stream width bounded) := by
  intro left right same
  exact Enable.digitBit_injective stream width bounded
    ((positionsOfEqualWires _ _ scope.viewed_wires).injective same)

lemma wire_record (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (index : Fin (width + 1)) :
    scope.viewed.quantumLayout.wire (wire scope stream width bounded index) =
      ⟨(Enable.digitBit stream width bounded index).wire.val, 2⟩ :=
  (wireAtCorrespondingPosition _ _ scope.viewed_wires
    (Enable.digitBit stream width bounded index).wire).trans
      (QubitLayout.toQuantum_wire _ _)

/-- Both streams reuse the same suffix, retaining the other stream top and all complements. -/
lemma wire_identity (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (index : Fin (width + 1)) :
    (scope.viewed.quantumLayout.wire (wire scope stream width bounded index)).identity =
      if index.val = 0 then (if stream.val = 0 then 836 else 838)
      else 839 + (index.val - 1) := by
  rw [wire_record]
  exact Enable.digitBit_wire stream width bounded index

/-- Same original result references and the literal selected existing bank. -/
def ports (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (start : Nat) (within : start + (width + 1) ≤ 260) (results : Results ctx) :
    QuantumFourierTransform.Semiclassical.Window.Ports scope.viewed 260 (width + 1) where
  stream := stream
  start := start
  within := within
  wires := ⟨wire scope stream width bounded, wire_injective scope stream width bounded⟩
  qubits := fun index => congrArg QuantumWire.dimension
    (wire_record scope stream width bounded index)
  results := fun position => scope.writable (results.cells position)
  results_injective := by
    intro left right same
    exact results.distinct same

/-- Chronological high tail occupies positions0..3; logical full window15 comes next. -/
def fullStart (logical : Fin 16) : Nat := 4 + 16 * (15 - logical.val)

def fullPorts (stream : Fin 2) (logical : Fin 16) (results : Results ctx) :
    QuantumFourierTransform.Semiclassical.Window.Ports scope.viewed 260 16 :=
  ports scope stream 15 (by omega) (fullStart logical)
    (by have bounded := logical.isLt; unfold fullStart; omega) results

def tailPorts (stream : Fin 2) (results : Results ctx) :
    QuantumFourierTransform.Semiclassical.Window.Ports scope.viewed 260 4 :=
  ports scope stream 3 (by omega) 0 (by omega) results

/-- The physical MSB-first digit reads the original little-endian logical window. -/
lemma fullPorts_sourceBit (stream : Fin 2) (logical : Fin 16) (results : Results ctx)
    (index : Fin 16) :
    ((fullPorts scope stream logical results).sourceBit index).val =
      16 * logical.val + 15 - index.val := by
  change 260 - (fullStart logical + index.val + 1) = _
  have logicalBound := logical.isLt
  have indexBound := index.isLt
  unfold fullStart
  omega

lemma tailPorts_sourceBit (stream : Fin 2) (results : Results ctx) (index : Fin 4) :
    ((tailPorts scope stream results).sourceBit index).val = 259 - index.val := by
  change 260 - (0 + index.val + 1) = _
  have bounded := index.isLt
  omega

/-- Every feedback read is the same original classical cell inside the owned scope. -/
lemma ports_result_read (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (start : Nat) (within : start + (width + 1) ≤ 260) (results : Results ctx)
    (store : Store ctx) (position : QuantumFourierTransform.Semiclassical.Window.BitPosition 260) :
    (scope.view.store store).read
        (.storage ((ports scope stream width bounded start within results).results
          position).toCStorageRef) =
      store.read (.storage (results.cells position).toCStorageRef) :=
  scope.writable_read store (results.cells position)

/-- The whole real H/MZ/feedback/reset recursion executes on these literal ports. -/
def circuit {services : ClassicalOracleModel} (stream : Fin 2) (width : Nat)
    (bounded : width ≤ 15) (start : Nat) (within : start + (width + 1) ≤ 260)
    (results : Results ctx) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false :=
  .ownedLayoutView scope.view
    (QuantumFourierTransform.Semiclassical.Window.inverseCode
      (ports scope stream width bounded start within results))

lemma circuit_execute {services : ClassicalOracleModel}
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (start : Nat) (within : start + (width + 1) ≤ 260) (results : Results ctx)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    (circuit scope stream width bounded start within results).execute environment Reference
        state =
      scope.view.join
        ((QuantumFourierTransform.Semiclassical.Window.inverseCode
          (operations := BitWord.model) (services := services)
          (ports scope stream width bounded start within results)).execute environment
            Reference (scope.view.split state)) :=
  Circuit.execute_ownedLayoutView scope.view _ environment Reference state

lemma circuit_eventTrace {services : ClassicalOracleModel} (stream : Fin 2) (width : Nat)
    (bounded : width ≤ 15) (start : Nat) (within : start + (width + 1) ≤ 260)
    (results : Results ctx)
    (path : (QuantumFourierTransform.Semiclassical.Window.inverseCode
      (operations := BitWord.model) (services := services)
      (ports scope stream width bounded start within results)).Path) :
    (circuit (services := services) scope stream width bounded start within results).eventTrace
        path =
      (QuantumFourierTransform.Semiclassical.Window.inverseCode
        (operations := BitWord.model) (services := services)
        (ports scope stream width bounded start within results)).eventTrace path :=
  Circuit.eventTrace_ownedLayoutView scope.view _ path

lemma circuit_quantumTime {services : ClassicalOracleModel} (stream : Fin 2) (width : Nat)
    (bounded : width ≤ 15) (start : Nat) (within : start + (width + 1) ≤ 260)
    (results : Results ctx)
    (path : (QuantumFourierTransform.Semiclassical.Window.inverseCode
      (operations := BitWord.model) (services := services)
      (ports scope stream width bounded start within results)).Path) :
    (circuit (services := services) scope stream width bounded start within results).quantumTime
        path =
      (QuantumFourierTransform.Semiclassical.Window.inverseCode
        (operations := BitWord.model) (services := services)
        (ports scope stream width bounded start within results)).quantumTime path :=
  Circuit.quantumTime_ownedLayoutView scope.view _ path

lemma circuit_peakResidentSpace {services : ClassicalOracleModel} (stream : Fin 2)
    (width : Nat) (bounded : width ≤ 15) (start : Nat)
    (within : start + (width + 1) ≤ 260) (results : Results ctx)
    (path : (circuit (services := services) scope stream width bounded start within results).Path) :
    (circuit scope stream width bounded start within results).peakResidentSpace path =
      ctx.residentSpace :=
  (circuit scope stream width bounded start within results).fixed_peakResidentSpace path

lemma circuit_peakAuxiliarySpace {services : ClassicalOracleModel} (stream : Fin 2)
    (width : Nat) (bounded : width ≤ 15) (start : Nat)
    (within : start + (width + 1) ≤ 260) (results : Results ctx)
    (path : (circuit (services := services) scope stream width bounded start within results).Path) :
    (circuit scope stream width bounded start within results).peakAuxiliarySpace path =
      ctx.auxiliarySpace :=
  (circuit scope stream width bounded start within results).fixed_peakAuxiliarySpace path

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Fourier
