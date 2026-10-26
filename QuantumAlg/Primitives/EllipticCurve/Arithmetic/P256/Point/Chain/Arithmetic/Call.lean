/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Execution
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Control
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Boundary.Initial
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Phase.Reference
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Swap
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Reset.Instrument

/-!
# The two actual measured arithmetic calls on the original point bank

Division uses a temporary N only while the genuine normal flag is still zero.
Multiplication retains the genuine N and clears only F around both resident
segments. The same measured mask selects each actual paid phase tail. Every
physical numerical swap executes on both control branches.

This allocation-free fragment does not prepare or clear the resident small
seed, load table values, or prepare the genuine normal selector. The complete
enclosing point must establish those actual states and clean its scope.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Call

noncomputable section

open Execution EncodedBit.WindowLookup
open scoped BigOperators

local instance {A : Type} : DecidableEq A := Classical.decEq A
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

inductive Kind where
  | division
  | multiplication
  deriving DecidableEq

/-- Recompute a selected saved product in the real reset Y, using original X and saved A. -/
def phasePorts : PortAssignment where
  source := .work2
  target := .numerator
  multiplier := .work1
  source_target := by decide
  source_multiplier := by decide
  target_multiplier := by decide

/-- Clear only F before the real whole-pool body; the true N is never overwritten. -/
def residentWithNormal (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (body : Native.Circuit) : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical Window.encoding.width).toQuantum :=
  (Window.Enable.inverseProgram stream width bounded).seq
    ((Window.suffixProgram body).seq (Window.Enable.program stream width bounded))

/-- Temporary N=E is used only before the true second-difference N is prepared. -/
def residentWithTemporary (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (body : Native.Circuit) : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical Window.encoding.width).toQuantum :=
  (Control.prepareProgram stream width bounded).seq
    ((Window.suffixProgram body).seq (Control.restoreProgram stream width bounded))

/-- Same-program reused adjoint, actual character correction and unconditional numerical swap. -/
def divisionTail (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (outcome : Fin (2 ^ 256)) : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical Window.encoding.width).toQuantum :=
  (residentWithTemporary stream width bounded Boundary.reusedBackward).seq
    ((Window.suffixProgram (Phase.program phasePorts .enable outcome)).seq Swap.program)

/-- The product is saved before inverse-X; its own reused forward is later fully reversed. -/
def multiplicationTail (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (outcome : Fin (2 ^ 256)) : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical Window.encoding.width).toQuantum :=
  (residentWithNormal stream width bounded Boundary.reusedForward).seq
    ((Window.suffixProgram (Phase.program phasePorts .normal outcome)).seq
      ((residentWithNormal stream width bounded Boundary.reusedBackward).seq Swap.program))

def tail (kind : Kind) (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (outcome : Fin (2 ^ 256)) : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical Window.encoding.width).toQuantum :=
  match kind with
  | .division => divisionTail stream width bounded outcome
  | .multiplication => multiplicationTail stream width bounded outcome

/-- Division's first forward precedes its save; multiplication saves the original X directly. -/
def beforeReset (kind : Kind) (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical Window.encoding.width).toQuantum :=
  match kind with
  | .division => (Control.firstResidentProgram stream width bounded).seq
      (Window.suffixProgram (Save.program Save.ports .enable))
  | .multiplication => Window.suffixProgram (Save.program Save.ports .normal)

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (sameWires : (QubitLayout.canonical Window.encoding.width).toQuantum.wires =
      ctx.quantumLayout.wires)
    (output : Fin 256 → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits 256))
    (kind : Kind) (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)

def firstCircuit : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services)
    ctx ctx false :=
  .unitary (unitaryOfEqualWires (QubitLayout.canonical _).toQuantum ctx.quantumLayout sameWires
    (beforeReset kind stream width bounded))

/-- The actual native unitary contributes its literal Unit path and no Store write. -/
def firstRecord (store : Store ctx) (_outcome : Unit) :
    Store ctx × (firstCircuit (services := services) sameWires kind stream width bounded).Path := by
  change Store ctx × Unit
  exact (store, ())

/-- Actual allocation-free quantum save/reset/native-feedback program with its real mask. -/
def circuit : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services)
    ctx ctx false :=
  (firstCircuit sameWires kind stream width bounded).seq
    (Reset.Instrument.circuit .numerator sameWires output mask (tail kind stream width bounded))

/-- The complete same-run chronological record retains every old Store, hidden state and path. -/
def record (store : Store ctx)
    (outcome : Reset.Instrument.Outcome (services := services) .numerator sameWires output) :
    Store ctx ×
      (circuit (services := services) sameWires output mask kind stream width bounded).Path :=
  let after := Reset.Instrument.record (services := services) .numerator sameWires output mask
    (tail kind stream width bounded) store outcome
  (after.1, ((), after.2))

def prefixOperator (environment : OracleModel.empty.Interpretation) (Reference : Register) :
    HilbertOperator (Register.prod ctx.register Reference) :=
  UnitaryOperator.prodTensor
    ((unitaryOfEqualWires (QubitLayout.canonical _).toQuantum ctx.quantumLayout sameWires
      (beforeReset kind stream width bounded)).matrix environment) (1 : UnitaryOperator Reference)

/-- Every actual mask-selected tail reads the same real Store written by the measured reset. -/
def branchOperator (store : Store ctx)
    (outcome : Reset.Instrument.Outcome (services := services) .numerator sameWires output)
    (environment : OracleModel.empty.Interpretation) (Reference : Register) :
    HilbertOperator (Register.prod ctx.register Reference) :=
  Reset.Instrument.branchOperator .numerator sameWires output mask (tail kind stream width bounded)
      store outcome environment Reference *
    prefixOperator sameWires kind stream width bounded environment Reference

private lemma prefix_block_matrix
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) result :
    (((firstCircuit sameWires kind stream width bounded).execute environment Reference state).block
      result).matrix =
      ∑ original : Store ctx × (services.HiddenState × History), ∑ _outcome : Unit,
        if Execution.Instrument.retainedRecord
            (firstRecord (services := services) sameWires kind stream width bounded)
            original () = result then
          prefixOperator sameWires kind stream width bounded environment.quantum Reference *
            (state.block original).matrix *
            Matrix.conjTranspose
              (prefixOperator sameWires kind stream width bounded environment.quantum Reference)
        else 0 := by
  dsimp only [firstCircuit, Circuit.Path] at result
  unfold firstCircuit
  rw [Circuit.execute_unitary]
  refine (@ExecutionState.mapClassical_block_matrix _ _ _ _ _ _ _ _ result).trans ?_
  simp only [Fintype.sum_unique, ExecutionState.applyUnitary_block,
    DensityOperator.applyUnitary_matrix]
  apply Finset.sum_congr rfl
  intro original _
  simp only [Execution.Instrument.retainedRecord, firstRecord, prefixOperator]
  exact Reset.Instrument.ite_decisions Iff.rfl _ _ _ _

/-- Exact complete blocks of these same literal arithmetic programs on arbitrary input states. -/
lemma circuit_block_matrix
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (result : Store ctx × (services.HiddenState × (History ×
      (circuit sameWires output mask kind stream width bounded).Path))) :
    (((circuit sameWires output mask kind stream width bounded).execute environment Reference
      state).block result).matrix =
      ∑ original : Store ctx × (services.HiddenState × History),
        ∑ outcome : Reset.Instrument.Outcome .numerator sameWires output,
          if Execution.Instrument.retainedRecord
              (record (services := services) sameWires output mask kind stream width bounded)
              original outcome = result then
            branchOperator sameWires output mask kind stream width bounded original.1 outcome
                environment.quantum Reference * (state.block original).matrix *
              (branchOperator sameWires output mask kind stream width bounded original.1 outcome
                environment.quantum Reference).conjTranspose
          else 0 := by
  have actual := Execution.Instrument.execute_sequenceRetainedBlocks
    (firstCircuit sameWires kind stream width bounded)
    (Reset.Instrument.circuit .numerator sameWires output mask (tail kind stream width bounded))
    (firstRecord (services := services) sameWires kind stream width bounded)
    (Reset.Instrument.record (services := services) .numerator sameWires output mask
      (tail kind stream width bounded))
    (fun reference _store (_ : Unit) =>
      prefixOperator sameWires kind stream width bounded environment.quantum reference)
    (fun reference store outcome => Reset.Instrument.branchOperator .numerator sameWires output
      mask (tail kind stream width bounded) store outcome environment.quantum reference)
    environment (prefix_block_matrix sameWires kind stream width bounded environment)
    (Reset.Instrument.circuit_block_matrix .numerator sameWires output mask
      (tail kind stream width bounded) environment) Reference state result
  refine actual.trans ?_
  simp only [Fintype.sum_unique]
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro outcome _
  simp only [Execution.Instrument.retainedRecord, Execution.Instrument.sequenceRetainedRecord,
    firstRecord, record, branchOperator]
  exact Reset.Instrument.ite_decisions Iff.rfl _ _ _ _

end

end Arithmetic.Call

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
