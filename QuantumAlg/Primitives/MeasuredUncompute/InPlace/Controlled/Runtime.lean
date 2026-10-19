/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Controlled.Native
import all QuantumAlg.Core.Execution.Selected.Unitary
import all QuantumAlg.Core.Base.Accounting.Context.Embedding.Construction
import all QuantumAlg.Core.Execution.Composition.Resources

/-!
# The actual coherently controlled measured arithmetic body

All native instructions act on the one already allocated owned context.
The existing H/Z/write/read/reset program is physically framed beside the
owned control. Its finite result read selects the same native suffix proved
separately. Quantum activation never reads or measures the control.
This extends the original measured arithmetic sequence
[LYL+26, sec_point_add/sec_point_add.tex:52-121].
-/

namespace QuantumAlg.MeasuredUncompute.InPlaceControlled

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open Execution MAU.Inversion.SharedEEA ContextUnion

/-- Execute the complete native word at its unchanged physical identities in the real context. -/
def runtimeProgram (width : Nat) (native : NativeCircuit width) :
    UnitaryCircuit AlgorithmGate.model .empty (context width).quantumLayout :=
  UnitaryCircuit.placeAt (nativeLayout width).toQuantum (context width).quantumLayout
    (nativePosition width) (nativePosition_dimensions width) native

/-- Exact matrix entries read the complete original physical placement. -/
lemma runtimeProgram_matrix (width : Nat) (native : NativeCircuit width)
    (row column : (context width).register.Index) :
    ((runtimeProgram width native).matrix environment) row column =
      (native.matrix environment) (nativeBasis width row) (nativeBasis width column) := by
  rw [runtimeProgram, UnitaryCircuit.placeAt_matrix]
  exact UnitaryCircuit.operatorAt_entry_of_surjective _ _ _ _
    (nativePosition_surjective width) _ row column

/-- Physical placement preserves the ordered actual native trace. -/
lemma runtimeProgram_trace (width : Nat) (native : NativeCircuit width) :
    (runtimeProgram width native).eventTrace = native.eventTrace :=
  UnitaryCircuit.placeAt_eventTrace _ _ _ _ _

/-- Every actual native coordinate keeps exactly its original multiplicity. -/
lemma runtimeProgram_cost (width : Nat) (native : NativeCircuit width) :
    (runtimeProgram width native).eventCost = native.eventCost :=
  UnitaryCircuit.placeAt_eventCost _ _ _ _ _

/-- The typed unitary instruction executes exactly the physically placed native word. -/
def nativeCode (width : Nat) (native : NativeCircuit width) (allowAllocation : Bool := true) :
    Circuit (.quantum AlgorithmGate.model .empty) (context width) (context width) allowAllocation :=
  .unitary (runtimeProgram width native)

/-- The unconditional measured reset executes as an original child beside the resident control. -/
def reset (width : Nat) (allowAllocation : Bool := true) :
    Circuit (.quantum AlgorithmGate.model .empty) (context width) (context width) allowAllocation :=
  .embed (ContextEmbedding.alongUnion (NumeratorMeasurement.context width)
    (controlContext width) (control_disjoint width))
      (NumeratorReset.code width (allowAllocation := false))

/-- The same real finite cells select the suffix, without reading the quantum control. -/
def selectedSuffix (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) (allowAllocation : Bool := true) :
    Circuit (.quantum AlgorithmGate.model .empty) (context modulus.size) (context modulus.size)
      allowAllocation :=
  .branch (resultInput modulus.size) (fun value =>
    nativeCode modulus.size (suffix operation modulus prime value) allowAllocation)

/-- One native prefix, one actual unconditional reset, and one actual stored-result suffix. -/
def body (operation : InPlaceTarget.Operation) (modulus : Nat) (prime : Nat.Prime modulus)
    (allowAllocation : Bool := true) :
    Circuit (.quantum AlgorithmGate.model .empty) (context modulus.size) (context modulus.size)
      allowAllocation :=
  .seq (nativeCode modulus.size (beforeReset operation modulus prime) allowAllocation)
    (.seq (reset modulus.size allowAllocation) (selectedSuffix operation modulus prime
      allowAllocation))

/-- All three original stages retain exactly the full already allocated caller context. -/
lemma body_visited {allowAllocation : Bool} (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) (path : (body operation modulus prime allowAllocation).Path) :
    (body operation modulus prime allowAllocation).visitedContexts path =
      [context modulus.size, context modulus.size, context modulus.size] := rfl

/-- The complete output lists all live keys and reads the actual measurement cells. -/
def output (width : Nat) : Output (context width) (.fixedVector width (.finite 2)) :=
  Output.all (context width) (.read (resultInput width))

lemma output_listing (width : Nat) : (output width).listing = (context width).keys :=
  Output.all_listing _ _

lemma output_read (width : Nat) (store : Store (context width)) :
    (output width).eval store = store.read (resultInput width) :=
  Output.all_eval _ _ _

variable {runtimeEnvironment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

/-- Actual stored-result selection preserves all joint reference entries in its interpretation. -/
lemma selectedSuffix_reference (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) {Reference : Register} {History : Type} [Fintype History]
    (state : State (context modulus.size) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    ((selectedSuffix operation modulus prime).execute runtimeEnvironment Reference
      state).quantumMarginal =
      (state.applyUnitary (fun entry => UnitaryOperator.prodTensor
        ((runtimeProgram modulus.size
          (suffix operation modulus prime (entry.1.read (resultInput modulus.size)))).matrix
            runtimeEnvironment.quantum)
        (1 : UnitaryOperator Reference))).quantumMarginal :=
  Circuit.selectedUnitary_quantumMarginal (environment := runtimeEnvironment) (resultInput
    modulus.size)
    (fun value => runtimeProgram modulus.size (suffix operation modulus prime value))
    state

end

end QuantumAlg.MeasuredUncompute.InPlaceControlled
