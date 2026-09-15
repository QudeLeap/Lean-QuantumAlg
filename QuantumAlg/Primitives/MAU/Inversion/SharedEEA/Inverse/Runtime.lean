/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Inverse.Runtime.Frame
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.InPlace.Placement
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Native.Inverse
import all QuantumAlg.Core.Execution.State.Preservation
import all QuantumAlg.Core.Execution.MarginalLaws
import all QuantumAlg.Core.Execution.Reference.Unitary

/-!
# Execute the complete native XOR inverse on its actually prepared frame

One fixed `Circuit.prepare` allocates only the original shared-frame
auxiliary bits beside the two supplied words. The same native forward,
actual XOR copy, and complete dagger then run through `Circuit.unitary`
[LYL+26, sec_EEA/sub_4phase.tex:104-128]. The arbitrary original input and
every prepared field are restored exactly; the target receives the
independent mathematical inverse by XOR on every positive-modulus unit domain.
The original source assumes a prime modulus; this domain extension is proved
in the project. Modulus one uses the full-frame identity after the same preparation.

All quantum-reference coherences evolve under this actual preparation
and complete unitary [dW19, qcnotes.tex:5381,5405]. The fixed preparation
depends only on the modulus. It does not receive an input-dependent label.
Every system remains live after execution and must be listed in the final
Output. This standalone XOR interface is distinct from the original
in-place forward consumed by measured division.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.InverseRuntime

noncomputable section

open Execution InversePreparation

private theorem native_within (modulus : Nat) (nontrivial : 1 < modulus) :
    (NativeInverse.program modulus nontrivial).physical_idx ⊆
      List.range (OutputCopy.encoding modulus.size).width := by
  have forward : (NativeInverse.forwardProgram modulus nontrivial).physical_idx ⊆
      List.range (OutputCopy.encoding modulus.size).width :=
    UnitaryCircuit.prodLeft_physical_idx_subset_range _
      (InPlacePlacement.corrected_within modulus nontrivial)
  exact UnitaryCircuit.seq_physical_idx_subset _ _ forward
    (UnitaryCircuit.seq_physical_idx_subset _ _ (OutputCopy.program_physical_range modulus.size)
      (UnitaryCircuit.dagger_physical_idx_subset _ forward))

/-- Select native arithmetic for a nontrivial modulus and the full-frame identity otherwise. -/
def nativeProgram (modulus : Nat) :
    UnitaryCircuit (Qubits (OutputCopy.encoding modulus.size).width) :=
  if nontrivial : 1 < modulus then NativeInverse.program modulus nontrivial
  else UnitaryCircuit.identity (Qubits (OutputCopy.encoding modulus.size).width)
    (List.range (OutputCopy.encoding modulus.size).width) List.nodup_range

private theorem nativeProgram_within (modulus : Nat) :
    (nativeProgram modulus).physical_idx ⊆
      List.range (OutputCopy.encoding modulus.size).width := by
  by_cases nontrivial : 1 < modulus
  · simpa only [nativeProgram, dif_pos nontrivial] using native_within modulus nontrivial
  · simp only [nativeProgram, dif_neg nontrivial]
    exact List.Subset.refl _

/-- The complete actual inverse on the exact runtime register after auxiliary preparation. -/
def program (modulus : Nat) : UnitaryCircuit (after modulus.size).register :=
  InverseRuntimeFrame.program modulus.size (nativeProgram modulus)

/-- The actual ordered footprint contains every live prepared, input, and target system. -/
theorem program_physical (modulus : Nat) :
    (program modulus).physical_idx = (after modulus.size).physicalIdx :=
  InverseRuntimeFrame.program_physical modulus.size (nativeProgram modulus)
    (nativeProgram_within modulus)

/-- The trivial branch preserves every full-frame basis column, including all auxiliaries. -/
theorem program_trivial_ket (modulus : Nat) (trivial : ¬1 < modulus)
    (basis : (after modulus.size).register.Index) :
    (program modulus).applyNormalized (NormalizedVector.ket basis) =
      NormalizedVector.ket basis := by
  let identity := UnitaryCircuit.identity (Qubits (OutputCopy.encoding modulus.size).width)
    (List.range (OutputCopy.encoding modulus.size).width) List.nodup_range
  have actual := InverseRuntimeFrame.program_apply_ket modulus.size identity
    (InverseAssembly.basisEquiv modulus.size basis) _
    (UnitaryCircuit.applyNormalized_identity _ _ _
      (NormalizedVector.ket (InverseAssembly.basisEquiv modulus.size basis)))
  simpa only [program, nativeProgram, dif_neg trivial, Equiv.symm_apply_apply] using actual

/-- Independently change only the target word by XOR with the mathematical modular inverse. -/
def outputOld (modulus : Nat) (old : (before modulus.size).register.Index)
    (positive : 0 < (inputBasisEquiv modulus.size old).1.val)
    (bounded : (inputBasisEquiv modulus.size old).1.val < modulus) :
    (before modulus.size).register.Index :=
  (inputBasisEquiv modulus.size).symm
    ((inputBasisEquiv modulus.size old).1,
      NativeInverse.output modulus (inputBasisEquiv modulus.size old).1.val positive bounded
        (inputBasisEquiv modulus.size old).2)

/-- The runtime output retains the same actual prepared values and original input word. -/
def outputBasis (modulus : Nat) (old : (before modulus.size).register.Index)
    (positive : 0 < (inputBasisEquiv modulus.size old).1.val)
    (bounded : (inputBasisEquiv modulus.size old).1.val < modulus) :
    (after modulus.size).register.Index :=
  assembly modulus.size ((InputPreparation.preparation modulus).value,
    outputOld modulus old positive bounded)

/-- The actually prepared source label is the exact full native input, with no phase discarded. -/
theorem program_prepared_input (modulus : Nat) (nontrivial : 1 < modulus)
    (old : (before modulus.size).register.Index)
    (coprime : Nat.Coprime (inputBasisEquiv modulus.size old).1.val modulus)
    (positive : 0 < (inputBasisEquiv modulus.size old).1.val)
    (bounded : (inputBasisEquiv modulus.size old).1.val < modulus) :
    (program modulus).applyNormalized
        (NormalizedVector.ket (R := (after modulus.size).register)
          (assembly modulus.size ((InputPreparation.preparation modulus).value, old))) =
      NormalizedVector.ket (R := (after modulus.size).register)
        (outputBasis modulus old positive bounded) := by
  have actual := NativeInverse.program_initial modulus nontrivial
    (inputBasisEquiv modulus.size old).1 (inputBasisEquiv modulus.size old).2
    coprime positive bounded
  have placed := InverseRuntimeFrame.program_apply_ket modulus.size
    (NativeInverse.program modulus nontrivial) _ _ actual
  have initial : (InverseAssembly.basisEquiv modulus.size).symm
      ((OutputCopy.encoding modulus.size).encode
        (InitialFrame.initial modulus (inputBasisEquiv modulus.size old).1,
          (inputBasisEquiv modulus.size old).2)) =
        assembly modulus.size ((InputPreparation.preparation modulus).value, old) := by
    apply (InverseAssembly.basisEquiv modulus.size).injective
    rw [Equiv.apply_symm_apply]
    exact (InverseAssembly.prepared_initial modulus old).symm
  have final : (InverseAssembly.basisEquiv modulus.size).symm
      ((OutputCopy.encoding modulus.size).encode
        (InitialFrame.initial modulus (inputBasisEquiv modulus.size old).1,
          NativeInverse.output modulus (inputBasisEquiv modulus.size old).1.val positive bounded
            (inputBasisEquiv modulus.size old).2)) = outputBasis modulus old positive bounded := by
    apply (InverseAssembly.basisEquiv modulus.size).injective
    rw [Equiv.apply_symm_apply]
    have prepared := InverseAssembly.prepared_initial modulus
      (outputOld modulus old positive bounded)
    simpa only [outputBasis, outputOld, Equiv.apply_symm_apply] using prepared.symm
  rw [initial, final] at placed
  simpa only [program, nativeProgram, dif_pos nontrivial] using placed

/-- The native arithmetic is one actual unitary instruction on the complete live context. -/
def body (modulus : Nat) :
    Circuit (after modulus.size) (after modulus.size) :=
  .unitary (program modulus) (program_physical modulus)

/-- Execute fixed auxiliary preparation and the complete native compute-copy-inverse program. -/
def code (modulus : Nat) :
    Circuit (before modulus.size) (after modulus.size) :=
  .seq (InversePreparation.circuit modulus) (body modulus)

/-- No original native occurrence is lost through actual runtime placement. -/
theorem program_eventTrace (modulus : Nat) :
    (program modulus).eventTrace = (nativeProgram modulus).eventTrace :=
  InverseRuntimeFrame.program_eventTrace modulus.size (nativeProgram modulus)

private theorem prepared_trace {ctx : RuntimeCtx .quantum} {count : Nat}
    (key : StorageKey) (layout : QuantumLayout count) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (preparation : BasisPreparation layout)
    (unitary : UnitaryCircuit (ctx.addOwnedLayout key layout fresh disjoint).register)
    (placement : unitary.physical_idx =
      (ctx.addOwnedLayout key layout fresh disjoint).physicalIdx)
    (events : List (Resource.Event .quantum)) (same : unitary.eventTrace = events)
    (path : ((Circuit.prepare ctx key layout fresh disjoint preparation).seq
      (Circuit.unitary unitary placement)).Path) :
    ((Circuit.prepare ctx key layout fresh disjoint preparation).seq
      (Circuit.unitary unitary placement)).eventTrace path = preparation.event :: events := by
  change [preparation.event] ++ unitary.eventTrace = preparation.event :: events
  exact congrArg (fun trace : List (Resource.Event .quantum) => preparation.event :: trace) same

/-- The trace contains actual preparation and every native forward, copy and inverse gate. -/
theorem code_eventTrace (modulus : Nat)
    (path : (code modulus).Path) :
    (code modulus).eventTrace path = (InputPreparation.preparation modulus).event ::
      (nativeProgram modulus).eventTrace :=
  prepared_trace auxiliaryKey (InputPreparation.auxiliaryLayout modulus.size)
    (auxiliary_fresh modulus.size) (auxiliary_disjoint modulus.size)
    (InputPreparation.preparation modulus) (program modulus) (program_physical modulus)
    (nativeProgram modulus).eventTrace (program_eventTrace modulus) path

variable {Reference : Register} {H : Type} [Fintype H]

/-- Actual execution is the prepared joint matrix conjugated by this same inverse program. -/
theorem code_quantumMarginal (modulus : Nat)
    (state : State (before modulus.size) Reference H) :
    ((code modulus).execute Reference state).quantumMarginal =
      DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor (program modulus).matrix (1 : UnitaryOperator Reference))
        (((InversePreparation.circuit modulus).execute Reference state).quantumMarginal) := by
  rw [code, Circuit.execute_seq, State.mapHistory_quantumMarginal, body,
    Circuit.execute_unitary]
  simp only [State.unitary, ExecutionState.mapClassical_quantumMarginal]
  exact ExecutionState.fixedUnitary_quantumMarginal _ _

/-- Complete inversion preserves every external-reference matrix entry, including coherences. -/
theorem code_reference_entry (modulus : Nat)
    (state : State (before modulus.size) Reference H) (left right : Reference.Index) :
    (∑ basis : (after modulus.size).register.Index,
      ((code modulus).execute Reference state).quantumMarginal.matrix
        (basis, left) (basis, right)) =
      ∑ basis : (before modulus.size).register.Index,
        state.quantumMarginal.matrix (basis, left) (basis, right) := by
  rw [code_quantumMarginal]
  exact (DensityOperator.localUnitary_reference_entry (program modulus).matrix
    (((InversePreparation.circuit modulus).execute Reference state).quantumMarginal)
      left right).trans
        (Circuit.prepare_reference_entry state auxiliaryKey
          (InputPreparation.auxiliaryLayout modulus.size) (auxiliary_fresh modulus.size)
          (auxiliary_disjoint modulus.size) (InputPreparation.preparation modulus) left right)

end

end QuantumAlg.MAU.Inversion.SharedEEA.InverseRuntime
