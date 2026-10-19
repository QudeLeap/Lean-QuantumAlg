/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Pattern
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Pattern.Resources
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Layout
import all QuantumAlg.Components.Encoded.BitGates.BinaryLabelEncoding
import all QuantumAlg.Components.Encoded.BitGates.GateSpec
import all QuantumAlg.Components.Encoded.Circuit
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum

/-!
# Native zero-pattern flip borrowing an existing signal bit

The phase wire precedes m block ancillas and n signal qubits. When n is
positive, the first existing signal bit supplies arbitrary work for the
balanced multi-control implementation. Its value and all correlations are
restored; no additional physical system is allocated. The empty signal space
is a separate scalar boundary case.
-/

namespace QuantumAlg.ZeroProjector.SourceWork
open EncodedBit EncodedBit.Word
noncomputable section

/-- Original big-endian labels of the phase, block ancillas and complete signal word. -/
def encoding (m n : Nat) := BinaryLabelEncoding.finIdentity (1 + (m + n))

/-- The block ancillas occupy their original positions immediately after the phase wire. -/
def sourceBit (m n : Nat) (index : Fin m) : EncodedBit (encoding m n) :=
  BinaryLabelEncoding.finIdentityBit (1 + (m + n)) ⟨1 + index.val, by omega⟩

/-- Only the original leading phase wire is the predicate-controlled output. -/
def outputBit (m n : Nat) : EncodedBit (encoding m n) :=
  BinaryLabelEncoding.finIdentityBit (1 + (m + n)) 0

/-- The first already resident signal bit is borrowed with no initialization assumption. -/
def workBit (m n : Nat) (positive : 0 < n) : EncodedBit (encoding m n) :=
  BinaryLabelEncoding.finIdentityBit (1 + (m + n)) ⟨1 + m, by omega⟩

/-- A concrete one-dirty layout with all controls and work in the original interface. -/
def layout (m n : Nat) (positive : 0 < n) :
    OneDirtyLayout (encoding := encoding m n) m where
  source := ⟨sourceBit m n⟩
  output := outputBit m n
  work := workBit m n positive
  source_injective := by
    intro left right same
    have values := congrArg (fun wire : Fin (encoding m n).width => wire.val) same
    change 1 + left.val = 1 + right.val at values
    exact Fin.ext (by omega)
  source_output_ne := by
    intro index same
    have values := congrArg (fun wire : Fin (encoding m n).width => wire.val) same
    change 1 + index.val = 0 at values
    omega
  source_work_ne := by
    intro index same
    have values := congrArg (fun wire : Fin (encoding m n).width => wire.val) same
    change 1 + index.val = 1 + m at values
    omega
  work_output_ne := by
    intro same
    have values := congrArg (fun wire : Fin (encoding m n).width => wire.val) same
    change 1 + m = 0 at values
    omega

/-- The complete actual native zero-pattern program, placed on every original physical wire. -/
def program (m n : Nat) (positive : 0 < n)
    (physical : QubitLayout (1 + (m + n))) (oracles : OracleModel) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  GateSpec.programList physical oracles ((layout m n positive).patternGates fun _ => false)

/-- The entire encoded label changes only by the declared zero-controlled phase-wire flip. -/
lemma program_realizes (m n : Nat) (positive : 0 < n)
    (physical : QubitLayout (1 + (m + n))) (oracles : OracleModel)
      (environment : oracles.Interpretation) :
    UnitaryCircuit.Realizes (encoding m n) (program m n positive physical oracles) environment
      (fun state => if ∀ index, (sourceBit m n index).get state = false
        then (outputBit m n).flip state else state) :=
  (layout m n positive).patternGates_realizes physical oracles (fun _ => false) environment

/-- Both zero masks and the borrowed conjunction contribute to the actual sequential depth. -/
lemma program_depth (m n : Nat) (positive : 0 < n)
    (physical : QubitLayout (1 + (m + n))) (oracles : OracleModel) :
    (program m n positive physical oracles).evaluatedEventDepth (fun _ => 1) =
      2 * m + OneDirtyLayout.gateCount m :=
  (layout m n positive).zeroPattern_program_depth physical oracles

end
end QuantumAlg.ZeroProjector.SourceWork
