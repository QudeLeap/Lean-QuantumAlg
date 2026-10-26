/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Boundary.Program
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Clip.Active
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Difference.Program

/-!
# Actual public-width clipping preparation on the existing complete pool

The public narrow case uses the existing high address as the active latch
and subtracts only the low metadata width. The wide case uses original
Ctrl and subtracts both complete carry words. Both execute on every input
label; no runtime value selects or constructs their program.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthClip

noncomputable section

open EncodedBit LengthCoordinates NumberTheory.SharedEEA

/-- Only the public physical width decides whether a spare high address position exists. -/
def narrow (width : Nat) : Prop := width + 3 < 2 ^ width.size

instance (width : Nat) : Decidable (narrow width) :=
  inferInstanceAs (Decidable (width + 3 < 2 ^ width.size))

/-- Both original low words or both complete carry words participate, as a static choice. -/
def subtractionWidth (width : Nat) : Nat :=
  if narrow width then width.size else ScanMetadata.addressWidth width

/-- Every selected arithmetic operand is a genuine existing pool subword. -/
lemma subtractionWidth_fits (width : Nat) :
    subtractionWidth width ≤ ScanMetadata.addressWidth width := by
  unfold subtractionWidth ScanMetadata.addressWidth
  split <;> omega

/-- Only the static narrow case emits the real negative-control activation word. -/
def activationGates (width : Nat) : List (GateSpec (encoding width)) :=
  if narrow width then activeGates width else []

/-- Every label executes the same literal static activation list. -/
def activationProgram (width : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (activationGates width)

/-- Exact all-label action of the actual activation instructions. -/
def activationStep (width : Nat) : Data width → Data width :=
  GateSpec.stepList (activationGates width)

/-- No clean prefix, metadata range or trajectory premise is hidden in activation semantics. -/
lemma activationProgram_realizes (width : Nat) (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (activationProgram width) environment
      (activationStep width) :=
  GateSpec.realizesList (QubitLayout.canonical _) .empty _ environment

/-- Actual public loading, complete other-key subtraction, activation and borrow arithmetic. -/
def prepareProgram (width : Nat) (field : Field) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  (LengthBoundary.prepareProgram width field).seq
    ((activationProgram width).seq
      (LengthDifference.program width (subtractionWidth width) (subtractionWidth_fits width)))

/-- Complete finite action in the exact chronological order of that real native program. -/
def prepareStep (width : Nat) (field : Field) (state : Data width) : Data width :=
  LengthDifference.step width (subtractionWidth width) (subtractionWidth_fits width)
    (activationStep width (LengthBoundary.prepareStep width field state))

/-- The same native sequence acts coherently on every original label and arbitrary reference. -/
lemma prepareProgram_realizes (width : Nat) (field : Field)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (prepareProgram width field) environment
      (prepareStep width field) := by
  have first := LengthBoundary.prepareProgram_realizes width field environment
  have second := activationProgram_realizes width environment
  have third := LengthDifference.program_realizes width (subtractionWidth width)
    (subtractionWidth_fits width) environment
  have tail := UnitaryCircuit.Realizes.seq second third
  have complete := UnitaryCircuit.Realizes.seq first tail
  exact complete

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthClip
