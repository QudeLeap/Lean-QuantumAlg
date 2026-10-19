/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Arithmetic
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.ParameterLayout
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Preparation.Empty
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Components.Encoded.BitGates.Word.BasisLoad
import all QuantumAlg.Components.Classical.Model.BitWord

/-!
# One owned control/arithmetic bank and every actual result cell

The enclosing factoring program allocates
this bank around its classical frame, so no external caller supplies a clean
quantum register. Exactly one control, a power word, and one auxiliary word
remain resident throughout both exponent streams. Distinct output cells are
retained once and are never reused for another output bit within a member.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling

noncomputable section

open Execution

abbrev model : ExecutionModel := .quantum AlgorithmGate.model .empty BitWord.model

def resultBits (m ell : Nat) : Nat := (ell + m) + ell

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])

include noQuantum in
private lemma allocationDisjoint (width : Nat) :
    List.Disjoint (Arithmetic.layout width).toQuantum.identities base.physicalIdx := by
  simp only [RuntimeCtx.physicalIdx, noQuantum, List.map_nil]
  exact List.disjoint_nil_right _

/-- This is the sole actual quantum allocation for the member and its later reuse rounds. -/
def bankContext (width : Nat) : RuntimeCtx .quantum :=
  base.addOwnedLayout base.canonicalFreshKey (Arithmetic.layout width).toQuantum
    base.runtimeCtx_canonicalFreshKey_fresh (allocationDisjoint base noQuantum width)

/-- All outcome cells are real retained binary storage; the quantum bank is unchanged. -/
def context (m ell width : Nat) : RuntimeCtx .quantum :=
  MeasurementCells.context (bankContext base noQuantum width) 2 (resultBits m ell)

lemma context_wires (m ell width : Nat) :
    (Arithmetic.layout width).toQuantum.wires =
      (context base noQuantum m ell width).quantumLayout.wires := by
  rw [RuntimeCtx.quantumLayout_wires]
  unfold context
  rw [MeasurementCells.context_quantumWires]
  change (Arithmetic.layout width).toQuantum.wires =
    (Arithmetic.layout width).toQuantum.wires ++ base.quantumWires
  rw [noQuantum, List.append_nil]

/-- The actual resident carrier contains no exponent banks, at any source widths. -/
lemma systemCount_eq (m ell width : Nat) :
    (context base noQuantum m ell width).systemCount = 1 + 2 * width := by
  have same := congrArg List.length (context_wires base noQuantum m ell width)
  simp only [QuantumLayout.wires_length] at same
  exact same.symm.trans (Arithmetic.width_eq width)

/-- The fixed RSA arithmetic width gives the actual 4097-qubit carrier. -/
lemma rsa2048_systemCount (m ell : Nat) :
    (context base noQuantum m ell 2048).systemCount = 4097 := by
  rw [systemCount_eq]

/-- The sole control is the first physical wire of the one-control native stage. -/
def control (m ell width : Nat) : Fin (context base noQuantum m ell width).systemCount :=
  positionsOfEqualWires (Arithmetic.layout width).toQuantum
    (context base noQuantum m ell width).quantumLayout
    (context_wires base noQuantum m ell width) ⟨0, by
      change 0 < 1 + (width + width)
      omega⟩

lemma control_qubit (m ell width : Nat) :
    ((context base noQuantum m ell width).quantumLayout.wire
      (control base noQuantum m ell width)).dimension = 2 := by
  have same := wireAtCorrespondingPosition (Arithmetic.layout width).toQuantum
    (context base noQuantum m ell width).quantumLayout
    (context_wires base noQuantum m ell width) ⟨0, by
      change 0 < 1 + (width + width)
      omega⟩
  exact (congrArg QuantumWire.dimension same).trans (by rfl)

def cells (m ell width : Nat) (index : Fin (resultBits m ell)) :
    CWriteRef (context base noQuantum m ell width) (.finite 2) :=
  MeasurementCells.reference (bankContext base noQuantum width) 2 (resultBits m ell) index

/-- Distinct positions have distinct bottom-level storage keys, irrespective of role records. -/
lemma cells_distinct (m ell width : Nat) :
    Function.Injective (fun index => (cells base noQuantum m ell width index).key) :=
  MeasurementCells.reference_key_injective (bankContext base noQuantum width)
    2 (resultBits m ell)

def firstCell (m ell width : Nat) (position : Fin (ell + m)) :
    CWriteRef (context base noQuantum m ell width) (.finite 2) :=
  cells base noQuantum m ell width ⟨position.val, by
    have bounded := position.isLt
    unfold resultBits
    omega⟩

def secondCell (m ell width : Nat) (position : Fin ell) :
    CWriteRef (context base noQuantum m ell width) (.finite 2) :=
  cells base noQuantum m ell width ⟨ell + m + position.val, by
    have bounded := position.isLt
    unfold resultBits
    omega⟩

/-- The second exponent cannot overwrite any retained outcome from the first exponent. -/
lemma first_second_distinct (m ell width : Nat)
    (first : Fin (ell + m)) (second : Fin ell) :
    (firstCell base noQuantum m ell width first).key ≠
      (secondCell base noQuantum m ell width second).key := by
  intro same
  have indices := cells_distinct base noQuantum m ell width same
  have values := congrArg Fin.val indices
  change first.val = ell + m + second.val at values
  have bounded := first.isLt
  omega

/-- Chronological stored outcomes; no physical bit/word computation occurs in this read. -/
def resultRead (m ell width : Nat) :
    OutputRead (context base noQuantum m ell width) (.fixedVector (resultBits m ell) (.finite 2)) :=
  .read (.fixedVector fun index => .storage (cells base noQuantum m ell width index).toCStorageRef)

/-- A future charged pack instruction can read each exponent in frequency-MSB order.
This only selects existing cells; it does not replace that instruction by free packing. -/
def frequencyInput (m ell width : Nat) :
    CInputRef (context base noQuantum m ell width) (.fixedVector (resultBits m ell) (.finite 2)) :=
  .fixedVector fun index => Fin.addCases
    (fun position => .storage (firstCell base noQuantum m ell width position.rev).toCStorageRef)
    (fun position => .storage (secondCell base noQuantum m ell width position.rev).toCStorageRef)
    index

/-- A total seed label keeps the original invalid-parameter extension inside the program. -/
def seedLabel (width N : Nat) : Fin (2 ^ (Arithmetic.encoding width).width) :=
  (Arithmetic.encoding width).encode (0, cleanWorkspace width N 1)

/-- Literal native X gates load the internally allocated zero bank. -/
def sourceLoad (width N : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty (Arithmetic.layout width).toQuantum :=
  EncodedBit.Word.BasisLoad.program (Arithmetic.layout width) .empty (seedLabel width N)

lemma sourceLoad_zero {environment : OracleModel.empty.Interpretation}
    (width N : Nat) :
    (sourceLoad width N).applyNormalized environment
        (NormalizedVector.ket ((Arithmetic.layout width).basisEquiv.symm 0)) =
      NormalizedVector.ket ((Arithmetic.layout width).basisEquiv.symm (seedLabel width N)) :=
  EncodedBit.Word.BasisLoad.basisLoad_apply_zero
    (Arithmetic.layout width) .empty (seedLabel width N)

def load (m ell width N : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (context base noQuantum m ell width).quantumLayout :=
  unitaryOfEqualWires (Arithmetic.layout width).toQuantum
    (context base noQuantum m ell width).quantumLayout
    (context_wires base noQuantum m ell width) (sourceLoad width N)

/-- Actual allocation precedes actual loading; no clean-state premise is taken from a caller. -/
def prepare (m ell width N : Nat) :
    Circuit model base (context base noQuantum m ell width) :=
  (Circuit.prepareZero base base.canonicalFreshKey (Arithmetic.layout width).toQuantum
    base.runtimeCtx_canonicalFreshKey_fresh (allocationDisjoint base noQuantum width)).seq
      ((MeasurementCells.allocate (model := model)
        (bankContext base noQuantum width) 2 (resultBits m ell)).seq
          (.unitary (load base noQuantum m ell width N)))

lemma context_resident (m ell width : Nat) :
    (context base noQuantum m ell width).residentSpace =
      resultBits m ell • SpacePool.ofShape (.finite 2) +
        (SpacePool.ofQuantumLayout (Arithmetic.layout width).toQuantum + base.residentSpace) := by
  rw [context, MeasurementCells.context_residentSpace]
  rfl

lemma context_auxiliary (m ell width : Nat) :
    (context base noQuantum m ell width).auxiliarySpace =
      resultBits m ell • SpacePool.ofShape (.finite 2) +
        (SpacePool.ofQuantumLayout (Arithmetic.layout width).toQuantum + base.auxiliarySpace) := by
  rw [context, MeasurementCells.context_auxiliarySpace]
  rfl

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling
