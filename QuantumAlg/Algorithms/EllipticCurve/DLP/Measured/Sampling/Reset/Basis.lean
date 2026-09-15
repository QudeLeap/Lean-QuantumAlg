/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.PublicInput.Framing
import all
  QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Encoding.Allocation.Montgomery

/-!
# Complete original sampling basis and existing reset result storage

The prescribed label includes the zero selector, every original fixed EEA
auxiliary, both original Montgomery coordinates, and both zero exponents.
The existing measurement-cell and public-input coordinate maps place this
whole label on the actual terminal context. Its first original numerator
result cell exists because the field modulus is prime, even at exponent
width zero. Reusing this cell leaves its actual measured value in storage;
no initial or final classical-zero assertion is made here.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ContextUnion ScalarMultiplication.MeasuredPlacement
open MeasuredUncompute MAU.Inversion.SharedEEA

private def QubitContext (ctx : RuntimeCtx .quantum) : Prop :=
  ∀ wire ∈ ctx.quantumWires, wire.dimension = 2

private theorem qubitLayout_member {width : Nat} (layout : QubitLayout width)
    (wire : QuantumWire) (present : wire ∈ layout.toQuantumLayout.wires) :
    wire.dimension = 2 := by
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
  rfl

private theorem owned_qubits (ctx : RuntimeCtx .quantum) (key : StorageKey)
    {count : Nat} (layout : QuantumLayout count) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (original : QubitContext ctx)
    (added : ∀ wire ∈ layout.wires, wire.dimension = 2) :
    QubitContext (ctx.addOwnedLayout key layout fresh disjoint) := by
  intro wire present
  rw [RuntimeCtx.runtimeCtx_quantumWires_addOwnedLayout] at present
  exact (List.mem_append.mp present).elim (added wire) (original wire)

private theorem cells_qubits (ctx : RuntimeCtx .quantum) (dimension : ℕ+) (count : Nat)
    (original : QubitContext ctx) :
    QubitContext (MeasurementCells.context ctx dimension count) := by
  intro wire present
  rw [MeasurementCells.context_quantumWires] at present
  exact original wire present

private theorem union_qubits (left right : RuntimeCtx .quantum)
    (separate : RuntimeCtx.StorageDisjoint left right)
    (first : QubitContext left) (second : QubitContext right) :
    QubitContext (left.disjointUnion right separate) := by
  intro wire present
  rw [RuntimeCtx.quantumWires_disjointUnion] at present
  exact (List.mem_append.mp present).elim (first wire) (second wire)

private theorem indexed_qubits (width : Nat) (indices : List Nat) (distinct : indices.Nodup) :
    QubitContext (indexedContext width indices distinct) := by
  intro wire present
  change wire ∈ (indices.map (indexedEntry width)).flatMap RuntimeEntry.quantumWires at present
  rw [indexed_wires] at present
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp present
  rfl

private theorem after_qubits (width count : Nat) : QubitContext (Allocation.after width count) := by
  have supplied : QubitContext (InversePreparation.before width) :=
    owned_qubits RuntimeCtx.empty ⟨0⟩ (InversePreparation.inputLayout width) (by decide)
      (by simp only [RuntimeCtx.runtimeCtx_empty_physicalIdx, List.disjoint_nil_right])
      (by intro wire present; exact False.elim (List.not_mem_nil present))
      (qubitLayout_member (InversePreparation.inputQubitLayout width))
  have arithmetic : QubitContext (InversePreparation.after width) :=
    owned_qubits (InversePreparation.before width) InversePreparation.auxiliaryKey
      (InputPreparation.auxiliaryLayout width) (InversePreparation.auxiliary_fresh width)
      (InversePreparation.auxiliary_disjoint width) supplied
      (qubitLayout_member (InputPreparation.auxiliaryQubitLayout width))
  have numerator : QubitContext (NumeratorMeasurement.context width) :=
    cells_qubits (InversePreparation.after width) 2 width arithmetic
  have original : QubitContext (Allocation.withCells width count) :=
    union_qubits _ _ (Allocation.complete_disjoint width count) numerator
      (indexed_qubits width (List.range count) List.nodup_range)
  exact owned_qubits (Allocation.withCells width count) (indexedKey width count)
    (indexedLayout width count) (Allocation.selector_fresh width count)
    (Allocation.selector_disjoint width count)
    original (by intro wire present; obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present; rfl)

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) (exponentWidth : Nat)

private theorem terminal_qubits : QubitContext (PublicInput.terminal E exponentWidth) :=
  union_qubits _ _ (PublicInput.terminal_disjoint E exponentWidth)
    (cells_qubits (Allocation.after p.size (2 * exponentWidth)) 2 (2 * exponentWidth)
      (after_qubits p.size (2 * exponentWidth)))
    (by intro wire present; rw [PublicInput.frame_quantumWires] at present; cases present)

/-- Every actual terminal system, including the complete auxiliary frame, is dimension two. -/
theorem samplingReset_qubits (wire : Fin (PublicInput.terminal E exponentWidth).systemCount) :
    ((PublicInput.terminal E exponentWidth).quantumLayout.wire wire).dimension = 2 := by
  apply terminal_qubits E exponentWidth
  rw [← RuntimeCtx.quantumLayout_wires, QuantumLayout.wires]
  exact List.mem_ofFn.mpr ⟨wire, rfl⟩

variable [Fact p.Prime]

/-- Reuse the first original numerator result cell without allocating any reset storage. -/
def samplingResetCell : CWriteRef (PublicInput.terminal E exponentWidth) (.finite 2) :=
  writeLeft (PublicInput.terminal_disjoint E exponentWidth)
    (MeasurementCells.liftWrite 2
      (ContextPermutation.writable (Allocation.body_entries p.size (2 * exponentWidth))
        (writeLeft (indexedContext_disjoint p.size
          (List.range (2 * exponentWidth + 1)) List.nodup_range)
          (NumeratorMeasurement.cell p.size
            ⟨0, Nat.size_pos.mpr (Nat.Prime.pos (Fact.out : p.Prime))⟩)))
      (2 * exponentWidth))

/-- Every reset writes the same existing cell after checking its actual physical dimension. -/
def samplingResetCells (wire : Fin (PublicInput.terminal E exponentWidth).systemCount) :
    CWriteRef (PublicInput.terminal E exponentWidth)
      (.finite ((PublicInput.terminal E exponentWidth).quantumLayout.wire wire).dimension) :=
  (samplingReset_qubits E exponentWidth wire).symm ▸ samplingResetCell E exponentWidth

/-- All original fixed auxiliary bits and the original Montgomery seed occupy their actual wires. -/
def samplingResetLabel (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (seed : AffinePoint E) :
    (PublicInput.terminal E exponentWidth).register.Index :=
  (unionBasisEquiv (exponentMeasurementContext p exponentWidth)
    (PublicInput.frame E exponentWidth) (PublicInput.terminal_disjoint E exponentWidth)).symm
    (MeasurementCells.basisEquiv (Allocation.after p.size (2 * exponentWidth)) 2
      (2 * exponentWidth)
      (Allocation.initializedAssembly p (2 * exponentWidth)
        ((BasisPreparation.zero (indexedLayout p.size (2 * exponentWidth))).value,
          (InPlacePreparation.preparation p).value,
          Encoding.pairedMontgomeryInput fieldTail exponentWidth sameWidth fits seed (0, 0))),
      (PublicInput.frame E exponentWidth).quantumLayout.zeroLabel)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
