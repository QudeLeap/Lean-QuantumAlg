/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.GateLevelAttempt.Native
import all QuantumAlg.Algorithms.FiniteCyclicDLP.GateLevelAttempt.Native.Batch.Layout
import all QuantumAlg.Core.Execution.Classical.Composition.Range
import all QuantumAlg.Core.Execution.FiniteReadout

/-!
# Actual finite-cyclic samples retained on one original bank

The original three-register bank is prepared once. Each sample measures the
original exponent wires directly into its own retained finite cells. Later
samples first reset that same bank, using their own first result cell as
temporary storage; previously measured samples are never overwritten. Every
live entry is retained in the final output, including when the count is zero.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical.GateLevelAttempt.Native.Batch

open Execution

noncomputable section

universe u

variable {G : Type u} [Group G]
  (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (P : KnownOrderProblem G) (count : Nat)

/-- Allocate the original bank once and retain exactly all requested raw finite readouts. -/
def allocate (ux : UxAccess P) : Circuit base (context base noQuantum P count) :=
  (Native.prepare base noQuantum P ux).seq
    (MeasurementCells.allocate (bankContext base noQuantum P) 2 (count * sampleWidth P))

/-- The same literal unitary acts on the unchanged physical bank beneath all sample cells. -/
def member (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P) :
    UnitaryCircuit (context base noQuantum P count).register :=
  UnitaryCircuit.reindex
    (basisEquiv P (nativeFiniteCyclicBatch_context_wires base noQuantum P count)).symm
    (GateLevelAttempt.quantumCircuit P B ux)

/-- The actual member retains the exact physical footprint of the original unitary. -/
theorem nativeFiniteCyclicBatch_member_physicalIdx
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P) :
    (member base noQuantum P count B ux).physical_idx =
      (context base noQuantum P count).physicalIdx :=
  (GateLevelAttempt.quantumCircuit_physical_idx P B ux).trans
    ((nativeFiniteCyclic_physicalIdx P
      (nativeFiniteCyclicBatch_context_wires base noQuantum P count)).trans
        (layout_systemIdx P)).symm

/-- Measure the original exponent position directly into the selected sample's actual cell. -/
def readout (slot : Fin count) (index : Fin (sampleWidth P)) :
    ZReadout (context base noQuantum P count) where
  wire := wireEquiv P (nativeFiniteCyclicBatch_context_wires base noQuantum P count)
    ⟨index.val, by
      have bound := index.isLt
      unfold sampleWidth at bound
      unfold totalQubits
      omega⟩
  output := by
    rw [nativeFiniteCyclic_context_qubits P
      (nativeFiniteCyclicBatch_context_wires base noQuantum P count)]
    exact cells base noQuantum P count slot index

/-- Measurement destinations keep the exact allocated sample-position key. -/
theorem nativeFiniteCyclicBatch_readout_key (slot : Fin count) (index : Fin (sampleWidth P)) :
    (readout base noQuantum P count slot index).output.key =
      (cells base noQuantum P count slot index).key :=
  FiniteReadout.transported_key
    (nativeFiniteCyclic_context_qubits P
      (nativeFiniteCyclicBatch_context_wires base noQuantum P count) _)
    (cells base noQuantum P count slot index)

/-- Sample slots change only the destination cells, leaving the measured physical position fixed. -/
theorem nativeFiniteCyclicBatch_readout_wire (left right : Fin count)
    (index : Fin (sampleWidth P)) :
    (readout base noQuantum P count left index).wire =
      (readout base noQuantum P count right index).wire := rfl

/-- Every sample measures both original exponent registers in their original consecutive order. -/
def readouts (slot : Fin count) : List (ZReadout (context base noQuantum P count)) :=
  List.ofFn (readout base noQuantum P count slot)

/-- Every measured exponent position has a distinct actual destination within its sample. -/
theorem nativeFiniteCyclicBatch_readouts_nodup (slot : Fin count) :
    ((readouts base noQuantum P count slot).map fun item => item.output.key).Nodup := by
  rw [readouts, List.map_ofFn]
  apply List.nodup_ofFn.mpr
  intro left right same
  have keys := (nativeFiniteCyclicBatch_readout_key base noQuantum P count slot left).symm.trans
    (same.trans (nativeFiniteCyclicBatch_readout_key base noQuantum P count slot right))
  exact congrArg Prod.snd
    (nativeFiniteCyclicBatch_cells_key_injective base noQuantum P count
      (a₁ := (slot, left)) (a₂ := (slot, right)) keys)

/-- One sample executes the original literal member and its real finite measurement sequence. -/
def sample (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P)
    (slot : Fin count) :
    Circuit (context base noQuantum P count) (context base noQuantum P count) :=
  (Circuit.unitary (member base noQuantum P count B ux)
    (nativeFiniteCyclicBatch_member_physicalIdx base noQuantum P count B ux)).seq
      (Circuit.measurementSequence (readouts base noQuantum P count slot))

/-- A later sample temporarily uses only its own first finite result cell during full-bank reset. -/
def resetCell (slot : Fin count) (wire : Fin (context base noQuantum P count).systemCount) :
    CWriteRef (context base noQuantum P count)
      (.finite ((context base noQuantum P count).quantumLayout.wire wire).dimension) := by
  rw [nativeFiniteCyclic_context_qubits P
    (nativeFiniteCyclicBatch_context_wires base noQuantum P count)]
  exact cells base noQuantum P count slot ⟨0, sampleWidth_pos P⟩

/-- The reset scratch destination belongs to the current sample alone. -/
theorem nativeFiniteCyclicBatch_resetCell_key (slot : Fin count)
    (wire : Fin (context base noQuantum P count).systemCount) :
    (resetCell base noQuantum P count slot wire).key =
      (cells base noQuantum P count slot ⟨0, sampleWidth_pos P⟩).key :=
  FiniteReadout.transported_key
    (nativeFiniteCyclic_context_qubits P
      (nativeFiniteCyclicBatch_context_wires base noQuantum P count) wire)
    (cells base noQuantum P count slot ⟨0, sampleWidth_pos P⟩)

/-- The reset basis uses the original zero exponents and encoded group identity. -/
def resetLabel (ux : UxAccess P) : (context base noQuantum P count).quantumLayout.Basis :=
  (basisEquiv P (nativeFiniteCyclicBatch_context_wires base noQuantum P count)).symm
    (tripleIndex 0 0 (ux.encode 1))

/-- Reset and charged corrections reseed the bank to the original encoded identity. -/
def reset (ux : UxAccess P) (slot : Fin count) :
    Circuit (context base noQuantum P count) (context base noQuantum P count) :=
  QuditShift.resetToBasis (resetCell base noQuantum P count slot)
    (resetLabel base noQuantum P count ux)

/-- Each later sample pays for reset before writing its own previously unused result cells. -/
def reusedSample (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P)
    (slot : Fin count) :
    Circuit (context base noQuantum P count) (context base noQuantum P count) :=
  (reset base noQuantum P count ux slot).seq (sample base noQuantum P count B ux slot)

/-- The first slot uses the initial preparation; every later slot includes paid reset. -/
def sampleBatch (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P) :
    (count : Nat) → Circuit (context base noQuantum P count) (context base noQuantum P count)
  | 0 => .id (context base noQuantum P 0)
  | count + 1 =>
      .seq (sample base noQuantum P (count + 1) B ux 0)
        (Circuit.forRange count fun index =>
          reusedSample base noQuantum P (count + 1) B ux index.succ)

/-- All sample cells and one bank are allocated before the original ordered sample sequence. -/
def code (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P) :
    Circuit base (context base noQuantum P count) :=
  (allocate base noQuantum P count ux).seq (sampleBatch base noQuantum P B ux count)

/-- Observe the raw samples structurally, retaining every caller entry, cell and wire. -/
def run (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P) :
    AlgorithmRun base (context base noQuantum P count)
      (.fixedVector count (.fixedVector (sampleWidth P) (.finite 2))) where
  code := code base noQuantum P count B ux
  output := Output.all (context base noQuantum P count)
    (.read (samplesInput base noQuantum P count))

/-- The complete output lists all live entries even for the actual zero-sample program. -/
theorem nativeFiniteCyclicBatch_output_listing
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P) :
    (run base noQuantum P count B ux).output.listing =
      (context base noQuantum P count).keys := rfl

end

end QuantumAlg.FiniteCyclicDLP.Canonical.GateLevelAttempt.Native.Batch
