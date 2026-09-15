/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.GateLevelAttempt.Native.Layout
import all QuantumAlg.Algorithms.FiniteCyclicDLP.GateLevelAttempt.Unitary
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Components.QuditShift.Reset.Circuit.Sequence

/-!
# Actual literal finite-cyclic sampling on the original three-register bank

The original non-power-of-two binary expansion determines the
literal preparation. Each sample performs the original opaque group query
and inverse QFTs before measuring the actual exponent wires. Every existing
wire and finite readout cell remains live. Reuse resets and seeds those same
wires with measured classical corrections and charged basis shifts.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical
namespace GateLevelAttempt.Native

open Execution

noncomputable section

universe u

variable {G : Type u} [Group G]
  (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (P : KnownOrderProblem G)

/-- Prepare the original zero-exponent and encoded-identity basis on one actual owned bank. -/
def prepare (ux : UxAccess P) : Circuit base (bankContext base noQuantum P) :=
  .prepare base base.canonicalFreshKey (bankLayout P) base.canonicalFreshKey_fresh
    (allocationDisjoint base noQuantum P) (preparation P ux)

/-- Allocate the bank and all original finite outcome cells exactly once. -/
def allocate (ux : UxAccess P) : Circuit base (context base noQuantum P) :=
  (prepare base noQuantum P ux).seq
    (MeasurementCells.allocate (bankContext base noQuantum P) 2 (sampleWidth P))

/-- Place the original literal preparation-query-QFT circuit on its unchanged physical bank. -/
def member (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P) :
    UnitaryCircuit (context base noQuantum P).register :=
  UnitaryCircuit.reindex (basisEquiv P (nativeFiniteCyclic_context_wires base noQuantum P)).symm
    (GateLevelAttempt.quantumCircuit P B ux)

/-- The actual sample preserves the complete physical footprint of the original circuit. -/
theorem nativeFiniteCyclic_member_physicalIdx
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P) :
    (member base noQuantum P B ux).physical_idx = (context base noQuantum P).physicalIdx :=
  (GateLevelAttempt.quantumCircuit_physical_idx P B ux).trans
    ((nativeFiniteCyclic_physicalIdx P (nativeFiniteCyclic_context_wires base noQuantum P)).trans
      (layout_systemIdx P)).symm

/-- Measure one original exponent position into its actual two-valued cell. -/
def readout (index : Fin (sampleWidth P)) : ZReadout (context base noQuantum P) where
  wire := wireEquiv P (nativeFiniteCyclic_context_wires base noQuantum P)
    ⟨index.val, by
      have bound := index.isLt
      unfold sampleWidth at bound
      unfold totalQubits
      omega⟩
  output := by
    rw [nativeFiniteCyclic_context_qubits P (nativeFiniteCyclic_context_wires base noQuantum P)]
    exact cells base noQuantum P index

/-- The two original exponent-register orders determine the real measurement sequence. -/
def readouts : List (ZReadout (context base noQuantum P)) :=
  List.ofFn (readout base noQuantum P)

/-- Original literal unitary execution is followed by real finite-outcome measurements. -/
def sample (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P) :
    Circuit (context base noQuantum P) (context base noQuantum P) :=
  (Circuit.unitary (member base noQuantum P B ux)
    (nativeFiniteCyclic_member_physicalIdx base noQuantum P B ux)).seq
      (Circuit.measurementSequence (readouts base noQuantum P))

private theorem sampleWidth_pos : 0 < sampleWidth P := by
  have orderPositive := P.order_pos
  have widthPositive : 0 < orderWidth P := by
    apply Nat.clog_pos (by decide)
    unfold FiniteCyclicDLP.oversampledOrder FiniteCyclicDLP.fourierOversamplingFactor
    omega
  unfold sampleWidth
  omega

/-- One existing finite readout cell is reused by each sequential reset and correction. -/
def resetCell (wire : Fin (context base noQuantum P).systemCount) :
    CWriteRef (context base noQuantum P)
      (.finite ((context base noQuantum P).quantumLayout.wire wire).dimension) := by
  rw [nativeFiniteCyclic_context_qubits P (nativeFiniteCyclic_context_wires base noQuantum P)]
  exact cells base noQuantum P ⟨0, sampleWidth_pos P⟩

/-- The original encoded-identity basis is transported to the same live wire positions. -/
def resetLabel (ux : UxAccess P) : (context base noQuantum P).quantumLayout.Basis :=
  (basisEquiv P (nativeFiniteCyclic_context_wires base noQuantum P)).symm
    (tripleIndex 0 0 (ux.encode 1))

/-- Reset, classical correction and basis shift act on every existing original wire. -/
def reset (ux : UxAccess P) : Circuit (context base noQuantum P) (context base noQuantum P) :=
  QuditShift.resetToBasis (resetCell base noQuantum P) (resetLabel base noQuantum P ux)

/-- Later samples reuse exactly the same bank and overwrite the same finite outcome cells. -/
def reusedSample (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P) :
    Circuit (context base noQuantum P) (context base noQuantum P) :=
  (reset base noQuantum P ux).seq (sample base noQuantum P B ux)

/-- A complete single-sample run retains every wire and exposes the actual finite readouts. -/
def run (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P) :
    AlgorithmRun base (context base noQuantum P)
      (.fixedVector (sampleWidth P) (.finite 2)) where
  code := (allocate base noQuantum P ux).seq (sample base noQuantum P B ux)
  output := Output.all (context base noQuantum P) (.read (sampleInput base noQuantum P))

/-- The sample output accounts for every original input and every surviving allocation. -/
theorem nativeFiniteCyclic_output_listing
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P) :
    (run base noQuantum P B ux).output.listing = (context base noQuantum P).keys := rfl

end

end GateLevelAttempt.Native
end QuantumAlg.FiniteCyclicDLP.Canonical
