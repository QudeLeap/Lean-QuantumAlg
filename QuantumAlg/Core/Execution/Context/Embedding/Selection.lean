/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Context.Embedding
public import QuantumAlg.Core.Base.Layout.Quantum.Selection
import all QuantumAlg.Core.Execution.Context.Embedding
import all QuantumAlg.Core.Execution.Context.Permutation.Layout
import all QuantumAlg.Core.Execution.Context.Relabeling.Layout
import all QuantumAlg.Core.Execution.Context.Union.Basis
import Mathlib.Data.Finset.Image

/-!
# Actual output wire selections through physical placement

The local and complement positions partition the actual caller layout. A
selected subsystem follows the same injective physical placement as execution,
retaining every wire dimension and finite basis value. No Hilbert-space
cardinality bijection replaces this wire correspondence
[dW19, qcnotes.tex:389,6827].
-/

namespace QuantumAlg.ContextEmbedding

noncomputable section

open Execution

variable {kind : ProblemKind} {localCtx caller : RuntimeCtx kind}
  (placement : ContextEmbedding localCtx caller)

/-- Every caller wire comes from exactly one original local or complement position. -/
public def positions : Fin localCtx.systemCount ⊕ Fin placement.frame.systemCount ≃
    Fin caller.systemCount :=
  ((ContextRelabeling.positions localCtx placement.keys placement.physical).sumCongr
      (Equiv.refl (Fin placement.frame.systemCount))).trans
    ((ContextUnion.unionPositionEquiv (localCtx.relabel placement.keys placement.physical)
      placement.frame placement.separate).trans (ContextPermutation.positions placement.covers))

/-- Inject each local wire into its prescribed physical caller position. -/
public def position : Fin localCtx.systemCount ↪ Fin caller.systemCount where
  toFun index := placement.positions (.inl index)
  inj' _ _ same := Sum.inl_injective (placement.positions.injective same)

/-- The placed wire has the prescribed identity and its original positive dimension. -/
public lemma contextEmbedding_position_wire (index : Fin localCtx.systemCount) :
    caller.quantumLayout.wire (placement.position index) =
      QuantumWire.relabel placement.physical (localCtx.quantumLayout.wire index) := by
  exact (ContextPermutation.positions_wire placement.covers _).trans
    ((ContextUnion.contextUnion_left_wire _ _ placement.separate _).trans
      (ContextRelabeling.positions_wire localCtx placement.keys placement.physical index))

/-- The complement's unchanged physical wire is present in the same caller layout. -/
public lemma contextEmbedding_frame_position_wire (index : Fin placement.frame.systemCount) :
    caller.quantumLayout.wire (placement.positions (.inr index)) =
      placement.frame.quantumLayout.wire index :=
  (ContextPermutation.positions_wire placement.covers _).trans
    (ContextUnion.contextUnion_right_wire _ _ placement.separate index)

/-- A physical placement never changes the native dimension of a local wire. -/
public lemma contextEmbedding_position_dimension (index : Fin localCtx.systemCount) :
    (caller.quantumLayout.wire (placement.position index)).dimension =
      (localCtx.quantumLayout.wire index).dimension := by
  simpa only [QuantumWire.relabel] using
    congrArg QuantumWire.dimension (placement.contextEmbedding_position_wire index)

/-- The caller selection consists exactly of the placed original selected wires. -/
public def selection (selected : Finset (Fin localCtx.systemCount)) :
    Finset (Fin caller.systemCount) := selected.map placement.position

/-- Each selected original position has exactly one position in the actual output selection. -/
public def selectedPositions (selected : Finset (Fin localCtx.systemCount)) :
    QuantumLayout.SelectedPosition selected ≃
      QuantumLayout.SelectedPosition (placement.selection selected) :=
  Finset.equivMap placement.position selected

/-- The selected dependent-product basis retains every original finite wire carrier. -/
public def selectedBasis (selected : Finset (Fin localCtx.systemCount)) :
    (localCtx.quantumLayout.selectedRegister selected).Index ≃
      (caller.quantumLayout.selectedRegister (placement.selection selected)).Index :=
  (placement.selectedPositions selected).piCongr fun index =>
    finCongr (congrArg PNat.val (placement.contextEmbedding_position_dimension index.val).symm)

end

end QuantumAlg.ContextEmbedding
