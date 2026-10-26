/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Runtime.Values
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Cycle.Protection
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Unlookup.Branch.Coherent

/-!
# Actual paid unlookup on the original constructed point-word graph

The actual parity program still reads the original array cell and executes
every AND/XOR, physical feedback and reset. Its per-record coefficient is
attached to the canonical point words in that same actual Store, rather
than to a separately supplied static table. The full external reference
and arbitrary coherent amplitudes remain visible.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution ClassicalAlgorithms.EllipticCurve EncodedBit EncodedBit.WindowLookup
open NormalizedVector
open scoped BigOperators

noncomputable section

variable {ctx : RuntimeCtx .quantum} {wordWidth lowWidth highRemaining : Nat}
  (tables : TableFrame ctx wordWidth (2 ^ (highRemaining + lowWidth + 1)))

private lemma wordEncoding_eq_toNat (word : CShape.Value (.unsignedWord wordWidth)) :
    RuntimeTable.wordEncoding word = (⟨word.toNat, word.toNat_lt⟩ : Fin (2 ^ wordWidth)) := by
  cases word
  rfl

/-- Every runtime parity word decodes the original constructed value at its full split address. -/
lemma constructedSplitInputs_read (curve : CurveSpec wordWidth) (point : Point curve)
    (store : Store ctx) (values : TableValue curve tables point store) (column : Fin 5)
    (top : Bool) (high : Fin (2 ^ highRemaining)) :
    RuntimeRow.readTable
      (RuntimeTable.splitInputs (tables.runtimeSource column) top high) store =
        fun low => pointWordTable curve point column top (joinedAddress high low) := by
  funext low
  have actual := tables.runtimeTableValue_eq_pointWord curve point store values column top
    (joinedAddress high low)
  rw [RuntimeTable.tableValue_read, wordEncoding_eq_toNat] at actual
  exact actual

/-- Every real outcome of the paid runtime instrument has the common original point-graph factor. -/
lemma constructedUnlookup_graph_coherent (curve : CurveSpec wordWidth) (point : Point curve)
    (store : Store ctx) (values : TableValue curve tables point store) (column : Fin 5)
    {Data : Type} {encoding : BinaryLabelEncoding Data} {services : ClassicalOracleModel}
    (frame : UnlookupFrame encoding wordWidth lowWidth highRemaining)
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin wordWidth → CWriteRef ctx (.finite 2))
    (outputDistinct : Function.Injective fun index => (output index).key)
    (mask : CWriteRef ctx (.bits wordWidth))
    (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
    (parityDistinct : Function.Injective fun index => (parity index).key)
    (temporaryDifferent : ∀ index, (parity index).key ≠ temporary.key)
    (environment : OracleModel.Interpretation .empty) (seed : Data)
    (outcome : Fin (2 ^ wordWidth))
    {Reference : Register} {Index : Type} [Fintype Index] (state : Index → Data)
    (graph : ∀ index, frame.Graph
      (fun top high low => pointWordTable curve point column top
        (joinedAddress high low)) (state index))
    (clean : ∀ index, frame.high.CleanFrom 0 (state index))
    (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    (RuntimeUnlookup.branchOperator frame (services := services) physical sameWires
      output mask parity temporary (RuntimeTable.splitInputs (tables.runtimeSource column))
      store (namedResultPath (oracles := .empty) (services := services)
        physical sameWires frame.result output seed outcome) environment Reference).applyVec
      (∑ index, amplitude index •
        (NormalizedVector.ket (R := Register.prod ctx.register Reference)
          (measuredEncodedBasis physical sameWires (state index), reference index)).vec) =
      invSqrt2 ^ wordWidth •
        ∑ index, amplitude index •
          (NormalizedVector.ket (R := Register.prod ctx.register Reference)
            (measuredEncodedBasis physical sameWires
              (resultSetConstant frame.result 0 (state index)), reference index)).vec := by
  have actualGraph : ∀ index, frame.Graph
      (fun top high => RuntimeRow.readTable
        (RuntimeTable.splitInputs (tables.runtimeSource column) top high) store)
      (state index) := by
    have same : (fun top high => RuntimeRow.readTable
        (RuntimeTable.splitInputs (tables.runtimeSource column) top high) store) =
        (fun top high low => pointWordTable curve point column top
          (joinedAddress high low)) := by
      funext top high
      exact tables.constructedSplitInputs_read curve point store values column top high
    rw [same]
    exact graph
  exact RuntimeUnlookup.branchOperator_graph_coherent frame physical sameWires
    output outputDistinct mask parity temporary
    (RuntimeTable.splitInputs (tables.runtimeSource column))
    (RuntimeTable.splitInputs_stored_protection (tables.finishColumns column)
      mask parity temporary parityDistinct temporaryDifferent)
    (RuntimeTable.splitInputs_stored_output_free (tables.finishColumns column) output)
    (RuntimeTable.splitInputs_stored_mask_free (tables.finishColumns column) mask)
    environment store seed outcome state actualGraph clean reference amplitude

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
