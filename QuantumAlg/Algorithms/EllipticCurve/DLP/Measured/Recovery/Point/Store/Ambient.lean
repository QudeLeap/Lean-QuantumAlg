/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.History.Feedback
import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.Measured.Stored.Cascade
import all QuantumAlg.Core.Execution.Store.Ext

/-!
# Unique classical markers of the actual indexed quantum frame

Every entry of the indexed ambient context is an owned quantum layout. Its
classical Store contains only presence markers, with no classical storage
reference. The quantum state of that frame remains in the complete joint
execution state and its external Reference; no quantum equality or erasure
follows from equality of these classical Stores.

The old point-call retain predicate is therefore always satisfied. The fixed
streaming stage still retains its entire outer measurement-cell frame. All
widths, arbitrary dirty Stores and zero result-cell counts remain included.
These are Store-coordinate facts, not a path correspondence or an equality
of instruments, common output densities or success probabilities.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point.Store

noncomputable section

open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open ScalarMultiplication.MeasuredPlacement

/-- Indexed quantum entries have no classical storage reads that could distinguish Stores. -/
lemma indexedContext_stores_equal (width : Nat) (indices : List Nat)
    (distinct : indices.Nodup) (first second : Store (indexedContext width indices distinct)) :
    first = second := by
  apply Store.store_eq_of_storage_reads
  intro shape input
  have present := input.present
  change RuntimeEntry.storage input.key input.role shape ∈
    indices.map (indexedEntry width) at present
  obtain ⟨index, _member, impossible⟩ := List.mem_map.mp present
  change RuntimeEntry.ownedLayout (indexedKey width index) (indexedLayout width index) =
    RuntimeEntry.storage input.key input.role shape at impossible
  cases impossible

/-- The actual old point call imposes no condition on its quantum-only ambient Store. -/
lemma old_retains_true (width : Nat) {count : Nat} (active : Fin count)
    (final original : Store (readyContext width count)) :
    Recovery.Reference.Measured.retains width active final original := by
  change (Recovery.Reference.Measured.pointStore width active original).2 =
    (Recovery.Reference.Measured.pointStore width active final).2
  exact indexedContext_stores_equal width ((List.range count).erase active.val)
    (List.nodup_range.erase _) _ _

/-- The fixed stage keeps the complete outer result-cell Store, including dirty cells. -/
lemma fixed_retains_iff_cells (width m : Nat)
    (stored original : Store (Recovery.Layout.terminal width m)) :
    Recovery.Stage.retains width m stored original ↔
      let outer := Recovery.Point.cellsPlacement (readyContext width 2) 2 (2 * m)
      (outer.store original).2 = (outer.store stored).2 := by
  let inner := Recovery.Point.indexedPointPlacement width (0 : Fin 2)
  let outer := Recovery.Point.cellsPlacement (readyContext width 2) 2 (2 * m)
  change ((inner.store (outer.store original).1).2 = (inner.store (outer.store stored).1).2 ∧
    (outer.store original).2 = (outer.store stored).2) ↔
      (outer.store original).2 = (outer.store stored).2
  constructor
  · exact And.right
  · intro cellsSame
    refine ⟨?_, cellsSame⟩
    exact indexedContext_stores_equal width ((List.range 2).erase 0)
      (List.nodup_range.erase _) _ _

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point.Store
