/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Workspace.Layout

/-!
# Exact classical capacity of the reusable quadratic workspace

The two candidate checks reuse the same physical cells. The formula counts
their single shared footprint, the square-root work, and all ten flag bits.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.QuadraticScratchLayout

/-- Independent bit count for the 26 simultaneously live quadratic cells. -/
def allocationBits (N : Nat) : Nat :=
  5 * DiscriminantWidth N + 7 * CandidateWidth N + CenterWidth N + 8 * WorkWidth N + 10

private lemma quadraticSpaceArithmetic {kind : ProblemKind}
    (discriminant candidate center work : Nat) :
    (([.unsignedWord discriminant, .unsignedWord candidate, .unsignedWord candidate,
      .unsignedWord center, .unsignedWord discriminant, .bit, .unsignedWord discriminant,
      .unsignedWord (work + work), .unsignedWord work, .unsignedWord work,
      .product (.unsignedWord work) .bit, .unsignedWord (work + work), .bit, .bit,
      .unsignedWord work, .unsignedWord candidate, .unsignedWord candidate, .bit,
      .unsignedWord candidate, .product (.unsignedWord candidate) .bit, .bit,
      .unsignedWord discriminant, .bit,
      .product (.unsignedWord discriminant) (.unsignedWord candidate), .bit, .bit].map
        SpacePool.ofShape).sum : SpacePool kind) =
      SpacePool.ofShape (.bits (5 * discriminant + 7 * candidate + center + 8 * work + 10)) := by
  ext axis
  cases axis <;>
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      SpacePool.ofShape, Pi.add_apply, Pi.zero_apply, CShape.bitWidth] <;> omega

/-- All allocated quadratic capacity is classical and has the stated exact width sum. -/
lemma quadraticAllocationSpace_eq_bits {kind : ProblemKind} (N : Nat) :
    (((shapes N).map SpacePool.ofShape).sum : SpacePool kind) =
      SpacePool.ofShape (.bits (allocationBits N)) :=
  quadraticSpaceArithmetic (DiscriminantWidth N) (CandidateWidth N) (CenterWidth N) (WorkWidth N)

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.QuadraticScratchLayout
