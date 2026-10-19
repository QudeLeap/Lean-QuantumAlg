/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Repetition
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Round.Space

/-!
# Live capacity of actual retained rounds on one bank

Each executed round retains one packed outcome. All earlier outcomes stay
live and therefore contribute to both actual role accounts. One group of
simultaneous reset result cells is reused between rounds. The quantum layout
is never enlarged by this repetition. The bounds apply at
every native dimension coordinate and include the zero-round identity.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimeRepetition

noncomputable section

private lemma round_space_weaken (scratch result : SpacePool .quantum) (count : Nat)
    (frame : SpacePool .quantum) :
    scratch + frame ≤
      scratch + count • result + frame := by
  intro axis
  change scratch axis + frame axis ≤
    scratch axis + (count • result) axis + frame axis
  omega

private lemma visited_spaces {shape : CShape} (m ell width N : Nat)
    (generator target : shape.Value → (ZMod N)ˣ)
    (ctx : RuntimeCtx .quantum)
    (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)
    (parameter : CInputRef ctx shape)
    (cells : Fin (RuntimeRound.resultBits m ell width) → CWriteRef ctx (.finite 2))
    (count : Nat)
    (path : (code m ell width N generator target ctx sameWires parameter cells count).Path)
    (frame : RuntimeCtx .quantum)
    (present : frame ∈
      (code m ell width N generator target ctx sameWires parameter cells count).visitedContexts
        path) :
    frame.residentSpace ≤ RuntimeRound.resetSpace m ell width +
        count • SpacePool.ofShape (.bits (RuntimeRound.resultBits m ell width)) +
          ctx.residentSpace ∧
      frame.auxiliarySpace ≤ RuntimeRound.resetSpace m ell width +
        count • SpacePool.ofShape (.bits (RuntimeRound.resultBits m ell width)) +
          ctx.auxiliarySpace := by
  induction count generalizing ctx frame with
  | zero =>
      change frame ∈ [ctx] at present
      obtain rfl := List.mem_singleton.mp present
      exact ⟨fun _ => Nat.le_add_left _ _, fun _ => Nat.le_add_left _ _⟩
  | succ count ih =>
      let result : SpacePool .quantum :=
        SpacePool.ofShape (.bits (RuntimeRound.resultBits m ell width))
      let nextCtx := RuntimeResults.next m ell width ctx
      let nextWires :=
        (RuntimeResults.shortDLP_runtimeResult_next_wires m ell width ctx).trans sameWires
      let nextParameter := parameter.underRetained ctx.canonicalFreshKey
        (.bits (RuntimeRound.resultBits m ell width)) ctx.canonicalFreshKey_fresh
      let nextCells := fun index => (cells index).underRetained ctx.canonicalFreshKey
        (.bits (RuntimeRound.resultBits m ell width)) ctx.canonicalFreshKey_fresh
      let first := RuntimeRound.code m ell width nextWires nextParameter N generator target
        nextCells (RuntimeResults.head m ell width ctx)
      let later := code m ell width N generator target nextCtx nextWires nextParameter
        nextCells count
      have resident : RuntimeRound.resetSpace m ell width + count • result + nextCtx.residentSpace =
          RuntimeRound.resetSpace m ell width + (count + 1) • result + ctx.residentSpace := by
        rw [show nextCtx.residentSpace = result + ctx.residentSpace from
          RuntimeCtx.residentSpace_addRetained ctx ctx.canonicalFreshKey
            (.bits (RuntimeRound.resultBits m ell width)) ctx.canonicalFreshKey_fresh,
          succ_nsmul]
        ac_rfl
      have auxiliary :
          RuntimeRound.resetSpace m ell width + count • result + nextCtx.auxiliarySpace =
          RuntimeRound.resetSpace m ell width + (count + 1) • result + ctx.auxiliarySpace := by
        rw [show nextCtx.auxiliarySpace = result + ctx.auxiliarySpace from
          RuntimeCtx.auxiliarySpace_addRetained ctx ctx.canonicalFreshKey
            (.bits (RuntimeRound.resultBits m ell width)) ctx.canonicalFreshKey_fresh,
          succ_nsmul]
        ac_rfl
      change frame ∈ List.append (α := RuntimeCtx .quantum) [ctx, nextCtx]
        (List.append (α := RuntimeCtx .quantum)
          (first.visitedContexts path.2.1) (later.visitedContexts path.2.2)) at present
      simp only [List.append_eq, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
        at present
      rcases present with (rfl | rfl) | firstPresent | laterPresent
      · exact ⟨fun _ => Nat.le_add_left _ _, fun _ => Nat.le_add_left _ _⟩
      · exact ⟨(show nextCtx.residentSpace ≤
              RuntimeRound.resetSpace m ell width + count • result + nextCtx.residentSpace from
            fun _ => Nat.le_add_left _ _).trans_eq resident,
          (show nextCtx.auxiliarySpace ≤
              RuntimeRound.resetSpace m ell width + count • result + nextCtx.auxiliarySpace from
            fun _ => Nat.le_add_left _ _).trans_eq auxiliary⟩
      · have firstResident :=
          (Circuit.residentSpace_le_peak_of_visited first path.2.1 frame firstPresent).trans
            (RuntimeRound.shortDLP_runtimeRound_resident_le m ell width nextWires nextParameter
              N generator target nextCells (RuntimeResults.head m ell width ctx) path.2.1)
        have firstAuxiliary :=
          (Circuit.auxiliarySpace_le_peak_of_visited first path.2.1 frame firstPresent).trans
            (RuntimeRound.shortDLP_runtimeRound_auxiliary_le m ell width nextWires nextParameter
              N generator target nextCells (RuntimeResults.head m ell width ctx) path.2.1)
        exact ⟨(firstResident.trans
            (round_space_weaken (RuntimeRound.resetSpace m ell width) result count
              nextCtx.residentSpace)).trans_eq resident,
          (firstAuxiliary.trans
            (round_space_weaken (RuntimeRound.resetSpace m ell width) result count
              nextCtx.auxiliarySpace)).trans_eq
            auxiliary⟩
      · have laterSpaces := ih nextCtx nextWires nextParameter nextCells path.2.2 frame laterPresent
        exact ⟨laterSpaces.1.trans_eq resident, laterSpaces.2.trans_eq auxiliary⟩

/-- Resident peak includes every retained outcome and the shared bank of reset result cells. -/
lemma shortDLP_runtimeRepetition_resident_le {shape : CShape} (m ell width N : Nat)
    (generator target : shape.Value → (ZMod N)ˣ)
    (ctx : RuntimeCtx .quantum)
    (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)
    (parameter : CInputRef ctx shape)
    (cells : Fin (RuntimeRound.resultBits m ell width) → CWriteRef ctx (.finite 2))
    (count : Nat)
    (path : (code m ell width N generator target ctx sameWires parameter cells count).Path) :
    (code m ell width N generator target ctx sameWires parameter cells count).peakResidentSpace
      path ≤
      RuntimeRound.resetSpace m ell width +
        count • SpacePool.ofShape (.bits (RuntimeRound.resultBits m ell width)) +
          ctx.residentSpace :=
  Circuit.peakResidentSpace_le_of_visited _ path _ (fun frame present =>
    (visited_spaces m ell width N generator target ctx sameWires parameter cells count
      path frame present).1)

/-- Auxiliary peak follows the same actual retained cells, without adding another quantum bank. -/
lemma shortDLP_runtimeRepetition_auxiliary_le {shape : CShape} (m ell width N : Nat)
    (generator target : shape.Value → (ZMod N)ˣ)
    (ctx : RuntimeCtx .quantum)
    (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)
    (parameter : CInputRef ctx shape)
    (cells : Fin (RuntimeRound.resultBits m ell width) → CWriteRef ctx (.finite 2))
    (count : Nat)
    (path : (code m ell width N generator target ctx sameWires parameter cells count).Path) :
    (code m ell width N generator target ctx sameWires parameter cells count).peakAuxiliarySpace
      path ≤
      RuntimeRound.resetSpace m ell width +
        count • SpacePool.ofShape (.bits (RuntimeRound.resultBits m ell width)) +
          ctx.auxiliarySpace :=
  Circuit.peakAuxiliarySpace_le_of_visited _ path _ (fun frame present =>
    (visited_spaces m ell width N generator target ctx sameWires parameter cells count
      path frame present).2)

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimeRepetition
