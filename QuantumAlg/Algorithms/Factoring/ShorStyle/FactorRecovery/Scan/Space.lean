/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scan.Layout
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scope.Space
import all QuantumAlg.Components.Classical.FirstAccepted.Resources
import all QuantumAlg.Core.Execution.Trace.Composition
import Mathlib.Tactic.Tauto

/-!
# Complete live capacity of actual first-success factor scanning

Every factor visit releases its own seven-cell and arithmetic workspaces
before the next visit. The ordered scan therefore needs one such complete
peak in addition to its actual input context. Its four persistent scan cells
remain live throughout that peak and add exactly `2m+3` classical bits.
The existing result and sampled tuples are counted in the caller context;
no part of their storage or of the nested arithmetic scratch is omitted.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeFactorScan

open ClassicalRoutines

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

private theorem selection_resident_le (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (selection cells result).Path) :
    (selection cells result).peakResidentSpace path ≤ ctx.residentSpace := by
  refine (Circuit.peakResidentSpace_seq (.classical (unpackOp cells result))
    (FirstAccepted.circuit (selectorInputs cells) (selectorRefs cells)) path).le.trans ?_
  exact SpacePool.max_le
    (Circuit.peakResidentSpace_classical (unpackOp cells result) path.1).le
    (FirstAccepted.firstAccepted_resident_le (selectorInputs cells) (selectorRefs cells) path.2)

/-- The actual recovery scope includes its full simultaneous resident workspace in each visit. -/
theorem visit_resident_le (source : Input N) (inputs : Inputs ctx N) (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (visit source inputs cells result).Path) :
    (visit source inputs cells result).peakResidentSpace path ≤
      ctx.residentSpace + FactorRecovery.NativeFactorScope.spaceBound kind N := by
  refine (Circuit.peakResidentSpace_seq
    (FactorRecovery.NativeFactorScope.code source inputs.parameter inputs.phase result)
    (selection cells result) path).le.trans ?_
  exact SpacePool.max_le
    (FactorRecovery.NativeFactorScope.code_resident_le
      source inputs.parameter inputs.phase result path.1)
    ((selection_resident_le cells result path.2).trans (fun _ => Nat.le_add_right _ _))

/-- Successive actual visits release their work and share one complete resident peak allowance. -/
theorem scan_resident_le (source : Input N) (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (inputs : List (Inputs ctx N)) : ∀ path : (scan source cells result inputs).Path,
    (scan source cells result inputs).peakResidentSpace path ≤
      ctx.residentSpace + FactorRecovery.NativeFactorScope.spaceBound kind N := by
  induction inputs with
  | nil =>
      intro path
      apply Circuit.peakResidentSpace_le_of_visited
      intro visited present
      have same : visited = ctx := List.mem_singleton.mp present
      subst visited
      exact fun _ => Nat.le_add_right _ _
  | cons input rest ih =>
      intro path
      refine (Circuit.peakResidentSpace_seq (visit source input cells result)
        (scan source cells result rest) path).le.trans ?_
      exact SpacePool.max_le (visit_resident_le source input cells result path.1) (ih path.2)

/-- Initial clearing and final real packing do not add a new resident cell to the complete scan. -/
theorem code_resident_le (source : Input N) (inputs : List (Inputs ctx N)) (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (code source inputs cells result).Path) :
    (code source inputs cells result).peakResidentSpace path ≤
      ctx.residentSpace + FactorRecovery.NativeFactorScope.spaceBound kind N := by
  refine (Circuit.peakResidentSpace_seq (.classical (clearAcceptedOp cells))
    (.seq (scan source cells result inputs) (.classical (packOp cells result))) path).le.trans ?_
  apply SpacePool.max_le
  · exact (Circuit.peakResidentSpace_classical (clearAcceptedOp cells) path.1).le.trans
      (fun _ => Nat.le_add_right _ _)
  · refine (Circuit.peakResidentSpace_seq (scan source cells result inputs)
      (.classical (packOp cells result)) path.2).le.trans ?_
    exact SpacePool.max_le (scan_resident_le source cells result inputs path.2.1)
      ((Circuit.peakResidentSpace_classical (packOp cells result) path.2.2).le.trans
        (fun _ => Nat.le_add_right _ _))

private theorem selection_auxiliary_le (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (selection cells result).Path) :
    (selection cells result).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq (.classical (unpackOp cells result))
    (FirstAccepted.circuit (selectorInputs cells) (selectorRefs cells)) path).le.trans ?_
  exact SpacePool.max_le
    (Circuit.peakAuxiliarySpace_classical (unpackOp cells result) path.1).le
    (FirstAccepted.firstAccepted_auxiliary_le (selectorInputs cells) (selectorRefs cells) path.2)

/-- The actual recovery scope includes its full simultaneous auxiliary workspace in each visit. -/
theorem visit_auxiliary_le (source : Input N) (inputs : Inputs ctx N) (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (visit source inputs cells result).Path) :
    (visit source inputs cells result).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + FactorRecovery.NativeFactorScope.spaceBound kind N := by
  refine (Circuit.peakAuxiliarySpace_seq
    (FactorRecovery.NativeFactorScope.code source inputs.parameter inputs.phase result)
    (selection cells result) path).le.trans ?_
  exact SpacePool.max_le
    (FactorRecovery.NativeFactorScope.code_auxiliary_le
      source inputs.parameter inputs.phase result path.1)
    ((selection_auxiliary_le cells result path.2).trans (fun _ => Nat.le_add_right _ _))

/-- Successive actual visits release their work and share one complete auxiliary peak allowance. -/
theorem scan_auxiliary_le (source : Input N) (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (inputs : List (Inputs ctx N)) : ∀ path : (scan source cells result inputs).Path,
    (scan source cells result inputs).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + FactorRecovery.NativeFactorScope.spaceBound kind N := by
  induction inputs with
  | nil =>
      intro path
      apply Circuit.peakAuxiliarySpace_le_of_visited
      intro visited present
      have same : visited = ctx := List.mem_singleton.mp present
      subst visited
      exact fun _ => Nat.le_add_right _ _
  | cons input rest ih =>
      intro path
      refine (Circuit.peakAuxiliarySpace_seq (visit source input cells result)
        (scan source cells result rest) path).le.trans ?_
      exact SpacePool.max_le (visit_auxiliary_le source input cells result path.1) (ih path.2)

/-- Initial clearing and final real packing do not add a new auxiliary cell to the complete scan. -/
theorem code_auxiliary_le (source : Input N) (inputs : List (Inputs ctx N)) (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (code source inputs cells result).Path) :
    (code source inputs cells result).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + FactorRecovery.NativeFactorScope.spaceBound kind N := by
  refine (Circuit.peakAuxiliarySpace_seq (.classical (clearAcceptedOp cells))
    (.seq (scan source cells result inputs) (.classical (packOp cells result))) path).le.trans ?_
  apply SpacePool.max_le
  · exact (Circuit.peakAuxiliarySpace_classical (clearAcceptedOp cells) path.1).le.trans
      (fun _ => Nat.le_add_right _ _)
  · refine (Circuit.peakAuxiliarySpace_seq (scan source cells result inputs)
      (.classical (packOp cells result)) path.2).le.trans ?_
    exact SpacePool.max_le (scan_auxiliary_le source cells result inputs path.2.1)
      ((Circuit.peakAuxiliarySpace_classical (packOp cells result) path.2.2).le.trans
        (fun _ => Nat.le_add_right _ _))

namespace Scope

/-- All four real scan cells remain live together with the complete factor-recovery workspace. -/
def spaceBound (kind : ProblemKind) (N : Nat) : SpacePool kind :=
  SpacePool.ofShape (.bits (4 * modulusBits N + 3 * phaseBits N + 10 +
    OrderRecovery.Native.extraClassicalBits (modulusBits N) (phaseBits N)))

/-- The original twice-modulus phase width yields this complete explicit scratch capacity. -/
theorem spaceBound_eq (kind : ProblemKind) (N : Nat) :
    spaceBound kind N = SpacePool.ofShape (.bits (38 * modulusBits N + 25)) := by
  have width : 4 * modulusBits N + 3 * phaseBits N + 10 +
      OrderRecovery.Native.extraClassicalBits (modulusBits N) (phaseBits N) =
        38 * modulusBits N + 25 := by
    unfold phaseBits OrderRecovery.Native.extraClassicalBits
    omega
  exact congrArg (fun count => SpacePool.ofShape (kind := kind) (.bits count)) width

private theorem code_visited (source : Input N) (inputs : List (Inputs ctx N))
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (code source inputs result).Path) (visited : RuntimeCtx kind)
    (present : visited ∈ (code source inputs result).visitedContexts path) :
    visited ∈ [ctx, candidateContext ctx N, acceptedContext ctx N, selectedContext ctx N] ∨
      visited ∈ (body source inputs result).visitedContexts path := by
  change visited ∈ (ctx) :: ((candidateContext ctx N) :: ((acceptedContext ctx N) ::
    ((selectedContext ctx N) :: ((body source inputs result).visitedContexts path ++
    [selectedContext ctx N]) ++ [acceptedContext ctx N]) ++ [candidateContext ctx N]) ++ [ctx])
    at present
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at present
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem prefix_resident_capacity (visited : RuntimeCtx kind)
    (present : visited ∈
      [ctx, candidateContext ctx N, acceptedContext ctx N, selectedContext ctx N]) :
    visited.residentSpace ≤ ctx.residentSpace + spaceBound kind N := by
  intro axis
  have capacities : ∀ entry ∈
      [ctx, candidateContext ctx N, acceptedContext ctx N, selectedContext ctx N],
      entry.residentSpace axis ≤ (ctx.residentSpace + spaceBound kind N) axis := by
    cases axis <;>
      simp [selectedContext, acceptedContext, candidateContext, spaceBound, SpacePool.ofShape]
    all_goals omega
  exact capacities visited present

private theorem full_resident_capacity :
    (context ctx N).residentSpace + FactorRecovery.NativeFactorScope.spaceBound kind N ≤
      ctx.residentSpace + spaceBound kind N := by
  intro axis
  cases axis <;>
    simp [context, selectedContext, acceptedContext, candidateContext,
      FactorRecovery.NativeFactorScope.spaceBound, spaceBound, SpacePool.ofShape]
  all_goals omega

/-- The scoped scan counts all persistent latches and nested resident arithmetic work together. -/
theorem code_resident_le (source : Input N) (inputs : List (Inputs ctx N))
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (code source inputs result).Path) :
    (code source inputs result).peakResidentSpace path ≤ ctx.residentSpace + spaceBound kind N := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rcases code_visited source inputs result path visited present with outer | inner
  · exact prefix_resident_capacity visited outer
  · exact (Circuit.residentSpace_le_peak_of_visited
      (body source inputs result) path visited inner).trans
        ((NativeFactorScan.code_resident_le source (inputs.map liftInputs)
          (cells ctx N) (liftWrite result) path).trans full_resident_capacity)

private theorem prefix_auxiliary_capacity (visited : RuntimeCtx kind)
    (present : visited ∈
      [ctx, candidateContext ctx N, acceptedContext ctx N, selectedContext ctx N]) :
    visited.auxiliarySpace ≤ ctx.auxiliarySpace + spaceBound kind N := by
  intro axis
  have capacities : ∀ entry ∈
      [ctx, candidateContext ctx N, acceptedContext ctx N, selectedContext ctx N],
      entry.auxiliarySpace axis ≤ (ctx.auxiliarySpace + spaceBound kind N) axis := by
    cases axis <;>
      simp [selectedContext, acceptedContext, candidateContext, spaceBound, SpacePool.ofShape]
    all_goals omega
  exact capacities visited present

private theorem full_auxiliary_capacity :
    (context ctx N).auxiliarySpace + FactorRecovery.NativeFactorScope.spaceBound kind N ≤
      ctx.auxiliarySpace + spaceBound kind N := by
  intro axis
  cases axis <;>
    simp [context, selectedContext, acceptedContext, candidateContext,
      FactorRecovery.NativeFactorScope.spaceBound, spaceBound, SpacePool.ofShape]
  all_goals omega

/-- The scoped scan counts all persistent latches and nested auxiliary arithmetic work together. -/
theorem code_auxiliary_le (source : Input N) (inputs : List (Inputs ctx N))
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (code source inputs result).Path) :
    (code source inputs result).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + spaceBound kind N := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rcases code_visited source inputs result path visited present with outer | inner
  · exact prefix_auxiliary_capacity visited outer
  · exact (Circuit.auxiliarySpace_le_peak_of_visited
      (body source inputs result) path visited inner).trans
        ((NativeFactorScan.code_auxiliary_le source (inputs.map liftInputs)
          (cells ctx N) (liftWrite result) path).trans full_auxiliary_capacity)

end Scope

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeFactorScan
