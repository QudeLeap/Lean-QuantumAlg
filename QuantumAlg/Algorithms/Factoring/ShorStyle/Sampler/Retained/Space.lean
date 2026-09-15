/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Program.Space

/-!
# Complete live space of the actual retained residue sampler

The retained source sample has sixteen width-many bits. The complete retained
parameter has two width-many words and one flag. They remain live throughout
preparation, whose eleven scopes and actual GCD work add at most nine
width-many bits and fourteen further bits. The total additional allowance is
therefore `27 * width + 15` classical bits. Every pre-existing quantum system
keeps its actual native dimension and role throughout the execution.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Retained

open ClassicalRoutines

variable {kind : ProblemKind}

/-- Exact capacity of the two actual retained results. -/
def resultSpace (kind : ProblemKind) (width : Nat) : SpacePool kind :=
  SpacePool.ofShape (.bits (18 * width + 1))

/-- Independent allowance for both retained results and simultaneously live preparation work. -/
def additionalSpace (kind : ProblemKind) (width : Nat) : SpacePool kind :=
  SpacePool.ofShape (.bits (27 * width + 15))

/-- The two retained cells contribute exactly their complete resident capacity. -/
theorem samplerRetained_context_resident (ctx : RuntimeCtx kind) (N : Nat) :
    (context ctx N).residentSpace = ctx.residentSpace + resultSpace kind (modulusBits N) := by
  apply SpacePool.ext
  intro axis
  cases axis <;>
    simp [context, sampleContext, ParameterShape, residueSamplingBits, residueProposalCount,
      resultSpace, SpacePool.ofShape]; omega

/-- Every actual allocation stage fits the final retained resident context. -/
theorem samplerRetained_allocation_resident_le (ctx : RuntimeCtx kind) (N : Nat)
    (path : (allocation ctx N).Path) :
    (allocation ctx N).peakResidentSpace path ≤ (context ctx N).residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro frame present
  change frame ∈ [ctx, sampleContext ctx N, sampleContext ctx N, context ctx N] at present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl | rfl
  all_goals
    intro axis
    cases axis <;>
      simp [context, sampleContext, SpacePool.ofShape] <;> omega

private theorem body_resident_le (ctx : RuntimeCtx kind) (N : Nat)
    (path : (body ctx N).Path) :
    (body ctx N).peakResidentSpace path ≤
      (context ctx N).residentSpace + Program.additionalSpace kind (modulusBits N) := by
  refine (Circuit.peakResidentSpace_seq (PackedSample.draw N (sampleRef ctx N))
    (Program.circuit N (FirstAccepted.cellRead (sampleRef ctx N))
      (parameterRef ctx N)) path).le.trans ?_
  apply SpacePool.max_le
  · have drawn : (PackedSample.draw N (sampleRef ctx N)).peakResidentSpace path.1 =
        (context ctx N).residentSpace := by
      funext axis
      change max ((context ctx N).residentSpace axis) 0 = _
      exact Nat.max_zero _
    exact drawn.le.trans (fun axis => Nat.le_add_right _ _)
  · exact Program.samplerProgram_resident_le N
      (FirstAccepted.cellRead (sampleRef ctx N)) (parameterRef ctx N) path.2

private theorem resident_budget (ctx : RuntimeCtx kind) (N : Nat) :
    (context ctx N).residentSpace + Program.additionalSpace kind (modulusBits N) =
      ctx.residentSpace + additionalSpace kind (modulusBits N) := by
  rw [samplerRetained_context_resident]
  apply SpacePool.ext
  intro axis
  cases axis <;>
    simp [resultSpace, Program.additionalSpace, additionalSpace, SpacePool.ofShape]; omega

/-- The complete native sampler's resident peak includes all retained and temporary cells. -/
theorem samplerRetained_resident_le (ctx : RuntimeCtx kind) (N : Nat)
    (path : (circuit ctx N).Path) :
    (circuit ctx N).peakResidentSpace path ≤
      ctx.residentSpace + additionalSpace kind (modulusBits N) := by
  have combined : (circuit ctx N).peakResidentSpace path ≤
      (context ctx N).residentSpace + Program.additionalSpace kind (modulusBits N) := by
    refine (Circuit.peakResidentSpace_seq (allocation ctx N) (body ctx N) path).le.trans ?_
    exact SpacePool.max_le
      ((samplerRetained_allocation_resident_le ctx N path.1).trans
        (fun axis => Nat.le_add_right _ _)) (body_resident_le ctx N path.2)
  exact combined.trans_eq (resident_budget ctx N)

/-- The two retained cells contribute exactly their complete auxiliary capacity. -/
theorem samplerRetained_context_auxiliary (ctx : RuntimeCtx kind) (N : Nat) :
    (context ctx N).auxiliarySpace = ctx.auxiliarySpace + resultSpace kind (modulusBits N) := by
  apply SpacePool.ext
  intro axis
  cases axis <;>
    simp [context, sampleContext, ParameterShape, residueSamplingBits, residueProposalCount,
      resultSpace, SpacePool.ofShape]; omega

/-- Every actual allocation stage fits the final retained auxiliary context. -/
theorem samplerRetained_allocation_auxiliary_le (ctx : RuntimeCtx kind) (N : Nat)
    (path : (allocation ctx N).Path) :
    (allocation ctx N).peakAuxiliarySpace path ≤ (context ctx N).auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro frame present
  change frame ∈ [ctx, sampleContext ctx N, sampleContext ctx N, context ctx N] at present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl | rfl
  all_goals
    intro axis
    cases axis <;>
      simp [context, sampleContext, SpacePool.ofShape] <;> omega

private theorem body_auxiliary_le (ctx : RuntimeCtx kind) (N : Nat)
    (path : (body ctx N).Path) :
    (body ctx N).peakAuxiliarySpace path ≤
      (context ctx N).auxiliarySpace + Program.additionalSpace kind (modulusBits N) := by
  refine (Circuit.peakAuxiliarySpace_seq (PackedSample.draw N (sampleRef ctx N))
    (Program.circuit N (FirstAccepted.cellRead (sampleRef ctx N))
      (parameterRef ctx N)) path).le.trans ?_
  apply SpacePool.max_le
  · have drawn : (PackedSample.draw N (sampleRef ctx N)).peakAuxiliarySpace path.1 =
        (context ctx N).auxiliarySpace := by
      funext axis
      change max ((context ctx N).auxiliarySpace axis) 0 = _
      exact Nat.max_zero _
    exact drawn.le.trans (fun axis => Nat.le_add_right _ _)
  · exact Program.samplerProgram_auxiliary_le N
      (FirstAccepted.cellRead (sampleRef ctx N)) (parameterRef ctx N) path.2

private theorem auxiliary_budget (ctx : RuntimeCtx kind) (N : Nat) :
    (context ctx N).auxiliarySpace + Program.additionalSpace kind (modulusBits N) =
      ctx.auxiliarySpace + additionalSpace kind (modulusBits N) := by
  rw [samplerRetained_context_auxiliary]
  apply SpacePool.ext
  intro axis
  cases axis <;>
    simp [resultSpace, Program.additionalSpace, additionalSpace, SpacePool.ofShape]; omega

/-- The complete native sampler's auxiliary peak includes all retained and temporary cells. -/
theorem samplerRetained_auxiliary_le (ctx : RuntimeCtx kind) (N : Nat)
    (path : (circuit ctx N).Path) :
    (circuit ctx N).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + additionalSpace kind (modulusBits N) := by
  have combined : (circuit ctx N).peakAuxiliarySpace path ≤
      (context ctx N).auxiliarySpace + Program.additionalSpace kind (modulusBits N) := by
    refine (Circuit.peakAuxiliarySpace_seq (allocation ctx N) (body ctx N) path).le.trans ?_
    exact SpacePool.max_le
      ((samplerRetained_allocation_auxiliary_le ctx N path.1).trans
        (fun axis => Nat.le_add_right _ _)) (body_auxiliary_le ctx N path.2)
  exact combined.trans_eq (auxiliary_budget ctx N)

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Retained
