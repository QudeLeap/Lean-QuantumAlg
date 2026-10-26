/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Cycle.Budget

/-!
# Symbolic actual query schedule for the two 260-bit streams

Every window contributes its supplied actual circuit, including its real
retained measurement paths. Each stream executes sixteen full windows and
its four-bit tail. Eighteen occurrences account for three rounds with six
load/unlookup calls per point. Composition preserves each child's internal
parallel depth; these lemmas do not count the separate point-arithmetic work.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.WindowSchedule

noncomputable section

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

local notation "Model" =>
  ExecutionModel.quantum AlgorithmGate.model OracleModel.empty BitWord.model services
local notation "Code" => Circuit Model ctx ctx false

/-- Chronologically compose the supplied actual fixed-context window circuits. -/
def sequenceCircuit (programs : List Code) : Code :=
  programs.foldr Circuit.seq (Circuit.id (model := Model) (allowAllocation := false) ctx)

private lemma sequenceCircuit_pool_cons (first : Code) (rest : List Code)
    (path : (sequenceCircuit (first :: rest)).Path) :
    (sequenceCircuit (first :: rest)).resourcePool path = first.resourcePool path.1 +
      (sequenceCircuit rest).resourcePool path.2 := by
  dsimp only [sequenceCircuit, List.foldr, Circuit.Path] at path
  change ResourcePool.ofList (_ ++ _) = _
  rw [ResourcePool.ofList_append]
  rfl

/-- Every real child contributes its own weighted native pool to the chronological schedule. -/
lemma sequenceCircuit_weight_le (programs : List Code) (weight : Resource.Event Model → Nat)
    (bound : Nat)
    (bounded : ∀ program ∈ programs, ∀ path,
      ResourcePool.weightedCount weight (program.resourcePool path) ≤ bound)
    (path : (sequenceCircuit programs).Path) :
    ResourcePool.weightedCount weight ((sequenceCircuit programs).resourcePool path) ≤
      programs.length * bound := by
  induction programs with
  | nil => simp [sequenceCircuit, Circuit.resourcePool, Circuit.eventTrace]
  | cons first rest ih =>
      have head := bounded first (List.mem_cons_self ..) path.1
      have tail := ih (fun program present => bounded program (List.mem_cons_of_mem _ present))
        path.2
      have actual := congrArg (ResourcePool.weightedCount weight)
        (sequenceCircuit_pool_cons first rest path)
      refine actual.trans_le ?_
      exact (ResourcePool.weightedCount_add weight _ _).trans_le (by
        simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
        omega)

/-- Exact native per-child multiplicities remain exact through the same actual schedule. -/
lemma sequenceCircuit_weight_eq (programs : List Code) (weight : Resource.Event Model → Nat)
    (amount : Nat)
    (exactAmount : ∀ program ∈ programs, ∀ path,
      ResourcePool.weightedCount weight (program.resourcePool path) = amount)
    (path : (sequenceCircuit programs).Path) :
    ResourcePool.weightedCount weight ((sequenceCircuit programs).resourcePool path) =
      programs.length * amount := by
  induction programs with
  | nil => simp [sequenceCircuit, Circuit.resourcePool, Circuit.eventTrace]
  | cons first rest ih =>
      have head := exactAmount first (List.mem_cons_self ..) path.1
      have tail := ih (fun program present => exactAmount program (List.mem_cons_of_mem _ present))
        path.2
      have actual := congrArg (ResourcePool.weightedCount weight)
        (sequenceCircuit_pool_cons first rest path)
      refine actual.trans ?_
      exact (ResourcePool.weightedCount_add weight _ _).trans (by
        rw [head, tail, List.length_cons, Nat.add_mul, Nat.one_mul]
        omega)

/-- Sequential window composition retains the original internal parallel depths of every child. -/
lemma sequenceCircuit_quantumTime_le (programs : List Code) (bound : Nat)
    (bounded : ∀ program ∈ programs, ∀ path,
      program.depth Resource.Event.quantumDuration path ≤ bound)
    (path : (sequenceCircuit programs).Path) :
    (sequenceCircuit programs).depth Resource.Event.quantumDuration path ≤
      programs.length * bound := by
  induction programs with
  | nil => simp [sequenceCircuit, Circuit.depth, Circuit.eventDepth]
  | cons first rest ih =>
      have head := bounded first (List.mem_cons_self ..) path.1
      have tail := ih (fun program present => bounded program (List.mem_cons_of_mem _ present))
        path.2
      have actual := Circuit.depth_seq first (sequenceCircuit rest)
        Resource.Event.quantumDuration path.1 path.2
      exact actual.trans_le (by
        simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
        omega)

/-- The actual stream executes its sixteen original full-window circuits before its final tail. -/
def streamCircuit (full : Fin 16 → Code) (tail : Code) : Code :=
  (sequenceCircuit (List.ofFn full)).seq tail

/-- Both actual streams are retained in their original full-window/tail order. -/
def blockCircuit (full : Fin 2 → Fin 16 → Code) (tail : Fin 2 → Code) : Code :=
  sequenceCircuit (List.ofFn fun stream => streamCircuit (full stream) (tail stream))

/-- The actual query fragment has three rounds and six load/unlookup calls per point. -/
def threeRoundCircuit (full : Fin 18 → Fin 2 → Fin 16 → Code)
    (tail : Fin 18 → Fin 2 → Code) : Code :=
  sequenceCircuit (List.ofFn fun occurrence => blockCircuit (full occurrence) (tail occurrence))

/-- Native weighted budgets propagate through the actual symbolic three-round window schedule. -/
lemma threeRoundCircuit_weight_le (full : Fin 18 → Fin 2 → Fin 16 → Code)
    (tail : Fin 18 → Fin 2 → Code) (weight : Resource.Event Model → Nat)
    (fullBound tailBound : Nat)
    (fullBounded : ∀ occurrence stream window path,
      ResourcePool.weightedCount weight ((full occurrence stream window).resourcePool path) ≤
        fullBound)
    (tailBounded : ∀ occurrence stream path,
      ResourcePool.weightedCount weight ((tail occurrence stream).resourcePool path) ≤ tailBound)
    (path : (threeRoundCircuit full tail).Path) :
    ResourcePool.weightedCount weight ((threeRoundCircuit full tail).resourcePool path) ≤
      18 * (2 * (16 * fullBound + tailBound)) := by
  have streamBound (occurrence : Fin 18) (stream : Fin 2)
      (current : (streamCircuit (full occurrence stream) (tail occurrence stream)).Path) :
      ResourcePool.weightedCount weight
        ((streamCircuit (full occurrence stream) (tail occurrence stream)).resourcePool current) ≤
          16 * fullBound + tailBound := by
    have first := sequenceCircuit_weight_le (List.ofFn (full occurrence stream)) weight fullBound
      (fun program included => by
        obtain ⟨window, rfl⟩ := List.mem_ofFn.mp included
        exact fullBounded occurrence stream window) current.1
    have last := tailBounded occurrence stream current.2
    have pools :
        (streamCircuit (full occurrence stream) (tail occurrence stream)).resourcePool current =
        (sequenceCircuit (List.ofFn (full occurrence stream))).resourcePool current.1 +
          (tail occurrence stream).resourcePool current.2 := by
      change ResourcePool.ofList (_ ++ _) = _
      exact ResourcePool.ofList_append _ _
    refine (congrArg (ResourcePool.weightedCount weight) pools).trans_le ?_
    exact (ResourcePool.weightedCount_add weight _ _).trans_le (by
      simp only [List.length_ofFn] at first
      omega)
  have blockBound (occurrence : Fin 18)
      (current : (blockCircuit (full occurrence) (tail occurrence)).Path) :
      ResourcePool.weightedCount weight
        ((blockCircuit (full occurrence) (tail occurrence)).resourcePool current) ≤
          2 * (16 * fullBound + tailBound) := by
    have actual := sequenceCircuit_weight_le
      (List.ofFn fun stream => streamCircuit (full occurrence stream) (tail occurrence stream))
      weight (16 * fullBound + tailBound) (fun program included => by
        obtain ⟨stream, rfl⟩ := List.mem_ofFn.mp included
        exact streamBound occurrence stream) current
    simpa only [blockCircuit, List.length_ofFn] using actual
  have actual := sequenceCircuit_weight_le
    (List.ofFn fun occurrence => blockCircuit (full occurrence) (tail occurrence)) weight
    (2 * (16 * fullBound + tailBound)) (fun program included => by
      obtain ⟨occurrence, rfl⟩ := List.mem_ofFn.mp included
      exact blockBound occurrence) path
  simpa only [threeRoundCircuit, List.length_ofFn] using actual

/-- Exact native measurement multiplicities remain exact in the actual three-round schedule. -/
lemma threeRoundCircuit_weight_eq (full : Fin 18 → Fin 2 → Fin 16 → Code)
    (tail : Fin 18 → Fin 2 → Code) (weight : Resource.Event Model → Nat)
    (fullAmount tailAmount : Nat)
    (fullExact : ∀ occurrence stream window path,
      ResourcePool.weightedCount weight ((full occurrence stream window).resourcePool path) =
        fullAmount)
    (tailExact : ∀ occurrence stream path,
      ResourcePool.weightedCount weight ((tail occurrence stream).resourcePool path) = tailAmount)
    (path : (threeRoundCircuit full tail).Path) :
    ResourcePool.weightedCount weight ((threeRoundCircuit full tail).resourcePool path) =
      18 * (2 * (16 * fullAmount + tailAmount)) := by
  have streamExact (occurrence : Fin 18) (stream : Fin 2)
      (current : (streamCircuit (full occurrence stream) (tail occurrence stream)).Path) :
      ResourcePool.weightedCount weight
        ((streamCircuit (full occurrence stream) (tail occurrence stream)).resourcePool current) =
          16 * fullAmount + tailAmount := by
    have first := sequenceCircuit_weight_eq (List.ofFn (full occurrence stream)) weight fullAmount
      (fun program included => by
        obtain ⟨window, rfl⟩ := List.mem_ofFn.mp included
        exact fullExact occurrence stream window) current.1
    have last := tailExact occurrence stream current.2
    have pools :
        (streamCircuit (full occurrence stream) (tail occurrence stream)).resourcePool current =
        (sequenceCircuit (List.ofFn (full occurrence stream))).resourcePool current.1 +
          (tail occurrence stream).resourcePool current.2 := by
      change ResourcePool.ofList (_ ++ _) = _
      exact ResourcePool.ofList_append _ _
    refine (congrArg (ResourcePool.weightedCount weight) pools).trans ?_
    exact (ResourcePool.weightedCount_add weight _ _).trans (by
      rw [first, last, List.length_ofFn])
  have blockExact (occurrence : Fin 18)
      (current : (blockCircuit (full occurrence) (tail occurrence)).Path) :
      ResourcePool.weightedCount weight
        ((blockCircuit (full occurrence) (tail occurrence)).resourcePool current) =
          2 * (16 * fullAmount + tailAmount) := by
    have actual := sequenceCircuit_weight_eq
      (List.ofFn fun stream => streamCircuit (full occurrence stream) (tail occurrence stream))
      weight (16 * fullAmount + tailAmount) (fun program included => by
        obtain ⟨stream, rfl⟩ := List.mem_ofFn.mp included
        exact streamExact occurrence stream) current
    simpa only [blockCircuit, List.length_ofFn] using actual
  have actual := sequenceCircuit_weight_eq
    (List.ofFn fun occurrence => blockCircuit (full occurrence) (tail occurrence)) weight
    (2 * (16 * fullAmount + tailAmount)) (fun program included => by
      obtain ⟨occurrence, rfl⟩ := List.mem_ofFn.mp included
      exact blockExact occurrence) path
  simpa only [threeRoundCircuit, List.length_ofFn] using actual

/-- The actual three-round query schedule retains every child's original parallel quantum depth. -/
lemma threeRoundCircuit_quantumTime_le (full : Fin 18 → Fin 2 → Fin 16 → Code)
    (tail : Fin 18 → Fin 2 → Code) (fullBound tailBound : Nat)
    (fullBounded : ∀ occurrence stream window path,
      (full occurrence stream window).depth Resource.Event.quantumDuration path ≤ fullBound)
    (tailBounded : ∀ occurrence stream path,
      (tail occurrence stream).depth Resource.Event.quantumDuration path ≤ tailBound)
    (path : (threeRoundCircuit full tail).Path) :
    (threeRoundCircuit full tail).depth Resource.Event.quantumDuration path ≤
      18 * (2 * (16 * fullBound + tailBound)) := by
  have streamBound (occurrence : Fin 18) (stream : Fin 2)
      (current : (streamCircuit (full occurrence stream) (tail occurrence stream)).Path) :
      (streamCircuit (full occurrence stream) (tail occurrence stream)).depth
        Resource.Event.quantumDuration current ≤ 16 * fullBound + tailBound := by
    have first := sequenceCircuit_quantumTime_le (List.ofFn (full occurrence stream)) fullBound
      (fun program included => by
        obtain ⟨window, rfl⟩ := List.mem_ofFn.mp included
        exact fullBounded occurrence stream window) current.1
    have last := tailBounded occurrence stream current.2
    have actual := Circuit.depth_seq (sequenceCircuit (List.ofFn (full occurrence stream)))
      (tail occurrence stream) Resource.Event.quantumDuration current.1 current.2
    exact actual.trans_le (by simp only [List.length_ofFn] at first; omega)
  have blockBound (occurrence : Fin 18)
      (current : (blockCircuit (full occurrence) (tail occurrence)).Path) :
      (blockCircuit (full occurrence) (tail occurrence)).depth Resource.Event.quantumDuration
        current ≤ 2 * (16 * fullBound + tailBound) := by
    have actual := sequenceCircuit_quantumTime_le
      (List.ofFn fun stream => streamCircuit (full occurrence stream) (tail occurrence stream))
      (16 * fullBound + tailBound) (fun program included => by
        obtain ⟨stream, rfl⟩ := List.mem_ofFn.mp included
        exact streamBound occurrence stream) current
    simpa only [blockCircuit, List.length_ofFn] using actual
  have actual := sequenceCircuit_quantumTime_le
    (List.ofFn fun occurrence => blockCircuit (full occurrence) (tail occurrence))
    (2 * (16 * fullBound + tailBound)) (fun program included => by
      obtain ⟨occurrence, rfl⟩ := List.mem_ofFn.mp included
      exact blockBound occurrence) path
  simpa only [threeRoundCircuit, List.length_ofFn] using actual

end

end QuantumAlg.EncodedBit.WindowLookup.WindowSchedule
