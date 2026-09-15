/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Parameters
import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Core.Execution.Random
import all QuantumAlg.Core.Execution.Trace

/-!
# Native random storage and exact RSA proposal addresses

The random-bit instruction stores its finite outcome in most-significant-bit
order. The RSA source decoder numbers the packed proposal bits from the least
significant end. Each proposal therefore uses reversed structural addresses;
no arithmetic is computed by a read reference. The subsequent word decoder
must still materialize each proposal through its actual classical instructions.

The random instruction retains every quantum-reference block with exactly its
uniform weight. These equations cover arbitrary prior stores and histories.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.PackedSample

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The actual stored bit convention of the native random instruction. -/
def storedBits {width : Nat} (value : Fin (2 ^ width)) : Fin width → Bool :=
  fun bit => value.val.testBit (width - 1 - bit.val)

/-- Little-endian location of one proposal bit in the packed source sample. -/
def packedIndex {width count : Nat} (proposal : Fin count)
    (bit : Fin width) : Fin (count * width) := by
  refine ⟨proposal.val * width + bit.val, ?_⟩
  calc
    proposal.val * width + bit.val < proposal.val * width + width :=
      Nat.add_lt_add_left bit.isLt _
    _ = (proposal.val + 1) * width := (Nat.succ_mul proposal.val width).symm
    _ ≤ count * width :=
      Nat.mul_le_mul_right width (Nat.succ_le_of_lt proposal.isLt)

/-- The real MSB storage address corresponding to the source's LSB position. -/
def storedIndex {width count : Nat} (proposal : Fin count)
    (bit : Fin width) : Fin (count * width) :=
  (packedIndex proposal bit).rev

/-- One proposal is a fixed vector of actual bit-cell references. -/
def proposalRefs {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width count : Nat} (sample : CInputRef ctx (.bits (count * width)))
    (proposal : Fin count) : Fin width → CInputRef ctx .bit :=
  fun bit => .bitsGet sample (storedIndex proposal bit)

/-- Reversing the address recovers exactly the source sample's numbered bit. -/
theorem packedSample_storedIndex_bit {width count : Nat}
    (value : Fin (2 ^ (count * width))) (proposal : Fin count) (bit : Fin width) :
    storedBits value (storedIndex proposal bit) =
      value.val.testBit (proposal.val * width + bit.val) := by
  have bounded := (packedIndex proposal bit).isLt
  change value.val.testBit
    (count * width - 1 - (count * width - (proposal.val * width + bit.val + 1))) = _
  congr 1
  change proposal.val * width + bit.val < count * width at bounded
  omega

/-- Reading the actual stored sample gives the exact addressed source bit. -/
theorem packedSample_proposalRefs_read {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width count : Nat} (store : Execution.Store ctx)
    (sample : CInputRef ctx (.bits (count * width)))
    (value : Fin (2 ^ (count * width)))
    (sampled : store.read sample = .bits (storedBits value))
    (proposal : Fin count) (bit : Fin width) :
    (store.read (proposalRefs sample proposal bit)).toBool =
      value.val.testBit (proposal.val * width + bit.val) := by
  change ((store.read sample).bitGet (storedIndex proposal bit)).toBool = _
  rw [sampled]
  exact packedSample_storedIndex_bit value proposal bit

/-- The source's quotient/remainder slice is exactly the addressed little-endian word. -/
theorem packedSample_proposalValue_eq_bits {width count : Nat}
    (value : Fin (2 ^ (count * width))) (proposal : Fin count) :
    (RSA.decodeFixedWidthWords width count value proposal).val =
      Nat.ofBits (fun bit : Fin width =>
        value.val.testBit (proposal.val * width + bit.val)) := by
  rw [RSA.decodeFixedWidthWords_eq_decodeFixedWidthWord]
  change value.val / 2 ^ (proposal.val * width) % 2 ^ width = _
  have bitsEq :
      (fun bit : Fin width =>
        (value.val / 2 ^ (proposal.val * width)).testBit bit.val) =
        fun bit : Fin width => value.val.testBit (proposal.val * width + bit.val) := by
    funext bit
    simpa [Nat.add_comm] using
      (Nat.testBit_div_two_pow (n := proposal.val * width) value.val bit.val)
  rw [← bitsEq, Nat.ofBits_testBit]

/-- The native source contains precisely one random instruction of the public width. -/
def draw {kind : ProblemKind} {ctx : RuntimeCtx kind} (N : Nat)
    (output : CWriteRef ctx (.bits (residueSamplingBits N))) : Circuit ctx ctx :=
  .randomBits (residueSamplingBits N) output

/-- The sample path is the instruction's actual finite uniform choice. -/
theorem packedSample_draw_execute {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (N : Nat) (output : CWriteRef ctx (.bits (residueSamplingBits N)))
    (Reference : Register) {H : Type} [Fintype H]
    (state : Execution.State ctx Reference H) :
    (draw N output).execute Reference state =
      (Execution.uniformChoice state ⟨2 ^ residueSamplingBits N,
        Nat.two_pow_pos _⟩).mapClassical (fun value =>
          (value.1.1.write output (.bits (storedBits value.2)),
            (value.1.2, value.2))) := rfl

private theorem mapped_uniformChoice_matrix {C D : Type} [Fintype C] [Fintype D]
    [DecidableEq D]
    {R : Register} (state : ExecutionState C R) (count : ℕ+)
    (update : C × Fin count → D) (result : D) :
    (((Execution.uniformChoice state count).mapClassical update).block result).matrix =
      ∑ entry : C × Fin count, if update entry = result then
        ((count : ℝ)⁻¹) • (state.block entry.1).matrix else 0 := by
  rw [ExecutionState.mapClassical_block_matrix]
  apply Finset.sum_congr rfl
  intro entry _
  exact congrArg (fun matrix => if update entry = result then matrix else 0)
    (Execution.uniformChoice_block_matrix state count entry.1 entry.2)

open Classical in
/-- Exact complete matrix law: every sample has one uniform fraction of its
original quantum-reference block, and the written bits encode that same sample. -/
theorem packedSample_draw_block_matrix {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (N : Nat) (output : CWriteRef ctx (.bits (residueSamplingBits N)))
    (Reference : Register) {H : Type} [Fintype H]
    (state : Execution.State ctx Reference H)
    (result : Execution.Store ctx × (H × Fin (2 ^ residueSamplingBits N))) :
    (((draw N output).execute Reference state).block result).matrix =
      ∑ value : (Execution.Store ctx × H) × Fin (2 ^ residueSamplingBits N),
        if (value.1.1.write output (.bits (storedBits value.2)),
            (value.1.2, value.2)) = result then
          ((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ • (state.block value.1).matrix
        else 0 := by
  rw [packedSample_draw_execute]
  exact mapped_uniformChoice_matrix state
    (⟨2 ^ residueSamplingBits N, Nat.two_pow_pos _⟩ : ℕ+)
    (fun value =>
      (value.1.1.write output (.bits (storedBits value.2)), (value.1.2, value.2))) result

/-- Writing the sampled outcome makes every proposal address readable as its
original source integer; this is a store equality, not an input assumption. -/
theorem packedSample_draw_written_proposal {kind : ProblemKind}
    {ctx : RuntimeCtx kind} (N : Nat) (store : Execution.Store ctx)
    (output : CWriteRef ctx (.bits (residueSamplingBits N)))
    (value : Fin (2 ^ residueSamplingBits N))
    (proposal : Fin residueProposalCount) (bit : Fin (modulusBits N)) :
    ((store.write output (.bits (storedBits value))).read
      (proposalRefs (.storage output.toCStorageRef) proposal bit)).toBool =
        value.val.testBit (proposal.val * modulusBits N + bit.val) :=
  packedSample_proposalRefs_read _ _ value
    (Execution.Store.read_write_same store output _) proposal bit

/-- Every actual random path emits exactly the declared random-bit event. -/
theorem packedSample_draw_trace {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (N : Nat) (output : CWriteRef ctx (.bits (residueSamplingBits N)))
    (path : (draw N output).Path) :
    (draw N output).eventTrace path =
      [.classicalOperation (.randomBits (residueSamplingBits N))] := rfl

/-- Exact native pool, independent of the chosen sample and prior state. -/
theorem packedSample_draw_pool {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (N : Nat) (output : CWriteRef ctx (.bits (residueSamplingBits N)))
    (path : (draw N output).Path) :
    (draw N output).resourcePool path =
      ResourcePool.singleton (.classicalOperation (.randomBits (residueSamplingBits N))) := by
  simp only [Circuit.resourcePool, packedSample_draw_trace,
    ResourcePool.ofList_cons, ResourcePool.ofList_nil, add_zero]

/-- Native random sampling has one sequential dependency layer. -/
theorem packedSample_draw_unit_depth {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (N : Nat) (output : CWriteRef ctx (.bits (residueSamplingBits N)))
    (path : (draw N output).Path) :
    (draw N output).depth (fun _event => 1) path = 1 := rfl

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.PackedSample
